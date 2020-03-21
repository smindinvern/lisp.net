module Parsing

    open Ast
    open Macros.Types
    open Extensions

    open System.Collections.Generic

    open smindinvern.State.Lazy
    open smindinvern.Utils
    
    type ParserState = { Macros: IDictionary<string, Macro>
                       ; Bindings: IDictionary<string, Ast.Binding>
                       }

    type ExprParser<'a> = State<ParserState, 'a>

    let untagId' (boundVars: IDictionary<string, Ast.Binding>) (sym: string) =
        if sym.Contains('#') then
            if boundVars.ContainsKey(sym) then
                sym
            else
                // identifier is free in this environment, so untag it.
                let sym' = new string(Array.takeWhile (fun x -> x <> '#') <| sym.ToCharArray())
                sym'
        else
            sym

    let untagId (sym: string) =
        state {
            let! s = get
            return untagId' s.Bindings sym
        }

    let rec internal untagSyms' boundVars ld () =
        match ld with
            | Symbol s -> (Symbol(Ast.Binding(untagId' boundVars s.sym)), ())
            | x -> foldLispData (untagSyms' boundVars) () x

    let untagSyms ld =
        state {
            let! s = get
            return untagSyms' s.Bindings ld ()
        }

    let tryGetMacro (m: string) : ExprParser<Macro option> =
        state {
            let! s = get
            return s.Macros.tryGetValue(m)
        }

    let isBoundVar (v: string) : ExprParser<bool> =
        state {
            let! s = get
            return s.Bindings.ContainsKey(v)
        }

    let internal addBoundVars' bs ps =
        // TODO: is it a bug to insert a duplicate key here?
        let bindingsSeq = Seq.map (fun (kvp: KeyValuePair<string, Ast.Binding>) -> (kvp.Key, kvp.Value)) <| Seq.cast ps.Bindings
        let kvps = List.map (fun (b: Ast.Binding) -> (b.sym, b)) bs
        let bindings' = Seq.append bindingsSeq kvps
        { ps with Bindings = dict bindings' }

    let addBoundVars (bs: Ast.Binding list) : ExprParser<unit> =
        modify (addBoundVars' bs)
    
    let rec pattern = function
        | Symbol sym ->
            inject <| SymbolPattern sym
        | ConsCell (left, right) ->
            state {
                let! l = pattern left
                let! r = pattern right
                return ConsPattern (l, r)
            }
        | List ((Symbol s)::pats) ->
            state {
                match! tryGetMacro s.sym with
                    | Some(m) ->
                        let ld = m.Transformer <| ((Symbol s)::pats)
                        return! pattern ld
                    | None ->
                        let! subpats = sequence <| List.map pattern ((Symbol s)::pats)
                        return ListPattern subpats
            }
        | List pats -> ListPattern <@> (sequence <| List.map pattern pats)
        | Quote _ -> failwith "Quoted expressions cannot appear in patterns"
        | LispFunc _ -> failwith "Functions cannot appear in patterns"
        | d -> inject <| Pattern.LiteralPattern d

    let rec patternBindings = function
        | SymbolPattern b -> [b]
        | ConsPattern (l, r) -> (patternBindings l) @ (patternBindings r)
        | ListPattern pats -> List.collect patternBindings pats
        | Pattern.LiteralPattern _ -> []
    let patternVars = (List.map (fun (b: Ast.Binding) -> b.sym)) << patternBindings

    let rec findFreeVars (e: Expr) (free: string list) =
        match e with
        | LetExpr (bs, _) ->
            let (_, free') = foldExpr findFreeVars [] e
            (e, collectFreeVars (free @ free') bs)
        | CaseExpr (e', arms) ->
            let (_, free') = foldExpr findFreeVars [] e'
            let arms' = List.map (fun (pat, e) -> (pat, ListExpr e)) arms
            (e, collectFreeVars (free @ free') arms')
        | LambdaExpr (args, body) ->
            (e, collectFreeVars' free args body)
        | SymbolExpr s -> (e, s.sym::free)
        | _ -> foldExpr findFreeVars free e
    and collectFreeVars' free pats exprs =
        let pvars = List.collect patternVars pats
        let (_, evars) = findFreeVars (ListExpr exprs) []
        let free' = List.distinct (free @ evars)
        List.except pvars free'
    and collectFreeVars free bindings =
        let (pats, exprs) = List.unzip bindings
        collectFreeVars' free pats exprs

    module Patterns =
        let (|If|_|) es =
            match es with
            | (Symbol s)::test::ifTrue::rest when s.sym = "if" ->
                let ifFalse =
                    match rest with
                    | [] -> Option.None
                    | [ifFalse] -> Option.Some(ifFalse)
                    | _ -> failwithf "Malformed if expression: %s" <| (List es).ToString()
                Option.Some(test, ifTrue, ifFalse)
            | _ -> Option.None
        let (|Let|_|) = function
            | (Symbol s)::(List bindings)::body when s.sym = "let" ->
                Option.Some(bindings, body)
            | _ -> Option.None
        let (|Case|_|) = function
            | [ Symbol s; e; List arms ] when s.sym = "case" ->
                Option.Some(e, arms)
            | _ -> Option.None
        let (|Lambda|_|) = function
            | (Symbol s)::(List paramList)::body when s.sym = "lambda" ->
                Option.Some(paramList, body)
            | _ -> Option.None
            
    open Patterns
    
    let rec letBinding bindings body =
        let binding = function
            | List [p; e] ->
                state {
                    let! pat = pattern p
                    let! s = get
                    // Parse the contents of @e *before* adding contents of @pat to the list of bound variables.
                    let! e' = expr e
                    // Anything bound within @e is dropped (as it is out of scope inside the let-binding body).
                    do! put <| addBoundVars' (patternBindings pat) s
                    return LetBinding (pat, e')
                }
            | _ ->
                failwith "Invalid form for let-binding"
        state {
            let! s = get
            let! bindings = sequence <| List.map binding bindings
            let! body = sequence <| List.map expr body
            // Restore original state.
            do! put s
            return LetExpr (bindings, body)
        }
    and caseArm = function
        | List (p::es) ->
            state {
                let! s = get
                let! pat = pattern p
                let! es = sequence <| List.map expr es
                // Restore original state.
                do! put s
                return (pat, es)
            }
        | _ -> failwith "Expected case-arm"
    and lambda paramList body =
        state {
            let! pats = sequence <| List.map pattern paramList
            let! s = get
            do! addBoundVars (List.collect patternBindings pats)
            let! body = sequence <| List.map expr body
            // Restore original state.
            do! put s
            return LambdaExpr (pats, body)
        }
    and expr = function
        | Symbol sym ->
            (SymbolExpr << Ast.Binding) <@> (untagId sym.sym)
            // TODO: Builtin environment needs to be added to BoundVars before this will work.
//            state {
//                let! s = get
//                if s.BoundVars.Contains(sym) then
//                    let! untagged = untagId sym
//                    return SymbolExpr untagged
//                else
//                    return failwithf "Reference to undefined variable `%s'" sym
//            }
        | Quote q ->
            // Untag identifiers.
            (QuotedExpr << fst) <@> untagSyms q
        | List es ->
            match es with
            | If(test, ifTrue, ifFalse) ->
                state {
                    let! test = expr test
                    let! ifTrue = expr ifTrue
                    let! ifFalse =
                        match ifFalse with
                        | Option.Some(x) -> Option.Some <@> expr x
                        | Option.None -> inject Option.None
                    return IfExpr (test, ifTrue, ifFalse)
                }
            | Let(bindings, body) ->
                letBinding bindings body
            | Case(e, arms) ->
                state {
                    let! e = expr e
                    let! arms = sequence <| List.map caseArm arms
                    return CaseExpr (e, arms)
                }
            | Lambda(paramList, body) ->
                lambda paramList body
            | (Symbol s)::args ->
                state {
                    match! tryGetMacro s.sym with
                    | Option.Some(m) ->
                        let ld = m.Transformer <| ((Symbol s)::args)
                        return! expr ld
                    | Option.None ->
                        let! es = sequence <| List.map expr ((Symbol s)::args)
                        return ListExpr es
                }
            | es ->
                ListExpr <@> (sequence <| List.map expr es)
        | ConsCell (left, right) ->
            state {
                let! l = expr left
                let! r = expr right
                return ConsExpr (l, r)
            }
        | Ellipsis _ -> failwith "Ellipses only allowed in macro definitions"
        | x -> inject <| LiteralExpr x
    
    let private foldM (f: 'acc -> 'a -> State<'s, 'acc>) (s: State<'s, 'acc>) (xs: 'a list) : State<'s, 'acc> =
        let g = flip f
        List.fold (fun (s: State<'s, 'acc>) (x: 'a) -> (s >>= (g x))) s xs

    let defun defuns ld  =
        match ld with
        | List ((Symbol s)::(Symbol name)::(List paramList)::body) when s.sym = "defun" ->
            state {
                let! paramList = sequence <| List.map pattern paramList
                let! s = get
                do! addBoundVars <| List.collect patternBindings paramList
                let! body = sequence <| List.map expr body
                do! put s
                let thisDefun = (name.sym, paramList, body)
                do! addBoundVars [name]
                return (thisDefun::defuns)
            }
        | List ((Symbol s)::rest) when s.sym = "define-syntax" ->
            let m = Macros.Parsing.defineSyntax rest
            state {
                let! s = get
                let d = dict <| (m.Keyword, m)::(List.ofSeq <| s.Macros.KeyValuePairs())
                do! put { s with Macros = d }
                return defuns
            }
        | x ->
            failwithf "Not a defun or macro definition: %A" x
            // state {
            //     let! e = expr x
            //     let scope = Compilation.Builtins.scope
            //     let c = Compilation.compileExpr e
            //     do! inject <| printfn "%A" (c scope)
            //     return defuns
            // }

    let topLevel defuns =
        let parsed =
            foldM defun (inject <| []) defuns
        let (s, defuns) = runState parsed { Bindings = dict []; Macros = dict [] }
        (s.Macros, List.rev defuns)
