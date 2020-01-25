module Parsing

    open Ast
    open Macros
    open Macros.Types
    open Macros.Parsing
    open Extensions

    open System.Collections.Generic

    open smindinvern.State.Lazy
    open smindinvern.Utils
    
    type ParserState = { BoundVars: HashSet<string>
                       ; Macros: IDictionary<string, Macro>
                       }

    type ExprParser<'a> = State<ParserState, 'a>

    let untagId' (boundVars: HashSet<string>) (sym: string) =
        if sym.Contains('#') then
            if boundVars.Contains(sym) then
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
            return untagId' s.BoundVars sym
        }

    let rec internal untagSyms' boundVars ld () =
        match ld with
            | Symbol s -> (Symbol <| untagId' boundVars s, ())
            | x -> foldLispData (untagSyms' boundVars) () x

    let untagSyms ld =
        state {
            let! s = get
            return untagSyms' s.BoundVars ld ()
        }

    // TODO: optimize this.
    let tryGetMacro (m: string) : ExprParser<Macro option> =
        state {
            let! s = get
            if s.Macros.ContainsKey(m) then
                return Some <| s.Macros.[m]
            else
                return None
        }

    let isBoundVar (v: string) : ExprParser<bool> =
        state {
            let! s = get
            return s.BoundVars.Contains(v)
        }

    let internal addBoundVars' vs ps =
        let boundVarsSeq = Seq.cast ps.BoundVars
        let boundVars' = new HashSet<string>(Seq.append boundVarsSeq (Seq.ofList vs))
        { ps with BoundVars = boundVars' }

    let addBoundVars (vs: string list) : ExprParser<unit> =
        modify (addBoundVars' vs)

    let rec pattern = function
        | Symbol sym ->
            inject <| SymbolPattern (Ast.Binding(sym))
        | ConsCell (left, right) ->
            state {
                let! l = pattern left
                let! r = pattern right
                return ConsPattern (l, r)
            }
        | List ((Symbol s)::pats) ->
            state {
                match! tryGetMacro s with
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

    let rec patternVars = function
        | SymbolPattern b -> [b.sym]
        | ConsPattern (l, r) -> (patternVars l) @ (patternVars r)
        | ListPattern pats -> List.collect patternVars pats
        | Pattern.LiteralPattern _ -> []

    let rec letBinding bindings body =
        let binding = function
            | List [p; e] ->
                state {
                    let! pat = pattern p
                    let! s = get
                    // Parse the contents of @e *before* adding contents of @pat to the list of bound variables.
                    let! e' = expr e
                    // Anything bound within @e is dropped (as it is out of scope inside the let-binding body).
                    do! put <| addBoundVars' (patternVars pat) s
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
            do! addBoundVars (List.collect patternVars pats)
            let! body = sequence <| List.map expr body
            // Restore original state.
            do! put s
            return LambdaExpr (pats, body)
        }
    and expr = function
        | Symbol sym ->
            SymbolExpr <@> untagId sym
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
                | (Symbol "if")::test::ifTrue::rest ->
                    let ifFalse =
                        match rest with
                        | [] -> inject Option.None
                        | [ifFalse] ->
                            Option.Some <@> expr ifFalse
                        | _ -> failwithf "Malformed if expression: %s" <| (List es).ToString()
                    state {
                        let! test = expr test
                        let! ifTrue = expr ifTrue
                        let! ifFalse = ifFalse
                        return IfExpr (test, ifTrue, ifFalse)
                    }
                | (Symbol "let")::(List bindings)::body ->
                    letBinding bindings body
                | [ Symbol "case"; e; List arms ] ->
                    state {
                        let! e = expr e
                        let! arms = sequence <| List.map caseArm arms
                        return CaseExpr (e, arms)
                    }
                | (Symbol "lambda")::(List paramList)::body ->
                    lambda paramList body
                | (Symbol s)::args ->
                    state {
                        match! tryGetMacro s with
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
        | Ellipsis e -> failwith "Ellipses only allowed in macro definitions"
        | x -> inject <| LiteralExpr x

    let private foldM (f: 'acc -> 'a -> State<'s, 'acc>) (s: State<'s, 'acc>) (xs: 'a list) : State<'s, 'acc> =
        let g = flip f
        List.fold (fun (s: State<'s, 'acc>) (x: 'a) -> (s >>= (g x))) s xs

    let defun defuns ld  =
        match ld with
        | List ((Symbol "defun")::(Symbol name)::(List paramList)::body) ->
            state {
                let! paramList = sequence <| List.map pattern paramList
                let! s = get
                do! addBoundVars <| List.collect patternVars paramList
                let! body = sequence <| List.map expr body
                do! put s
                let thisDefun = (name, paramList, body)
                do! addBoundVars [name]
                return (thisDefun::defuns)
            }
        | List ((Symbol "define-syntax")::rest) ->
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
        let (s, defuns) = runState parsed { BoundVars = new HashSet<string>(); Macros = dict [] }
        (s.Macros, List.rev defuns)
