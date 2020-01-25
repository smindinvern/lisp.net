module Compilation

    open Scope
    open Ast
    open Evaluation
    
    open System

    open System.Collections.Generic
    open smindinvern.State.Lazy
    
    type CompilerState = { Bindings: Scope }
    type Compiled = State<CompilerState, Scope -> (Scope * LispData)>

    open Extensions
    
    let addToDict (d: IDictionary<'k, 'v>) (k: 'k, v: 'v) =
        dict <| Seq.append (Seq.singleton (k, v)) (d.KeyValuePairs())
    
    let rec evalCompiledList (scope: Scope) =
        function
            | [] -> (scope, Symbol "nil")
            | [last] -> last scope
            | head::tail ->
                let (scope', _) = head scope
                evalCompiledList scope' tail
    
    let rec addPatternBindings (p: Pattern) : State<CompilerState, unit> =
        state {
            let! s = get
            match p with
            | SymbolPattern b ->
                do! put { s with Bindings = s.Bindings.Add(b.sym, b) }
            | ListPattern ps ->
                do! addAllPatternBindings ps
            | ConsPattern (head, tail) ->
                do! addAllPatternBindings [head; tail]
            | LiteralPattern _ -> return ()
        }
    and addAllPatternBindings (ps: Pattern list) =
        ignore <@> (sequence <| List.map addPatternBindings ps)
    
    let bindAll (p: Pattern list) (args: LispData list) =
        match bindPattern (ListPattern p) (Ast.List args) with
        | Option.Some(bindings) ->
            bindings
        | Option.None ->
            failwith "Binding failed"
    
    let addToScope (scope: Scope) (bindings: Binding list) =
        let bindings = List.map (fun (b: Binding) -> (b.sym, b)) bindings
        scope.FreshScope().AddRange(bindings)

    let bindInNewScope (p: Pattern list) (args: LispData list) (scope: Scope) =
        scope.FreshScope().AddRange(List.map (fun (b: Binding) -> (b.sym, b)) (bindAll p args))
    
    let rec compileExpr (e: Expr) : Compiled =
        match e with
            | SymbolExpr s ->
                let f (v: LispData option ref) scope =
                    match !v with
                    | Option.Some(v) -> (scope, v)
                    | Option.None -> failwithf "Compiler error: variable `%s' has not yet been assigned." s
                state {
                    let! st = get
                    match st.Bindings.Lookup(s) with
                    | Some(b) ->
                        match !b.ldr with
                        | Option.Some(v) -> return (fun scope -> (scope, v))
                        | Option.None -> return f b.ldr  // Lazy initialization. 
                    // TODO: fall back to looking up `s' in the dynamic environment?
                    | None -> return failwithf "Attempt to use free variable: %s" s
                }
            | LiteralExpr l -> inject <| fun x -> (x, l)
            | ListExpr es ->
                compileListExpr es
            | LetExpr (bindings, es) -> compileLetExpr (bindings, es)
            | CaseExpr (p, arms) -> compileCaseExpr p arms
            | IfExpr (test, ifTrue, ifFalse) -> compileIfExpr test ifTrue ifFalse
            | QuotedExpr q -> compileQuoted q
            | ConsExpr (head, tail) ->
                let f hc tc scope =
                    let (scope, h) = hc scope
                    let (scope, t) = tc scope
                    match t with
                        | Ast.List xs -> (scope, Ast.List (h::xs))
                        | _ -> failwith <| sprintf "Cannot cons %A and %A" h t
                state {
                    let! hc = compileExpr head
                    let! tc = compileExpr tail
                    return f hc tc
                }
            | LambdaExpr (parms, body) ->
                compileLambda parms body
    and compileLetExpr (bindings: LetBinding list, es: Expr list) : Compiled =
        let (patterns, exprs) = List.unzip bindings
        let f exprs body scope =
            let exprs = List.map (snd << ((|>) scope)) exprs
            let newScope = bindInNewScope patterns exprs scope
            let (newScope', ld) = evalCompiledList newScope body
            (newScope'.PopScope(), ld)
        state {
            let! exprs' = sequence <| List.map compileExpr exprs
            let! s = get
            do! put { s with Bindings = s.Bindings.FreshScope() }
            do! addAllPatternBindings patterns
            let! body = sequence <| List.map compileExpr es
            do! put s
            return f exprs' body
        }
    and compileCaseArm (p: Pattern, es: Expr list) =
        state {
            let! s = get
            do! put { s with Bindings = s.Bindings.FreshScope() }
            do! addPatternBindings p
            let! result = sequence <| List.map compileExpr es
            do! put s
            return (p, result)
        }
    and compileCaseExpr (e: Expr) (arms: (Pattern * Expr list) list) =
        let rec eval (scope: Scope) (v: LispData) (carms: (Pattern * (Scope -> Scope * LispData) list) list) =
            // try binding @e to each pattern in @arms until we find a match
            match carms with
            | (p, cbody)::carms' ->
                match bindPattern p v with
                | Option.Some(bindings) ->
                    let (_, result) = evalCompiledList (addToScope scope bindings) cbody
                    (scope, result)
                | Option.None -> eval scope v carms'
            | [] -> failwith "No match in case expression"
        state {
            let! carms = sequence <| List.map compileCaseArm arms
            let! ce = compileExpr e
            return fun scope ->
                let (_, v) = ce scope
                eval scope v carms
        }
    and compileListExpr (es: Expr list) : Compiled =
        state {
            let! cs = sequence <| List.map compileExpr es
            return fun scope ->
                match List.map (snd << ((|>) scope)) cs with
                | [] -> (scope, Ast.List [])
                | (Symbol f)::args ->
                    match Option.bind (fun (b: Binding) -> !b.ldr) <| scope.Lookup(f) with
                        | Some(LispFunc func) -> (scope, func.Invoke(args))
                        | _ -> failwith <| sprintf "%s is not a callable object" f
                | (LispFunc func)::args ->
                    (scope, func.Invoke(args))
                | x::_ -> failwith <| sprintf "%A is not a callable object" x
        }
    and compileIfExpr (test: Expr) (ifTrue: Expr) (ifFalse: Expr option) : Compiled =
        state {
            let! ifFalse' =
                compileExpr (
                    match ifFalse with
                    | Some(x) -> x
                    | None -> SymbolExpr "nil")
            let! ifTrue' = compileExpr ifTrue
            let! test' = compileExpr test
            return fun scope ->
                if (snd <| test' scope) <> (Symbol "nil") then
                    ifTrue' scope
                else
                    ifFalse' scope
        }
    and compileQuoted (q: LispData) : Compiled =
        inject <| fun scope -> (scope, q)
    and compileLambda (paramList: Pattern list) (body: Expr list) =
        state {
            let! s = get
            do! put { s with Bindings = s.Bindings.FreshScope() }
            do! addAllPatternBindings paramList
            let! cbody = sequence <| List.map compileExpr body
            do! put s
            let f (scope: Scope) (args: LispData list) =
                let newScope = bindInNewScope paramList args scope
                snd <| evalCompiledList newScope cbody
            return fun scope ->
                (scope, LispFunc (Func<LispData list, LispData>(f scope)))
        }
        
    let compileDefun (sym: string, paramList: ParamList, body: Expr list) : Compiled =
        state {
            // Insert an empty binding for @sym.  This allows for recursive function definitions.
            let b = Binding(sym)
            let! s = get
            do! put { s with Bindings = s.Bindings.Add(sym, b) }
            let! clambda = compileLambda paramList body
            return fun scope ->
                let (scope', cfunc) = clambda scope
                // Update the binding to resolve to the compiled function.
                b.ldr := Option.Some(cfunc)
                (scope'.Add (b.sym, b), cfunc)
        }
        
    open Environment
        
    let scope : Scope = Scope([dict (List.map (fun (k, v: LispData) -> (k, Binding(k, v))) Builtins)])
    
    let compileTopLevel (t: TopLevel) : Scope =
        let f (sym: string, ld: LispData) =
            (sym, Binding(sym, ld))
        let environment = List.map f Builtins
        let compiled = sequence <| List.map compileDefun t
        let (x, compiled) = runState compiled { Bindings = Scope([dict environment]) } 
        List.fold (fun s c -> fst <| c s) scope compiled
