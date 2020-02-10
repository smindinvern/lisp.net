module Compilation

    open Scope
    open Ast
    open Evaluation
    
    open System

    open smindinvern.State.Lazy
    open smindinvern.Utils
    
    type CompilerState = { Bindings: Scope }
    type Compiled = State<CompilerState, State<Scope, LispData>>

    open Parsing
    
    // Evaluate a list of expressions in sequence, preserving modifications made to the
    // dynamic environment.
    let sequenceExpressions cexprs : State<Scope, LispData> =
        foldM (flip konst) (Symbol "nil") cexprs

    // Evaluate a list of expressions in sequence, discarding modifications made to the
    // dynamic environment.
    let evalExpressions (cexprs: State<Scope, LispData> list) =
        sequence <| List.map discard cexprs
    
    // Extract and return all Bindings from a Pattern as a list of key-value pairs.
    let getPatternBindings (ps: Pattern list) =
        List.map (fun (b: Binding) -> (b.sym, b)) <| Parsing.patternBindings (ListPattern ps)
    
    // Extract all Bindings from a list of Patterns and add them to the set of bindings
    // for the current compilation.
    let addPatternBindings (ps: Pattern list) =
        let bindings = getPatternBindings ps
        modify (fun s -> { s with Bindings = s.Bindings.FreshScope().AddRange(bindings) })

    // Bind a list of LispData to a list of Patterns, mutating the underlying
    // reference cell contents of each Binding.
    let bindAll (p: Pattern list) (args: LispData list) =
        match bindPattern (ListPattern p) (Ast.List args) with
        | Option.Some(bindings) ->
            bindings
        | Option.None ->
            failwith "Binding failed"
    
    let addToScope (bindings: Binding list) (scope: Scope) =
        let bindings = List.map (fun (b: Binding) -> (b.sym, b)) bindings
        scope.FreshScope().AddRange(bindings)
    
    let runtimeLookup (b: Binding) : State<Scope, LispData> =
        state {
            // This needs to go first.  Otherwise the match expression below will be executed
            // outside of the computation expression.
            let! scope = get
            // First attempt to resolve the compile-time reference.
            match !b.ldr with
            | Option.Some(v) -> return v
            | Option.None ->
                // Attempt to lookup @s in the dynamic environment.  This is used only for lambda-captured values.
                match scope.LookupValue(b.sym) with
                | Option.Some(v) -> return v
                | Option.None ->
                    return failwithf "Compiler error: variable `%s' has not yet been assigned." b.sym
        }
    
    let rec compileExpr (e: Expr) : Compiled =
        match e with
            | SymbolExpr s ->
                state {
                    let! st = get
                    match st.Bindings.Lookup(s) with
                    | Some(b) ->
                        match !b.ldr with
                        | Option.Some(v) -> return inject v
                        | Option.None -> return runtimeLookup b // Lazy initialization.
                    | None -> return failwithf "Attempt to use free variable: %s" s
                }
            | LiteralExpr l -> inject <| inject l
            | ListExpr es ->
                compileListExpr es
            | LetExpr (bindings, es) -> compileLetExpr (bindings, es)
            | CaseExpr (p, arms) -> compileCaseExpr p arms
            | IfExpr (test, ifTrue, ifFalse) -> compileIfExpr test ifTrue ifFalse
            | QuotedExpr q -> compileQuoted q
            | ConsExpr (head, tail) ->
                let f hc tc =
                    state {
                        let! h = hc
                        let! t = tc
                        match t with
                        | Ast.List xs -> return Ast.List(h::xs)
                        | _ -> return failwithf "Cannot cons %A and %A" h t
                    }
                state {
                    let! hc = compileExpr head
                    let! tc = compileExpr tail
                    return f hc tc
                }
            | LambdaExpr (parms, body) ->
                compileLambda parms body
    and compileLetExpr (bindings: LetBinding list, es: Expr list) : Compiled =
        let (patterns, exprs) = List.unzip bindings
        let bindAtRuntime exprs body =
            state {
                let! exprs = evalExpressions exprs
                // NB: Mutating state.
                do ignore <| bindAll patterns exprs
                return! sequenceExpressions body
            }
        state {
            let! exprs' = sequence <| List.map compileExpr exprs
            let! s = get
            do! addPatternBindings patterns
            let! body = sequence <| List.map compileExpr es
            do! put s
            return bindAtRuntime exprs' body
        }
    and compileCaseArm (p: Pattern, es: Expr list) =
        state {
            let! s = get
            do! addPatternBindings [p]
            let! result = sequence <| List.map compileExpr es
            do! put s
            return (p, result)
        }
    and compileCaseExpr (e: Expr) (arms: (Pattern * Expr list) list) =
        let rec eval (v: LispData) (carms: (Pattern * State<Scope, LispData> list) list) =
            state {
                let! s = get
                // try binding @e to each pattern in @arms until we find a match
                match carms with
                | (p, cbody)::carms' ->
                    match bindPattern p v with
                    | Option.Some(bindings) ->
                        do! modify (fun scope -> addToScope bindings scope)
                        let! result = sequenceExpressions cbody
                        do! put s
                        return result
                    | Option.None -> return! eval v carms'
                | [] -> return failwith "No match in case expression"
            }
        state {
            let! carms = sequence <| List.map compileCaseArm arms
            let! ce = compileExpr e
            return state {
                let! v = discard ce
                return! eval v carms
            }
        }
    and compileListExpr (es: Expr list) : Compiled =
        state {
            let! cs = sequence <| List.map compileExpr es
            return state {
                let! scope = get
                let! evaled = evalExpressions cs
                match evaled with
                | [] -> return Ast.List []
                | (Symbol f)::args ->
                    match scope.LookupValue(f) with
                        | Some(LispFunc func) -> return func.Invoke(args)
                        | _ -> return failwith <| sprintf "%s is not a callable object" f
                | (LispFunc func)::args ->
                    return func.Invoke(args)
                | x::_ -> return failwith <| sprintf "%A is not a callable object" x
            }
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
            return state {
                let! result = discard test'
                if result <> (Symbol "nil") then
                    return! ifTrue'
                else
                    return! ifFalse'
            }
        }
    and compileQuoted (q: LispData) : Compiled =
        inject <| inject q
    and compileClosure (captureList: string list) =
        state {
            let! s = get
            let captured = List.map (fun sym ->
                match s.Bindings.Lookup(sym) with
                | Option.Some(b) -> b
                | Option.None -> failwithf "Reference to free variable `%s'" sym) captureList
            // Temporarily insert empty bindings for captured variables so that they won't be
            // resolved to anything, forcing a lookup in the dynamic environment.
            let empties = List.map (fun sym -> Binding(sym)) captureList
            do! put { s with Bindings = addToScope empties s.Bindings }
            return state {
                // This needs to go first.  Otherwise the let-binding below will be executed
                // outside of the computation expression.
                let! (scope: Scope) = get
                // Make a copy of each binding.
                let copies = List.map (fun (b: Binding) ->
                    // Check if this variable is captured by an outer lambda.
                    match scope.Lookup(b.sym) with
                    // If so, return the reference to the captured variable in the dynamic environment.
                    | Option.Some(b) -> b
                    // Otherwise, create a copy of the binding that refers to a different location.
                    | Option.None -> Binding(b.sym, !b.ldr)) captured
                // Insert into the dynamic environment.
                do! put (addToScope copies scope)
            }
        }
    and compileFunction (paramList: Pattern list) (body: Expr list) : State<CompilerState, State<Scope, LispData>> =
        state {
            let! s = get
            do! addPatternBindings paramList
            let! cbody = sequence <| List.map compileExpr body
            do! put s
            let bindArgs (scope: Scope) (args: LispData list) =
                // NB: Mutating state.
                do ignore <| bindAll paramList args
                snd <| runState (sequenceExpressions cbody) scope
            return state {
                let! scope = get
                return LispFunc (Func<LispData list, LispData>(bindArgs scope))
            }
        }
    and compileLambda (paramList: Pattern list) (body: Expr list) =
        let (_, freeVars) = findFreeVars (ListExpr body) []
        let patVars = List.collect patternVars paramList
        let freeVars = List.except patVars freeVars
        state {
            let! s = get
            let! closure = compileClosure freeVars
            let! cfunc = compileFunction paramList body
            do! put s
            return state {
                let! scope = get
                // Capture @freeVars
                do! closure
                let! result = cfunc
                do! put scope
                return result
            }
        }
        
    let compileDefun (sym: string, paramList: ParamList, body: Expr list) : Compiled =
        state {
            // Insert an empty binding for @sym.  This allows for recursive function definitions.
            let b = Binding(sym)
            let! s = get
            do! put { s with Bindings = s.Bindings.Add(sym, b) }
            let! cfunc = compileFunction paramList body
            return state {
                // Insert binding into the dynamic scope so that it can be looked up and invoked.
                do! modify (fun (scope: Scope) -> scope.Add(b.sym, b))
                let! cfunc' = cfunc
                // Update the binding to resolve to the compiled function.
                // NB: Mutating state.
                b.ldr := Option.Some(cfunc')
                return cfunc'
            }
        }
        
    open Environment
        
    let scope : Scope = Scope([dict (List.map (fun (k, v: LispData) -> (k, Binding(k, v))) Builtins)])
    
    let compileTopLevel (t: TopLevel) : Scope =
        let f (sym: string, ld: LispData) =
            (sym, Binding(sym, ld))
        let environment = List.map f Builtins
        let compiled = sequence <| List.map compileDefun t
        let (x, compiled) = runState compiled { Bindings = Scope([dict environment]) }
        fst <| runState (sequence compiled) scope
