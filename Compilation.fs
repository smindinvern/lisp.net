module Compilation

    open Scope
    open Ast
    open Evaluation
    
    open System

    open smindinvern.State.Lazy
    
    type CompilerState = { Bindings: Scope }
    type Compiled = State<CompilerState, Scope -> (Scope * LispData)>

    open Parsing
    
    // Evaluate a list of expressions in sequence, preserving modifications made to the
    // dynamic environment.
    let sequenceExpressions (cexprs: (Scope -> (Scope * LispData)) list) (scope: Scope) =
        List.fold
            // Discard result of previous expression and evaluate the next one, threading
            // the current scope through the evaluation.
            (fun (scope, _) cexpr -> cexpr scope)
            // Start with the initial scope.  If the list is empty return 'nil.
            (scope, Symbol "nil")
            cexprs

    // Evaluate a list of expressions in sequence, discarding modifications made to the
    // dynamic environment.
    let evalExpressions (cexprs: (Scope -> (Scope * LispData)) list) (scope: Scope) =
        List.map (snd << ((|>) scope)) cexprs
    
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
    
    let addToScope (scope: Scope) (bindings: Binding list) =
        let bindings = List.map (fun (b: Binding) -> (b.sym, b)) bindings
        scope.FreshScope().AddRange(bindings)
    
    let runtimeLookup (b: Binding) (scope: Scope) =
        // First attempt to resolve the compile-time reference.
        match !b.ldr with
        | Option.Some(v) -> (scope, v)
        | Option.None ->
            // Attempt to lookup @s in the dynamic environment.  This is used only for lambda-captured values.
            match scope.LookupValue(b.sym) with
            | Option.Some(v) -> (scope, v)
            | Option.None -> failwithf "Compiler error: variable `%s' has not yet been assigned." b.sym
    
    let rec compileExpr (e: Expr) : Compiled =
        match e with
            | SymbolExpr s ->
                state {
                    let! st = get
                    match st.Bindings.Lookup(s) with
                    | Some(b) ->
                        match !b.ldr with
                        | Option.Some(v) -> return (fun scope -> (scope, v))
                        | Option.None -> return runtimeLookup b // Lazy initialization.
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
        let bindAtRuntime exprs body scope =
            let exprs = evalExpressions exprs scope
            ignore <| bindAll patterns exprs
            let (_, ld) = sequenceExpressions body scope
            (scope, ld)
        state {
            // FIXME: this makes this a letrec-binding.
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
        let rec eval (scope: Scope) (v: LispData) (carms: (Pattern * (Scope -> Scope * LispData) list) list) =
            // try binding @e to each pattern in @arms until we find a match
            match carms with
            | (p, cbody)::carms' ->
                match bindPattern p v with
                | Option.Some(bindings) ->
                    let (_, result) = sequenceExpressions cbody (addToScope scope bindings)
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
                match evalExpressions cs scope with
                | [] -> (scope, Ast.List [])
                | (Symbol f)::args ->
                    match scope.LookupValue(f) with
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
            do! put { s with Bindings = addToScope s.Bindings empties }
            return fun (scope: Scope) ->
                // Make a copy of each binding.
                let copies = List.map (fun (b: Binding) ->
                    // Check if this variable is captured by an outer lambda.
                    match scope.Lookup(b.sym) with
                    // If so, return the reference to the captured variable in the dynamic environment.
                    | Option.Some(b) -> b
                    // Otherwise, create a copy of the binding that refers to a different location.
                    | Option.None -> Binding(b.sym, !b.ldr)) captured
                // Insert into the dynamic environment.
                addToScope scope copies
        }
    and compileFunction (paramList: Pattern list) (body: Expr list) =
        state {
            let! s = get
            do! addPatternBindings paramList
            let! cbody = sequence <| List.map compileExpr body
            do! put s
            let bindArgs (scope: Scope) (args: LispData list) =
                ignore <| bindAll paramList args
                snd <| sequenceExpressions cbody scope
            return fun scope ->
                (scope, LispFunc (Func<LispData list, LispData>(bindArgs scope))) 
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
            return fun scope ->
                // Capture @freeVars
                let newScope = closure scope
                (scope, snd <| cfunc newScope)
        }
        
    let compileDefun (sym: string, paramList: ParamList, body: Expr list) : Compiled =
        state {
            // Insert an empty binding for @sym.  This allows for recursive function definitions.
            let b = Binding(sym)
            let! s = get
            do! put { s with Bindings = s.Bindings.Add(sym, b) }
            let! cfunc = compileFunction paramList body
            return fun scope ->
                // Insert empty binding to allow recursive references to @sym.
                let scope = scope.Add(b.sym, b)
                let (scope', cfunc') = cfunc <| scope
                // Update the binding to resolve to the compiled function.
                b.ldr := Option.Some(cfunc')
                (scope', cfunc')
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
