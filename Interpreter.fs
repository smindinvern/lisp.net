module Interpreter

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
    
    module Runtime =
        
        let ResolveBinding (b: Binding) : State<Scope, LispData> =
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
        let Cons head tail : State<Scope, LispData> =
            state {
                let! h = head
                let! t = tail
                match t with
                | Ast.List xs -> return Ast.List(h::xs)
                | _ -> return failwithf "Cannot cons %A and %A" h t
            }
        let LetBinding patterns exprs body : State<Scope, LispData> =
            state {
                let! exprs = evalExpressions exprs
                // NB: Mutating state.
                do ignore <| bindAll patterns exprs
                return! sequenceExpressions body
            }
        let rec Case (v: LispData) (carms: (Pattern * State<Scope, LispData> list) list) : State<Scope, LispData> =
            state {
                let! s = get
                // try binding @v to each pattern in @carms until we find a match
                match carms with
                | (p, cbody)::carms' ->
                    match bindPattern p v with
                    | Option.Some(bindings) ->
                        do! modify (fun scope -> addToScope bindings scope)
                        let! result = sequenceExpressions cbody
                        do! put s
                        return result
                    | Option.None -> return! Case v carms'
                | [] -> return failwith "No match in case expression"
            }
        let LispList cs : State<Scope, LispData> =
            state {
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
        let If test ifTrue ifFalse : State<Scope, LispData> =
            state {
                let! result = discard test
                if result <> (Symbol "nil") then
                    return! ifTrue
                else
                    return! ifFalse
            }
        let Closure captured : State<Scope, unit> =
            state {
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
        let Function paramList cbody : State<Scope, LispData> =
            let bindArgs (scope: Scope) (args: LispData list) =
                // NB: Mutating state.
                do ignore <| bindAll paramList args
                snd <| runState (sequenceExpressions cbody) scope
            state {
                let! scope = get
                return LispFunc (Func<LispData list, LispData>(bindArgs scope))
            }
        let Lambda closure cfunc : State<Scope, LispData> =
            state {
                let! scope = get
                // Capture values.
                do! closure
                let! result = cfunc
                do! put scope
                return result
            }
        let Defun (b: Binding) cfunc : State<Scope, LispData> =
            state {
                // Insert binding into the dynamic scope so that it can be looked up and invoked.
                do! modify (fun (scope: Scope) -> scope.Add(b.sym, b))
                let! cfunc' = cfunc
                // Update the binding to resolve to the compiled function.
                // NB: Mutating state.
                b.ldr := Option.Some(cfunc')
                return cfunc'
            }
    
    module Compile =
        
        let rec Expr (e: Expr) : Compiled =
            match e with
                | SymbolExpr s ->
                    state {
                        let! st = get
                        match st.Bindings.Lookup(s) with
                        | Some(b) ->
                            match !b.ldr with
                            | Option.Some(v) -> return inject v  // Compile-time constant
                            | Option.None -> return Runtime.ResolveBinding b
                        | None -> return failwithf "Attempt to use free variable: %s" s
                    }
                | LiteralExpr l -> inject <| inject l
                | ListExpr es ->
                    ListExpr es
                | LetExpr (bindings, es) -> LetExpr (bindings, es)
                | CaseExpr (p, arms) -> CaseExpr p arms
                | IfExpr (test, ifTrue, ifFalse) -> IfExpr test ifTrue ifFalse
                | QuotedExpr q -> Quoted q
                | ConsExpr (head, tail) ->
                    state {
                        let! hc = Expr head
                        let! tc = Expr tail
                        return Runtime.Cons hc tc
                    }
                | LambdaExpr (parms, body) ->
                    Lambda parms body
        and LetExpr (bindings: LetBinding list, es: Expr list) : Compiled =
            let (patterns, exprs) = List.unzip bindings
            state {
                let! exprs' = sequence <| List.map Expr exprs
                let! s = get
                do! addPatternBindings patterns
                let! body = sequence <| List.map Expr es
                do! put s
                return Runtime.LetBinding patterns exprs' body
            }
        and CaseArm (p: Pattern, es: Expr list) =
            state {
                let! s = get
                do! addPatternBindings [p]
                let! result = sequence <| List.map Expr es
                do! put s
                return (p, result)
            }
        and CaseExpr (e: Expr) (arms: (Pattern * Expr list) list) =
            state {
                let! carms = sequence <| List.map CaseArm arms
                let! ce = Expr e
                return state {
                    let! v = discard ce
                    return! Runtime.Case v carms
                }
            }
        and ListExpr (es: Expr list) : Compiled =
            state {
                let! cs = sequence <| List.map Expr es
                return Runtime.LispList cs
            }
        and IfExpr (test: Expr) (ifTrue: Expr) (ifFalse: Expr option) : Compiled =
            state {
                let! ifFalse' =
                    Expr (
                        match ifFalse with
                        | Some(x) -> x
                        | None -> SymbolExpr "nil")
                let! ifTrue' = Expr ifTrue
                let! test' = Expr test
                return Runtime.If test' ifTrue' ifFalse'
            }
        and Quoted (q: LispData) : Compiled =
            inject <| inject q
        and Closure (captureList: string list) =
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
                return Runtime.Closure captured
            }
        and Function (paramList: Pattern list) (body: Expr list) : State<CompilerState, State<Scope, LispData>> =
            state {
                let! s = get
                do! addPatternBindings paramList
                let! cbody = sequence <| List.map Expr body
                do! put s
                return Runtime.Function paramList cbody
            }
        and Lambda (paramList: Pattern list) (body: Expr list) =
            let (_, freeVars) = findFreeVars (Ast.ListExpr body) []
            let patVars = List.collect patternVars paramList
            let freeVars = List.except patVars freeVars
            state {
                let! s = get
                let! closure = Closure freeVars
                let! cfunc = Function paramList body
                do! put s
                return Runtime.Lambda closure cfunc
            }
        
        let Defun (sym: string, paramList: ParamList, body: Expr list) : Compiled =
            state {
                // Insert an empty binding for @sym.  This allows for recursive function definitions.
                let b = Binding(sym)
                let! s = get
                do! put { s with Bindings = s.Bindings.Add(sym, b) }
                let! cfunc = Function paramList body
                return Runtime.Defun b cfunc
            }
        
    open Environment
        
    let scope : Scope = Scope([dict (List.map (fun (k, v: LispData) -> (k, Binding(k, v))) Builtins)])
    
    let compileTopLevel (t: TopLevel) : Scope =
        let compiled = sequence <| List.map Compile.Defun t
        let (_, compiled) = runState compiled { Bindings = scope }
        fst <| runState (sequence compiled) scope
