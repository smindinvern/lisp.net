module Compilation

    open Scope
    open Ast
    open Evaluation
    
    open System

    type Compiled = Scope -> (Scope * LispData)

    open Macros.Extensions

    open System.Collections.Generic
    
    let rec evalCompiledList (scope: Scope) =
        function
            | [] -> (scope, Symbol "nil")
            | [last] -> last scope
            | head::tail ->
                let (scope', _) = head scope
                evalCompiledList scope' tail
    
    let bindAll (p: Pattern list) (args: LispData list) =
        bindPattern (ListPattern p) (Ast.List args)
    
    let addToScope (scope: Scope) (bindings: Binding list) =
        let newScope = new Dictionary<string, LispData>(dict bindings)
        newScope::scope
    
    let bindInNewScope (p: Pattern list) (args: LispData list) =
        match bindAll p args with
            | None ->
                failwith "Binding failed"
            | Some(bindings) ->
                new Dictionary<string, LispData>(dict bindings)
    
    let rec compileExpr (e: Expr) : Compiled =
        match e with
            | SymbolExpr s ->
                fun scope ->
                    match lookup s scope with
                        | Some(obj) -> (scope, obj)
                        | None -> failwith <| sprintf "Attempt to use free variable: %s" s
            | LiteralExpr l -> fun x -> (x, l)
            | ListExpr es ->
                compileListExpr es
            | LetExpr (bindings, es) -> compileLetExpr (bindings, es)
            | CaseExpr (p, arms) -> compileCaseExpr p arms
            | IfExpr (test, ifTrue, ifFalse) -> compileIfExpr test ifTrue ifFalse
            | QuotedExpr q -> compileQuoted q
            | ConsExpr (head, tail) ->
                let hc = compileExpr head
                let tc = compileExpr tail
                fun scope ->
                    let (scope, h) = hc scope
                    let (scope, t) = tc scope
                    match t with
                        | Ast.List xs -> (scope, Ast.List (h::xs))
                        | _ -> failwith <| sprintf "Cannot cons %A and %A" h t
            | LambdaExpr (parms, body) ->
                compileLambda parms body
    and compileLetExpr (bindings: LetBinding list, es: Expr list) : Compiled =
        let (patterns, exprs) = List.unzip bindings
        let exprs' = List.map compileExpr exprs
        let body = List.map compileExpr es
        fun scope ->
            let exprs'' = List.map (snd << ((|>) scope)) exprs'
            let newScope = (bindInNewScope patterns exprs'')::scope
            let (newScope', obj) = evalCompiledList newScope body
            (List.tail newScope', obj)
    and compileCaseExpr (e: Expr) (arms: (Pattern * Expr list) list) =
        let carms = List.map (fun (p, body) -> (p, List.map compileExpr body)) arms
        let ce = compileExpr e
        let rec eval (scope: Scope) (v: LispData) (carms: (Pattern * Compiled list) list) =
            // try binding @e to each pattern in @arms until we find a match
            match carms with
            | (p, cbody)::carms' ->
                match bindPattern p v with
                | Option.Some(bindings) ->
                    let (_, result) = evalCompiledList (addToScope scope bindings) cbody
                    (scope, result)
                | Option.None -> eval scope v carms'
            | [] -> failwith "No match in case expression"
        fun scope ->
            let (_, v) = ce scope
            eval scope v carms

    and compileListExpr (es: Expr list) : Compiled =
        let cs = List.map compileExpr es
        fun scope ->
            match List.map (snd << ((|>) scope)) cs with
                | [] -> (scope, Ast.List [])
                | (Symbol f)::args ->
                    match lookup f scope with
                        | Some(LispFunc func) -> (scope, func.Invoke(args))
                        | _ -> failwith <| sprintf "%s is not a callable object" f
                | (LispFunc func)::args ->
                    (scope, func.Invoke(args))
                | x::_ -> failwith <| sprintf "%A is not a callable object" x
    and compileIfExpr (test: Expr) (ifTrue: Expr) (ifFalse: Expr option) : Compiled =
        let ifFalse' =
            compileExpr <|
            match ifFalse with
                | Some(x) -> x
                | None -> SymbolExpr "nil"
        let ifTrue' = compileExpr ifTrue
        let test' = compileExpr test
        fun scope ->
            if (snd <| test' scope) <> (Symbol "nil") then
                ifTrue' scope
            else
                ifFalse' scope
    and compileQuoted (q: LispData) : Compiled =
        fun scope -> (scope, q)
    and compileLambda (paramList: Pattern list) (body: Expr list) =
        let cbody = List.map compileExpr body
        let f (scope: Scope) (args: LispData list) =
            let newScope = (bindInNewScope paramList args)::scope
            snd <| evalCompiledList newScope cbody
        fun scope ->
            (scope, LispFunc (new Func<LispData list, LispData>(f scope)))
    
    let compileDefun (s: string, paramList: ParamList, body: Expr list) : Compiled =
        let clambda = compileLambda paramList body
        fun scope ->
            let (scope', cfunc) = clambda scope
            (Scope.add (s, cfunc) scope', cfunc)

    open Environment
        
    let scope : Scope = [new System.Collections.Generic.Dictionary<string, LispData>(dict Builtins)]
    
    let compileTopLevel (t: TopLevel) : Scope =
        let compiled = List.map compileDefun t
        List.fold (fun s c -> fst <| c s) scope compiled
