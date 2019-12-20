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
    
    let rec compileExpr (macros: IDictionary<string, Macros.Types.Macro>) (e: Expr) : Compiled =
        match e with
            | SymbolExpr s ->
                fun scope ->
                    match lookup s scope with
                        | Some(obj) -> (scope, obj)
                        | None -> failwith <| sprintf "Attempt to use free variable: %s" s
            | LiteralExpr l -> fun x -> (x, l)
            | ListExpr es ->
                match es with
                    | (SymbolExpr keyword)::args ->
                        match macros.tryGetValue(keyword) with
                            | Option.Some(macro) ->
                                let ld = macro.Transformer <| List.map exprToData es
                                compileExpr macros (Parsing.expr ld)
                            | Option.None -> compileListExpr macros es
                    | _ -> compileListExpr macros es
            | LetExpr (bindings, es) -> compileLetExpr macros (bindings, es)
            | CaseExpr (p, arms) -> compileCaseExpr macros p arms
            | IfExpr (test, ifTrue, ifFalse) -> compileIfExpr macros test ifTrue ifFalse
            | QuotedExpr q -> compileQuoted q
            | ConsExpr (head, tail) ->
                let hc = compileExpr macros head
                let tc = compileExpr macros tail
                fun scope ->
                    let (scope, h) = hc scope
                    let (scope, t) = tc scope
                    match t with
                        | Ast.List xs -> (scope, Ast.List (h::xs))
                        | _ -> failwith <| sprintf "Cannot cons %A and %A" h t
            | LambdaExpr (parms, body) ->
                compileLambda macros parms body
    and compileLetExpr (macros: IDictionary<string, Macros.Types.Macro>) (bindings: LetBinding list, es: Expr list) : Compiled =
        let (patterns, exprs) = List.unzip bindings
        let exprs' = List.map (compileExpr macros) exprs
        let body = List.map (compileExpr macros) es
        fun scope ->
            let exprs'' = List.map (snd << ((|>) scope)) exprs'
            let newScope = (bindInNewScope patterns exprs'')::scope
            let (newScope', obj) = evalCompiledList newScope body
            (List.tail newScope', obj)
    and compileCaseExpr (macros: IDictionary<string, Macros.Types.Macro>) (e: Expr) (arms: (Pattern * Expr list) list) =
        let carms = List.map (fun (p, body) -> (p, List.map (compileExpr macros) body)) arms
        let ce = compileExpr macros e
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

    and compileListExpr (macros: IDictionary<string, Macros.Types.Macro>) (es: Expr list) : Compiled =
        let cs = List.map (compileExpr macros) es
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
    and compileIfExpr (macros: IDictionary<string, Macros.Types.Macro>) (test: Expr) (ifTrue: Expr) (ifFalse: Expr option) : Compiled =
        let ifFalse' =
            compileExpr macros <|
            match ifFalse with
                | Some(x) -> x
                | None -> SymbolExpr "nil"
        let ifTrue' = compileExpr macros ifTrue
        let test' = compileExpr macros test
        fun scope ->
            if (snd <| test' scope) <> (Symbol "nil") then
                ifTrue' scope
            else
                ifFalse' scope
    and compileQuoted (q: Expr) : Compiled =
        fun scope -> (scope, exprToData q)
    and compileLambda (macros: IDictionary<string, Macros.Types.Macro>) (paramList: Pattern list) (body: Expr list) =
        let cbody = List.map (compileExpr macros) body
        let f (scope: Scope) (args: LispData list) =
            let newScope = (bindInNewScope paramList args)::scope
            snd <| evalCompiledList newScope cbody
        fun scope ->
            (scope, LispFunc (new Func<LispData list, LispData>(f scope)))
    
    let compileDefun (macros: IDictionary<string, Macros.Types.Macro>) (s: string, paramList: ParamList, body: Expr list) : Compiled =
        let clambda = compileLambda macros paramList body
        fun scope ->
            let (scope', cfunc) = clambda scope
            (Scope.add (s, cfunc) scope', cfunc)
    
    module Builtins =
        let S_t = ("t", Symbol "t")
        let S_nil = ("nil", Symbol "nil")
        let private eq2 (obj1: LispData) (obj2: LispData) =
            snd <| if obj1 = obj2 then S_t else S_nil
        let private eq (objs: LispData list) =
            match objs with
                | [obj1; obj2] -> eq2 obj1 obj2
                | _ -> failwith "= takes exactly two arguments"
        let F_eq = ("=", LispFunc (new Func<LispData list, LispData>(eq)))
        let private plus =
            function
                | [IntLiteral a; IntLiteral b] -> IntLiteral (a+b)
                | [FloatLiteral a; FloatLiteral b] -> FloatLiteral (a+b)
                | [IntLiteral a; FloatLiteral b] -> FloatLiteral ((float a) + b)
                | [FloatLiteral a; IntLiteral b] -> FloatLiteral (a + (float b))
                | [a; b] -> failwith <| sprintf "%A and %A are not both numeric values" a b
                | _ -> failwith "+ takes exactly two arguments"
        let F_plus = ("+", LispFunc (new Func<LispData list, LispData>(plus)))
        let private minus =
            function
                | [IntLiteral a; IntLiteral b] -> IntLiteral (a-b)
                | [FloatLiteral a; FloatLiteral b] -> FloatLiteral (a-b)
                | [IntLiteral a; FloatLiteral b] -> FloatLiteral ((float a) - b)
                | [FloatLiteral a; IntLiteral b] -> FloatLiteral (a - (float b))
                | [a; b] -> failwith <| sprintf "%A and %A are not both numeric values" a b
                | _ -> failwith "- takes exactly two arguments"
        let F_minus = ("-", LispFunc (new Func<LispData list, LispData>(minus)))
    
        let private println =
            function
                | [StringLiteral s] ->
                    printfn "%s" s
                    snd S_nil
                | [IntLiteral i] ->
                    printfn "%d" i
                    snd S_nil
                | [FloatLiteral f] ->
                    printfn "%f" f
                    snd S_nil
                | x ->
                    printfn "%A" x
                    snd S_nil
        let F_println = ("println", LispFunc (new Func<LispData list, LispData>(println)))
    
        let scope : Scope = [new System.Collections.Generic.Dictionary<string, LispData>(dict [S_t; S_nil; F_eq; F_plus; F_minus; F_println])]
    
    let compileTopLevel (macros: IDictionary<string, Macros.Types.Macro>) (t: TopLevel) : Scope =
        let compiled = List.map (compileDefun macros) t
        List.fold (fun s c -> fst <| c s) Builtins.scope compiled
