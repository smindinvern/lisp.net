module Compilation

    open Scope
    open Ast
    open Evaluation
    
    open System
    
    type Compiled = Scope -> (Scope * LispData)
    
    let rec exprToObject (e: Ast.Expr) =
        match e with
            | Ast.SymbolExpr s -> Symbol s
            | Ast.LiteralExpr x -> x
            | Ast.ListExpr es -> List (List.map exprToObject es)
            | _ -> failwith <| sprintf "Cannot translate to object: %A" e
    
    let rec evalCompiledList (scope: Scope) =
        function
            | [] -> (scope, Symbol "nil")
            | [last] -> last scope
            | head::tail ->
                let (scope', _) = head scope
                evalCompiledList scope' tail
    
    let bindAll (p: Pattern list) (args: LispData list) =
        bindPattern (ListPattern p) (List args)
    
    let bindInNewScope (p: Pattern list) (args: LispData list) =
        match bindAll p args with
            | None ->
                failwith "Binding failed"
            | Some(bindings) ->
                new System.Collections.Generic.Dictionary<string, LispData>(dict bindings)
    
    let rec compileExpr (e: Expr) : Compiled =
        match e with
            | SymbolExpr s ->
                fun scope ->
                    match lookup s scope with
                        | Some(obj) -> (scope, obj)
                        | None -> failwith <| sprintf "Attempt to use free variable: %s" s
            | LiteralExpr l -> fun x -> (x, l)
            | ListExpr es -> compileListExpr es
            | LetExpr (bindings, es) -> compileLetExpr (bindings, es)
            | IfExpr (test, ifTrue, ifFalse) -> compileIfExpr test ifTrue ifFalse
            | QuotedExpr q -> compileQuoted q
            | ConsExpr (head, tail) ->
                let hc = compileExpr head
                let tc = compileExpr tail
                fun scope ->
                    let (scope, h) = hc scope
                    let (scope, t) = tc scope
                    match t with
                        | List xs -> (scope, List (h::xs))
                        | _ -> failwith <| sprintf "Cannot cons %A and %A" h t
            | _ -> failwith <| sprintf "%A: construct not supported" e
    and compileLetExpr (bindings: LetBinding list, es: Expr list) : Compiled =
        let (patterns, exprs) = List.unzip bindings
        let exprs' = List.map compileExpr exprs
        let body = List.map compileExpr es
        fun scope ->
            let exprs'' = List.map (snd << ((|>) scope)) exprs'
            let newScope = (bindInNewScope patterns exprs'')::scope
            let (newScope', obj) = evalCompiledList newScope body
            (List.tail newScope', obj)
    and compileListExpr (es: Expr list) : Compiled =
        let cs = List.map compileExpr es
        fun scope ->
            match List.map (snd << ((|>) scope)) cs with
                | [] -> (scope, List [])
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
    and compileQuoted (q: Expr) : Compiled =
        fun scope -> (scope, exprToObject q)
    
    let compileDefun (s: string, paramList: ParamList, body: Expr list) : Compiled =
        let cbody = List.map compileExpr body
        let f (scope: Scope) (args: LispData list) =
            let newScope = (bindInNewScope paramList args)::scope
            let (newScope', obj) = evalCompiledList newScope cbody
            obj
        fun scope ->
            let obj = LispFunc (new Func<LispData list, LispData>(f scope))
            (Scope.add (s, obj) scope, obj)
    
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
    
    let compileTopLevel (t: TopLevel) : Scope =
        let compiled = List.map compileDefun t
        List.fold (fun s c -> fst <| c s) Builtins.scope compiled
