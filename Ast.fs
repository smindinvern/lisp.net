module Ast

    open System
    
    type LispData =
        | List of LispData list
        | ConsCell of LispData * LispData
        | IntLiteral of int
        | FloatLiteral of float
        | StringLiteral of string
        | Symbol of string
        | Quote of LispData
        | LispFunc of Func<LispData list, LispData>
        | Ellipsis of LispData  // This is only valid for macro templates.
        with
            member private x.ToStringBuilder(sb: Text.StringBuilder) =
                match x with
                | List xs ->
                    let append (y: LispData) (sb: Text.StringBuilder) = y.ToStringBuilder(sb)
                    let space (sb: Text.StringBuilder) = sb.Append(' ')
                    let bound = List.map ((<|) append) xs
                    let sequence = smindinvern.Utils.List.intersperse space bound
                    let f = List.fold (>>) id sequence
                    (f (sb.Append('('))).Append(')')
                | ConsCell (l, r) ->
                    r.ToStringBuilder(l.ToStringBuilder(sb.Append('(')).Append(" . ")).Append(')')
                | IntLiteral i -> sb.Append(i)
                | FloatLiteral f -> sb.Append(f)
                | StringLiteral s -> sb.Append('"').Append(s).Append('"')
                | Symbol s -> sb.Append(s)
                | Quote q -> q.ToStringBuilder(sb.Append('\''))
                | LispFunc f -> sb.Append(f.ToString())
                | Ellipsis data -> data.ToStringBuilder(sb).Append(" ...")
            override x.ToString() =
                x.ToStringBuilder(new Text.StringBuilder()).ToString()
            
    let rec foldLispData (f: LispData -> 'state -> (LispData * 'state)) (s: 'state) (ld: LispData) =
        match ld with
        | List xs ->
            let folder x (xs, state) =
                let (x, state) = f x state
                (x::xs, state)
            let (xs, s) =
                List.foldBack folder xs ([], s)
            (List xs, s)
        | ConsCell (l, r) ->
            let (ldl, s) = f l s
            let (ldr, s) = f r s
            (ConsCell (ldl, ldr), s)
        | Quote q ->
            let (q, s) = f q s
            (Quote q, s)
        | Ellipsis e ->
            let (e, s) = f e s
            (Ellipsis e, s)
        | x -> (x, s)

    type Expr =
        | SymbolExpr of string
        | LiteralExpr of LispData
        | ListExpr of Expr list
        | ConsExpr of Expr * Expr
        | LetExpr of (LetBinding list) * (Expr list)
        | CaseExpr of Expr * ((Pattern * (Expr list)) list)
        | IfExpr of Expr * Expr * (Expr option)
        | QuotedExpr of Expr
        | LambdaExpr of (Pattern list) * (Expr list)
        | EllipsizedExpr of Expr  // This is only valid for macro templates.
    and LetBinding = Pattern * Expr
    and Pattern =
        | SymbolPattern of string
        | LiteralPattern of LispData
        | ListPattern of Pattern list
        | ConsPattern of Pattern * Pattern
        
    let rec foldPattern (f: Pattern -> 'state -> (Pattern * 'state)) (s: 'state) (pat: Pattern) =
        match pat with
        | ListPattern pats ->
            let folder pat (pats, state) =
                let (pat, state) = f pat state
                (pat::pats, state)
            let (pats, s) =
                List.foldBack folder pats ([], s)
            (ListPattern pats, s)
        | ConsPattern (patl, patr) ->
            let (patl, s) = f patl s
            let (patr, s) = f patr s
            (ConsPattern (patl, patr), s)
        | x -> (x, s)
    
    let rec foldExpr (f: Expr -> 'state -> (Expr * 'state)) (s: 'state) (e: Expr) =
        match e with
        | ListExpr es ->
            let (es, s) = foldExprList f es s
            (ListExpr es, s)
        | ConsExpr (el, er) ->
            let (el, s) = f el s
            let (er, s) = f er s
            (ConsExpr (el, er), s)
        | LetExpr (bindings, es) ->
            let (es, s) = foldExprList f es s
            (LetExpr (bindings, es), s)
        | CaseExpr (e, cases) ->
            let (e, s) = f e s
            let (pats, bodies) = List.unzip cases
            let (bodies, s) = foldExprListList f bodies s
            (CaseExpr (e, List.zip pats bodies), s)
        | IfExpr (e1, e2, e3) ->
            let (e1, s) = f e1 s
            let (e2, s) = f e2 s
            match e3 with
            | Option.None -> (IfExpr (e1, e2, Option.None), s)
            | Option.Some(e3) ->
                let (e3, s) = f e3 s
                (IfExpr (e1, e2, Option.Some(e3)), s)
        | QuotedExpr q ->
            let (q, s) = f q s
            (QuotedExpr q, s)
        | LambdaExpr (pats, body) ->
            let (body, s) = foldExprList f body s
            (LambdaExpr (pats, body), s)
        | EllipsizedExpr e ->
            let (e, s) = f e s
            (EllipsizedExpr e, s)
        | x -> (x, s)
    and private foldExprList' f g es s =
        let folder e (es, state) =
            let (e, state) = f g e state
            (e::es, state)
        List.foldBack folder es ([], s)
    and internal foldExprList f es s = foldExprList' (<|) f es s
    and internal foldExprListList f es s = foldExprList' foldExprList f es s       

    let rec patternToData = function
        | SymbolPattern s -> Symbol s
        | Pattern.LiteralPattern data -> data
        | ListPattern pats -> List <| List.map patternToData pats
        | ConsPattern (l, r) -> ConsCell (patternToData l, patternToData r)

    let rec exprToData = function
        | SymbolExpr s -> Symbol s
        | LiteralExpr data -> data
        | ListExpr es -> List <| List.map exprToData es
        | ConsExpr (l, r) -> ConsCell (exprToData l, exprToData r)
        | LetExpr (bindings, body) ->
            let bindings = List.map (fun (pat, e) -> List [patternToData pat; exprToData e]) bindings
            let body = List.map exprToData body
            List ((Symbol "let")::(List bindings)::body)
        | CaseExpr (e, arms) ->
            let e = exprToData e
            let arms = List.map (fun (pat, body) -> List ((patternToData pat)::(List.map exprToData body))) arms
            List [Symbol "case"; e; List arms]
        | IfExpr (e1, e2, e3) ->
            let e1 = exprToData e1
            let e2 = exprToData e2
            List <| (Symbol "if")::e1::e2::(Option.toList <| Option.map exprToData e3)
        | QuotedExpr q -> Quote <| exprToData q
        | LambdaExpr (args, body) ->
            let args = List.map patternToData args
            let body = List.map exprToData body
            List <| (Symbol "lambda")::(List args)::body
        | EllipsizedExpr e -> Ellipsis <| exprToData e
        
    type ParamList = Pattern list
    
    type Defun = string * ParamList * (Expr list)
    type TopLevel = Defun list

