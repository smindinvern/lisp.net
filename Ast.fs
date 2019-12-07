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
        | Ellipsis of LispData
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
    and LetBinding = Pattern * Expr
    and Pattern =
        | SymbolPattern of string
        | LiteralPattern of LispData
        | ListPattern of Pattern list
        | ConsPattern of Pattern * Pattern
    type ParamList = Pattern list
    
    type Defun = string * ParamList * (Expr list)
    type TopLevel = Defun list

