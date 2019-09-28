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
    
    type Expr =
        | SymbolExpr of string
        | LiteralExpr of LispData
        | ListExpr of Expr list
        | ConsExpr of Expr * Expr
        | LetExpr of (LetBinding list) * (Expr list)
        | CaseExpr of Expr * ((Pattern * (Expr list)) list)
        | IfExpr of Expr * Expr * (Expr option)
        | QuotedExpr of Expr
    and LetBinding = Pattern * Expr
    and Pattern =
        | SymbolPattern of string
        | LiteralPattern of LispData
        | ListPattern of Pattern list
        | ConsPattern of Pattern * Pattern
    type ParamList = Pattern list
    
    type Defun = string * ParamList * (Expr list)
    type TopLevel = Defun list

