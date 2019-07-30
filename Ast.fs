module Ast

    open System
    
    type LispObject =
        | LispList of LispObject list
        | LispString of string
        | LispInt of int
        | LispFloat of double
        | LispSymbol of string
        | LispFunc of Func<LispObject list, LispObject>
    
    type Expr =
        | SymbolExpr of string
        | LiteralExpr of LispObject
        | ListExpr of Expr list
        | ConsExpr of Expr * Expr
        | LetExpr of (LetBinding list) * (Expr list)
        | CaseExpr of Expr * ((Pattern * (Expr list)) list)
        | IfExpr of Expr * Expr * (Expr option)
        | QuotedExpr of Expr
    and LetBinding = Pattern * Expr
    and Pattern =
        | SymbolPattern of string
        | LiteralPattern of LispObject
        | ListPattern of Pattern list
        | ConsPattern of Pattern * Pattern
    type ParamList = Pattern list
    
    type Defun = string * ParamList * (Expr list)
    type TopLevel = Defun list

