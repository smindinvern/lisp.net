module Parsing

    open Ast

    let rec pattern = function
        | Symbol sym -> SymbolPattern sym
        | ConsCell (left, right) -> ConsPattern (pattern left, pattern right)
        | List pats -> ListPattern <| List.map pattern pats
        | Quote _ -> failwith "Quoted expressions cannot appear in patterns"
        | LispFunc _ -> failwith "Functions cannot appear in patterns"
        | d -> LiteralPattern d

    let rec letBinding = function
        | List [ p; e] ->
            LetBinding (pattern p, expr e)
        | _ -> failwith "Expected let-binding"
    and caseArm = function
        | List (p::es) ->
            (pattern p, List.map expr es)
        | _ -> failwith "Expected case-arm"
    and expr = function
        | Symbol sym -> SymbolExpr sym
        | Quote q -> QuotedExpr <| expr q
        | List es ->
            match es with
                | [ Symbol "if"; test; ifTrue ] ->
                    IfExpr (expr test, expr ifTrue, Option.None)
                | [ Symbol "if"; test; ifTrue; ifFalse ] ->
                    IfExpr (expr test, expr ifTrue, Option.Some(expr ifFalse))
                | (Symbol "let")::(List bindings)::body ->
                    LetExpr (List.map letBinding bindings, List.map expr body)
                | [ Symbol "case"; e; List arms ] ->
                    CaseExpr (expr e, List.map caseArm arms)
                | es ->
                    ListExpr <| List.map expr es
        | ConsCell (left, right) -> ConsExpr (expr left, expr right)
        | x -> LiteralExpr x

    let defun = function
        | List ((Symbol "defun")::(Symbol name)::(List paramList)::body) ->
            (name, List.map pattern paramList, List.map expr body)
        | x -> failwith <| sprintf "Expected defun expression, got %A" x
            

    let topLevel defuns = List.map defun defuns
