module Parsing

    open Ast
    open Macros
    open Macros.Types
    open Macros.Parsing
    open Macros.Extensions

    open System.Collections.Generic

    let untagId (boundVars: HashSet<string>) (sym: string) =
        if sym.Contains('#') then
            if boundVars.Contains(sym) then
                sym
            else
                // identifier is free in this environment, so untag it.
                let sym' = new string(Array.takeWhile (fun x -> x <> '#') <| sym.ToCharArray())
                sym'
        else
            sym

    let rec pattern (macros: IDictionary<string, Macro>) = function
        | Symbol sym -> SymbolPattern sym
        | ConsCell (left, right) -> ConsPattern (pattern macros left, pattern macros right)
        | List ((Symbol s)::pats) when macros.ContainsKey(s) ->
            let m = macros.[s]
            let ld = m.Transformer <| ((Symbol s)::pats)
            pattern macros ld
        | List pats ->
            ListPattern <| List.map (pattern macros) pats
        | Quote _ -> failwith "Quoted expressions cannot appear in patterns"
        | LispFunc _ -> failwith "Functions cannot appear in patterns"
        | d -> Pattern.LiteralPattern d

    let rec patternVars = function
        | SymbolPattern s -> [s]
        | ConsPattern (l, r) -> (patternVars l) @ (patternVars r)
        | ListPattern pats -> List.collect patternVars pats
        | Pattern.LiteralPattern _ -> []

    let rec letBinding (boundVars: HashSet<string>) (macros: IDictionary<string, Macro>) bindings body =
        let binding = function
            | List [p; e] ->
                let pat = pattern macros p
                let boundVarsSeq = Seq.cast boundVars
                let boundVars' = new HashSet<string>(Seq.append boundVarsSeq (Seq.ofList <| patternVars pat))
                (boundVars', LetBinding (pat, expr boundVars macros e))
            | _ ->
                failwith "Invalid form for let-binding"
        let (boundVars's, bindings) = List.unzip <| List.map binding bindings
        let boundVars = new HashSet<string>(List.collect (List.ofSeq << Seq.cast) boundVars's)
        LetExpr (bindings, List.map (expr boundVars macros) body)
    and caseArm (boundVars: HashSet<string>) (macros: IDictionary<string, Macro>) = function
        | List (p::es) ->
            let pat = pattern macros p
            let boundVarsSeq = Seq.cast boundVars
            let boundVars' = new HashSet<string>(Seq.append boundVarsSeq (Seq.ofList <| patternVars pat))
            (pat, List.map (expr boundVars' macros) es)
        | _ -> failwith "Expected case-arm"
    and lambda (boundVars: HashSet<string>) (macros: IDictionary<string, Macro>) paramList body =
        let pats = List.map (pattern macros) paramList
        let boundVarsSeq = Seq.cast boundVars
        let boundVars' = new HashSet<string>(Seq.append boundVarsSeq (Seq.ofList << (List.collect patternVars) <| pats))
        LambdaExpr (pats, List.map (expr boundVars' macros) body)
    and expr (boundVars: HashSet<string>) (macros: IDictionary<string, Macro>) = function
        | Symbol sym ->
            SymbolExpr <| untagId boundVars sym
        | Quote q ->
            // Untag identifiers.
            let rec untagSyms ld () =
                match ld with
                    | Symbol s -> (Symbol <| untagId boundVars s, ())
                    | x -> foldLispData untagSyms () x
            QuotedExpr << fst <| untagSyms q ()
        | List es ->
            match es with
                | [ Symbol "if"; test; ifTrue ] ->
                    IfExpr (expr boundVars macros test, expr boundVars macros ifTrue, Option.None)
                | [ Symbol "if"; test; ifTrue; ifFalse ] ->
                    IfExpr (expr boundVars macros test, expr boundVars macros ifTrue, Option.Some(expr boundVars macros ifFalse))
                | (Symbol "let")::(List bindings)::body ->
                    letBinding boundVars macros bindings body
                | [ Symbol "case"; e; List arms ] ->
                    CaseExpr (expr boundVars macros e, List.map (caseArm boundVars macros) arms)
                | (Symbol "lambda")::(List paramList)::body ->
                    lambda boundVars macros paramList body
                | (Symbol s)::args when macros.ContainsKey(s) ->
                    let m = macros.[s]
                    let ld = m.Transformer <| ((Symbol s)::args)
                    expr boundVars macros ld
                | es ->
                    ListExpr <| List.map (expr boundVars macros) es
        | ConsCell (left, right) -> ConsExpr (expr boundVars macros left, expr boundVars macros right)
        | Ellipsis e -> failwith "Ellipses only allowed in macro definitions"
        | x -> LiteralExpr x
