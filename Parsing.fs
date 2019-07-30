module Parsing

    #nowarn "40"
    
    open System
    
    open Tokenization
    open Parser
    open Ast
    
    type LispParser<'a> = Parser<Token, unit, 'a>
    
    let (~%) (t: Token) : LispParser<Token> =
        parse {
            let! t' = pop
            if t' = t then
                return t'
            else
                return! error <| sprintf "Expected %A, got %A" t t'
            }
    
    let symbol : LispParser<string> =
        parse {
            match! pop with
                | Symbol s -> return s
                | t -> return! error <| sprintf "Expected Symbol, got %A" t
        }
    let literal : LispParser<LispObject> =
        parse {
            match! pop with
                | IntLiteral i -> return LispInt i
                | FloatLiteral f -> return LispFloat f
                | StringLiteral s -> return LispString s
                | t -> return! error <| sprintf "Expected Literal, got %A" t
        }
    let lParen : LispParser<unit> =
        ignore <@> %LParen
    let rParen : LispParser<unit> =
        ignore <@> %RParen
    
    let mkLetBinding p e = LetBinding (p, e)
    let mkLetExpr bindings exprs = LetExpr (bindings, exprs)
    let mkIfExpr test t f = IfExpr (test, t, f)
    let mkCaseExpr e ps = CaseExpr (e, ps)
    
    let inParens<'a> (p: LispParser<'a>) : LispParser<'a> =
        parse {
            do! lParen
            let! x = p
            do! rParen
            return x
        }
    
    let list'<'a> (p: LispParser<'a>) (canBeEmpty: bool) : LispParser<'a list> =
        inParens ((if canBeEmpty then some else many) p)
    
    let symbolPattern : LispParser<Pattern> =
        SymbolPattern <@> symbol
    let literalPattern : LispParser<Pattern> =
        LiteralPattern <@> literal
    
    open Zipper
    
    let rec symbolExpr : LispParser<Expr> =
        SymbolExpr <@> symbol
    and literalExpr : LispParser<Expr> =
        LiteralExpr <@> literal
    and listExpr' : LispParser<Expr list> =
        list' expr true
    and consCell'<'a> (p: LispParser<'a>): LispParser<'a * 'a> =
        parse {
            let! head = p
            do! ignore <@> %Dot
            let! tail = p
            return (head, tail)
        }
    and consCellExpr : LispParser<Expr> =
        inParens (ConsExpr <@> consCell' expr)
    and listExpr : LispParser<Expr> =
        ListExpr <@> listExpr'
    and letBinding : LispParser<LetBinding> =
        inParens (mkLetBinding <@> pattern <*> expr)
    and listPattern : LispParser<Pattern> =
        ListPattern <@> (list' pattern true)
    and consCellPattern : LispParser<Pattern> =
        inParens (ConsPattern <@> consCell' pattern)
    // The F# compiler isn't smart enough to figure out that LispParser *is* a function type.
    and pattern ((s, _, _)) : (Zipper<Token> * unit * bool) * Result<Pattern, string> =
        let p = oneOf [ symbolPattern; literalPattern; consCellPattern; listPattern ]
        runParser p s ()
    and ifExpr : LispParser<Expr> =
        inParens <|
            parse {
                match! symbol with
                    | "if" -> return! mkIfExpr <@> expr <*> expr <*> (tryParse expr)
                    | _ -> return! error "Not an if expression"
            }
    and letExpr : LispParser<Expr> =
        inParens <|
            parse {
                match! symbol with
                    | "let" -> return! mkLetExpr <@> (list' letBinding false) <*> (many expr)
                    | s -> return! error <| sprintf "Expected let-expression, got %A" s
            }
    and caseArm : LispParser<Pattern * (Expr list)> =
        inParens <|
            parse {
                let! p = pattern
                let! es = many expr
                return (p, es)
            }
    and caseExpr : LispParser<Expr> =
        inParens <|
            parse {
                match! symbol with
                    | "case" -> return! mkCaseExpr <@> expr <*> (list' caseArm false)
                    | s -> return! error <| sprintf "Expected case-expression, got %A" s
            }
    and quotedExpr : LispParser<Expr> =
        parse {
            do! ignore <@> %SingleQuote
            return! QuotedExpr <@> expr
        }
    // and expr : LispParser<Expr> =
    and expr ((s, _, _): Zipper<Token> * unit * bool) : (Zipper<Token> * unit * bool) * Result<Expr, string> =
        let p = oneOf [ symbolExpr
                        ; literalExpr
                        ; consCellExpr
                        ; letExpr
                        ; caseExpr
                        ; ifExpr
                        ; listExpr
                        ; quotedExpr
                        ]
        runParser p s ()
    
    let mkDefun name paramList body = (name, paramList, body)
    
    let defun : LispParser<Defun> =
        inParens <|
            parse {
                match! symbol with
                    | "defun" -> return! mkDefun <@> symbol <*> (list' pattern true) <*> (many expr)
                    | s -> return! error <| sprintf "Expected defun-expression, got %A" s
                }
    
    let topLevel : LispParser<TopLevel> = parseUntil isEOF defun
