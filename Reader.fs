module Reader

open Ast

open Tokenization

module internal Parsers =
    open smindinvern.Alternative
    open smindinvern.Parser.Types
    open smindinvern.Parser.Primitives
    open smindinvern.Parser.Combinators
    open smindinvern.Parser.Monad
    
    type LispReader<'a> = Parser<Token, unit, 'a>

    let (~%) (t: Token) : LispReader<Token> =
        parse {
            let! t' = pop1
            if t' = t then
                return t'
            else
                return! error <| sprintf "Expected %A, got %A" t t'
        }

    let symbol : LispReader<LispData> =
        parse {
            match! pop1 with
            | SymbolToken s -> return Symbol s
            | t-> return! error <| sprintf "Expected Symbol, got %A" t
        }

    let literal : LispReader<LispData> =
        parse {
            match! pop1 with
            | IntToken i -> return IntLiteral i
            | FloatToken f -> return FloatLiteral f
            | StringToken s -> return StringLiteral s
            | t -> return! error <| sprintf "Expected Literal, got %A" t
        }

    let lParen : LispReader<unit> =
        ignore <@> %LParen
    let rParen : LispReader<unit> =
        ignore <@> %RParen
    let inParens<'a> (r: LispReader<'a>) : LispReader<'a> =
        parse {
            do! lParen
            let! x = r
            do! rParen
            return x
        }

    let rec consCell : LispReader<LispData> =
        lazy ((inParens <| parse {
            let! left = maybeEllipsized lispData
            do! ignore <@> %Dot
            let! right = lispDataOrConsCell
            return ConsCell (left, right)
        }).Force())
    and lispList : LispReader<LispData> =
        lazy ((List <@> (inParens <| some lispDataOrConsCell)).Force())
    and quote : LispReader<LispData> =
        lazy ((parse {
            match! pop1 with
            | SingleQuote -> return! Quote <@> (maybeEllipsized lispData)
            | t -> return! error <| sprintf "Expected Quote, got %A" t
        }).Force())
    and lispData : LispReader<LispData> =
        lazy ((quote <|> symbol <|> literal <|> lispList).Force())
    and lispDataOrConsCell : LispReader<LispData> =
        lazy ((maybeEllipsized <| lispData <|> consCell).Force())
    and maybeEllipsized' (ld: LispData) : LispReader<LispData> =
        lazy ((parse {
            match! tryParse %(SymbolToken "...") with
            | Option.Some(_) -> return! LispData.Ellipsis <@> maybeEllipsized' ld
            | Option.None -> return ld
            }).Force())
    and maybeEllipsized (p: LispReader<LispData>): LispReader<LispData> =
        lazy ((parse {
            let! ld = p
            return! maybeEllipsized' ld
            }).Force())
        
    let read : LispReader<LispData list> =
        parseUntil isEOF lispDataOrConsCell

open smindinvern.Parser

let read (input: string) =
    let ts = LineInfo.Tokenization.TokenizeString(input)
    match Primitives.runParser Tokenization.tokens ts () with
    | (_, Result.Ok(tokens)) ->
        let ts = Tokenization.Tokenize(tokens)
        match Primitives.runParser Parsers.read ts () with
        | (_, Result.Ok(data)) -> data
        | (s, Result.Error(e)) -> failwithf "read failed with: %A. Parser state = %A" e s
    | (s, Result.Error(e)) -> failwithf "Tokenization failed with: %A. Parser state = %A" e s
    
