module Reader

open Ast

open Tokenization

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
//
//let mutable consCell = Unchecked.defaultof<LispReader<LispData>>
//let mutable lispList = Unchecked.defaultof<LispReader<LispData>>
//let mutable quote = Unchecked.defaultof<LispReader<LispData>>


let rec consCell : LispReader<LispData> =
    lazy ((inParens <| parse {
        let! left = lispData
        do! ignore <@> %Dot
        let! right = lispData
        return ConsCell (left, right)
    }).Force())
and lispList : LispReader<LispData> =
    lazy ((List <@> (inParens <| some (lispDataOrConsCell))).Force())
and quote : LispReader<LispData> =
    lazy ((parse {
        match! pop1 with
        | SingleQuote -> return! Quote <@> (lispData)
        | t -> return! error <| sprintf "Expected Quote, got %A" t
    }).Force())
and lispData : LispReader<LispData> =
    lazy (((quote) <|> (symbol) <|> (literal) <|> (lispList)).Force())
and lispDataOrConsCell : LispReader<LispData> =
    lazy (((lispData) <|> (consCell)).Force())
    
let read : LispReader<LispData list> =
    parseUntil isEOF (lispDataOrConsCell)
