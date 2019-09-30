module Reader

open Ast

open Tokenization

open smindinvern.Parser
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

open Zipper

#nowarn "40"

let rec consCell : LispReader<LispData> =
    parse {
        let! left = lispData
        do! ignore <@> %Dot
        let! right = lispData
        return ConsCell (left, right)
    }
and lispList : LispReader<LispData> =
    List <@> (inParens <| some lispData)
and quote : LispReader<LispData> =
    parse {
        match! pop1 with
        | SingleQuote -> return! Quote <@> lispData
        | t -> return! error <| sprintf "Expected Quote, got %A" t
    }
// Break recursion by inserting a lazy link in the cycle.
and lispDataLazy : LispReader<LispData> Lazy =
    lazy oneOf [ quote; consCell; lispList; symbol; literal ]
and lispData : LispReader<LispData> =
    lispDataLazy.Force()
and read : LispReader<LispData list> =
    parseUntil isEOF lispData
