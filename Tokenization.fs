module Tokenization

    open Utils
    
    type Token =
        | LParen
        | RParen
        | SingleQuote
        | Dot
        | StringLiteral of string
        | IntLiteral of int
        | FloatLiteral of double
        | Symbol of string
    
    open smindinvern.Parser
    open smindinvern.Parser.Types
    open smindinvern.Parser.LineInfo
    open smindinvern.Parser.Primitives
    open smindinvern.Parser.Primitives.LineInfo
    open smindinvern.Parser.Combinators
    open smindinvern.Parser.Combinators.LineInfo
    open smindinvern.Parser.Monad
    
    type Tokenizer = Parser<char, unit, Token>
    
    let (~%) (c: char) =
        parse {
            let! x = pop1
            if x = c then
                return c
            else
            return! error <| "Failed to match " + (string c)
        }
    
    let matchChar c t = (konst t) <@> %c
    
    let (~%%) (s: string) =
        let cs = s.ToCharArray() |> List.ofArray
        parse {
            do! ignore <@> (sequence <| List.map (~%) cs)
            return s
        }
    
    let matchString s t = (konst t) <@> %%s
    
    let lParen : Tokenizer = matchChar '(' LParen
    let rParen : Tokenizer = matchChar ')' RParen
    let singleQuote : Tokenizer = matchChar '\'' SingleQuote
    let dot : Tokenizer = matchChar '.' Dot
    let stringLit : Tokenizer =
        parse {
            do! ignore <@> %'"'
            let! cs = parseUntil (peek1 <=> (inject '"')) pop1
            do! ignore <@> %'"'
            return StringLiteral (new string(List.toArray cs))
        }
    let digit : Parser<char, unit, char> = 
        parse {
            let! c = pop1
            if System.Char.IsDigit(c) then
                return c
            else
            return! error <| "Expected digit but got '" + (string c) + "'."
        }
    let numericLit : Tokenizer =
        parse {
            let! maybeString = tryParse (%'+' <|> %'-')
            let s = new string(Option.toArray maybeString)
            let! integral = some digit
            let i = new string(List.toArray integral)
            let! f =
                parse {
                    do! ignore <@> %'.'
                    let! digits = many digit
                    return new string(List.toArray <| '.'::digits)
                } <|> (inject "")
            if i.Length = 0 && f.Length = 0 then
                return! error <| "Expected NumericLiteral"
            elif f.Length > 0 then
                return FloatLiteral <| System.Double.Parse(s + i + f)
            else
                return IntLiteral <| System.Int32.Parse(s + i)
        }
    
    let literal : Tokenizer = numericLit <|> stringLit
    
    let identifier : Tokenizer =
        let isValidCharacter c =
            System.Char.IsLetterOrDigit(c) || c = '_' || c = '-' || c = '*' || c = '/'
        parse {
            let! first = pop1
            if isValidCharacter first && not(System.Char.IsDigit(first)) then
                let! rest = parseUntil (isEOF <||> (not <@> (isValidCharacter <@> peek1))) pop1
                return Symbol (new string(List.toArray(first::rest)))
            else
                return! error <| "Expected letter or '_', got '" + (string first) + "'."
        }
    let builtin : Tokenizer =
        parse {
            let! c = pop1
            if c = '+' || c = '-' || c = '*' || c = '/' || c = '=' then
                return Symbol (new string([|c|]))
            else
                return! error <| "Not a builtin"
        }
    
    let token : Tokenizer =
        oneOf [ lParen
            ; rParen
            ; singleQuote
            ; dot
            ; literal
            ; builtin
            ; identifier
            ]
    
    let whitespace : Parser<char, unit, char> =
        oneOf <| List.map (~%) [' '; '\t'; '\r'; '\n']
    
    let parseUntilEOF (p: Tokenizer) : Parser<char, unit, Token list> =
        let eof =
            parse {
                do! ignore <@> some whitespace
                return! isEOF
            }
        parseUntil eof p
    
    let tokens : Parser<char, unit, Token list> =
        parseUntilEOF token

