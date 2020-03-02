module Tokenization

    open smindinvern.Utils
    
    type LispToken =
        | LParen
        | RParen
        | SingleQuote
        | Dot
        | Ellipsis
        | StringToken of string
        | IntToken of int
        | FloatToken of double
        | SymbolToken of string
    
    open smindinvern
    open smindinvern.Alternative
    open smindinvern.Parser.Types
    open smindinvern.Parser.RangeInfo
    open smindinvern.Parser.Primitives
    open smindinvern.Parser.Primitives.RangeInfo
    open smindinvern.Parser.Combinators
    open smindinvern.Parser.Combinators.RangeInfo
    open smindinvern.Parser.Monad
    
    type Tokenizer<'a> = RangeInfo.Parser<char, unit, Token<'a>>
    
    let (~%) (c: char) : Tokenizer<char> =
        parse {
            let! x = RangeInfo.popToken
            if x.Value = c then
                return x
            else
            return! error <| "Failed to match " + (string c)
        }
    
    let matchChar c (t: 'a) : Tokenizer<'a> =
        parse {
            let! x = %c
            return Token.Create(t, x.Range)
        }
    
    let (~%%) (s: string) : Tokenizer<string> =
        let cs = s.ToCharArray() |> List.ofArray
        parse {
            let! cs = sequence <| List.map (~%) cs
            return TChar.Concat(cs)
        }
    
    let matchString s (t: 'a) : Tokenizer<'a> =
        parse {
            let! x = %%s
            return Token.Create(t, x.Range)
        }
    
    let lParen : Tokenizer<LispToken> = matchChar '(' LParen
    let rParen : Tokenizer<LispToken> = matchChar ')' RParen
    let singleQuote : Tokenizer<LispToken> = matchChar '\'' SingleQuote
    let dot : Tokenizer<LispToken> = matchChar '.' Dot
    let ellipsis : Tokenizer<LispToken> = matchString "..." (SymbolToken "...")
    let stringLit : Tokenizer<LispToken> =
        parse {
            do! ignore <@> %'"'
            let! cs = parseUntil (peek1 <=> (inject '"')) popToken
            do! ignore <@> %'"'
            let s = TChar.Concat(cs)
            return Token.Create(StringToken s.Value, s.Range)
        }
    let digit : Tokenizer<char> = 
        parse {
            let! c = popToken
            if System.Char.IsDigit(c.Value) then
                return c
            else
            return! error <| "Expected digit but got '" + (string c) + "'."
        }
    let numericLit : Tokenizer<LispToken> =
        parse {
            let! sign = Option.toList <@> tryParse (%'+' <|> %'-')
            let! integral = some digit
            let! f =
                parse {
                    let! dot = %'.'
                    let! digits = many digit
                    return dot::digits
                } <|> (inject [])
            if integral.Length = 0 && f.Length = 0 then
                return! error <| "Expected NumericLiteral"
            else
                // Verify that the next character is either whitespace, a comment, or a ')'
                let! nextChar = peek1
                if not (List.contains nextChar [' '; '\t'; '\n'; ';'; ')']) then
                    return! error <| "Expected NumericLiteral"
                else
                    let s = TChar.Concat(sign @ integral @ f)
                    if f.Length > 0 then
                        return Token.Create(FloatToken <| System.Double.Parse(s.Value), s.Range)
                    else
                        return Token.Create(IntToken <| System.Int32.Parse(s.Value), s.Range)
        }
    
    let literal : Tokenizer<LispToken> = numericLit <|> stringLit
    
    let identifier : Tokenizer<LispToken> =
        let isValidCharacter c =
            System.Char.IsLetterOrDigit(c) || List.contains c ['_'; '-'; '*'; '/']
        parse {
            let! first = popToken
            if isValidCharacter first.Value && not(System.Char.IsDigit(first.Value)) then
                let! rest = parseUntil (isEOF <||> (not <@> (isValidCharacter <@> peek1))) popToken
                let s = TChar.Concat(first::rest)
                return Token.Create(SymbolToken s.Value, s.Range)
            else
                return! error <| "Expected letter or '_', got '" + (string first.Value) + "'."
        }
    let builtin : Tokenizer<LispToken> =
        parse {
            let! c = popToken
            if List.contains c.Value ['+'; '-'; '*'; '/'; '='] then
                return Token.Create(SymbolToken (string(c.Value)), c.Range)
            else
                return! error <| "Not a builtin"
        }
    
    let token : Tokenizer<LispToken> =
        oneOf [ lParen
            ; rParen
            ; singleQuote
            ; ellipsis
            ; dot
            ; literal
            ; builtin
            ; identifier
            ]
    
    let comment : Parser<char, unit, unit> =
        parse {
            do! ignore <@> %';'
            do! ignore <@> parseUntil (pop1 <=> (inject '\n')) (inject ())
        }
    let whitespace : Parser<char, unit, unit> =
        oneOf <| List.map (fun c -> ignore <@> %c) [' '; '\t'; '\r'; '\n']
    
    let parseUntilEOF (p: Tokenizer<LispToken>) : Parser<char, unit, Token<LispToken> list> =
        let eof =
            parse {
                do! ignore <@> some (whitespace <|> comment)
                return! isEOF
            }
        parseUntil eof p
    
    let tokens : Parser<char, unit, Token<LispToken> list> =
        parseUntilEOF token
