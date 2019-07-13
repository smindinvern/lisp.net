module Parsing

#nowarn "40"

open System

module Tokenization =
    open Utils
    open Parser
    open Parser.LineInfo
    
    type Token =
        | LParen
        | RParen
        | SingleQuote
        | Dot
        | StringLiteral of string
        | IntLiteral of int
        | FloatLiteral of double
        | Symbol of string

    type Tokenizer = Parser<char, unit, Token>

    let (~%) (c: char) =
        parse {
            let! x = pop
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
            let! cs = parseUntil (peek <=> (inject '"')) pop
            do! ignore <@> %'"'
            return StringLiteral (new string(List.toArray cs))
        }
    let digit : Parser<char, unit, char> = 
        parse {
            let! c = pop
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
            let! first = pop
            if isValidCharacter first && not(System.Char.IsDigit(first)) then
                let! rest = parseUntil (isEOF <||> (not <@> (isValidCharacter <@> peek))) pop
                return Symbol (new string(List.toArray(first::rest)))
            else
                return! error <| "Expected letter or '_', got '" + (string first) + "'."
        }
    let builtin : Tokenizer =
        parse {
            let! c = pop
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

module Data =
    type LispObject =
        | LispList of LispObject list
        | LispString of string
        | LispInt of int
        | LispFloat of double
        | LispSymbol of string
        | LispFunc of Func<LispObject list, LispObject>

module Ast =
    open Data

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

    open Parser
    open Tokenization

    type LispParser<'a> = Parser<Token, unit, 'a>

    let (~%) (t: Token) : LispParser<Token> =
        parse {
            let! t' = pop
            if t' = t then
                return t'
            else
                return! error <| sprintf "Not a %A" t
            }

    let symbol : LispParser<string> =
        parse {
            match! pop with
                | Symbol s -> return s
                | _ -> return! error "Not a symbol"
        }
    let literal : LispParser<LispObject> =
        parse {
            match! pop with
                | IntLiteral i -> return LispInt i
                | FloatLiteral f -> return LispFloat f
                | StringLiteral s -> return LispString s
                | _ -> return! error "Not a literal"
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
                    | _ -> return! error "Not a let expression"
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
                    | _ -> return! error "Not a case expression"
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
                    | _ -> return! error "Not a defun"
                }

    let topLevel : LispParser<TopLevel> = parseUntil isEOF defun

open Data

let rec exprToObject (e: Ast.Expr) =
    match e with
        | Ast.SymbolExpr s -> LispSymbol s
        | Ast.LiteralExpr x -> x
        | Ast.ListExpr es -> LispList (List.map exprToObject es)
        | _ -> failwith <| sprintf "Cannot translate to object: %A" e

module Scope =
    open System.Collections.Generic

    type Scope = System.Collections.Generic.Dictionary<string, LispObject> list

    type Binding = string * LispObject

    let rec lookup s : Scope -> LispObject option =
        function
            | [] -> None
            | scope::hidden ->
                let mutable x = LispInt 0
                if scope.TryGetValue(s, &x) then
                    Some(x)
                else
                    lookup s hidden

    let add ((s, v): Binding) (scope: Scope) =
        match scope with
            | head::tail when Option.isNone <| lookup s scope ->
                head.[s] <- v
                head::tail
            | scope' ->
                let x = new System.Collections.Generic.Dictionary<string, LispObject>()
                x.[s] <- v
                x::scope'

module Evaluation =
    open Ast

    let concatOptions<'a> (a: ('a list) option) (b: ('a list) option) =
        Option.bind (fun head -> Option.map (fun tail -> head @ tail) b) a

    open Scope
    
    let rec bindList = function
        | (p::ps, LispList (o::os)) ->
            concatOptions (bindPattern p o) (bindList (ps, LispList os))
        | ([], LispList []) -> Some []
        | _ -> None
    and bindPattern (pat: Pattern) (obj: LispObject) : (Binding list) option =
        match pat with
            | SymbolPattern s ->
                Some [(s, obj)]
            | LiteralPattern l ->
                if l = obj then
                    Some []
                else
                    None
            | ListPattern ps -> bindList (ps, obj)
            | ConsPattern (head, tail) ->
                match obj with
                    | LispList (h::t) ->
                        concatOptions (bindPattern head h) (bindPattern tail (LispList t))
                    | _ -> None

    let rec eval (scope: Scope) = function
        | LispSymbol s -> Option.map (fun x -> (scope, x)) (lookup s scope) 
        | LispList (f::args) ->
            match eval scope f with
                | None -> None
                | Some(scope', f') ->
                    match f' with
                        | LispFunc func ->
                            Some(scope', func.Invoke(args))
                        | _ -> failwith "Not a callable object"
        | x -> Some(scope, x)

module Compilation =
    open Scope
    open Ast
    open Evaluation
    
    type Compiled = Scope -> (Scope * LispObject)

    let rec evalCompiledList (scope: Scope) =
        function
            | [] -> (scope, LispSymbol "nil")
            | [last] -> last scope
            | head::tail ->
                let (scope', _) = head scope
                evalCompiledList scope' tail

    let bindAll (p: Pattern list) (args: LispObject list) =
        bindPattern (ListPattern p) (LispList args)

    let bindInNewScope (p: Pattern list) (args: LispObject list) =
        match bindAll p args with
            | None ->
                failwith "Binding failed"
            | Some(bindings) ->
                new System.Collections.Generic.Dictionary<string, LispObject>(dict bindings)

    let rec compileExpr (e: Expr) : Compiled =
        match e with
            | SymbolExpr s ->
                fun scope ->
                    match lookup s scope with
                        | Some(obj) -> (scope, obj)
                        | None -> failwith <| sprintf "Attempt to use free variable: %s" s
            | LiteralExpr l -> fun x -> (x, l)
            | ListExpr es -> compileListExpr es
            | LetExpr (bindings, es) -> compileLetExpr (bindings, es)
            | IfExpr (test, ifTrue, ifFalse) -> compileIfExpr test ifTrue ifFalse
            | QuotedExpr q -> compileQuoted q
            | ConsExpr (head, tail) ->
                let hc = compileExpr head
                let tc = compileExpr tail
                fun scope ->
                    let (scope, h) = hc scope
                    let (scope, t) = tc scope
                    match t with
                        | LispList xs -> (scope, LispList (h::xs))
                        | _ -> failwith <| sprintf "Cannot cons %A and %A" h t
            | _ -> failwith <| sprintf "%A: construct not supported" e
    and compileLetExpr (bindings: LetBinding list, es: Expr list) : Compiled =
        let (patterns, exprs) = List.unzip bindings
        let exprs' = List.map compileExpr exprs
        let body = List.map compileExpr es
        fun scope ->
            let exprs'' = List.map (snd << ((|>) scope)) exprs'
            let newScope = (bindInNewScope patterns exprs'')::scope
            let (newScope', obj) = evalCompiledList newScope body
            (List.tail newScope', obj)
    and compileListExpr (es: Expr list) : Compiled =
        let cs = List.map compileExpr es
        fun scope ->
            match List.map (snd << ((|>) scope)) cs with
                | [] -> (scope, LispList [])
                | (LispSymbol f)::args ->
                    match lookup f scope with
                        | Some(LispFunc func) -> (scope, func.Invoke(args))
                        | _ -> failwith <| sprintf "%s is not a callable object" f
                | (LispFunc func)::args ->
                    (scope, func.Invoke(args))
                | x::_ -> failwith <| sprintf "%A is not a callable object" x
    and compileIfExpr (test: Expr) (ifTrue: Expr) (ifFalse: Expr option) : Compiled =
        let ifFalse' =
            compileExpr <|
            match ifFalse with
                | Some(x) -> x
                | None -> SymbolExpr "nil"
        let ifTrue' = compileExpr ifTrue
        let test' = compileExpr test
        fun scope ->
            if (snd <| test' scope) <> (LispSymbol "nil") then
                ifTrue' scope
            else
                ifFalse' scope
    and compileQuoted (q: Expr) : Compiled =
        fun scope -> (scope, exprToObject q)

    let compileDefun (s: string, paramList: ParamList, body: Expr list) : Compiled =
        let cbody = List.map compileExpr body
        let f (scope: Scope) (args: LispObject list) =
            let newScope = (bindInNewScope paramList args)::scope
            let (newScope', obj) = evalCompiledList newScope cbody
            obj
        fun scope ->
            let obj = LispFunc (new Func<LispObject list, LispObject>(f scope))
            (Scope.add (s, obj) scope, obj)

    module Builtins =
        let S_t = ("t", LispSymbol "t")
        let S_nil = ("nil", LispSymbol "nil")
        let private eq2 (obj1: LispObject) (obj2: LispObject) =
            snd <| if obj1 = obj2 then S_t else S_nil
        let private eq (objs: LispObject list) =
            match objs with
                | [obj1; obj2] -> eq2 obj1 obj2
                | _ -> failwith "= takes exactly two arguments"
        let F_eq = ("=", LispFunc (new Func<LispObject list, LispObject>(eq)))
        let private plus =
            function
                | [LispInt a; LispInt b] -> LispInt (a+b)
                | [LispFloat a; LispFloat b] -> LispFloat (a+b)
                | [LispInt a; LispFloat b] -> LispFloat ((float a) + b)
                | [LispFloat a; LispInt b] -> LispFloat (a + (float b))
                | [a; b] -> failwith <| sprintf "%A and %A are not both numeric values" a b
                | _ -> failwith "+ takes exactly two arguments"
        let F_plus = ("+", LispFunc (new Func<LispObject list, LispObject>(plus)))
        let private minus =
            function
                | [LispInt a; LispInt b] -> LispInt (a-b)
                | [LispFloat a; LispFloat b] -> LispFloat (a-b)
                | [LispInt a; LispFloat b] -> LispFloat ((float a) - b)
                | [LispFloat a; LispInt b] -> LispFloat (a - (float b))
                | [a; b] -> failwith <| sprintf "%A and %A are not both numeric values" a b
                | _ -> failwith "- takes exactly two arguments"
        let F_minus = ("-", LispFunc (new Func<LispObject list, LispObject>(minus)))

        let private println =
            function
                | [LispString s] ->
                    printfn "%s" s
                    snd S_nil
                | [LispInt i] ->
                    printfn "%d" i
                    snd S_nil
                | [LispFloat f] ->
                    printfn "%f" f
                    snd S_nil
                | x ->
                    printfn "%A" x
                    snd S_nil
        let F_println = ("println", LispFunc (new Func<LispObject list, LispObject>(println)))

        let scope : Scope = [new System.Collections.Generic.Dictionary<string, LispObject>(dict [S_t; S_nil; F_eq; F_plus; F_minus; F_println])]

    let compileTopLevel (t: TopLevel) : Scope =
        let compiled = List.map compileDefun t
        List.fold (fun s c -> fst <| c s) Builtins.scope compiled
