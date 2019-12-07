module Macros

open Ast
open smindinvern.Parser

// See R6RS sections 11.18 and 11.19.
// This implementation uses SRFI 149 semantics.

module Types =
    type Macro = { Keyword: string;
                   Transformer: LispData list -> LispData }
    
    open smindinvern.Parser.Types
        
    // Parse the pattern into a SyntaxPattern first.  This will make it
    // easier to handle ellipses when constructing the PatternMatcher.
    type SyntaxPattern =
        | SyntaxListPattern of SyntaxPattern list
        | SyntaxConsPattern of SyntaxPattern * SyntaxPattern
        | IdentifierPattern of string
        | LiteralPattern of string
        | ConstantPattern of LispData 
        | EllipsizedPattern of SyntaxPattern
    
    type Values =
        | EllipsizedValue of Values list
        | Repeat of Values
        | Value of LispData
    type Binding =
        | Binding of string * Values

    // Match a Lisp list to a pattern to produce a set of bindings.
    type PatternMatcher = Parser<LispData, unit, Binding list>

module Extensions =
    open System.Collections.Generic
    open System.Runtime.CompilerServices
    open Types
    
    [<Extension>]
    type Extensions() =
        [<Extension>]
        static member KeyValuePairs<'k, 'v>(d: IDictionary<'k, 'v>) =
            Seq.zip (d.Keys) (d.Values)
        [<Extension>]
        static member tryGetValue<'k, 'v>(d: IDictionary<'k, 'v>, key: 'k) =
            let v = ref Unchecked.defaultof<'v>
            if d.TryGetValue(key, v) then
                Some(!v)
            else
                None
        [<Extension>]
        static member tryPeelOff<'a>(xs: 'a list, pred: 'a -> bool) =
            let (matching, nonmatching) = List.partition pred xs
            match matching with
            | head::tail -> Option.Some(head, tail @ nonmatching)
            | _ -> Option.None

module PatternMatching =
    open Types
    
    open smindinvern
    open smindinvern.Alternative
    open smindinvern.Parser.Primitives
    open smindinvern.Parser.Monad
    open smindinvern.Parser.Combinators
        

    let rec listMatcher' (pats: SyntaxPattern list) : PatternMatcher =
        parse {
            let! result = List.concat <@> sequence (List.map patternMatcher pats)
            let! _ = isEOF <||> error "List not completely matched."
            return result
        }
    and listMatcher (pats: SyntaxPattern list) : PatternMatcher =
        parse {
            match! pop1 with
            | Ast.List input ->
                let (_, r) = runParser (listMatcher' pats) (Parser.Tokenization.Tokenize(input)) ()
                return! liftResult r
            | _ -> return! error "List pattern did not match a list."
        }
    and patternMatcher : SyntaxPattern -> PatternMatcher = function
        | EllipsizedPattern ep ->
            parse {
                let! matches = List.concat <@> some (patternMatcher ep)
                let xs = List.groupBy (fun (Binding (s, v)) -> s) matches
                let xs' = List.map (fun (name, bindings) -> Binding (name, EllipsizedValue <| List.map (fun (Binding (_, vs)) -> vs) bindings)) xs
                return xs'
            }
        | SyntaxListPattern pats -> listMatcher pats
        | SyntaxConsPattern (l, r) ->
            let l' = patternMatcher l
            let r' = patternMatcher r
            List.append <@> l' <*> r'
        | IdentifierPattern id -> 
            // The *pattern* is an identifier, meaning that we bind whatever
            // datum is in this position of the input to the identifier.
            parse {
                let! datum = pop1
                return [Binding (id, Value datum)]
            }
        | LiteralPattern lit ->
            // The pattern is an identifier that appears in the list of literals
            // in the `syntax-rules`.
            parse {
                match! pop1 with
                | Symbol id ->
                    // TODO: Check that the input form is an identifier and that it has
                    // TODO: the same lexical binding as the pattern literal or that both
                    // TODO: it and the pattern literal have no lexical binding.
                    return []
                | _ -> return! error <| "A pattern literal must match an identifier"
            }
        | ConstantPattern c ->
            // The input must match the value of the constant pattern.
            parse {
                let! input = pop1
                if input = c then
                    return []
                else
                    return! error <| "Input does not match pattern constant."
            }

module Transformers =
    open Types
            
    let rec renameIdentifier (in_use: string list) (name: string) =
        if List.contains name in_use then
            renameIdentifier in_use (name + "\'")
        else
            name
            
    let rec renameIdentifiers (literals: string list) (names_seen: string list) (renames: (string * string) list) = function
        | Ast.List xs ->
            let (x, y, zs) =
                List.foldBack (fun t (names_seen, renames, xs) ->
                                   let (x, y, z) = renameIdentifiers literals names_seen renames t
                                   (x, y, z::xs)) xs (names_seen, renames, [])
            (x, y, Ast.List zs)
        | ConsCell (l, r) ->
            let (x, y, l') = renameIdentifiers literals names_seen renames l
            let (x, y, r') = renameIdentifiers literals x y r
            (x, y, ConsCell (l', r'))
        | Symbol s ->
            if List.contains s literals then
                (names_seen, renames, Symbol s)
            else
                let renamed = renameIdentifier names_seen s
                (renamed::names_seen, (if renamed <> s then (s, renamed)::renames else renames), Symbol renamed)
        | Quote q ->
            let (x, y, q') = renameIdentifiers literals names_seen renames q
            (x, y, Quote q')
        | Ellipsis e ->
            let (x, y, e') = renameIdentifiers literals names_seen renames e
            (x, y, Ellipsis e')
        | x -> (names_seen, renames, x)

    open Extensions
    
    let rec getEllipsisDepths = function
        | Ast.List xs ->
            let results = List.map getEllipsisDepths xs
            dict <| Seq.collect Extensions.KeyValuePairs results
        | ConsCell (l, r) ->
            getEllipsisDepths (Ast.List [l; r])
        | Symbol s ->
            dict [(s, 0)]
        | Quote q ->
            getEllipsisDepths q
        | Ellipsis e ->
            let results = getEllipsisDepths e
            dict <| Seq.map (fun (k, v) -> (k, v + 1)) (results.KeyValuePairs())
    
    let rec getBindingEllipsisDepth = function
        | EllipsizedValue (v::_) -> (getBindingEllipsisDepth v) + 1
        | Value v -> 0
    
    let rec repeatNTimes (v: Values) (n: int) =
        if n = 0 then
            v
        else
            repeatNTimes (Repeat v) (n - 1)
    
    let reshapeBindings (bindings: Binding list) (renames: (string * string) list) (depths: (string * int) list) =
        let bindingsDict = dict <| List.map (fun (Binding (name, v)) -> (name, v)) bindings
        let copies = List.map (fun (old_name, new_name) -> (new_name, bindingsDict.[old_name])) renames
        let bindings = Seq.append (bindingsDict.KeyValuePairs()) copies
        let depths = dict depths
        let reshape (name: string, v: Values) =
            (name, repeatNTimes v ((depths.[name]) - (getBindingEllipsisDepth v)))
        dict <| Seq.map reshape bindings 
                
    open System.Collections.Generic
    
    let splitBindings (xs: (string * Values) list) =
        let (constants, ellipses, repeats) =
            List.unzip3 <|
            List.map (fun (name, v) ->
                match v with
                | EllipsizedValue vs -> (Option.None, Option.Some(name, vs), Option.None)
                | Repeat v -> (Option.None, Option.None, Option.Some(name, v))
                | Value _ -> (Option.Some(name, v), Option.None, Option.None)) xs
        (List.collect Option.toList constants,
         List.collect Option.toList ellipses,
         List.collect Option.toList repeats)
    
    let rec transform (literals: string list) (bindings: IDictionary<string, Values>) = function
        | Ast.List templates ->
            Ast.List <| transformList literals bindings templates
        | ConsCell (l, r) ->
            ConsCell (transform literals bindings l, transform literals bindings r)
        | Symbol s ->
            if List.contains s literals then
                Symbol s
            else
                match bindings.[s] with
                | Value v -> v
                | _ -> failwith "Incorrect ellipsis depth."
        | Quote q ->
            Quote (transform literals bindings q)
        | x -> x
    and transformList (literals: string list) (bindings: IDictionary<string, Values>) = function
        | (Ellipsis e)::xs ->
            (transformEllipsis literals bindings e) @ (transformList literals bindings xs)
        | x::xs -> (transform literals bindings x)::(transformList literals bindings xs)
        | [] -> []
    and transformEllipsis (literals: string list) (bindings: IDictionary<string, Values>) (e: LispData) =
        let kvps = List.ofSeq <| bindings.KeyValuePairs()
        let (constants, ellipsized, repeats) = splitBindings kvps
        let (names, ellipsized) = List.unzip ellipsized
        let ellipsized' = List.transpose ellipsized
        let repeat (ellipsized: Values list) =
            let xs = List.zip names ellipsized
            let bindings = xs @ repeats @ constants
            match e with
            | Ellipsis e' -> transformEllipsis literals (dict bindings) e'
            | e -> [transform literals (dict bindings) e]
        List.collect repeat ellipsized'
    
    let createTransformer (literals: string list) (bindings: Binding list) (template: LispData) =
        let (renamed, renames, template') = renameIdentifiers literals [] [] template
        let depths = getEllipsisDepths template'
        let bindings = reshapeBindings bindings renames (Seq.toList <| depths.KeyValuePairs())
        transform literals bindings template'
        
module Parsing =
    open Types
    
    let rec fixupEllipses (data: LispData) =
        match data with
        | Ast.List xs -> Ast.List <| fixupListEllipses xs
        | ConsCell (l, r) -> ConsCell (fixupEllipses l, fixupEllipses r)
        | Quote q -> Quote (fixupEllipses q)
        | x -> x
    and fixupListEllipses (xs: LispData list) =
        match xs with
        | x::(Symbol "...")::xs ->
            fixupListEllipses ((Ellipsis (fixupEllipses x))::xs)
        | x::xs -> (fixupEllipses x)::(fixupListEllipses xs)
        | [] -> []
    
    let rec pattern (literals : string list) = function
        | Symbol sym ->
            if List.contains sym literals then
                LiteralPattern sym
            else
                IdentifierPattern sym
        | ConsCell (l, r) ->
            SyntaxConsPattern (pattern literals l, pattern literals r)
        | List pats ->
            SyntaxListPattern <| listPattern literals pats
        | Quote _ -> failwith "Quoted expressions cannot appear in patterns"
        | LispFunc _ -> failwith "Functions cannot appear in patterns"
        | d -> ConstantPattern d
    and listPattern (literals : string list) (p: LispData list) =
        // TODO: Check that each pattern variable only appears once in the pattern.
        match p with
        | [] -> []
        | head::(Symbol "...")::tail ->
            (EllipsizedPattern <| pattern literals head)::(listPattern literals tail)
        | head::tail -> (pattern literals head)::(listPattern literals tail)
    
    open smindinvern
    open smindinvern.Alternative
    open smindinvern.Parser.Primitives
            
    open smindinvern.Utils
        
    let syntaxRule' (literals: string list) (p: LispData list) (template: LispData) =
        let pat = listPattern literals p
        let matcher = PatternMatching.listMatcher' pat
        fun (input: LispData list) ->
            let (_, r) = runParser matcher (Parser.Tokenization.Tokenize(input)) ()
            match r with
            | Result.Ok(_::bindings) ->
                try
                    Result.Ok(Transformers.createTransformer literals bindings (fixupEllipses template))
                with
                | e -> Result.Error({Errors.Tree.Value = e.Message; Errors.Tree.Children = []})
            | Result.Error(e) -> Result.Error(e)
            
    let syntaxRule (literals: string list) = function
        | Ast.List [Ast.List patterns; template] ->
            syntaxRule' literals patterns template
        | _ -> failwith "Invalid form for syntax-rule."
    
    let syntaxRules = function
        | (Symbol "syntax-rules")::(List literals)::rules ->
            // TODO: check form of @literals
            let literals' = List.map (function
                | Ast.Symbol s -> s
                | _ -> failwith "Literal list may only include identifiers.") literals
            List.map (syntaxRule literals') rules
        | _ -> failwith "Incorrect form for syntax-rules"
            
    let defineSyntax = function
        | [Symbol "define-syntax"; Symbol keyword; Ast.List syntax_rules] ->
            (keyword, syntaxRules syntax_rules)
        | _ -> failwith "Incorrect form for define-syntax"