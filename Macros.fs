module Macros

open Ast
open smindinvern
open smindinvern.Parser

open System.Collections.Generic

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

open Extensions

let tagId (s: string) (i: int) =
    if s.Contains('#') || List.contains s ["let"; "case"; "lambda"; "if"] then
        s
    else
        sprintf "%s#%d" s i

let rec tagIds' (ld: LispData) (i: int) =
    match ld with
        | Symbol s -> (Symbol <| tagId s i, i)
        | x -> foldLispData tagIds' i x
let tagIds ld i = fst <| tagIds' ld i


module PatternMatching =
    open Types
    
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
                // Tag all identifiers in @datum to be distinct from identifiers
                // introduced by macro transformers.
                return [Binding (id, Value <| tagIds datum 0)]
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

module internal Unique =
    let mutable i = 1

    let nextI () =
        let i' = i
        i <- i + 1
        i'

    let uniquify (s: string) =
        sprintf "%s#%d" s <| nextI()

module Transformers =
    open Types
    open Unique

    module SyntaxRules =

        let rec renameIdentifiers' (bound: HashSet<string>) (ld: LispData) (renames: (string * string) list) =
            match ld with
            | Symbol s ->
                if bound.Contains(s) then
                    let renamed = uniquify s
                    (Symbol renamed, (s, renamed)::renames)
                else
                    (Symbol s, renames)
            | x -> foldLispData (renameIdentifiers' bound) renames x

        let renameIdentifiers (bound: HashSet<string>) (ld: LispData) =
            renameIdentifiers' bound ld []

        let rec getEllipsisDepths' = function
            | Ast.List xs ->
                List.collect getEllipsisDepths' xs
            | ConsCell (l, r) ->
                getEllipsisDepths' (Ast.List [l; r])
            | Symbol s ->
                [(s, 0)]
            | Quote q ->
                getEllipsisDepths' q
            | Ellipsis e ->
                let results = getEllipsisDepths' e
                List.map (fun (k, v) -> (k, v + 1)) results
            | _ -> []

        let getEllipsisDepths x = dict <| getEllipsisDepths' x

        let rec getBindingEllipsisDepth = function
            | EllipsizedValue (v::_) -> (getBindingEllipsisDepth v) + 1
            | Value _ -> 0

        let rec repeatNTimes (v: Values) (n: int) =
            if n = 0 then
                v
            else
                repeatNTimes (Repeat v) (n - 1)

        // Add repeats to ellipsized bindings to replicate inputs as necessary.
        let reshapeBindings (bindings: Binding list) (renames: (string * string) list) (depths: IDictionary<string, int>) =
            let bindingsDict = dict <| List.map (fun (Binding (name, v)) -> (name, v)) bindings
            let bindings = List.map (fun (old_name, new_name) -> (new_name, bindingsDict.[old_name])) renames
            let reshape (name: string, v: Values) =
                (name, repeatNTimes v ((depths.[name]) - (getBindingEllipsisDepth v)))
            dict <| Seq.map reshape bindings 

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

        let rec transform (bindings: IDictionary<string, Values>) = function
            | Ast.List templates ->
                Ast.List <| transformList bindings templates
            | ConsCell (l, r) ->
                ConsCell (transform bindings l, transform bindings r)
            | Symbol s ->
                match bindings.tryGetValue(s) with
                | Option.None -> Symbol s
                | Option.Some(Value v) -> v
                | _ -> failwith "Incorrect ellipsis depth."
            | Quote q ->
                Quote (transform bindings q)
            | x -> x
        and transformList (bindings: IDictionary<string, Values>) = function
            | (Ellipsis e)::xs ->
                (transformEllipsis bindings e) @ (transformList bindings xs)
            | x::xs -> (transform bindings x)::(transformList bindings xs)
            | [] -> []
        and transformEllipsis (bindings: IDictionary<string, Values>) (e: LispData) =
            let kvps = List.ofSeq <| bindings.KeyValuePairs()
            let (constants, ellipsized, repeats) = splitBindings kvps
            let (names, ellipsized) = List.unzip ellipsized
            let ellipsized' = List.transpose ellipsized
            let repeat (ellipsized: Values list) =
                let xs = List.zip names ellipsized
                let bindings = xs @ repeats @ constants
                match e with
                | Ellipsis e' -> transformEllipsis (dict bindings) e'
                | e -> [transform (dict bindings) e]
            List.collect repeat ellipsized'

        let createTransformer (literals: string list) (template: LispData) (boundVars: HashSet<string>) =
            let (template, renames) = renameIdentifiers boundVars template
            let depths = getEllipsisDepths template
            fun (bindings: Binding list) ->
                let bindings = reshapeBindings bindings renames depths
                let result = transform bindings template
                tagIds result <| Unique.nextI()

module Parsing =
    open Types
    
    let rec pattern (literals : string list) = function
        | Symbol sym ->
            if List.contains sym literals then
                LiteralPattern sym
            else
                IdentifierPattern sym
        | ConsCell (l, r) ->
            SyntaxConsPattern (pattern literals l, pattern literals r)
        | List pats ->
            SyntaxListPattern <| List.map (pattern literals) pats
        | Ellipsis pat ->
            EllipsizedPattern <| pattern literals pat
        | Quote _ -> failwith "Quoted expressions cannot appear in patterns"
        | LispFunc _ -> failwith "Functions cannot appear in patterns"
        | d -> ConstantPattern d
    
    open smindinvern.Alternative
    open smindinvern.Parser.Primitives
            
    open smindinvern.Utils

    let rec srPatternVars = function
        | IdentifierPattern s -> [s]
        | SyntaxListPattern pats -> List.collect srPatternVars pats
        | SyntaxConsPattern (l, r) -> List.collect srPatternVars [l; r]
        | EllipsizedPattern e -> srPatternVars e
        | _ -> []
        
    let syntaxRule' (literals: string list) (ps: LispData list) (template: LispData) =
        let pats = List.map (pattern literals) ps
        let boundVars = new HashSet<string>(List.collect srPatternVars pats)
        let matcher = PatternMatching.listMatcher' pats
        let transformer = Transformers.SyntaxRules.createTransformer literals template boundVars
        Parser.Monad.parse {
            let! (_::bindings) = matcher
            return! catch <| lazy (transformer bindings)
        }
            
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
        | [Symbol keyword; Ast.List syntax_rules] ->
            let rules = syntaxRules syntax_rules
            let runMacro (input: LispData list) =
                let (_, r) = runParser (Parser.Combinators.oneOf rules) (Parser.Tokenization.Tokenize(input)) ()
                match r with
                    | Result.Ok(result) -> result
                    | Result.Error(e) -> failwithf "%A" e
            { Keyword = keyword; Transformer = runMacro }
        | _ -> failwith "Incorrect form for define-syntax"
