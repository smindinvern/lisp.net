module Macros

open Ast
open smindinvern.Parser

// See R6RS sections 11.18 and 11.19.

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
    
    type Match =
        | Match of LispData
        | EllipsizedMatch of Match list

    // Match a Lisp list to a pattern to produce a set of bindings.
    type PatternMatcher = Parser<LispData, unit, (string * Match) list>


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
                let xs = List.groupBy fst matches
                let xs' = List.map (fun (name, matches) -> (name, EllipsizedMatch <| List.map snd matches)) xs
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
                return [(id, Match datum)]
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
        
    open System.Collections.Generic
    open System.Runtime.CompilerServices
    
    [<Extension>]
    type Extensions() =
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
        [<Extension>]
        static member tryGetMatch(matches: (string * Match) list, name: string) =
            matches.tryPeelOff(function
            | (x, _) when x = name -> true
            | _ -> false)
            
    open smindinvern.Utils
    
    let reduceRank (xs: (string * Match) list) =
        let lift = function
            | (name, EllipsizedMatch vs) -> List.map (fun v -> (name, v)) vs
            | v -> [v]
        List.collect lift xs
    
    let unconsGroups (xs: (string * Match) list) : ((string * Match) list * (string * Match) list) =
        let (heads, tails) = List.unzip <| List.map (fun (s, EllipsizedMatch ys) ->
            match ys with
            | [y] -> ((s, y), Option.None)
            | y::ys' -> ((s, y), Option.Some(s, EllipsizedMatch ys'))) xs
        (heads, List.collect Option.toList tails)
        
    let splitMatches (xs: (string * Match) list) =
        List.partition (function
            | (_, EllipsizedMatch _) -> true
            | _ -> false) xs
    
    let rec transformer (template: LispData) (constant: (string * Match) list) (replicate: (string * Match) list) (iterate: (string * Match) list) : (string * Match) list * (string * Match) list * LispData =
        match template with
        | Ast.List templates ->
            let (replicate', iterate', xs) = listTransformer templates constant replicate iterate
            (replicate', iterate', Ast.List xs)
        | ConsCell (l, r) ->
            let (replicate', iterate', left) = transformer l constant replicate iterate
            let (replicate'', iterate'', right) = transformer r constant replicate' iterate'
            (replicate'', iterate'', ConsCell (left, right))
        | Symbol s ->
            match replicate.tryGetMatch(s) with
            | Option.Some((x, Match v), rest) -> (rest, iterate, v)
            | _ ->
                match iterate.tryGetMatch(s) with
                | Option.Some((x, Match v), rest) -> (replicate, rest, v)
                | _ -> failwith "No more matches for pattern variable %s" s
        | Quote q ->
            let (replicate', iterate', x) = transformer q constant replicate iterate
            (replicate', iterate', Quote x)
        | x -> (replicate, iterate, x)
    and repeatTransformer (template: LispData) (nEllipses: int) (constant: (string * Match) list) (replicate: (string * Match) list) (iterate: (string * Match) list) : (string * Match) list * (string * Match) list * LispData list =
        let (replicate', iterate', x) = ellipsisTransformer template (nEllipses - 1) constant replicate iterate
        match (replicate', iterate') with
        | ([], []) -> ([], [], x)
        | (_, []) -> failwith "Incompatible ellipsis match counts."
        | _ ->
            let r = if List.isEmpty replicate' then replicate else replicate'
            let (replicate'', iterate'', y) = repeatTransformer template nEllipses constant r iterate'
            (replicate'', iterate'', x @ y)
    and ellipsisTransformer' (template: LispData) (nEllipses: int) (constant: (string * Match) list) (replicate: (string * Match) list) (iterate: (string * Match) list) : (string * Match) list * (string * Match) list * LispData list =
        let (heads, tails) = unconsGroups iterate
        let ([], [], x) = repeatTransformer template nEllipses constant replicate heads
        if List.isEmpty tails then
            ([], [], x)
        else
            let ([], [], tailResult) = ellipsisTransformer' template nEllipses constant replicate tails
            ([], [], x @ tailResult)
    and ellipsisTransformer (template: LispData) (nEllipses: int) (constant: (string * Match) list) (replicate: (string * Match) list) (iterate: (string * Match) list) : (string * Match) list * (string * Match) list * LispData list =
        if (nEllipses = 1) then
            let iterate' = reduceRank iterate
            let (replicate', iterate', x) = transformer template constant replicate iterate'
            (replicate', iterate', [x])
        else
            // reduce ellipsis rank
            let replicateReduced = reduceRank replicate
            ellipsisTransformer' template nEllipses constant replicateReduced iterate
    and listTransformer (templates: LispData list) (constant: (string * Match) list) (replicate: (string * Match) list) (iterate: (string * Match) list) : (string * Match) list * (string * Match) list * LispData list =
        match templates with
        | x::(Symbol "...")::xs ->
            let ellipses = List.takeWhile (function
                | Symbol "..." -> true
                | _ -> false) xs
            let nEllipses = (List.length ellipses) + 1
            let xs' = List.skip (nEllipses - 1) xs
            let (replicate', iterate', expanded) = ellipsisTransformer x nEllipses constant replicate iterate
            let (replicate'', iterate'', next) = listTransformer xs' constant replicate' iterate'
            (replicate'', iterate'', expanded @ next)
        | x::xs ->
            let (replicate', iterate', head) = transformer x constant replicate iterate
            let (replicate'', iterate'', tail) = listTransformer xs constant replicate' iterate'
            (replicate'', iterate'', head::tail)
        | [] -> (replicate, iterate, [])
    
    let rec ellipsisDepth = function
        | EllipsizedMatch (m::_) -> (ellipsisDepth m) + 1
        | _ -> 0
        
    let syntaxRule' (literals: string list) (p: LispData list) (template: LispData) =
        let pat = listPattern literals p
        let matcher = listMatcher' pat
        fun (input: LispData list) ->
            let (_, r) = runParser matcher (Parser.Tokenization.Tokenize(input)) ()
            match r with
            | Result.Ok(bindings) ->
                let sized = List.groupBy (ellipsisDepth << snd) bindings
                let (constants, ellipsized) = List.partition (fun (size, _) -> size = 0) sized
                // TODO: will throw if no ellipsized bindings
                let (_, iterate)::replicated = List.sortByDescending fst ellipsized
                let replicate = List.collect snd replicated
                let constant = List.collect snd constants
                Result.Ok(transformer template constant replicate iterate)
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