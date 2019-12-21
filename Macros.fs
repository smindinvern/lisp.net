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
    
    open Extensions

    let rec patternVars = function
        | SymbolPattern s -> [s]
        | Pattern.LiteralPattern _ -> []
        | ListPattern ps -> List.collect patternVars ps
        | ConsPattern (pl, pr) -> List.collect patternVars [pl; pr]

    let getBoundVars (boundInTemplate: HashSet<string>) pat =
        patternVars pat
        |> List.filter (fun s -> not(boundInTemplate.Contains(s)))

    let renameNewBindings (boundVars: string list) (rename: string -> string) =
        let renames = List.map (fun s -> (s, uniquify s)) boundVars
        let renamesDict = dict renames
        fun s ->
            match renamesDict.tryGetValue(s) with
                | Option.Some(v) -> v
                | Option.None -> rename s

    let rec renameInPatternThunk : Pattern -> ((string -> string) -> LispData) = function
        | SymbolPattern s -> fun rename -> Symbol <| rename s
        | Pattern.LiteralPattern d -> fun _ -> d
        | ListPattern pats ->
            let thunks = List.map renameInPatternThunk pats
            fun rename -> Ast.List (List.map ((|>) rename) thunks)
        | ConsPattern (l, r) ->
            let lthunk = renameInPatternThunk l
            let rthunk = renameInPatternThunk r
            fun rename -> ConsCell (lthunk rename, rthunk rename)

    let rec renameInBindingThunk (boundVars: HashSet<string>) (pat, e) =
        let patThunk = renameInPatternThunk pat
        let exprThunk = renameNewBindingsThunk boundVars e
        fun rename ->
            (patThunk rename, exprThunk rename)

    and renameInCaseArmThunk (boundVars: HashSet<string>) (pat, body) : ((string -> string) -> LispData) =
        let newBoundVars = getBoundVars boundVars pat
        let bodyThunks = List.map (renameNewBindingsThunk boundVars) body
        let patThunk = renameInPatternThunk pat
        fun rename ->
            let rename = renameNewBindings newBoundVars rename
            let newPat = patThunk rename
            let newBody = List.map ((|>) rename) bodyThunks
            Ast.List <| newPat::newBody
            
    and renameNewBindingsThunk (boundVars: HashSet<string>) : Expr -> ((string -> string) -> LispData) = function
        | SymbolExpr s ->
            fun rename -> Symbol <| rename s
        | LetExpr (bindings, body) ->
            // Rename every identifier bound in @bindings that is NOT in @boundVars.
            // This is to prevent bindings introduced by the macro from shadowing
            // any other identifiers.
            let newBoundVars = List.collect (getBoundVars boundVars) (List.map (fun (pat, _) -> pat) bindings)
            let bodyThunks = List.map (renameNewBindingsThunk boundVars) body
            let bindingsThunks = List.map (renameInBindingThunk boundVars) bindings
            fun rename ->
                let rename = renameNewBindings newBoundVars rename
                let bindings = List.map ((|>) rename) bindingsThunks
                let body = List.map ((|>) rename) bodyThunks
                Ast.List <| (Symbol "let")::(Ast.List <| List.map (fun (x, y) -> Ast.List [x; y]) bindings)::body
        | CaseExpr (e, arms) ->
            let exprThunk = renameNewBindingsThunk boundVars e
            let armThunks = List.map (renameInCaseArmThunk boundVars) arms
            fun rename -> Ast.List <| (Symbol "case")::(exprThunk rename)::(List.map ((|>) rename) armThunks)
        | LambdaExpr (pats, body) ->
            let newBoundVars = List.collect (getBoundVars boundVars) pats
            let bodyThunks = List.map (renameNewBindingsThunk boundVars) body
            let patThunks = List.map (renameInPatternThunk) pats
            fun rename ->
                let rename = renameNewBindings newBoundVars rename
                let newPats = List.map ((|>) rename) patThunks
                let newBody = List.map ((|>) rename) bodyThunks
                Ast.List <| (Symbol "lambda")::(Ast.List newPats)::newBody
        | LiteralExpr d -> fun _ -> d
        | ListExpr es ->
            let thunks = List.map (renameNewBindingsThunk boundVars) es
            fun rename -> Ast.List (List.map ((|>) rename) thunks)
        | ConsExpr (l, r) ->
            let lthunk = renameNewBindingsThunk boundVars l
            let rthunk = renameNewBindingsThunk boundVars r
            fun rename -> ConsCell (lthunk rename, rthunk rename)
        | IfExpr (e1, e2, e3) ->
            let e1thunk = renameNewBindingsThunk boundVars e1
            let e2thunk = renameNewBindingsThunk boundVars e2
            let e3thunk = Option.map (renameNewBindingsThunk boundVars) e3
            fun rename ->
                let e1 = e1thunk rename
                let e2 = e2thunk rename
                let e3 = Option.map ((|>) rename) e3thunk
                Ast.List <| (Symbol "if")::e1::e2::(Option.toList e3)
        | QuotedExpr q ->
            let thunk = renameNewBindingsThunk boundVars q
            fun rename -> Quote <| thunk rename
        | EllipsizedExpr e ->
            let thunk = renameNewBindingsThunk boundVars e
            fun rename -> Ellipsis <| thunk rename
            
    let rec renameIdentifier (in_use: string list) (name: string) =
        if List.contains name in_use then
            renameIdentifier in_use (uniquify name)
        else
            name
    
    let rec renameIdentifiers' (bound: HashSet<string>) (ld: LispData) (names_seen: string list, renames: (string * string) list) =
        match ld with
        | Symbol s ->
            if bound.Contains(s) then
                let renamed = renameIdentifier names_seen s
                let x = if renamed <> s then ((s, renamed)::renames) else renames
                (Symbol renamed, (renamed::names_seen, x))
            else
                (Symbol s, (names_seen, renames))
        | x -> foldLispData (renameIdentifiers' bound) (names_seen, renames) x
    
    let renameIdentifiers (bound: HashSet<string>) (names_seen: string list) (renames: (string * string) list) (ld: LispData) =
        renameIdentifiers' bound ld (names_seen, renames)
    
    open Extensions
    
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
        let copies = List.map (fun (old_name, new_name) -> (new_name, bindingsDict.[old_name])) renames
        let bindings = Seq.append (bindingsDict.KeyValuePairs()) copies
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
        let (template, (names_seen, renames)) = renameIdentifiers boundVars [] [] template
        let depths = getEllipsisDepths template
        let templateExpr = Parsing.expr template
        let templateThunk = renameNewBindingsThunk boundVars templateExpr
        fun (bindings: Binding list) ->
            let bindings = reshapeBindings bindings renames depths
            let template = templateThunk id
            transform bindings template

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

    let rec srPatternVars = function
        | IdentifierPattern s -> [s]
        | SyntaxListPattern pats -> List.collect srPatternVars pats
        | SyntaxConsPattern (l, r) -> List.collect srPatternVars [l; r]
        | EllipsizedPattern e -> srPatternVars e
        | _ -> []
        
    let syntaxRule' (literals: string list) (p: LispData list) (template: LispData) =
        let pat = listPattern literals p
        let boundVars = new HashSet<string>(List.collect srPatternVars pat)
        let matcher = PatternMatching.listMatcher' pat
        let transformer = Transformers.createTransformer literals (fixupEllipses template) boundVars
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
        | [Symbol "define-syntax"; Symbol keyword; Ast.List syntax_rules] ->
            let rules = syntaxRules syntax_rules
            let runMacro (input: LispData list) =
                let (_, r) = runParser (Parser.Combinators.oneOf rules) (Parser.Tokenization.Tokenize(input)) ()
                match r with
                    | Result.Ok(result) -> result
                    | Result.Error(e) -> failwithf "%A" e
            { Keyword = keyword; Transformer = runMacro }
        | _ -> failwith "Incorrect form for define-syntax"
