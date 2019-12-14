module Macros

open Ast
open smindinvern
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
    
    let rec renameIdentifiers' (bound: string list) (ld: LispData) (names_seen: string list, renames: (string * string) list) =
        match ld with
        | Symbol s ->
            if List.contains s bound then
                let renamed = renameIdentifier names_seen s
                let x = if renamed <> s then ((s, renamed)::renames) else renames
                (Symbol renamed, (renamed::names_seen, x))
            else
                (Symbol s, (names_seen, renames))
        | x -> foldLispData (renameIdentifiers' bound) (names_seen, renames) x
    
    let renameIdentifiers (bound: string list) (names_seen: string list) (renames: (string * string) list) (ld: LispData) =
        renameIdentifiers' bound ld (names_seen, renames)

    let rec renameInPattern' (literals: string list) (bound: string list) (pat: Pattern) (renamed: string list) =
        match pat with
        | SymbolPattern s ->
            if List.contains s literals || List.contains s bound then
                (SymbolPattern s, renamed)
            else
                (SymbolPattern ("&" + s), s::renamed)
        | x -> foldPattern (renameInPattern' literals bound) renamed x
    
    let renameInPattern (literals: string list) (bound: string list) (pat: Pattern) =
        renameInPattern' literals bound pat []
    
    let rec renameInExpr' (literals: string list) (bound: string list) (e: Expr) (let_bound: string list, names_seen: string list, renames: (string * string) list) =
        match e with
        | SymbolExpr s ->
            if List.contains s bound then
                let renamed = renameIdentifier names_seen s
                let x = if renamed <> s then ((s, renamed)::renames) else renames
                (SymbolExpr renamed, (let_bound, renamed::names_seen, x))
            elif List.contains s let_bound then
                let renamed = "&" + s
                (SymbolExpr renamed, (let_bound, names_seen, renames))
            else
                (SymbolExpr s, (let_bound, names_seen, renames))
        | LetExpr (bindings, body) ->
            // Rename every identifier bound in @bindings that is NOT in @bound.
            // Rename by prepending an '&', i.e. a character not allowed in identifiers,
            // so that it *cannot* clash with a user-defined identifier.
            let (pats, exprs) = List.unzip bindings
            let (pats, renamed) = List.unzip <| List.map (renameInPattern literals bound) pats
            // Flatten all renames to a single list.
            let renamed = List.concat renamed
            let bindings = List.zip pats exprs
            // Apply renames to let-bound variables in body while we continue renaming identifiers.
            let (result, (_, names_seen, renames)) = foldExpr (renameInExpr' literals bound) (renamed @ let_bound, names_seen, renames) (LetExpr (bindings, body))
            (result, (let_bound, names_seen, renames))
        | CaseExpr (e, cases) ->
            let (e, (_, names_seen, renames)) = renameInExpr' literals bound e (let_bound, names_seen, renames)
            let (pats, bodies) = List.unzip cases
            let (pats, renamed) = List.unzip <| List.map (renameInPattern literals bound) pats
            // Apply renames to case bodies.
            let processBody (renamed, body) (results, let_bound, names_seen, renames) =
                let (body, (_, names_seen, renames)) = foldExprList (renameInExpr' literals bound) body (renamed @ let_bound, names_seen, renames)
                (body::results, let_bound, names_seen, renames)
            let (bodies, _, names_seen, renames) =
                List.foldBack processBody (List.zip renamed bodies) ([], let_bound, names_seen, renames)
            (CaseExpr (e, List.zip pats bodies), (let_bound, names_seen, renames))
        | LambdaExpr (args, body) ->
            let (args, renamed) = List.unzip <| List.map (renameInPattern literals bound) args
            let renamed = List.concat renamed
            let (body, (_, names_seen, renames)) =
                foldExprList (renameInExpr' literals bound) body (renamed @ let_bound, names_seen, renames)
            (LambdaExpr (args, body), (let_bound, names_seen, renames))
        | x -> foldExpr (renameInExpr' literals bound) (let_bound, names_seen, renames) x
        
    let renameInExpr (literals: string list) (bound: string list) (e: Expr) =
        let (e, (_, names_seen, renames)) = renameInExpr' literals bound e ([], [], [])
        (e, names_seen, renames)
    
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
            match bindings.tryGetValue(s) with
            | Option.None -> Symbol s
            | Option.Some(Value v) -> v
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
    
    let rec patternToData = function
        | SymbolPattern s -> Symbol s
        | Pattern.LiteralPattern data -> data
        | ListPattern pats -> Ast.List <| List.map patternToData pats
        | ConsPattern (l, r) -> ConsCell (patternToData l, patternToData r)
    
    let rec exprToData = function
        | SymbolExpr s -> Symbol s
        | LiteralExpr data -> data
        | ListExpr es -> Ast.List <| List.map exprToData es
        | ConsExpr (l, r) -> ConsCell (exprToData l, exprToData r)
        | LetExpr (bindings, body) ->
            let bindings = List.map (fun (pat, e) -> Ast.List [patternToData pat; exprToData e]) bindings
            let body = List.map exprToData body
            Ast.List ((Symbol "let")::(Ast.List bindings)::body)
        | CaseExpr (e, arms) ->
            let e = exprToData e
            let arms = List.map (fun (pat, body) -> Ast.List ((patternToData pat)::(List.map exprToData body))) arms
            Ast.List [Symbol "case"; e; Ast.List arms]
        | IfExpr (e1, e2, e3) ->
            let e1 = exprToData e1
            let e2 = exprToData e2
            Ast.List <| (Symbol "if")::e1::e2::(Option.toList <| Option.map exprToData e3)
        | QuotedExpr q -> Quote <| exprToData q
        | LambdaExpr (args, body) ->
            let args = List.map patternToData args
            let body = List.map exprToData body
            Ast.List <| (Symbol "lambda")::(Ast.List args)::body
        | EllipsizedExpr e -> Ellipsis <| exprToData e
        
    let createTransformer (literals: string list) (bindings: Binding list) (template: LispData) =
        let templateExpr = Parsing.expr template
        let (templateExpr', renamed, renames) = renameInExpr literals (List.map (fun (Binding (k, _)) -> k) bindings) templateExpr
        let template' = exprToData templateExpr'
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