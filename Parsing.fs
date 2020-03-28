module rec Parsing

    open Ast
    open Macros.Types
    open Extensions

    open System.Collections.Generic

    open smindinvern.State.Lazy
    open smindinvern.Utils
    
    open Patterns

    let withState (s: 's) (m: State<'s, 'a>) =
        state {
            let! s' = get
            do! put s
            let! result = m
            do! put s'
            return result
        }
    
    type ParserState = { Macros : IDictionary<string, Macro>
                       ; Bindings : IDictionary<string, Ast.Binding> }
    
    type ExprParser<'a> = State<ParserState, 'a>
    let tryGetMacro (m: string) : ExprParser<Macro option> =
        state {
            let! s = get
            return s.Macros.tryGetValue(m)
        }

    let internal addBoundVars' bs ps =
        // TODO: is it a bug to insert a duplicate key here?
        let bindingsSeq = Seq.map (fun (kvp: KeyValuePair<string, Ast.Binding>) -> (kvp.Key, kvp.Value)) <| Seq.cast ps.Bindings
        let kvps = List.map (fun (b: Ast.Binding) -> (b.sym, b)) bs
        let bindings' = Seq.append bindingsSeq kvps
        { ps with Bindings = dict bindings' }

    let addBoundVars (bs: Ast.Binding list) =
        modify (addBoundVars' bs)
    
    let rec pattern = function
        | Symbol sym ->
            state {
                do! addBoundVars [sym]
                return SymbolPattern sym
            }
        | ConsCell (left, right) ->
            state {
                let! l = pattern left
                let! r = pattern right
                return ConsPattern (l, r)
            }
        | List pats -> ListPattern <@> (sequence <| List.map pattern pats)
        | Quote _ -> failwith "Quoted expressions cannot appear in patterns"
        | LispFunc _ -> failwith "Functions cannot appear in patterns"
        | d -> inject <| Pattern.LiteralPattern d

    let rec patternBindings = function
        | SymbolPattern b -> [b]
        | ConsPattern (l, r) -> (patternBindings l) @ (patternBindings r)
        | ListPattern pats -> List.collect patternBindings pats
        | Pattern.LiteralPattern _ -> []
    let patternVars = (List.map (fun (b: Ast.Binding) -> b.sym)) << patternBindings

    let rec findFreeVars (e: Expr) (free: string list) =
        match e with
        | LetExpr (bs, _) ->
            let (_, free') = foldExpr findFreeVars [] e
            (e, collectFreeVars (free @ free') bs)
        | CaseExpr (e', arms) ->
            let (_, free') = foldExpr findFreeVars [] e'
            let arms' = List.map (fun (pat, e) -> (pat, ListExpr e)) arms
            (e, collectFreeVars (free @ free') arms')
        | LambdaExpr (args, body) ->
            (e, collectFreeVars' free args body)
        | SymbolExpr s -> (e, s.sym::free)
        | _ -> foldExpr findFreeVars free e
    and collectFreeVars' free pats exprs =
        let pvars = List.collect patternVars pats
        let (_, evars) = findFreeVars (ListExpr exprs) []
        let free' = List.distinct (free @ evars)
        List.except pvars free'
    and collectFreeVars free bindings =
        let (pats, exprs) = List.unzip bindings
        collectFreeVars' free pats exprs

    module Patterns =
        let (|If|_|) es =
            match es with
            | (Symbol s)::test::ifTrue::rest when s.sym = "if" ->
                let ifFalse =
                    match rest with
                    | [] -> Option.None
                    | [ifFalse] -> Option.Some(ifFalse)
                    | _ -> failwithf "Malformed if expression: %s" <| (List es).ToString()
                Option.Some(test, ifTrue, ifFalse)
            | _ -> Option.None
        let (|Let|_|) = function
            | (Symbol s)::(List bindings)::body when s.sym = "let" ->
                Option.Some(bindings, body)
            | _ -> Option.None
        let (|Case|_|) = function
            | [ Symbol s; e; List arms ] when s.sym = "case" ->
                Option.Some(e, arms)
            | _ -> Option.None
        let (|Lambda|_|) = function
            | (Symbol s)::(List paramList)::body when s.sym = "lambda" ->
                Option.Some(paramList, body)
            | _ -> Option.None

    type ExpressionParser() =
        class
            abstract member ParseExpression : LispData -> ExprParser<Expr>
            default this.ParseExpression ld =
                match ld with
                | Symbol sym -> this.ParseSymbol sym
                | Quote q -> this.ParseQuote q
                | List es ->
                    match es with
                    | If(test, ifTrue, ifFalse) -> this.ParseIf test ifTrue ifFalse
                    | Let(bindings, body) -> this.ParseLetBinding bindings body
                    | Case(e, arms) -> this.ParseCase e arms
                    | Lambda(paramList, body) -> this.ParseLambda paramList body
                    | es -> this.ParseList es
                | ConsCell (left, right) -> this.ParseConsCell left right
                | Ellipsis _ -> failwith "Ellipses only allowed in macro definitions"
                | x -> inject <| LiteralExpr x
            
            abstract member ParseSymbol : Ast.Binding -> ExprParser<Expr>
            default this.ParseSymbol b =
                state {
                    let! s = get
                    match s.Bindings.tryGetValue(b.sym) with
                    | Option.Some(v) -> return SymbolExpr v
                    | Option.None -> return SymbolExpr <| Ast.Binding(b.sym) // failwithf "Reference to undefined variable `%s'" b.sym
                }                

            abstract member ParseQuote : LispData -> ExprParser<Expr>
            default this.ParseQuote q =
                inject <| QuotedExpr q
            
            abstract member ParseIf : LispData -> LispData -> LispData option -> ExprParser<Expr>
            default this.ParseIf test ifTrue ifFalse =
                state {
                    let! test = this.ParseExpression test
                    let! ifTrue = this.ParseExpression ifTrue
                    let! ifFalse =
                        match ifFalse with
                        | Option.Some(x) -> Option.Some <@> this.ParseExpression x
                        | Option.None -> inject Option.None
                    return IfExpr (test, ifTrue, ifFalse)
                }

            abstract member ParseLetBinding : LispData list -> LispData list -> ExprParser<Expr>
            default this.ParseLetBinding bindings body =
                let binding = function
                    | List [p; e] ->
                        state {
                            let! pat = pattern p
                            let! s = get
                            // Parse the contents of @e *before* adding contents of @pat to the list of bound variables.
                            let! e' = this.ParseExpression e
                            // Anything bound within @e is dropped (as it is out of scope inside the let-binding body).
                            do! put s
                            return LetBinding (pat, e')
                        }
                    | _ ->
                        failwith "Invalid form for let-binding"
                state {
                    let! s = get
                    let! bindings = sequence <| List.map binding bindings
                    let! body = sequence <| List.map this.ParseExpression body
                    // Restore original state.
                    do! put s
                    return LetExpr (bindings, body)
                }
            
            member this.caseArm = function
                | List (p::es) ->
                    state {
                        let! s = get
                        let! pat = pattern p
                        let! es = sequence <| List.map this.ParseExpression es
                        // Restore original state.
                        do! put s
                        return (pat, es)
                    }
                | _ -> failwith "Expected case-arm"

            abstract member ParseCase : LispData -> LispData list -> ExprParser<Expr>
            default this.ParseCase e arms =
                state {
                    let! e = this.ParseExpression e
                    let! arms = sequence <| List.map this.caseArm arms
                    return CaseExpr (e, arms)
                }                

            // TODO: Lambda-captured values need to be resolved at runtime!
            abstract member ParseLambda : LispData list -> LispData list -> ExprParser<Expr>
            default this.ParseLambda paramList body =
                state {
                    let! s = get
                    do! put { s with Bindings = dict [] }
                    let! pats = sequence <| List.map pattern paramList
                    let! body = sequence <| List.map this.ParseExpression body
                    // Restore original state.
                    do! put s
                    return LambdaExpr (pats, body)
                }           
            
            abstract member ParseList : LispData list -> ExprParser<Expr>
            default this.ParseList ld =
                match ld with
                | (Symbol s)::args ->
                    state {
                        match! tryGetMacro s.sym with
                        | Option.Some(m) ->
                            let! st = get
                            resetI()
                            return! m.Transformer ((Symbol s)::args) (fun ld -> withState st <| this.ParseExpression ld)
                        | Option.None ->
                            return! ListExpr <@> (sequence <| List.map this.ParseExpression ld)
                    }
                | _ -> ListExpr <@> (sequence <| List.map this.ParseExpression ld)
            
            abstract member ParseConsCell : LispData -> LispData -> ExprParser<Expr>
            default this.ParseConsCell left right =
                state {
                    let! l = this.ParseExpression left
                    let! r = this.ParseExpression right
                    return ConsExpr (l, r)
                }
        end
    
    let expressionParser = ExpressionParser()
    
    type MacroParser(Parse : LispData -> ExprParser<Expr>) =
        class
            inherit ExpressionParser()

            let rec transform (ld: LispData) =
                let rec f (ld: LispData) () =
                    match ld with
                    | Ast.Symbol s ->
                        if s.sym.EndsWith('#') then
                            ((!s.ldr).Value, ())
                        else
                            (Ast.Symbol s, ())
                    | _ -> foldLispData f () ld
                fst <| foldLispData f () ld
            
            override this.ParseSymbol b =
                state {
                    if b.sym.EndsWith('#') then
                        return! Parse((!b.ldr).Value)
                    else
                        return! expressionParser.ParseSymbol b
                }
            
            override this.ParseQuote ld =
                inject <| QuotedExpr (transform ld)
        end
    
    let private foldM (f: 'acc -> 'a -> State<'s, 'acc>) (s: State<'s, 'acc>) (xs: 'a list) : State<'s, 'acc> =
        let g = flip f
        List.fold (fun (s: State<'s, 'acc>) (x: 'a) -> (s >>= (g x))) s xs

    
    
    let defun defuns ld  =
        match ld with
        | List ((Symbol s)::(Symbol name)::(List paramList)::body) when s.sym = "defun" ->
            state {
                // Add binding for this definition *first*, so that recursive references
                // can be resolved.
                do! addBoundVars [name]
                let! s = get
                let! paramList = sequence <| List.map pattern paramList
                let! body = sequence <| List.map expressionParser.ParseExpression body
                do! put s
                let thisDefun = (name.sym, paramList, body)
                return (thisDefun::defuns)
            }
        | List ((Symbol s)::rest) when s.sym = "define-syntax" ->
            let m = Macros.Parsing.defineSyntax rest
            state {
                let! s = get
                let d = dict <| (m.Keyword, m)::(List.ofSeq <| s.Macros.KeyValuePairs())
                do! put { s with Macros = d }
                return defuns
            }
        | x ->
            failwithf "Not a defun or macro definition: %A" x
            // state {
            //     let! e = expr x
            //     let scope = Compilation.Builtins.scope
            //     let c = Compilation.compileExpr e
            //     do! inject <| printfn "%A" (c scope)
            //     return defuns
            // }

    let env =
        Environment.Builtins
        |> List.map (function
            | (s, Symbol sym) -> (s, sym)
            | (s, ld) -> (s, Ast.Binding(s, ld)))
        |> dict
    
    let topLevel defuns =
        let parsed =
            foldM defun (inject <| []) defuns
        let (s, defuns) = runState parsed { Bindings = env; Macros = dict [] }
        (s.Macros, List.rev defuns)

    module Macros =

        open smindinvern
        open smindinvern.Parser
        open smindinvern.Parser.Types
        
        // See R6RS sections 11.18 and 11.19.
        // This implementation uses SRFI 149 semantics.

        module Types =
            type Macro = { Keyword: string;
                           Transformer: LispData list -> (LispData -> ExprParser<Expr>) -> ExprParser<Expr> }
  
            // Parse the pattern into a SyntaxPattern first.  This will make it
            // easier to handle ellipses when constructing the PatternMatcher.
            type SyntaxPattern =
                | SyntaxListPattern of SyntaxPattern list
                | SyntaxConsPattern of SyntaxPattern * SyntaxPattern
                | IdentifierPattern of string
                | LiteralPattern of string
                | ConstantPattern of LispData 
                | EllipsizedPattern of SyntaxPattern
            
            type Values<'a> =
                | EllipsizedValue of Values<'a> list
                | Repeat of Values<'a>
                | Value of 'a
            type Binding<'a> =
                | Binding of string * Values<'a>

            // Match a Lisp list to a pattern to produce a set of bindings.
            type PatternMatcher = Parser<LispData, unit, Binding<LispData> list>

        module PatternMatching =
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
            module SyntaxRules =
                let uniquify (s: string) = sprintf "%s#%i" s (nextI())
                let rec renameIdentifiers' (bound: HashSet<string>) (ld: LispData) (renames: (string * string) list) =
                    match ld with
                    | Symbol s ->
                        if bound.Contains(s.sym) then
                            let renamed = uniquify s.sym
                            (Symbol(Ast.Binding(renamed)), (s.sym, renamed)::renames)
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
                        [(s.sym, 0)]
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

                let rec repeatNTimes (v: Values<'a>) (n: int) =
                    if n = 0 then
                        v
                    else
                        repeatNTimes (Repeat v) (n - 1)

                // Add repeats to ellipsized bindings to replicate inputs as necessary.
                let reshapeBindings (bindings: Binding<'a> list) (renames: (string * string) list) (depths: IDictionary<string, int>) =
                    // For each variable @x in the input pattern with corresponding, uniquely-named instances @x_1..@x_n in the template,
                    // map each @x_i to the set of values bound to @x in the input.
                    let bindingsDict = dict <| List.map (fun (Binding (name, v)) -> (name, v)) bindings
                    let bindings = List.map (fun (old_name, new_name) -> (new_name, bindingsDict.[old_name])) renames
                    // If the number of ellipses following a variable in the template exceeds the number of ellipses following
                    // the variable in the input pattern, the bound values are repeated in the output.
                    let reshape (name: string, v: Values<'a>) =
                        (name, repeatNTimes v ((depths.[name]) - (getBindingEllipsisDepth v)))
                    dict <| Seq.map reshape bindings

                let splitBindings (xs: (string * Values<LispData>) list) =
                    let f (name, v) (c, e, r) =
                        match v with
                        | EllipsizedValue vs ->(c, (name, vs)::e, r)
                        | Repeat v -> (c, e, (name, v)::r)
                        | Value _ -> ((name, v)::c, e, r)
                    let (constants, ellipses, repeats) =
                        List.foldBack f xs ([], [], [])
                    (constants, ellipses, repeats)

                // Expand ellipsized data, marking each occurrence of a macro-bound identifier.  These marks are used
                // when parsing the output of the macro transformer to identify data that needs to be parsed in its
                // original context.
                let rec expand (macroBindings: IDictionary<string, Values<LispData>>) (ld: LispData) () =
                    match ld with
                    | Ast.List templates ->
                        let (ld, renames) = expandList macroBindings templates ()
                        (Ast.List <| ld, renames)
                    | Symbol s ->
                        // If this symbol is a macro-bound value, replace it with a new marked identifier which
                        // is bound to the corresponding data.
                        match macroBindings.tryGetValue(s.sym) with
                        | Option.None -> (Symbol s, ())
                        | Option.Some(Value v) ->
                            let uniqueName = sprintf "%s#" s.sym
                            (Symbol <| Ast.Binding(uniqueName, v), ())
                        | _ -> failwith "Incorrect ellipsis depth."
                    | _ -> foldLispData (expand macroBindings) () ld
                and expandList (macroBindings: IDictionary<string, Values<LispData>>) (ld: LispData list) () =
                    match ld with
                    | (Ellipsis e)::xs ->
                        let (ld1, _) = expandEllipsis macroBindings e ()
                        let (ld2, _) = expandList macroBindings xs ()
                        (ld1 @ ld2, ())
                    | x::xs ->
                        let (ld1, _) = expand macroBindings x ()
                        let (ld2, _) = expandList macroBindings xs ()
                        (ld1::ld2, ())
                    | [] -> ([], ())
                and expandEllipsis (macroBindings: IDictionary<string, Values<LispData>>) (ld: LispData) () =
                    let kvps = List.ofSeq <| macroBindings.KeyValuePairs()
                    let (constants, ellipsized, repeats) = splitBindings kvps
                    let (names, ellipsized) = List.unzip ellipsized
                    let ellipsized' = List.transpose ellipsized
                    let repeat (ellipsized: Values<LispData> list) =
                        let xs = List.zip names ellipsized
                        let bindings = xs @ repeats @ constants
                        match ld with
                        | Ellipsis e' -> expandEllipsis (dict bindings) e' ()
                        | e ->
                            let (ld, _) = expand (dict bindings) e ()
                            ([ld], ())
                    let xs = List.map repeat ellipsized'
                    let (lds, _) = List.unzip xs
                    (List.concat lds, ())
                    
                let createTransformer (literals: string list) (template: LispData) (boundVars: HashSet<string>) =
                    // For each variable @x in the input pattern, rename all occurrences of @x in @template to be unique.
                    let (template, renames) = renameIdentifiers boundVars template
                    // Get the number of ellipses each variable in @template is followed by
                    let depths = getEllipsisDepths template
                    fun (bindings: Binding<LispData> list) (parse: LispData -> ExprParser<Expr>) ->
                        // Parse each matched datum in the context in which it appears.
                        let bindings = reshapeBindings bindings renames depths
                        let (expanded, _) = expand bindings template ()
                        let result = MacroParser(parse).ParseExpression(expanded)
                        result

        module Parsing =
            open smindinvern.Alternative
            open smindinvern.Parser.Primitives
            
            let rec pattern (literals : string list) = function
                | Symbol sym ->
                    if List.contains sym.sym literals then
                        LiteralPattern sym.sym
                    else
                        IdentifierPattern sym.sym
                | ConsCell (l, r) ->
                    SyntaxConsPattern (pattern literals l, pattern literals r)
                | List pats ->
                    SyntaxListPattern <| List.map (pattern literals) pats
                | Ellipsis pat ->
                    EllipsizedPattern <| pattern literals pat
                | Quote _ -> failwith "Quoted expressions cannot appear in patterns"
                | LispFunc _ -> failwith "Functions cannot appear in patterns"
                | d -> ConstantPattern d
            
            let rec srPatternVars = function
                | IdentifierPattern s -> [s]
                | SyntaxListPattern pats -> List.collect srPatternVars pats
                | SyntaxConsPattern (l, r) -> List.collect srPatternVars [l; r]
                | EllipsizedPattern e -> srPatternVars e
                | _ -> []
                
            let syntaxRule' (literals: string list) (ps: LispData list) (template: LispData) =
                let (p::pats) = List.map (pattern literals) ps
                let boundVars = new HashSet<string>(List.collect srPatternVars pats)
                let matcher = PatternMatching.listMatcher' (p::pats)
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
                | (Symbol s)::(List literals)::rules when s.sym = "syntax-rules" ->
                    // TODO: check form of @literals
                    let literals' = List.map (function
                        | Ast.Symbol s -> s.sym
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
                    { Keyword = keyword.sym; Transformer = runMacro }
                | _ -> failwith "Incorrect form for define-syntax"
