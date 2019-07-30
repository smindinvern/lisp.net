module Evaluation

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
