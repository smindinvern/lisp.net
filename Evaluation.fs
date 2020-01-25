module Evaluation

    open Ast
    
    let concatOptions<'a> (a: ('a list) option) (b: ('a list) option) =
        Option.bind (fun head -> Option.map (fun tail -> head @ tail) b) a
    
    open Scope
    
    let rec bindList = function
        | (p::ps, List (o::os)) ->
            concatOptions (bindPattern p o) (bindList (ps, List os))
        | ([], List []) -> Some []
        | _ -> None
    and bindPattern (pat: Pattern) (obj: LispData) : (Binding list) option =
        match pat with
            | SymbolPattern b ->
                b.ldr := Option.Some(obj)
                Some [b]
            | LiteralPattern l ->
                if l = obj then
                    Some []
                else
                    None
            | ListPattern ps -> bindList (ps, obj)
            | ConsPattern (head, tail) ->
                match obj with
                    | List (h::t) ->
                        concatOptions (bindPattern head h) (bindPattern tail (List t))
                    | _ -> None
    
    open smindinvern.Utils

    let rec eval (scope: Scope) = function
        | Symbol s ->
            Option.bind
                (fun (x: Binding) -> Option.map (mkPair scope) !x.ldr)
                (scope.Lookup(s)) 
        | List (f::args) ->
            match eval scope f with
                | None -> None
                | Some(scope', f') ->
                    match f' with
                        | LispFunc func ->
                            Some(scope', func.Invoke(args))
                        | _ -> failwith "Not a callable object"
        | x -> Some(scope, x)
