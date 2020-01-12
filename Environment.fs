module Environment

open System

open Ast

let mutable Builtins : (string * LispData) list = []

let addBuiltin (form: string * LispData) =
    Builtins <- form::Builtins

module Primitives =
    let S_t = ("t", Symbol "t")
    addBuiltin S_t
    
    let S_nil = ("nil", Symbol "nil")
    addBuiltin S_nil
    
    let private eq2 (obj1: LispData) (obj2: LispData) =
        snd <| if obj1 = obj2 then S_t else S_nil
    let private eq (objs: LispData list) =
        match objs with
            | [obj1; obj2] -> eq2 obj1 obj2
            | _ -> failwith "= takes exactly two arguments"
    let F_eq = ("=", LispFunc (new Func<LispData list, LispData>(eq)))
    addBuiltin F_eq
    
    let private plus =
        function
            | [IntLiteral a; IntLiteral b] -> IntLiteral (a+b)
            | [FloatLiteral a; FloatLiteral b] -> FloatLiteral (a+b)
            | [IntLiteral a; FloatLiteral b] -> FloatLiteral ((float a) + b)
            | [FloatLiteral a; IntLiteral b] -> FloatLiteral (a + (float b))
            | [a; b] -> failwith <| sprintf "%A and %A are not both numeric values" a b
            | _ -> failwith "+ takes exactly two arguments"
    let F_plus = ("+", LispFunc (new Func<LispData list, LispData>(plus)))
    addBuiltin F_plus
    
    let private minus =
        function
            | [IntLiteral a; IntLiteral b] -> IntLiteral (a-b)
            | [FloatLiteral a; FloatLiteral b] -> FloatLiteral (a-b)
            | [IntLiteral a; FloatLiteral b] -> FloatLiteral ((float a) - b)
            | [FloatLiteral a; IntLiteral b] -> FloatLiteral (a - (float b))
            | [a; b] -> failwith <| sprintf "%A and %A are not both numeric values" a b
            | _ -> failwith "- takes exactly two arguments"
    let F_minus = ("-", LispFunc (new Func<LispData list, LispData>(minus)))
    addBuiltin F_minus

    let private println =
        function
            | [x] ->
                match x with
                | StringLiteral s ->
                    printfn "%s" s
                | IntLiteral i ->
                    printfn "%d" i
                | FloatLiteral f ->
                    printfn "%f" f
                | _ -> printfn "%s" <| x.ToString()
                snd S_nil
            | _ ->
                failwith "println takes exactly one argument"
    let F_println = ("println", LispFunc (new Func<LispData list, LispData>(println)))
    addBuiltin F_println

    let private map = function
        | [LispFunc f; Ast.List xs] ->
            let apply x = f.Invoke([x])
            Ast.List <| List.map apply xs
        | args -> failwithf "map syntax: (map f xs).  called with %s" <| (Ast.List <| (Symbol "map")::args).ToString()
    let F_map = ("map", LispFunc (new Func<LispData list, LispData>(map)))
    addBuiltin F_map
