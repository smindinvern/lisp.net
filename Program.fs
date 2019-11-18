// Learn more about F# at http://fsharp.org

open System
open System.IO

open Parsing

let testString1 =
    @"(defun plus (a b)
       (+ a b))
      (defun car (xs)
       (let (((head . tail) xs)) head))
      (defun cdr (xs)
       (let (((head . tail) xs)) tail))
      (defun fib (m n l i)
       (println n)
       (if (= i 0)
           l
           (fib n (+ m n) (n . l) (- i 1))))
      (defun test ()
       (let ((fibs (fib 1 1 '() 20)))
        (println ((if nil '+ '-) 10 20))
        (cdr fibs)))"

let macroTest =
    @"(define-syntax macro
        (syntax-rules ()
          ((macro (a b ...) ...)
           ((a b) ... ...)
          )
        )
      )"
      
let macroTest2 =
    @"(define-syntax macro
        (syntax-rules ()
          ((macro (((z ...) ...) ((x ...) y) ...))
           '((x y z) ... ...)
          )
        )
      )"

open smindinvern.Parser
open Ast
open Macros

[<EntryPoint>]
let main argv =
    let ts = LineInfo.Tokenization.TokenizeString(macroTest2)
    let (s, r) = Primitives.runParser Tokenization.tokens ts ()
    match r with
        | Result.Ok(tokens) ->
            List.map (sprintf "%A") tokens |> String.concat "; " |> printfn "[%A]"
            let ts = Tokenization.Tokenize(tokens)
            let (s, r) = Primitives.runParser Reader.read ts ()
            match r with
                | Result.Ok(x) ->
                    printfn "%A" x
                    match List.head x with
                    | Ast.List xs ->
                        let (_, m::_) = Parsing.defineSyntax xs
                        printfn "%A" m
                        // let result = m [ Symbol "macro"; Ast.List [ Symbol "a"; Symbol "b"; Symbol "c" ]; Ast.List [ Symbol "d"; Symbol "e"; Symbol "f" ] ]
                        // let result = m [ Symbol "macro"; Ast.List <| List.map Symbol [ "a"; "b"; "c"; "d" ]; Ast.List <| List.map Symbol [ "e"; "f"; "g"; "h" ]; Ast.List <| List.map Symbol [ "i"; "j"; "k"; "l" ] ]
                        let result = m [ Symbol "macro"; Ast.List [ Ast.List [ Ast.List [ Symbol "g"; Symbol "h" ]; Ast.List [ Symbol "i"; Symbol "j" ] ]; Ast.List [ Ast.List [ Symbol "a"; Symbol "b" ]; Symbol "c" ]; Ast.List [ Ast.List [ Symbol "d"; Symbol "e" ]; Symbol "f" ] ] ]
                        printfn "%A" result
                    | _ -> printf "Unexpected input: %A" x
//                    let parsed = Parsing.topLevel x
//                    let compiled = Compilation.compileTopLevel parsed
//                    match Scope.lookup "test" compiled with
//                        | Some(LispFunc f) ->
//                            printfn "%A" (f.Invoke([]))
//                        | x -> printfn "Compilation error: %A" x
                | Result.Error(e) -> printfn "%s" <| e.ToString()
        | Result.Error(e) -> printfn "%s" <| e.ToString()
    0 // return an integer exit code
