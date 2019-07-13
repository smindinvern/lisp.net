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

open Zipper
open Parser
open Data

[<EntryPoint>]
let main argv =
    let arr = Array.mapi (fun i c -> (c, i)) <| testString1.ToCharArray()
    let tokenStream = new Zipper<char*int>(ref arr, 0)
    let (s, r) = runParser Tokenization.tokens tokenStream ()
    match r with
        | Result.Ok(tokens) ->
            printfn "%A" tokens
            let arr = List.toArray tokens
            let tokenStream = new Zipper<Tokenization.Token>(ref arr, 0)
            let (s, r) = runParser Ast.topLevel tokenStream ()
            match r with
                | Result.Ok(x) ->
                    printfn "%A" x
                    let compiled = Compilation.compileTopLevel x
                    match Scope.lookup "test" compiled with
                        | Some(LispFunc f) ->
                            printfn "%A" (f.Invoke([]))
                        | x -> printfn "Compilation error: %A" x
                | Result.Error(e) -> printfn "%s" e
        | Result.Error(e) -> printfn "%s" e
    0 // return an integer exit code
