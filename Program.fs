open Reader

type TestCase = { code: string
                ; correctResult: Ast.LispData }

let macroTestCase1 =
    { code =
          @"(define-syntax macro
              (syntax-rules ()
                ((macro (((z ...) ...) ((x ...) y) ...))
                 '((x y z ...) ... ...)
                )
              )
            )
            (macro (((g h) (i j)) ((a b) c) ((d e) f)))"
    ; correctResult =
          List.head << read
          <| @"'((a c g h) (b f i j) (d c g h) (e f i j))"
    }

let macroTestCase2 =
    { code =
          @"(define-syntax macro2
              (syntax-rules ()
                ((macro2 ((a b ...) ...))
                 '((a b) ... ...)
                )
              )
            )
            (macro2 ((a b c) (d e f)))"
    ; correctResult =
          List.head << read
          <| @"'((a b) (d c) (a e) (d f))"
    }

let macroTestCase3 =
    { code =
          @"(define-syntax macro3
              (syntax-rules ()
                ((macro3 ((a b ...) ...))
                 '((a ... b) ... ...)
                )
              )
            )
            (macro3 ((a b c) (d e f) (g h i) (j k l)))"
    ; correctResult =
          List.head << read
          <| @"'((a d g j b) (a d g j c) (a d g j e) (a d g j f) (a d g j h) (a d g j i) (a d g j k) (a d g j l))"
    }

let macroTestCase4 =
    { code =
          @"(define-syntax macro4
              (syntax-rules ()
                ((macro4 (((z ...) ...) ((x ...) y) ...))
                 '((x y z) ... ...)
                )
              )
            )
            (macro4 (((g h) (i j)) ((a b) c) ((d e) f)))"
    ; correctResult =
          List.head << read
          <| @"'((a c g) (b f h) (d c i) (e f j))"
    }
    
let macroTestCase5 =
    { code =
          @"(define-syntax macro5
              (syntax-rules ()
                ((macro5 ((a b ...) ...))
                 '((a ... a b) ... ...)
                )
              )
            )
            (macro5 ((a b c) (d e f)))"
    ; correctResult =
          List.head << read
          <| @"'((a d a b) (a d d c) (a d a e) (a d d f))"
    }

let testCase1 =
    { code = 
          @"(defun plus (a b)
              (+ a b)
            )
            (defun car (xs)
              (let (((head . tail) xs))
                head
              )
            )
            (defun cdr (xs)
              (let (((head . tail) xs))
                tail
              )
            )
            (defun fib (m n l i)
              (println n)
              (if (= i 0)
                l
                (fib n (plus m n) (n . l) (- i 1))
              )
            )
            (defun test ()
              (let ((fibs (fib 1 1 '() 20)))
                ((car fibs) . (cdr fibs))
              )
            )"
    ; correctResult =
          List.head << read
          <| @"(10946 6765 4181 2584 1597 987 610 377 233 144 89 55 34 21 13 8 5 3 2 1)"
    }

let testCase2 =
    { code =
          @"(defun rev-tail (xs rest)
              (case xs
                (
                  (
                    (x1 x2)
                      (x2 . (x1 . rest))
                  )
                  (
                    (head . tail)
                      (rev-tail tail (head . rest))
                  )
                )
              )
            )
            (defun rev (xs) (rev-tail xs '()))
            (defun test ()
              (let ((list '(1 2 3 4 5 6 7 8 9)))
                (rev list)
              )
            )"
    ; correctResult =
          List.head << read
          <| @"(9 8 7 6 5 4 3 2 1)"
    }

let testCase3 =
    { code =
          @"(defun sumClosure (x y)
              (lambda ()
                (+ x y)
              )
            )
            (defun test ()
              (let (
                     (closure1 (sumClosure 2 2))
                     (closure2 (sumClosure 4 4))
                   )
                (+ (closure1) (closure2))
              )
            )"
    ; correctResult = Ast.IntLiteral 12
    }

let lambdaTest2 =
    @"(defun f (x y)
        (let ((g (lambda (z)
                   (f (- x 1) z)
                 )
              )
             )
          (if (= x 0)
            y
            (g (+ y 1))
          )
        )
      )
      (defun test ()
        (f 2 4)
      )"

open Macros

let testMacros =
    for s in [macroTestCase1; macroTestCase2; macroTestCase3; macroTestCase4; macroTestCase5] do
        printfn "%s" (new System.String('-', 50))
        printfn "%s" s.code
        match Reader.read s.code with
        | [ Ast.List macroDef; Ast.List macroUse ] ->
            let (_, m::_) = Parsing.defineSyntax macroDef
            match m macroUse with
            | Result.Ok(x) ->
                printfn "Expected:\n%s" (s.correctResult.ToString())
                printfn "Got:\n%s" (x.ToString())
                printfn "%s" (if s.correctResult = x then "PASS" else "FAIL")
            | x -> printfn "%A" x
        | _ -> printf "Unexpected input"

let testFunctions =
    for tc in [testCase1; testCase2; testCase3] do
        printfn "%s" (new System.String('-', 50))
        printfn "%s" tc.code
        let data = Reader.read tc.code
        let tl = Parsing.topLevel data
        let ctl = Compilation.compileTopLevel tl
        match Scope.lookup "test" ctl with
        | Option.Some(test) ->
            match Evaluation.eval ctl (Ast.List [test]) with
            | Option.Some(_, result) ->
                printfn "Expected:\n%s" (tc.correctResult.ToString())
                printfn "Got:\n%s" (result.ToString())
                printfn "%s" (if tc.correctResult = result then "PASS" else "FAIL")
            | Option.None ->
                printfn "%s" "Evaluation failed!"
        | Option.None ->
            printfn "%s" "Compilation failed!"

[<EntryPoint>]
let main argv =
    testMacros
    testFunctions
    0
