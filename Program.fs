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
    
let macroTestCase6 =
    { code =
          @"(define-syntax macro6
              (syntax-rules ()
                ((macro6 ((a b c ...) ...))
                  ((let ((a b))
                     c ...
                   ) ...
                  )
                )
              )
            )
            (macro6 ((a b c d) (d c b a)))"
    ; correctResult =
        List.head << read
        <| @"((let ((a b)) c d) (let ((d c)) b a))"
    }

let macroTestCase7 =
    { code =
          @"(define-syntax macro7
              (syntax-rules ()
                ((macro7 ((a b c ...) ...))
                  ((let ((d b))
                     a
                     d
                     (let ((e (c ...)))
                       e
                     )
                   ) ...
                  )
                )
              )
            )
            (macro7 ((a b c d) (d c b a)))"
    ; correctResult =
        Ast.List [
            Ast.List [
                Ast.Symbol "let";
                Ast.List [
                    Ast.List [
                        Ast.Symbol "&d";
                        Ast.Symbol "b"
                    ]
                ];
                Ast.Symbol "a";
                Ast.Symbol "&d";
                Ast.Symbol "c";
                Ast.Symbol "d"
            ];
            Ast.List [
                Ast.Symbol "let";
                Ast.List [
                    Ast.List [
                        Ast.Symbol "&d";
                        Ast.Symbol "c"
                    ]
                ];
                Ast.Symbol "d";
                Ast.Symbol "&d";
                Ast.Symbol "b";
                Ast.Symbol "a"
            ];
        ]
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

let testCase4 =
    { code =
          @"(define-syntax map
              (syntax-rules ()
                ((map f (xs ...))
                 '((f xs) ...)
                )
              )
            )
            (defun test ()
              (let ((f (lambda (x) (+ x 1))))
                (map f (1 2 3 4 5))
              )
            )"
      ; correctResult = Ast.Quote <| Ast.List (List.map Ast.IntLiteral [2; 3; 4; 5; 6])
    }

let testCase5 =
    { code =
          @"(define-syntax macro
              (syntax-rules ()
                ((macro x f)
                 (let ((y x))
                   (f y)
                 )
                )
              )
            )
            (defun test ()
              (let ((x 12)
                    (y 2))
                (let ((f (lambda (x) (+ x y))))
                  (macro x f)
                )
              )
            )"
        ; correctResult = Ast.IntLiteral 14
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

open Ast
open Macros.Extensions
open System.Collections.Generic

let defun (macros, defuns) ld  =
    match ld with
    | List ((Symbol "defun")::(Symbol name)::(List paramList)::body) ->
        let boundVars = new HashSet<string>(Seq.ofList <| List.map (fun (x, _, _) -> x) defuns)
        let thisDefun = (name, List.map (Parsing.pattern macros) paramList, List.map (Parsing.expr boundVars macros) body)
        (macros, thisDefun::defuns)
    | List ((Symbol "define-syntax")::rest) ->
        let m = Macros.Parsing.defineSyntax rest
        (dict <| (m.Keyword, m)::(List.ofSeq <| macros.KeyValuePairs()), defuns)
    | x ->
        let boundVars = new HashSet<string>(Seq.ofList <| List.map (fun (x, _, _) -> x) defuns)
        let e = Parsing.expr boundVars macros x
        let scope = Compilation.Builtins.scope
        let c = Compilation.compileExpr e
        printfn "%A" (c scope)
        (macros, defuns)

let topLevel defuns =
    let (macros, defuns) =
        List.fold defun (dict [], []) defuns
    (macros, List.rev defuns)

let testMacros =
    for s in [macroTestCase1; macroTestCase2; macroTestCase3; macroTestCase4; macroTestCase5; macroTestCase6; macroTestCase7] do
        printfn "%s" (new System.String('-', 50))
        printfn "%s" s.code
        match Reader.read s.code with
        | [ Ast.List ((Symbol "define-syntax")::macroDef); macroUse ] ->
            let m = Macros.Parsing.defineSyntax macroDef
            try
                let e = Parsing.expr (new HashSet<string>()) (dict [(m.Keyword, m)]) macroUse
                printfn "Expected:\n%s" (s.correctResult.ToString())
                printfn "Got:\n%s" (e.ToString())
            with
            | e -> printfn "%A" e
        | _ -> printf "Unexpected input"

let testFunctions =
    for tc in [testCase1; testCase2; testCase3; testCase4; testCase5] do
        printfn "%s" (new System.String('-', 50))
        printfn "%s" tc.code
        let data = Reader.read tc.code
        let (macros, defuns) = topLevel data
        let ctl = Compilation.compileTopLevel defuns
        match Scope.lookup "test" ctl with
        | Option.Some(test) ->
            try
                match Evaluation.eval ctl (Ast.List [test]) with
                | Option.Some(_, result) ->
                    printfn "Expected:\n%s" (tc.correctResult.ToString())
                    printfn "Got:\n%s" (result.ToString())
                    printfn "%s" (if tc.correctResult = result then "PASS" else "FAIL")
                | Option.None ->
                    printfn "%s" "Evaluation failed!"
            with
            | e -> printfn "%A" e
        | Option.None ->
            printfn "%s" "Compilation failed!"

[<EntryPoint>]
let main argv =
    testMacros
    testFunctions
    0
