type TestCase = { code: string
                ; correctResult: Ast.LispData }

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


let runFile (fs: System.IO.StreamReader) =
    let data = Reader.read <| fs.ReadToEnd()
    let (macros, defuns) = Parsing.topLevel data
    let ctl = Compilation.compileTopLevel defuns
    match ctl.Lookup("main") with
    | Option.Some(main) ->
        try
            match Evaluation.eval ctl (Ast.List [(!main.ldr).Value]) with
            | Option.Some(_, result) ->
                printfn "%s" (result.ToString())
            | Option.None ->
                printfn "Evaluation failed!"
        with
        | e -> printfn "%A" e
    | Option.None ->
        printfn "Compilation failed!"

[<EntryPoint>]
let main argv =
    if argv.Length <> 1 then
        printfn "Usage: lisp.net File.lsp"
    else
        using (System.IO.File.OpenText(argv.[0])) runFile
    0
