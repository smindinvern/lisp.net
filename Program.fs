let runFile (fs: System.IO.StreamReader) =
    let data = Reader.read <| fs.ReadToEnd()
    let (macros, defuns) = Parsing.topLevel data
    let ctl = Interpreter.compileTopLevel defuns
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
