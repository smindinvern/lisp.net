module Scope

    open Ast
    open Extensions
    
    open System.Collections.Generic
    
    type Scoped<'k, 'v when 'k : equality>(scopes : IDictionary<'k, 'v> list) =
        static let rec lookup (key: 'k) (scopes: IDictionary<'k, 'v> list) =
            match scopes with
            | [] -> Option.None
            | scope::hidden ->
                match scope.tryGetValue(key) with
                | Option.None -> lookup key hidden
                | v -> v
            
        member this.FreshScope() =
            Scoped<'k, 'v>((dict [])::scopes)
        member this.Lookup(key: 'k) =
            lookup key scopes
        member this.Add(key: 'k, v: 'v) =
            this.AddRange(Seq.singleton (key, v))
        member this.AddRange(kvps: seq<'k * 'v>) =
            match scopes with
            | [] ->
                this.FreshScope().AddRange(kvps)
            | scope::hidden ->
                let kvps' = Seq.append (kvps) (scope.KeyValuePairs())
                Scoped<'k, 'v>((dict kvps')::hidden)
        member this.PopScope() =
            match scopes with
            | _::hidden ->
                Scoped<'k, 'v>(scopes)
            | _ ->
                Scoped<'k, 'v>([])
                
    type Scope = Scoped<string, Binding>
    
    open System.Runtime.CompilerServices
    
    [<AbstractClass; Sealed; Extension>]
    type Extensions =
        [<Extension>]
        static member LookupValue(scope: Scope, key: string) =
            Option.bind (fun (b: Binding) -> !b.ldr) <| scope.Lookup(key)