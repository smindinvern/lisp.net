module Scope

    open Ast
    
    open System.Collections.Generic
    
    type Scope = System.Collections.Generic.Dictionary<string, LispData> list
    
    type Binding = string * LispData
    
    let rec lookup s : Scope -> LispData option =
        function
            | [] -> None
            | scope::hidden ->
                let mutable x = IntLiteral 0
                if scope.TryGetValue(s, &x) then
                    Some(x)
                else
                    lookup s hidden
    
    let add ((s, v): Binding) (scope: Scope) =
        match scope with
            | head::tail when Option.isNone <| lookup s scope ->
                head.[s] <- v
                head::tail
            | scope' ->
                let x = new System.Collections.Generic.Dictionary<string, LispData>()
                x.[s] <- v
                x::scope'
