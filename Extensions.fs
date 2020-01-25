module Extensions
    open System.Collections.Generic
    open System.Runtime.CompilerServices
    
    [<AbstractClass; Sealed; Extension>]
    type Extensions =
        [<Extension>]
        static member KeyValuePairs<'k, 'v>(d: IDictionary<'k, 'v>) =
            Seq.zip (d.Keys) (d.Values)
        [<Extension>]
        static member tryGetValue<'k, 'v>(d: IDictionary<'k, 'v>, key: 'k) =
            let v = ref Unchecked.defaultof<'v>
            if d.TryGetValue(key, v) then
                Some(!v)
            else
                None
