// Learn more about F# at http://fsharp.org

open System
open Reaptor.Json

[<EntryPoint>]
let main argv =

    """ { "kalle": "anka" } """
    |> JsonValue.ofString id failwith
    |> JsonValue.toString JsonFormatting.Indented
    |> printfn "%A"

    0 // return an integer exit code
