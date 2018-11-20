open Json

[<EntryPoint>]
let main args =
    let j =
        """ { "kalle": "anka" } """
        |> JsonValue.ofString id failwith
        // |> printfn "%A"

    JsonValue.toString JsonFormatting.Indented j
    |> printfn "%A"
    0