// --------------------------------------------------------------------------------------
// Copyright (c) Kristoffer Löfberg
// This sample code is provided "as is" without warranty of any kind.
// We disclaim all warranties, either express or implied, including the
// warranties of merchantability and fitness for a particular purpose.
//
// Json parser originally copied from FSharp.Data Json
// https://github.com/fsharp/FSharp.Data
// --------------------------------------------------------------------------------------

namespace Reaptor.Json

open System
open System.Text
open System.Globalization

[<AutoOpen>]
module private InternalHelpers =
    /// Convert the result of TryParse to option type
    let asOption = function true, v -> Some v | _ -> None

    let (|OneOfIgnoreCase|_|) set str =
        if Array.exists (fun s -> StringComparer.OrdinalIgnoreCase.Compare(s, str) = 0) set then Some() else None

    /// Conversions from string to string/int/int64/decimal/float/boolean/datetime/timespan/guid options
    type TextConversions private() =
        /// `%` `‰` `‱`
        static member val DefaultNonCurrencyAdorners = [| '%'; '‰'; '‱' |] |> Set.ofArray

        /// `¤` `$` `¢` `£` `¥` `₱` `﷼` `₤` `₭` `₦` `₨` `₩` `₮` `€` `฿` `₡` `៛` `؋` `₴` `₪` `₫` `₹` `ƒ`
        static member val DefaultCurrencyAdorners = [| '¤'; '$'; '¢'; '£'; '¥'; '₱'; '﷼'; '₤'; '₭'; '₦'; '₨'; '₩'; '₮'; '€'; '฿'; '₡'; '៛'; '؋'; '₴'; '₪'; '₫'; '₹'; 'ƒ' |] |> Set.ofArray

        static member val private DefaultRemovableAdornerCharacters =
            Set.union TextConversions.DefaultNonCurrencyAdorners TextConversions.DefaultCurrencyAdorners

        //This removes any adorners that might otherwise casue the inference to infer string. A notable a change is
        //Currency Symbols are now treated as an Adorner like a '%' sign thus are now independant
        //of the culture. Which is probably better since we have lots of scenarios where we want to
        //consume values prefixed with € or $ but in a different culture.
        static member private RemoveAdorners (value:string) =
            String(value.ToCharArray() |> Array.filter (not << TextConversions.DefaultRemovableAdornerCharacters.Contains))

        static member AsDecimal cultureInfo text =
            Decimal.TryParse(TextConversions.RemoveAdorners text, NumberStyles.Currency, cultureInfo) |> asOption

        /// if useNoneForMissingValues is true, NAs are returned as None, otherwise Some Double.NaN is used
        static member AsFloat missingValues useNoneForMissingValues cultureInfo (text:string) =
            match text.Trim() with
            | OneOfIgnoreCase missingValues -> if useNoneForMissingValues then None else Some Double.NaN
            | _ -> Double.TryParse(text, NumberStyles.Any, cultureInfo)
                   |> asOption
                   |> Option.bind (fun f -> if useNoneForMissingValues && Double.IsNaN f then None else Some f)

module private UnicodeHelper =

    // used http://en.wikipedia.org/wiki/UTF-16#Code_points_U.2B010000_to_U.2B10FFFF as a guide below
    let getUnicodeSurrogatePair num =
        // only code points U+010000 to U+10FFFF supported
        // for coversion to UTF16 surrogate pair
        let codePoint = num - 0x010000u
        let HIGH_TEN_BIT_MASK = 0xFFC00u                     // 1111|1111|1100|0000|0000
        let LOW_TEN_BIT_MASK = 0x003FFu                      // 0000|0000|0011|1111|1111
        let leadSurrogate = (codePoint &&& HIGH_TEN_BIT_MASK >>> 10) + 0xD800u
        let trailSurrogate = (codePoint &&& LOW_TEN_BIT_MASK) + 0xDC00u
        char leadSurrogate, char trailSurrogate


type JsonValue =
    | JsStr of string
    | JsNumber of decimal
    | JsFloat of float
    | JsObj of properties:(string * JsonValue) list
    | JsArr of elements:JsonValue list
    | JsBool of bool
    | JsNull

exception private JsonParserException of string

type private JsonParser(jsonText:string) =

    let mutable i = 0
    let s = jsonText

    let buf = StringBuilder() // pre-allocate buffers for strings

    // Helper functions
    let skipWhitespace() =
      while i < s.Length && Char.IsWhiteSpace s.[i] do
        i <- i + 1
    let isNumChar c =
      Char.IsDigit c || c = '.' || c='e' || c='E' || c='+' || c='-'
    let throw() =
      let msg =
        sprintf
          "Invalid JSON starting at character %d, snippet = \n----\n%s\n-----\njson = \n------\n%s\n-------"
          i (jsonText.[(max 0 (i-10))..(min (jsonText.Length-1) (i+10))]) (if jsonText.Length > 1000 then jsonText.Substring(0, 1000) else jsonText)
      raise (JsonParserException msg)
    let ensure cond =
      if not cond then throw()

    // Recursive descent parser for JSON that uses global mutable index
    let rec parseValue() =
        skipWhitespace()
        ensure(i < s.Length)
        match s.[i] with
        | '"' -> JsStr(parseString())
        | '-' -> parseNum()
        | c when Char.IsDigit(c) -> parseNum()
        | '{' -> parseObject()
        | '[' -> parseArray()
        | 't' -> parseLiteral("true", JsBool true)
        | 'f' -> parseLiteral("false", JsBool false)
        | 'n' -> parseLiteral("null", JsNull)
        | _ -> throw()

    and parseRootValue() =
        skipWhitespace()
        ensure(i < s.Length)
        match s.[i] with
        | '{' -> parseObject()
        | '[' -> parseArray()
        | _ -> throw()

    and parseString() =
        ensure(i < s.Length && s.[i] = '"')
        i <- i + 1
        while i < s.Length && s.[i] <> '"' do
            if s.[i] = '\\' then
                ensure(i+1 < s.Length)
                match s.[i+1] with
                | 'b' -> buf.Append('\b') |> ignore
                | 'f' -> buf.Append('\f') |> ignore
                | 'n' -> buf.Append('\n') |> ignore
                | 't' -> buf.Append('\t') |> ignore
                | 'r' -> buf.Append('\r') |> ignore
                | '\\' -> buf.Append('\\') |> ignore
                | '/' -> buf.Append('/') |> ignore
                | '"' -> buf.Append('"') |> ignore
                | 'u' ->
                    ensure(i+5 < s.Length)
                    let hexdigit d =
                        if d >= '0' && d <= '9' then int32 d - int32 '0'
                        elif d >= 'a' && d <= 'f' then int32 d - int32 'a' + 10
                        elif d >= 'A' && d <= 'F' then int32 d - int32 'A' + 10
                        else failwith "hexdigit"
                    let unicodeChar (s:string) =
                        if s.Length <> 4 then failwith "unicodeChar";
                        char (hexdigit s.[0] * 4096 + hexdigit s.[1] * 256 + hexdigit s.[2] * 16 + hexdigit s.[3])
                    let ch = unicodeChar (s.Substring(i+2, 4))
                    buf.Append(ch) |> ignore
                    i <- i + 4  // the \ and u will also be skipped past further below
                | 'U' ->
                    ensure(i+9 < s.Length)
                    let unicodeChar (s:string) =
                        if s.Length <> 8 then failwith "unicodeChar";
                        if s.[0..1] <> "00" then failwith "unicodeChar";
                        UnicodeHelper.getUnicodeSurrogatePair <| System.UInt32.Parse(s, NumberStyles.HexNumber)
                    let lead, trail = unicodeChar (s.Substring(i+2, 8))
                    buf.Append(lead) |> ignore
                    buf.Append(trail) |> ignore
                    i <- i + 8  // the \ and u will also be skipped past further below
                | _ -> throw()
                i <- i + 2  // skip past \ and next char
            else
                buf.Append(s.[i]) |> ignore
                i <- i + 1
        ensure(i < s.Length && s.[i] = '"')
        i <- i + 1
        let str = buf.ToString()
        buf.Clear() |> ignore
        str

    and parseNum() =
        let start = i
        while i < s.Length && (isNumChar s.[i]) do
            i <- i + 1
        let len = i - start
        let sub = s.Substring(start,len)
        match TextConversions.AsDecimal CultureInfo.InvariantCulture sub with
        | Some x -> JsNumber x
        | _ ->
            match TextConversions.AsFloat [| |] (*useNoneForMissingValues*)false CultureInfo.InvariantCulture sub with
            | Some x -> JsFloat x
            | _ -> throw()

    and parsePair() =
        let key = parseString()
        skipWhitespace()
        ensure(i < s.Length && s.[i] = ':')
        i <- i + 1
        skipWhitespace()
        key, parseValue()

    and parseObject() =
        ensure(i < s.Length && s.[i] = '{')
        i <- i + 1
        skipWhitespace()
        let pairs = ResizeArray<_>()
        if i < s.Length && s.[i] = '"' then
            pairs.Add(parsePair())
            skipWhitespace()
            while i < s.Length && s.[i] = ',' do
                i <- i + 1
                skipWhitespace()
                pairs.Add(parsePair())
                skipWhitespace()
        ensure(i < s.Length && s.[i] = '}')
        i <- i + 1
        JsObj(pairs.ToArray() |> List.ofArray)

    and parseArray() =
        ensure(i < s.Length && s.[i] = '[')
        i <- i + 1
        skipWhitespace()
        let vals = ResizeArray<_>()
        if i < s.Length && s.[i] <> ']' then
            vals.Add(parseValue())
            skipWhitespace()
            while i < s.Length && s.[i] = ',' do
                i <- i + 1
                skipWhitespace()
                vals.Add(parseValue())
                skipWhitespace()
        ensure(i < s.Length && s.[i] = ']')
        i <- i + 1
        JsArr(vals.ToArray() |> List.ofArray)

    and parseLiteral(expected, r) =
        ensure(i+expected.Length < s.Length)
        for j in 0 .. expected.Length - 1 do
            ensure(s.[i+j] = expected.[j])
        i <- i + expected.Length
        r

    // Start by parsing the top-level value
    member x.Parse() =
        let value = parseRootValue()
        skipWhitespace()
        if i <> s.Length then
            throw()
        else
            value

    member x.ParseMultiple() =
        seq {
            while i <> s.Length do
                yield parseRootValue()
                skipWhitespace()
        }

type JsonFormatting =
    /// Format (indent) the JsonValue
    | Indented = 0
    /// Print the JsonValue in one line in a compact way
    | None = 1

module JsonValue =
    open System.IO

    let ofString isSuccess isError str =
        let p = JsonParser(str)
        try
            p.Parse() |> isSuccess
        with JsonParserException msg -> isError msg

    // Encode characters that are not valid in JS string. The implementation is based
    // on https://github.com/mono/mono/blob/master/mcs/class/System.Web/System.Web/HttpUtility.cs
    let private jsonStringEncodeTo (w:TextWriter) (value:string) =
        if String.IsNullOrEmpty value then ()
        else
          for i = 0 to value.Length - 1 do
            let c = value.[i]
            let ci = int c
            if ci >= 0 && ci <= 7 || ci = 11 || ci >= 14 && ci <= 31 then
                w.Write("\\u{0:x4}", ci) |> ignore
            else
                match c with
                | '\b' -> w.Write "\\b"
                | '\t' -> w.Write "\\t"
                | '\n' -> w.Write "\\n"
                | '\f' -> w.Write "\\f"
                | '\r' -> w.Write "\\r"
                | '"'  -> w.Write "\\\""
                | '\\' -> w.Write "\\\\"
                | _    -> w.Write c

    let writeTo (w:TextWriter) saveOptions jsonValue =

        let newLine =
          if saveOptions = JsonFormatting.Indented then
            fun indentation plus ->
              w.WriteLine()
              System.String(' ', indentation + plus) |> w.Write
          else
            fun _ _ -> ()

        let propSep =
            if saveOptions = JsonFormatting.Indented then "\": "
            else "\":"

        let rec serialize indentation =
            function
            | JsNull -> w.Write "null"
            | JsBool b -> w.Write(if b then "true" else "false")
            | JsNumber number -> w.Write number
            | JsFloat number -> w.Write number
            | JsStr s ->
                w.Write "\""
                jsonStringEncodeTo w s
                w.Write "\""
            | JsObj properties ->
                w.Write "{"
                for i = 0 to properties.Length - 1 do
                    let k,v = properties.[i]
                    if i > 0 then w.Write ","
                    newLine indentation 2
                    w.Write "\""
                    jsonStringEncodeTo w k
                    w.Write propSep
                    serialize (indentation + 2) v
                newLine indentation 0
                w.Write "}"
            | JsArr elements ->
                w.Write "["
                for i = 0 to elements.Length - 1 do
                  if i > 0 then w.Write ","
                  newLine indentation 2
                  serialize (indentation + 2) elements.[i]
                if elements.Length > 0 then
                  newLine indentation 0
                w.Write "]"

        serialize 0 jsonValue

    let toString saveOptions jsonValue =
        let w = new StringWriter(CultureInfo.InvariantCulture)
        writeTo w saveOptions jsonValue
        w.GetStringBuilder().ToString()