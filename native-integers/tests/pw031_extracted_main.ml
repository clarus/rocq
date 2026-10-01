open PW031Extracted

let fail message = failwith ("PW031 generated extraction: " ^ message)
let z = Big_int_Z.big_int_of_string
let zs = Big_int_Z.string_of_big_int

let rec nat_of_int n = if n = 0 then O else S (nat_of_int (n - 1))

let emit fields values =
  print_endline
    (String.concat "\t" (fields @ [String.concat "," (List.map zs values)]))

let pair width x y amount =
  let raw, public, meta = match width with
    | 8 -> pw031_raw8 x y, pw031_public8 x y amount, pw031_meta8 x y amount
    | 16 -> pw031_raw16 x y, pw031_public16 x y amount, pw031_meta16 x y amount
    | 32 -> pw031_raw32 x y, pw031_public32 x y amount, pw031_meta32 x y amount
    | 64 -> pw031_raw64 x y, pw031_public64 x y amount, pw031_meta64 x y amount
    | 128 -> pw031_raw128 x y, pw031_public128 x y amount, pw031_meta128 x y amount
    | 256 -> pw031_raw256 x y, pw031_public256 x y amount, pw031_meta256 x y amount
    | _ -> fail "unsupported width"
  in raw @ public @ meta

let conversion width zv nv natural =
  match width with
  | 8 -> pw031_conversion8 zv nv natural
  | 16 -> pw031_conversion16 zv nv natural
  | 32 -> pw031_conversion32 zv nv natural
  | 64 -> pw031_conversion64 zv nv natural
  | 128 -> pw031_conversion128 zv nv natural
  | 256 -> pw031_conversion256 zv nv natural
  | _ -> fail "unsupported width"

let cross src dst value = match src, dst with
  | 8, 16 -> pw031_cross_8_16 value
  | 8, 32 -> pw031_cross_8_32 value
  | 8, 64 -> pw031_cross_8_64 value
  | 8, 128 -> pw031_cross_8_128 value
  | 8, 256 -> pw031_cross_8_256 value
  | 16, 32 -> pw031_cross_16_32 value
  | 16, 64 -> pw031_cross_16_64 value
  | 16, 128 -> pw031_cross_16_128 value
  | 16, 256 -> pw031_cross_16_256 value
  | 32, 64 -> pw031_cross_32_64 value
  | 32, 128 -> pw031_cross_32_128 value
  | 32, 256 -> pw031_cross_32_256 value
  | 64, 128 -> pw031_cross_64_128 value
  | 64, 256 -> pw031_cross_64_256 value
  | 128, 256 -> pw031_cross_128_256 value
  | _ -> fail "unsupported conversion direction"

let constants width = match width with
  | 8 -> pw031_constants8 | 16 -> pw031_constants16
  | 32 -> pw031_constants32 | 64 -> pw031_constants64
  | 128 -> pw031_constants128 | 256 -> pw031_constants256
  | _ -> fail "unsupported width"

let process line =
  match String.split_on_char '\t' line with
  | ["constants"; width] ->
      emit ["constants"; width] (constants (int_of_string width))
  | ["pair"; width; x; y; amount; family] ->
      let wi, ai = int_of_string width, int_of_string amount in
      emit ["pair"; width; x; y; amount; family]
        (pair wi (z x) (z y) (nat_of_int ai))
  | ["conv"; width; zv; nv; natural] ->
      let wi, ni = int_of_string width, int_of_string natural in
      emit ["conv"; width; zv; nv; natural]
        (conversion wi (z zv) (z nv) (nat_of_int ni))
  | ["cross"; src; dst; value] ->
      emit ["cross"; src; dst; value]
        (cross (int_of_string src) (int_of_string dst) (z value))
  | [] -> ()
  | _ -> fail ("malformed vector: " ^ line)

let () =
  if Array.length Sys.argv <> 2 then fail "usage: executable vectors.tsv";
  let channel = open_in Sys.argv.(1) in
  Fun.protect ~finally:(fun () -> close_in channel) (fun () ->
    try while true do process (input_line channel) done with End_of_file -> ())
