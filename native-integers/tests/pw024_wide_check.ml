module W128 = Primitive_words_runtime.Word128
module W256 = Primitive_words_runtime.Word256

let bool value = if value then 1 else 0

let bits128 value =
  let low, high = W128.to_limbs value in
  Printf.sprintf "%016Lx%016Lx" high low

let bits256 value =
  let limb0, limb1, limb2, limb3 = W256.to_limbs value in
  Printf.sprintf "%016Lx%016Lx%016Lx%016Lx" limb3 limb2 limb1 limb0

let chunk text offset =
  Int64.of_string ("0x" ^ String.sub text offset 16)

let word128 text =
  if String.length text <> 32 then invalid_arg "Word128 input width";
  W128.of_limbs ~low:(chunk text 16) ~high:(chunk text 0)

let word256 text =
  if String.length text <> 64 then invalid_arg "Word256 input width";
  W256.of_limbs ~limb0:(chunk text 48) ~limb1:(chunk text 32)
    ~limb2:(chunk text 16) ~limb3:(chunk text 0)

let prefix fields = String.concat "\t" (Array.to_list fields)

let emit_pair128 fields =
  let left = word128 fields.(4) in
  let right = word128 fields.(5) in
  let carry, sum = W128.add_with_carry left right in
  let borrow, difference = W128.sub_with_borrow left right in
  let quotient, remainder = W128.divmodu_total left right in
  if not (W128.equal quotient (W128.divu_total left right) &&
          W128.equal remainder (W128.modu_total left right)) then
    failwith "Word128 split division mismatch";
  Printf.printf
    "%s\tadd=%s\tsub=%s\tmul=%s\tcarry=%d\tborrow=%d\tdivu=%s\tmodu=%s\tdivs=%s\trems=%s\n"
    (prefix fields) (bits128 sum) (bits128 difference)
    (bits128 (W128.mul left right)) (bool carry) (bool borrow)
    (bits128 quotient) (bits128 remainder)
    (bits128 (W128.divs_total left right))
    (bits128 (W128.rems_total left right))

let emit_pair256 fields =
  let left = word256 fields.(4) in
  let right = word256 fields.(5) in
  let carry, sum = W256.add_with_carry left right in
  let borrow, difference = W256.sub_with_borrow left right in
  let quotient, remainder = W256.divmodu_total left right in
  if not (W256.equal quotient (W256.divu_total left right) &&
          W256.equal remainder (W256.modu_total left right)) then
    failwith "Word256 split division mismatch";
  Printf.printf
    "%s\tadd=%s\tsub=%s\tmul=%s\tcarry=%d\tborrow=%d\tdivu=%s\tmodu=%s\tdivs=%s\trems=%s\n"
    (prefix fields) (bits256 sum) (bits256 difference)
    (bits256 (W256.mul left right)) (bool carry) (bool borrow)
    (bits256 quotient) (bits256 remainder)
    (bits256 (W256.divs_total left right))
    (bits256 (W256.rems_total left right))

let emit_unary fields =
  match fields.(1) with
  | "128" ->
      let value = word128 fields.(4) in
      Printf.printf "%s\tneg=%s\tnot=%s\n" (prefix fields)
        (bits128 (W128.neg value)) (bits128 (W128.lognot value))
  | "256" ->
      let value = word256 fields.(4) in
      Printf.printf "%s\tneg=%s\tnot=%s\n" (prefix fields)
        (bits256 (W256.neg value)) (bits256 (W256.lognot value))
  | _ -> invalid_arg "unary width"

let emit_shift fields =
  let word_count = fields.(0) = "word_shift" in
  match fields.(1) with
  | "128" ->
      let value = word128 fields.(4) in
      let left, logical, arithmetic =
        if word_count then
          let count = word128 fields.(5) in
          W128.shift_left_word value count,
          W128.shift_right_logical_word value count,
          W128.shift_right_arithmetic_word value count
        else
          let count = int_of_string fields.(5) in
          W128.shift_left value count,
          W128.shift_right_logical value count,
          W128.shift_right_arithmetic value count in
      Printf.printf "%s\tleft=%s\tlogical=%s\tarithmetic=%s\n"
        (prefix fields) (bits128 left) (bits128 logical) (bits128 arithmetic)
  | "256" ->
      let value = word256 fields.(4) in
      let left, logical, arithmetic =
        if word_count then
          let count = word256 fields.(5) in
          W256.shift_left_word value count,
          W256.shift_right_logical_word value count,
          W256.shift_right_arithmetic_word value count
        else
          let count = int_of_string fields.(5) in
          W256.shift_left value count,
          W256.shift_right_logical value count,
          W256.shift_right_arithmetic value count in
      Printf.printf "%s\tleft=%s\tlogical=%s\tarithmetic=%s\n"
        (prefix fields) (bits256 left) (bits256 logical) (bits256 arithmetic)
  | _ -> invalid_arg "shift width"

let emit_cross fields =
  let left128 = word128 fields.(3) in
  let right128 = word128 fields.(4) in
  let extend value =
    let low, high = W128.to_limbs value in
    W256.of_limbs ~limb0:low ~limb1:high ~limb2:0L ~limb3:0L in
  let left256 = extend left128 in
  let right256 = extend right128 in
  let agrees operation128 operation256 =
    bits256 (operation256 left256 right256) =
    String.make 32 '0' ^ bits128 (operation128 left128 right128) in
  let sub =
    if W128.compare_unsigned left128 right128 < 0 then "na"
    else string_of_int (bool (agrees W128.sub W256.sub)) in
  Printf.printf
    "%s\tadd=%d\tsub=%s\tmul=%d\tand=%d\tor=%d\txor=%d\tdivu=%d\tmodu=%d\tcmpu=%d\n"
    (prefix fields)
    (bool (agrees W128.add W256.add)) sub
    (bool (agrees W128.mul W256.mul))
    (bool (agrees W128.logand W256.logand))
    (bool (agrees W128.logor W256.logor))
    (bool (agrees W128.logxor W256.logxor))
    (bool (agrees W128.divu_total W256.divu_total))
    (bool (agrees W128.modu_total W256.modu_total))
    (bool ((W128.compare_unsigned left128 right128 < 0) =
           (W256.compare_unsigned left256 right256 < 0)))

let emit fields =
  match fields.(0) with
  | "unary" -> emit_unary fields
  | "pair" ->
      if fields.(1) = "128" then emit_pair128 fields
      else if fields.(1) = "256" then emit_pair256 fields
      else invalid_arg "pair width"
  | "shift" | "word_shift" -> emit_shift fields
  | "cross" -> emit_cross fields
  | kind -> invalid_arg ("unknown vector kind: " ^ kind)

let run path =
  let channel = open_in path in
  let rec loop () =
    match input_line channel with
    | line -> emit (Array.of_list (String.split_on_char '\t' line)); loop ()
    | exception End_of_file -> close_in channel
  in
  loop ()

let () =
  match Array.to_list Sys.argv with
  | [_; path] -> run path
  | _ -> invalid_arg "VECTORS.tsv"
