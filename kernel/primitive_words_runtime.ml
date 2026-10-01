(************************************************************************)
(* Isolated primitive-words fork: standard OCaml integer runtime.        *)
(************************************************************************)

module Small (W : sig val bits : int end) = struct
  type t = int
  let mask = (1 lsl W.bits) - 1
  let sign = 1 lsl (W.bits - 1)
  let of_int x = let x = x land mask in if x land sign = 0 then x else x - (1 lsl W.bits)
  let unsigned_to_int x = x land mask
  let zero () = 0
  let one () = 1
  let minus_one () = -1
  let min_int () = -sign
  let neg x = of_int (-x)
  let add x y = of_int (x + y)
  let sub x y = of_int (x - y)
  let mul x y = of_int (x * y)
  let logand x y = of_int (x land y)
  let logor x y = of_int (x lor y)
  let logxor x y = of_int (x lxor y)
  let lognot x = of_int (lnot x)
  let equal = Int.equal
  let compare = Int.compare
  let unsigned_compare x y = Int.compare (unsigned_to_int x) (unsigned_to_int y)
  let shift_left x n = of_int (x lsl n)
  let shift_right x n = of_int (x asr n)
  let shift_right_logical x n = of_int (unsigned_to_int x lsr n)
  let div x y = of_int (x / y)
  let rem x y = of_int (x mod y)
  let unsigned_div x y = of_int (unsigned_to_int x / unsigned_to_int y)
  let unsigned_rem x y = of_int (unsigned_to_int x mod unsigned_to_int y)
end

module Word8 = struct
  module U = Small (struct let bits = 8 end)

  type t

  external register_custom_operations : unit -> unit
    = "rocq_primitive_word8_register"
  external registered_identifier : unit -> string
    = "rocq_primitive_word8_identifier"
  external of_raw : U.t -> t
    = "rocq_primitive_word8_of_int8_bytecode"
  external to_raw : t -> U.t
    = "rocq_primitive_word8_to_int8_bytecode"
  external is_runtime_value : Obj.t -> bool
    = "rocq_primitive_word8_is_runtime_value" [@@noalloc]

  let () = register_custom_operations ()
  let custom_identifier = registered_identifier ()

  let[@inline always] of_int value = of_raw (U.of_int value)
  let[@inline always] to_int value = U.unsigned_to_int (to_raw value)
  let to_string value = string_of_int (to_int value)

  let zero = of_raw (U.zero ())
  let one = of_raw (U.one ())
  let max_unsigned = of_raw (U.minus_one ())
  let min_signed = of_raw (U.min_int ())
  let width = of_int 8

  let[@inline always] neg x = of_raw (U.neg (to_raw x))
  let[@inline always] add x y = of_raw (U.add (to_raw x) (to_raw y))
  let[@inline always] sub x y = of_raw (U.sub (to_raw x) (to_raw y))
  let[@inline always] mul x y = of_raw (U.mul (to_raw x) (to_raw y))
  let[@inline always] logand x y = of_raw (U.logand (to_raw x) (to_raw y))
  let[@inline always] logor x y = of_raw (U.logor (to_raw x) (to_raw y))
  let[@inline always] logxor x y = of_raw (U.logxor (to_raw x) (to_raw y))
  let[@inline always] lognot x = of_raw (U.lognot (to_raw x))
  let[@inline always] equal x y = U.equal (to_raw x) (to_raw y)
  let hash value = Hashtbl.hash value
  let[@inline always] compare_signed x y = U.compare (to_raw x) (to_raw y)
  let[@inline always] compare_unsigned x y =
    U.unsigned_compare (to_raw x) (to_raw y)
  let[@inline always] ltb_signed x y = compare_signed x y < 0
  let[@inline always] leb_signed x y = compare_signed x y <= 0
  let[@inline always] ltb_unsigned x y = compare_unsigned x y < 0
  let[@inline always] leb_unsigned x y = compare_unsigned x y <= 0

  let shift_left value count =
    if leb_unsigned width count then zero
    else of_raw (U.shift_left (to_raw value) (to_int count))

  let shift_right_logical value count =
    if leb_unsigned width count then zero
    else of_raw (U.shift_right_logical (to_raw value) (to_int count))

  let shift_right_arithmetic value count =
    if leb_unsigned width count then
      if ltb_signed value zero then max_unsigned else zero
    else of_raw (U.shift_right (to_raw value) (to_int count))

  let divu_total dividend divisor =
    if equal divisor zero then zero
    else of_raw (U.unsigned_div (to_raw dividend) (to_raw divisor))

  let modu_total dividend divisor =
    if equal divisor zero then dividend
    else of_raw (U.unsigned_rem (to_raw dividend) (to_raw divisor))

  let divs_total dividend divisor =
    if equal divisor zero then zero
    else if equal dividend min_signed && equal divisor max_unsigned
    then min_signed
    else of_raw (U.div (to_raw dividend) (to_raw divisor))

  let rems_total dividend divisor =
    if equal divisor zero then dividend
    else if equal dividend min_signed && equal divisor max_unsigned then zero
    else of_raw (U.rem (to_raw dividend) (to_raw divisor))
end

module Word16 = struct
  module U = Small (struct let bits = 16 end)

  type t

  external register_custom_operations : unit -> unit
    = "rocq_primitive_word16_register"
  external registered_identifier : unit -> string
    = "rocq_primitive_word16_identifier"
  external of_raw : U.t -> t
    = "rocq_primitive_word16_of_int16_bytecode"
  external to_raw : t -> U.t
    = "rocq_primitive_word16_to_int16_bytecode"
  external is_runtime_value : Obj.t -> bool
    = "rocq_primitive_word16_is_runtime_value" [@@noalloc]

  let () = register_custom_operations ()
  let custom_identifier = registered_identifier ()

  let[@inline always] of_int value = of_raw (U.of_int value)
  let[@inline always] to_int value = U.unsigned_to_int (to_raw value)
  let to_string value = string_of_int (to_int value)

  let zero = of_raw (U.zero ())
  let one = of_raw (U.one ())
  let max_unsigned = of_raw (U.minus_one ())
  let min_signed = of_raw (U.min_int ())
  let width = of_int 16

  let[@inline always] neg x = of_raw (U.neg (to_raw x))
  let[@inline always] add x y = of_raw (U.add (to_raw x) (to_raw y))
  let[@inline always] sub x y = of_raw (U.sub (to_raw x) (to_raw y))
  let[@inline always] mul x y = of_raw (U.mul (to_raw x) (to_raw y))
  let[@inline always] logand x y = of_raw (U.logand (to_raw x) (to_raw y))
  let[@inline always] logor x y = of_raw (U.logor (to_raw x) (to_raw y))
  let[@inline always] logxor x y = of_raw (U.logxor (to_raw x) (to_raw y))
  let[@inline always] lognot x = of_raw (U.lognot (to_raw x))
  let[@inline always] equal x y = U.equal (to_raw x) (to_raw y)
  let hash value = Hashtbl.hash value
  let[@inline always] compare_signed x y = U.compare (to_raw x) (to_raw y)
  let[@inline always] compare_unsigned x y =
    U.unsigned_compare (to_raw x) (to_raw y)
  let[@inline always] ltb_signed x y = compare_signed x y < 0
  let[@inline always] leb_signed x y = compare_signed x y <= 0
  let[@inline always] ltb_unsigned x y = compare_unsigned x y < 0
  let[@inline always] leb_unsigned x y = compare_unsigned x y <= 0

  let shift_left value count =
    if leb_unsigned width count then zero
    else of_raw (U.shift_left (to_raw value) (to_int count))

  let shift_right_logical value count =
    if leb_unsigned width count then zero
    else of_raw (U.shift_right_logical (to_raw value) (to_int count))

  let shift_right_arithmetic value count =
    if leb_unsigned width count then
      if ltb_signed value zero then max_unsigned else zero
    else of_raw (U.shift_right (to_raw value) (to_int count))

  let divu_total dividend divisor =
    if equal divisor zero then zero
    else of_raw (U.unsigned_div (to_raw dividend) (to_raw divisor))

  let modu_total dividend divisor =
    if equal divisor zero then dividend
    else of_raw (U.unsigned_rem (to_raw dividend) (to_raw divisor))

  let divs_total dividend divisor =
    if equal divisor zero then zero
    else if equal dividend min_signed && equal divisor max_unsigned
    then min_signed
    else of_raw (U.div (to_raw dividend) (to_raw divisor))

  let rems_total dividend divisor =
    if equal divisor zero then dividend
    else if equal dividend min_signed && equal divisor max_unsigned then zero
    else of_raw (U.rem (to_raw dividend) (to_raw divisor))
end

module Word32 = struct
  module U = Int32

  type t

  external register_custom_operations : unit -> unit
    = "rocq_primitive_word32_register"
  external registered_identifier : unit -> string
    = "rocq_primitive_word32_identifier"
  external of_raw : U.t -> t
    = "rocq_primitive_word32_of_int32_bytecode"
  external to_raw : t -> U.t
    = "rocq_primitive_word32_to_int32_bytecode"
  external is_runtime_value : Obj.t -> bool
    = "rocq_primitive_word32_is_runtime_value" [@@noalloc]

  let () = register_custom_operations ()
  let custom_identifier = registered_identifier ()

  let[@inline always] of_int32 value = of_raw (Fun.id value)
  let[@inline always] to_int32 value = Fun.id (to_raw value)
  let to_string value =
    Int64.to_string (Int64.logand (Int64.of_int32 (to_int32 value)) 0xffff_ffffL)

  let zero = of_raw (U.of_int 0)
  let one = of_raw (U.of_int 1)
  let max_unsigned = of_raw (U.of_int (-1))
  let min_signed = of_int32 Int32.min_int
  let width = of_raw (U.of_int 32)

  let[@inline always] neg x = of_raw (U.neg (to_raw x))
  let[@inline always] add x y = of_raw (U.add (to_raw x) (to_raw y))
  let[@inline always] sub x y = of_raw (U.sub (to_raw x) (to_raw y))
  let[@inline always] mul x y = of_raw (U.mul (to_raw x) (to_raw y))
  let[@inline always] logand x y = of_raw (U.logand (to_raw x) (to_raw y))
  let[@inline always] logor x y = of_raw (U.logor (to_raw x) (to_raw y))
  let[@inline always] logxor x y = of_raw (U.logxor (to_raw x) (to_raw y))
  let[@inline always] lognot x = of_raw (U.lognot (to_raw x))
  let[@inline always] equal x y = U.equal (to_raw x) (to_raw y)
  let hash value = Hashtbl.hash value
  let[@inline always] compare_signed x y = U.compare (to_raw x) (to_raw y)
  let[@inline always] compare_unsigned x y =
    U.unsigned_compare (to_raw x) (to_raw y)
  let[@inline always] ltb_signed x y = compare_signed x y < 0
  let[@inline always] leb_signed x y = compare_signed x y <= 0
  let[@inline always] ltb_unsigned x y = compare_unsigned x y < 0
  let[@inline always] leb_unsigned x y = compare_unsigned x y <= 0

  let shift_count count = U.to_int (to_raw count)

  let shift_left value count =
    if leb_unsigned width count then zero
    else of_raw (U.shift_left (to_raw value) (shift_count count))

  let shift_right_logical value count =
    if leb_unsigned width count then zero
    else of_raw (U.shift_right_logical (to_raw value) (shift_count count))

  let shift_right_arithmetic value count =
    if leb_unsigned width count then
      if ltb_signed value zero then max_unsigned else zero
    else of_raw (U.shift_right (to_raw value) (shift_count count))

  let divu_total dividend divisor =
    if equal divisor zero then zero
    else of_raw (U.unsigned_div (to_raw dividend) (to_raw divisor))

  let modu_total dividend divisor =
    if equal divisor zero then dividend
    else of_raw (U.unsigned_rem (to_raw dividend) (to_raw divisor))

  let divs_total dividend divisor =
    if equal divisor zero then zero
    else if equal dividend min_signed && equal divisor max_unsigned
    then min_signed
    else of_raw (U.div (to_raw dividend) (to_raw divisor))

  let rems_total dividend divisor =
    if equal divisor zero then dividend
    else if equal dividend min_signed && equal divisor max_unsigned then zero
    else of_raw (U.rem (to_raw dividend) (to_raw divisor))
end

module Word64 = struct
  module U = Int64

  type t

  external register_custom_operations : unit -> unit
    = "rocq_primitive_word64_register"

  external registered_identifier : unit -> string
    = "rocq_primitive_word64_identifier"

  external of_raw : int64 -> t
    = "rocq_primitive_word64_of_int64_bytecode"

  external to_raw : t -> int64
    = "rocq_primitive_word64_to_int64_bytecode"

  external is_runtime_value : Obj.t -> bool
    = "rocq_primitive_word64_is_runtime_value" [@@noalloc]

  let () = register_custom_operations ()

  let custom_identifier = registered_identifier ()

  let[@inline always] of_int64 value = of_raw (Fun.id value)
  let[@inline always] to_int64 value = Fun.id (to_raw value)

  let zero = of_int64 0L
  let one = of_int64 1L
  let max_unsigned = of_int64 (-1L)
  let min_signed = of_int64 Int64.min_int
  let max_signed = of_int64 Int64.max_int
  let shift_width = of_raw (U.of_int 64)

  let[@inline always] neg x = of_raw (U.neg (to_raw x))
  let[@inline always] add x y = of_raw (U.add (to_raw x) (to_raw y))
  let[@inline always] sub x y = of_raw (U.sub (to_raw x) (to_raw y))
  let[@inline always] mul x y = of_raw (U.mul (to_raw x) (to_raw y))

  let[@inline always] logand x y = of_raw (U.logand (to_raw x) (to_raw y))
  let[@inline always] logor x y = of_raw (U.logor (to_raw x) (to_raw y))
  let[@inline always] logxor x y = of_raw (U.logxor (to_raw x) (to_raw y))
  let[@inline always] lognot x = of_raw (U.lognot (to_raw x))

  let[@inline always] equal x y = U.equal (to_raw x) (to_raw y)
  let hash value = Hashtbl.hash value
  let[@inline always] compare_signed x y = U.compare (to_raw x) (to_raw y)
  let[@inline always] compare_unsigned x y =
    U.unsigned_compare (to_raw x) (to_raw y)
  let[@inline always] ltb_signed x y = compare_signed x y < 0
  let[@inline always] leb_signed x y = compare_signed x y <= 0
  let[@inline always] ltb_unsigned x y = compare_unsigned x y < 0
  let[@inline always] leb_unsigned x y = compare_unsigned x y <= 0

  let add_with_carry x y =
    let result = add x y in
    ltb_unsigned result x, result

  let sub_with_borrow x y = ltb_unsigned x y, sub x y

  let neg_checked x = if equal x min_signed then None else Some (neg x)

  let add_checked x y =
    let result = add x y in
    let x_negative = ltb_signed x zero in
    let y_negative = ltb_signed y zero in
    let result_negative = ltb_signed result zero in
    if x_negative = y_negative && result_negative <> x_negative
    then None
    else Some result

  let sub_checked x y =
    let result = sub x y in
    let x_negative = ltb_signed x zero in
    let y_negative = ltb_signed y zero in
    let result_negative = ltb_signed result zero in
    if x_negative <> y_negative && result_negative <> x_negative
    then None
    else Some result

  let mul_checked x y =
    if equal x zero || equal y zero then Some zero
    else if (equal x min_signed && equal y max_unsigned) ||
            (equal y min_signed && equal x max_unsigned)
    then None
    else
      let result = mul x y in
      if U.equal (U.div (to_raw result) (to_raw x)) (to_raw y)
      then Some result
      else None

  let check_shift_count count =
    if count < 0 then invalid_arg "Primitive_words_runtime.Word64: negative shift"

  let shift_left value count =
    check_shift_count count;
    if count >= 64 then zero else of_raw (U.shift_left (to_raw value) count)

  let shift_right_logical value count =
    check_shift_count count;
    if count >= 64 then zero
    else of_raw (U.shift_right_logical (to_raw value) count)

  let shift_right_arithmetic value count =
    check_shift_count count;
    if count >= 64 then
      if compare_signed value zero < 0 then max_unsigned else zero
    else of_raw (U.shift_right (to_raw value) count)

  let word_shift_count count = U.to_int (to_raw count)

  let shift_left_word value count =
    if leb_unsigned shift_width count then zero
    else of_raw (U.shift_left (to_raw value) (word_shift_count count))

  let shift_right_logical_word value count =
    if leb_unsigned shift_width count then zero
    else of_raw (U.shift_right_logical (to_raw value) (word_shift_count count))

  let shift_right_arithmetic_word value count =
    if leb_unsigned shift_width count then
      if ltb_signed value zero then max_unsigned else zero
    else of_raw (U.shift_right (to_raw value) (word_shift_count count))

  let divu_total dividend divisor =
    if equal divisor zero then zero
    else of_raw (U.unsigned_div (to_raw dividend) (to_raw divisor))

  let modu_total dividend divisor =
    if equal divisor zero then dividend
    else of_raw (U.unsigned_rem (to_raw dividend) (to_raw divisor))

  let divs_total dividend divisor =
    if equal divisor zero then zero
    else if equal dividend min_signed && equal divisor max_unsigned
    then min_signed
    else of_raw (U.div (to_raw dividend) (to_raw divisor))

  let rems_total dividend divisor =
    if equal divisor zero then dividend
    else if equal dividend min_signed && equal divisor max_unsigned then zero
    else of_raw (U.rem (to_raw dividend) (to_raw divisor))

  let divmodu dividend divisor =
    if equal divisor zero then None
    else
      let dividend = to_raw dividend in
      let divisor = to_raw divisor in
      Some (of_raw (U.unsigned_div dividend divisor),
            of_raw (U.unsigned_rem dividend divisor))

  let divu dividend divisor =
    match divmodu dividend divisor with
    | None -> None
    | Some (quotient, _) -> Some quotient

  let modu dividend divisor =
    match divmodu dividend divisor with
    | None -> None
    | Some (_, remainder) -> Some remainder

  let divs_checked dividend divisor =
    if equal divisor zero then None
    else if equal dividend min_signed && equal divisor max_unsigned then None
    else Some (of_raw (U.div (to_raw dividend) (to_raw divisor)))

  let rems dividend divisor =
    if equal divisor zero then None
    else if equal dividend min_signed && equal divisor max_unsigned then Some zero
    else Some (of_raw (U.rem (to_raw dividend) (to_raw divisor)))

  let signed_shift_amount count =
    if ltb_signed count zero then
      if equal count min_signed then 64
      else
        let magnitude = neg count in
        if leb_unsigned shift_width magnitude then 64
        else U.to_int (to_raw magnitude)
    else if leb_unsigned shift_width count then 64
    else U.to_int (to_raw count)

  let shift_left_signed value count =
    let amount = signed_shift_amount count in
    if ltb_signed count zero
    then shift_right_arithmetic value amount
    else shift_left value amount

  let shift_right_signed value count =
    let amount = signed_shift_amount count in
    if ltb_signed count zero
    then shift_left value amount
    else shift_right_arithmetic value amount
end

module Word128 = struct
  module U = Int64

  type t

  external register_custom_operations : unit -> unit
    = "rocq_primitive_word128_register"
  external registered_identifier : unit -> string
    = "rocq_primitive_word128_identifier"
  external of_raw : U.t -> U.t -> t
    = "rocq_primitive_word128_of_limbs_bytecode"
  external to_raw_low : t -> U.t
    = "rocq_primitive_word128_low_bytecode"
  external to_raw_high : t -> U.t
    = "rocq_primitive_word128_high_bytecode"
  external is_runtime_value : Obj.t -> bool
    = "rocq_primitive_word128_is_runtime_value" [@@noalloc]

  let () = register_custom_operations ()
  let custom_identifier = registered_identifier ()

  let[@inline always] raw value = (to_raw_low value, to_raw_high value)
  let[@inline always] value (low, high) = of_raw low high
  let[@inline always] uzero () = U.of_int 0
  let[@inline always] uone () = U.of_int 1
  let[@inline always] umax () = Fun.id (-1L)

  let of_limbs ~low ~high = of_raw (Fun.id low) (Fun.id high)
  let to_limbs x =
    let (low, high) = raw x in
    Fun.id low, Fun.id high

  let zero = of_limbs ~low:0L ~high:0L
  let one = of_limbs ~low:1L ~high:0L
  let max_unsigned = of_limbs ~low:(-1L) ~high:(-1L)
  let min_signed = of_limbs ~low:0L ~high:Int64.min_int
  let max_signed = of_limbs ~low:(-1L) ~high:Int64.max_int

  let[@inline always] equal_raw (al, ah) (bl, bh) =
    U.equal al bl && U.equal ah bh

  let[@inline always] compare_unsigned_raw (al, ah) (bl, bh) =
    let high = U.unsigned_compare ah bh in
    if high = 0 then U.unsigned_compare al bl else high

  let[@inline always] compare_signed_raw (al, ah) (bl, bh) =
    let high = U.compare ah bh in
    if high = 0 then U.unsigned_compare al bl else high

  let[@inline always] neg_raw (low, high) =
    let low' = U.neg low in
    let carry = if U.equal low (uzero ()) then uone () else uzero () in
    (low', U.add (U.lognot high) carry)

  let[@inline always] add_raw (al, ah) (bl, bh) =
    let low = U.add al bl in
    let carry = if U.unsigned_compare low al < 0 then uone () else uzero () in
    (low, U.add (U.add ah bh) carry)

  let[@inline always] sub_raw (al, ah) (bl, bh) =
    let borrow = if U.unsigned_compare al bl < 0 then uone () else uzero () in
    (U.sub al bl, U.sub (U.sub ah bh) borrow)

  let[@inline always] logand_raw (al, ah) (bl, bh) =
    (U.logand al bl, U.logand ah bh)
  let[@inline always] logor_raw (al, ah) (bl, bh) =
    (U.logor al bl, U.logor ah bh)
  let[@inline always] logxor_raw (al, ah) (bl, bh) =
    (U.logxor al bl, U.logxor ah bh)
  let[@inline always] lognot_raw (low, high) =
    (U.lognot low, U.lognot high)

  (* The high half of unsigned [left * right], using four 32-bit digits.  Each
     intermediate is below 2^64; operations use standard Int64 values. *)
  let[@inline always] mul_high_unsigned left right =
    let mask = Fun.id 0xffff_ffffL in
    let left0 = U.logand left mask in
    let left1 = U.shift_right_logical left 32 in
    let right0 = U.logand right mask in
    let right1 = U.shift_right_logical right 32 in
    let product00 = U.mul left0 right0 in
    let middle = U.add (U.mul left1 right0)
        (U.shift_right_logical product00 32) in
    let middle_low = U.logand middle mask in
    let upper = U.add (U.mul left0 right1) middle_low in
    U.add (U.add (U.mul left1 right1)
                     (U.shift_right_logical middle 32))
      (U.shift_right_logical upper 32)

  let[@inline always] mul_raw (al, ah) (bl, bh) =
    let low = U.mul al bl in
    let high = U.add (mul_high_unsigned al bl)
        (U.add (U.mul al bh) (U.mul ah bl)) in
    (low, high)

  let neg x = value (neg_raw (raw x))
  let add x y = value (add_raw (raw x) (raw y))
  let sub x y = value (sub_raw (raw x) (raw y))
  let mul x y = value (mul_raw (raw x) (raw y))
  let logand x y = value (logand_raw (raw x) (raw y))
  let logor x y = value (logor_raw (raw x) (raw y))
  let logxor x y = value (logxor_raw (raw x) (raw y))
  let lognot x = value (lognot_raw (raw x))

  let equal x y = equal_raw (raw x) (raw y)
  let hash value = Hashtbl.hash value
  let compare_unsigned x y = compare_unsigned_raw (raw x) (raw y)
  let compare_signed x y = compare_signed_raw (raw x) (raw y)
  let ltb_unsigned x y = compare_unsigned x y < 0
  let leb_unsigned x y = compare_unsigned x y <= 0
  let ltb_signed x y = compare_signed x y < 0
  let leb_signed x y = compare_signed x y <= 0

  let add_with_carry x y =
    let result = add x y in
    ltb_unsigned result x, result
  let sub_with_borrow x y = ltb_unsigned x y, sub x y

  let check_shift_count count =
    if count < 0 then invalid_arg "Primitive_words_runtime.Word128: negative shift"

  let shift_left_raw (low, high) count =
    if count = 0 then (low, high)
    else if count >= 128 then (uzero (), uzero ())
    else if count >= 64 then
      (uzero (), U.shift_left low (count - 64))
    else
      (U.shift_left low count,
        U.logor (U.shift_left high count)
          (U.shift_right_logical low (64 - count)))

  let shift_right_logical_raw (low, high) count =
    if count = 0 then (low, high)
    else if count >= 128 then (uzero (), uzero ())
    else if count >= 64 then
      (U.shift_right_logical high (count - 64), uzero ())
    else
      (U.logor (U.shift_right_logical low count)
          (U.shift_left high (64 - count)),
        U.shift_right_logical high count)

  let shift_right_arithmetic_raw ((low, high) as input) count =
    let negative = U.compare high (uzero ()) < 0 in
    if count = 0 then input
    else if count >= 128 then
      let fill = if negative then umax () else uzero () in (fill, fill)
    else if count >= 64 then
      (U.shift_right high (count - 64),
        if negative then umax () else uzero ())
    else
      (U.logor (U.shift_right_logical low count)
          (U.shift_left high (64 - count)),
        U.shift_right high count)

  let shift_left x count =
    check_shift_count count; value (shift_left_raw (raw x) count)
  let shift_right_logical x count =
    check_shift_count count; value (shift_right_logical_raw (raw x) count)
  let shift_right_arithmetic x count =
    check_shift_count count; value (shift_right_arithmetic_raw (raw x) count)

  let word_shift_count count =
    let (low, high) = raw count in
    if not (U.equal high (uzero ())) || U.unsigned_compare low (U.of_int 128) >= 0
    then 128
    else U.to_int low

  let shift_left_word x count = shift_left x (word_shift_count count)
  let shift_right_logical_word x count =
    shift_right_logical x (word_shift_count count)
  let shift_right_arithmetic_word x count =
    shift_right_arithmetic x (word_shift_count count)

  let bit_length_limb limb =
    let rec loop length remaining =
      if U.equal remaining (uzero ()) then length
      else loop (length + 1) (U.shift_right_logical remaining 1)
    in
    loop 0 limb

  let bit_length (low, high) =
    if U.equal high (uzero ()) then bit_length_limb low
    else 64 + bit_length_limb high

  let bit_raw index =
    if index < 64 then (U.shift_left (uone ()) index, uzero ())
    else (uzero (), U.shift_left (uone ()) (index - 64))

  (* Normalized fixed-limb division.  The divisor's leading one is aligned to
     the dividend's leading one, then at most 128 quotient positions are
     visited from high to low.  The loop state is always two Int64 limbs;
     no mathematical-integer or C arithmetic backend participates. *)
  let divmodu_raw dividend divisor =
    if equal_raw divisor (uzero (), uzero ()) then
      ((uzero (), uzero ()), dividend)
    else if compare_unsigned_raw dividend divisor < 0 then
      ((uzero (), uzero ()), dividend)
    else
      let shift = bit_length dividend - bit_length divisor in
      let aligned = shift_left_raw divisor shift in
      let rec loop index quotient remainder aligned =
        if index < 0 then (quotient, remainder)
        else if compare_unsigned_raw remainder aligned >= 0 then
          loop (index - 1)
            (logor_raw quotient (bit_raw index))
            (sub_raw remainder aligned)
            (shift_right_logical_raw aligned 1)
        else
          loop (index - 1) quotient remainder
            (shift_right_logical_raw aligned 1)
      in
      loop shift (uzero (), uzero ()) dividend aligned

  let divmodu_total dividend divisor =
    let (quotient, remainder) = divmodu_raw (raw dividend) (raw divisor) in
    value quotient, value remainder
  let divu_total dividend divisor =
    let (quotient, _) = divmodu_raw (raw dividend) (raw divisor) in
    value quotient
  let modu_total dividend divisor =
    let (_, remainder) = divmodu_raw (raw dividend) (raw divisor) in
    value remainder

  let signed_negative (_, high) = U.compare high (uzero ()) < 0

  let divmods_raw dividend divisor =
    if equal_raw divisor (uzero (), uzero ()) then
      ((uzero (), uzero ()), dividend)
    else
      let dividend_negative = signed_negative dividend in
      let divisor_negative = signed_negative divisor in
      let dividend_magnitude =
        if dividend_negative then neg_raw dividend else dividend in
      let divisor_magnitude =
        if divisor_negative then neg_raw divisor else divisor in
      let (quotient, remainder) =
        divmodu_raw dividend_magnitude divisor_magnitude in
      let quotient =
        if dividend_negative <> divisor_negative then neg_raw quotient else quotient in
      let remainder = if dividend_negative then neg_raw remainder else remainder in
      (quotient, remainder)

  let divs_total dividend divisor =
    let (quotient, _) = divmods_raw (raw dividend) (raw divisor) in value quotient
  let rems_total dividend divisor =
    let (_, remainder) = divmods_raw (raw dividend) (raw divisor) in value remainder
end

module Word256 = struct
  module U = Int64

  type t

  external register_custom_operations : unit -> unit
    = "rocq_primitive_word256_register"
  external registered_identifier : unit -> string
    = "rocq_primitive_word256_identifier"
  external of_raw : U.t -> U.t -> U.t -> U.t -> t
    = "rocq_primitive_word256_of_limbs_bytecode"
  external to_raw0 : t -> U.t
    = "rocq_primitive_word256_limb0_bytecode"
  external to_raw1 : t -> U.t
    = "rocq_primitive_word256_limb1_bytecode"
  external to_raw2 : t -> U.t
    = "rocq_primitive_word256_limb2_bytecode"
  external to_raw3 : t -> U.t
    = "rocq_primitive_word256_limb3_bytecode"
  external is_runtime_value : Obj.t -> bool
    = "rocq_primitive_word256_is_runtime_value" [@@noalloc]

  let () = register_custom_operations ()
  let custom_identifier = registered_identifier ()

  let[@inline always] raw value =
    (to_raw0 value, to_raw1 value, to_raw2 value, to_raw3 value)
  let[@inline always] value (limb0, limb1, limb2, limb3) =
    of_raw limb0 limb1 limb2 limb3
  let[@inline always] uzero () = U.of_int 0
  let[@inline always] uone () = U.of_int 1
  let[@inline always] umax () = Fun.id (-1L)
  let[@inline always] zero_raw () =
    (uzero (), uzero (), uzero (), uzero ())

  let of_limbs ~limb0 ~limb1 ~limb2 ~limb3 =
    of_raw (Fun.id limb0) (Fun.id limb1)
      (Fun.id limb2) (Fun.id limb3)
  let to_limbs x =
    let (limb0, limb1, limb2, limb3) = raw x in
    Fun.id limb0, Fun.id limb1,
    Fun.id limb2, Fun.id limb3

  let zero = of_limbs ~limb0:0L ~limb1:0L ~limb2:0L ~limb3:0L
  let one = of_limbs ~limb0:1L ~limb1:0L ~limb2:0L ~limb3:0L
  let max_unsigned =
    of_limbs ~limb0:(-1L) ~limb1:(-1L) ~limb2:(-1L) ~limb3:(-1L)
  let min_signed =
    of_limbs ~limb0:0L ~limb1:0L ~limb2:0L ~limb3:Int64.min_int
  let max_signed =
    of_limbs ~limb0:(-1L) ~limb1:(-1L) ~limb2:(-1L)
      ~limb3:Int64.max_int

  let[@inline always] equal_raw (a0, a1, a2, a3) (b0, b1, b2, b3) =
    U.equal a0 b0 && U.equal a1 b1 && U.equal a2 b2 && U.equal a3 b3

  let[@inline always] compare_unsigned_raw
      (a0, a1, a2, a3) (b0, b1, b2, b3) =
    let high = U.unsigned_compare a3 b3 in
    if high <> 0 then high else
    let next = U.unsigned_compare a2 b2 in
    if next <> 0 then next else
    let next = U.unsigned_compare a1 b1 in
    if next <> 0 then next else U.unsigned_compare a0 b0

  let[@inline always] compare_signed_raw
      (a0, a1, a2, a3) (b0, b1, b2, b3) =
    let high = U.compare a3 b3 in
    if high <> 0 then high else
    let next = U.unsigned_compare a2 b2 in
    if next <> 0 then next else
    let next = U.unsigned_compare a1 b1 in
    if next <> 0 then next else U.unsigned_compare a0 b0

  let[@inline always] add_digit left right carry =
    let first = U.add left right in
    let carry0 = U.unsigned_compare first left < 0 in
    let sum = U.add first carry in
    let carry1 = U.unsigned_compare sum first < 0 in
    (sum, if carry0 || carry1 then uone () else uzero ())

  let[@inline always] sub_digit left right borrow =
    let first = U.sub left right in
    let borrow0 = U.unsigned_compare left right < 0 in
    let difference = U.sub first borrow in
    let borrow1 = U.unsigned_compare first borrow < 0 in
    (difference, if borrow0 || borrow1 then uone () else uzero ())

  let[@inline always] add_raw (a0, a1, a2, a3) (b0, b1, b2, b3) =
    let (r0, c0) = add_digit a0 b0 (uzero ()) in
    let (r1, c1) = add_digit a1 b1 c0 in
    let (r2, c2) = add_digit a2 b2 c1 in
    let (r3, _) = add_digit a3 b3 c2 in
    (r0, r1, r2, r3)

  let[@inline always] sub_raw (a0, a1, a2, a3) (b0, b1, b2, b3) =
    let (r0, c0) = sub_digit a0 b0 (uzero ()) in
    let (r1, c1) = sub_digit a1 b1 c0 in
    let (r2, c2) = sub_digit a2 b2 c1 in
    let (r3, _) = sub_digit a3 b3 c2 in
    (r0, r1, r2, r3)

  let[@inline always] logand_raw (a0, a1, a2, a3) (b0, b1, b2, b3) =
    (U.logand a0 b0, U.logand a1 b1,
      U.logand a2 b2, U.logand a3 b3)
  let[@inline always] logor_raw (a0, a1, a2, a3) (b0, b1, b2, b3) =
    (U.logor a0 b0, U.logor a1 b1, U.logor a2 b2, U.logor a3 b3)
  let[@inline always] logxor_raw (a0, a1, a2, a3) (b0, b1, b2, b3) =
    (U.logxor a0 b0, U.logxor a1 b1, U.logxor a2 b2, U.logxor a3 b3)
  let[@inline always] lognot_raw (a0, a1, a2, a3) =
    (U.lognot a0, U.lognot a1, U.lognot a2, U.lognot a3)
  let[@inline always] neg_raw input =
    add_raw (lognot_raw input) (uone (), uzero (), uzero (), uzero ())

  let[@inline always] mul_high_unsigned left right =
    let mask = Fun.id 0xffff_ffffL in
    let left0 = U.logand left mask in
    let left1 = U.shift_right_logical left 32 in
    let right0 = U.logand right mask in
    let right1 = U.shift_right_logical right 32 in
    let product00 = U.mul left0 right0 in
    let middle = U.add (U.mul left1 right0)
        (U.shift_right_logical product00 32) in
    let middle_low = U.logand middle mask in
    let upper = U.add (U.mul left0 right1) middle_low in
    U.add (U.add (U.mul left1 right1)
                     (U.shift_right_logical middle 32))
      (U.shift_right_logical upper 32)

  let[@inline always] add_at0 (r0, r1, r2, r3) amount =
    let (r0, c0) = add_digit r0 amount (uzero ()) in
    let (r1, c1) = add_digit r1 (uzero ()) c0 in
    let (r2, c2) = add_digit r2 (uzero ()) c1 in
    let (r3, _) = add_digit r3 (uzero ()) c2 in
    (r0, r1, r2, r3)

  let[@inline always] add_at1 (r0, r1, r2, r3) amount =
    let (r1, c1) = add_digit r1 amount (uzero ()) in
    let (r2, c2) = add_digit r2 (uzero ()) c1 in
    let (r3, _) = add_digit r3 (uzero ()) c2 in
    (r0, r1, r2, r3)

  let[@inline always] add_at2 (r0, r1, r2, r3) amount =
    let (r2, c2) = add_digit r2 amount (uzero ()) in
    let (r3, _) = add_digit r3 (uzero ()) c2 in
    (r0, r1, r2, r3)

  let[@inline always] add_at3 (r0, r1, r2, r3) amount =
    (r0, r1, r2, U.add r3 amount)

  (* Fully unrolled, truncated four-by-four schoolbook multiplication. The
     ten cells with i+j < 4 contribute sixteen low/high limb values. Fixed
     add-at-position helpers propagate every carry through the remaining result
     limbs; high contributions above limb 3 are deliberately discarded. *)
  let[@inline always] mul_raw (a0, a1, a2, a3) (b0, b1, b2, b3) =
    let result = zero_raw () in
    let result = add_at0 result (U.mul a0 b0) in
    let result = add_at1 result (mul_high_unsigned a0 b0) in
    let result = add_at1 result (U.mul a0 b1) in
    let result = add_at2 result (mul_high_unsigned a0 b1) in
    let result = add_at2 result (U.mul a0 b2) in
    let result = add_at3 result (mul_high_unsigned a0 b2) in
    let result = add_at3 result (U.mul a0 b3) in
    let result = add_at1 result (U.mul a1 b0) in
    let result = add_at2 result (mul_high_unsigned a1 b0) in
    let result = add_at2 result (U.mul a1 b1) in
    let result = add_at3 result (mul_high_unsigned a1 b1) in
    let result = add_at3 result (U.mul a1 b2) in
    let result = add_at2 result (U.mul a2 b0) in
    let result = add_at3 result (mul_high_unsigned a2 b0) in
    let result = add_at3 result (U.mul a2 b1) in
    add_at3 result (U.mul a3 b0)

  let neg x = value (neg_raw (raw x))
  let add x y = value (add_raw (raw x) (raw y))
  let sub x y = value (sub_raw (raw x) (raw y))
  let mul x y = value (mul_raw (raw x) (raw y))
  let logand x y = value (logand_raw (raw x) (raw y))
  let logor x y = value (logor_raw (raw x) (raw y))
  let logxor x y = value (logxor_raw (raw x) (raw y))
  let lognot x = value (lognot_raw (raw x))

  let equal x y = equal_raw (raw x) (raw y)
  let hash value = Hashtbl.hash value
  let compare_unsigned x y = compare_unsigned_raw (raw x) (raw y)
  let compare_signed x y = compare_signed_raw (raw x) (raw y)
  let ltb_unsigned x y = compare_unsigned x y < 0
  let leb_unsigned x y = compare_unsigned x y <= 0
  let ltb_signed x y = compare_signed x y < 0
  let leb_signed x y = compare_signed x y <= 0

  let add_with_carry x y =
    let result = add x y in ltb_unsigned result x, result
  let sub_with_borrow x y = ltb_unsigned x y, sub x y

  let check_shift_count count =
    if count < 0 then invalid_arg "Primitive_words_runtime.Word256: negative shift"

  let shift_left_raw (limb0, limb1, limb2, limb3) count =
    if count = 0 then (limb0, limb1, limb2, limb3)
    else if count >= 256 then zero_raw ()
    else if count < 64 then
      (U.shift_left limb0 count,
        U.logor (U.shift_left limb1 count)
          (U.shift_right_logical limb0 (64 - count)),
        U.logor (U.shift_left limb2 count)
          (U.shift_right_logical limb1 (64 - count)),
        U.logor (U.shift_left limb3 count)
          (U.shift_right_logical limb2 (64 - count)))
    else if count < 128 then
      let amount = count - 64 in
      if amount = 0 then (uzero (), limb0, limb1, limb2) else
      (uzero (), U.shift_left limb0 amount,
        U.logor (U.shift_left limb1 amount)
          (U.shift_right_logical limb0 (64 - amount)),
        U.logor (U.shift_left limb2 amount)
          (U.shift_right_logical limb1 (64 - amount)))
    else if count < 192 then
      let amount = count - 128 in
      if amount = 0 then (uzero (), uzero (), limb0, limb1) else
      (uzero (), uzero (), U.shift_left limb0 amount,
        U.logor (U.shift_left limb1 amount)
          (U.shift_right_logical limb0 (64 - amount)))
    else
      let amount = count - 192 in
      if amount = 0 then (uzero (), uzero (), uzero (), limb0) else
      (uzero (), uzero (), uzero (), U.shift_left limb0 amount)

  let shift_right_logical_raw (limb0, limb1, limb2, limb3) count =
    if count = 0 then (limb0, limb1, limb2, limb3)
    else if count >= 256 then zero_raw ()
    else if count < 64 then
      (U.logor (U.shift_right_logical limb0 count)
          (U.shift_left limb1 (64 - count)),
        U.logor (U.shift_right_logical limb1 count)
          (U.shift_left limb2 (64 - count)),
        U.logor (U.shift_right_logical limb2 count)
          (U.shift_left limb3 (64 - count)),
        U.shift_right_logical limb3 count)
    else if count < 128 then
      let amount = count - 64 in
      if amount = 0 then (limb1, limb2, limb3, uzero ()) else
      (U.logor (U.shift_right_logical limb1 amount)
          (U.shift_left limb2 (64 - amount)),
        U.logor (U.shift_right_logical limb2 amount)
          (U.shift_left limb3 (64 - amount)),
        U.shift_right_logical limb3 amount, uzero ())
    else if count < 192 then
      let amount = count - 128 in
      if amount = 0 then (limb2, limb3, uzero (), uzero ()) else
      (U.logor (U.shift_right_logical limb2 amount)
          (U.shift_left limb3 (64 - amount)),
        U.shift_right_logical limb3 amount, uzero (), uzero ())
    else
      let amount = count - 192 in
      if amount = 0 then (limb3, uzero (), uzero (), uzero ()) else
      (U.shift_right_logical limb3 amount,
        uzero (), uzero (), uzero ())

  let shift_right_arithmetic_raw
      ((limb0, limb1, limb2, limb3) as input) count =
    let negative = U.compare limb3 (uzero ()) < 0 in
    let fill = if negative then umax () else uzero () in
    if count = 0 then input
    else if count >= 256 then (fill, fill, fill, fill)
    else if count < 64 then
      (U.logor (U.shift_right_logical limb0 count)
          (U.shift_left limb1 (64 - count)),
        U.logor (U.shift_right_logical limb1 count)
          (U.shift_left limb2 (64 - count)),
        U.logor (U.shift_right_logical limb2 count)
          (U.shift_left limb3 (64 - count)),
        U.shift_right limb3 count)
    else if count < 128 then
      let amount = count - 64 in
      if amount = 0 then (limb1, limb2, limb3, fill) else
      (U.logor (U.shift_right_logical limb1 amount)
          (U.shift_left limb2 (64 - amount)),
        U.logor (U.shift_right_logical limb2 amount)
          (U.shift_left limb3 (64 - amount)),
        U.shift_right limb3 amount, fill)
    else if count < 192 then
      let amount = count - 128 in
      if amount = 0 then (limb2, limb3, fill, fill) else
      (U.logor (U.shift_right_logical limb2 amount)
          (U.shift_left limb3 (64 - amount)),
        U.shift_right limb3 amount, fill, fill)
    else
      let amount = count - 192 in
      if amount = 0 then (limb3, fill, fill, fill) else
      (U.shift_right limb3 amount, fill, fill, fill)

  let shift_left x count =
    check_shift_count count; value (shift_left_raw (raw x) count)
  let shift_right_logical x count =
    check_shift_count count; value (shift_right_logical_raw (raw x) count)
  let shift_right_arithmetic x count =
    check_shift_count count; value (shift_right_arithmetic_raw (raw x) count)

  let word_shift_count count =
    let (limb0, limb1, limb2, limb3) = raw count in
    if not (U.equal limb1 (uzero ()))
       || not (U.equal limb2 (uzero ()))
       || not (U.equal limb3 (uzero ()))
       || U.unsigned_compare limb0 (U.of_int 256) >= 0
    then 256 else U.to_int limb0

  let shift_left_word x count = shift_left x (word_shift_count count)
  let shift_right_logical_word x count =
    shift_right_logical x (word_shift_count count)
  let shift_right_arithmetic_word x count =
    shift_right_arithmetic x (word_shift_count count)

  let bit_length_limb limb =
    let rec loop length remaining =
      if U.equal remaining (uzero ()) then length
      else loop (length + 1) (U.shift_right_logical remaining 1)
    in
    loop 0 limb

  let bit_length (limb0, limb1, limb2, limb3) =
    if not (U.equal limb3 (uzero ())) then 192 + bit_length_limb limb3
    else if not (U.equal limb2 (uzero ())) then 128 + bit_length_limb limb2
    else if not (U.equal limb1 (uzero ())) then 64 + bit_length_limb limb1
    else bit_length_limb limb0

  let bit_raw index =
    if index < 64 then
      (U.shift_left (uone ()) index, uzero (), uzero (), uzero ())
    else if index < 128 then
      (uzero (), U.shift_left (uone ()) (index - 64), uzero (), uzero ())
    else if index < 192 then
      (uzero (), uzero (), U.shift_left (uone ()) (index - 128), uzero ())
    else
      (uzero (), uzero (), uzero (), U.shift_left (uone ()) (index - 192))

  (* Leading-bit normalized restoring division. The aligned divisor and
     quotient position move downward together for at most 256 fixed-limb
     iterations; all loop values remain four Int64 limbs. *)
  let divmodu_raw dividend divisor =
    if equal_raw divisor (zero_raw ()) then (zero_raw (), dividend)
    else if compare_unsigned_raw dividend divisor < 0 then
      (zero_raw (), dividend)
    else
      let shift = bit_length dividend - bit_length divisor in
      let aligned = shift_left_raw divisor shift in
      let rec loop index quotient remainder aligned =
        if index < 0 then (quotient, remainder)
        else if compare_unsigned_raw remainder aligned >= 0 then
          loop (index - 1)
            (logor_raw quotient (bit_raw index))
            (sub_raw remainder aligned)
            (shift_right_logical_raw aligned 1)
        else
          loop (index - 1) quotient remainder
            (shift_right_logical_raw aligned 1)
      in
      loop shift (zero_raw ()) dividend aligned

  let divmodu_total dividend divisor =
    let (quotient, remainder) = divmodu_raw (raw dividend) (raw divisor) in
    value quotient, value remainder
  let divu_total dividend divisor =
    let (quotient, _) = divmodu_raw (raw dividend) (raw divisor) in
    value quotient
  let modu_total dividend divisor =
    let (_, remainder) = divmodu_raw (raw dividend) (raw divisor) in
    value remainder

  let signed_negative (_, _, _, high) = U.compare high (uzero ()) < 0

  let divmods_raw dividend divisor =
    if equal_raw divisor (zero_raw ()) then (zero_raw (), dividend)
    else
      let dividend_negative = signed_negative dividend in
      let divisor_negative = signed_negative divisor in
      let dividend_magnitude =
        if dividend_negative then neg_raw dividend else dividend in
      let divisor_magnitude =
        if divisor_negative then neg_raw divisor else divisor in
      let (quotient, remainder) =
        divmodu_raw dividend_magnitude divisor_magnitude in
      let quotient =
        if dividend_negative <> divisor_negative then neg_raw quotient
        else quotient in
      let remainder =
        if dividend_negative then neg_raw remainder else remainder in
      (quotient, remainder)

  let divs_total dividend divisor =
    let (quotient, _) = divmods_raw (raw dividend) (raw divisor) in
    value quotient
  let rems_total dividend divisor =
    let (_, remainder) = divmods_raw (raw dividend) (raw divisor) in
    value remainder
end
