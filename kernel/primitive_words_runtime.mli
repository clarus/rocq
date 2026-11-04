(************************************************************************)
(* Isolated primitive-words fork: standard OCaml integer runtime.        *)
(************************************************************************)

(** Host runtime values for width-distinct Rocq primitive words.

    Arithmetic is implemented in OCaml with standard OCaml integers.  The
    abstract value types are GC-compatible custom blocks with dedicated custom
    operations identities. They remain distinct from one another and from
    OCaml's boxed integer types at polymorphic boundaries. *)
module Word8 : sig
  type t

  val custom_identifier : string
  val is_runtime_value : Obj.t -> bool

  (** [of_int] retains the low eight bits; [to_int] is unsigned. *)
  val of_int : int -> t
  val to_int : t -> int
  val to_string : t -> string

  val zero : t
  val one : t
  val max_unsigned : t
  val min_signed : t

  val neg : t -> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t
  val lognot : t -> t
  val equal : t -> t -> bool
  val hash : t -> int
  val compare_signed : t -> t -> int
  val compare_unsigned : t -> t -> int
  val ltb_signed : t -> t -> bool
  val leb_signed : t -> t -> bool
  val ltb_unsigned : t -> t -> bool
  val leb_unsigned : t -> t -> bool
  val shift_left : t -> t -> t
  val shift_right_logical : t -> t -> t
  val shift_right_arithmetic : t -> t -> t
  val divu_total : t -> t -> t
  val modu_total : t -> t -> t
  val divs_total : t -> t -> t
  val rems_total : t -> t -> t
end

module Word16 : sig
  type t

  val custom_identifier : string
  val is_runtime_value : Obj.t -> bool

  (** [of_int] retains the low 16 bits; [to_int] is unsigned. *)
  val of_int : int -> t
  val to_int : t -> int
  val to_string : t -> string

  val zero : t
  val one : t
  val max_unsigned : t
  val min_signed : t

  val neg : t -> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t
  val lognot : t -> t
  val equal : t -> t -> bool
  val hash : t -> int
  val compare_signed : t -> t -> int
  val compare_unsigned : t -> t -> int
  val ltb_signed : t -> t -> bool
  val leb_signed : t -> t -> bool
  val ltb_unsigned : t -> t -> bool
  val leb_unsigned : t -> t -> bool
  val shift_left : t -> t -> t
  val shift_right_logical : t -> t -> t
  val shift_right_arithmetic : t -> t -> t
  val divu_total : t -> t -> t
  val modu_total : t -> t -> t
  val divs_total : t -> t -> t
  val rems_total : t -> t -> t
end

module Word32 : sig
  type t

  val custom_identifier : string
  val is_runtime_value : Obj.t -> bool

  (** Boxed [int32] is used only at the value-compatible boundary. *)
  val of_int32 : int32 -> t
  val to_int32 : t -> int32
  val to_string : t -> string

  val zero : t
  val one : t
  val max_unsigned : t
  val min_signed : t

  val neg : t -> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t
  val lognot : t -> t
  val equal : t -> t -> bool
  val hash : t -> int
  val compare_signed : t -> t -> int
  val compare_unsigned : t -> t -> int
  val ltb_signed : t -> t -> bool
  val leb_signed : t -> t -> bool
  val ltb_unsigned : t -> t -> bool
  val leb_unsigned : t -> t -> bool
  val shift_left : t -> t -> t
  val shift_right_logical : t -> t -> t
  val shift_right_arithmetic : t -> t -> t
  val divu_total : t -> t -> t
  val modu_total : t -> t -> t
  val divs_total : t -> t -> t
  val rems_total : t -> t -> t
end

module Word64 : sig
  type t

  val custom_identifier : string
  val is_runtime_value : Obj.t -> bool

  val of_int64 : int64 -> t
  val to_int64 : t -> int64

  val zero : t
  val one : t
  val max_unsigned : t
  val min_signed : t
  val max_signed : t

  val neg : t -> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t

  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t
  val lognot : t -> t

  val equal : t -> t -> bool
  val hash : t -> int
  val compare_signed : t -> t -> int
  val compare_unsigned : t -> t -> int
  val ltb_signed : t -> t -> bool
  val leb_signed : t -> t -> bool
  val ltb_unsigned : t -> t -> bool
  val leb_unsigned : t -> t -> bool

  (** Results are [(carry_or_borrow, wrapped_result)]. *)
  val add_with_carry : t -> t -> bool * t
  val sub_with_borrow : t -> t -> bool * t

  (** Checked operations interpret both operands and the result as signed
      two's-complement integers. *)
  val neg_checked : t -> t option
  val add_checked : t -> t -> t option
  val sub_checked : t -> t -> t option
  val mul_checked : t -> t -> t option

  (** Negative counts are rejected. Counts at least 64 have the target's
      explicit zero/sign-fill behavior rather than relying on unspecified
      host shift behavior. *)
  val shift_left : t -> int -> t
  val shift_right_logical : t -> int -> t
  val shift_right_arithmetic : t -> int -> t

  (** Word-valued counts used by primitive reduction. Counts at least 64 are
      totalized to zero/sign-fill before reaching host shift primitives. *)
  val shift_left_word : t -> t -> t
  val shift_right_logical_word : t -> t -> t
  val shift_right_arithmetic_word : t -> t -> t
  val divu_total : t -> t -> t
  val modu_total : t -> t -> t
  val divs_total : t -> t -> t
  val rems_total : t -> t -> t

  val divmodu : t -> t -> (t * t) option
  val divu : t -> t -> t option
  val modu : t -> t -> t option

  (** Signed division truncates toward zero. [divs_checked min_signed
      max_unsigned] is [None], while [rems] on those operands is [Some zero]. *)
  val divs_checked : t -> t -> t option
  val rems : t -> t -> t option

  (** The signed word count selects direction. Its absolute magnitude is
      capped at 64, including the minimum signed count. *)
  val shift_left_signed : t -> t -> t
  val shift_right_signed : t -> t -> t
end

(** A width-distinct 128-bit runtime value represented by exactly two
    little-significance-order 64-bit limbs.  Boxed [int64] values only cross
    the public observation/construction boundary; arithmetic uses standard OCaml
    [int64] limbs internally. *)
module Word128 : sig
  type t

  val custom_identifier : string
  val is_runtime_value : Obj.t -> bool

  val of_limbs : low:int64 -> high:int64 -> t
  val to_limbs : t -> int64 * int64

  val zero : t
  val one : t
  val max_unsigned : t
  val min_signed : t
  val max_signed : t

  val neg : t -> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t
  val lognot : t -> t

  val equal : t -> t -> bool
  val hash : t -> int
  val compare_signed : t -> t -> int
  val compare_unsigned : t -> t -> int
  val ltb_signed : t -> t -> bool
  val leb_signed : t -> t -> bool
  val ltb_unsigned : t -> t -> bool
  val leb_unsigned : t -> t -> bool

  val add_with_carry : t -> t -> bool * t
  val sub_with_borrow : t -> t -> bool * t

  (** Negative host counts are rejected.  Counts at least 128 are capped to
      zero or arithmetic sign-fill before any host shift primitive is called. *)
  val shift_left : t -> int -> t
  val shift_right_logical : t -> int -> t
  val shift_right_arithmetic : t -> int -> t
  val shift_left_word : t -> t -> t
  val shift_right_logical_word : t -> t -> t
  val shift_right_arithmetic_word : t -> t -> t

  (** Total primitive-level contracts: division by zero returns quotient zero
      and the dividend as remainder.  Signed minimum / -1 wraps to minimum and
      has remainder zero. *)
  val divmodu_total : t -> t -> t * t
  val divu_total : t -> t -> t
  val modu_total : t -> t -> t
  val divs_total : t -> t -> t
  val rems_total : t -> t -> t
end

(** A width-distinct 256-bit runtime value represented by exactly four
    little-significance-order 64-bit limbs. Boxed [int64] values are confined
    to construction/observation boundaries; arithmetic uses standard [int64]
    limbs internally. *)
module Word256 : sig
  type t

  val custom_identifier : string
  val is_runtime_value : Obj.t -> bool

  val of_limbs :
    limb0:int64 -> limb1:int64 -> limb2:int64 -> limb3:int64 -> t
  val to_limbs : t -> int64 * int64 * int64 * int64

  val zero : t
  val one : t
  val max_unsigned : t
  val min_signed : t
  val max_signed : t

  val neg : t -> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t
  val lognot : t -> t

  val equal : t -> t -> bool
  val hash : t -> int
  val compare_signed : t -> t -> int
  val compare_unsigned : t -> t -> int
  val ltb_signed : t -> t -> bool
  val leb_signed : t -> t -> bool
  val ltb_unsigned : t -> t -> bool
  val leb_unsigned : t -> t -> bool

  val add_with_carry : t -> t -> bool * t
  val sub_with_borrow : t -> t -> bool * t

  (** Negative host counts are rejected. Counts at least 256 are capped to
      zero or arithmetic sign-fill before a host shift primitive is called. *)
  val shift_left : t -> int -> t
  val shift_right_logical : t -> int -> t
  val shift_right_arithmetic : t -> int -> t
  val shift_left_word : t -> t -> t
  val shift_right_logical_word : t -> t -> t
  val shift_right_arithmetic_word : t -> t -> t

  (** Total primitive-level contracts: division by zero returns quotient zero
      and the dividend as remainder. Signed minimum / -1 wraps to minimum and
      has remainder zero. *)
  val divmodu_total : t -> t -> t * t
  val divu_total : t -> t -> t
  val modu_total : t -> t -> t
  val divs_total : t -> t -> t
  val rems_total : t -> t -> t
end
