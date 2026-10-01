(* Reduction of native operators *)
open Names
open CPrimitives
open Retroknowledge
open Environ
open CErrors

type _ action_kind =
  | IncompatTypes : _ prim_type -> Constant.t action_kind
  | IncompatInd : _ prim_ind -> inductive action_kind

type exn += IncompatibleDeclarations : 'a action_kind * 'a * 'a -> exn

let check_same_types typ c1 c2 =
  if not (Constant.UserOrd.equal c1 c2)
  then raise (IncompatibleDeclarations (IncompatTypes typ, c1, c2))

let check_same_inds ind i1 i2 =
  if not (Ind.UserOrd.equal i1 i2)
  then raise (IncompatibleDeclarations (IncompatInd ind, i1, i2))

let add_retroknowledge retro action =
  match action with
  | Register_type(typ,c) ->
    begin match typ with
      | PT_int63 ->
        (match retro.retro_int63 with
         | None -> { retro with retro_int63 = Some c }
         | Some c' -> check_same_types typ c c'; retro)

      | PT_word8 ->
        (match retro.retro_word8 with
         | None -> { retro with retro_word8 = Some c }
         | Some c' -> check_same_types typ c c'; retro)

      | PT_word16 ->
        (match retro.retro_word16 with
         | None -> { retro with retro_word16 = Some c }
         | Some c' -> check_same_types typ c c'; retro)

      | PT_word32 ->
        (match retro.retro_word32 with
         | None -> { retro with retro_word32 = Some c }
         | Some c' -> check_same_types typ c c'; retro)

      | PT_word64 ->
        (match retro.retro_word64 with
         | None -> { retro with retro_word64 = Some c }
         | Some c' -> check_same_types typ c c'; retro)

      | PT_word128 ->
        (match retro.retro_word128 with
         | None -> { retro with retro_word128 = Some c }
         | Some c' -> check_same_types typ c c'; retro)

      | PT_word256 ->
        (match retro.retro_word256 with
         | None -> { retro with retro_word256 = Some c }
         | Some c' -> check_same_types typ c c'; retro)

      | PT_float64 ->
        (match retro.retro_float64 with
         | None -> { retro with retro_float64 = Some c }
         | Some c' -> check_same_types typ c c'; retro)

      | PT_string ->
        (match retro.retro_string with
         | None -> { retro with retro_string = Some c }
         | Some c' -> check_same_types typ c c'; retro)

      | PT_array ->
        (match retro.retro_array with
         | None -> { retro with retro_array = Some c }
         | Some c' -> check_same_types typ c c'; retro)
    end

  | Register_ind(pit,ind) ->
    begin match pit with
      | PIT_bool ->
        let r =
          match retro.retro_bool with
          | None -> ((ind,1), (ind,2))
          | Some (((ind',_),_) as t) -> check_same_inds pit ind ind'; t in
        { retro with retro_bool = Some r }
      | PIT_carry ->
        let r =
          match retro.retro_carry with
          | None -> ((ind,1), (ind,2))
          | Some (((ind',_),_) as t) -> check_same_inds pit ind ind'; t in
        { retro with retro_carry = Some r }
      | PIT_pair ->
        let r =
          match retro.retro_pair with
          | None -> (ind,1)
          | Some ((ind',_) as t) -> check_same_inds pit ind ind'; t in
        { retro with retro_pair = Some r }
      | PIT_cmp ->
        let r =
          match retro.retro_cmp with
          | None -> ((ind,1), (ind,2), (ind,3))
          | Some (((ind',_),_,_) as t) -> check_same_inds pit ind ind'; t in
        { retro with retro_cmp = Some r }
      | PIT_f_cmp ->
        let r =
          match retro.retro_f_cmp with
          | None -> ((ind,1), (ind,2), (ind,3), (ind,4))
          | Some (((ind',_),_,_,_) as t) -> check_same_inds pit ind ind'; t in
        { retro with retro_f_cmp = Some r }
      | PIT_f_class ->
        let r =
          match retro.retro_f_class with
          | None -> ((ind,1), (ind,2), (ind,3), (ind,4),
                     (ind,5), (ind,6), (ind,7), (ind,8),
                     (ind,9))
          | Some (((ind',_),_,_,_,_,_,_,_,_) as t) ->
            check_same_inds pit ind ind'; t in
        { retro with retro_f_class = Some r }
    end

let add_retroknowledge env action =
  set_retroknowledge env (add_retroknowledge (Environ.retroknowledge env) action)

let get_int_type env =
  match (Environ.retroknowledge env).retro_int63 with
  | Some c -> c
  | None -> anomaly Pp.(str"Reduction of primitive: int63 not registered")

let get_float_type env =
  match (Environ.retroknowledge env).retro_float64 with
  | Some c -> c
  | None -> anomaly Pp.(str"Reduction of primitive: float64 not registered")

let get_string_type env =
  match (Environ.retroknowledge env).retro_string with
  | Some c -> c
  | None -> anomaly Pp.(str"Reduction of primitive: string not registered")

let get_cmp_type env =
  match (Environ.retroknowledge env).retro_cmp with
  | Some (((mindcmp,_),_),_,_) ->
     Constant.make (MutInd.user mindcmp) (MutInd.canonical mindcmp)
  | None -> anomaly Pp.(str"Reduction of primitive: comparison not registered")

let get_bool_constructors env =
  match (Environ.retroknowledge env).retro_bool with
  | Some r -> r
  | None -> anomaly Pp.(str"Reduction of primitive: bool not registered")

let get_carry_constructors env =
  match (Environ.retroknowledge env).retro_carry with
  | Some r -> r
  | None -> anomaly Pp.(str"Reduction of primitive: carry not registered")

let get_pair_constructor env =
  match (Environ.retroknowledge env).retro_pair with
  | Some c  -> c
  | None -> anomaly Pp.(str"Reduction of primitive: pair not registered")

let get_cmp_constructors env =
  match (Environ.retroknowledge env).retro_cmp with
  | Some r -> r
  | None -> anomaly Pp.(str"Reduction of primitive: cmp not registered")

let get_f_cmp_constructors env =
  match (Environ.retroknowledge env).retro_f_cmp with
  | Some r -> r
  | None -> anomaly Pp.(str"Reduction of primitive: fcmp not registered")

let get_f_class_constructors env =
  match (Environ.retroknowledge env).retro_f_class with
  | Some r -> r
  | None -> anomaly Pp.(str"Reduction of primitive: fclass not registered")

exception NativeDestKO

module type RedNativeEntries =
  sig
    type elem
    type args
    type evd (* will be unit in kernel, evar_map outside *)
    type uinstance

    val get : args -> int -> elem
    val get_int : evd -> elem -> Uint63.t
    val get_word8 : evd -> elem -> Primitive_words_runtime.Word8.t
    val get_word16 : evd -> elem -> Primitive_words_runtime.Word16.t
    val get_word32 : evd -> elem -> Primitive_words_runtime.Word32.t
    val get_word64 : evd -> elem -> Primitive_words_runtime.Word64.t
    val get_word128 : evd -> elem -> Primitive_words_runtime.Word128.t
    val get_word256 : evd -> elem -> Primitive_words_runtime.Word256.t
    val get_float : evd -> elem -> Float64.t
    val get_string : evd -> elem -> Pstring.t
    val get_parray : evd -> elem -> elem Parray.t
    val mkInt : env -> Uint63.t -> elem
    val mkWord8 : env -> Primitive_words_runtime.Word8.t -> elem
    val mkWord16 : env -> Primitive_words_runtime.Word16.t -> elem
    val mkWord32 : env -> Primitive_words_runtime.Word32.t -> elem
    val mkWord64 : env -> Primitive_words_runtime.Word64.t -> elem
    val mkWord128 : env -> Primitive_words_runtime.Word128.t -> elem
    val mkWord256 : env -> Primitive_words_runtime.Word256.t -> elem
    val mkFloat : env -> Float64.t -> elem
    val mkString : env -> Pstring.t -> elem
    val mkBool : env -> bool -> elem
    val mkCarry : env -> bool -> elem -> elem (* true if carry *)
    val mkIntPair : env -> elem -> elem -> elem
    val mkFloatIntPair : env -> elem -> elem -> elem
    val mkLt : env -> elem
    val mkEq : env -> elem
    val mkGt : env -> elem
    val mkFLt : env -> elem
    val mkFEq : env -> elem
    val mkFGt : env -> elem
    val mkFNotComparable : env -> elem
    val mkPNormal : env -> elem
    val mkNNormal : env -> elem
    val mkPSubn : env -> elem
    val mkNSubn : env -> elem
    val mkPZero : env -> elem
    val mkNZero : env -> elem
    val mkPInf : env -> elem
    val mkNInf : env -> elem
    val mkNaN : env -> elem
    val mkArray : env -> uinstance -> elem Parray.t -> elem -> elem
  end

module type RedNative =
 sig
   type elem
   type args
   type evd
   type uinstance
   val red_prim : env -> evd -> CPrimitives.t -> uinstance -> args -> elem option
 end

module RedNative (E:RedNativeEntries) :
  RedNative with type elem = E.elem
  with type args = E.args
  with type evd = E.evd
  with type uinstance = E.uinstance =
struct
  type elem = E.elem
  type args = E.args
  type evd = E.evd
  type uinstance = E.uinstance

  module type Word_runtime = sig
    type t
    val neg : t -> t
    val add : t -> t -> t
    val sub : t -> t -> t
    val mul : t -> t -> t
    val logand : t -> t -> t
    val logor : t -> t -> t
    val logxor : t -> t -> t
    val lognot : t -> t
    val equal : t -> t -> bool
    val ltb_unsigned : t -> t -> bool
    val leb_unsigned : t -> t -> bool
    val ltb_signed : t -> t -> bool
    val leb_signed : t -> t -> bool
    val shift_left : t -> t -> t
    val shift_right_logical : t -> t -> t
    val shift_right_arithmetic : t -> t -> t
    val divu_total : t -> t -> t
    val modu_total : t -> t -> t
    val divs_total : t -> t -> t
    val rems_total : t -> t -> t
  end

  let get_int evd args i = E.get_int evd (E.get args i)

  let get_int1 evd args = get_int evd args 0

  let get_int2 evd args = get_int evd args 0, get_int evd args 1

  let get_int3 evd args =
    get_int evd args 0, get_int evd args 1, get_int evd args 2

  let get_word64 evd args i = E.get_word64 evd (E.get args i)

  let get_word8 evd args i = E.get_word8 evd (E.get args i)
  let get_word16 evd args i = E.get_word16 evd (E.get args i)
  let get_word32 evd args i = E.get_word32 evd (E.get args i)
  let get_word128 evd args i = E.get_word128 evd (E.get args i)
  let get_word256 evd args i = E.get_word256 evd (E.get args i)

  let reduce_word (type a) env evd args op
      (get : evd -> args -> int -> a) (mk : env -> a -> E.elem)
      (module W : Word_runtime with type t = a) =
    let x () = get evd args 0 in
    let y () = get evd args 1 in
    match op with
    | CPrimitives.Wneg -> mk env (W.neg (x ()))
    | Wadd -> mk env (W.add (x ()) (y ()))
    | Wsub -> mk env (W.sub (x ()) (y ()))
    | Wmul -> mk env (W.mul (x ()) (y ()))
    | Wland -> mk env (W.logand (x ()) (y ()))
    | Wlor -> mk env (W.logor (x ()) (y ()))
    | Wlxor -> mk env (W.logxor (x ()) (y ()))
    | Wlnot -> mk env (W.lognot (x ()))
    | Weq -> E.mkBool env (W.equal (x ()) (y ()))
    | Wltu -> E.mkBool env (W.ltb_unsigned (x ()) (y ()))
    | Wleu -> E.mkBool env (W.leb_unsigned (x ()) (y ()))
    | Wlts -> E.mkBool env (W.ltb_signed (x ()) (y ()))
    | Wles -> E.mkBool env (W.leb_signed (x ()) (y ()))
    | Wlsl -> mk env (W.shift_left (x ()) (y ()))
    | Wlsr -> mk env (W.shift_right_logical (x ()) (y ()))
    | Wasr -> mk env (W.shift_right_arithmetic (x ()) (y ()))
    | Wdivu -> mk env (W.divu_total (x ()) (y ()))
    | Wmodu -> mk env (W.modu_total (x ()) (y ()))
    | Wdivs -> mk env (W.divs_total (x ()) (y ()))
    | Wrems -> mk env (W.rems_total (x ()) (y ()))

  let get_float evd args i = E.get_float evd (E.get args i)

  let get_float1 evd args = get_float evd args 0

  let get_float2 evd args = get_float evd args 0, get_float evd args 1

  let get_parray evd args i = E.get_parray evd (E.get args i)

  let get_string evd args i = E.get_string evd (E.get args i)

  let red_prim_aux env evd op u args =
    let open CPrimitives in
    match op with
    | Int63head0 ->
      let i = get_int1 evd args in E.mkInt env (Uint63.head0 i)
    | Int63tail0 ->
      let i = get_int1 evd args in E.mkInt env (Uint63.tail0 i)
    | Int63add ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.add i1 i2)
    | Int63sub ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.sub i1 i2)
    | Int63mul ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.mul i1 i2)
    | Int63div ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.div i1 i2)
    | Int63mod ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.rem i1 i2)
    | Int63divs ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.divs i1 i2)
    | Int63mods ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.rems i1 i2)
    | Int63lsr ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.l_sr i1 i2)
    | Int63lsl ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.l_sl i1 i2)
    | Int63asr ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.a_sr i1 i2)
    | Int63land ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.l_and i1 i2)
    | Int63lor ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.l_or i1 i2)
    | Int63lxor ->
      let i1, i2 = get_int2 evd args in E.mkInt env (Uint63.l_xor i1 i2)
    | Int63addc ->
      let i1, i2 = get_int2 evd args in
      let s = Uint63.add i1 i2 in
      E.mkCarry env (Uint63.lt s i1) (E.mkInt env s)
    | Int63subc ->
      let i1, i2 = get_int2 evd args in
      let s = Uint63.sub i1 i2 in
      E.mkCarry env (Uint63.lt i1 i2) (E.mkInt env s)
    | Int63addCarryC  ->
      let i1, i2 = get_int2 evd args in
      let s = Uint63.add (Uint63.add i1 i2) (Uint63.of_int 1) in
      E.mkCarry env (Uint63.le s i1) (E.mkInt env s)
    | Int63subCarryC  ->
      let i1, i2 = get_int2 evd args in
      let s = Uint63.sub (Uint63.sub i1 i2) (Uint63.of_int 1) in
      E.mkCarry env (Uint63.le i1 i2) (E.mkInt env s)
    | Int63mulc ->
      let i1, i2 = get_int2 evd args in
      let (h, l) = Uint63.mulc i1 i2 in
      E.mkIntPair env (E.mkInt env h) (E.mkInt env l)
    | Int63diveucl ->
      let i1, i2 = get_int2 evd args in
      let q,r = Uint63.div i1 i2, Uint63.rem i1 i2 in
      E.mkIntPair env (E.mkInt env q) (E.mkInt env r)
    | Int63div21 ->
      let i1, i2, i3 = get_int3 evd args in
      let q,r = Uint63.div21 i1 i2 i3 in
      E.mkIntPair env (E.mkInt env q) (E.mkInt env r)
    | Int63addMulDiv ->
      let p, i, j = get_int3 evd args in
      E.mkInt env
        (Uint63.l_or
           (Uint63.l_sl i p)
           (Uint63.l_sr j (Uint63.sub (Uint63.of_int Uint63.uint_size) p)))
    | Int63eq ->
      let i1, i2 = get_int2 evd args in
      E.mkBool env (Uint63.equal i1 i2)
    | Int63lt ->
      let i1, i2 = get_int2 evd args in
      E.mkBool env (Uint63.lt i1 i2)
    | Int63le ->
      let i1, i2 = get_int2 evd args in
      E.mkBool env (Uint63.le i1 i2)
    | Int63lts ->
      let i1, i2 = get_int2 evd args in
      E.mkBool env (Uint63.lts i1 i2)
    | Int63les ->
      let i1, i2 = get_int2 evd args in
      E.mkBool env (Uint63.les i1 i2)
    | Int63compare ->
      let i1, i2 = get_int2 evd args in
      begin match Uint63.compare i1 i2 with
        | x when x < 0 ->  E.mkLt env
        | 0 -> E.mkEq env
        | _ -> E.mkGt env
      end
    | Int63compares ->
      let i1, i2 = get_int2 evd args in
      begin match Uint63.compares i1 i2 with
        | x when x < 0 ->  E.mkLt env
        | 0 -> E.mkEq env
        | _ -> E.mkGt env
      end
    | Word (width, op) ->
      begin match width with
      | Word8 -> reduce_word env evd args op get_word8 E.mkWord8
          (module Primitive_words_runtime.Word8)
      | Word16 -> reduce_word env evd args op get_word16 E.mkWord16
          (module Primitive_words_runtime.Word16)
      | Word32 -> reduce_word env evd args op get_word32 E.mkWord32
          (module Primitive_words_runtime.Word32)
      | Word64 ->
        let module W = struct
          include Primitive_words_runtime.Word64
          let shift_left = shift_left_word
          let shift_right_logical = shift_right_logical_word
          let shift_right_arithmetic = shift_right_arithmetic_word
        end in
        reduce_word env evd args op get_word64 E.mkWord64 (module W)
      | Word128 ->
        let module W = struct
          include Primitive_words_runtime.Word128
          let shift_left = shift_left_word
          let shift_right_logical = shift_right_logical_word
          let shift_right_arithmetic = shift_right_arithmetic_word
        end in
        reduce_word env evd args op get_word128 E.mkWord128 (module W)
      | Word256 ->
        let module W = struct
          include Primitive_words_runtime.Word256
          let shift_left = shift_left_word
          let shift_right_logical = shift_right_logical_word
          let shift_right_arithmetic = shift_right_arithmetic_word
        end in
        reduce_word env evd args op get_word256 E.mkWord256 (module W)
      end
    | Float64opp ->
      let f = get_float1 evd args in E.mkFloat env (Float64.opp f)
    | Float64abs ->
      let f = get_float1 evd args in E.mkFloat env (Float64.abs f)
    | Float64eq ->
      let i1, i2 = get_float2 evd args in
      E.mkBool env (Float64.eq i1 i2)
    | Float64lt ->
      let i1, i2 = get_float2 evd args in
      E.mkBool env (Float64.lt i1 i2)
    | Float64le ->
      let i1, i2 = get_float2 evd args in
      E.mkBool env (Float64.le i1 i2)
    | Float64compare ->
      let f1, f2 = get_float2 evd args in
      (match Float64.compare f1 f2 with
      | Float64.FEq -> E.mkFEq env
      | Float64.FLt -> E.mkFLt env
      | Float64.FGt -> E.mkFGt env
      | Float64.FNotComparable -> E.mkFNotComparable env)
    | Float64equal ->
      let f1, f2 = get_float2 evd args in
      E.mkBool env (Float64.equal f1 f2)
    | Float64classify ->
      let f = get_float1 evd args in
      (match Float64.classify f with
      | Float64.PNormal -> E.mkPNormal env
      | Float64.NNormal -> E.mkNNormal env
      | Float64.PSubn -> E.mkPSubn env
      | Float64.NSubn -> E.mkNSubn env
      | Float64.PZero -> E.mkPZero env
      | Float64.NZero -> E.mkNZero env
      | Float64.PInf -> E.mkPInf env
      | Float64.NInf -> E.mkNInf env
      | Float64.NaN -> E.mkNaN env)
    | Float64add ->
      let f1, f2 = get_float2 evd args in E.mkFloat env (Float64.add f1 f2)
    | Float64sub ->
      let f1, f2 = get_float2 evd args in E.mkFloat env (Float64.sub f1 f2)
    | Float64mul ->
      let f1, f2 = get_float2 evd args in E.mkFloat env (Float64.mul f1 f2)
    | Float64div ->
      let f1, f2 = get_float2 evd args in E.mkFloat env (Float64.div f1 f2)
    | Float64sqrt ->
      let f = get_float1 evd args in E.mkFloat env (Float64.sqrt f)
    | Float64ofUint63 ->
      let i = get_int1 evd args in E.mkFloat env (Float64.of_uint63 i)
    | Float64normfr_mantissa ->
      let f = get_float1 evd args in E.mkInt env (Float64.normfr_mantissa f)
    | Float64frshiftexp ->
      let f = get_float1 evd args in
      let (m,e) = Float64.frshiftexp f in
      E.mkFloatIntPair env (E.mkFloat env m) (E.mkInt env e)
    | Float64ldshiftexp ->
      let f = get_float evd args 0 in
      let e = get_int evd args 1 in
      E.mkFloat env (Float64.ldshiftexp f e)
    | Float64next_up ->
      let f = get_float1 evd args in E.mkFloat env (Float64.next_up f)
    | Float64next_down ->
      let f = get_float1 evd args in E.mkFloat env (Float64.next_down f)
    | Arraymake ->
      let ty = E.get args 0 in
      let i = get_int evd args 1 in
      let d = E.get args 2 in
      E.mkArray env u (Parray.make i d) ty
    | Arrayget ->
      let t = get_parray evd args 1 in
      let i = get_int evd args 2 in
      Parray.get t i
    | Arraydefault ->
      let t = get_parray evd args 1 in
      Parray.default t
    | Arrayset ->
      let ty = E.get args 0 in
      let t = get_parray evd args 1 in
      let i = get_int evd args 2 in
      let a = E.get args 3 in
      let t' = Parray.set t i a in
      E.mkArray env u t' ty
    | Arraycopy ->
      let ty = E.get args 0 in
      let t = get_parray evd args 1 in
      let t' = Parray.copy t in
      E.mkArray env u t' ty
    | Arraylength ->
      let t = get_parray evd args 1 in
      E.mkInt env (Parray.length t)
    | Stringmake ->
      let i = get_int evd args 0 in
      let c = get_int evd args 1 in
      E.mkString env (Pstring.make i c)
    | Stringlength ->
      let s = get_string evd args 0 in
      E.mkInt env (Pstring.length s)
    | Stringget ->
      let s = get_string evd args 0 in
      let i = get_int evd args 1 in
      E.mkInt env (Pstring.get s i)
    | Stringsub ->
      let s = get_string evd args 0 in
      let off = get_int evd args 1 in
      let len = get_int evd args 2 in
      E.mkString env (Pstring.sub s off len)
    | Stringcat ->
      let s1 = get_string evd args 0 in
      let s2 = get_string evd args 1 in
      E.mkString env (Pstring.cat s1 s2)
    | Stringcompare ->
      let s1 = get_string evd args 0 in
      let s2 = get_string evd args 1 in
      begin match Pstring.compare s1 s2 with
        | x when x < 0 -> E.mkLt env
        | 0 -> E.mkEq env
        | _ -> E.mkGt env
      end

  let red_prim env evd p u args =
    try
      let r =
        red_prim_aux env evd p u args
      in Some r
    with NativeDestKO -> None

end
