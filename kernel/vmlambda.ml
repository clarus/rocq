open Util
open Declarations
open Genlambda
open Vmvalues

type lval = int * structured_values (* keep the hash *)
type lambda = lval Genlambda.lambda

let get_lval (_, v) = v

(** Simplification of lambda expression *)

(*s Translation from [constr] to [lambda] *)

(* Translation of constructor *)

let is_value lc =
  match node lc with
  | Lval _ | Lint _ | Luint _ | Lword8 _ | Lword16 _ | Lword32 _ | Lword64 _ | Lword128 _ | Lword256 _ | Lfloat _ | Lstring _ -> true
  | _ -> false

let get_value lc =
  match node lc with
  | Luint i -> val_of_uint i
  | Lword8 i -> val_of_word8 i
  | Lword16 i -> val_of_word16 i
  | Lword32 i -> val_of_word32 i
  | Lword64 i -> val_of_word64 i
  | Lword128 i -> val_of_word128 i
  | Lword256 i -> val_of_word256 i
  | Lval (_, v) -> v
  | Lint i -> val_of_int i
  | Lfloat f -> val_of_float f
  | Lstring s -> val_of_string s
  | _ -> assert false

let hash_block tag args =
  let open Hashset.Combine in
  let fold accu v =
    let h = match node v with
    | Luint i -> Uint63.hash i
    | Lword8 i -> Primitive_words_runtime.Word8.hash i
    | Lword16 i -> Primitive_words_runtime.Word16.hash i
    | Lword32 i -> Primitive_words_runtime.Word32.hash i
    | Lword64 i -> Primitive_words_runtime.Word64.hash i
    | Lword128 i -> Primitive_words_runtime.Word128.hash i
    | Lword256 i -> Primitive_words_runtime.Word256.hash i
    | Lint i -> Hashtbl.hash (i : int)
    | Lfloat f -> Float64.hash f
    | Lstring s -> Pstring.hash s
    | Lval (h, _) -> h
    | _ -> assert false
    in
    combine accu h
  in
  combine tag (Array.fold_left fold 0 args)

module HashBlock =
struct
  type t = int * structured_values array * structured_values (* tag, block, value *)
  let eq (tag1, args1, _) (tag2, args2, _) =
    Int.equal tag1 tag2 && CArray.equal (==) args1 args2
end

module HashsetBlock = Hashset.Make(HashBlock)

let block_table = HashsetBlock.create 97

let as_value tag args =
  if Array.for_all is_value args then
    let h = hash_block tag args in
    (* Don't simplify this to Array.map because of flat float arrays *)
    let args =
      let dummy_val = Obj.magic 0 in
      let ans = Array.make (Array.length args) dummy_val in
      let () = Array.iteri (fun i v -> ans.(i) <- get_value v) args in
      ans
    in
    if tag < Obj.last_non_constant_constructor_tag then
      let block = val_of_block tag args in
      let (_, _, block) = HashsetBlock.repr h (tag, args, block) block_table in
      Some (h, block)
    else
      let args = Array.append [| val_of_int (tag - Obj.last_non_constant_constructor_tag) |] args in
      let block = val_of_block Obj.last_non_constant_constructor_tag args in
      let (_, _, block) = HashsetBlock.repr h (tag, args, block) block_table in
      Some (h, block)
  else None

module Val =
struct
  type value = int * structured_values
  let as_value = as_value
  let check_inductive (_, i) mb =
    let { mind_typename=name; mind_nb_args; mind_nb_constant; _ } = mb.mind_packets.(i) in
    Vmerrors.check_compilable_ind ~name ~mind_nb_args ~mind_nb_constant
end

module Lambda = Genlambda.Make(Val)

(*********************************)
let dump_lambda_flag, dump_lambda = CDebug.create_full ~name:"vmlambda" ()

let lambda_of_constr env sigma c =
  let lam = Lambda.lambda_of_constr env sigma c in
  let lam = optimize lam in
  dump_lambda (fun () -> pp_lam lam);
  lam
