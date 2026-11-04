module W8 = Primitive_words_runtime.Word8
module W16 = Primitive_words_runtime.Word16
module W32 = Primitive_words_runtime.Word32
module W64 = Primitive_words_runtime.Word64
module W128 = Primitive_words_runtime.Word128
module W256 = Primitive_words_runtime.Word256

type any_word =
  | A8 of W8.t | A16 of W16.t | A32 of W32.t | A64 of W64.t
  | A128 of W128.t | A256 of W256.t

type archive = {
  words : any_word list;
  nested : ((any_word option * any_word option) list * bool list) option;
}

let require condition message = if not condition then failwith message
let backend () = match Sys.backend_type with
  | Native -> "native" | Bytecode -> "bytecode" | Other name -> name

let samples () =
  [ A8 (W8.of_int 0xa5); A16 (W16.of_int 0xa55a);
    A32 (W32.of_int32 0xa55a_a55al);
    A64 (W64.of_int64 0xfedc_ba98_7654_3210L);
    A128 (W128.of_limbs ~low:0x0123_4567_89ab_cdefL
      ~high:0xfedc_ba98_7654_3210L);
    A256 (W256.of_limbs ~limb0:0x0123_4567_89ab_cdefL
      ~limb1:0x1111_2222_3333_4444L ~limb2:0xaaaa_bbbb_cccc_ddddL
      ~limb3:0xfedc_ba98_7654_3210L) ]

let repr = function
  | A8 x -> Obj.repr x | A16 x -> Obj.repr x | A32 x -> Obj.repr x
  | A64 x -> Obj.repr x | A128 x -> Obj.repr x | A256 x -> Obj.repr x

let increment = function
  | A8 x -> A8 (W8.add x W8.one) | A16 x -> A16 (W16.add x W16.one)
  | A32 x -> A32 (W32.add x W32.one) | A64 x -> A64 (W64.add x W64.one)
  | A128 x -> A128 (W128.add x W128.one)
  | A256 x -> A256 (W256.add x W256.one)

let width = function
  | A8 _ -> 8 | A16 _ -> 16 | A32 _ -> 32 | A64 _ -> 64
  | A128 _ -> 128 | A256 _ -> 256

let equal_any left right = match left, right with
  | A8 x, A8 y -> W8.equal x y | A16 x, A16 y -> W16.equal x y
  | A32 x, A32 y -> W32.equal x y | A64 x, A64 y -> W64.equal x y
  | A128 x, A128 y -> W128.equal x y | A256 x, A256 y -> W256.equal x y
  | _ -> false

let read_at index value =
  match index with
  | 0 -> ignore (W8.to_int (Obj.obj value))
  | 1 -> ignore (W16.to_int (Obj.obj value))
  | 2 -> ignore (W32.to_int32 (Obj.obj value))
  | 3 -> ignore (W64.to_int64 (Obj.obj value))
  | 4 -> ignore (W128.to_limbs (Obj.obj value))
  | 5 -> ignore (W256.to_limbs (Obj.obj value))
  | _ -> assert false

let predicates = [|W8.is_runtime_value; W16.is_runtime_value;
  W32.is_runtime_value; W64.is_runtime_value;
  W128.is_runtime_value; W256.is_runtime_value|]

module type WORD_CALLBACK = sig
  type t
  val one : t
  val add : t -> t -> t
  val equal : t -> t -> bool
end

module Repeat (W : WORD_CALLBACK) = struct
  let rec apply count callback value =
    if count = 0 then value else apply (count - 1) callback (callback value)
  let captured captured value = W.add value captured
  let check value = W.equal (apply 258 (captured W.one) value)
      (apply 258 (fun x -> W.add x W.one) value)
end

module Repeat8 = Repeat(W8)
module Repeat256 = Repeat(W256)

let archive () =
  let words = samples () in
  let advanced = List.map increment words in
  { words; nested = Some (List.map2 (fun x y -> Some x, Some y) words advanced,
      List.map2 (fun x y -> width x = width y && not (equal_any x y)) words advanced) }

let validate_archive value =
  require (List.map width value.words = [8;16;32;64;128;256]) "archive widths";
  match value.nested with
  | Some (pairs, checks) ->
      require (List.length pairs = 6 && List.for_all (fun x -> x) checks)
        "nested archive";
      List.iter2 (fun before pair -> match pair with
        | Some x, Some y ->
            require (width before = width x && width x = width y) "nested width";
            require (equal_any before x && not (equal_any x y)) "nested values"
        | _ -> failwith "nested option") value.words pairs
  | None -> failwith "nested archive missing"

let boundary () =
  let values = samples () in
  let objects = Array.of_list (List.map repr values) in
  Array.iteri (fun i predicate -> Array.iteri (fun j value ->
    require (predicate value = (i = j)) "custom identity predicate";
    if i = j then read_at i value
    else match read_at i value with
      | () -> failwith "wrong-width access accepted"
      | exception Invalid_argument _ -> ()) objects) predicates;
  Array.iteri (fun i left -> Array.iteri (fun j right ->
    require ((Stdlib.compare left right = 0) = (i = j))
      "polymorphic compare/custom identity") objects) objects;
  List.iter (fun value ->
    let same = match value with
      | A8 x -> A8 (W8.add x W8.zero) | A16 x -> A16 (W16.add x W16.zero)
      | A32 x -> A32 (W32.add x W32.zero) | A64 x -> A64 (W64.add x W64.zero)
      | A128 x -> A128 (W128.add x W128.zero)
      | A256 x -> A256 (W256.add x W256.zero) in
    require (equal_any value same) "width equality";
    require (Hashtbl.hash (repr value) = Hashtbl.hash (repr same)) "width hash") values;
  let caught = ref 0 in
  for _ = 1 to 64 do
    let mapped = List.map increment values in
    let folded = List.fold_left (fun n value -> n + width value) 0 mapped in
    require (folded = 504) "map/fold";
    List.iter (fun f -> try f (); failwith "exception path accepted"
      with Invalid_argument _ -> incr caught)
      [ (fun () -> read_at 0 objects.(5)); (fun () -> read_at 5 objects.(0)) ];
    Gc.minor (); Gc.full_major (); Gc.compact ();
    List.iter2 (fun before after ->
      require (width before = width after && not (equal_any before after))
        "GC/HOF identity") values mapped
  done;
  require (!caught = 128) "exception callback count";
  require (Repeat8.check W8.max_unsigned) "functor/closure Word8";
  require (Repeat256.check W256.max_unsigned) "functor/closure Word256";
  validate_archive (archive ());
  Printf.printf "boundary_backend=%s\n" (backend ());
  print_endline "six_width_polymorphic_gc_compare_hash_wrong_access=passed"

let write path =
  let channel = open_out_bin path in
  Marshal.to_channel channel (archive ()) [];
  close_out channel;
  print_endline "nested_six_width_marshal_write=passed"

let read path =
  let channel = open_in_bin path in
  let value : archive = Marshal.from_channel channel in
  close_in channel;
  validate_archive value;
  Gc.full_major (); Gc.compact (); validate_archive value;
  print_endline "nested_six_width_marshal_read_gc=passed"

let reject path =
  match read path with
  | () -> failwith "malformed stream accepted"
  | exception ((Failure _ | Invalid_argument _ | End_of_file) as error) ->
      Printf.printf "marshal_rejected=%S\n" (Printexc.to_string error)

let () = match Array.to_list Sys.argv with
  | [_; "boundary"] -> boundary ()
  | [_; "write"; path] -> write path
  | [_; "read"; path] -> read path
  | [_; "reject"; path] -> reject path
  | _ -> invalid_arg "boundary | write FILE | read FILE | reject FILE"
