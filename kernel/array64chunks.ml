(************************************************************************)
(* Chunked literal payloads for native arrays with 64-bit lengths.       *)
(* Distributed under the GNU Lesser General Public License Version 2.1. *)
(************************************************************************)

module Word = Primitive_words_runtime.Word64
type 'a t = 'a array list

let empty = []
let is_empty t = List.for_all (fun a -> Array.length a = 0) t
let chunk_capacity = 128

let of_arrays arrays =
  let chunks = List.fold_left (fun chunks a ->
    let rec copy pos chunks =
      if pos = Array.length a then chunks
      else
        let len = min chunk_capacity (Array.length a - pos) in
        copy (pos + len) (Array.sub a pos len :: chunks)
    in copy 0 chunks) [] arrays
  in List.rev chunks

let to_arrays t = t

let length64 t =
  List.fold_left (fun size a ->
    let n = Int64.of_int (Array.length a) in
    if Int64.unsigned_compare n (Int64.sub Int64.minus_one size) > 0 then
      invalid_arg "Array64chunks.length: length overflow";
    Int64.add size n) 0L t
let length t = Word.of_int64 (length64 t)

let iter f t = List.iter (Array.iter f) t
let exists f t = List.exists (Array.exists f) t
let for_all f t = List.for_all (Array.for_all f) t
let map f t = List.rev (List.fold_left (fun acc a -> Array.map f a :: acc) [] t)

let smartmap f t =
  let changed = ref false in
  let mapped = List.fold_left (fun acc a ->
    let chunk_changed = ref false in
    let b = Array.map (fun x ->
      let y = f x in if x != y then chunk_changed := true; y) a in
    if !chunk_changed then (changed := true; b :: acc) else a :: acc) [] t in
  if !changed then List.rev mapped else t

let fold_left f s t = List.fold_left (Array.fold_left f) s t
let fold_right f t s =
  List.fold_left (fun s a -> Array.fold_right f a s) s (List.rev t)
let fold_map f s t =
  let state = ref s in
  let t = map (fun x -> let s, y = f !state x in state := s; y) t in
  !state, t

(* The cursor also tolerates empty chunks. In particular comparison remains
   extensional for older or externally marshalled non-normalized payloads. *)
let rec cursor = function
  | [] -> None
  | a :: rest when Array.length a = 0 -> cursor rest
  | a :: rest -> Some (a, 0, rest)
let advance (a, i, rest) =
  if i + 1 = Array.length a then cursor rest else Some (a, i + 1, rest)

let fold_left2 f s a b =
  if not (Int64.equal (length64 a) (length64 b)) then
    invalid_arg "Array64chunks.fold_left2";
  let rec loop s a b = match a, b with
  | None, None -> s
  | Some ((aa, i, _) as ac), Some ((bb, j, _) as bc) ->
    let s = f s aa.(i) bb.(j) in loop s (advance ac) (advance bc)
  | None, Some _ | Some _, None -> assert false
  in loop s (cursor a) (cursor b)

let equal_norefl eq a b =
  let rec loop a b = match a, b with
  | None, None -> true
  | Some ((aa, i, _) as ac), Some ((bb, j, _) as bc) ->
    eq aa.(i) bb.(j) && loop (advance ac) (advance bc)
  | None, Some _ | Some _, None -> false
  in Int64.equal (length64 a) (length64 b) && loop (cursor a) (cursor b)

let equal eq a b = a == b || equal_norefl eq a b

let compare cmp a b =
  let rec loop a b = match a, b with
  | None, None -> 0
  | None, Some _ -> -1
  | Some _, None -> 1
  | Some ((aa, i, _) as ac), Some ((bb, j, _) as bc) ->
    let c = cmp aa.(i) bb.(j) in
    if c = 0 then loop (advance ac) (advance bc) else c
  in loop (cursor a) (cursor b)

let hash hash_element t =
  fold_left (fun h x -> h * 65599 + hash_element x) 0 t
