(************************************************************************)
(* Native persistent arrays with unsigned 64-bit lengths.                *)
(* Distributed under the GNU Lesser General Public License Version 2.1. *)
(************************************************************************)

module Word = Primitive_words_runtime.Word64
type size = Word.t

(* An element can itself be a boxed float. Keeping leaves explicitly as
   Obj.t arrays prevents OCaml's float-array specialization from changing
   their representation. These arrays are never modified after publication. *)
module UArray = struct
  type 'a t = Obj.t array
  let length = Array.length
  let get a i = Obj.obj (Array.get a i)
  let init n f =
    let a = Array.make n (Obj.repr ()) in
    for i = 0 to n - 1 do Array.set a i (Obj.repr (f i)) done;
    a
  let make n x =
    let a = Array.make n (Obj.repr ()) in
    Array.fill a 0 n (Obj.repr x);
    a
  let sub a pos len = Array.sub a pos len
  let set a i x =
    let b = Array.copy a in
    Array.set b i (Obj.repr x);
    b
  let append = Array.append
  let to_array a = Array.init (length a) (get a)
end

let leaf_capacity = 128

type 'a t =
  | Empty
  | Leaf of 'a UArray.t
  | Node of { left : 'a t; right : 'a t; length : int64; height : int }

let empty = Empty
let is_empty = function Empty -> true | Leaf _ | Node _ -> false
let length64 = function
  | Empty -> 0L
  | Leaf a -> Int64.of_int (UArray.length a)
  | Node n -> n.length
let length a = Word.of_int64 (length64 a)
let height = function Empty -> 0 | Leaf _ -> 1 | Node n -> n.height
let ule a b = Int64.unsigned_compare a b <= 0
let ult a b = Int64.unsigned_compare a b < 0

(* Callers establish that the combined length fits before creating nodes. *)
let node left right = match left, right with
  | Empty, t | t, Empty -> t
  | _ -> Node { left; right; length = Int64.add (length64 left) (length64 right);
                height = 1 + max (height left) (height right) }

let balance left right =
  if height left > height right + 1 then
    match left with
    | Node l when height l.left >= height l.right ->
      node l.left (node l.right right)
    | Node { left = ll; right = Node lr; _ } ->
      node (node ll lr.left) (node lr.right right)
    | Empty | Leaf _ | Node _ -> assert false
  else if height right > height left + 1 then
    match right with
    | Node r when height r.right >= height r.left ->
      node (node left r.left) r.right
    | Node { left = Node rl; right = rr; _ } ->
      node (node left rl.left) (node rl.right rr)
    | Empty | Leaf _ | Node _ -> assert false
  else node left right

(* Height-aware join is also used by splitting. Unlike repeatedly invoking
   a general concatenation at each split frame, its total work is logarithmic. *)
let rec join left right =
  if height left > height right + 1 then
    match left with
    | Node l -> balance l.left (join l.right right)
    | Empty | Leaf _ -> assert false
  else if height right > height left + 1 then
    match right with
    | Node r -> balance (join left r.left) r.right
    | Empty | Leaf _ -> assert false
  else node left right

let rec first = function
  | Leaf a -> a | Node n -> first n.left | Empty -> assert false
let rec last = function
  | Leaf a -> a | Node n -> last n.right | Empty -> assert false
let rec pop_first = function
  | Leaf a -> a, Empty
  | Node n -> let a, left = pop_first n.left in a, join left n.right
  | Empty -> assert false
let rec pop_last = function
  | Leaf a -> Empty, a
  | Node n -> let right, a = pop_last n.right in join n.left right, a
  | Empty -> assert false

let concat_valid left right = match left, right with
  | Empty, t | t, Empty -> t
  | _ ->
    if UArray.length (last left) + UArray.length (first right) <= leaf_capacity then
      let left, a = pop_last left in
      let b, right = pop_first right in
      join (join left (Leaf (UArray.append a b))) right
    else join left right

let concat left right =
  if ule (length64 right) (Int64.sub Int64.minus_one (length64 left))
  then Some (concat_valid left right)
  else None

let compact_first = function
  | Empty | Leaf _ as t -> t
  | t -> let a, rest = pop_first t in concat_valid (Leaf a) rest
let compact_last = function
  | Empty | Leaf _ as t -> t
  | t -> let rest, a = pop_last t in concat_valid rest (Leaf a)

let leaf a = if UArray.length a = 0 then Empty else Leaf a

let rec split_raw t i =
  if Int64.equal i 0L then Empty, t
  else if Int64.equal i (length64 t) then t, Empty
  else match t with
  | Empty -> assert false
  | Leaf a ->
    let i = Int64.to_int i in
    leaf (UArray.sub a 0 i), leaf (UArray.sub a i (UArray.length a - i))
  | Node n ->
    let len = length64 n.left in
    if ult i len then
      let l, r = split_raw n.left i in l, join r n.right
    else
      let l, r = split_raw n.right (Int64.sub i len) in join n.left l, r

let split t i =
  let left, right = split_raw t i in compact_last left, compact_first right

let range_valid t start len =
  ule start (length64 t) && ule len (Int64.sub (length64 t) start)

let slice t start len =
  let start, len = Word.to_int64 start, Word.to_int64 len in
  if not (range_valid t start len) then None
  else if Int64.equal len 0L then Some Empty
  else
    let _, rest = split t start in
    let selected, _ = split rest len in Some selected

let replace t start source =
  let start = Word.to_int64 start in
  if not (range_valid t start (length64 source)) then None
  else if is_empty source then Some t
  else
    let left, rest = split t start in
    let _, right = split rest (length64 source) in
    Some (concat_valid (concat_valid left source) right)

let rec get_valid t i = match t with
  | Empty -> assert false
  | Leaf a -> UArray.get a (Int64.to_int i)
  | Node n ->
    if ult i (length64 n.left) then get_valid n.left i
    else get_valid n.right (Int64.sub i (length64 n.left))

let get t i =
  let i = Word.to_int64 i in
  if ult i (length64 t) then Some (get_valid t i) else None

let rec set_valid t i x = match t with
  | Empty -> assert false
  | Leaf a -> Leaf (UArray.set a (Int64.to_int i) x)
  | Node n ->
    if ult i (length64 n.left) then node (set_valid n.left i x) n.right
    else node n.left (set_valid n.right (Int64.sub i (length64 n.left)) x)

let set t i x =
  let i = Word.to_int64 i in
  if ult i (length64 t) then Some (set_valid t i x) else None

let make n x =
  let n = Word.to_int64 n in
  let cap = Int64.of_int leaf_capacity in
  let chunks = Int64.add (Int64.unsigned_div n cap)
      (if Int64.equal (Int64.unsigned_rem n cap) 0L then 0L else 1L) in
  let rec build chunks n =
    if Int64.equal chunks 0L then Empty
    else if Int64.equal chunks 1L then Leaf (UArray.make (Int64.to_int n) x)
    else
      let left_chunks = Int64.shift_right_logical chunks 1 in
      let left_length = Int64.mul left_chunks cap in
      let left = build left_chunks left_length in
      let right = build (Int64.sub chunks left_chunks) (Int64.sub n left_length) in
      node left right
  in build chunks n

let repeat = make

let of_array a =
  let rec build pos len =
    if len = 0 then Empty
    else if len <= leaf_capacity then Leaf (UArray.init len (fun i -> a.(pos + i)))
    else
      let chunks = 1 + (len - 1) / leaf_capacity in
      let left_len = (chunks / 2) * leaf_capacity in
      node (build pos left_len) (build (pos + left_len) (len - left_len))
  in build 0 (Array.length a)

let of_chunks chunks =
  List.fold_left (fun t a -> match concat t (of_array a) with
    | Some t -> t
    | None -> invalid_arg "Parray64.of_chunks: length overflow") Empty chunks

let to_chunks t =
  let rec visit t rest = match t with
  | Empty -> rest
  | Leaf a -> UArray.to_array a :: rest
  | Node n -> visit n.left (visit n.right rest)
  in visit t []

let rec fold_left f s = function
  | Empty -> s
  | Leaf a ->
    let s = ref s in
    for i = 0 to UArray.length a - 1 do s := f !s (UArray.get a i) done;
    !s
  | Node n -> fold_left f (fold_left f s n.left) n.right

let rec fold_right f t s = match t with
  | Empty -> s
  | Leaf a ->
    let s = ref s in
    for i = UArray.length a - 1 downto 0 do s := f (UArray.get a i) !s done;
    !s
  | Node n -> fold_right f n.left (fold_right f n.right s)

let iter f t = fold_left (fun () x -> f x) () t
let rec exists f = function
  | Empty -> false
  | Leaf a -> Array.exists (fun x -> f (Obj.obj x)) a
  | Node n -> exists f n.left || exists f n.right
let for_all f t = not (exists (fun x -> not (f x)) t)

let rec map f = function
  | Empty -> Empty
  | Leaf a -> Leaf (UArray.init (UArray.length a) (fun i -> f (UArray.get a i)))
  | Node n -> let left = map f n.left in let right = map f n.right in node left right

let rec smartmap f t = match t with
  | Empty -> t
  | Leaf a ->
    let changed = ref false in
    let b = UArray.init (UArray.length a) (fun i ->
      let x = UArray.get a i in let y = f x in
      if x != y then changed := true;
      y) in
    if !changed then Leaf b else t
  | Node n ->
    let left = smartmap f n.left in let right = smartmap f n.right in
    if left == n.left && right == n.right then t else node left right

let fold_map f s t =
  let state = ref s in
  let t = map (fun x -> let s, y = f !state x in state := s; y) t in
  !state, t

(* A zipper walks each tree once and does not allocate a flattened sequence. *)
let rec next = function
  | [] -> None
  | Empty :: rest -> next rest
  | Node n :: rest -> next (n.left :: n.right :: rest)
  | Leaf a :: rest -> Some (a, rest)

let fold_left2 f s t1 t2 =
  if not (Int64.equal (length64 t1) (length64 t2)) then
    invalid_arg "Parray64.fold_left2";
  let advance pending = match next pending with
    | None -> None, 0, []
    | Some (a, rest) -> Some a, 0, rest
  in
  let rec loop s a i ar b j br =
    match a, b with
    | None, None -> s
    | Some a, Some b ->
      let count = min (UArray.length a - i) (UArray.length b - j) in
      let s = ref s in
      for k = 0 to count - 1 do s := f !s (UArray.get a (i+k)) (UArray.get b (j+k)) done;
      let i, j = i + count, j + count in
      let a, i, ar = if i = UArray.length a then advance ar else Some a, i, ar in
      let b, j, br = if j = UArray.length b then advance br else Some b, j, br in
      loop !s a i ar b j br
    | None, Some _ | Some _, None -> assert false
  in
  let a, i, ar = advance [t1] in let b, j, br = advance [t2] in
  loop s a i ar b j br
