(* Standalone differential tests: compiled copies expose tree invariants only
   to this executable; the installed Parray64 interface remains abstract. *)
module P = Parray64_candidate
module C = Array64chunks_candidate
module W = Primitive_words_runtime.Word64
let size n = W.of_int64 (Int64.of_int n)
let get = Option.get
let checks = ref 0
let check name b = incr checks; if not b then failwith name

let rec invariant = function
  | P.Empty -> 0L, 0, 0, 0
  | P.Leaf a ->
    let n = P.UArray.length a in
    check "leaf bounds" (n > 0 && n <= P.leaf_capacity);
    check "uniform leaf representation" (Obj.tag (Obj.repr a) = 0);
    Int64.of_int n, 1, n, n
  | P.Node n ->
    let llen, lh, first, left_last = invariant n.left in
    let rlen, rh, right_first, last = invariant n.right in
    check "AVL balance" (abs (lh-rh) <= 1 && lh > 0 && rh > 0);
    check "adjacent leaf density" (left_last + right_first > P.leaf_capacity);
    check "cached height" (n.height = 1 + max lh rh);
    check "cached length" (Int64.equal n.length (Int64.add llen rlen));
    n.length, n.height, first, last

let contents t = Array.of_list (List.rev (P.fold_left (fun xs x -> x :: xs) [] t))
let compare name t a =
  ignore (invariant t);
  check (name ^ ": length") (W.equal (P.length t) (size (Array.length a)));
  check (name ^ ": contents") (contents t = a);
  check (name ^ ": chunks") (Array.concat (P.to_chunks t) = a)

let boundary_tests () =
  List.iter (fun n ->
    let a = Array.init n Fun.id in
    let t = P.of_array a in
    compare "of_array" t a;
    compare "repeat" (P.repeat (size n) 7) (Array.make n 7);
    check "end get" (P.get t (size n) = None);
    check "max get" (P.get t W.max_unsigned = None);
    check "end set" (P.set t (size n) 0 = None);
    check "empty slice at end" (P.is_empty (get (P.slice t (size n) (size 0))));
    check "oversized slice" (P.slice t (size 0) (size (n+1)) = None);
    check "overflow slice" (P.slice t W.max_unsigned (size 1) = None);
    check "zero invalid slice" (P.slice t (size (n+1)) (size 0) = None);
    List.iter (fun start -> if start <= n then
      List.iter (fun len -> if len <= n-start then
        let sliced = get (P.slice t (size start) (size len)) in
        compare "slice" sliced (Array.sub a start len);
        compare "replace original" (get (P.replace t (size start) sliced)) a)
        [0; 1; 31; 32; 63; 64; 127; 128; 129; n-start])
      [0; 1; 31; 63; 127; 128; 129; n])
    [0; 1; 2; 31; 32; 63; 64; 127; 128; 129; 255; 256; 257; 511; 1024; 4097];
  let floats = P.of_array [|1.5; 2.5; 3.5|] in
  compare "float array input" floats [|1.5; 2.5; 3.5|];
  let modified = get (P.set floats (size 1) 8.5) in
  check "float persistence" (P.get floats (size 1) = Some 2.5);
  check "float update" (P.get modified (size 1) = Some 8.5);
  compare "float repeat" (P.repeat (size 3) 2.75) [|2.75; 2.75; 2.75|];
  compare "float map" (P.map float_of_int (P.of_array [|1; 2; 3|])) [|1.; 2.; 3.|];
  let original = [|1; 2; 3|] in
  let t = P.of_array original in original.(0) <- 99;
  check "input copied" (P.get t W.zero = Some 1);
  let chunks = P.to_chunks t in (List.hd chunks).(0) <- 88;
  check "output copied" (P.get t W.zero = Some 1)

let random_tests () =
  let rng = Random.State.make [|0x22550; 0x64|] in
  let choose n = Random.State.int rng n in
  let states = Array.make 128 (P.empty, [||]) in
  for round = 0 to 9999 do
    let t, a = states.(choose (Array.length states)) in
    let n = Array.length a in
    let t', a' = match choose 7 with
    | 0 -> let len = choose 1025 and x = choose 10000 in
      P.repeat (size len) x, Array.make len x
    | 1 when n > 0 ->
      let i = choose n and x = choose 10000 in
      let a' = Array.copy a in a'.(i) <- x;
      get (P.set t (size i) x), a'
    | 2 ->
      let start = choose (n+1) in let len = choose (n-start+1) in
      get (P.slice t (size start) (size len)), Array.sub a start len
    | 3 ->
      let start = choose (n+1) in let len = choose (n-start+1) in
      let x = choose 10000 in let a' = Array.copy a in
      Array.fill a' start len x;
      get (P.replace t (size start) (P.repeat (size len) x)), a'
    | 4 ->
      let src = choose (n+1) in let len = choose (n-src+1) in
      let dst = choose (n-len+1) in let a' = Array.copy a in
      Array.blit a src a' dst len;
      get (P.replace t (size dst) (get (P.slice t (size src) (size len)))), a'
    | 5 ->
      let u, b = states.(choose (Array.length states)) in
      if n + Array.length b > 8192 then t, a else
      get (P.concat t u), Array.append a b
    | _ -> P.map (fun x -> x lxor 13) t, Array.map (fun x -> x lxor 13) a in
    compare "random result" t' a';
    compare "preserved history" t a;
    states.(choose (Array.length states)) <- t', a';
    if round mod 100 = 0 then
      Array.iter (fun (t, a) -> compare "retained history" t a) states
  done

let large_lengths () =
  let power = ref (P.repeat (size 1) 17) in
  for _ = 1 to 63 do power := get (P.concat !power !power) done;
  check "unsigned high bit length" (W.equal (P.length !power) W.min_signed);
  check "u64 concat overflow" (P.concat !power !power = None);
  let low = W.of_int64 Int64.max_int in
  let almost = get (P.slice !power W.zero low) in
  let maximal = get (P.concat !power almost) in
  check "max length" (W.equal (P.length maximal) W.max_unsigned);
  let final = W.of_int64 (-2L) in
  check "last get unsigned" (P.get maximal final = Some 17);
  check "one past maximal" (P.get maximal W.max_unsigned = None);
  let changed = get (P.set maximal final 29) in
  check "last update" (P.get changed final = Some 29);
  check "huge snapshot" (P.get maximal final = Some 17);
  compare "huge tail slice" (get (P.slice changed (W.of_int64 (-5L)) (size 4)))
    [|17; 17; 17; 29|];
  check "maximal zero range" (P.slice maximal W.max_unsigned W.zero = Some P.empty);
  check "maximal overflowing range" (P.slice maximal W.max_unsigned W.one = None);
  check "wrapped range rejected" (P.slice maximal (W.of_int64 (-2L)) (size 3) = None);
  check "maximal concat empty" (get (P.concat maximal P.empty) == maximal);
  check "maximal concat one" (P.concat maximal (P.repeat W.one 0) = None);
  check "empty replacement at max" (get (P.replace maximal W.max_unsigned P.empty) == maximal);
  check "replacement past max" (P.replace maximal W.max_unsigned (P.repeat W.one 0) = None);
  let patterned = ref (P.of_array [|10; 11; 12|]) in
  for _ = 1 to 62 do patterned := get (P.concat !patterned !patterned) done;
  List.iter (fun i ->
    let expected = 10 + Int64.to_int (Int64.unsigned_rem i 3L) in
    check "high unsigned patterned index" (P.get !patterned (W.of_int64 i) = Some expected))
    [0L; 1L; 2L; Int64.max_int; Int64.min_int;
     Int64.add Int64.min_int 1L; Int64.sub (Int64.mul 3L (Int64.shift_left 1L 62)) 1L]

let traversal_tests () =
  let a = Array.init 1000 Fun.id in
  let t = P.of_array a in
  let u = P.of_chunks [Array.sub a 0 37; Array.sub a 37 111; Array.sub a 148 852] in
  let calls = ref 0 in
  check "different tree fold2" (P.fold_left2 (fun ok x y -> incr calls; ok && x=y) true t u);
  check "fold2 calls" (!calls = 1000);
  calls := 0;
  ignore (P.fold_left2 (fun () _ _ -> incr calls) () t t);
  check "fold2 physical identity still traverses" (!calls = 1000);
  check "heterogeneous fold2" (P.fold_left2 (fun ok x y -> ok && string_of_int x=y)
    true t (P.map string_of_int t));
  let total = P.fold_left ( + ) 0 t in check "fold" (total = 499500);
  check "fold_right order" (P.fold_right (fun x xs -> x :: xs) t [] = Array.to_list a);
  let calls = ref 0 in
  let unchanged = P.smartmap (fun x -> incr calls; x) t in
  check "smartmap sharing" (unchanged == t && !calls = 1000);
  let count, mapped = P.fold_map (fun i x -> check "foldmap order" (i=x); i+1, x+1) 0 t in
  check "foldmap count" (count=1000);
  compare "foldmap values" mapped (Array.map succ a);
  check "empty for_all" (P.for_all (fun _ -> false) P.empty);
  check "exists" (P.exists ((=) 800) t)

let chunk_tests () =
  let a = Array.init 1000 Fun.id in
  let t = C.of_arrays [a] in
  let u = C.of_arrays [Array.sub a 0 7; Array.sub a 7 113; Array.sub a 120 880] in
  check "empty serialized chunks" (C.is_empty [ [||]; [||] ]);
  check "empty chunk comparison" (C.equal_norefl (=) [ [||]; [||] ] C.empty);
  check "noncanonical serialized chunks" (C.equal_norefl (=) ([||] :: a :: [ [||] ]) t);
  check "noncanonical chunk hash" (C.hash Fun.id ([||] :: a :: [ [||] ]) = C.hash Fun.id t);
  check "noncanonical chunk length" (W.equal (C.length ([||] :: a :: [ [||] ])) (size 1000));
  check "float chunks" (C.equal_norefl Float.equal (C.of_arrays [ [|1.5; 2.5|] ])
    (C.of_arrays [ [|1.5|]; [||]; [|2.5|] ]));
  check "chunk equality" (C.equal_norefl (=) t u);
  check "chunk compare" (C.compare Int.compare t u = 0);
  check "chunk hash" (C.hash Fun.id t = C.hash Fun.id u);
  let calls = ref 0 in
  check "no physical skip" (C.equal_norefl (fun x y -> incr calls; x=y) t t && !calls=1000);
  check "nonreflexive callback" (not (C.equal_norefl (fun _ _ -> false) t t));
  check "chunk smartmap" (C.smartmap Fun.id t == t);
  check "chunk fold2" (C.fold_left2 (fun s x y -> s+x-y) 3 t u = 3);
  let malformed = try ignore (C.fold_left2 (fun _ _ _ -> failwith "called before length check")
    () t C.empty); false with Invalid_argument _ -> true in
  check "chunk length mismatch" malformed;
  check "chunk equality length before callbacks"
    (not (C.equal_norefl (fun _ _ -> failwith "compared unequal lengths") t C.empty));
  a.(0) <- 12345;
  check "chunk input copy" ((List.hd (C.to_arrays t)).(0) = 0)

let () =
  boundary_tests (); random_tests (); large_lengths (); traversal_tests (); chunk_tests ();
  let big = P.repeat (size 4194431) 19 in
  check "beyond old limit" (P.get big (size 4194430) = Some 19);
  check "beyond old length" (W.equal (P.length big) (size 4194431));
  Printf.printf "Passed %d runtime checks (10,000 randomized persistent operations).\n%!" !checks
