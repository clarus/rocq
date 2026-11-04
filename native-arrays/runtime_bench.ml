module W = Primitive_words_runtime.Word64
let size n = W.of_int64 (Int64.of_int n)

module type SEQUENCE = sig
  type t
  val name : string
  val make : int -> int -> t
  val get : t -> int -> int
  val set : t -> int -> int -> t
  val slice : t -> int -> int -> t
  val replace : t -> int -> t -> t
  val concat : t -> t -> t
end

module type ROPE = sig
  type 'a t
  val make : W.t -> 'a -> 'a t
  val get : 'a t -> W.t -> 'a option
  val set : 'a t -> W.t -> 'a -> 'a t option
  val slice : 'a t -> W.t -> W.t -> 'a t option
  val replace : 'a t -> W.t -> 'a t -> 'a t option
  val concat : 'a t -> 'a t -> 'a t option
end

module Adapt (P : ROPE) (N : sig val name : string end) : SEQUENCE = struct
  type t = int P.t
  let name = N.name
  let make n x = P.make (size n) x
  let get a i = Option.get (P.get a (size i))
  let set a i x = Option.get (P.set a (size i) x)
  let slice a i n = Option.get (P.slice a (size i) (size n))
  let replace a i b = Option.get (P.replace a (size i) b)
  let concat a b = Option.get (P.concat a b)
end

module Flat : SEQUENCE = struct
  type t = int Parray.t
  let name = "parray"
  let make n x = Parray.make (Uint63.of_int n) x
  let get a i = Parray.get a (Uint63.of_int i)
  let set a i x = Parray.set a (Uint63.of_int i) x
  let slice a pos n = Parray.init (Uint63.of_int n) (fun i -> get a (pos+i)) 0
  let replace a pos b =
    let a = ref a in
    (* Source and destination are distinct snapshots in these workloads. *)
    for i = 0 to Parray.length_int b - 1 do a := set !a (pos+i) (get b i) done;
    !a
  let concat a b =
    let n = Parray.length_int a and m = Parray.length_int b in
    Parray.init (Uint63.of_int (n+m)) (fun i -> if i<n then get a i else get b (i-n)) 0
end

module P32 = Adapt(Parray64_32)(struct let name = "avl32" end)
module P128 = Adapt(Parray64_128)(struct let name = "avl128" end)
module P256 = Adapt(Parray64_256)(struct let name = "avl256" end)

let measure implementation case f =
  Gc.full_major ();
  let live_before = (Gc.stat ()).live_words in
  let before = Gc.allocated_bytes () in
  let start = Unix.gettimeofday () in
  let checksum, retained = Sys.opaque_identity (f ()) in
  let seconds = Unix.gettimeofday () -. start in
  let after = Gc.allocated_bytes () in
  Gc.full_major ();
  let live_after = (Gc.stat ()).live_words in
  ignore (Sys.opaque_identity (f, retained));
  Printf.printf "{\"implementation\":\"%s\",\"case\":\"%s\",\"seconds\":%.9f,\"bytes\":%.0f,\"retained_bytes\":%d,\"checksum\":%d}\n%!"
    implementation case seconds (after -. before)
    (max 0 (live_after - live_before) * 8) checksum

let bench (module S : SEQUENCE) =
  let n = 65536 in
  let with_base case f =
    let base = S.make n 17 in
    measure S.name case (fun () -> f base)
  in
  measure S.name "repeat_65536" (fun () ->
    let checksum = ref 0 and final = ref (S.make 0 0) in
    for i = 0 to 63 do let a = S.make n i in checksum := !checksum + S.get a (n-1); final := a done;
    !checksum, [Obj.repr !final]);
  with_base "read_262144" (fun base ->
    let sum = ref 0 in
    for i = 0 to 262143 do sum := !sum + S.get base ((i * 8191) land (n-1)) done;
    !sum, []);
  with_base "update_32768" (fun base ->
    let a = ref base in
    for i = 0 to 32767 do a := S.set !a ((i * 8191) land (n-1)) i done;
    S.get !a 8191, [Obj.repr !a]);
  with_base "history_alternation_1000" (fun base ->
    let a = ref base in
    for i = 0 to 1023 do a := S.set !a i i done;
    let sum = ref 0 in
    for _ = 1 to 1000 do sum := !sum + S.get base 1023 + S.get !a 1023 done;
    !sum, [Obj.repr !a]);
  with_base "slice_replace_8192x512" (fun base ->
    let a = ref base in
    for i = 0 to 511 do
      let slice = S.slice !a ((i * 127) land 32767) 8192 in
      let slice = S.set slice 4096 i in
      a := S.replace !a 32768 slice
    done;
    S.get !a 36864, [Obj.repr !a]);
  measure S.name "concat_1024x64" (fun () ->
    let chunk = S.make 1024 3 in
    let a = ref (S.make 0 0) in
    for _ = 1 to 64 do a := S.concat !a chunk done;
    S.get !a (n-1), [Obj.repr !a]);
  with_base "fill_8192x512" (fun base ->
    let a = ref base in
    for i = 0 to 511 do a := S.replace !a 32768 (S.make 8192 i) done;
    S.get !a 32768, [Obj.repr !a])

let () =
  let implementations = [| (module Flat : SEQUENCE); (module P32 : SEQUENCE);
      (module P128 : SEQUENCE); (module P256 : SEQUENCE) |] in
  let offset = int_of_string Sys.argv.(1) mod Array.length implementations in
  for i = 0 to Array.length implementations - 1 do
    bench implementations.((i + offset) mod Array.length implementations)
  done
