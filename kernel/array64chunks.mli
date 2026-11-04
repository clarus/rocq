(************************************************************************)
(* Chunked literal payloads for native arrays with 64-bit lengths.       *)
(* Distributed under the GNU Lesser General Public License Version 2.1. *)
(************************************************************************)

(** A sequence of dense chunks, without cached metadata in serialized terms.
    Operations treat chunk boundaries as unobservable. *)
type 'a t

val empty : 'a t
val is_empty : 'a t -> bool
(** Copies and subdivides input arrays. *)
val of_arrays : 'a array list -> 'a t
(** Shared chunks: callers must never mutate these arrays. *)
val to_arrays : 'a t -> 'a array list
val length : 'a t -> Primitive_words_runtime.Word64.t
val iter : ('a -> unit) -> 'a t -> unit
val exists : ('a -> bool) -> 'a t -> bool
val for_all : ('a -> bool) -> 'a t -> bool
val map : ('a -> 'b) -> 'a t -> 'b t
val smartmap : ('a -> 'a) -> 'a t -> 'a t
val fold_map : ('s -> 'a -> 's * 'b) -> 's -> 'a t -> 's * 'b t
val fold_left : ('s -> 'a -> 's) -> 's -> 'a t -> 's
val fold_right : ('a -> 's -> 's) -> 'a t -> 's -> 's
(** Raises [Invalid_argument] on unequal lengths, before calling [f]. *)
val fold_left2 : ('s -> 'a -> 'b -> 's) -> 's -> 'a t -> 'b t -> 's
(** May shortcut physically identical payloads; [eq] must be reflexive. *)
val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
(** Never skips element comparisons based on physical equality. *)
val equal_norefl : ('a -> 'b -> bool) -> 'a t -> 'b t -> bool
val compare : ('a -> 'b -> int) -> 'a t -> 'b t -> int
val hash : ('a -> int) -> 'a t -> int
