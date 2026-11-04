(************************************************************************)
(* Native persistent arrays with unsigned 64-bit lengths.                *)
(* Distributed under the GNU Lesser General Public License Version 2.1. *)
(************************************************************************)

type 'a t
type size = Primitive_words_runtime.Word64.t

val empty : 'a t
val is_empty : 'a t -> bool
val length : 'a t -> size

(** Every element slot is allocated eagerly. Resource failures propagate;
    they never truncate the array or become a logical bounds failure. *)
val make : size -> 'a -> 'a t
val repeat : size -> 'a -> 'a t
val get : 'a t -> size -> 'a option
val set : 'a t -> size -> 'a -> 'a t option
val slice : 'a t -> size -> size -> 'a t option
val replace : 'a t -> size -> 'a t -> 'a t option
val concat : 'a t -> 'a t -> 'a t option

(** Input arrays are copied. Output arrays are fresh copies. No flat array
    proportional to the total length is allocated by chunk conversion. *)
val of_array : 'a array -> 'a t
val of_chunks : 'a array list -> 'a t
val to_chunks : 'a t -> 'a array list

val iter : ('a -> unit) -> 'a t -> unit
val exists : ('a -> bool) -> 'a t -> bool
val for_all : ('a -> bool) -> 'a t -> bool
val map : ('a -> 'b) -> 'a t -> 'b t
val smartmap : ('a -> 'a) -> 'a t -> 'a t
val fold_map : ('s -> 'a -> 's * 'b) -> 's -> 'a t -> 's * 'b t
val fold_left : ('s -> 'a -> 's) -> 's -> 'a t -> 's
val fold_right : ('a -> 's -> 's) -> 'a t -> 's -> 's
(** Raises [Invalid_argument] on unequal lengths. The callback is called
    for every pair, including physically equal values and shared subtrees. *)
val fold_left2 : ('s -> 'a -> 'b -> 's) -> 's -> 'a t -> 'b t -> 's
