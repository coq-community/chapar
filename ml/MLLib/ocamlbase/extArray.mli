(** Extended [Array] module.

    The [ExtArray] module contains an extension of the [Array] module in the
    OCaml standard library. *)

(** Extended [Array] module. *)
module Array:
sig

  val swap: 'a array -> int -> int -> unit
  (** [swap a i j] swaps the elements of [a] at indices [i] and [j].

      @raise Invalid_argument if one of [i] and [j] is not a valid index. *)

  val lexicographic_compare: ('a -> 'b -> int) -> 'a array -> 'b array -> int
  (** [lexicographic_compare cmp a1 a2] compares the arrays [a1] and [a2]
      lexicographically using the element order [cmp].  It returns a
      negative value if [a1] is less than [a2], a positive value if [a1] is
      greater than [a2], and 0 if [a1] equals [a2] (wrt. the element order
      [cmp]).  *)

(** {2 Iterators} *)

  val rev_iter : ('a -> unit) -> 'a array -> unit
  (** [rev_iter f a] applies the function [f] successively to the elements of
      [a] in reverse direction.  It is equal to [f a.(length a - 1); ...; f
      a.(0)]. *)

  val rev_iteri : (int -> 'a -> unit) -> 'a array -> unit
  (** [rev_iter f a] applies the function [f] successively to the elements of
      [a] in reverse direction and their indices.  It is equal to [f (length
      a - 1) a.(length a - 1); ...; f 0 a.(0)]. *)

  val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b array -> 'c array -> 'a
  (** [fold_left2 f a \[|b1; ...; bn|\] \[|c1; ...; cn|\]] returns [f ( ... (f
      (f a b1 c1) b2 c2) ... ) bn cn].

      @raise Invalid_argument if the two arrays have different lengths. *)

  val fold_right2 : ('a -> 'b -> 'c -> 'c) -> 'a array -> 'b array -> 'c -> 'c
  (** [fold_right2 f \[|a1; ...; an|\] \[|b1; ...; bn|\] c] returns [f a1 b1
      (f a2 b2 ( ... (f an bn c) ... ))].

      @raise Invalid_argument if the two arrays have different lengths. *)

  (** {2 Scanning} *)

  val for_all: ('a -> bool) -> 'a array -> bool
  (** [for_all p \[a1; ...; an\]] returns [true] if [p ai = true] for all [i],
      and [false] otherwise. *)

  val exists: ('a -> bool) -> 'a array -> bool
  (** [exists p \[a1; ...; an\]] returns [true] if [p ai = true] for some [i],
      and [false] otherwise. *)

  val for_all2: ('a -> 'b -> bool) -> 'a array -> 'b array -> bool
  (** [for_all2 p \[a1; ...; an\] \[b1; ...; bn\]] returns [true] if [p ai bi
      = true] for all [i], and [false] otherwise. *)

  val exists2: ('a -> 'b -> bool) -> 'a array -> 'b array -> bool
  (** [exists2 p \[a1; ...; an\] \[b1; ...; bn\]] returns [true] if [p ai bi =
      true] for some [i], and [false] otherwise. *)

  (** {2 From the OCaml standard library}

      The following definitions are unmodified from the OCaml standard
      library.  See the OCaml manual for documentation. *)

  external length : 'a array -> int = "%array_length"

  external get : 'a array -> int -> 'a = "%array_safe_get"

  external set : 'a array -> int -> 'a -> unit = "%array_safe_set"

  external make : int -> 'a -> 'a array = "caml_make_vect"

  external create : int -> 'a -> 'a array = "caml_make_vect"

  val init : int -> (int -> 'a) -> 'a array

  val make_matrix : int -> int -> 'a -> 'a array array

  val create_matrix : int -> int -> 'a -> 'a array array

  val append : 'a array -> 'a array -> 'a array

  val concat : 'a array list -> 'a array

  val sub : 'a array -> int -> int -> 'a array

  val copy : 'a array -> 'a array

  val fill : 'a array -> int -> int -> 'a -> unit

  val blit : 'a array -> int -> 'a array -> int -> int -> unit

  val to_list : 'a array -> 'a list

  val of_list : 'a list -> 'a array

  val iter : ('a -> unit) -> 'a array -> unit

  val map : ('a -> 'b) -> 'a array -> 'b array

  val iteri : (int -> 'a -> unit) -> 'a array -> unit

  val mapi : (int -> 'a -> 'b) -> 'a array -> 'b array

  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b array -> 'a

  val fold_right : ('b -> 'a -> 'a) -> 'b array -> 'a -> 'a

  val sort : ('a -> 'a -> int) -> 'a array -> unit

  val stable_sort : ('a -> 'a -> int) -> 'a array -> unit

  val fast_sort : ('a -> 'a -> int) -> 'a array -> unit

  (**/**)

  external unsafe_get : 'a array -> int -> 'a = "%array_unsafe_get"

  external unsafe_set : 'a array -> int -> 'a -> unit = "%array_unsafe_set"

end
