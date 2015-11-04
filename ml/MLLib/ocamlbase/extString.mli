(** Extended [String] module.

    The [ExtString] module contains an extension of the [String] module in the
    OCaml standard library. *)

(** Extended [String] module. *)
module String:
sig

  val concat_conj: string -> string -> string list -> string
  (** [concat_conj sep conj strings] concatenates the elements of [strings]
      using the separator [sep] and the conjunction [conj] according to the
      rules of the English language.  For example, [concat_conj "," "and"
      \["A"; "B"; "C"\]] results in the string ["A, B, and C"]. *)

  val explode: string -> char list
  (** [explode s] returns a list with the characters of the string [s]. *)

  val collect: char list -> string
  (** [collect l] returns a string with the characters in the list [l]. *)

  (** {2 Iterators} *)

  val fold_left: ('a -> char -> 'a) -> 'a -> string -> 'a
  (** [fold_left f a s] returns [f (... (f (f a c1) c2) ...) cn], where [c1],
      ..., [cn] are the characters of [s]. *)

  val fold_right: (char -> 'a -> 'a) -> string -> 'a -> 'a
  (** [fold_right f s a] returns [f c1 (f c2 (... (f cn a) ...))], where [c1],
      ..., [cn] are the characters of [s]. *)

  val rev_iter: (char -> unit) -> string -> unit
  (** [rev_iter f s] applies the function [f] successively to all characters
      of [s] in reverse direction.  It is equivalent to [f s.\[length s -
      1\]; ...; f s.\[1\]; f s.\[0\]; ()]. *)

  val iteri: (int -> char -> unit) -> string -> unit
  (** [iteri f s] applies the function [f] successively to all characters of
      [s] and their indices.  It is equal to [f 0 c1; ..., f (n - 1) cn)],
      where [c1], ..., [cn] are the characters of the string [s]. *)

  val rev_iteri: (int -> char -> unit) -> string -> unit
  (** [rev_iteri f s] applies the function [f] successively to all characters
      in reverse direction of [s] and their indices.  It is equal to [f (n -
      1) cn; ..., f 0 c1)], where [c1], ..., [cn] are the characters of the
      string [s]. *)

  (** {2 Scanning} *)

  val for_all: (char -> bool) -> string -> bool
  (** [for_all p s] returns [true] if [p c = true] for all characters [c] of
      [s], and [false] otherwise. *)

  val exists: (char -> bool) -> string -> bool
  (** [exists p s] returns [true] if [p c = true] for some character [c] of
      [s], and [false] otherwise. *)

  val any_index_from: string -> int -> char list -> int option
  (** [any_index_from s start chars] returns [Some i] where [i] is the index
      of the first occurrence of a character in [chars] in the string [s]
      starting at [start], or [None] if no character from [chars] occurs in
      [s] starting at [start]. *)

  (** {2 Matching} *)

  val match_sub: string -> int -> string -> bool
  (** [match_sub s start pat] returns [true] if the string [s] contains the
      string [pat] as a substring starting at position [start], and [false]
      otherwise.

      @raise Invalid_argument if [start] is no valid index in [s]. *)

  val match_sub2: string -> int -> string -> int -> int -> bool
  (** [match_sub2 s1 start1 s2 start2 len] returns [true] if [sub s1 start1
      len = sub s2 start2 len], and [false] otherwise.

      @raise Invalid_argument if [start1], [start2], and [len] do not specify
      valid substrings of [s1] and [s2]. *)

  (** {2 From the OCaml standard library}

      The following definitions are unmodified from the OCaml standard
      library.  See the OCaml manual for documentation. *)

  type t = string

  val compare : t -> t -> int

  external length : string -> int = "%string_length"

  external get : string -> int -> char = "%string_safe_get"

  external set : string -> int -> char -> unit = "%string_safe_set"

  external create : int -> string = "caml_create_string"

  val make : int -> char -> string

  val copy : string -> string

  val sub : string -> int -> int -> string

  val fill : string -> int -> int -> char -> unit

  val blit : string -> int -> string -> int -> int -> unit

  val concat : string -> string list -> string

  val iter : (char -> unit) -> string -> unit

  val escaped : string -> string

  val index : string -> char -> int

  val rindex : string -> char -> int

  val index_from : string -> int -> char -> int

  val rindex_from : string -> int -> char -> int

  val contains : string -> char -> bool

  val contains_from : string -> int -> char -> bool

  val rcontains_from : string -> int -> char -> bool

  val uppercase : string -> string

  val lowercase : string -> string

  val capitalize : string -> string

  val uncapitalize : string -> string

  (**/**)

  external unsafe_get : string -> int -> char = "%string_unsafe_get"

  external unsafe_set : string -> int -> char -> unit = "%string_unsafe_set"

  external unsafe_blit : string -> int -> string -> int -> int -> unit = "caml_blit_string" "noalloc"

  external unsafe_fill : string -> int -> int -> char -> unit = "caml_fill_string" "noalloc"

end
