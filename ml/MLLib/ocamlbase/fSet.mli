(** Finite sets.

    The [FSet] module provides a purely functional finite set datastructure
    based on balanced binary trees.  Most operations on single elements, for
    example inserting elements or testing membership, can be performed in time
    logarithmic in the size of the set.

    This module provides a superset of the operations in the [Set] module in
    the OCaml standard library, but with a polymorphic interface in addition
    to the standard functorial interface.

    A set provided by this module requires a strict order on its set elements.
    When using the polymorphic interface, set elements are compared using the
    structural comparison operators [(=)] and [(<)].  For this reason, the
    polymorphic interface can only be used if semantic equality in the element
    type is equivalent to structural equality.  This is {e not} the case for
    ['a FSet.t] itself, which means that the polymorphic interface cannot be
    used for creating sets of sets. *)

type +'a t
(** The type of finite sets over type ['a]. *)

val size: 'a t -> int
(** Returns the number of elements in a set. *)

val cardinal: 'a t -> int
(** Returns the number of elements in a set (same as [size]). *)

(** {2 Set comparison} *)

val equal: 'a t -> 'a t -> bool
(** Tests whether two sets contain the same elements. *)

val compare: 'a t -> 'a t -> int
(** Defines a total ordering on sets. *)

val subset: 'a t -> 'a t -> bool
(** [subset s1 s2] tests whether [s1] is a subset of the set [s2]. *)

(** {2 Set construction} *)

val empty: 'a t
(** The empty set. *)

val singleton: 'a -> 'a t
(** [singleton x] returns the one-element set containing only [x]. *)

val add: 'a -> 'a t -> 'a t
(** [add x s] returns the union of the set [s] and the one-element set
    containing only [x]. *)

val remove: 'a -> 'a t -> 'a t
(** [remove x s] returns the difference of the set [s] and the set containing
    only [x]. *)

val union: 'a t -> 'a t -> 'a t
(** [union s1 s2] returns the union of the sets [s1] and [s2]. *)

val inter: 'a t -> 'a t -> 'a t
(** [inter s1 s2] returns the intersection of the sets [s1] and [s2]. *)

val diff: 'a t -> 'a t -> 'a t
(** [diff s1 s2] returns the difference of the sets [s1] and [s2]. *)

(** {2 Iterators} *)

val iter: ('a -> unit) -> 'a t -> unit
(** [iter f s] applies [f] to all elements of the set [s].  The elements of
    [s] are processed in increasing order. *)

val rev_iter: ('a -> unit) -> 'a t -> unit
(** [rev_iter f s] applies [f] to all elements of the set [s].  The elements
    of [s] are processed in decreasing order. *)

val fold: ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
(** [fold f s a] returns [(f an ... (f a2 (f a1 a)) ... )], where [a1], ...,
    [an] are the elements of [s] in increasing order. *)

val rev_fold: ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
(** [rev_fold f s a] returns [(f a1 ... (f a(n-1) (f an a)) ... )], where
    [a1], ..., [an] are the elements of [s] in increasing order. *)

val map: ('a -> 'b) -> 'a t -> 'b t
(** [map f s] returns a set with elements [f a1], ... [f an], where [a1], ...,
    [an] are the elements of the set [s]. *)

(** {2 Filters} *)

val filter: ('a -> bool) -> 'a t -> 'a t
(** [filter p s] returns a set containing all elements of the set [s] that
    satisfy the predicate [p]. *)

val partition: ('a -> bool) -> 'a t -> 'a t * 'a t
(** [partition p s] returns a pair [(s1, s2)] of sets, such that [s1] contains
    the elements of [s] that satisfy the predicate [p], and [s2] contains
    the elements of [s] that do not satisfy the predicate [p]. *)

val split: 'a -> 'a t -> 'a t * bool * 'a t
(** [split x s] returns a triple [(l, present, r)], where [l] is the set of
    elements of [s] that are strictly less than [x], [r] is the set of
    elements of [s] that are strictly greater than [x], and [present] is
    [true] if [s] contains an element equal to [x] and [false] otherwise. *)

(** {2 Scanning} *)

val is_empty: 'a t -> bool
(** Tests whether a set is empty. *)

val for_all: ('a -> bool) -> 'a t -> bool
(** [for_all p s] returns [true] if [p a = true] for all elements [a] of the
    set [s], and [false] otherwise. *)

val exists: ('a -> bool) -> 'a t -> bool
(** [for_all p s] returns true if [p a = true] for some element [a] of the set
    [s], and [false] otherwise. *)

(** {2 Searching} *)

val mem: 'a -> 'a t -> bool
(** [mem x s] test whether the set [s] contains the element [x]. *)

val choose: 'a t -> 'a
(** Returns an element of a set.  It is unspecified how the element is chosen,
    but equal elements will be chosen for equal sets. *)

val min_elt: 'a t -> 'a option
(** [min_elt s] returns [Some x] if [x] is the minimum element of [s], or
    [None] if [s] is empty. *)

val max_elt: 'a t -> 'a option
(** [max_elt s] returns [Some x] if [x] is the maximum element of [s], or
    [None] if [s] is empty. *)

(** {2 Conversion} *)

val to_list: 'a t -> 'a list
(** Returns a list containing the elements of a set in increasing order. *)

val of_list: 'a list -> 'a t
(** Returns a set containing the elements of a list. *)

val elements: 'a t -> 'a list
(** Returns a list containing the elements of a set in increasing order (same
    as [to_list]). *)

(** Input signature of the functor {!FSet.Make}. *)
module type OrderedType =
sig
  type t
  (** The type of set elements. *)

  val compare : t -> t -> int
  (** A function defining a total ordering on the type [t].  [compare x y]
      must be negative if [x] is smaller than [y], positive if [x] is greater
      than [x], and zero if [x] and [y] are equal. *)
end

(** Output signature of the functor {!FSet.Make}. *)
module type S =
sig
  type elt
  (** The element type. *)

  type t
  (** The type of finite sets over type [elt]. *)

  val size: t -> int
  (** Returns the number of elements in a set. *)

  val cardinal: t -> int
  (** Returns the number of elements in a set (same as [size]). *)

  (** {2 Set comparison} *)

  val equal: t -> t -> bool
  (** Tests whether two sets contain the same elements. *)

  val compare: t -> t -> int
  (** Defines a total ordering on sets. *)

  val subset: t -> t -> bool
  (** [subset s1 s2] tests whether [s1] is a subset of the set [s2]. *)

  (** {2 Set construction} *)

  val empty: t
  (** The empty set. *)

  val singleton: elt -> t
  (** [singleton x] returns the one-element set containing only [x]. *)

  val add: elt -> t -> t
  (** [add x s] returns the union of the set [s] and the one-element set
      containing only [x]. *)

  val remove: elt -> t -> t
  (** [remove x s] returns the difference of the set [s] and the set
      containing only [x]. *)

  val union: t -> t -> t
  (** [union s1 s2] returns the union of the sets [s1] and [s2]. *)

  val inter: t -> t -> t
  (** [inter s1 s2] returns the intersection of the sets [s1] and [s2]. *)

  val diff: t -> t -> t
  (** [diff s1 s2] returns the difference of the sets [s1] and [s2]. *)

  (** {2 Iterators} *)

  val iter: (elt -> unit) -> t -> unit
  (** [iter f s] applies [f] to all elements of the set [s].  The elements of
      [s] are processed in increasing order. *)

  val rev_iter: (elt -> unit) -> t -> unit
  (** [rev_iter f s] applies [f] to all elements of the set [s].  The elements
      of [s] are processed in decreasing order. *)

  val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
  (** [fold f s a] returns [(f an ... (f a2 (f a1 a)) ... )], where [a1], ...,
      [an] are the elements of [s] in increasing order. *)

  val rev_fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
  (** [rev_fold f s a] returns [(f a1 ... (f a(n-1) (f an a)) ... )], where
      [a1], ..., [an] are the elements of [s] in increasing order. *)

  val map: (elt -> elt) -> t -> t
  (** [map f s] returns a set with elements [f a1], ... [f an], where [a1],
      ..., [an] are the elements of the set [s]. *)

  (** {2 Filters} *)

  val filter: (elt -> bool) -> t -> t
  (** [filter p s] returns a set containing all elements of the set [s] that
      satisfy the predicate [p]. *)

  val partition: (elt -> bool) -> t -> t * t
  (** [partition p s] returns a pair [(s1, s2)] of sets, such that [s1]
      contains the elements of [s] that satisfy the predicate [p], and [s2]
      contains the elements of [s] that do not satisfy the predicate [p]. *)

  val split: elt -> t -> t * bool * t
  (** [split x s] returns a triple [(l, present, r)], where [l] is the set of
      elements of [s] that are strictly less than [x], [r] is the set of
      elements of [s] that are strictly greater than [x], and [present] is
      [true] if [s] contains an element equal to [x] and [false] otherwise. *)

  (** {2 Scanning} *)

  val is_empty: t -> bool
  (** Tests whether a set is empty. *)

  val for_all: (elt -> bool) -> t -> bool
  (** [for_all p s] returns [true] if [p a = true] for all elements [a] of the
      set [s], and [false] otherwise. *)

  val exists: (elt -> bool) -> t -> bool
  (** [for_all p s] returns true if [p a = true] for some element [a] of the
      set [s], and [false] otherwise. *)

  (** {2 Searching} *)

  val mem: elt -> t -> bool
  (** [mem x s] test whether the set [s] contains the element [x]. *)

  val choose: t -> elt
  (** Returns an element of a set.  It is unspecified how the element is
      chosen, but equal elements will be chosen for equal sets. *)

  val min_elt: t -> elt option
  (** [min_elt s] returns [Some x] if [x] is the minimum element of [s], or
      [None] if [s] is empty. *)

  val max_elt: t -> elt option
  (** [max_elt s] returns [Some x] if [x] is the maximum element of [s], or
      [None] if [s] is empty. *)

  (** {2 Conversion} *)

  val to_list: t -> elt list
  (** Returns a list containing the elements of a set in increasing order. *)

  val of_list: elt list -> t
  (** Returns a set containing the elements of a list. *)

  val elements: t -> elt list
  (** Returns a list containing the elements of a set in increasing order
      (same as [to_list]). *)

end

(** Functor returning a finite set module over a totally ordered type. *)
module Make (Ord: OrderedType): S with type elt = Ord.t
