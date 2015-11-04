(** Finite maps.

    The [FMap] module provides a purely functional finite map datastructure
    based on balanced binary trees.  Most operations on single elements, for
    example adding bindings or testing membership, can be performed in time
    logarithmic in the size of the map.

    This module provides a superset of the operations in the [Map] module in
    the OCaml standard library, but with a polymorphic interface in addition
    to the standard functorial interface.

    A map provided by this module requires a strict order on its domain
    elements.  When using the polymorphic interface, domain elements are
    compared using the structural comparison operators [(=)] and [(<)].  For
    this reason, the polymorphic interface can only be used if semantic
    equality in the domain type is equivalent to structural equality. *)

type ('a, +'b) t
(** The type of finite maps with domain type ['a] and range type ['b].  Values
    of this type can be considered as finite sets of pairs where an element
    [(x, y)] represents the mapping of [x] to [y].  The domain of a map [m] is
    the set of values [x] such that [m] contains a pair [(x, y)] for some [y]
    ([m] maps [x] to some value); the range of [m] is the set of values [y]
    such that [m] contains a pair [(x, y)] for some [x] (some value is mapped
    to [y] by [m]). *)

val size: ('a, 'b) t -> int
(** Returns the size of the domain of a map. *)

(** {2 Map comparison} *)

val equal: ('b -> 'b -> bool) -> ('a, 'b) t -> ('a, 'b) t -> bool
(** [equal cmp m1 m2] tests whether the maps [m1] and [m2] are equal.  Two
    maps are equal if they have equal domains and map each domain element to
    equal values, where the values are compared using [cmp]. *)

val compare: ('b -> 'b -> int) -> ('a, 'b) t -> ('a, 'b) t -> int
(** [compare cmp] returns a total ordering on maps using [cmp] to compare
    values. *)

(** {2 Map construction} *)

val empty: ('a, 'b) t
(** The empty map. *)

val add: 'a -> 'b -> ('a, 'b) t -> ('a, 'b) t
(** [add x y m] returns a map that maps [x] to [y] and all other elements to
    the values they are mapped to by [m]. *)

val remove: 'a -> ('a, 'b) t -> ('a, 'b) t
(** [remove x m] returns a map that is undefined at [x] and maps all other
    elements to the values they are mapped to by [m]. *)

(** {2 Iterators} *)

val iter: ('a -> 'b -> unit) -> ('a, 'b) t -> unit
(** [iter f m] applies [f] to all pairs [x] and [y], where [(x, y)] is an
    element of [m].  The elements of [m] are processed in increasing domain
    order. *)

val fold: ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
(** [fold f m a] returns [(f xn yn ... (f x2 y2 (f x1 y1 a)) ... )], where
    [(x1, y1)], ..., [(xn, yn)] are the elements of [m] in increasing domain
    order. *)

val rev_fold: ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
(** [fold f m a] returns [(f x1 y1 (f x2 y2 ... (f xn yn a)) ... )], where
    [(x1, y1)], ..., [(xn, yn)] are the elements of [m] in increasing domain
    order. *)

val map: ('b -> 'c) -> ('a, 'b) t -> ('a, 'c) t
(** [map f m] returns a map that has the same domain as [m] and maps all
    elements [x] in its domain to [f (find x m)]. *)

val mapi: ('a -> 'b -> 'c) -> ('a, 'b) t -> ('a, 'c) t
(** [mapi f m] returns a map that has the same domain as [m] and maps all
    elements [x] in its domain to [f x (find x m)]. *)

(** {2 Scanning} *)

val is_empty: ('a, 'b) t -> bool
(** Tests whether a map has an empty domain. *)

val for_all: ('a -> 'b -> bool) -> ('a, 'b) t -> bool
(** [for_all p m] returns [true] if [p x y = true] for all elements [(x, y)]
    of [m], and [false] otherwise. *)

val exists: ('a -> 'b -> bool) -> ('a, 'b) t -> bool
(** [for_all p m] returns [true] if [p x y = true] some element [(x, y)] of
    [m], and [false] otherwise. *)

(** {2 Searching} *)

val mem: 'a -> ('a, 'b) t -> bool
(** [mem x m] tests whether [m] is defined at [x]. *)

val is_defined: 'a -> ('a, 'b) t -> bool
(** [is_defined x m] tests whether [m] is defined at [x] (the same as
    [mem]). *)

val find: 'a -> ('a, 'b) t -> 'b
(** [find x m] returns the value [x] is mapped to by [m].

    @raise Not_found if [x] is not in the domain of [m]. *)

val apply: ('a, 'b) t -> 'a -> 'b
(** [apply m x] returns the value [x] is mapped to by [m] (the same as
    [find]).

    @raise Not_found if [x] is not in the domain of [m]. *)

(** {2 Conversion} *)

val to_list: ('a, 'b) t -> ('a * 'b) list
(** Returns an association list containing all element of the map in
    increasing order of the domain elements. *)

val of_list: ('a * 'b) list -> ('a, 'b) t
(** Creates a map from an association list. *)

(** Input signature of the functor {!FSet.Make}. *)
module type OrderedType =
sig
  type t
  (** The type of domain elements. *)

  val compare : t -> t -> int
  (** A function defining a total ordering on the type [t].  [compare x y]
      must be negative if [x] is smaller than [y], positive if [x] is greater
      than [x], and zero if [x] and [y] are equal. *)
end

(** Output signature of the functor {!FSet.Make}. *)
module type S =
sig
  type key
  (** The domain type. *)

  type 'a t
  (** The range type. *)

  val size: 'a t -> int
  (** Returns the size of the domain of a map. *)

  (** {2 Map comparison} *)

  val compare: ('a -> 'a -> int) -> 'a t -> 'a t -> int
  (** [equal cmp m1 m2] tests whether the maps [m1] and [m2] are equal.  Two
      maps are equal if they have equal domains and map each domain element to
      equal values, where the values are compared using [cmp]. *)

  val equal: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  (** [compare cmp] returns a total ordering on maps using [cmp] to compare
      values. *)

  (** {2 Map construction} *)

  val empty: 'a t
  (** The empty map. *)

  val add: key -> 'a -> 'a t -> 'a t
  (** [add x y m] returns a map that maps [x] to [y] and all other elements to
      the values they are mapped to by [m]. *)

  val remove: key -> 'a t -> 'a t
  (** [remove x m] returns a map that is undefined at [x] and maps all other
      elements to the values they are mapped to by [m]. *)

  (** {2 Iterators} *)

  val iter: (key -> 'a -> unit) -> 'a t -> unit
  (** [iter f m] applies [f] to all pairs [x] and [y], where [(x, y)] is an
      element of [m].  The elements of [m] are processed in increasing domain
      order. *)

  val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  (** [fold f m a] returns [(f xn yn ... (f x2 y2 (f x1 y1 a)) ... )], where
      [(x1, y1)], ..., [(xn, yn)] are the elements of [m] in increasing domain
      order. *)

  val rev_fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  (** [fold f m a] returns [(f x1 y1 (f x2 y2 ... (f xn yn a)) ... )], where
      [(x1, y1)], ..., [(xn, yn)] are the elements of [m] in increasing domain
      order. *)

  val map: ('a -> 'b) -> 'a t -> 'b t
  (** [map f m] returns a map that has the same domain as [m] and maps all
      elements [x] in its domain to [f (find x m)]. *)

  val mapi: (key -> 'a -> 'b) -> 'a t -> 'b t
  (** [mapi f m] returns a map that has the same domain as [m] and maps all
      elements [x] in its domain to [f x (find x m)]. *)

  (** {2 Scanning} *)

  val is_empty: 'a t -> bool
  (** Tests whether a map has an empty domain. *)

  val for_all: (key -> 'a -> bool) -> 'a t -> bool
  (** [for_all p m] returns [true] if [p x y = true] for all elements [(x, y)]
      of [m], and [false] otherwise. *)

  val exists: (key -> 'a -> bool) -> 'a t -> bool
  (** [for_all p m] returns [true] if [p x y = true] some element [(x, y)] of
      [m], and [false] otherwise. *)

  (** {2 Searching} *)

  val mem: key -> 'a t -> bool
  (** [mem x m] tests whether [m] is defined at [x]. *)

  val is_defined: key -> 'a t -> bool
  (** [is_defined x m] tests whether [m] is defined at [x] (the same as
      [mem]). *)

  val find: key -> 'a t -> 'a
  (** [find x m] returns the value [x] is mapped to by [m].

      @raise Not_found if [x] is not in the domain of [m]. *)

  val apply: 'a t -> key -> 'a
  (** [apply m x] returns the value [x] is mapped to by [m] (the same as
      [find]).

      @raise Not_found if [x] is not in the domain of [m]. *)

  (** {2 Conversion} *)

  val to_list: 'a t -> (key * 'a) list
  (** Returns an association list containing all element of the map in
      increasing order of the domain elements. *)

  val of_list: (key * 'a) list -> 'a t
  (** Creates a map from an association list. *)

end

module Make (Ord: OrderedType): S with type key = Ord.t
