(** Extended [List] module.

    The [ExtList] module contains an extension of the [List] module in the
    OCaml standard library. *)

(** Extended [List] module. *)
module List:
sig

  val cons: 'a -> 'a list -> 'a list
  (** The list constructor [::] in functional form. *)

  val singleton: 'a -> 'a list
  (** [singleton a] returns the list [\[a\]]. *)

  val lexicographic_compare: ('a -> 'b -> int) -> 'a list -> 'b list -> int
  (** [lexicographic_compare cmp l1 l2] compares the lists [l1] and [l2]
      lexicographically using the element order [cmp].  It returns a negative
      value if [l1] is less than [l2], a positive value if [l1] is greater
      than [l2], and 0 if [l1] equals [l2].  *)

  (** {2 Iterators} *)

  val fold_left1: ('a -> 'a -> 'a) -> 'a list -> 'a
  (** [fold_left1 f \[a1; ...; an\]] returns [f (... (f (f a1 a2) a3) ...)
      an)], and [fold_left1 f \[a\]] returns [a].

      @raise Failure if applied to an empty list. *)

  val fold_right1: ('a -> 'a -> 'a) -> 'a list -> 'a
  (** [fold_right1 f \[a1; ...; an\]] returns [f a1 (f a2 (... (f a(n-1) an)
      ...))], and [fold_right1 f \[a\]] returns [a].  Not tail-recursive
      (linear in the list length).

      @raise Failure if applied to an empty list. *)

  val fold_map: ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  (** [fold_map f a \[b1; ...; bn\]] returns [(an, \[c1; ...; cn\]], where [a1
      = fst (f a b1)], [a(i+1) = fst (f ai b(i+1))], [c1 = snd (f a b1)],
      and [c(i+1) = snd (f ai b(i+1))].  [fold_map f a \[\]] returns [(a,
      [])]. *)

  val iteri: (int -> 'a -> unit) -> 'a list -> unit
  (** [iteri f \[a1; ...; an\]] applies the function [f] successively to the
      elements [a1], ..., [an] and their indices.  It is equal to [f 0 a1;
      ...; f (n - 1) an]. *)

  val iter_pairs: ('a -> 'b -> unit) -> 'a list -> 'b list -> unit
  (** [iter_pairs f \[a1; ...; am\] \[b1; ...; bn\]] applies the function [f]
      successively to all elements [ai] and [bj].  It is equal to [f a1 b1;
      f a1 b2; ...; f a2 b1; f a2 b2; ...; f am bn]. *)

  (** {2 Generators} *)

  val generate: (int -> 'a) -> int -> int -> 'a list
  (** [generate f a b] returns the list [\[f a; f (a+1); ...; f b\]] if [a <=
      b], and [\[\]] if [a > b].  Not tail-recursive (linear in the range
      length). *)

  val range: int -> int -> int list
  (** [range a b] returns the list [\[a; a+1; ...; b\]] if [a <= b], and
      [\[\]] if [a > b].  Not tail-recursive (linear in the range
      length). *)

  (** {2 Filters} *)

  val remove_dup: 'a list -> 'a list
  (** Returns a list with all successive duplicate elements removed.  Not
      tail-recursive (linear in the list length). *)

  (** {2 Scanning} *)

  val for_all_pairs: ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  (** [for_all_pairs p \[a1; ...; am\] \[b1; ...; bn\]] returns [true] if [p
      ai bj = true] for all [i] and [j], and [false] otherwise. *)

  val exists_pair: ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  (** [exists_pair p \[a1; ...; am\] \[b1; ...; bn\]] returns [true] if [p ai
      bj = true] for some [i] and [j], and [false] otherwise. *)

  (** {2 Searching} *)

  val max_elt: 'a list -> 'a option
  (** [max_elt l] returns [Some x] if [x] is the maximum element of [l] with
      respect to [Pervasives.max], or [None] if [l] is empty. *)

  val min_elt: 'a list -> 'a option
  (** [min_elt l] returns [Some x] if [x] is the minimum element of [l] with
      respect to [Pervasives.min], or [None] if [l] is empty. *)

  val find2: ('a -> 'b -> bool) -> 'a list -> 'b list -> ('a * 'b)
  (** [find2 p l1 l2] returns the first pair [(a, b)] such that [a = nth l1 i]
      and [b = nth l2 i] for some index [i] and [p a b = true].

      @raise Not_found if there is no such pair of elements. *)

  (** {2 Association lists} *)

  val assoc_map: ('b -> 'c) -> ('a * 'b) list -> ('a * 'c) list
  (** [assoc_map f \[(a1, b1), ..., (an, bn)\]] applies the function [f] to
      the elements [b1, ..., bn] and returns the list [\[(a1, f b1), ...,
      (an, f bn)\]]. *)

  (** {2 Setified lists}

      A list is called setified if it is sorted with respect to the [compare]
      function from the [Pervasives] module and contains no duplicate
      elements.  A setified list can be created using the [setify] functions.
      The following functions (except [setify], of course) expect their list
      arguments to be setified and return setified lists. *)

  val setify: 'a list -> 'a list
  (** Returns a setified list, i.e., a sorted list without any duplicate
      elements.  [setify] uses constant heap space and logarithmic stack
      space. *)

  val add: 'a -> 'a list -> 'a list
  (** [add x s] returns the union of [s] and \{x\}.  [add x s] is equal to
      [union \[x\] s]. *)

  val union: 'a list -> 'a list -> 'a list
  (** [union s1 s2] returns the union of [s1] and [s2].  Not tail-recursive
      (linear in the sum of the list lengths).  *)

  val inter: 'a list -> 'a list -> 'a list
  (** [inter s1 s2] returns the intersection of [s1] and [s2].  Not
      tail-recursive (linear in the sum of the list lengths).  *)

  val diff: 'a list -> 'a list -> 'a list
  (** [diff s1 s2] returns the difference of [s1] and [s2].  Not
      tail-recursive (linear in the sum of the list lengths). *)

  val subset: 'a list -> 'a list -> bool
  (** [subset s1 s2] returns [true] if [s1] is a subset of [s2]. *)

  val proper_subset: 'a list -> 'a list -> bool
  (** [proper_subset s1 s2] returns [true] if [s1] is a proper subset of
      [s2]. *)

  val set_map: ('a -> 'b) -> 'a list -> 'b list
  (** [set_map f s] is equal to [setify (map f s)]. *)

  (** {2 From the OCaml standard library}

      The following definitions are unmodified from the OCaml standard
      library.  See the OCaml manual for documentation. *)

  val length : 'a list -> int

  val hd : 'a list -> 'a

  val tl : 'a list -> 'a list

  val nth : 'a list -> int -> 'a

  val rev : 'a list -> 'a list

  val append : 'a list -> 'a list -> 'a list

  val rev_append : 'a list -> 'a list -> 'a list

  val concat : 'a list list -> 'a list

  val flatten : 'a list list -> 'a list

  val iter : ('a -> unit) -> 'a list -> unit

  val map : ('a -> 'b) -> 'a list -> 'b list

  val rev_map : ('a -> 'b) -> 'a list -> 'b list

  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a

  val fold_right : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b

  val iter2 : ('a -> 'b -> unit) -> 'a list -> 'b list -> unit

  val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

  val rev_map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

  val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a

  val fold_right2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c

  val for_all : ('a -> bool) -> 'a list -> bool

  val exists : ('a -> bool) -> 'a list -> bool

  val for_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

  val exists2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

  val mem : 'a -> 'a list -> bool

  val memq : 'a -> 'a list -> bool

  val find: ('a -> bool) -> 'a list -> 'a

  val filter : ('a -> bool) -> 'a list -> 'a list

  val find_all : ('a -> bool) -> 'a list -> 'a list

  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list

  val assoc : 'a -> ('a * 'b) list -> 'b

  val assq : 'a -> ('a * 'b) list -> 'b

  val mem_assoc : 'a -> ('a * 'b) list -> bool

  val mem_assq : 'a -> ('a * 'b) list -> bool

  val remove_assoc : 'a -> ('a * 'b) list -> ('a * 'b) list

  val remove_assq : 'a -> ('a * 'b) list -> ('a * 'b) list

  val split : ('a * 'b) list -> 'a list * 'b list

  val combine : 'a list -> 'b list -> ('a * 'b) list

  val sort : ('a -> 'a -> int) -> 'a list -> 'a list

  val stable_sort : ('a -> 'a -> int) -> 'a list -> 'a list

  val fast_sort : ('a -> 'a -> int) -> 'a list -> 'a list

  val merge : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list

end
