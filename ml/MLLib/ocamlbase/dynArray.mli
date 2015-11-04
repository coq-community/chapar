(** Dynamic arrays.

    The [DynArray] module provides arrays that automatically change their size
    as necessary.  The resizing behavior of dynamic arrays can be adapted
    through customized resizer functions, as described below.

    The interface of this module is similar to the interface of the [Array]
    module in the OCaml standard library, but some functions ({!append}, for
    example) have been changed to modify their argument in-place instead of
    returning a new copy. *)

type 'a t
(** The type of resizable arrays with elements of type ['a]. *)

val length: 'a t -> int
(** Returns the length of an array. *)

val get: 'a t -> int -> 'a
(** [get a i] returns the element with index [i] of [a].  The first element
    has index 0.

    @raise Invalid_argument if [i] is not a valid index of [a]. *)

val set: 'a t -> int -> 'a -> unit
(** [set a i x] replaces the element with index [i] of [a] by the value [x].
    This function {e cannot} be used to extend an array.

    @raise Invalid_argument if [i] is not a valid index of [a]. *)

(** {2 Array construction} *)

val make: int -> 'a -> 'a t
(** [make n x] returns a new dynamic array of length [n] that is initialized
    with [n] copies of [x].

    @raise Invalid_argument if [n] < 0 or if [n] > [Sys.max_array_length]. *)

val init: int -> (int -> 'a) -> 'a t
(** [init n f] returns a new dynamic array of length [n] where the element
    with index [i] is equal to [f i].

    @raise Invalid_argument if [n] < 0 or if [n] > [Sys.max_array_length]. *)

val sub: 'a t -> int -> int -> 'a t
(** [sub a i n] returns a new dynamic array containing the elements with
    indices [i], ..., [i + n - 1] of [a].

    @raise Invalid_argument if [i] and [n] do not specify a valid subarray of
    [a]. *)

val copy: 'a t -> 'a t
(** [copy a] returns a new dynamic array containing the same elements as
    [a]. *)

(** {2 Array modification with automatic resizing} *)

val add: 'a t -> 'a -> unit
(** [add a x] adds [x] to the end of [a].  The array is automatically
    resized. *)

val insert: 'a t -> int -> 'a -> unit
(** [insert a x i] inserts [x] into the array [a] at index [i].  The array is
    automatically resized.

    @raise Invalid_argument if [i] is not a valid insertion index of [a].
    Valid insertion indices are [0 .. length a]. *)

val insert_range: 'a t -> int -> 'a t -> int -> int -> unit
(** [insert_range a1 i1 a2 i2 n] inserts the subarray [sub a2 i2 n] into the
    array [a1] at index [i1].  The array [a1] is automatically resized.

    @raise Invalid_argument if [i1] and [n] do not specify a valid subarray of
    [a1] or if [i2] is not a valid insertion index of [a2]. *)

val remove: 'a t -> int -> unit
(** [remove a i] removes the element with index [i] from [a].  The array is
    automatically resized.

    @raise Invalid_argument if [i] and [n] do not specify a valid subarray of
    [a]. *)

val remove_last: 'a t -> unit
(** [remove_last a] removes the element with index [length a - 1] from [a].
    The array is automatically resized. *)

val remove_range: 'a t -> int -> int -> unit
(** [remove_range a i n] removes the elements with indices [i], ..., [i + n -
    1] from [a].  The array is automatically resized.

    @raise Invalid_argument if [i] and [n] do not specify a valid subarray of
    [a]. *)

val remove_all: 'a t -> unit
(** [remove_all a] removes all elements from [a].  The array is automatically
    resized. *)

val clear: 'a t -> unit
(** [clear a] removes all elements from [a].  The array is automatically
    resized (same as [remove_all]). *)

val append: 'a t -> 'a t -> unit
(** [append a b] appends the elements of [a] to the end of [b].  The array
    [b] is automatically resized.  *)

(** {2 Array modification without automatic resizing} *)

val fill: 'a t -> int -> int -> 'a -> unit
(** [fill a i n x] replaces the elements of the array [a] with indices [i],
    ..., [i + n - 1] by [n] copies of the value [x].  This function {e cannot}
    be used to extend an array.

    @raise Invalid_argument if [i] and [n] do not specify a valid subarray of
    [a]. *)

val blit: 'a t -> int -> 'a t -> int -> int -> unit
(** [blit a i b j n] replaces [n] elements of array [b] starting at index [j]
    by [n] elements of array [a] starting at index [i].

    @raise Invalid_argument if [i] and [n] do not specify a valid subarray of
    [a] or [j] and [n] do not specify a valid subarray of [b]. *)

(** {2 Iterators} *)

val iter: ('a -> unit) -> 'a t -> unit
(** [iter f a] applies the function [f] successively to all elements of [a].
    It is equal to [f a1; ..., f an)], where [a1], ..., [an] are the elements
    of the array [a]. *)

val rev_iter: ('a -> unit) -> 'a t -> unit
(** [rev_iter f a] applies the function [f] successively to all elements of
    [a] in reverse direction.  It is equal to [f an; ..., f a1)], where [a1],
    ..., [an] are the elements of the array [a]. *)

val iteri: (int -> 'a -> unit) -> 'a t -> unit
(** [iteri f a] applies the function [f] successively to all elements of [a]
    and their indices.  It is equal to [f 0 a1; ..., f (n - 1) an)], where
    [a1], ..., [an] are the elements of the array [a]. *)

val rev_iteri: (int -> 'a -> unit) -> 'a t -> unit
(** [rev_iteri f a] applies the function [f] successively to all elements of
    [a] in reverse direction and their indices.  It is equal to [f (n - 1) an;
    ..., f 0 a1)], where [a1], ..., [an] are the elements of the array [a]. *)

val fold_left: ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
(** [fold_left f x a] returns [f (... (f (f x a1) a2) ...) an], where [a1],
    ..., [an] are the elements of [a]. *)

val fold_right: ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
(** [fold_right f a x] returns [f a1 (f a2 (... (f an x) ...))], where [a1],
    ..., [an] are the elements of [a]. *)

val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b t -> 'c t -> 'a
(** [fold_left2 f x a b] returns [f ( ... (f (f x a1 b1) a2 b2) ... ) an bn],
    where [a1], ..., [an] are the elements of [a], and [b1], ..., [bn] are the
    elements of [b].

    @raise Invalid_argument if the two arrays have different lengths. *)

val fold_right2 : ('a -> 'b -> 'c -> 'c) -> 'a t -> 'b t -> 'c -> 'c
(** [fold_right2 f a b x] returns [f a1 b1 (f a2 b2 ( ... (f an bn x) ... ))],
    where [a1], ..., [an] are the elements of [a], and [b1], ..., [bn] are the
    elements of [b].

    @raise Invalid_argument if the two arrays have different lengths. *)

val map: ('a -> 'b) -> 'a t -> 'b t
(** [map f a] returns an array with elements [f a1], ..., [f an], where [a1],
    ..., [an] are the elements of [a]. *)

val mapi: (int -> 'a -> 'b) -> 'a t -> 'b t
(** [mapi f a] returns an array with elements [f 0 a1], ..., [f (n - 1) an],
    where [a1], ..., [an] are the elements of [a]. *)

(** {2 Scanning} *)

val is_empty: 'a t -> bool
(** Tests whether an array is empty. *)

val for_all: ('a -> bool) -> 'a t -> bool
(** [for_all p a] returns [true] if [p x = true] for all elements [x] of the
    array [a], and [false] otherwise. *)

val exists: ('a -> bool) -> 'a t -> bool
(** [exists p a] returns [true] if [p x = true] for some element [x] of the
    array [a], and [false] otherwise. *)

val for_all2: ('a -> 'b -> bool) -> 'a t -> 'b t -> bool
(** [for_all2 p a b] returns [true] if [p x y = true] for all pairs of
    elements [x] and [y] where [x] has the same index in [a] as [y] in [b].

    @raise Invalid_argument if [a] and [b] have different lengths. *)

val exists2: ('a -> 'b -> bool) -> 'a t -> 'b t -> bool
(** [exists2 p a b] returns [true] if [p x y = true] for some pair of elements
    [x] and [y] where [x] has the same index in [a] as [y] in [b].

    @raise Invalid_argument if [a] and [b] have different lengths. *)

(** {2 Searching} *)

val first: 'a t -> 'a option
(** [first a] returns [Some x] if [x] is the first element (the element with
    index 0) of [a], or [None] if the array is empty. *)

val last: 'a t -> 'a option
(** [last a] returns [Some x] if [x] is the last element (the element with
    index [length a - 1]) of [a], or [None] if the array is empty. *)

(** {2 Conversion} *)

val to_list: 'a t -> 'a list
(** [to_list a] returns a list containing the elements of [a]. *)

val of_list: 'a list -> 'a t
(** [of_list l] returns a dynamic array containing the elements of [l]. *)

val to_array: 'a t -> 'a array
(** [to_array a] returns a new standard OCaml array containing the same
    elements as [a]. *)

val of_array: 'a array -> 'a t
(** [of_array a] returns a new dynamic array containing the same elements as
    [a]. *)

(** {2 Resizer functions}

    A resizer is a function that computes how much space is to be reserved
    when elements are added to or removed from a dynamic array.  When a
    dynamic array is created, a default resizer is assigned to it, which can
    then be changed.  When a dynamic array is copied using the functions
    [sub], [copy], or [map], the new array uses the same resizer as the
    original array.

    A resizer is called with three arguments: the current reserved size of the
    array, the number of elements of the array before the modification, and
    the number of elements of the array after the modification. *)

type resizer = curr_size:int -> old_length:int -> new_length:int -> int
(** The type of resizer functions. *)

val doubling_resizer_with_shrinking: resizer
(** A resizer that grows and shrinks an array by doubling or halving the size
    of the array as necessary. *)

val doubling_resizer_without_shrinking: resizer
(** A resizer that grows an array by doubling the size of the array as
    necessary.  It never shrinks the array, which is not a problem in many use
    cases.  This is currently the default resizer. *)

val set_resizer: 'a t -> resizer -> unit
(** Sets the resizer function of an array. *)

val set_default_resizer: resizer -> unit
(** Sets the default resizer function.  *)

(**/**)

val unsafe_get: 'a t -> int -> 'a

val unsafe_set: 'a t -> int -> 'a -> unit
