(** Priority queues.

    The [PriorityQueue] module provides a polymorphic and a functorial
    interface to an imperative priority queue data structure.  A queue is
    implemented by embeddeding a heap in a resizable array.

    The polymorphic interface requires that the elements in a priority queue
    are distinct w.r.t. [(=)].  The functorial interface requires that the
    elements in a priority queue are distinct w.r.t. the [equal] function in
    their [HashedType] module.  Otherwise the functions based on element
    values ([mem], [remove], [reorder_up], and [reorder_down]) may not work
    correctly. *)

type 'a order = 'a -> 'a -> bool
(** The type of priority orders on ['a].  A priority order [ord] is a
    non-strict total order where [ord a b = true] means that the priority of
    [b] is not higher than the priority of [a].  When the priority of an
    element changes, the queue must be notified using the [reorder_up] or
    [reorder_down] function. *)

type 'a t
(** The type of priority queues with element type ['a]. *)

val make: 'a order -> 'a t
(** [make ord] creates a new priority queue with order [ord]. *)

val length: 'a t -> int
(** Returns the number of elements in a queue. *)

val is_empty: 'a t -> bool
(** Tests whether a queue is empty. *)

val add: 'a t -> 'a -> unit
(** Adds an elements to the queue. *)

val mem: 'a t -> 'a -> bool
(** Tests whether a queue contains a given element. *)

val first: 'a t -> 'a
(** [first q] returns an element with maximal priority contained in the queue
    [q].

    @raise Failure if [q] is empty. *)

val remove_first: 'a t -> unit
(** [remove_first q] removes the element returned by [first q] from the queue
    [q].

    @raise Failure if [q] is empty. *)

val remove: 'a t -> 'a -> unit
(** [remove q x] removes the element [x] from the queue [q].  If [q] does not
    contain the element [x], the function does nothing. *)

val clear: 'a t -> unit
(** Removes all elements from a queue. *)

val reorder_up: 'a t -> 'a -> unit
(** [reorder_up q x] notifies the queue [q] that the priority of the element
    [x] has increased.  If [q] does not contain [x], the function does
    nothing. *)

val reorder_down: 'a t -> 'a -> unit
(** [reorder_down q x] notifies the queue [q] that the priority of the element
    [x] has decreased.  If [q] does not contain [x], the function does
    nothing. *)

(** Input signature of the functor {!PriorityQueue.Make}. *)
module type HashedType =
sig
  type t
  (** The element type. *)

  val equal: t -> t -> bool
  (** The equality predicate on the element type. *)

  val hash: t -> int
  (** A hash function on the elements.  This function must be compatible with
      equality, which means that if [equal x y = true], then [hash] must
      compute the same hash values for [x] and [y]. *)
end

(** Output signature of the functor {!PriorityQueue.Make}. *)
module type S =
sig
  type elt
  (** The element type. *)

  type order = elt -> elt -> bool
  (** The type of priority orders on [elt].  A priority order [ord] is a
      non-strict total order where [ord a b = true] means that the priority of
      [b] is not higher than the priority of [a].  When the priority of an
      element changes, the queue must be notified using the [reorder_up] or
      [reorder_down] function. *)

  type t
  (** The type of priority queues with element type [elt]. *)

  val make: order -> t
  (** [make ord] creates a new priority queue with order [ord]. *)

  val length: t -> int
  (** Returns the number of elements in a queue. *)

  val is_empty: t -> bool
  (** Tests whether a queue is empty. *)

  val add: t -> elt -> unit
  (** Adds an elements to the queue. *)

  val mem: t -> elt -> bool
  (** Tests whether a queue contains a given element. *)

  val first: t -> elt
  (** [first q] returns an element with maximal priority contained in the
      queue [q].

      @raise Failure if [q] is empty. *)

  val remove_first: t -> unit
  (** [remove_first q] removes the element returned by [first q] from the
      queue [q].

      @raise Failure if [q] is empty. *)

  val remove: t -> elt -> unit
  (** [remove q x] removes the element [x] from the queue [q].  If [q] does
      not contain the element [x], the function does nothing. *)

  val clear: t -> unit
  (** Removes all elements from a queue. *)

  val reorder_up: t -> elt -> unit
  (** [reorder_up q x] notifies the queue [q] that the priority of the element
      [x] has increased.  If [q] does not contain [x], the function does
      nothing. *)

  val reorder_down: t -> elt -> unit
  (** [reorder_down q x] notifies the queue [q] that the priority of the
      element [x] has decreased.  If [q] does not contain [x], the function does
      nothing. *)
end

module Make (H: HashedType): S with type elt = H.t

(**/**)

val is_heap: 'a t -> bool
