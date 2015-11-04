(** Utilities for functions. *)

val identity: 'a -> 'a
(** The identity funcrion. *)

val const: 'a -> 'b -> 'a
(** [const c] is the function that maps every value to [c]. *)

val compose: ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c
(** [compose f g] composes the functions [f] and [g] such that [(compose f g)
    x = f (g x)] for all [x]. *)

val (|>): 'a -> ('a -> 'b) -> 'b
(** [x |> f] is equivalent to [f x].  This operator is useful to chain
    function applications in the form [x |> f |> g |> h ...]. *)

val iterate: ('a -> 'a) -> int -> 'a -> 'a
(** Function power; [iterate f n = f^n]. *)

val curry: ('a * 'b -> 'c) -> 'a -> 'b -> 'c
(** Function currying; [(curry f) x y = f (x, y)] for all [x] and [y]. *)

val uncurry: ('a -> 'b -> 'c) -> ('a * 'b) -> 'c
(** Function uncurrying; [(uncurry f) (x, y) = f x y] for all [x] and [y]. *)

val non: ('a -> bool) -> ('a -> bool)
(** [non p] returns the negation of the predicate [p], i.e., [non p x = not (p
    x)]. *)

val fix: ('a -> 'a) -> 'a -> 'a
(** [fix f x] returns the fixed point of the function [f] with starting point
    [x] if it exists, or loops forever if [f] does not converge.  The values
    are compared using the structural equality [=] operator. *)

val fix_cmp: ('a -> 'a -> bool) -> ('a -> 'a) -> 'a -> 'a
(** [fix_cmp eq f x] returns the fixed point of the function [f] with starting
    point [x] if it exists, or loops forever if [f] does not converge.  The
    values are compared using the function [eq]. *)

exception No_fixed_point
(** Raised by [bounded_fix] if no fixed point is reached within the iterations
    bound. *)

val bounded_fix: ('a -> 'a) -> 'a -> int -> 'a
(** [bounded_fix f x bound] returns the fixed point of the function [f] with
    starting point [x] if it is reached within [bound] iterations.  The
    values are compared using the structural equality [=] operator.

    @raise No_fixed_point if [f] does not converge within [bound]
    iterations. *)

val bounded_fix_cmp: ('a -> 'a -> bool) -> ('a -> 'a) -> 'a -> int -> 'a
(** [bounded_fix_cmp eq f x bound] returns the fixed point of the function [f]
    with starting point [x] if it is reached within [bound] iterations.  The
    values are compared using the function [eq].

    @raise No_fixed_point if [f] does not converge within [bound]
    iterations. *)
