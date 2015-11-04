(* The implementation of the FSet module is based on binary trees of bounded
   balance (BB trees) as described in the following papers:

   - Stephen Adams, "Efficient sets: a balancing act", Journal of Functional
     Programming 3(4), 553-652, 1993.

   - Jürg Nievergelt and Edward M. Reingold, "Binary search trees of bounded
     balance", SIAM Journal of Computing 2(1), 1973.

   The code is based on Daan Leijen's Haskell implementation, Stephen Adams
   SML implementation, and the implementation of the Set module in the OCaml
   Standard Library.

   Copyright (C) 2002       Daan Leijen
   Copyright (C) 1992-1996  Stephen Adams
   Copyright (C) 1996       Institut National de Recherche en
                            Informatique et en Automatique
*)

open ExtList

type 'a t =
    Empty
  | Node of ('a * int * 'a t * 'a t)

let empty = Empty

let is_empty t = t = Empty

let singleton x = Node (x, 1, Empty, Empty)

let size t =
  match t with
      Node (_, n, _, _) -> n
    | Empty -> 0

let cardinal = size

let rec mem x t =
  match t with
      Empty -> false
    | Node (y, _, l, r) ->
        if x < y then mem x l
        else if x > y then mem x r
        else true

(** Tree balancing

    A tree is called well-formed if every node contains the correct size and
    for every node, the element at the node is greater than all elements in
    the node's left subtree and less than all elements in the node's right
    subtree.

    A tree is called balanced if for every node, the size of the larger
    subtree is at most [delta] times the size of the smaller subtree.

    Balanced and well-formed trees can be created using the following
    functions:

    [make_tree x l r] assumes that the tree [Node (x, _, l, r)] ist
    well-formed and balanced.

    [balance x l r] assumes that [Node (x, _, l, r)] is obtained by adding one
    element to or removing one element from a well-formed and balanced tree.

    [join x l r] assumes that [l] and [r] are balanced and well-formed trees
    and that [x] is greater than all elements of [l] and less than all
    elements of [r].

    [glue_balanced l r] assumes that [Node (_, _, l, r)] is well-formed and
    balanced.

    [glue l r] assumes that [l] and [r] are well-formed and balanced.
*)

let delta = 4    (** The tree balancing factor. *)
let alpha = 2    (** The single / double rotation factor. *)

let make_tree x l r =
  match l, r with
      Empty, Empty -> singleton x
    | Empty, Node (_, n, _, _)
    | Node (_, n, _, _), Empty -> Node (x, n + 1, l, r)
    | Node (_, n, _, _), Node (_, m, _, _) -> Node (x, n + m + 1, l, r)

let single_rot_left x a t =
  match t with
      Node (y, _, b, c) -> make_tree y (make_tree x a b) c
    | Empty -> failwith "FSet.single_rot_left: empty tree"

let single_rot_right y t c =
  match t with
      Node (x, _, a, b) -> make_tree x a (make_tree y b c)
    | Empty -> failwith "FSet.single_rot_right: empty tree"

let double_rot_left x a t =
  match t with
      Node (z, _, Node (y, _, b, c), d) ->
        make_tree y (make_tree x a b) (make_tree z c d)
    | _ -> failwith "FSet.double_rot_left: invalid right tree"

let double_rot_right z t d =
  match t with
      Node (x, _, a, Node (y, _, b, c)) ->
        make_tree y (make_tree x a b) (make_tree z c d)
    | _ -> failwith "FSet.double_rot_right: invalid left tree"

let rotate_left x l r =
  match r with
      Node (_, _, rl, rr) ->
        if size rl < alpha * size rr then single_rot_left x l r
        else double_rot_left x l r
    | _ -> failwith "FSet.rotate_left: invalid right tree"

let rotate_right x l r =
  match l with
      Node (_, _, ll, lr) ->
        if size lr < alpha * size ll then single_rot_right x l r
        else double_rot_right x l r
    | _ -> failwith "FSet.rotate_right: invalid left tree"

let balance x l r =
  let nl = size l in
  let nr = size r in
    if nl + nr <= 1 then Node (x, nl + nr + 1, l, r)
    else if nr > delta * nl then rotate_left x l r
    else if nl > delta * nr then rotate_right x l r
    else Node (x, nl + nr + 1, l, r)

let rec add x t =
  match t with
      Empty -> singleton x
    | Node (y, _, l, r) ->
        if x < y then balance y (add x l) r
        else if x > y then balance y l (add x r)
        else t

let rec join x l r =
  match l, r with
      Empty, _ -> add x r
    | _, Empty -> add x l
    | Node (y, nl, ll, lr), Node (z, nr, rl, rr) ->
        if delta * nl < nr then balance z (join x l rl) rr
        else if delta * nr < nl then balance y ll (join x lr r)
        else make_tree x l r

let rec remove_min_elt t =
  match t with
      Node (x, _, Empty, r) -> (x, r)
    | Node (x, _, l, r) ->
        let (y, l') = remove_min_elt l in (y, balance x l' r)
    | Empty -> failwith "FSet.remove_min_elt: empty tree"

let glue_balanced l r =
  match l, r with
      Empty, _ -> r
    | _, Empty -> l
    | _ -> let (x, r') = remove_min_elt r in balance x l r'

let rec glue l r =
  match l, r with
      Empty, _ -> r
    | _, Empty -> l
    | Node (x, nl, ll, lr), Node (y, nr, rl, rr) ->
        if delta * nl < nr then balance y (glue l rl) rr
        else if delta * nr < nl then balance x ll (glue lr r)
        else let (x, r') = remove_min_elt r in balance x l r'

let rec min_elt t =
  match t with
      Node (x, _, Empty, _) -> Some x
    | Node (_, _, l, _) -> min_elt l
    | Empty -> None

let rec max_elt t =
  match t with
      Node (x, _, _, Empty) -> Some x
    | Node (_, _, _, r) -> max_elt r
    | Empty -> None

let rec remove x t =
  match t with
      Empty -> Empty
    | Node (y, _, l, r) ->
        if x < y then balance y (remove x l) r
        else if x > y then balance y l (remove x r)
        else glue_balanced l r

let rec split x t =
  match t with
      Empty -> (Empty, false, Empty)
    | Node (y, _, l, r) ->
        if x < y then
          let (lt, present, gt) = split x l
          in (lt, present, join y gt r)
        else if x > y then
          let (lt, present, gt) = split x r
          in (join y l lt, present, gt)
        else
          (l, true, r)

let rec union t1 t2 =
  match t1, t2 with
      Empty, _ -> t2
    | _, Empty -> t1
    | _, Node (x, _, l, r) ->
        let (l', _, r') = split x t1 in
          join x (union l' l) (union r' r)

let rec diff t1 t2 =
  match t1, t2 with
      Empty, _ -> Empty
    | _, Empty -> t1
    | _, Node (x, _, l, r) ->
        let (l', _, r') = split x t1 in
          glue (diff l' l) (diff r' r)

let rec inter t1 t2 =
  match t1, t2 with
      Empty, _ -> Empty
    | _, Empty -> Empty
    | _, Node (x, _, l, r) ->
        let (l', present, r') = split x t1 in
          if present then
            join x (inter l' l) (inter r' r)
          else
            glue (inter l' l) (inter r' r)

let rec fold f t a =
  match t with
      Empty -> a
    | Node (x, _, l, r) -> fold f r (f x (fold f l a))

let rec rev_fold f t a =
  match t with
      Empty -> a
    | Node (x, _, l, r) -> rev_fold f l (f x (rev_fold f r a))

let map f t =
  fold (fun x q -> add (f x) q) t empty

let rec iter f t =
  match t with
      Empty -> ()
    | Node (x, _, l, r) -> iter f l; f x; iter f r

let rec rev_iter f t =
  match t with
      Empty -> ()
    | Node (x, _, l, r) -> rev_iter f r; f x; rev_iter f l

let rec for_all p t =
  match t with
      Empty -> true
    | Node (x, _, l, r) -> p x && for_all p l && for_all p r

let rec exists p t =
  match t with
      Empty -> false
    | Node (x, _, l, r) -> p x || for_all p l || for_all p r

let filter p t =
  fold (fun x q -> if p x then add x q else q) t empty

let partition p t =
  fold
    (fun x (q, r) -> if p x then (add x q, r) else (q, add x r))
    t (empty, empty)

let elements t =
  rev_fold List.cons t []

let choose s =
  match min_elt s with
    | Some x -> x
    | None -> raise Not_found

type 'a enum =
    End
  | More of ('a * 'a t * 'a enum)

let rec cons_enum t e =
  match t with
      Empty -> e
    | Node (x, _, l, r) -> cons_enum l (More (x, r, e))

let rec enum_size e =
  match e with
      End -> 0
    | More (x, r, e) -> 1 + size r + enum_size e

let enum t = cons_enum t End

let compare t1 t2 =
  let rec compare_enums e1 e2 =
    match e1, e2 with
        End, End ->  0
      | End, _   -> -1
      | _, End   ->  1
      | More (x1, r1, e1'), More (x2, r2, e2') ->
          if x1 < x2 then -1
          else if x1 > x2 then 1
          else compare_enums (cons_enum r1 e1') (cons_enum r2 e2')
  in
    compare_enums (enum t1) (enum t2)

let equal t1 t2 =
  compare t1 t2 = 0

let rec subset t1 t2 =
  match t1, t2 with
      Empty, _ -> true
    | _, Empty -> false
    | Node (x1, _, l1, r1), Node (x2, _, l2, r2) ->
        if x1 < x2 then
          subset (Node (x1, 0, l1, Empty)) l2 && subset r1 t2
        else if x1 > x2 then
          subset (Node (x1, 0, Empty, r2)) r2 && subset l1 t2
        else
          subset l1 l2 && subset r1 r2

let to_list = elements

let of_list l =
  List.fold_left (fun s x -> add x s) empty l

module type OrderedType =
sig
  type t
  val compare : t -> t -> int
end

module type S =
sig
  type elt
  type t
  val size: t -> int
  val cardinal: t -> int
  val equal: t -> t -> bool
  val compare: t -> t -> int
  val subset: t -> t -> bool
  val empty: t
  val singleton: elt -> t
  val add: elt -> t -> t
  val remove: elt -> t -> t
  val union: t -> t -> t
  val inter: t -> t -> t
  val diff: t -> t -> t
  val iter: (elt -> unit) -> t -> unit
  val rev_iter: (elt -> unit) -> t -> unit
  val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val rev_fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val map: (elt -> elt) -> t -> t
  val filter: (elt -> bool) -> t -> t
  val partition: (elt -> bool) -> t -> t * t
  val split: elt -> t -> t * bool * t
  val is_empty: t -> bool
  val for_all: (elt -> bool) -> t -> bool
  val exists: (elt -> bool) -> t -> bool
  val mem: elt -> t -> bool
  val choose: t -> elt
  val min_elt: t -> elt option
  val max_elt: t -> elt option
  val to_list: t -> elt list
  val of_list: elt list -> t
  val elements: t -> elt list
end

module Make (Ord: OrderedType) =
struct

  type elt = Ord.t

  type t =
      Empty
    | Node of (elt * int * t * t)

  let empty = Empty

  let is_empty t = t = Empty

  let singleton x = Node (x, 1, Empty, Empty)

  let size t =
    match t with
        Node (_, n, _, _) -> n
      | Empty -> 0

  let cardinal = size

  let rec mem x t =
    match t with
        Empty -> false
      | Node (y, _, l, r) ->
          let c = Ord.compare x y in
            if c < 0 then mem x l
            else if c > 0 then mem x r
            else true

  let delta = 4
  let alpha = 2

  let make_tree x l r =
    match l, r with
        Empty, Empty -> singleton x
      | Empty, Node (_, n, _, _)
      | Node (_, n, _, _), Empty -> Node (x, n + 1, l, r)
      | Node (_, n, _, _), Node (_, m, _, _) -> Node (x, n + m + 1, l, r)

  let single_rot_left x a t =
    match t with
        Node (y, _, b, c) -> make_tree y (make_tree x a b) c
      | Empty -> failwith "FSet.single_rot_left: empty tree"

  let single_rot_right y t c =
    match t with
        Node (x, _, a, b) -> make_tree x a (make_tree y b c)
      | Empty -> failwith "FSet.single_rot_right: empty tree"

  let double_rot_left x a t =
    match t with
        Node (z, _, Node (y, _, b, c), d) ->
          make_tree y (make_tree x a b) (make_tree z c d)
      | _ -> failwith "FSet.double_rot_left: invalid right tree"

  let double_rot_right z t d =
    match t with
        Node (x, _, a, Node (y, _, b, c)) ->
          make_tree y (make_tree x a b) (make_tree z c d)
      | _ -> failwith "FSet.double_rot_right: invalid left tree"

  let rotate_left x l r =
    match r with
        Node (_, _, rl, rr) ->
          if size rl < alpha * size rr then single_rot_left x l r
          else double_rot_left x l r
      | _ -> failwith "FSet.rotate_left: invalid right tree"

  let rotate_right x l r =
    match l with
        Node (_, _, ll, lr) ->
          if size lr < alpha * size ll then single_rot_right x l r
          else double_rot_right x l r
      | _ -> failwith "FSet.rotate_right: invalid left tree"

  let balance x l r =
    let nl = size l in
    let nr = size r in
      if nl + nr <= 1 then Node (x, nl + nr + 1, l, r)
      else if nr > delta * nl then rotate_left x l r
      else if nl > delta * nr then rotate_right x l r
      else Node (x, nl + nr + 1, l, r)

  let rec add x t =
    match t with
        Empty -> singleton x
      | Node (y, _, l, r) ->
          let c = Ord.compare x y in
            if c < 0 then balance y (add x l) r
            else if c > 0 then balance y l (add x r)
            else t

  let rec join x l r =
    match l, r with
        Empty, _ -> add x r
      | _, Empty -> add x l
      | Node (y, nl, ll, lr), Node (z, nr, rl, rr) ->
          if delta * nl < nr then balance z (join x l rl) rr
          else if delta * nr < nl then balance y ll (join x lr r)
          else make_tree x l r

  let rec remove_min_elt t =
    match t with
        Node (x, _, Empty, r) -> (x, r)
      | Node (x, _, l, r) ->
          let (y, l') = remove_min_elt l in (y, balance x l' r)
      | Empty -> failwith "FSet.remove_min_elt: empty tree"

  let glue_balanced l r =
    match l, r with
        Empty, _ -> r
      | _, Empty -> l
      | _ -> let (x, r') = remove_min_elt r in balance x l r'

  let rec glue l r =
    match l, r with
        Empty, _ -> r
      | _, Empty -> l
      | Node (x, nl, ll, lr), Node (y, nr, rl, rr) ->
          if delta * nl < nr then balance y (glue l rl) rr
          else if delta * nr < nl then balance x ll (glue lr r)
          else let (x, r') = remove_min_elt r in balance x l r'

  let rec min_elt t =
    match t with
        Node (x, _, Empty, _) -> Some x
      | Node (_, _, l, _) -> min_elt l
      | Empty -> None

  let rec max_elt t =
    match t with
        Node (x, _, _, Empty) -> Some x
      | Node (_, _, _, r) -> max_elt r
      | Empty -> None

  let rec remove x t =
    match t with
        Empty -> Empty
      | Node (y, _, l, r) ->
          let c = Ord.compare x y in
            if c < 0 then balance y (remove x l) r
            else if c > 0 then balance y l (remove x r)
            else glue_balanced l r

  let rec split x t =
    match t with
        Empty -> (Empty, false, Empty)
      | Node (y, _, l, r) ->
          let c = Ord.compare x y in
            if c < 0 then
              let (lt, present, gt) = split x l
              in (lt, present, join y gt r)
            else if c > 0 then
              let (lt, present, gt) = split x r
              in (join y l lt, present, gt)
            else
              (l, true, r)

  let rec union t1 t2 =
    match t1, t2 with
        Empty, _ -> t2
      | _, Empty -> t1
      | _, Node (x, _, l, r) ->
          let (l', _, r') = split x t1 in
            join x (union l' l) (union r' r)

  let rec diff t1 t2 =
    match t1, t2 with
        Empty, _ -> Empty
      | _, Empty -> t1
      | _, Node (x, _, l, r) ->
          let (l', _, r') = split x t1 in
            glue (diff l' l) (diff r' r)

  let rec inter t1 t2 =
    match t1, t2 with
        Empty, _ -> Empty
      | _, Empty -> Empty
      | _, Node (x, _, l, r) ->
          let (l', present, r') = split x t1 in
            if present then
              join x (inter l' l) (inter r' r)
            else
              glue (inter l' l) (inter r' r)

  let rec fold f t a =
    match t with
        Empty -> a
      | Node (x, _, l, r) -> fold f r (f x (fold f l a))

  let rec rev_fold f t a =
    match t with
        Empty -> a
      | Node (x, _, l, r) -> rev_fold f l (f x (rev_fold f r a))

  let map f t =
    fold (fun x q -> add (f x) q) t empty

  let rec iter f t =
    match t with
        Empty -> ()
      | Node (x, _, l, r) -> iter f l; f x; iter f r

  let rec rev_iter f t =
    match t with
        Empty -> ()
      | Node (x, _, l, r) -> rev_iter f r; f x; rev_iter f l

  let rec for_all p t =
    match t with
        Empty -> true
      | Node (x, _, l, r) -> p x && for_all p l && for_all p r

  let rec exists p t =
    match t with
        Empty -> false
      | Node (x, _, l, r) -> p x || for_all p l || for_all p r

  let filter p t =
    fold (fun x q -> if p x then add x q else q) t empty

  let partition p t =
    fold
      (fun x (q, r) -> if p x then (add x q, r) else (q, add x r))
      t (empty, empty)

  let elements t =
    rev_fold List.cons t []

  let choose s =
    match min_elt s with
      | Some x -> x
      | None -> raise Not_found

  type enum =
      End
    | More of (elt * t * enum)

  let rec cons_enum t e =
    match t with
        Empty -> e
      | Node (x, _, l, r) -> cons_enum l (More (x, r, e))

  let rec enum_size e =
    match e with
        End -> 0
      | More (x, r, e) -> 1 + size r + enum_size e

  let enum t = cons_enum t End

  let compare s1 s2 =
    let rec compare_enums e1 e2 =
      match e1, e2 with
          End, End ->  0
        | End, _   -> -1
        | _, End   ->  1
        | More (x1, r1, e1'), More (x2, r2, e2') ->
            let c = Ord.compare x1 x2 in
              if c <> 0 then c
              else compare_enums (cons_enum r1 e1') (cons_enum r2 e2')
    in
      compare_enums (enum s1) (enum s2)

  let equal s1 s2 =
    compare s1 s2 = 0

  let rec subset t1 t2 =
    match t1, t2 with
        Empty, _ -> true
      | _, Empty -> false
      | Node (x1, _, l1, r1), Node (x2, _, l2, r2) ->
          let c = Ord.compare x1 x2 in
            if c < 0 then
              subset (Node (x1, 0, l1, Empty)) l2 && subset r1 t2
            else if c > 0 then
              subset (Node (x1, 0, Empty, r2)) r2 && subset l1 t2
            else
              subset l1 l2 && subset r1 r2

  let to_list = elements

  let of_list l =
    List.fold_left (fun s x -> add x s) empty l

end
