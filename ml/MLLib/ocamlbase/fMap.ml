(* The implementation of the FMap module is based on binary trees of bounded
   balance as described in the following papers:

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

type ('a, 'b) t =
    Empty
  | Node of (('a * 'b) * int * ('a, 'b) t * ('a, 'b) t)

let empty = Empty

let is_empty t = t = Empty

let singleton x = Node (x, 1, Empty, Empty)

let size t =
  match t with
      Node (_, n, _, _) -> n
    | Empty -> 0

let rec is_defined x t =
  match t with
      Empty -> false
    | Node ((x', _), _, l, r) ->
        if x < x' then is_defined x l
        else if x > x' then is_defined x r
        else true

let mem = is_defined

let rec find x t =
  match t with
      Empty -> raise Not_found
    | Node ((x', y), _, l, r) ->
        if x < x' then find x l
        else if x > x' then find x r
        else y

let make_tree x l r =
  match l, r with
      Empty, Empty -> singleton x
    | Empty, Node (_, n, _, _)
    | Node (_, n, _, _), Empty -> Node (x, n + 1, l, r)
    | Node (_, n, _, _), Node (_, m, _, _) -> Node (x, n + m + 1, l, r)

let delta = 4
let alpha = 2

let single_rot_left x a t =
  match t with
      Node (y, _, b, c) -> make_tree y (make_tree x a b) c
    | Empty -> failwith "FMap.single_rot_left: empty tree"

let single_rot_right y t c =
  match t with
      Node (x, _, a, b) -> make_tree x a (make_tree y b c)
    | Empty -> failwith "FMap.single_rot_right: empty tree"

let double_rot_left x a t =
  match t with
      Node (z, _, Node (y, _, b, c), d) ->
        make_tree y (make_tree x a b) (make_tree z c d)
    | _ -> failwith "FMap.double_rot_left: invalid right tree"

let double_rot_right z t d =
  match t with
      Node (x, _, a, Node (y, _, b, c)) ->
        make_tree y (make_tree x a b) (make_tree z c d)
    | _ -> failwith "FMap.double_rot_right: invalid left tree"

let rotate_left x l r =
  match r with
      Node (_, _, rl, rr) ->
        if size rl < alpha * size rr then single_rot_left x l r
        else double_rot_left x l r
    | _ -> failwith "FMap.rotate_left: invalid right tree"

let rotate_right x l r =
  match l with
      Node (_, _, ll, lr) ->
        if size lr < alpha * size ll then single_rot_right x l r
        else double_rot_right x l r
    | _ -> failwith "FMap.rotate_right: invalid left tree"

let balance x l r =
  let nl = size l in
  let nr = size r in
    if nl + nr <= 1 then Node (x, nl + nr + 1, l, r)
    else if nr > delta * nl then rotate_left x l r
    else if nl > delta * nr then rotate_right x l r
    else Node (x, nl + nr + 1, l, r)

let rec add x y t =
  match t with
      Empty -> singleton (x, y)
    | Node ((x', _) as z, _, l, r) ->
        if x < x' then balance z (add x y l) r
        else if x > x' then balance z l (add x y r)
        else make_tree (x, y) l r

let rec remove_min_elt t =
  match t with
      Node (x, _, Empty, r) -> (x, r)
    | Node (x, _, l, r) ->
        let (y, l') = remove_min_elt l in (y, balance x l' r)
    | Empty -> failwith "FMap.remove_min_elt: empty tree"

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

let rec remove x t =
  match t with
      Empty -> Empty
    | Node ((x', _) as z, _, l, r) ->
        if x < x' then balance z (remove x l) r
        else if x > x' then balance z l (remove x r)
        else glue_balanced l r

let rec fold f t a =
  match t with
      Empty -> a
    | Node ((x, y), _, l, r) -> fold f r (f x y (fold f l a))

let rec rev_fold f t a =
  match t with
      Empty -> a
    | Node ((x, y), _, l, r) -> rev_fold f l (f x y (rev_fold f r a))

let rec iter f t =
  match t with
      Empty -> ()
    | Node ((x, y), _, l, r) -> iter f l; f x y; iter f r

let rec rev_iter f t =
  match t with
      Empty -> ()
    | Node ((x, y), _, l, r) -> rev_iter f r; f x y; rev_iter f l

let rec map f t =
  match t with
      Empty -> Empty
    | Node ((x, y), n, l, r) -> Node ((x, f y), n, map f l, map f r)

let rec mapi f t =
  match t with
      Empty -> Empty
    | Node ((x, y), n, l, r) -> Node ((x, f x y), n, mapi f l, mapi f r)

let rec for_all p t =
  match t with
      Empty -> true
    | Node ((x, y), _, l, r) -> p x y && for_all p l && for_all p r

let rec exists p t =
  match t with
      Empty -> false
    | Node ((x, y), _, l, r) -> p x y || for_all p l || for_all p r

let apply t x =
  find x t

type ('a, 'b) enum =
    End
  | More of (('a * 'b) * ('a, 'b) t * ('a, 'b) enum)

let rec cons_enum t e =
  match t with
      Empty -> e
    | Node (x, _, l, r) -> cons_enum l (More (x, r, e))

let enum t = cons_enum t End

let compare cmp t1 t2 =
  let rec compare_enums e1 e2 =
    match e1, e2 with
        End, End ->  0
      | End, _   -> -1
      | _, End   ->  1
      | More ((x1, y1), r1, e1'), More ((x2, y2), r2, e2') ->
          if x1 < x2 then -1
          else if x1 > x2 then 1
          else let c = cmp y1 y2 in
            if c <> 0 then c
            else compare_enums (cons_enum r1 e1') (cons_enum r2 e2')
  in
    compare_enums (enum t1) (enum t2)

let equal cmp t1 t2 =
  let rec equal_enums e1 e2 =
    match e1, e2 with
        End, End -> true
      | End, _   -> false
      | _, End   -> false
      | More ((x1, y1), r1, e1'), More ((x2, y2), r2, e2') ->
          x1 = x2 && cmp y1 y2 &&
    equal_enums (cons_enum r1 e1') (cons_enum r2 e2')
  in
    equal_enums (enum t1) (enum t2)

let to_list t =
  rev_fold (fun x y l -> (x, y) :: l) t []

let of_list l =
  List.fold_left (fun s (x, y) -> add x y s) empty l

module type OrderedType =
sig
  type t
  val compare : t -> t -> int
end

module type S =
sig
  type key
  type 'a t
  val size: 'a t -> int
  val compare: ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val equal: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val empty: 'a t
  val add: key -> 'a -> 'a t -> 'a t
  val remove: key -> 'a t -> 'a t
  val iter: (key -> 'a -> unit) -> 'a t -> unit
  val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val rev_fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val map: ('a -> 'b) -> 'a t -> 'b t
  val mapi: (key -> 'a -> 'b) -> 'a t -> 'b t
  val is_empty: 'a t -> bool
  val for_all: (key -> 'a -> bool) -> 'a t -> bool
  val exists: (key -> 'a -> bool) -> 'a t -> bool
  val mem: key -> 'a t -> bool
  val is_defined: key -> 'a t -> bool
  val find: key -> 'a t -> 'a
  val apply: 'a t -> key -> 'a
  val to_list: 'a t -> (key * 'a) list
  val of_list: (key * 'a) list -> 'a t
end

module Make (Ord: OrderedType) =
struct

  type key = Ord.t

  type 'a t =
      Empty
    | Node of ((key * 'a) * int * 'a t * 'a t)

  let empty = Empty

  let is_empty t = t = Empty

  let singleton x = Node (x, 1, Empty, Empty)

  let size t =
    match t with
        Node (_, n, _, _) -> n
      | Empty -> 0

  let rec is_defined x t =
    match t with
        Empty -> false
      | Node ((x', _), _, l, r) ->
          let c = Ord.compare x x' in
            if c < 0 then is_defined x l
            else if c > 0 then is_defined x r
            else true

  let mem = is_defined

  let rec find x t =
    match t with
        Empty -> raise Not_found
      | Node ((x', y), _, l, r) ->
          let c = Ord.compare x x' in
            if c < 0 then find x l
            else if c > 0 then find x r
            else y

  let make_tree x l r =
    match l, r with
        Empty, Empty -> singleton x
      | Empty, Node (_, n, _, _)
      | Node (_, n, _, _), Empty -> Node (x, n + 1, l, r)
      | Node (_, n, _, _), Node (_, m, _, _) -> Node (x, n + m + 1, l, r)

  let delta = 4
  let alpha = 2

  let single_rot_left x a t =
    match t with
        Node (y, _, b, c) -> make_tree y (make_tree x a b) c
      | Empty -> failwith "FMap.single_rot_left: empty tree"

  let single_rot_right y t c =
    match t with
        Node (x, _, a, b) -> make_tree x a (make_tree y b c)
      | Empty -> failwith "FMap.single_rot_right: empty tree"

  let double_rot_left x a t =
    match t with
        Node (z, _, Node (y, _, b, c), d) ->
          make_tree y (make_tree x a b) (make_tree z c d)
      | _ -> failwith "FMap.double_rot_left: invalid right tree"

  let double_rot_right z t d =
    match t with
        Node (x, _, a, Node (y, _, b, c)) ->
          make_tree y (make_tree x a b) (make_tree z c d)
      | _ -> failwith "FMap.double_rot_right: invalid left tree"

  let rotate_left x l r =
    match r with
        Node (_, _, rl, rr) ->
          if size rl < alpha * size rr then single_rot_left x l r
          else double_rot_left x l r
      | _ -> failwith "FMap.rotate_left: invalid right tree"

  let rotate_right x l r =
    match l with
        Node (_, _, ll, lr) ->
          if size lr < alpha * size ll then single_rot_right x l r
          else double_rot_right x l r
      | _ -> failwith "FMap.rotate_right: invalid left tree"

  let balance x l r =
    let nl = size l in
    let nr = size r in
      if nl + nr <= 1 then Node (x, nl + nr + 1, l, r)
      else if nr > delta * nl then rotate_left x l r
      else if nl > delta * nr then rotate_right x l r
      else Node (x, nl + nr + 1, l, r)

  let rec add x y t =
    match t with
        Empty -> singleton (x, y)
      | Node ((x', _) as z, _, l, r) ->
          let c = Ord.compare x x' in
            if c < 0 then balance z (add x y l) r
            else if c > 0 then balance z l (add x y r)
            else make_tree (x, y) l r

  let rec remove_min_elt t =
    match t with
        Node (x, _, Empty, r) -> (x, r)
      | Node (x, _, l, r) ->
          let (y, l') = remove_min_elt l in (y, balance x l' r)
      | Empty -> failwith "FMap.remove_min_elt: empty tree"

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

  let rec remove x t =
    match t with
        Empty -> Empty
      | Node ((x', _) as z, _, l, r) ->
          let c = Ord.compare x x' in
            if c < 0 then balance z (remove x l) r
            else if c > 0 then balance z l (remove x r)
            else glue_balanced l r

  let rec fold f t a =
    match t with
        Empty -> a
      | Node ((x, y), _, l, r) -> fold f r (f x y (fold f l a))

  let rec rev_fold f t a =
    match t with
        Empty -> a
      | Node ((x, y), _, l, r) -> rev_fold f l (f x y (rev_fold f r a))

  let rec iter f t =
    match t with
        Empty -> ()
      | Node ((x, y), _, l, r) -> iter f l; f x y; iter f r

  let rec rev_iter f t =
    match t with
        Empty -> ()
      | Node ((x, y), _, l, r) -> rev_iter f r; f x y; rev_iter f l

  let rec map f t =
    match t with
        Empty -> Empty
      | Node ((x, y), n, l, r) -> Node ((x, f y), n, map f l, map f r)

  let rec mapi f t =
    match t with
        Empty -> Empty
      | Node ((x, y), n, l, r) -> Node ((x, f x y), n, mapi f l, mapi f r)

  let rec for_all p t =
    match t with
        Empty -> true
      | Node ((x, y), _, l, r) -> p x y && for_all p l && for_all p r

  let rec exists p t =
    match t with
        Empty -> false
      | Node ((x, y), _, l, r) -> p x y || for_all p l || for_all p r

  let apply t x =
    find x t

  type 'a enum =
      End
    | More of ((key * 'a) * 'a t * 'a enum)

  let rec cons_enum t e =
    match t with
        Empty -> e
      | Node (x, _, l, r) -> cons_enum l (More (x, r, e))

  let enum t = cons_enum t End

  let compare cmp t1 t2 =
    let rec compare_enums e1 e2 =
      match e1, e2 with
          End, End ->  0
        | End, _   -> -1
        | _, End   ->  1
        | More ((x1, y1), r1, e1'), More ((x2, y2), r2, e2') ->
            let c1 = Ord.compare x1 x2 in
              if c1 <> 0 then c1
              else let c2 = cmp y1 y2 in
                if c2 <> 0 then c2
                else compare_enums (cons_enum r1 e1') (cons_enum r2 e2')
    in
      compare_enums (enum t1) (enum t2)

  let equal cmp t1 t2 =
    let rec equal_enums  e1 e2 =
      match e1, e2 with
          End, End -> true
        | End, _   -> false
        | _, End   -> false
        | More ((x1, y1), r1, e1'), More ((x2, y2), r2, e2') ->
            Ord.compare x1 x2 = 0 && cmp y1 y2 &&
      equal_enums (cons_enum r1 e1') (cons_enum r2 e2')
    in
      equal_enums (enum t1) (enum t2)

  let to_list t =
    rev_fold (fun x y l -> (x, y) :: l) t []

  let of_list l =
    List.fold_left (fun s (x, y) -> add x y s) empty l

end
