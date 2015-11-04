module List =
struct

  include List

  open Fun

  let cons x xs =
    x :: xs

  let singleton x =
    [x]

  let max_elt l =
    match l with
      | x :: xs -> Some (fold_left max x xs)
      | [] -> None

  let min_elt l =
    match l with
      | x :: xs -> Some (fold_left min x xs)
      | [] -> None

  let iteri f l =
    ignore (fold_left (fun i x -> f i x; i + 1) 0 l); ()

  let rec generate f a b =
    if a > b then [] else (f a) :: (generate f (a + 1) b)

  let range = generate (fun x -> x)

  let fold_left1 f l =
    match l with
        x :: xs -> fold_left f x xs
      | [] -> failwith "ExtList.List.fold_left1: empty list"

  let rec fold_right1 f l =
    match l with
        [x] -> x
      | x :: xs -> f x (fold_right1 f xs)
      | [] -> failwith "ExtList.List.fold_right1: empty list"

  let fold_map f a l =
    let (a', l') =
      fold_left
        (fun (a, r) x -> let (a', x') = (f a x) in (a', x' :: r))
        (a, []) l
    in
      (a', rev l')

  let rec remove_dup l =
    match l with
        x1 :: (x2 :: _ as xs) ->
          if x1 = x2 then remove_dup xs
          else x1 :: (remove_dup xs)
      | _ -> l

  let rec set_merge s1 s2 =
    match s1, s2 with
        [], _ -> s2
      | _, [] -> s1
      | x :: xs, y :: ys ->
          if x = y then x :: set_merge xs ys
          else if x < y then x :: set_merge xs s2
          else y :: set_merge s1 ys

  let set_sort s =
    remove_dup (fast_sort compare s)

  let setify =
    set_sort

  let union =
    set_merge

  let rec inter s1 s2 =
    match s1, s2 with
        [], _ -> []
      | _, [] -> []
      | x :: xs, y :: ys ->
          if x = y then x :: inter xs ys
          else if x < y then inter xs s2
          else inter s1 ys

  let rec diff s1 s2 =
    match s1, s2 with
        [], _ -> []
      | _, [] -> s1
      | x :: xs, y :: ys ->
          if x = y then diff xs ys
          else if x < y then x :: diff xs s2
          else diff s1 ys

  let rec subset s1 s2 =
    match s1, s2 with
        [], _ -> true
      | _, [] -> false
      | x :: xs, y :: ys ->
          if x = y then subset xs ys
          else if x < y then false
          else subset s1 ys

  let rec proper_subset s1 s2 =
    match s1, s2 with
        _, [] -> false
      | [], _ -> true
      | x :: xs, y :: ys ->
          if x = y then proper_subset xs ys
          else if x < y then false
          else subset s1 ys

  let set_map f s =
    setify (map f s)

  let add x s =
    union [x] s

  let assoc_map f =
    map (fun (x, y) -> (x, f y))

  let for_all_pairs p l1 l2 =
    for_all (fun x -> for_all (fun y -> p x y) l2) l1

  let exists_pair p l1 l2 =
    exists (fun x -> exists (fun y -> p x y) l2) l1

  let iter_pairs f l1 l2 =
    iter (fun x -> iter (fun y -> f x y) l2) l1

  let rec find2 p l1 l2 =
    match l1, l2 with
        [], _
      | _ , [] -> raise Not_found
      | (x :: xs), (y :: ys) -> if p x y then (x, y) else find2 p xs ys

  let rec lexicographic_compare cmp l1 l2 =
    match l1, l2 with
        [], [] -> 0
      | [], _ -> -1
      | _, [] ->  1
      | (x :: xs), (y :: ys) ->
          let c = cmp x y
          in if c <> 0 then c else lexicographic_compare cmp xs ys

end
