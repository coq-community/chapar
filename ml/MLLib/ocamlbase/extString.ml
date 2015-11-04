module String =
struct

  include String

  open ExtList

  let concat_conj sep conj strings =
    let rec concat strings =
      match strings with
        | [s1; s2] -> s1 ^ sep ^ " " ^ conj ^ " " ^ s2
        | s :: r -> s ^ sep ^ " " ^ (concat r)
        | _ -> "" in
    match strings with
      | [] -> ""
      | [s] -> s
      | [s1; s2] -> s1 ^ " " ^ conj ^ " " ^ s2
      | _ -> concat strings

  let for_all p a =
    let rec for_all i =
      if i >= length a then true
      else if p (unsafe_get a i) then for_all (i + 1)
      else false
    in
      for_all 0

  let exists p a =
    let rec exists i =
      if i >= length a then false
      else if p (unsafe_get a i) then true
      else exists (i + 1)
    in
      exists 0

  let any_index_from s i chars =
    let length = length s in
    let rec loop i =
      if i < length then
        if List.mem (unsafe_get s i) chars then Some i
        else loop (i + 1)
      else
        None
    in
      if 0 <= i && i < length then
        loop i
      else
        invalid_arg "ExtString.String.any_index_from: invalid index"

  let match_sub s start pat =
    let len_s = String.length s in
    let len_pat = String.length pat in
      if 0 <= start && start < len_s then
        if start + len_pat > len_s then false
        else
          let rec compare i =
            if i >= len_pat then true
            else if unsafe_get pat i <> unsafe_get s (start + i) then false
            else compare (i + 1)
          in
            compare 0
      else
        invalid_arg "ExtString.String.match_sub: invalid index"

  let match_sub2 s1 i1 s2 i2 n =
    if 0 <= i1 && i1 + n <= length s1 &&
       0 <= i2 && i2 + n <= length s2 then
         let rec compare i =
           if i >= n then true
           else if unsafe_get s1 (i1 + i) <> unsafe_get s2 (i2 + i) then false
           else compare (i + 1)
         in
           compare 0
    else
      invalid_arg "ExtString.String.match_sub2: invalid index"

  let fold_left f a s =
    let rec fold a i =
      if i > length s - 1 then a
      else fold (f a (unsafe_get s i)) (i + 1)
    in
      fold a 0

  let fold_right f s a =
    let rec fold a i =
      if i < 0 then a
      else fold (f (unsafe_get s i) a) (i - 1)
    in
      fold a (length s - 1)

  let rev_iter f s =
    for i = length s - 1 downto 0 do
      f (unsafe_get s i)
    done

  let iteri f s =
    for i = 0 to length s - 1 do
      f i (unsafe_get s i)
    done

  let rev_iteri f s =
    for i = length s - 1 downto 0 do
      f i (unsafe_get s i)
    done

  let explode s =
    fold_right (fun c l -> c :: l) s []

  let collect l =
    let s = create (List.length l) in
      List.iteri (fun i c -> set s i c) l;
      s

end
