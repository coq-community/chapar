module Array =
struct

  include Array

  let swap a i j =
    let ai = get a i in
      set a i (get a j);
      set a j ai

  let rev_iter f a =
    for i = length a - 1 downto 0 do
      f (unsafe_get a i)
    done

  let rev_iteri f a =
    for i = length a - 1 downto 0 do
      f i (unsafe_get a i)
    done

  let fold_left2 f a b c =
    let rec fold a i =
      if i > length b - 1 then a
      else fold (f a (unsafe_get b i) (unsafe_get c i)) (i + 1)
    in
      if length b = length c then
        fold a 0
      else
        invalid_arg "ExtArray.Array.fold_left2: array lengths not equal"

  let fold_right2 f a b c =
    let rec fold c i =
      if i < 0 then c
      else fold (f (unsafe_get a i) (unsafe_get b i) c) (i - 1)
    in
      if length a = length b then
        fold c 0
      else
        invalid_arg "ExtArray.Array.fold_right2: array lengths not equal"

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

  let for_all2 p a b =
    let rec for_all i =
      if i >= length a then false
      else if p (unsafe_get a i) (unsafe_get b i) then for_all (i + 1)
      else false
    in
      if length a = length b then
        for_all 0
      else
        invalid_arg "Array.for_all2: array lengths not equal"

  let exists2 p a b =
    let rec exists i =
      if i >= length a then false
      else if p (unsafe_get a i) (unsafe_get b i) then true
      else exists (i + 1)
    in
      if length a = length b then
        exists 0
      else
        invalid_arg "Array.exists2: array lengths not equal"

  let lexicographic_compare cmp a1 a2 =
    let l1 = length a1 in
    let l2 = length a2 in
    let rec lex_compare i =
      if i >= l1 || i >= l2 then l1 - l2
      else
        let c = cmp (unsafe_get a1 i) (unsafe_get a2 i)
        in if c <> 0 then c else lex_compare (i + 1)
    in
      lex_compare 0

end
