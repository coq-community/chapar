let identity x = x

let const a _ = a

let compose f g x = f (g x)

let (|>) x f = f x

let rec iterate f n =
  if n <= 0 then identity
  else compose f (iterate f (n - 1))

let curry f x y = f (x, y)

let uncurry f (x, y) = f x y

let non p x = not (p x)

let rec fix f x =
  let x' = f x in
    if x = x' then x' else fix f x'

let rec fix_cmp eq f x =
  let x' = f x in
    if eq x x' then x' else fix_cmp eq f x'

exception No_fixed_point

let rec bounded_fix f x bound =
  if bound > 0 then
    let x' = f x in
      if x = x' then x' else bounded_fix f x' (bound - 1)
  else raise No_fixed_point

let rec bounded_fix_cmp eq f x bound =
  if bound > 0 then
    let x' = f x in
      if eq x x' then x' else bounded_fix_cmp eq f x' (bound - 1)
  else raise No_fixed_point

