open List



let rec optmap f = function
| [] -> []
| hd :: tl ->
   match f hd with
   | None -> optmap f tl
   | Some x -> x :: optmap f tl

   
let take n l =
  let rec sub_list n accu l =
    match l with 
    | [] -> accu
    | hd :: tl ->
      if n = 0 then accu
      else sub_list (n - 1) (hd :: accu) tl
  in
  rev (sub_list n [] l)

   
   