(* open KVSAlg1 *)
(* open SysPredefs *)


type key = int (* coq_Key *)
type valu = int
type node_id = int (* coq_NId *)


type program =
| Put of key * valu * program
| Get of key * (valu -> program)
| Skip
| Fault



(*
let p1 =
   Put (1, 2, Skip)
   
let _ =
   print_endline "Executed"

*)