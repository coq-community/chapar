open Printf
open Unix

open BatDllist

open Common
open Algorithm
open KVSAlg2


module Algorithm2 : Algorithm = struct
   open KVSAlg2

   type state = valu KVSAlg2.coq_State
  
   type update = valu KVSAlg2.coq_Update

   let init_method = KVSAlg2.init_method
   
   let get_method = KVSAlg2.get_method
   
   let put_method = KVSAlg2.put_method
   
   let guard_method = KVSAlg2.guard_method
   
   let update_method = KVSAlg2.update_method

   type update_data = update

   let to_data u = u
   let from_data u = u   
   
   type message = node_id * key * valu * update     
   type mqueue = message node_t
   
   let init_queue = create (0, 0, 0, dummy_update)

   let check_messages nid st qu =
      let cst = ref st in
      let h = qu in 
      let c = ref (next h) in
      let p = ref h in
(*       printf "Node %d: Entering the loop %f\n%!" nid (time ()); *)
      while not (!c == h) do
         let m = get !c in
         let (n, k, v, u) = m in
         p := !c;
         c := next !c;
         let g = guard_method nid !cst k v u in
         if g then (
            cst := update_method nid !cst k v u;
            remove !p
(*             ; printf "Node %d: Applying update from node %d for key %d\n%!" nid n k             *)
         )
      done;
(*       printf "Node %d: Exiting the loop %f\n%!" nid (time ()); *)
      !cst
      
   let enqueue_message nid qu m =
      add qu m      
(*      let (n, k, v, u) = m in      
      printf "Node %d: Received message from node %d key %d\n%!" nid n k;
      add qu m*)

end



(*
   type mqueue = message list
   
   let init_queue = []

   let rec check_messages_rec nid st qu qu' =
      match qu with
      | [] -> (st, qu')
      | m :: qur ->
         let (_, k, v, u) = m in
         let g = guard_method nid st k v u in
         if g then (
            let st' = update_method nid st k v u in
            check_messages_rec nid st' qur qu'
         ) else
            check_messages_rec nid st qur (m :: qu')

   let check_messages nid st qu =
      check_messages_rec nid st qu []
      
   let enqueue_message qu m =
      m :: qu
*)
      
