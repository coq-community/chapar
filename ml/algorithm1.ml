open Printf
open List

open Common
open Algorithm

open KVSAlg1
open SysPredefs



module Algorithm1 : Algorithm = struct
   open KVSAlg1
   
   type state = valu KVSAlg1.coq_State
  
   type update = valu KVSAlg1.coq_Update

   let init_method = KVSAlg1.init_method
   
   let get_method = KVSAlg1.get_method
   
   let put_method = KVSAlg1.put_method
   
   let guard_method = KVSAlg1.guard_method
   
   let update_method = KVSAlg1.update_method

   type clock = KVSAlg1.coq_Clock
   type update_data = { sender_node_data : node_id;
                        sender_clock_data : (node_id * clock) list }
   
   let nid_fun_to_list f =
      List.map (fun nid -> (nid, f nid))
                nids

   let rec nid_fun_from_list_rec f l =
      match l with
      | [] -> f
      | (nid, c) :: l' -> 
        nid_fun_from_list_rec (override f nid c) l'
      
   let nid_fun_from_list l =
      nid_fun_from_list_rec (fun n -> 0) l
      
      
   let to_data u = { sender_node_data = u.KVSAlg1.sender_node;
                     sender_clock_data = nid_fun_to_list u.KVSAlg1.sender_clock }

   let from_data u = { KVSAlg1.sender_node = u.sender_node_data;
                       KVSAlg1.sender_clock = nid_fun_from_list u.sender_clock_data }


   open BatDllist
   type message = node_id * key * valu * update     
   type mqueue = message node_t
   
   let init_queue = create (0, 0, 0, dummy_update)
         
   let check_messages nid st qu =
      let cst = ref st in
      let h = qu in 
      let c = ref (next h) in
      let p = ref h in
      while not (!c == h) do
         let m = get !c in
         let (n, k, v, u) = m in
         p := !c;
         c := next !c;
         let g = guard_method nid !cst k v u in
         if g then (
            cst := update_method nid !cst k v u;
            remove !p
(*             ; printf "Node %d: Applying update from node %d for key %d\n%!" nid n k *)
         )
      done;
      !cst
      
   let enqueue_message nid qu m =
      add qu m      
(*      let (n, k, v, u) = m in      
      printf "Node %d: Received message from node %d key %d\n%!" nid n k;
      add qu m*)

(*
   open PriorityQueue
   
   
   type message = node_id * key * valu * update  
   let moder: message order =
      fun m1 m2 ->
         let (_, _, _, u1) = m1 in
         let c1 = u1.sender_clock in
         let (_, _, _, u2) = m2 in
         let c2 = u2.sender_clock in
         for_all (fun n -> c1 n <= c2 n) nids

   type mqueue = message PriorityQueue.t

   let init_queue = make moder   

   let print_clock nid u =
      let c = u.sender_clock in
      List.iter (fun n -> 
                  printf "Node %d: Clock for Node %d: %d\n%!" nid n (c n)
                ) nids
         
         
   let check_messages nid st qu =
      let cst = ref st in
      let fin = ref false in 
      while (not (!fin)) && (not (is_empty qu)) do         
         let m = first qu in
         let (n, k, v, u) = m in
         printf "Node %d: Looking at first with key %d and value %d\n%!" nid k v;
         print_clock nid u;
         let g = guard_method nid !cst k v u in
         if g then (
            remove_first qu;
            cst := update_method nid !cst k v u
            ; printf "Node %d: Applying update from node %d for key %d\n%!" nid n k
         ) else 
            fin := true
      done;
      !cst
      
   let enqueue_message nid qu m =
(*       add qu m *)
      let (n, k, v, u) = m in      
      printf "Node %d: Received message from node %d for key %d\n%!" nid n k;
      add qu m
*)

end

