open Common
open Printf
open Unix
open Configuration

(* The module Marshal is used for serialization and deserialization. *)

open Util
open Common
open Algorithm
               
module RuntimeSystem (Alg: Algorithm) = struct

open Alg


   (*
   let get =
      node_id -> state -> key -> valu * state

   let put =
      node_id -> state -> key -> valu -> state * payload

   let guard =
      node_id -> state -> key -> valu -> payload -> bool

   let update =
      node_id -> state -> key -> valu -> payload -> state
   *)   

   
   type message_data = node_id * key * valu * update_data

   type env = {   
      nid: node_id
      ; in_sock: file_descr
      ; in_sock_cmsg: file_descr
      ; in_chan: in_channel
      ; in_chan_cmsg: in_channel
      
      (* nodes: Other nodes in the system. *)
      (* ; nodes : (node_id * (file_descr * sockaddr)) list *)
      ; nodes: (node_id * (file_descr * out_channel)) list
      ; nodes_cmsg: (node_id * (file_descr * out_channel)) list
      
      (* st: The current state of the node. *)
      ; mutable st: state

      ; mutable prog: program
      
      ; mutable qu: mqueue
      
      ; mutable put_time: float
      ; mutable get_time: float
      ; mutable update_time: float
      
   }
   
   let make_sockaddr ip p =
      ADDR_INET (inet_addr_of_string ip, p)
      
   let make_udp_socket =
      let s = socket PF_INET SOCK_DGRAM 0 in
      setsockopt s SO_REUSEADDR true;
      s

   let make_out_udp_socket ip p =
      let s = socket PF_INET SOCK_DGRAM 0 in
      setsockopt s SO_REUSEADDR true;
      connect s (make_sockaddr ip p);
      s

   let make_in_udp_socket p =
      let s = socket PF_INET SOCK_DGRAM 0 in
      setsockopt s SO_REUSEADDR true;
      bind s (ADDR_INET (inet_addr_any, p));
      s
      (*
         PF_INET: Internet domain (IPv4)
         SOCK_DGRAM: Datagram socket
         SOCK_STREAM: Stream socket
      *)
      (* 
         setsockopt: Set or clear a boolean-valued option in the given socket. 
         SO_REUSEADDR: Allow reuse of local addresses for bind
      *)
      (* 
         bind: Bind a socket to an address.
         val inet_addr_any: A special IPv4 address, for use only with bind, representing all the Internet addresses that the host machine possesses.
      *)

   (*
   let chan_of env nid : out_channel =
      let (_, sa) = List.assoc nid env.nodes in
      let s = make_udp_socket in
      ignore(getsockopt_error s);
      connect s sa;
      out_channel_of_descr s
   *)
   
   let chan_of env nid : out_channel =  
      let (_, c) = List.assoc nid env.nodes in
      c
      
   let chan_of_cmsg env nid : out_channel =
      let (_, c) = List.assoc nid env.nodes_cmsg in
      c

   let nid_of env chan : node_id =
(*       let flip = function (n, (s, sa, c)) -> (c, n) in *)
      let flip = function (n, (_, c)) -> (c, n) in
      List.assoc chan (List.map flip env.nodes)
      

   (* The function setup prepares and returns the environment for the input node id. *)
   let setup net_info nid prog =
      let n_info = List.assoc nid net_info in
      let p = n_info.port in
      (* let prog = n_info.prog in *)
      let sock = make_in_udp_socket p in
      let sock_cmsg = make_in_udp_socket (p + List.length net_info) in
      {
         nid = nid
         ; in_sock = sock
         ; in_sock_cmsg = sock_cmsg
         ; in_chan = in_channel_of_descr sock
         ; in_chan_cmsg = in_channel_of_descr sock_cmsg
         ; nodes = optmap (fun (nid', {ip; port}) ->
                              if nid' = nid || nid' = -1 then
                                 None 
                              else
                                 let sock = make_out_udp_socket ip port in
                                 let chan = out_channel_of_descr sock in
                                 Some (nid', (sock, chan)))
                           net_info
         ; nodes_cmsg = optmap (fun (nid', {ip; port}) ->
                              if (nid <> -1 && nid' <> -1) || (nid = -1 && nid' = -1) then
                                 None
                              else
                                 let sock = make_out_udp_socket ip (port + List.length net_info) in
                                 let chan = out_channel_of_descr sock in
                                 Some (nid', (sock, chan)))
                           net_info
         ; st = init_method 0
         ; prog = prog
         ; qu = init_queue
         ; put_time = 0.0
         ; get_time = 0.0
         ; update_time = 0.0

      }

   
   
   let receive env : message_data =
      (* Marshal.from_channel env.in_chan *)
      let m = Marshal.from_channel env.in_chan in
(*       let (nid, _, _ , _) = m in *)
(*       printf "Node %d: Received message from node %d\n%!" env.nid nid; *)
      m

   let send_chan env chan m nid =
(*       printf "Node %d: Sending message to node %d\n%!" env.nid nid; (* (nid_of env chan); *) *)
      Marshal.to_channel chan m [];
      flush chan

   let send env nid m =
      send_chan env (chan_of env nid) m nid

   (*
   let broadcast env m =      
      List.iter
         (fun (nid', (_, sa)) ->
              let s = make_udp_socket in
              ignore(getsockopt_error s);
              connect s sa;
              ignore(send_chan env (out_channel_of_descr s) m nid'))
         env.nodes
   *)
   
   let broadcast env m =      
      List.iter
         (fun (nid', (sock, chan)) ->
              ignore(getsockopt_error sock);
              ignore(send_chan env chan m nid'))
         env.nodes


(*    type cmsg = node_id * int *)
   type cmsg = int
   let start_cmsg = 7
   let finish_cmsg = 8


   (* cmsg *)
   let receive_cmsg env : cmsg =
      Marshal.from_channel env.in_chan_cmsg
(*      let c = Marshal.from_channel env.in_chan_cmsg in
      let (nid, m) = c in
      printf "Node %d: Received cmsg %d from node %d\n%!" env.nid m nid;
      c*)

   let send_chan_cmsg env chan c nid =
(*      let (_, m) = c in
      printf "Node %d: Sending cmsg %d to node %d\n%!" env.nid m nid; (* (nid_of env chan); *)*)
      Marshal.to_channel chan c [];
      flush chan

   let send_cmsg env nid c =
      send_chan_cmsg env (chan_of_cmsg env nid) c nid

   (*
   let broadcast_cmsg env c =
      List.iter
         (fun (nid', (_, sa)) ->
              let s = make_udp_socket in
              ignore(getsockopt_error s);
              connect s sa;
              ignore(send_chan env (out_channel_of_descr s) c nid'))
         env.nodes
   *)
   
   let broadcast_cmsg env c =
      List.iter
         (fun (nid', (sock, chan)) ->
              ignore(getsockopt_error sock);
              ignore(send_chan_cmsg env chan c nid'))
         env.nodes_cmsg
         
         
(*
      let check_message env nid m =
      let (_, k, v, u) = m in
      let st = env.st in
      let t1 = time () in
      let g = guard_method nid st k v u in
      let t2 = time () in
      env.guard_time <- (env.guard_time +. (t2 -. t1));
      if g then (
         env.st <- update_method nid st k v u
(*          ; printf "Node %d: Applying update for key %d\n%!" nid k *)
      )

   let check_messages env nid =
      let t1 = time () in
      List.iter (check_message env nid) env.messages;
      let t2 = time () in
      env.update_time <- (env.update_time +. (t2 -. t1))
*)

   let prog_step env nid : bool =
      let st = env.st in
      match env.prog with
      | Put (k, v, p) ->
(*          let t1' = time () in *)
         let (st', u) = put_method nid st k v in         
         env.st <- st';
         env.prog <- p;
         if (List.length env.nodes > 0) then (
            let u' = to_data u in
            broadcast env (nid, k, v, u')
         );
(*          let t2' = time () in *)
(*          env.put_time <- (env.put_time +. (t2' -. t1')); *)
(*          printf "Node %d: executing Put(%d, %d)\n%!" nid k v; *)
         false

      | Get (k, pf) ->
(*          let t1 = time () in *)
         let (v, st') = get_method nid st k in
         env.st <- st';
         env.prog <- pf v;
(*          let t2 = time () in *)
(*          env.get_time <- (env.get_time +. (t2 -. t1)); *)
(*          printf "Node %d: executing Get (%d): %d\n%!" nid k v; *)
         false

      | Skip ->
(*          printf "Node %d: executing Skip\n%!" nid; *)
         true

      | Fault ->
(*          printf "Node %d: Assertion Failure!\n%!" nid; *)
         true

   let rec prog_step_rec env nid n =
      if n = 0 then
         false
      else
         let b = prog_step env nid in
         if b then
            true
         else
            prog_step_rec env nid (n - 1)
   
   let exec_step env nid : bool =
(*       let t1 = time () in *)
      let st' = check_messages nid env.st env.qu in
(*       let t2 = time () in *)
(*       env.update_time <- (env.update_time +. (t2 -. t1)); *)
      env.st <- st';
      prog_step_rec env nid 350
(*       prog_step_rec env nid 200 *)
(*       prog_step_rec env nid 400 *)
(*       prog_step env nid *)


(*   let handshake env nid =
      printf "Node %d: Sending control messages\n%!" nid;
      broadcast_cmsg env (nid, are_you_on_cmsg);
(*       broadcast_cmsg env (nid, are_you_on_cmsg); *)
      printf "Node %d: Receiving control messages\n%!" nid;
      for i = 0 to (2*(List.length env.nodes_cmsg) - 1) do
         let (n, c) = receive_cmsg env in
         if c = are_you_on_cmsg then
            send_cmsg env n (nid, i_am_on_cmsg)
      done*)


   let flag_start env =
      ignore(broadcast_cmsg env start_cmsg)

   let wait_for_start_flag env =
      ignore (receive_cmsg env)

   let flag_finish env =
      ignore(broadcast_cmsg env finish_cmsg)
      
   let wait_for_finish_flag env =
      for i = 0 to (List.length env.nodes_cmsg - 1) do
         ignore (receive_cmsg env)
      done

   
   let deliver_step env nid =
      let m = receive env in
      let (n, k, v, u) = m in
(*       printf "Node %d: Delivered message from node %d\n%!" nid n; *)
      let u' = from_data u in
      enqueue_message nid env.qu (n, k, v, u')
(*       env.messages <- (n, k, v, u') :: env.messages *)
      

   (* It loops until a socket is ready to read from. *)
   let rec select_ready rs ws es t =
      try select rs ws es t
      with Unix_error (err, fn, arg) ->
         select_ready rs ws es t
      (* 
         select: Wait until some input/output operations become possible on some channels. The three list arguments are, respectively, a set of descriptors to check 
         for reading (first argument), 
         for writing (second argument), or 
         for exceptional conditions (third argument). 
         The fourth argument is the maximal timeout, in seconds; a negative fourth argument means no timeout (unbounded wait). 
         The result is composed of three sets of descriptors: those ready for reading (first component), ready for writing (second component), and over which an exceptional condition is pending (third component).
      *)

(*    let rec step_loop env nid c = *)
   let rec step_loop env nid =
(*       let (fds, _, _) = select_ready [env.in_sock] [] [] 0.01 in *)      
      let (fds, _, _) = select_ready [env.in_sock] [] [] 0.0 in
      let fin =
         try 
            match fds with
            | _ :: _ ->               
               deliver_step env nid;
               false
            | _ ->               
               let b = exec_step env nid in
(*                c := !c + 400; *)
(*                printf "Node %d: Done ops %d\n%!" nid !c; *)
               b
         with _ -> 
            printf "Node %d: Error\n%!" nid;
            false 
         in
      if not fin then
         step_loop env nid
(*          step_loop env nid c *)


         
   let main (net_info: (node_id * node_info) list) nid prog = 
      printf "Node %d: Setting up the node state\n%!" nid;
      let env = setup net_info nid prog in
(*       printf "Node %d: Handshaking with others\n%!" nid; *)
(*       handshake env nid; *)
(*       printf "Node %d: Press Enter once all servers are setup\n%!" nid; *)
(*       let _ = input_line Pervasives.stdin in *)
      if nid <> -1 then (
         printf "Node %d: Waiting for start flag\n%!" nid;
         wait_for_start_flag env;
         printf "Node %d: Entering the step loop\n%!" nid;
         let t1 = time () in
         step_loop env nid;
(*          step_loop env nid (ref 0); *)
         let t2 = time () in
         printf "Node %d: Finished in %f seconds.\n%!" nid (t2 -. t1);
         let oc = open_out "Result.txt" in
         fprintf oc "%f\n%!" (t2 -. t1);
(*          fprintf oc "%f\n%!" env.put_time; *)
(*          fprintf oc "%f\n%!" env.get_time; *)
(*          fprintf oc "%f\n%!" env.update_time; *)
         close_out oc;
         printf "Node %d: Sending finish flag and waiting for termination flag\n%!" nid;
         flag_finish env;
         wait_for_start_flag env;
         printf "Node %d: Received termination flag\n%!" nid

      ) else (
         printf "Node %d: sending flag\n%!" nid;
         flag_start env;
         printf "Node %d: Waiting for finish flag\n%!" nid;
         wait_for_finish_flag env;
         printf "Node %d: Sending termination flag\n%!" nid;
         flag_start env
      )


end














