open Common





module type Algorithm = sig   
   
   type state
   type update
   
   val init_method : valu -> state
   
   val get_method :
      node_id -> state -> key -> valu * state
   
   val put_method :
      node_id -> state -> key -> valu -> state * update
   
   val guard_method :
      node_id -> state -> key -> valu -> update -> bool
   
   val update_method :
      node_id -> state -> key -> valu -> update -> state

   type update_data
   
   val to_data : update -> update_data
   val from_data: update_data -> update

   type mqueue
   
   type message = node_id * key * valu * update
   
   val init_queue: mqueue
   
(*    val check_messages: node_id -> state -> mqueue -> (state * mqueue) *)
   val check_messages: node_id -> state -> mqueue -> state

(*    val enqueue_message: node_id -> mqueue -> message -> mqueue *)
   val enqueue_message: node_id -> mqueue -> message -> unit
   
end




(*
open Common

module type Algorithm = sig

   type state
   type payload

   val init: state
   val put: node_id -> state -> key -> valu -> (state * payload)
   val get: node_id -> state -> key -> (valu * state)
   val guard: node_id -> state -> key -> valu -> payload -> bool
   val update: node_id -> state -> key -> valu -> payload -> state

end
*)
