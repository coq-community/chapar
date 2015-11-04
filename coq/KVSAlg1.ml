type 'a sig2 =
  'a
  (* singleton inductive, whose constructor was exist2 *)

(** val plus : int -> int -> int **)

let rec plus = (+)

module SysPredefs = 
 struct 
  (** val coq_MaxNId : int **)
  
  let coq_MaxNId =
    4
  
  type coq_NId = int
  
  (** val nid_eq_dec : int -> int -> bool **)
  
  let nid_eq_dec =
    (=)
  
  (** val beq_nid : int -> int -> bool **)
  
  let beq_nid =
    (=)
  
  (** val bnats : int -> int list sig2 **)
  
  let rec bnats n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      [])
      (fun n' ->
      n' :: (bnats n'))
      n
  
  (** val nids : coq_NId list **)
  
  let nids =
    bnats coq_MaxNId
  
  (** val init_nid : int **)
  
  let init_nid =
    coq_MaxNId
  
  type coq_Key = int
  
  (** val key_eq_dec : int -> int -> bool **)
  
  let key_eq_dec =
    (=)
  
  (** val override : (int -> 'a1) -> int -> 'a1 -> int -> 'a1 **)
  
  let override m k v k' =
    if (=) k' k then v else m k'
  
  (** val update_key :
      (coq_Key -> 'a1) -> coq_Key -> 'a1 -> coq_Key -> 'a1 **)
  
  let update_key m k v k' =
    if key_eq_dec k' k then v else m k
  
  (** val update_nid :
      (coq_NId -> 'a1) -> coq_NId -> 'a1 -> coq_NId -> 'a1 **)
  
  let update_nid m n v n' =
    if nid_eq_dec n' n then v else m n
  
  type coq_Clock = int
 end

module KVSAlg1 = 
 struct 
  type coq_Clock = int
  
  type 'val0 coq_StateRec = { store : (SysPredefs.coq_Key -> 'val0);
                              clock : (SysPredefs.coq_NId -> coq_Clock) }
  
  (** val coq_StateRec_rect :
      ((SysPredefs.coq_Key -> 'a1) -> (SysPredefs.coq_NId -> coq_Clock) ->
      'a2) -> 'a1 coq_StateRec -> 'a2 **)
  
  let coq_StateRec_rect f s =
    let { store = x; clock = x0 } = s in f x x0
  
  (** val coq_StateRec_rec :
      ((SysPredefs.coq_Key -> 'a1) -> (SysPredefs.coq_NId -> coq_Clock) ->
      'a2) -> 'a1 coq_StateRec -> 'a2 **)
  
  let coq_StateRec_rec f s =
    let { store = x; clock = x0 } = s in f x x0
  
  (** val store : 'a1 coq_StateRec -> SysPredefs.coq_Key -> 'a1 **)
  
  let store x = x.store
  
  (** val clock : 'a1 coq_StateRec -> SysPredefs.coq_NId -> coq_Clock **)
  
  let clock x = x.clock
  
  (** val state :
      (SysPredefs.coq_Key -> 'a1) -> (SysPredefs.coq_NId -> coq_Clock) -> 'a1
      coq_StateRec **)
  
  let state store0 x =
    { store = store0; clock = x }
  
  type 'val0 coq_State = 'val0 coq_StateRec
  
  type 'val0 coq_UpdateRec = { sender_node : SysPredefs.coq_NId;
                               sender_clock : (SysPredefs.coq_NId ->
                                              coq_Clock) }
  
  (** val coq_UpdateRec_rect :
      (SysPredefs.coq_NId -> (SysPredefs.coq_NId -> coq_Clock) -> 'a2) -> 'a1
      coq_UpdateRec -> 'a2 **)
  
  let coq_UpdateRec_rect f u =
    let { sender_node = x; sender_clock = x0 } = u in f x x0
  
  (** val coq_UpdateRec_rec :
      (SysPredefs.coq_NId -> (SysPredefs.coq_NId -> coq_Clock) -> 'a2) -> 'a1
      coq_UpdateRec -> 'a2 **)
  
  let coq_UpdateRec_rec f u =
    let { sender_node = x; sender_clock = x0 } = u in f x x0
  
  (** val sender_node : 'a1 coq_UpdateRec -> SysPredefs.coq_NId **)
  
  let sender_node x = x.sender_node
  
  (** val sender_clock :
      'a1 coq_UpdateRec -> SysPredefs.coq_NId -> coq_Clock **)
  
  let sender_clock x = x.sender_clock
  
  (** val update :
      SysPredefs.coq_NId -> (SysPredefs.coq_NId -> coq_Clock) -> 'a1
      coq_UpdateRec **)
  
  let update sender_node0 sender_clock0 =
    { sender_node = sender_node0; sender_clock = sender_clock0 }
  
  type 'val0 coq_Update = 'val0 coq_UpdateRec
  
  (** val dummy_update : 'a1 coq_UpdateRec **)
  
  let dummy_update =
    update 0 (fun n -> 0)
  
  (** val init_method : 'a1 -> 'a1 coq_State **)
  
  let init_method init_val =
    state (fun k -> init_val) (fun n -> 0)
  
  (** val get_method :
      SysPredefs.coq_NId -> 'a1 coq_State -> SysPredefs.coq_Key -> 'a1 * 'a1
      coq_State **)
  
  let get_method n this k =
    let s = this.store in let c = this.clock in ((s k), (state s c))
  
  (** val put_method :
      SysPredefs.coq_NId -> 'a1 coq_State -> SysPredefs.coq_Key -> 'a1 -> 'a1
      coq_State * 'a1 coq_Update **)
  
  let put_method n this k v =
    let s = this.store in
    let c = this.clock in
    let c' = SysPredefs.override c n (plus (c n) (Pervasives.succ 0)) in
    let s' = SysPredefs.override s k v in ((state s' c'), (update n c'))
  
  (** val guard_method :
      SysPredefs.coq_NId -> 'a1 coq_State -> SysPredefs.coq_Key -> 'a1 -> 'a1
      coq_Update -> bool **)
  
  let guard_method n this k v u =
    let c = this.clock in
    let n' = u.sender_node in
    let c' = u.sender_clock in
    (&&) ((=) (c' n') (plus (c n') (Pervasives.succ 0)))
      ((fun a b c -> List.fold_left a c b) (fun b n0 ->
        (&&) b ((||) ((=) n0 n') ((<=) (c' n0) (c n0)))) SysPredefs.nids
        true)
  
  (** val update_method :
      SysPredefs.coq_NId -> 'a1 coq_State -> SysPredefs.coq_Key -> 'a1 -> 'a1
      coq_Update -> 'a1 coq_State **)
  
  let update_method n this k v u =
    let s = this.store in
    let c = this.clock in
    let n' = u.sender_node in
    let c' = u.sender_clock in
    let c'' = SysPredefs.override c n' (c' n') in
    let s'' = SysPredefs.override s k v in state s'' c''
 end

