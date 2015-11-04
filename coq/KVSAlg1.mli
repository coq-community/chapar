type 'a sig2 =
  'a
  (* singleton inductive, whose constructor was exist2 *)

val plus : int -> int -> int

module SysPredefs : 
 sig 
  val coq_MaxNId : int
  
  type coq_NId = int
  
  val nid_eq_dec : int -> int -> bool
  
  val beq_nid : int -> int -> bool
  
  val bnats : int -> int list sig2
  
  val nids : coq_NId list
  
  val init_nid : int
  
  type coq_Key = int
  
  val key_eq_dec : int -> int -> bool
  
  val override : (int -> 'a1) -> int -> 'a1 -> int -> 'a1
  
  val update_key : (coq_Key -> 'a1) -> coq_Key -> 'a1 -> coq_Key -> 'a1
  
  val update_nid : (coq_NId -> 'a1) -> coq_NId -> 'a1 -> coq_NId -> 'a1
  
  type coq_Clock = int
 end

module KVSAlg1 : 
 sig 
  type coq_Clock = int
  
  type 'val0 coq_StateRec = { store : (SysPredefs.coq_Key -> 'val0);
                              clock : (SysPredefs.coq_NId -> coq_Clock) }
  
  val coq_StateRec_rect :
    ((SysPredefs.coq_Key -> 'a1) -> (SysPredefs.coq_NId -> coq_Clock) -> 'a2)
    -> 'a1 coq_StateRec -> 'a2
  
  val coq_StateRec_rec :
    ((SysPredefs.coq_Key -> 'a1) -> (SysPredefs.coq_NId -> coq_Clock) -> 'a2)
    -> 'a1 coq_StateRec -> 'a2
  
  val store : 'a1 coq_StateRec -> SysPredefs.coq_Key -> 'a1
  
  val clock : 'a1 coq_StateRec -> SysPredefs.coq_NId -> coq_Clock
  
  val state :
    (SysPredefs.coq_Key -> 'a1) -> (SysPredefs.coq_NId -> coq_Clock) -> 'a1
    coq_StateRec
  
  type 'val0 coq_State = 'val0 coq_StateRec
  
  type 'val0 coq_UpdateRec = { sender_node : SysPredefs.coq_NId;
                               sender_clock : (SysPredefs.coq_NId ->
                                              coq_Clock) }
  
  val coq_UpdateRec_rect :
    (SysPredefs.coq_NId -> (SysPredefs.coq_NId -> coq_Clock) -> 'a2) -> 'a1
    coq_UpdateRec -> 'a2
  
  val coq_UpdateRec_rec :
    (SysPredefs.coq_NId -> (SysPredefs.coq_NId -> coq_Clock) -> 'a2) -> 'a1
    coq_UpdateRec -> 'a2
  
  val sender_node : 'a1 coq_UpdateRec -> SysPredefs.coq_NId
  
  val sender_clock : 'a1 coq_UpdateRec -> SysPredefs.coq_NId -> coq_Clock
  
  val update :
    SysPredefs.coq_NId -> (SysPredefs.coq_NId -> coq_Clock) -> 'a1
    coq_UpdateRec
  
  type 'val0 coq_Update = 'val0 coq_UpdateRec
  
  val dummy_update : 'a1 coq_UpdateRec
  
  val init_method : 'a1 -> 'a1 coq_State
  
  val get_method :
    SysPredefs.coq_NId -> 'a1 coq_State -> SysPredefs.coq_Key -> 'a1 * 'a1
    coq_State
  
  val put_method :
    SysPredefs.coq_NId -> 'a1 coq_State -> SysPredefs.coq_Key -> 'a1 -> 'a1
    coq_State * 'a1 coq_Update
  
  val guard_method :
    SysPredefs.coq_NId -> 'a1 coq_State -> SysPredefs.coq_Key -> 'a1 -> 'a1
    coq_Update -> bool
  
  val update_method :
    SysPredefs.coq_NId -> 'a1 coq_State -> SysPredefs.coq_Key -> 'a1 -> 'a1
    coq_Update -> 'a1 coq_State
 end

