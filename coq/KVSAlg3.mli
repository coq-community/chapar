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

module KVSAlg3 : 
 sig 
  type coq_Clock = int
  
  type 'val0 coq_Entry = { entry_val : 'val0;
                           entry_node : SysPredefs.coq_NId;
                           entry_clock : coq_Clock }
  
  val coq_Entry_rect :
    ('a1 -> SysPredefs.coq_NId -> coq_Clock -> 'a2) -> 'a1 coq_Entry -> 'a2
  
  val coq_Entry_rec :
    ('a1 -> SysPredefs.coq_NId -> coq_Clock -> 'a2) -> 'a1 coq_Entry -> 'a2
  
  val entry_val : 'a1 coq_Entry -> 'a1
  
  val entry_node : 'a1 coq_Entry -> SysPredefs.coq_NId
  
  val entry_clock : 'a1 coq_Entry -> coq_Clock
  
  val entry : 'a1 -> SysPredefs.coq_NId -> coq_Clock -> 'a1 coq_Entry
  
  type 'val0 coq_StateRec = { store : (SysPredefs.coq_Key -> 'val0 coq_Entry);
                              coq_rec : (SysPredefs.coq_NId -> coq_Clock);
                              dep : (SysPredefs.coq_NId -> coq_Clock) }
  
  val coq_StateRec_rect :
    ((SysPredefs.coq_Key -> 'a1 coq_Entry) -> (SysPredefs.coq_NId ->
    coq_Clock) -> (SysPredefs.coq_NId -> coq_Clock) -> 'a2) -> 'a1
    coq_StateRec -> 'a2
  
  val coq_StateRec_rec :
    ((SysPredefs.coq_Key -> 'a1 coq_Entry) -> (SysPredefs.coq_NId ->
    coq_Clock) -> (SysPredefs.coq_NId -> coq_Clock) -> 'a2) -> 'a1
    coq_StateRec -> 'a2
  
  val store : 'a1 coq_StateRec -> SysPredefs.coq_Key -> 'a1 coq_Entry
  
  val coq_rec : 'a1 coq_StateRec -> SysPredefs.coq_NId -> coq_Clock
  
  val dep : 'a1 coq_StateRec -> SysPredefs.coq_NId -> coq_Clock
  
  val state :
    (SysPredefs.coq_Key -> 'a1 coq_Entry) -> (SysPredefs.coq_NId ->
    coq_Clock) -> (SysPredefs.coq_NId -> coq_Clock) -> 'a1 coq_StateRec
  
  type 'val0 coq_State = 'val0 coq_StateRec
  
  type 'val0 coq_UpdateRec = { sender_node : SysPredefs.coq_NId;
                               sender_dep : (SysPredefs.coq_NId -> coq_Clock) }
  
  val coq_UpdateRec_rect :
    (SysPredefs.coq_NId -> (SysPredefs.coq_NId -> coq_Clock) -> 'a2) -> 'a1
    coq_UpdateRec -> 'a2
  
  val coq_UpdateRec_rec :
    (SysPredefs.coq_NId -> (SysPredefs.coq_NId -> coq_Clock) -> 'a2) -> 'a1
    coq_UpdateRec -> 'a2
  
  val sender_node : 'a1 coq_UpdateRec -> SysPredefs.coq_NId
  
  val sender_dep : 'a1 coq_UpdateRec -> SysPredefs.coq_NId -> coq_Clock
  
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

