(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, y) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (x, y) -> y

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

module KVSAlg2 = 
 struct 
  type coq_Clock = int
  
  type 'val0 coq_Entry = { entry_val : 'val0;
                           entry_node : SysPredefs.coq_NId;
                           entry_clock : coq_Clock }
  
  (** val coq_Entry_rect :
      ('a1 -> SysPredefs.coq_NId -> coq_Clock -> 'a2) -> 'a1 coq_Entry -> 'a2 **)
  
  let coq_Entry_rect f e =
    let { entry_val = x; entry_node = x0; entry_clock = x1 } = e in f x x0 x1
  
  (** val coq_Entry_rec :
      ('a1 -> SysPredefs.coq_NId -> coq_Clock -> 'a2) -> 'a1 coq_Entry -> 'a2 **)
  
  let coq_Entry_rec f e =
    let { entry_val = x; entry_node = x0; entry_clock = x1 } = e in f x x0 x1
  
  (** val entry_val : 'a1 coq_Entry -> 'a1 **)
  
  let entry_val x = x.entry_val
  
  (** val entry_node : 'a1 coq_Entry -> SysPredefs.coq_NId **)
  
  let entry_node x = x.entry_node
  
  (** val entry_clock : 'a1 coq_Entry -> coq_Clock **)
  
  let entry_clock x = x.entry_clock
  
  (** val entry : 'a1 -> SysPredefs.coq_NId -> coq_Clock -> 'a1 coq_Entry **)
  
  let entry entry_val0 x x0 =
    { entry_val = entry_val0; entry_node = x; entry_clock = x0 }
  
  type 'val0 coq_StateRec = { store : (SysPredefs.coq_Key -> 'val0 coq_Entry);
                              received : (SysPredefs.coq_NId -> coq_Clock);
                              clock : coq_Clock;
                              dep : (SysPredefs.coq_NId * coq_Clock) list }
  
  (** val coq_StateRec_rect :
      ((SysPredefs.coq_Key -> 'a1 coq_Entry) -> (SysPredefs.coq_NId ->
      coq_Clock) -> coq_Clock -> (SysPredefs.coq_NId * coq_Clock) list ->
      'a2) -> 'a1 coq_StateRec -> 'a2 **)
  
  let coq_StateRec_rect f s =
    let { store = x; received = x0; clock = x1; dep = x2 } = s in
    f x x0 x1 x2
  
  (** val coq_StateRec_rec :
      ((SysPredefs.coq_Key -> 'a1 coq_Entry) -> (SysPredefs.coq_NId ->
      coq_Clock) -> coq_Clock -> (SysPredefs.coq_NId * coq_Clock) list ->
      'a2) -> 'a1 coq_StateRec -> 'a2 **)
  
  let coq_StateRec_rec f s =
    let { store = x; received = x0; clock = x1; dep = x2 } = s in
    f x x0 x1 x2
  
  (** val store : 'a1 coq_StateRec -> SysPredefs.coq_Key -> 'a1 coq_Entry **)
  
  let store x = x.store
  
  (** val received : 'a1 coq_StateRec -> SysPredefs.coq_NId -> coq_Clock **)
  
  let received x = x.received
  
  (** val clock : 'a1 coq_StateRec -> coq_Clock **)
  
  let clock x = x.clock
  
  (** val dep : 'a1 coq_StateRec -> (SysPredefs.coq_NId * coq_Clock) list **)
  
  let dep x = x.dep
  
  (** val state :
      (SysPredefs.coq_Key -> 'a1 coq_Entry) -> (SysPredefs.coq_NId ->
      coq_Clock) -> coq_Clock -> (SysPredefs.coq_NId * coq_Clock) list -> 'a1
      coq_StateRec **)
  
  let state store0 x x0 x1 =
    { store = store0; received = x; clock = x0; dep = x1 }
  
  type 'val0 coq_State = 'val0 coq_StateRec
  
  type 'val0 coq_UpdateRec = { sender_node : SysPredefs.coq_NId;
                               sender_clock : coq_Clock;
                               sender_dep : (SysPredefs.coq_NId * coq_Clock)
                                            list }
  
  (** val coq_UpdateRec_rect :
      (SysPredefs.coq_NId -> coq_Clock -> (SysPredefs.coq_NId * coq_Clock)
      list -> 'a2) -> 'a1 coq_UpdateRec -> 'a2 **)
  
  let coq_UpdateRec_rect f u =
    let { sender_node = x; sender_clock = x0; sender_dep = x1 } = u in
    f x x0 x1
  
  (** val coq_UpdateRec_rec :
      (SysPredefs.coq_NId -> coq_Clock -> (SysPredefs.coq_NId * coq_Clock)
      list -> 'a2) -> 'a1 coq_UpdateRec -> 'a2 **)
  
  let coq_UpdateRec_rec f u =
    let { sender_node = x; sender_clock = x0; sender_dep = x1 } = u in
    f x x0 x1
  
  (** val sender_node : 'a1 coq_UpdateRec -> SysPredefs.coq_NId **)
  
  let sender_node x = x.sender_node
  
  (** val sender_clock : 'a1 coq_UpdateRec -> coq_Clock **)
  
  let sender_clock x = x.sender_clock
  
  (** val sender_dep :
      'a1 coq_UpdateRec -> (SysPredefs.coq_NId * coq_Clock) list **)
  
  let sender_dep x = x.sender_dep
  
  (** val update :
      SysPredefs.coq_NId -> coq_Clock -> (SysPredefs.coq_NId * coq_Clock)
      list -> 'a1 coq_UpdateRec **)
  
  let update sender_node0 x x0 =
    { sender_node = sender_node0; sender_clock = x; sender_dep = x0 }
  
  type 'val0 coq_Update = 'val0 coq_UpdateRec
  
  (** val dummy_update : 'a1 coq_UpdateRec **)
  
  let dummy_update =
    update 0 0 []
  
  (** val init_method : 'a1 -> 'a1 coq_State **)
  
  let init_method init_val =
    state (fun k -> entry init_val SysPredefs.init_nid 0) (fun n -> 0) 0 []
  
  (** val get_method :
      SysPredefs.coq_NId -> 'a1 coq_State -> SysPredefs.coq_Key -> 'a1 * 'a1
      coq_State **)
  
  let get_method n this k =
    let s = this.store in
    let r = this.received in
    let c = this.clock in
    let d = this.dep in
    let e = s k in
    let v = e.entry_val in
    let n' = e.entry_node in
    let c' = e.entry_clock in
    let d' = if not ((=) n' SysPredefs.init_nid) then (n', c') :: d else d in
    (v, (state s r c d'))
  
  (** val put_method :
      SysPredefs.coq_NId -> 'a1 coq_State -> SysPredefs.coq_Key -> 'a1 -> 'a1
      coq_State * 'a1 coq_Update **)
  
  let put_method n this k v =
    let s = this.store in
    let r = this.received in
    let c = this.clock in
    let d = this.dep in
    let c' = plus c (Pervasives.succ 0) in
    let s' = SysPredefs.override s k (entry v n c') in
    let d' = (n, c') :: [] in
    let r' = SysPredefs.override r n c' in
    ((state s' r' c' d'), (update n c' d))
  
  (** val guard_method :
      SysPredefs.coq_NId -> 'a1 coq_State -> SysPredefs.coq_Key -> 'a1 -> 'a1
      coq_Update -> bool **)
  
  let guard_method n this k v u =
    let r = this.received in
    let d' = u.sender_dep in
    (fun a b c -> List.fold_left a c b) (fun b p ->
      let n' = fst p in let c' = snd p in (&&) b ((<=) c' (r n'))) d' true
  
  (** val update_method :
      SysPredefs.coq_NId -> 'a1 coq_State -> SysPredefs.coq_Key -> 'a1 -> 'a1
      coq_Update -> 'a1 coq_State **)
  
  let update_method n this k v u =
    let s = this.store in
    let r = this.received in
    let c = this.clock in
    let d = this.dep in
    let n' = u.sender_node in
    let c' = u.sender_clock in
    let s' = SysPredefs.override s k (entry v n' c') in
    let r' = SysPredefs.override r n' c' in state s' r' c d
 end

