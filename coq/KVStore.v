Require Import FunctionalExtensionality Omega.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Max.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Le.

Require Import Coq.Relations.Relation_Operators. (* For union and transitive closure. *)
Require Import Coq.Lists.List. (* For In function. *)
(* Require Import Coq.Lists.ListSet. *)

Add LoadPath "Lib".
Require Import Predefs.


Module SysPredefs.

  (*
  Definition bfun (n n': nat) := n' < n.
  Definition BNat (n: nat) := sig (bfun n). (* {n': nat | n' < n}. *)
  Definition inum {m: nat}(n: BNat m) := proj1_sig n.
  *)

  (* Node identifier *)
  Parameter MaxNId: nat.
  (* Axiom at_least_one_node: MaxNId > 0. *)
  (* Definition NId := BNat MaxNId. *)
  Definition NId := nat.
  (* Definition eq_nid_dec (n n': NId) := eq_nat_dec (inum n) (inum n'). *)
  Definition nid_eq_dec := eq_nat_dec.
  (* Definition beq_nid (n n': NId) := beq_nat (inum n) (inum n'). *)

  Definition beq_nid := beq_nat.
  (* Notation "n =? n'" := (nid_eq n n'). *)

  (*
  Definition below_in {m: nat}(n: nat): list (@BNat m) -> Prop := 
    fun bnats => forall n', 
                   (   (inum n' < n -> exists n'', In n'' bnats /\ inum n' = inum n'')
                    /\ (In n' bnats -> inum n' < n)).
  Definition no_dups {m: nat}: list (@BNat m) -> Prop := 
    fun bnats => NoDup bnats.
  *)
  Definition below_in (n: nat): list nat -> Prop := 
    fun bnats => forall n', n' < n <-> In n' bnats.
  Definition no_dups: list nat -> Prop := 
    fun bnats => NoDup bnats.

  Fixpoint bnats (n: nat): @sig2 (list nat) (below_in n) no_dups.
    refine(
      match n return (sig2 (below_in n) no_dups) with
        | 0 =>
            exist2 (below_in 0) no_dups nil _ _
        | S n' => 
            match (bnats n') with
              | exist2 pbnats H H' => 
                exist2 (below_in (S n')) no_dups 
                       (n'::pbnats)
                       _ _
            end
      end).

    unfold below_in. intros. split; intros. subst. inversion H. subst. inversion H.
    unfold no_dups. constructor.

    unfold below_in. intros. split; intros; subst.

      apply lt_n_Sm_le in H0. apply le_lt_or_eq in H0. destruct H0; subst. 
      simpl. right. unfold below_in in H. apply H. assumption.
      simpl. left. reflexivity.
      
      simpl in H0. destruct H0; subst.
      (*  (_ < S _). *) apply lt_n_Sn.
      unfold below_in in H. apply H in H0. apply lt_S. assumption.

    unfold no_dups. constructor. unfold not. intros. unfold below_in in H. apply H in H0. 
    clear bnats pbnats H H'. induction n'. inversion H0. apply IHn'. apply lt_S_n. assumption.
    unfold no_dups in H'. assumption.
  Defined.


  Definition nids: list NId.        
    refine(
        match (bnats MaxNId) with
          | exist2 l H1 H2 => l
        end).
  Defined.


  (* Definition NId := nat. *)
  (* Axiom LA: forall (n: NId), n < MaxNId. *)
  (* Definition nids := seq 0 MaxNId. *)


  (* Lemma n_in_nids: forall (n: NId), exists n': NId, inum n = inum n' /\ In n' nids. *)
  Lemma below_max_in_nids: forall (n: NId), n < MaxNId <-> In n nids.
    Proof.
      intros.
      unfold nids.
      destruct (bnats MaxNId) as [nids B N].
      unfold below_in in B.
      apply B.
    Qed.

  Lemma nodup_nids:
    NoDup nids.
    Proof.
      intros.
      unfold nids.
      destruct (bnats MaxNId) as [nids B N].
      assumption.
    Qed. 

  Definition init_nid := MaxNId.

  Lemma init_not_in_nids:
    not (In init_nid nids).

    Proof.
      intro.
      unfold init_nid in H.
      assert (A := below_max_in_nids MaxNId).
      apply A in H.
      apply lt_irrefl in H.
      assumption.
    Qed.
  
  Definition Key := nat.
  (* Definition Val := nat. *)
  Definition key_eq_dec := eq_nat_dec.

  Definition override {V: Type} (m: nat -> V) (k: nat) (v: V): nat -> V :=
    fun (k': nat) =>
      if (eq_nat_dec k' k) then v else (m k').


  Lemma override_new_val:
    forall (V: Type) m k (v: V),
      (override m k v) k = v.

    Proof.
      intros.
      unfold override.
      rewrite eq_nat_dec_eq.
      reflexivity.
    Qed.

  Lemma override_new_val':
    forall (V: Type) m k1 k2 (v: V),
      k1 = k2 ->
      (override m k1 v) k2 = v.

    Proof.
      intros.
      subst.
      unfold override.
      rewrite eq_nat_dec_eq.
      reflexivity.
    Qed.

  Lemma override_new_val'':
    forall (V: Type) m k1 k2 (v: V),
      k2 = k1 ->
      (override m k1 v) k2 = v.

    Proof.
      intros.
      subst.
      unfold override.
      rewrite eq_nat_dec_eq.
      reflexivity.
    Qed.


  Lemma override_old_val:
    forall (V: Type) m k k' (v: V),
      (not (k = k'))
      -> (override m k v) k' = m k'.

    Proof.
      intros.
      unfold override.
      rewrite eq_nat_dec_neq.
      reflexivity.
      unfold not. intro. symmetry in H0. apply H in H0. assumption.
    Qed.

  Lemma override_old_val':
    forall (V: Type) m k k' (v: V),
      (not (k' = k))
      -> (override m k v) k' = m k'.

    Proof.
      intros.
      unfold override.
      rewrite eq_nat_dec_neq.
      reflexivity.
      assumption.
    Qed.

    Tactic Notation "simpl_override" :=
      try rewrite override_new_val;
      try (
      (rewrite override_new_val'; [ | assumption]) ||
      (rewrite override_new_val''; [ | assumption]) ||
      (rewrite override_old_val; [ | assumption]) ||
      (rewrite override_old_val'; [ | assumption]));
      simpl.

    Tactic Notation "simpl_override_in" ident(H) :=
      try rewrite override_new_val in H;
      try (
      (rewrite override_new_val'; [ | assumption]) ||
      (rewrite override_new_val''; [ | assumption]) ||
      (rewrite override_old_val in H; [ | assumption]) ||
      (rewrite override_old_val' in H; [ | assumption]));
      simpl in H.

    Lemma simpl_override_test:
      forall (V: Type) m k1 k2 k3 (v: V),
      ((not (k2 = k1))
       /\(not (k1 = k3)))
      -> ((override m k1 v) k1 = v
          /\ (override m k1 v) k2 = m k2
          /\ (override m k1 v) k3 = m k3).

      Proof.
        intros.
        open_conjs.
        split_all.
        
        simpl_override.
        reflexivity.

        simpl_override.
        reflexivity.

        simpl_override.
        reflexivity.

      Qed.

  Definition update_key {V: Set} (m: Key -> V) (k: Key) (v: V): Key -> V :=
    fun (k': Key) =>
      if (key_eq_dec k' k) then v else (m k).

  Definition update_nid {V: Set} (m: NId -> V) (n: NId) (v: V): NId -> V :=
    fun (n': NId) =>
      if (nid_eq_dec n' n) then v else (m n).

  Definition Clock := nat.

End SysPredefs.

(* -------------------------------------------- *)
Section ValSec.
  (* We define these unification across modules. *)
  Import SysPredefs.
  Variable Val: Set.

  Inductive Prog :=
  | put: Key -> Val -> Prog -> Prog
  | get: Key -> (Val -> Prog) -> Prog
  | skip: Prog
  | fault: Prog.

  Inductive ExtLabel :=
  | ext_put_label: NId -> Key -> Val -> ExtLabel
  | ext_get_label: NId -> Key -> Val -> ExtLabel
  | ext_skip_label: ExtLabel
  | ext_fault_label: NId -> ExtLabel.

  Record InstValRec := {
    inst_val_nid: NId;
    inst_val_clock: Clock;
    inst_val_val: Val
  }.
  Definition inst_val := Build_InstValRec.

End ValSec.

Section ValSec2.
  (* We define these unification across modules. *)
  Import SysPredefs.

  Fixpoint prog_map (Val: Set)(p: Prog Val)(n: NId)(c: Clock): Prog (InstValRec Val) :=
    match p with
      | put k v p => 
        put _ k (inst_val _ n (c + 1) v) (prog_map _ p n (c + 1))
      | get k p =>
        get _ k (fun v => prog_map _ (p (inst_val_val _ v)) n c)
      | skip =>
        skip _
      | fault =>
        fault _ 
    end.

End ValSec2.


Module Type SyntaxPar.
  (* Parameter Val: Type. *)
  Parameter Val: Set.
  Parameter init_val: Val.
End SyntaxPar.


(* Module Type Syntax. *)
Module Syntax (SyntaxArg: SyntaxPar).
  Import SysPredefs.
  Export SyntaxArg.

  (*
  Parameter Val: Set.
  Parameter init_val: Val.
  *)

  Definition Prog := Prog Val.
  
  (*
  Inductive Stat :=
  | put: Key -> Val -> Stat
  | get: Key -> Stat
  | skip: Stat.

  Definition Prog := list Stat.
  *)

  Definition PProg := NId -> Prog.

  (*
  Definition is_put (p: Prog) :=
    match p with
    | put _ _ _ => True
    | get _ _ => False
    | skip => False
    end.
  Definition is_get (p: Prog) :=
    match p with
    | put _ _ _ => False
    | get _ _ => True
    | skip => False
    end.
  Definition is_skip (p: Prog) :=
    match p with
    | put _ _ _ => False
    | get _ _ => False
    | skip => True
    end.
  Definition key (p: Prog): option Key :=
    match p with
    | put k _ _ => Some k
    | get k _ => Some k
    | skip => None
    end.
  Definition value (p: Prog): option Val :=
    match p with
    | put _ v _ => Some v
    | get _ _ => None
    | skip => None
    end.
  *)

  Definition is_put (s: Prog) :=
    match s with
    | put _ _ _ => True
    | get _ _ => False
    | skip => False
    | fault => False
    end.
  Definition is_get (s: Prog) :=
    match s with
    | put _ _ _ => False
    | get _ _ => True
    | skip => False
    | fault => False
    end.
  Definition is_skip (s: Prog) :=
    match s with
    | put _ _ _ => False
    | get _ _ => False
    | skip => True
    | fault => False
    end.
  Definition key (s: Prog): option Key :=
    match s with
    | put k _ _ => Some k
    | get k _ => Some k
    | skip => None
    | fault => None
    end.
  Definition value (s: Prog): option Val :=
    match s with
    | put _ v _ => Some v
    | get _ _ => None
    | skip => None
    | fault => None
    end.

  Definition put k v p := put Val k v p.
  Definition get k p := get Val k p.
  Definition skip := skip Val.
  Definition fault := fault Val.

  Definition ExtLabel := ExtLabel Val.
  
End Syntax.

Module InstSyntaxArg (SyntaxArg: SyntaxPar) <: SyntaxPar.
  Import SysPredefs.
  Import SyntaxArg.

  Definition inst_val := inst_val Val.
  Definition inst_val_nid := inst_val_nid Val.
  Definition inst_val_clock := inst_val_clock Val.
  Definition inst_val_val := inst_val_val Val.
  Definition Val := InstValRec Val.
  Definition init_val := inst_val init_nid 0 init_val.

  Definition prog_map (p: Prog SyntaxArg.Val)(n: NId)(c: Clock): Prog Val :=
    prog_map SyntaxArg.Val p n c.

End InstSyntaxArg.

(* -------------------------------------------- *)
Module Type StepStarParams.

  Parameter State: Type.
  Parameter Label: Type.
  Parameter step: State -> Label -> State -> Prop.

End StepStarParams.

Module StepStar (StepStarArgs: StepStarParams).

  Import StepStarArgs.

  Inductive step_star: State -> list Label -> State -> Prop :=
  | refl s: 
      step_star s nil s
  | steps s1 ls s2 l s3: 
      step_star s1 ls s2
      -> step s2 l s3
      -> step_star s1 (ls ++ [l]) s3.

  Definition history (init: State)(ls: list Label): Prop :=
    exists (s: State), step_star init ls s.

  Lemma step_star_end:
    forall s l h s'',
      step_star s (l :: h) s''
      <-> exists s',
           step s l s'
           /\ step_star s' h s''.

    Proof.
      intros.
      split;
      intros.      

      generalize dependent s''.
      induction h using rev_ind.

      intros.
      exists s''.
      split.
      inversion H.
      subst.
      rewrite <- app_nil_l in H0.
      apply app_inj_tail in H0.
      destruct H0; subst.
      inversion H1.
      subst.
      assumption.
      subst.
      apply app_eq_nil in H0.
      destruct H0; subst.     
      inversion H4.
      constructor.

      intros.
      rewrite app_comm_cons in H.
      inversion H.
      rewrite app_comm_cons in H0.
      apply app_inj_tail in H0.
      destruct H0.
      subst.
      apply IHh in H1.
      destruct H1 as [s' [N1 N2]].
      exists s'.
      split.
      assumption.
      econstructor; eassumption.

      (* inverse *)
      generalize dependent s''. 
      induction h using rev_ind.

      intros.
      destruct H as [s' [H1 H2]].
      inversion H2.
      subst.
      clear H2.
      assert (A := steps s nil s l s'').
      depremise A.
      constructor.
      depremise A.
      assumption.
      rewrite app_nil_l in A.
      assumption.

      subst.
      apply app_eq_nil in H.
      destruct H. inversion H3.

      intros.
      destruct H as [s' [H1 H2]].
      remember (h ++ [x]) as hh eqn: Hh.
      destruct H2.
      symmetry in Hh. apply app_eq_nil in Hh.
      destruct Hh.
      subst.
      inversion H0.

      apply app_inj_tail in Hh.
      destruct Hh.
      subst.
      specialize (IHh s2).
      depremise IHh.
      exists s1.
      split.
      assumption.
      assumption.
      rewrite app_comm_cons.
      econstructor; eassumption.      
    Qed.


  Lemma step_star_app:
    forall s h1 h2 s'',
      step_star s (h1 ++ h2) s''
      <-> exists s',
           step_star s h1 s'
           /\ step_star s' h2 s''.

    Proof.
      intros.
      split.

      intros.
      generalize dependent s.
      generalize dependent h2.
      induction h1.
      (* -- *)
      intros.
      rewrite app_nil_l in H.
      exists s.
      split. apply refl. assumption.
      (* -- *)
      intros.
      rewrite <- app_comm_cons in H.
      apply step_star_end in H.
      destruct H as [s' [H1 H2]].
      specialize (IHh1 h2 s').
      depremise IHh1. assumption.
      destruct IHh1 as [sm [IHh1 IHh2]].
      exists sm.
      split. 
        apply step_star_end. exists s'. split; assumption.
        assumption.

      intros.
      generalize dependent s.
      generalize dependent h2.
      induction h1.
      (* -- *)
      intros.
      destruct H as [s' [H1 H2]].
      rewrite app_nil_l.
      inversion H1. 
        subst. assumption.
        subst. destruct ls. rewrite app_nil_l in H. inversion H. inversion H.
      (* -- *)
      intros.
      destruct H as [s' [H1 H2]].
      apply step_star_end in H1.
      destruct H1 as [sm [H11 H12]].
      specialize (IHh1 h2 sm).
      depremise IHh1.
      exists s'. split; assumption.
      rewrite <- app_comm_cons.
      eapply step_star_end.
      exists sm. split; assumption.      

    Qed.


  Lemma step_star_one:
    forall s l s',
      step_star s [l] s'
      <-> step s l s'.

    Proof.
      intros; split; intros.

      inversion H.
      destruct ls.
      subst.
      (* app.*)
      rewrite app_nil_l in H0.
      inversion H0.
      subst.
      inversion H1.
      subst.
      assumption.
      destruct ls.
      rewrite app_nil_l in H2.
      inversion H2.
      inversion H2.
      inversion H0.
      destruct ls.
      rewrite app_nil_l in H7.
      inversion H7.
      inversion H7.

      assert (A : [l] = nil ++ [l]).
      apply app_nil_l.
      rewrite A in *; clear A.
      eapply steps.
      constructor.
      assumption.
    Qed.

  Lemma step_star_app_one:
    forall s h l s'',
      step_star s (h ++ [l]) s''
      <-> exists s',
           step_star s h s'
           /\ step s' l s''.

    Proof.
      intros.
      assert (L := step_star_app).
      specialize (L s h [l] s'').
      split; intros.
      destruct L as [L _].
      depremise L.
      assumption.
      destruct L as [s' [L1 L2]].
      assert (L := step_star_one).
      specialize (L s' l s'').
      destruct L as [L _].
      depremise L.
      assumption.
      exists s'.
      split; assumption.

      destruct L as [_ L].      
      depremise L.
      destruct H as [s' [H1 H2]].
      exists s'.      
      split.
      assumption.
      assert (L := step_star_one).
      specialize (L s' l s'').
      destruct L as [_ L].
      depremise L. assumption.
      assumption.
      assumption.
    Qed.


  Hint Constructors step_star.

End StepStar.


Module AbsExec (SyntaxArg: SyntaxPar).

  Import SysPredefs.
  Import SyntaxArg.
  Module Syntax := Syntax SyntaxArg.
  Import Syntax.

  Record PutId := {
    put_id_nid: NId;
    put_id_clock: Clock
  }.
  Definition put_id := Build_PutId.
  (* Coq represents this constructor much more succinct. *)

  Record TPut := {
    t_put_key: Key;
    t_put_val: Val;
    t_put_dep: list PutId 
  }.
  Definition t_put := Build_TPut.

  Record Entry := {
    entry_val: Val;
    entry_nid: NId;
    entry_clock: Clock;
    entry_dep: list PutId
  }.
  Definition entry := Build_Entry.

  Record NodeState := {
    prog: Prog;
    ptrace: list TPut;
    dep: list PutId;
    rec: NId -> Clock;
    store: Key -> Entry
  }.
  Definition node_state := Build_NodeState.

  Definition State := NId -> NodeState.
  
  Definition dummy_t_put := t_put 0 init_val [put_id init_nid 0].
  (* Definition dummy_t_put := t_put 0 init_val nil. *)
  Definition init (p: PProg): State := 
    fun n => node_state (p n) nil nil (fun n => 0) (fun k => entry init_val init_nid 0 nil).

  Inductive Label :=
  | put_label: NId -> Clock -> Key -> Val -> Label
  | get_label: NId -> Clock -> NId -> Key -> Val -> Label
  | update_label: NId -> Clock -> NId -> Key -> Val -> Label
  | fault_label: NId -> Label.

  Inductive step: State -> Label -> State -> Prop :=
  | put_step: 
      forall s n k v p u d r m,
      let u' := u ++ [(t_put k v d)] in
      let d' := (put_id n (length u')) :: d in
      let r' := override r n ((r n) + 1) in
      let m' := override m k (entry v n (length u') nil) in
      In n nids ->
      step (override s n (node_state (put k v p) u d r m))
           (put_label n (length u') k v)
           (override s n (node_state p u' d' r' m'))

  | get_step: 
      forall s n k p u d r m,
      let v := entry_val (m k) in
      let n'' := entry_nid (m k) in
      let c'' := entry_clock (m k) in
      let d'' := entry_dep (m k) in
      let d' := if eq_nat_dec n'' init_nid then d
                else d ++ [put_id n'' c''] ++ d'' in
      In n nids ->
      step (override s n (node_state (get k p) u d r m))
           (get_label n'' c'' n k v)
           (override s n (node_state (p v) u d' r m))

  | update_step:
      forall s n_1 p_1 u_1 d_1 r_1 m_1 n_2 p_2 u_2 d_2 r_2 m_2,
      let k := t_put_key (nth (r_1 n_2) u_2 dummy_t_put) in
      let v := t_put_val (nth (r_1 n_2) u_2 dummy_t_put) in
      let d := t_put_dep (nth (r_1 n_2) u_2 dummy_t_put) in
      let r_1' := override r_1 n_2 ((r_1 n_2) + 1) in
      let m_1' := override m_1 k (entry v n_2 (r_1' n_2) d) in
      In n_1 nids ->
      not (n_1 = n_2) ->
      r_1 n_2 < length u_2 ->
      Forall (fun pid => put_id_clock pid <= r_1 (put_id_nid pid)) d ->
      step (override (override s
                      n_1 (node_state p_1 u_1 d_1 r_1 m_1))
                      n_2 (node_state p_2 u_2 d_2 r_2 m_2))
           (update_label n_2 (r_1' n_2) n_1 k v)
           (override (override s
                      n_1 (node_state p_1 u_1 d_1 r_1' m_1'))
                      n_2 (node_state p_2 u_2 d_2 r_2 m_2))

  | fault_step: 
      forall s n u d r m,
      In n nids ->
      step (override s n (node_state fault u d r m))
           (fault_label n)
           (override s n (node_state skip u d r m)).


  Module StepStarArgs <: StepStarParams.
    Definition State := State.
    Definition Label := Label.
    Definition step := step.
  End StepStarArgs.
  Module StepStar := StepStar StepStarArgs.
  Export StepStar.

  Definition history := StepStar.history.

  Definition ext (l: Label): ExtLabel :=
    match l with
      | put_label n c k v => ext_put_label _ n k v
      | get_label n' c' n k v => ext_get_label _ n k v
      | update_label n_1 c_1 n_2 k v => ext_skip_label _
      | fault_label n => ext_fault_label _ n
    end.

  Definition ext_hist (h: list Label): list ExtLabel :=
    map ext h.

  Lemma ext_app:
    forall h1 h2,
      ext_hist (h1 ++ h2) = (ext_hist h1) ++ (ext_hist h2).
    
    Proof.
      intros.
      unfold ext_hist.
      apply map_app.
    Qed.


  (*
  Lemma in_dep_in_nid:
    forall p h s,
      step_star (init p) h s
      -> ((forall n pid,
            (In pid (dep (s n))
             -> In (put_id_nid pid) nids))
         /\ (forall n k pid,
               In pid (entry_dep ((store (s n)) k))
               -> In (put_id_nid pid) nids)
         /\ (forall n tput pid,
               (In tput (ptrace (s n))
                /\ In pid (t_put_dep tput))
               -> In (put_id_nid pid) nids)).
                   
    Proof.
      intros.
      remember (init p) as s0 eqn: Hs.
      induction H.

      subst s. simpl in *. split_all. 
      intros; contradiction.
      intros; contradiction.
      intros. open_conjs. contradiction.

      depremise IHstep_star. assumption.
      destruct IHstep_star as [IH1 [IH2 IH3]].
      inversion H0.

      (* put *)
      split_all.

      intros.
      destruct (eq_nat_dec n0 n).
        (* - *)
        subst n0.
        simpl_override_in H5.
        destruct H5.
        subv pid.
        assumption.
        specialize (IH1 n pid).
        subv_in s2 IH1.
        simpl_override_in IH1.
        eapply IH1.
        eassumption.

        (* - *)
        simpl_override_in H5.
        specialize (IH1 n0 pid).
        subv_in s2 IH1.
        simpl_override_in IH1.
        apply IH1.
        assumption.

      intros.
      destruct (eq_nat_dec n0 n).
        (* - *)
        subst n0.
        simpl_override_in H5.
        subv_in m' H5.
        destruct (eq_nat_dec k0 k).
        subst k0.
        simpl_override_in H5.
        contradiction.
        simpl_override_in H5.
        specialize (IH2 n k0 pid).
        subv_in s2 IH2.
        simpl_override_in IH2.
        eapply IH2.
        eassumption.

        (* - *)
        simpl_override_in H5.
        specialize (IH2 n0 k0 pid).
        subv_in s2 IH2.
        simpl_override_in IH2.
        eapply IH2.
        eassumption.                

      intros.
      open_conjs.
      destruct (eq_nat_dec n0 n).
        (* - *)
        subst n0.
        simpl_override_in H5.
        subv_in u' H5.
        apply in_app_iff in H5.
        destruct H5.
        eapply IH3. split.
        subv s2. simpl_override. eassumption.
        assumption.
        simpl in H5. destruct H5; try contradiction.
        rewrite <- H5 in H6; clear H5.
        simpl in H6.
        subv_in d H6.
        eapply IH1.
        subv s2. simpl_override.
        assumption.

        (* - *)
        simpl_override_in H5.
        eapply IH3. split.
        subv s2. instantiate (1 := n0). simpl_override.
        eassumption.
        eassumption.

      (* get *)
      split_all.
      intros.
      destruct (eq_nat_dec n0 n).      
        subst n0.
        simpl_override_in H5.
        subv_in d' H5. apply in_app_iff in H5.
        destruct H5.
        specialize (IH1 n pid).
        subv_in s2 IH1.
        simpl_override_in IH1.
        apply IH1.
        assumption.
        apply in_inv in H5.
        destruct H5.
        subv pid.
        
        subv_in d'' H5.
        eapply IH2.
        subv s2.
        simpl_override.
        eassumption.

        simpl_override_in H5.
        specialize (IH1 n0 pid).
        subv_in s2 IH1.
        simpl_override_in IH1.
        apply IH1.
        assumption.
        
      intros.
      destruct (eq_nat_dec n0 n).      
        subst n.
        simpl_override_in H5.
        specialize (IH2 n0 k0 pid).
        subv_in s2 IH2.
        simpl_override_in IH2.
        eapply IH2.
        eassumption.

        simpl_override_in H5.
        specialize (IH2 n0 k0 pid).
        subv_in s2 IH2.
        simpl_override_in IH2.
        eapply IH2.
        eassumption.

      intros.
      open_conjs.
      destruct (eq_nat_dec n0 n).
        (* - *)
        subst n0.
        simpl_override_in H5.
        eapply IH3. split.
        subv s2. simpl_override. eassumption.
        assumption.

        (* - *)
        simpl_override_in H5.
        eapply IH3. split.
        subv s2. instantiate (1 := n0). simpl_override.
        eassumption.
        eassumption.

      (* update *)
      split_all.
      intros.
      destruct (eq_nat_dec n_1 n).
        (* - *)
        subst n.
        simpl_override_in H8.
        simpl_override_in H8.
        specialize (IH1 n_1 pid).
        subv_in s2 IH1.
        simpl_override_in IH1.
        simpl_override_in IH1.
        eapply IH1. eassumption.

        destruct (eq_nat_dec n_2 n).
        subst n.
        simpl_override_in H8.
        specialize (IH1 n_2 pid).
        subv_in s2 IH1.
        simpl_override_in IH1.
        apply IH1. assumption.
        
        simpl_override_in H8.
        simpl_override_in H8.
        specialize (IH1 n pid).
        subv_in s2 IH1.
        simpl_override_in IH1.
        simpl_override_in IH1.
        apply IH1. assumption.

      intros.
      destruct (eq_nat_dec n_1 n).
        subst n.
        simpl_override_in H8.
        simpl_override_in H8.
        subv_in m_1' H8.
        destruct (eq_nat_dec k0 k).
          subst k0.
          simpl_override_in H8.
          subv_in d H8.
          eapply nth_In in H3. instantiate (1 := dummy_t_put) in H3.       
          specialize (IH3 n_2 (nth (r_1 n_2) u_2 dummy_t_put) pid).
          apply IH3.
          split_all.
          subv s2. simpl_override. assumption.
          assumption.

          (* - *)
          simpl_override_in H8.
          specialize (IH2 n_1 k0 pid).
          apply IH2.
          subv s2.
          simpl_override.
          simpl_override.
          assumption.

        destruct (eq_nat_dec n_2 n).
          subst n.
          simpl_override_in H8.
          specialize (IH2 n_2 k0 pid).
          apply IH2.
          subv s2.
          simpl_override.
          simpl_override.
          assumption.
       
          simpl_override_in H8.
          simpl_override_in H8.
          specialize (IH2 n k0 pid).
          apply IH2.
          subv s2.
          simpl_override.
          simpl_override.
          assumption.

      intros.
      open_conjs.
      destruct (eq_nat_dec n_1 n).
        (* - *)
        subst n_1.
        simpl_override_in H8.
        simpl_override_in H8.
        eapply IH3. split.
        subv s2. instantiate (1 := n). simpl_override. simpl_override. eassumption.
        assumption.

        destruct (eq_nat_dec n_2 n).
        subst n.
        simpl_override_in H8.
        simpl_override_in H8.
        eapply IH3. split.
        subv s2. instantiate (1 := n_2). simpl_override. simpl_override. eassumption.
        assumption.

        simpl_override_in H8.
        simpl_override_in H8.
        eapply IH3. split.
        subv s2. instantiate (1 := n). simpl_override. simpl_override. eassumption.
        assumption.

    Qed.

  



  Lemma no_dummy_t_put:
    forall p h s n,
      step_star (init p) h s
      -> not (In dummy_t_put (ptrace (s n))).

    Proof.
      intros.
      remember (init p) as s0 eqn: Hs.
      induction H.
      
      subv s. intro. contradiction.

      depremise IHstep_star. assumption.
      intro.
      inversion H0.

      subv_in s3 H1.
      destruct (eq_nat_dec n0 n).
        (* - *)
        subst n.
        simpl_override_in H1.
        subv_in u' H1.
        apply in_app_iff in H1.
        destruct H1.
        subv_in s2 IHstep_star.
        simpl_override_in IHstep_star.
        contradiction.

        simpl in H1. destruct H1; try contradiction.
        unfold dummy_t_put in H1.
        inversion H1.
        assert (A := in_dep_in_nid).
        specex_deprem A. subst s1. eassumption.
        destruct A as [A _].
        specex_deprem A.
        subv s2.
        instantiate (1 := n0).
        simpl_override.
        instantiate (1 := put_id init_nid 0).
        subv d.
        left. reflexivity.
        simpl in A.
        apply init_not_in_nids.
        assumption.

        (* - *)
        simpl_override_in H1.
        subv_in s2 IHstep_star.
        simpl_override_in IHstep_star.
        contradiction.

      subv_in s3 H1.
      destruct (eq_nat_dec n0 n).
        (* - *)
        subst n.
        simpl_override_in H1.
        subv_in s2 IHstep_star.
        simpl_override_in IHstep_star.
        contradiction.

        simpl_override_in H1.
        subv_in s2 IHstep_star.
        simpl_override_in IHstep_star.
        contradiction.


      subv_in s3 H1.
      destruct (eq_nat_dec n_1 n).
        (* - *)
        subst n.
        simpl_override_in H1.
        simpl_override_in H1.
        subv_in s2 IHstep_star.
        simpl_override_in IHstep_star.
        simpl_override_in IHstep_star.
        contradiction.

        destruct (eq_nat_dec n_2 n).
        subst n.
        simpl_override_in H1.
        simpl_override_in H1.
        subv_in s2 IHstep_star.
        simpl_override_in IHstep_star.
        simpl_override_in IHstep_star.
        contradiction.

        simpl_override_in H1.
        simpl_override_in H1.
        subv_in s2 IHstep_star.
        simpl_override_in IHstep_star.
        simpl_override_in IHstep_star.
        contradiction.

    Qed.
    *)

  (*
  Fixpoint hist_to_prog (h: list Label): Prog :=
    match h with
      | nil => skip
      | l :: h' => 
        match l with
          | put_label k v => put k v (hist_to_prog h')
          | get_label k v => get k (fun v => (hist_to_prog h'))
        end
    end.

  Fixpoint hist_to_prog (h: list Label): Prog :=
    match h with
    | nil => skip
    | l :: h' => (label_to_prog l) (hist_to_prog h')
    end.

  Definition history (h: list Label) := StepStar.history (init (hist_to_prog h)) h.
  *)



  (*
  Lemma steps_prog_ext:
    forall p m h s' p',
      step_star (state p m) h s'
      -> step_star
           (state (p++p') m)
           h
           (state ((prog s') ++ p') (amap s')).

    Proof.
      intros.
      remember (state p m) as s eqn: Hs. 
      induction H.
      
      subst s.
      simpl.
      constructor.

      depremise IHstep_star. assumption.
      eapply steps.
      eassumption.
      clear Hs H IHstep_star.

      destruct l.
      inversion H0.
      subst.
      simpl.
      constructor.

      inversion H0.
      subst.
      simpl.
      constructor.
      
    Qed.

  Lemma hist_to_prog_split:
    forall h1 h2,
      hist_to_prog (h1 ++ h2) = (hist_to_prog h1) ++ (hist_to_prog h2).

    Proof.
      intros.
      unfold hist_to_prog.
      apply map_app.

    Qed.
  *)

End AbsExec.

(* -------------------------------------------- *)

(*
Module Type AlgDefParams.

  Parameter Val: Set.
  Parameter init_val: Val.

End AlgDefParams.
Module Type AlgDef (AlgDefArgs: AlgDefParams).
*)

Module Type AlgDef.

  Import SysPredefs.
  (* Import AlgDefArgs. *)


  Parameter State: Type -> Type.
  Parameter Update: Type -> Type.


  Section ValParam.

  Variable Val: Type.  

  Parameter dummy_update: Update Val.

  Parameter init_method: Val -> State Val.
  Parameter get_method: NId -> State Val -> Key -> (Val * State Val).
  Parameter put_method: NId -> State Val -> Key -> Val -> (State Val * Update Val).
  Parameter guard_method: NId -> State Val -> Key -> Val -> Update Val -> bool.
  Parameter update_method: NId -> State Val -> Key -> Val -> Update Val -> State Val.

  End ValParam.

  (*
  Print State.
  Print init_method.
  *)

End AlgDef.

Module Type Parametric(AlgDef: AlgDef).
(* Module Type ParametricAlgDef. *)

  (* Include AlgDef. *)
  Import AlgDef.

  Section ParallelWorlds.
    Parameter RState : forall Val1 Val2, (Val1 -> Val2 -> Prop) -> State Val1 -> State Val2 -> Prop.
    Parameter RUpdate : forall Val1 Val2, (Val1 -> Val2 -> Prop) -> Update Val1 -> Update Val2 -> Prop.

    Variables Val1 Val2 : Type.
    Variable R : Val1 -> Val2 -> Prop.

    Axiom init_method_R : forall v1 v2, R v1 v2 -> RState _ _ R (init_method _ v1) (init_method _ v2).

    Axiom get_method_R : forall n s1 s2 k,
      RState _ _ R s1 s2
      -> let (v1', s1') := get_method _ n s1 k in
         let (v2', s2') := get_method _ n s2 k in
         R v1' v2' /\ RState _ _ R s1' s2'.

    Axiom put_method_R : forall n s1 s2 k v1 v2,
      RState _ _ R s1 s2
      -> R v1 v2
      -> let (s1', u1) := put_method _ n s1 k v1 in
         let (s2', u2) := put_method _ n s2 k v2 in
         RState _ _ R s1' s2' /\ RUpdate _ _ R u1 u2.

    Axiom guard_method_R : forall n s1 s2 k v1 v2 u1 u2,
      RState _ _ R s1 s2
      -> R v1 v2
      -> RUpdate _ _ R u1 u2
      -> guard_method _ n s1 k v1 u1 = guard_method _ n s2 k v2 u2.

    Axiom update_method_R : forall n s1 s2 k v1 v2 u1 u2,
      RState _ _ R s1 s2
      -> R v1 v2
      -> RUpdate _ _ R u1 u2
      -> RState _ _ R (update_method _ n s1 k v1 u1) (update_method _ n s2 k v2 u2).
  End ParallelWorlds.

End Parametric.
(* End ParametricAlgDef. *)

(* -------------------------------------------- *)

Module ConcExec (SyntaxArg: SyntaxPar)(Alg: AlgDef).

  Import SysPredefs.
  Import SyntaxArg.
  Module Syntax := Syntax SyntaxArg.
  Import Syntax.


  (*
  Module AlgDefArgs <: AlgDefParams.
    Definition Val := Syntax.Val.
    Definition init_val := Syntax.init_val.
  End AlgDefArgs.
  Module Alg := AlgDef AlgDefArgs.
  Import Alg.
  *)

  Import Alg.

  (* Record Message := message { *)
  Record Message := {
    msg_key: Key;
    msg_val: Val;
    msg_update: Update Val;
    msg_receiver: NId
  }.
  Definition message := Build_Message.

  Definition AlgState := Alg.State Val.
  (* Record NodeState := node_state { *)
  Record NodeState :=  {
    prog_state: Prog;
    alg_state: AlgState
  }.
  Definition node_state := Build_NodeState.

  Definition NodeStates := NId -> NodeState.
  Definition Messages := list Message.

  (* Record State := state { *)
  Record State := {
    node_states: NodeStates;
    messages: Messages
  }.
  Definition state := Build_State.

  Definition init (p: PProg) :=
    state 
      (fun n => (node_state (p n) (init_method Val init_val))) 
      nil.
    (* state (fun n => (node_state (p n) init_method)) nil. *)

  Inductive Label :=
  | put_label: NId -> Key -> Val -> Label
  | get_label: NId -> Key -> Val -> Label
  | update_label: NId -> Key -> Val -> Label
  | fault_label: NId -> Label.

  (*
  Definition override (nss: NodeStates) (n: NId) (ns: NodeState): NodeStates :=
    fun (n': NId) =>
      if (key_eq_dec n' n) then ns else nss(n').
  *)

  Inductive step : State -> Label -> State -> Prop :=
  | put_step: 
      forall (nss: NodeStates)(n: NId)(k: Key)(v: Val)(p: Prog)(s: AlgState)(ms: Messages),
      let r := put_method Val n s k v in
      let s' := fst r in
      let u := snd r in
      In n nids ->
      step (state (override nss n (node_state (put k v p) s)) 
                  ms)
           (put_label n k v)
           (state (override nss n (node_state p s'))
                  (ms ++ (map (fun n' => (message k v u n'))
                              (filter (fun n' => if (nid_eq_dec n n') then false else true) nids))))

  | get_step: 
      forall (nss: NodeStates)(n: NId)(k: Key)(p: Val -> Prog)(s: AlgState)(ms: Messages),
      let r := get_method Val n s k in
      let v' := fst r in
      let s' := snd r in
      In n nids ->
      step (state (override nss n (node_state (get k p) s)) ms)
           (get_label n k v')
           (state (override nss n (node_state (p v') s')) ms)

  | update_step:
      forall (nss: NodeStates)(n: NId)(k: Key)(v: Val)(p: Prog)(s: AlgState)(u: Update Val)(ms1 ms2: Messages),
      In n nids 
      -> guard_method Val n s k v u = true
      -> let s' := update_method Val n s k v u in
         step (state (override nss n (node_state p s)) (ms1 ++ (message k v u n) :: ms2))
              (update_label n k v)
              (state (override nss n (node_state p s')) (ms1 ++ ms2))

  | fault_step: 
      forall (nss: NodeStates)(n: NId)(k: Key)(s: AlgState)(ms: Messages),
      In n nids ->
      step (state (override nss n (node_state fault s)) ms)
           (fault_label n)
           (state (override nss n (node_state skip s)) ms).


  Module StepStarArgs <: StepStarParams.
    Definition State := State.
    Definition Label := Label.
    Definition step := step.
  End StepStarArgs.
  Module StepStar := StepStar StepStarArgs.
  Export StepStarArgs.
  Export StepStar.
  Definition history := StepStar.history.

  Definition ext (l: Label): ExtLabel :=
    match l with
      | put_label n k v => ext_put_label _ n k v
      | get_label n k v => ext_get_label _ n k v
      | update_label n k v => ext_skip_label _
      | fault_label n => ext_fault_label _ n
    end.

  Definition ext_hist (h: list Label): list ExtLabel :=
    map ext h.

  Lemma ext_app:
    forall h1 h2,
      ext_hist (h1 ++ h2) = (ext_hist h1) ++ (ext_hist h2).
    
    Proof.
      intros.
      unfold ext_hist.
      apply map_app.
    Qed.

  Definition eff (l: Label): ExtLabel :=
    match l with
      | put_label n k v => 
        ext_put_label _ n k v
      | get_label n k v => 
        ext_get_label _ n k v
      | update_label n k v => 
        ext_put_label _ n k v
      | fault_label n => 
        ext_fault_label _ n
    end.
  
  Definition eff_hist (h: list Label): list ExtLabel :=
    map eff h.

  Lemma exec_eff_app:
    forall h1 h2,
      eff_hist (h1 ++ h2) = (eff_hist h1) ++ (eff_hist h2).
    
    Proof.
      intros.
      unfold eff_hist.
      apply map_app.
    Qed.

  Definition label_is_put (l: Label): Prop :=
    match l with
      | put_label n k v => True
      | get_label n k v => False
      | update_label n k v => False
      | fault_label n => False
    end.

  Definition label_is_get (l: Label): Prop :=
    match l with
      | put_label n k v => False
      | get_label n k v => True
      | update_label n k v => False
      | fault_label n => False
    end.

  Definition label_is_update (l: Label): Prop :=
    match l with
      | put_label n k v => False
      | get_label n k v => False
      | update_label n k v => True
      | fault_label n => False
    end.

End ConcExec.



(* -------------------------------------------- *)
Module InstConcExec (SyntaxArg: SyntaxPar)(Alg: AlgDef).
(* Module InstConcExec (Syntax: Syntax)(AlgDef: AlgDef). *)

  Import SysPredefs.
  Import SyntaxArg.
  Module InstSyntaxArg := InstSyntaxArg SyntaxArg.
  Module Syntax := Syntax SyntaxArg.
  Import Syntax.

  (*
  Module AlgDefArgs <: AlgDefParams.
    Record InstVal := inst_val {
      inst_val_val: Syntax.Val;
      inst_val_node: NId;
      inst_val_clock: Clock
    }.
    Definition Val := InstVal.
    Definition init_val := inst_val Syntax.init_val 0 0.
  End AlgDefArgs.
  Export AlgDefArgs.
  Definition Val := Syntax.Val.
  Module Alg := AlgDef AlgDefArgs.
  Export Alg.
  *)


  (* Record InstVal := inst_val { *)
  (*
  Record InstVal := {
    inst_val_val: Val;
    inst_val_node: NId;
    inst_val_clock: Clock
  }.
  Definition inst_val := Build_InstVal.
  *)

  Definition Val := SyntaxArg.Val.
  Definition InstVal := InstSyntaxArg.Val.
  Definition inst_val := InstSyntaxArg.inst_val.
  Definition init_inst_val := InstSyntaxArg.init_val.
  Definition inst_val_nid := InstSyntaxArg.inst_val_nid.
  Definition inst_val_clock := InstSyntaxArg.inst_val_clock.
  Definition inst_val_val := InstSyntaxArg.inst_val_val.
  (* inst_val init_val init_nid 0. *)

  Export Alg.

  Definition AlgState := Alg.State InstVal.

  Inductive Label: Type :=
  | put_label: nat -> NId -> Clock -> Key -> Val -> AlgState -> AlgState -> Update InstVal -> Label
  | get_label: nat -> NId -> Clock -> NId -> Key -> AlgState -> AlgState -> Val -> Label
  (* | update_label: nat -> NId -> Clock -> NId -> Key -> Val -> AlgState -> AlgState -> Label. *)
  | update_label: nat -> NId -> Clock -> NId -> Key -> Val -> AlgState -> Message -> AlgState -> Label
  | fault_label: nat -> NId -> AlgState -> AlgState -> Label
  with Message :=
  | message: NId -> Clock -> Key -> Val -> Update InstVal -> NId -> Label -> Message.

  Definition msg_sender (m: Message) :=
    match m with
      | message n c k v u n' l => n
    end.

  Definition msg_clock (m: Message) :=
    match m with
      | message n c k v u n' l => c
    end.

  Definition msg_key (m: Message) :=
    match m with
      | message n c k v u n' l => k
    end.

  Definition msg_val (m: Message) :=
    match m with
      | message n c k v u n' l => v
    end.

  Definition msg_update (m: Message) :=
    match m with
      | message n c k v u n' l => u
    end.

  Definition msg_receiver (m: Message) :=
    match m with
      | message n c k v u n' l => n'
    end.

  Definition msg_label (m: Message) :=
    match m with
      | message n c k v u n' l => l
    end.

  (*
  (* Record Message := message { *)
  Record Message := {
    msg_sender: NId;
    msg_clock: Clock;
    msg_key: Key;
    msg_val: Val;
    msg_update: Update InstVal;
    msg_receiver: NId;
    msg_label: Label
  }.
  Definition message := Build_Message.
  *)

  (* Record NodeState := node_state { *)
  Record NodeState := {
    prog_state: Prog;
    alg_state: AlgState;
    clock_state: Clock
  }.
  Definition node_state := Build_NodeState.

  Definition NodeStates := NId -> NodeState.
  Definition Messages := list Message.

  (* Record State := state { *)
  Record State := {
    node_states: NodeStates;
    messages: Messages;
    latest_label: nat
  }.
  Definition state := Build_State.

  Definition init (p: PProg) :=
    state 
      (fun n => (node_state (p n) (init_method InstVal init_inst_val) 0)) 
      nil
      0.
    (* state (fun n => (node_state (p n) init_method 0)) nil. *)

  (*
  Definition eq_label_dec (l l': Label): {l = l'} + {l <> l'}.
  Proof.
    decide equality.
  Qed.
  *)

  Definition label_is_put (l: Label): Prop :=
    match l with
      | put_label _ n c k v _ s u => True
      | get_label _ n c n' k _ s v => False
      | update_label _ n c n' k v _ _ s => False
      | fault_label _ n _ _ => False
    end.

  Definition label_is_get (l: Label): Prop :=
    match l with
      | put_label _ n c k v s s' u => False
      | get_label _ n c n' k s s' v => True
      | update_label _ n c n' k v s m s' => False
      | fault_label _ n _ _ => False
    end.

  Definition label_is_update (l: Label): Prop :=
    match l with
      | put_label _ n c k v s s' u => False
      | get_label _ n c n' k s s' v => False
      | update_label _ n c n' k v s m s' => True
      | fault_label _ n _ _ => False
    end.

  Definition label_orig_node (l: Label): NId :=
    match l with
      | put_label _ n c k v s s' u => n
      | get_label _ n c n' k s s' v => n
      | update_label _ n c n' k v s m s' => n
      | fault_label _ n _ _ => n
    end.

  Definition label_node (l: Label): NId :=
    match l with
      | put_label _ n c k v s s' u => n
      | get_label _ n c n' k s s' v => n'
      | update_label _ n c n' k v s m s' => n'
      | fault_label _ n _ _ => n
    end.

  Definition label_clock (l: Label): Clock :=
    match l with
      | put_label _ n c k v s s' u => c
      | get_label _ n c n' k s s' v => c
      | update_label _ n c n' k v s m s' => c
      | fault_label _ n _ _ => 0
    end.

  Definition label_key (l: Label): NId :=
    match l with
      | put_label _ n c k v s s' u => k
      | get_label _ n c n' k s s' v => k
      | update_label _ n c n' k v s m s' => k
      | fault_label _ n _ _ => 0
    end.

  Definition label_val (l: Label): Val :=
    match l with
      | put_label _ n c k v s s' u => v
      | get_label _ n c n' k s s' v => v
      | update_label _ n c n' k v s m s' => v
      | fault_label _ n _ _ => init_val
    end.

  Definition label_pre_state (l: Label): AlgState :=
    match l with
      | put_label _ n c k v s s' u => s
      | get_label _ n c n' k s s' v => s
      | update_label _ n c n' k v s m s' => s
      | fault_label _ n s1 s2 => s1
    end.

  Definition label_message (l: Label): Message :=
    match l with
      | put_label _ n c k v s s' u => message 0 0 0 v u 0 l
      | get_label _ n c n' k s s' v => message 0 0 0 v (dummy_update InstVal) 0 l 
      | update_label _ n c n' k v s m s' => m
      | fault_label _ n _ _ => message 0 0 0 init_val (dummy_update InstVal) 0 l 
    end.

  Definition label_post_state (l: Label): AlgState :=
    match l with
      | put_label _ n c k v s s' u => s'
      | get_label _ n c n' k s s' v => s'
      | update_label _ n c n' k v s m s' => s'
      | fault_label _ n s1 s2 => s2
    end.

  Definition label_num (l: Label): nat :=
    match l with
      | put_label no n c k v s s' u => no
      | get_label no n c n' k s s' v => no
      | update_label no n c n' k v s m s' => no
      | fault_label no n s1 s2 => no
    end.


  (*
  Definition override (nss: NodeStates) (n: NId) (ns: NodeState): NodeStates :=
    fun (n': NId) =>
      if (key_eq_dec n' n) then ns else nss(n').
  *)

  Inductive step: State -> Label -> State -> Prop :=
  | put_step: 
      forall (nss: NodeStates)(n: NId)(k: Key)(v: Val)(p: Prog)(s: AlgState)(ms: Messages)(c: Clock)(e: nat),
      let r := put_method InstVal n s k (inst_val n (c+1) v) in
      let s' := fst r in
      let u := snd r in
      let l := (put_label (S e) n (c+1) k v s s' u) in
      In n nids ->
      step (state (override nss n (node_state (put k v p) s c))
                  ms
                  e)
           l
           (state (override nss n (node_state p s' (c+1)))
                  (ms ++ (map (fun n' => (message n (c+1) k v u n' l))
                              (filter (fun n' => if (nid_eq_dec n n') then false else true) nids)))
                  (S e))

  | get_step: 
      forall (nss: NodeStates)(n: NId)(k: Key)(p: Val -> Prog)(s: AlgState)(ms: Messages)(c: Clock)(e: nat),
      let r := get_method InstVal n s k in
      let u := fst r in
      let s' := snd r in
      let v' := InstSyntaxArg.inst_val_val u in
      let n' := InstSyntaxArg.inst_val_nid u in
      let c' := InstSyntaxArg.inst_val_clock u in
      In n nids ->
      step (state (override nss n (node_state (get k p) s c)) ms e)
           (get_label (S e) n' c' n k s s' v')
           (state (override nss n (node_state (p v') s' c)) ms (S e))

  | update_step:
      forall (nss: NodeStates)(n n': NId)(k: Key)(v: Val)(p: Prog)(s: AlgState)(u: Update InstVal)(lp: Label)(ms1 ms2: Messages)(c c': Clock)(e: nat),
      In n nids 
      -> guard_method InstVal n s k (inst_val n' c' v) u = true
      -> let s' := update_method InstVal n s k (inst_val n' c' v) u in
         step (state (override nss n (node_state p s c)) 
                     (ms1 ++ (message n' c' k v u n lp) :: ms2) 
                     e)
              (update_label (S e) n' c' n k v s (message n' c' k v u n lp) s')
              (state (override nss n (node_state p s' c)) 
                     (ms1 ++ ms2)
                     (S e))

  | fault_step: 
      forall (nss: NodeStates)(n: NId)(k: Key)(s: AlgState)(ms: Messages)(c: Clock)(e: nat),
      In n nids ->
      step (state (override nss n (node_state fault s c)) ms e)
           (fault_label (S e) n s s)
           (state (override nss n (node_state (skip) s c)) ms (S e)).


  Module StepStarArgs <: StepStarParams.
    Definition State := State.
    Definition Label := Label.
    Definition step := step.
  End StepStarArgs.
  Module StepStar := StepStar StepStarArgs.
  Export StepStarArgs.
  Export StepStar.
  Definition history := StepStar.history.

  Definition ext (l: Label): ExtLabel :=
    match l with
      | put_label no n c k v s s' u => 
        ext_put_label _ n k v
      | get_label no n' c n k s s' v => 
        ext_get_label _ n k v
      | update_label no n c n' k v s m s' => 
        ext_skip_label _
      | fault_label no n s s' => 
        ext_fault_label _ n
    end.

  Definition ext_hist (h: list Label): list ExtLabel :=
    map ext h.

  Lemma ext_app:
    forall h1 h2,
      ext_hist (h1 ++ h2) = (ext_hist h1) ++ (ext_hist h2).
    
    Proof.
      intros.
      unfold ext_hist.
      apply map_app.
    Qed.

  Lemma msg_label_eq_key_val:
    forall p h s m,
      step_star (init p) h s
      /\ In m (messages s)
      -> (let lp := msg_label m in
          label_is_put lp
          /\ msg_key m = label_key lp
          /\ msg_val m = label_val lp
          /\ msg_sender m = label_node lp
          /\ msg_clock m = label_clock lp
          /\ In lp h).

    Proof.
      intros.
      open_conjs.
      remember (init p) as s0 eqn: Hi.
      induction H.

      subst s.
      simpl in H0.
      contradiction.

      depremise IHstep_star.
      assumption.

      inversion H1.
      rewrite <- H5 in H0.
      simpl in H0.
      apply in_app_iff in H0.
      destruct H0 as [H0 | H0].
      
      depremise IHstep_star.
      rewrite <- H3.
      simpl.
      assumption.
      open_conjs.
      split_all.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
      apply in_app_iff. left. assumption.
      
      apply in_map_iff in H0.
      destruct H0 as [n' [N1 N2]].
      subst lp.
      subst m.
      simpl.
      split_all; [ apply I | reflexivity | reflexivity | reflexivity | reflexivity | apply in_app_iff; right; apply in_eq ].

      rewrite <- H3 in IHstep_star.
      simpl in IHstep_star.
      depremise IHstep_star.
      rewrite <- H5 in H0.
      assumption.
      open_conjs.
      split_all.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
      apply in_app_iff. left. assumption.

      rewrite <- H4 in IHstep_star.
      simpl in IHstep_star.
      depremise IHstep_star.
      rewrite <- H6 in H0.
      simpl in H0.
      apply in_app_iff in H0.
      destruct H0 as [H0 | H0].
      apply in_app_iff.
      left. assumption.
      apply in_app_iff.
      right. apply in_cons. assumption.
      open_conjs.
      split_all.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
      apply in_app_iff. left. assumption.

      depremise IHstep_star.
      subv s2.
      subv_in s3 H0.
      assumption.
      open_conjs.
      split_all; try assumption.
      apply in_app_iff. left. assumption.      

    Qed.


  Hint Rewrite app_length : length.

  Ltac length_contra :=
    match goal with
      | [ H : _ = _ |- _ ] => apply (f_equal _ _ (@length _)) in H;
                             repeat (simpl in H; autorewrite with length in H); omega
    end.

  Lemma rev_cons_invert : forall A (x1 x2 : A) ls1 ls2,
    ls1 ++ [x1] = ls2 ++ [x2]
    -> x1 = x2 /\ ls1 = ls2.
  Proof.
    intros; apply (f_equal _ _ (@rev _)) in H.
    repeat rewrite rev_app_distr in H; simpl in H.
    inversion H; intuition auto using rev_involutive.
    apply (f_equal _ _ (@rev _)) in H2.
    repeat rewrite rev_involutive in *; auto.
  Qed.

  Ltac substs := repeat match goal with
                          | [ x : _ |- _ ] => subst x
                        end.

  Lemma re_override : forall A k m1 (v1 : A) m2 v2 v1' v2',
    override m1 k v1 = override m2 k v2
    -> (v1 = v2 -> v1' = v2')
    -> override m1 k v1' = override m2 k v2'.
  Proof.
    intros; extensionality x; unfold override in *.
    apply (f_equal _ _ (fun f => f x)) in H.
    destruct (x =_? k); auto.
  Qed.

  Definition msgid_inv (s : InstConcExec.State) :=
    NoDup (map (fun m => (msg_sender m, msg_clock m, msg_receiver m)) (messages s))
    /\ Forall (fun m => clock_state (node_states s (msg_sender m)) >= msg_clock m) (messages s).

  Hint Constructors NoDup.

  Hint Rewrite app_nil_r.
        
  Lemma NoDup_app : forall A (ls1 : list A),
    NoDup ls1
    -> forall ls2, NoDup ls2
      -> (forall x, In x ls1 -> ~In x ls2)
      -> NoDup (ls1 ++ ls2).
  Proof.
    induction 1; inversion 1; simpl; intuition (subst; eauto).

    constructor; autorewrite with core; eauto.

    constructor; autorewrite with core; eauto.
    intro HIn.
    apply in_app_or in HIn; simpl in *; intuition (subst; eauto).
  Qed.

  Lemma NoDup_app_bwd : forall A (ls1 ls2 : list A),
    NoDup (ls1 ++ ls2)
    -> NoDup ls1 /\ NoDup ls2 /\ (forall x, In x ls1 -> ~In x ls2).
  Proof.
    induction ls1; simpl; eauto; inversion 1; subst.
    apply IHls1 in H3; intuition (subst; eauto using in_or_app).
    constructor; intuition eauto using in_or_app.
  Qed.

  Lemma NoDup_map_inj : forall A B (f : A -> B),
    (forall x y, f x = f y -> x = y)
    -> forall ls, NoDup ls
      -> NoDup (map f ls).
  Proof.
    induction 2; simpl; eauto.
    constructor; eauto.
    intro.
    apply in_map_iff in H2; firstorder.
    apply H in H2.
    congruence.
  Qed.

  Lemma NoDup_filter : forall A (p : A -> bool) ls,
    NoDup ls
    -> NoDup (filter p ls).
  Proof.
    induction 1; simpl; eauto.
    destruct (p x); eauto.
    constructor; eauto.
    intro.
    apply filter_In in H1; tauto.
  Qed.

  Lemma Forall_app : forall A (P : A -> Prop) ls1,
    Forall P ls1
    -> forall ls2, Forall P ls2
      -> Forall P (ls1 ++ ls2).
  Proof.
    induction 1; simpl; intuition.
  Qed.

  Lemma Forall_app_bwd : forall A (P : A -> Prop) ls1 ls2,
    Forall P (ls1 ++ ls2)
    -> Forall P ls1 /\ Forall P ls2.
  Proof.
    induction ls1; simpl; eauto; inversion 1; subst.
    apply IHls1 in H3; intuition.
  Qed.

  Lemma Forall_impl : forall A (P P' : A -> Prop) ls,
    Forall P ls
    -> (forall x, In x ls -> P x -> P' x)
    -> Forall P' ls.
  Proof.
    induction 1; simpl; intuition.
  Qed.

  Lemma Forall_map : forall A B (f : A -> B) (P : B -> Prop) ls,
    Forall (fun x => P (f x)) ls
    -> Forall P (map f ls).
  Proof.
    induction 1; simpl; auto.
  Qed.
  
  Lemma Forall_filter : forall A (p : A -> bool) (P : A -> Prop) ls,
    Forall (fun x => p x = true -> P x) ls
    -> Forall P (filter p ls).
  Proof.
    induction 1; simpl; auto.
    destruct (p x); auto.
  Qed.

  Hint Resolve nodup_nids.

  Hint Rewrite map_app map_map override_new_val override_old_val using congruence.

  Ltac msgid :=
    repeat (simpl; autorewrite with core);
    repeat ((apply NoDup_app || apply NoDup_map_inj || apply NoDup_filter);
            intuition (try congruence; auto));
    repeat match goal with
             | [ H : _ |- _ ] => apply in_map_iff in H; firstorder subst
             | [ H : _ |- _ ] => apply filter_In in H; firstorder subst
             | [ H : (_, _, _) = (_, _, _) |- _ ] => injection H; clear H; intros; subst
           end.

  Lemma step_msgid_inv:
    forall s1 s2 l,
      step s1 l s2
      -> msgid_inv s1
      -> msgid_inv s2.
  Proof.
    destruct 1; substs; unfold msgid_inv; simpl; intuition.

    msgid.
    
    destruct (nid_eq_dec (msg_sender x) (msg_receiver x)); try discriminate.
    eapply Forall_forall in H2; eauto.
    autorewrite with core in *; simpl in *.
    omega.

    apply Forall_app; auto.
    eapply Forall_impl; [ eassumption | ].
    simpl; intros.
    destruct (nid_eq_dec n (msg_sender x)); subst;
    autorewrite with core in *; simpl in *; auto; omega.

    apply Forall_map; simpl.
    autorewrite with core; simpl.
    apply Forall_forall; auto.
    eapply Forall_impl; [ eassumption | ].
    simpl; intros.
    destruct (nid_eq_dec n (msg_sender x)); subst;
    autorewrite with core in *; simpl in *; auto; omega.

    autorewrite with core in *; simpl in *.
    apply NoDup_app_bwd in H2; intuition.
    inversion_clear H2.
    eapply NoDup_app; eauto.
    simpl in *.
    intuition eauto.

    apply Forall_app_bwd in H3; intuition.
    inversion_clear H4.
    eapply Forall_app; eauto.
    eapply Forall_impl; [ eassumption | ].
    simpl; intros.
    destruct (nid_eq_dec n (msg_sender x)); subst;
    autorewrite with core in *; simpl in *; auto; omega.
    eapply Forall_impl; [ eassumption | ].
    simpl; intros.
    destruct (nid_eq_dec n (msg_sender x)); subst;
    autorewrite with core in *; simpl in *; auto; omega.

    eapply Forall_impl; [ eassumption | ].
    simpl; intros.
    destruct (nid_eq_dec n (msg_sender x)); subst;
    autorewrite with core in *; simpl in *; auto; omega.

  Qed.

  Lemma steps_msgid_inv:
    forall s1 s2 h,
      step_star s1 h s2
      -> msgid_inv s1
      -> msgid_inv s2.
  Proof.
    induction 1; eauto using step_msgid_inv.
  Qed.

  Lemma NoDup_map_middle : forall A B (f : A -> B) x ls2 ls1 x' ls2',
    NoDup (map f (ls1 ++ x :: ls2))
    -> forall ls1', ls1 ++ x :: ls2 = ls1' ++ x' :: ls2'
    -> f x = f x'
    -> ls1 = ls1' /\ ls2 = ls2'.
  Proof.
    induction ls1; simpl; inversion_clear 1; intros.

    destruct ls1'; simpl in *.
    intuition congruence.
    injection H; clear H; intros; subst.
    exfalso; apply H0.
    autorewrite with core; simpl.
    rewrite H2.
    eapply in_or_app; simpl; eauto.

    destruct ls1'; simpl in *.
    injection H; clear H; intros; subst.
    rewrite <- H2 in H0.
    exfalso; apply H0.
    autorewrite with core; simpl.
    eapply in_or_app; simpl; eauto.
    injection H; clear H; intros; subst.
    apply IHls1 in H; eauto.
    intuition congruence.
  Qed.

  Lemma step_det:
    forall s1 s2 l,
      step s1 l s2
      -> msgid_inv s1
      -> forall s3, step s1 l s3
        -> s2 = s3.
  Proof.
    destruct 1; (inversion 2; substs;
      try match goal with
            | [ H' : msgid_inv _, H : _ ++ _ = _ ++ _ |- _ ] =>
              destruct H'; simpl in *;
              symmetry in H; eapply NoDup_map_middle in H; [ | eauto | eauto ]; intuition subst
          end;
      repeat match goal with
               | [ H : _ = _ |- _ ] => rewrite H
             end;
      repeat (eapply re_override; [ solve [ eauto ] | inversion 1; congruence ] || f_equal)).
  Qed.

  Lemma steps_det':
    forall s1 s2 h,
      step_star s1 h s2
      -> msgid_inv s1
      -> forall s3, step_star s1 h s3
        -> s2 = s3.
  Proof. 
    induction 1; inversion 2; intuition subst.
    length_contra.
    length_contra.
    apply rev_cons_invert in H3; intuition subst.
    apply H8 in H4; clear H8; subst.
    eauto using step_det, steps_msgid_inv.
  Qed.

  Lemma init_msgid_inv:
    forall p,
      msgid_inv (init p).
    
    Proof.
      intros.
      unfold msgid_inv.
      simpl.
      split.
      constructor.
      apply Forall_forall.
      intros.
      simpl in H.
      contradiction.
    Qed.

  Lemma steps_det:
    forall p s1 s2 h,
      (step_star (init p) h s1
      /\ step_star (init p) h s2)
      -> s1 = s2.

  Proof. 
    intros.
    destruct H as [H1 H2].
    eapply steps_det'.
    eassumption.
    apply init_msgid_inv.
    eassumption.
  Qed.



  Lemma alg_state_nochange:
    forall s1 l s2 n',
      let n := label_node l in
      let as1 := alg_state (node_states s1 n') in
      let as2 := alg_state (node_states s2 n') in
      (step s1 l s2
      /\ not (n' = n))
      -> as1 = as2.

    Proof.
      intros.
      open_conjs.

      inversion H;

      subst as1;
      subst as2;
      subst s1;
      subst s2;
      simpl;
      subst n;
      subst l;
      simpl in *;
      simpl_override;
      simpl_override;
      reflexivity.
    Qed.

  Definition prec (h: list Label)(l l': Label) :=
    exists h1 h2 h3, 
      h = h1 ++ (l :: h2) ++ (l' :: h3).


  Lemma prec_ext_prec:
    forall h l l' h',
    prec h l l'
    -> prec (h ++ h') l l'.

  Proof.
    intros.    
    unfold prec in H.
    destruct H as [h1 [h2 [h3 H]]].
    exists h1.
    exists h2.
    exists (h3 ++ h').
    rewrite H.
    rewrite app_comm_cons.
    rewrite app_assoc.
    rewrite app_assoc.
    rewrite app_assoc.
    reflexivity.
  Qed.

  Lemma in_prec:
    forall h l l',
      In l h
      -> prec (h++[l']) l l'.

    Proof.
      intros.
      apply in_split in H.
      destruct H as [h1 [h2 H]].
      unfold prec.
      exists h1.
      exists h2.
      exists nil.
      rewrite H.
      rewrite app_assoc.
      reflexivity.

    Qed.

  Lemma prec_in:
    forall (h: list Label)(l l': Label),
      prec h l l'
      -> (In l h /\ In l' h).

    Proof.
      intros.
      unfold prec in H.
      destruct H as [h1 H].
      destruct H as [h2 H].
      destruct H as [h3 H].
      rewrite H.
      split.

      (* Left *)
        simpl.
        apply in_or_app.
        right.
        apply in_eq.

      (* Right *)      
        apply in_or_app.
        right.
        apply in_or_app.
        right.
        apply in_eq.
    Qed.

  Lemma in_exec:
    forall (h: list Label)(s s': State)(l: Label),
      (step_star s h s'
       /\ In l h)
      -> exists (h1: list Label) (s1: State) (s2: State) (h2: list Label),
         (h = h1 ++ l :: h2
          /\ step_star s h1 s1
          /\ step s1 l s2
          /\ step_star s2 h2 s').

    Proof.
      intros.
      destruct H as [H1 H2].

      induction H1.

      inversion H2.

      apply in_app_or in H2.
      destruct H2.

      depremise IHstep_star.
      assumption.
      destruct IHstep_star as [h1 [s3' [s4' [h2 H2]]]].
      open_conjs.
      exists h1.
      exists s3'.
      exists s4'.
      exists (h2 ++ [l0]).
      split_all; try assumption.
      subst ls.
      rewrite app_comm_cons. 
      rewrite app_assoc.
      reflexivity.
      eapply steps; eassumption.

      clear IHstep_star.
      unfold In in H0.
      destruct H0; try contradiction.
      subst.
      exists ls.
      exists s2.
      exists s3.
      exists nil.
      split_all.
      reflexivity.
      assumption.
      assumption.
      constructor.
    Qed.


  Lemma split_exec:
    forall (h1 h2 h3: list Label)(s s': State)(l l': Label),
      step_star s (h1 ++ (l :: h2) ++ (l' :: h3)) s'
      -> exists s1 s2,
         (step_star s h1 s1
         /\ step_star s1 (l :: h2 ++ [l']) s2
         /\ step_star s2 h3 s').

    Proof.
      intros.
      apply step_star_app in H.
      destruct H as [s'' H].
      destruct H as [H1 H2].
      apply step_star_app in H2.
      destruct H2 as [s''' H2].
      destruct H2 as [H2 H3].
      apply step_star_end in H3.
      destruct H3 as [s'''' H3].
      destruct H3 as [H3 H4].
      exists s''.
      exists s''''.
      split.
      assumption.
      split.
      rewrite app_comm_cons.
      eapply steps; eassumption.
      assumption.
    Qed.


  Lemma prec_exec:
    forall (p: PProg)(h: list Label)(s: State)(l l': Label),
      (step_star (init p) h s
      /\ prec h l l')
      -> exists h1 s1 s1' h2 s2' s2 h3,
         step_star (init p) h1 s1
         /\ step s1 l s1'
         /\ step_star s1' h2 s2'
         /\ step s2' l' s2
         /\ step_star s2 h3 s
         /\ h = h1 ++ l :: h2 ++ l' :: h3.

    Proof.
      intros.
      destruct H as [H H'].
      unfold prec in H'.
      destruct H' as [h1 H'].
      destruct H' as [h2 H'].
      destruct H' as [h3 H'].
      rewrite H' in H.
      apply split_exec in H.
      destruct H as [s1 H].
      destruct H as [s2 H].
      open_conjs.
      apply step_star_end in H0.
      destruct H0 as [s1' [H01 H02]].
      apply step_star_app_one in H02.
      destruct H02 as [s2' [H021 H022]].      
      exists h1.
      exists s1.
      exists s1'.
      exists h2.
      exists s2'.
      exists s2.
      exists h3.
      split_all.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
      rewrite H'.
      rewrite app_assoc. 
      rewrite app_comm_cons.
      rewrite app_assoc. 
      reflexivity.

    Qed.


  Lemma label_num_inc:
    forall s l s',
       step s l s'
      -> (latest_label s < label_num l 
          /\ label_num l ≤ latest_label s').
    
    Proof.
      intros.
      inversion H;
      simpl;
      split;
      try apply le_refl; try apply lt_n_Sn.      
    Qed.

  Lemma label_num_steps:
    forall p h s l,
      (step_star (init p) h s
       /\ In l h)
      -> (label_num l <= latest_label s).

    Proof.
      intros.
      destruct H as [N1 N2].
      remember (init p) as s0 eqn: E.
      induction N1.

      unfold In in N2. contradiction.

      depremise IHN1.
      assumption.
      apply in_app_iff in N2.
      destruct N2 as [N2 | N2].
      depremise IHN1.
      assumption.
      subst s1.
      assert (A := label_num_inc s2 l0 s3).
      depremise A. assumption.
      destruct A.
      apply lt_le_weak.
      eapply le_lt_trans. eassumption.
      eapply lt_le_trans; eassumption.

      simpl in N2. destruct N2; try contradiction.
      subst l0.
      clear N1 IHN1.
      assert (A:= label_num_inc s2 l s3 H).
      destruct A.
      assumption.

    Qed.


  Lemma labels_step_unique:
    forall p h s l s',
      (step_star (init p) h s
       /\ step s l s')
      -> not (In l h).

    Proof.
      intros.
      destruct H as [N1 N2].
      intro.
      assert (L1 := label_num_steps p h s l).
      depremise L1.
      split; assumption.
      assert (L2 := label_num_inc s l s'). 
      depremise L2.
      assumption.
      destruct L2 as [L2 L3].
      assert (A: label_num l < label_num l).
      eapply le_lt_trans. apply L1. assumption.
      apply lt_irrefl in A.
      assumption.
    Qed.      

  Lemma labels_unique:
    forall p h s l l',
      (step_star (init p) h s
       /\ prec h l l')
      -> not (l = l').

    Proof.
      intros.
      intro.
      open_conjs.
      subst l'.
      assert (A := prec_exec p h s l l).
      depremise A.
      split. assumption.
      assumption.
      destruct A as [h1 [s1 [s1' [h2 [s2' [s2 [h3 A]]]]]]].
      open_conjs.
      assert (L := labels_step_unique p (h1++l::h2) s2' l s2).
      depremise L.
      split.
      apply step_star_app.
      exists s1.
      split. assumption.
      apply step_star_end.
      exists s1'. split; assumption.
      assumption.
      unfold not in L.
      apply L.
      apply in_app_iff.
      right.
      apply in_eq.      
    Qed.



  Lemma eq_label_dec:
    forall p h s l l',
      (step_star (init p) h s
       /\ In l h
       /\ In l' h)
      -> (l = l') \/ (not (l = l')).

    Proof.
      intros.
      destruct H as [N1 [N2 N3]].
      remember (init p) as s0 eqn: Hs.
      induction N1.

      inversion N2.

      depremise IHN1.
        assumption.

      assert (A := labels_step_unique p ls s2 l0 s3).
      depremise A. subst s1. split; assumption.
      apply in_app_iff in N2.
      apply in_app_iff in N3.
      destruct N2 as [N2 | N2].
        destruct N3 as [N3 | N3].
        (* - *)
        apply IHN1. assumption. assumption.
        (* - *)
        unfold In in N3. destruct N3 as [N3 | N3]; try contradiction. subst l0.
        right. intro. subst. contradiction.
        (* - *)
        destruct N3 as [N3 | N3].
        unfold In in N2. destruct N2 as [N2 | N2]; try contradiction. subst l0.
        right. intro. subst. contradiction.
        (* - *)
        unfold In in N2. destruct N2 as [N2 | N2]; try contradiction.
        unfold In in N3. destruct N3 as [N3 | N3]; try contradiction.
        subst.
        left. assumption.

    Qed.


  Ltac expand :=
    repeat match goal with
             | [ x := _ |- _ ] => subst x
           end.

  Ltac t := simpl in *; subst; expand; intuition; subst; autorewrite with core; intuition.

  Lemma prec_split : forall A h (l : A) x l' x0 l'' x1,
    h ++ [l] = x ++ l' :: x0 ++ l'' :: x1
    -> (x1 = nil /\ l = l'' /\ h = x ++ l' :: x0)
       \/ exists x1', x1 = x1' ++ [l]
                      /\ h = x ++ l' :: x0 ++ l'' :: x1'.
  Proof.
    destruct x1; t.

    rewrite app_comm_cons in *.
    rewrite app_assoc in H. 
    apply app_inj_tail in H; t.

    specialize (@exists_last _ (a :: x1)).
    t.
    firstorder (try congruence).
    rewrite p in H.
    repeat (rewrite app_comm_cons in * || rewrite app_assoc in *).
    apply app_inj_tail in H; t.
    rewrite <- app_assoc.
    simpl; eauto.    
  Qed.

  Lemma prec_pre_in:
    forall p h s l l',
      (step_star (init p) (h ++ [l]) s
      /\ prec (h ++ [l]) l' l)
      -> In l' h.
  Proof.
    unfold prec; firstorder.
    apply prec_split in H0; firstorder (subst; eauto using in_eq, in_or_app).
  Qed.

  Lemma prec_pre_prec:
    forall h l l' l'',
      (prec (h ++ [l]) l' l''
      /\ l <> l'')
      -> prec h l' l''.
  Proof.
    unfold prec; firstorder.
    apply prec_split in H; firstorder.
  Qed.


  Definition msgid_hinv n (h : list Label) :=
    NoDup (map label_num h)
    /\ Forall (fun l => label_num l <= n) h.

  Lemma step_star_NoDup : forall s h s',
    step_star s h s'
    -> msgid_hinv (latest_label s') h.
  Proof.
    induction 1; t.
    split; simpl; auto.
    destruct H0; substs; simpl in *; unfold msgid_hinv in *; simpl in *; intuition.

    msgid.
    eapply Forall_forall in H2; eauto; omega.

    apply Forall_app; auto.
    eapply Forall_impl; [ eassumption | ].
    simpl; intros; omega.

    msgid.
    eapply Forall_forall in H2; eauto; omega.

    eapply Forall_app; auto.
    eapply Forall_impl; [ eassumption | ].
    simpl; intros; omega.

    msgid.
    eapply Forall_forall in H3; eauto; omega.

    apply Forall_app; auto.
    eapply Forall_impl; [ eassumption | ].
    simpl; intros; omega.

    msgid.
    eapply Forall_forall in H2; eauto; omega.

    apply Forall_app; auto.
    eapply Forall_impl; [ eassumption | ].
    simpl; intros; omega.

  Qed.

  Lemma force_split : forall A h' ls' (x : A) h ls,
    h ++ h' = ls ++ x :: ls'
    -> ~In x h'
    -> exists ls'', h = ls ++ x :: ls''.
  Proof.
    induction h; simpl; intuition subst.
    exfalso; apply H0.
    apply in_or_app; simpl; eauto.
    destruct ls; simpl in *.
    injection H; intros; subst; eauto.
    injection H; clear H; intros; subst.
    apply IHh in H; auto.
    firstorder.
    eexists; f_equal; eauto.
  Qed.

  Lemma prec_in_prefix_history:
    forall p h h' s l l',
      step_star (init p) (h ++ h') s
      -> In l' h
      -> prec (h ++ h') l l'
      -> prec h l l'.
    Proof.
      unfold prec; firstorder.
      eapply step_star_NoDup in H.
      destruct H; simpl in *.
      autorewrite with core in *.
      apply NoDup_app_bwd in H; intuition.
      rewrite app_comm_cons in H1.
      rewrite app_assoc in H1.
      eapply force_split in H1.
      Focus 2.
      intro.
      eapply H5.
      eapply in_map_iff; eauto.
      rewrite plus_0_r.
      apply in_map_iff.
      eauto.
      
      firstorder subst.
      rewrite <- app_assoc.
      simpl; eauto.
    Qed.

  Lemma prec_pre_post_in:
    forall p h h' s l l',
      (step_star (init p) (h++ [l'] ++h') s
      /\ prec (h ++ [l'] ++ h') l l')
      -> In l h.

    Proof.
      intros.
      open_conjs.
      rewrite app_assoc in H.
      generalize H; intro Hdup.
      eapply prec_in_prefix_history in Hdup.
      2: apply in_or_app; simpl; eauto.
      2: rewrite <- app_assoc; eauto.
      eapply step_star_NoDup in H.
      destruct H.
      clear H0.
      unfold prec in Hdup; firstorder subst.
      rewrite (app_nil_end (h ++ [l'])) in H0.
      rewrite <- app_assoc in H0.
      rewrite (app_assoc x) in H0.
      autorewrite with core in H.
      apply NoDup_app_bwd in H; intuition.
      eapply NoDup_map_middle in H0.
      2: autorewrite with core; eauto.
      2: auto.
      intuition subst.
      apply in_or_app; simpl; eauto.
    Qed.


  Lemma label_node_in_nids:
    forall p h s l,
      (step_star (init p) h s
       /\ In l h)
      -> let n := label_node l in
         In n nids.
  
    Proof.
      intros.
      open_conjs.
      
      remember (init p) as s0 eqn: Hs.
      induction H.

      simpl in H0. contradiction.

      apply in_app_iff in H0.
      destruct H0.

      depremise IHstep_star.
      assumption.
      depremise IHstep_star.
      assumption.
      assumption.
            
      clear IHstep_star.
      simpl in H0. destruct H0; try contradiction.
      subst l0.
      inversion H1;
      subst n;
      subst l;
      simpl;
      assumption.
    Qed.

  Lemma label_node_not_in_nids:
    forall p h s l,
      (step_star (init p) h s
       /\ In l h)
      -> not (label_node l = init_nid).

    Proof.
      intros.
      intro.
      apply label_node_in_nids in H.
      rewrite H0 in H. clear H0.
      apply init_not_in_nids in H.
      assumption.
    Qed.

  
  Lemma NoDup_app_unique : forall A x (ls : list A), NoDup ls
    -> forall ls1 ls2 ls1' ls2',
         ls = ls1 ++ x :: ls2
         -> ls = ls1' ++ x :: ls2'
         -> ls1 = ls1' /\ ls2 = ls2'.
  Proof.
    induction 1; t; try length_contra;
    repeat match goal with
             | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; clear H; subst
             | [ H : _ :: _ = ?ls ++ _ |- _ ] =>
               destruct ls; t
             | [ H : _ -> False |- _ ] => exfalso; apply H; solve [ eauto using in_eq, in_or_app ]
             | [ H : _ |- _ ] => specialize (IHNoDup _ _ _ _ eq_refl H); intuition congruence
           end; auto.
  Qed.
  
  Hint Constructors NoDup.

  Lemma step_star_latest_label : forall s1 h s2,
    step_star s1 h s2
    -> latest_label s1 <= latest_label s2.
  Proof.
    induction 1; simpl; eauto.
    destruct H0; substs; simpl in *; auto.
  Qed.

  Lemma label_num_steps_lower:
    forall h s s' l,
      step_star s h s'
      -> In l h
      -> latest_label s < label_num l.
  Proof.
    induction 1; t; eauto using le_trans, lt_le_trans.
    apply in_app_or in H1; intuition eauto.
    simpl in *; intuition subst.
    apply label_num_inc in H0; intuition.
    apply step_star_latest_label in H.
    omega.
  Qed.


  Lemma prec_trans:
    forall p h s l l' l'',
      step_star (init p) h s
      -> prec h l l'
      -> prec h l' l''
      -> prec h l l''.
    Proof.
      unfold prec; firstorder subst.
      eapply step_star_NoDup in H.
      destruct H; simpl in H.
      rewrite app_assoc in H1.
      simpl in H1.
      eapply NoDup_map_middle in H1.
      2: rewrite <- app_assoc; eauto.
      2: auto.
      intuition subst.
      simpl.
      exists x.
      exists (x1 ++ l' :: x2).
      exists x4.
      rewrite <- app_assoc.
      auto.
    Qed.

  Lemma label_poststate_state:
    forall (s s': State)(l: Label),
      step s l s'
      ->
      label_post_state l = alg_state (node_states s' (label_node l)).
    
    Proof.
      intros.
      inversion H; clear H;
      simpl in *;
      simpl_override;
      simpl; reflexivity.
    Qed.

  Lemma label_poststate_clock:
    forall (s s': State)(l: Label),
      (step s l s'
       /\ label_is_put l)
      -> label_clock l = clock_state (node_states s' (label_node l)).
    
    Proof.
      intros.
      open_conjs.
      inversion H.

      simpl in *.
      simpl_override.
      simpl. reflexivity.
      
      subst l. unfold label_is_put in H0. contradiction.
      subst l. unfold label_is_put in H0. contradiction.
      subst l. unfold label_is_put in H0. contradiction.
    Qed.

  Lemma put_clock_gtz:
    forall (p: PProg)(h: list Label)(s: State)(l: Label),
      (step_star (init p) h s
       /\ In l h
       /\ label_is_put l)
      -> label_clock l > 0.

    Proof.
      intros.
      open_conjs.
      induction H.
      
      inversion H0.
      
      apply in_app_iff in H0.
      destruct H0.

      apply IHstep_star in H0.
      assumption.

      clear H IHstep_star.
      unfold In in H0. destruct H0; try contradiction.
      subst l0.      
      inversion H2.

      simpl. rewrite Plus.plus_comm. simpl. apply Gt.gt_Sn_O.

      rewrite <- H3 in H1. unfold label_is_put in H1. contradiction.
      rewrite <- H4 in H1. unfold label_is_update in H1. contradiction.      
      rewrite <- H3 in H1. unfold label_is_update in H1. contradiction.      

    Qed.


  Lemma clock_inc:
    forall (h: list Label)(s s': State),
      step_star s h s'
      -> (forall n,
            let c := (clock_state (node_states s n)) in
            let c' := (clock_state (node_states s' n)) in
            c <= c').

    Proof.
      intros.
      induction H.
      
      subst c. subst c'. apply Le.le_refl.

      rename c' into c''.
      pose (c' := clock_state (node_states s2 n)).
      assert (c' <= c'').
      inversion H0.
      
      (* put *)
        subst c'. subst c''. subst s2. subst s3.
        simpl.
        unfold override.
        destruct (eq_nat_dec n n0).
        simpl.
        rewrite Plus.plus_comm.
        simpl.
        apply Le.le_n_Sn.
        apply Le.le_refl.
      
      (* get *)
        subst c'. subst c''. subst s2. subst s3.
        simpl.
        unfold override.
        destruct (eq_nat_dec n n0).
        simpl.
        apply Le.le_refl.
        apply Le.le_refl.


      (* update *)
        subst c'. subst c''. subst s2. subst s3.
        simpl.
        unfold override.
        destruct (eq_nat_dec n n0).
        simpl.
        apply Le.le_refl.
        apply Le.le_refl.


      (* fault *)
        subst c'. subst c''. subst s2. subst s3.
        simpl.
        unfold override.
        destruct (eq_nat_dec n n0).
        simpl.
        apply Le.le_refl.
        apply Le.le_refl.

      eapply le_trans; eassumption.

    Qed.

  Lemma put_inc_clock:
    forall (h: list Label)(s s': State)(l l': Label),
      (step_star s ((l :: h) ++ [l']) s'
       /\ label_is_put l
       /\ label_is_put l'
       /\ label_node l = label_node l')
      -> label_clock l < label_clock l'.

    Proof.
      intros.
      open_conjs.
      apply step_star_app_one in H.
      destruct H as [s2 [M1 M3]].
      apply step_star_end in M1.
      destruct M1 as [s1 [M1 M2]].
      assert (L := clock_inc h s1 s2 M2 (label_node l)).
      simpl in L.

      assert (N1 := label_poststate_clock s s1 l (conj M1 H0)).
      assert (N2 := label_poststate_clock s2 s' l' (conj M3 H1)).
      rewrite N1; clear N1.
      rewrite N2; clear N2.

      rewrite <- H2 in *.
      assert (M : clock_state (node_states s2 (label_node l)) <
                  clock_state (node_states s' (label_node l))).

      inversion M3.
      simpl.
      rewrite <- H4 in H2. simpl in H2. rewrite H2.
      simpl_override.
      simpl_override.
      
      simpl.
      rewrite Plus.plus_comm.
      simpl.
      apply Lt.lt_n_Sn.

      rewrite <- H4 in H1. unfold label_is_put in H1. contradiction.
      rewrite <- H5 in H1. unfold label_is_put in H1. contradiction.
      rewrite <- H4 in H1. unfold label_is_put in H1. contradiction.

      eapply Lt.le_lt_trans; eassumption.

    Qed.


  Lemma put_unique:
    forall (p: PProg)(h: list Label)(s: State)(l l': Label),
      (step_star (init p) h s
       /\ In l h
       /\ In l' h
       /\ label_is_put l
       /\ label_is_put l'
       /\ label_node l = label_node l'
       /\ label_clock l = label_clock l')
      -> l = l'.

    Proof.
      intros.
      open_conjs.
      assert (L := in_exec h (init p) s l (conj H H0)).
      destruct L as [h1 [s1 [s2 [h2 [L1 [L2 [L3 L4]]]]]]].
      assert (L' := in_exec h (init p) s l' (conj H H1)).
      destruct L' as [h1' [s1' [s2' [h2' [L1' [L2' [L3' L4']]]]]]].
      rewrite L1 in H1.
      apply in_app_iff in H1.
      destruct H1 as [H1 | H1].
      (* in left history *)
        exfalso.
        assert (E := in_exec h1 (init p) s1 l' (conj L2 H1)).
        destruct E as [h1'' [s1'' [s2'' [h2'' [E1 [E2 [E3 E4]]]]]]].
        assert (F: step_star s1'' ((l' :: h2'') ++ [l]) s2).
        apply step_star_app.
        exists s1.
        split.
        apply step_star_end.
        exists s2''. split; assumption.
        apply step_star_one. assumption.
        assert (L := put_inc_clock h2'' s1'' s2 l' l). 
        depremise L. split_all. assumption. assumption. assumption. symmetry. assumption.
        rewrite H5 in *.
        apply Lt.lt_irrefl in L. assumption.        

      apply in_inv in H1.
      destruct H1 as [H1 | H1].       
      (* equal *)
        assumption.

      (* in right history *)
        exfalso.
        assert (E := in_exec h2 s2 s l' (conj L4 H1)).
        destruct E as [h1'' [s1'' [s2'' [h2'' [E1 [E2 [E3 E4]]]]]]].
        assert (F: step_star s1 ((l :: h1'') ++ [l']) s2'').
        apply step_star_app.
        exists s1''.
        split.
        apply step_star_end.
        exists s2. split; assumption.
        apply step_star_one. assumption.
        assert (L := put_inc_clock h1'' s1 s2'' l l'). 
        depremise L. split_all. assumption. assumption. assumption. assumption.
        rewrite H5 in *.
        apply Lt.lt_irrefl in L. assumption.
    Qed.


  Lemma no_self_message:
    forall p h s m,
      step_star (init p) h s
      /\ In m (messages s)
      -> (not (msg_sender m = msg_receiver m)).

    Proof.
      intros.
      open_conjs.
      remember (init p) as s0 eqn: Hi.
      induction H.

      subst s.
      simpl in H0.
      contradiction.

      depremise IHstep_star.
      assumption.

      inversion H1.
      rewrite <- H5 in H0.
      simpl in H0.
      apply in_app_iff in H0.
      destruct H0 as [H0 | H0].
      
      depremise IHstep_star.
      rewrite <- H3.
      simpl.
      assumption.
      assumption.
      
      apply in_map_iff in H0.
      destruct H0 as [n' [N1 N2]].
      subst m.
      simpl in *.
      apply filter_In in N2.
      destruct N2 as [N2 N3].
      destruct (nid_eq_dec n n').
      inversion N3.
      assumption.

      rewrite <- H3 in IHstep_star.
      simpl in IHstep_star.
      depremise IHstep_star.
      rewrite <- H5 in H0.
      assumption.
      assumption.

      rewrite <- H4 in IHstep_star.
      simpl in IHstep_star.
      depremise IHstep_star.
      rewrite <- H6 in H0.
      simpl in H0.
      apply in_app_iff in H0.
      destruct H0 as [H0 | H0].
      apply in_app_iff.
      left. assumption.
      apply in_app_iff.
      right. apply in_cons. assumption.
      assumption.

      rewrite <- H3 in IHstep_star.
      simpl in IHstep_star.
      depremise IHstep_star.
      rewrite <- H5 in H0.
      simpl in H0.
      assumption.
      assumption.

    Qed.


  Lemma msg_clock_lte_state_clock:
    forall p h s m,
      let n := msg_sender m in
      let c := msg_clock m in
      step_star (init p) h s
      /\ In m (messages s)
      -> c <= clock_state (node_states s n).

    Proof.
      intros.
      remember (init p) as s0 eqn: Hs.
      destruct H as [N1 N2].
      induction N1.

      subst s.
      simpl in N2.
      contradiction.

      depremise  IHN1. assumption.
      inversion H.

      (* put *)
        subst l0.
        simpl.
        destruct (eq_nat_dec n0 n).

          simpl_override.
          simpl.
          rewrite <- H3 in N2. simpl in N2.
          apply in_app_iff in N2.
          destruct N2 as [N2 | N2].

            depremise IHN1.
              rewrite <- H1. simpl. assumption.
            rewrite <- H1 in IHN1.
            simpl in IHN1. rewrite e0 in IHN1. simpl_override_in IHN1. simpl in IHN1.
            apply le_plus_trans. assumption.

            apply in_map_iff in N2.
            destruct N2 as [tn [N2 _]].
            subst c. rewrite <- N2. simpl.
            apply le_refl.

            simpl_override.
            depremise IHN1.
            rewrite <- H1. simpl.
            rewrite <- H3 in N2. simpl in N2.
            apply in_app_iff in N2.
            destruct N2 as [N2 | N2].
            assumption.
            exfalso.
            apply in_map_iff in N2.
            destruct N2 as [tn [N21 N22]].
            apply filter_In in N22.
            destruct N22 as [_ N22].
            destruct (nid_eq_dec n0 tn).
            inversion N22.
            subst n.
            rewrite <- N21 in n1.
            simpl in n1.
            apply n1. reflexivity.

        
          rewrite <- H1 in IHN1.
          simpl in IHN1.
          simpl_override_in IHN1.
          assumption.
        
      (* get *)
        simpl.
        destruct (eq_nat_dec n0 n).        

          simpl_override.
          simpl.
          depremise IHN1.
          rewrite <- H1.
          simpl.
          rewrite <- H3 in N2.
          simpl in N2.
          assumption.
          rewrite <- H1 in IHN1.
          simpl in IHN1.
          rewrite e0 in IHN1.
          simpl_override_in IHN1.
          simpl in IHN1.
          assumption.

          simpl_override.
          depremise IHN1.
          rewrite <- H1.
          simpl.
          rewrite <- H3 in N2.
          simpl in N2.
          assumption.
          rewrite <- H1 in IHN1.
          simpl in IHN1.
          simpl_override_in IHN1.
          simpl in IHN1.
          assumption.


      (* update *)
        simpl.
        destruct (eq_nat_dec n0 n).        

          simpl_override.
          simpl.
          depremise IHN1.
          rewrite <- H2.
          simpl.
          rewrite <- H4 in N2.
          simpl in N2.
          apply in_app_iff in N2. destruct N2. 
          apply in_app_iff. left. assumption. 
          apply in_app_iff. right. apply in_cons. assumption.
          rewrite <- H2 in IHN1.
          simpl in IHN1.
          rewrite e0 in IHN1.
          simpl_override_in IHN1.
          simpl in IHN1.
          assumption.

          simpl_override.
          depremise IHN1.
          rewrite <- H2.
          simpl.
          rewrite <- H4 in N2.
          simpl in N2.
          apply in_app_iff in N2. destruct N2. 
          apply in_app_iff. left. assumption. 
          apply in_app_iff. right. apply in_cons. assumption.
          rewrite <- H2 in IHN1.
          simpl in IHN1.
          simpl_override_in IHN1.
          simpl in IHN1.
          assumption.

      (* fault *)
        simpl.
        destruct (eq_nat_dec n0 n).        

          subst n.
          subst n0.
          simpl_override.
          depremise IHN1.
          rewrite <- H1.
          simpl.
          rewrite <- H3 in N2.
          simpl in N2.
          assumption.
          subv_in s2 IHN1.
          simpl_override_in IHN1.
          simpl in IHN1.
          assumption.
          
          simpl_override.
          depremise IHN1.
          rewrite <- H1.
          simpl.
          rewrite <- H3 in N2.
          simpl in N2.
          assumption.
          subv_in s2 IHN1.
          simpl_override_in IHN1.
          simpl in IHN1.
          assumption.        
      
    Qed.

  Definition cause_step (h: list Label)(l l': Label) :=
    (prec h l l' /\ label_node l = label_node l'
     /\ ((label_is_get l /\ label_is_put l')
         \/ (label_is_put l /\ label_is_put l')))
    \/ (prec h l l'
        /\ label_is_put l /\ label_is_get l' 
        /\ (label_node l = label_orig_node l') 
        /\ (label_clock l = label_clock l')).

  Inductive cause: list Label -> Label -> Label -> Prop :=
  | cause_cause_step:
      forall (h: list Label)(l l': Label), 
        cause_step h l l'
        -> cause h l l'
  | cause_trans:
      forall (h: list Label)(l l' l'': Label),
        cause h l l'
        -> cause_step h l' l''
        -> cause h l l''.

  Lemma cause_cause_trans:
    forall h l l' l'',
      (cause h l l'
      /\ cause h l' l'')
      -> cause h l l''.

    Proof.
      intros.
      open_conjs.
      induction H0.

      intros.
      eapply cause_trans; eassumption.

      depremise IHcause. assumption.
      eapply cause_trans; eassumption.      

    Qed.      


  Lemma cause_step_ext_cause_step:
    forall h l l' h',
      cause_step h l l'
      -> cause_step (h ++ h') l l'.

    Proof.
      intros.
      unfold cause_step in H.
      unfold cause_step.
      destruct H.

      left.
      open_conjs.
      split_all.
      apply prec_ext_prec. assumption.
      assumption.
      assumption.

      right.
      open_conjs.
      split_all.
      apply prec_ext_prec. assumption.
      assumption.
      assumption.
      assumption.
      assumption.

    Qed.

  Lemma cause_ext_cause:
    forall h l l' h',
    cause h l l'
    -> cause (h ++ h') l l'.

  Proof.
    intros.    
    induction H.

    eapply cause_step_ext_cause_step in H.
    apply cause_cause_step in H.
    eassumption.

    eapply cause_step_ext_cause_step in H0.
    eapply cause_trans.
    eassumption.
    eassumption.

  Qed.



  Lemma cause_prec:
    forall p h s l l',
      (step_star (init p) h s
       /\ cause h l l')
      -> prec h l l'.

    Proof.
      intros.
      open_conjs.
      induction H0.

      unfold cause_step in H0.
      destruct H0; open_conjs; assumption.      

      assert (A: prec h l' l'').
      unfold cause_step in H1.
      destruct H1; open_conjs; assumption.      
      depremise IHcause. assumption.
      eapply prec_trans; eauto.
    Qed.



  Lemma cause_step_in:
    forall h l l',
      cause_step h l l'
      -> (In l h
          /\ In l' h).

    Proof.
      intros.

      unfold cause_step in H;
      destruct H; open_conjs;
      unfold prec in H;
      destruct H as [h1 [h2 [h3 H]]];
      rewrite H;
      split;
      apply in_app_iff;
      right.

      apply in_eq;
      apply in_app_iff;
      right;
      apply in_app_iff;
      right;
      apply in_eq.

      apply in_app_iff.
      right.
      apply in_eq.

      apply in_eq.

      apply in_app_iff.
      right.
      apply in_eq.
    Qed.

  Lemma cause_in:
    forall h l l',
      cause h l l'
      -> (In l h
          /\ In l' h).

    Proof.
      intros.
      open_conjs.
      induction H.
      
      apply cause_step_in. assumption.

      open_conjs.
      split.
      assumption.
      assert (A:= cause_step_in h l' l'' H0).
      open_conjs.
      assumption.
      
      (*
      intros.
      apply cause_prec in H.
      unfold prec in H.
      destruct H as [h1 [h2 [h3 H]]].
      subst h.
      split.
      apply in_app_iff.
      right.
      apply in_app_iff.
      left.
      apply in_eq.
      apply in_app_iff.
      right.
      apply in_app_iff.
      right.
      apply in_eq.
      *)
    Qed.

  Lemma cause_pre_in:
    forall p h l s l',
      (step_star (init p) (h ++ [l]) s
       /\ cause (h ++ [l]) l' l)
      -> In l' h.

    Proof.
      intros.
      destruct H as [N1 N2].
      assert (A1: prec (h ++ [l]) l' l).
      eapply cause_prec.
        split; eassumption.
      unfold prec in A1.
      destruct A1 as [h1 [h2 [h3 A1]]].
      assert (A2: l :: h3 <> nil).
        intro.
        inversion H.
      assert (L := exists_last A2).
      destruct L.
      destruct s0.
      rewrite e in A1.
      clear A2 e.
      rewrite app_assoc in A1.
      rewrite app_assoc in A1.
      apply app_inj_tail in A1.
      destruct A1 as [A1 A2].
      rewrite A1.
      apply in_app_iff.
      left.
      apply in_app_iff.
      right.
      apply in_eq.
    Qed.

  Lemma cause_in_pre_in:
    forall p h l'' s l l',
      (step_star (init p) (h ++ [l'']) s
       /\ In l' h
       /\ cause (h ++ [l'']) l l')
      -> In l h.

    Proof.
      intros.
      open_conjs.
      assert (L := cause_prec p (h++[l'']) s l l').
      depremise L.
      split;
      assumption.

      unfold prec in L.
      destruct L as [h1 [h2 [h3 L]]].
      apply in_split in H0.
      destruct H0 as [h1' [h2' H0]].
      rewrite H0 in L.
      destruct h3.
        rewrite app_assoc in L.
        apply app_inj_tail in L.
        open_conjs.
        rewrite H0.
        rewrite H2.
        apply in_app_iff.
        right.
        apply in_eq.

        assert (A: l0 :: h3 <> nil).
        intro.
        inversion H2.
        assert (M := exists_last A).
        destruct M.
        destruct s0.
        rewrite e in L. clear A e.
        rewrite app_comm_cons in L.
        rewrite app_assoc in L.
        rewrite app_assoc in L.
        apply app_inj_tail in L.
        open_conjs.
        rewrite H0.
        rewrite H2.
        apply in_app_iff.
        left.
        apply in_app_iff.
        right.
        apply in_eq.
    Qed.

  Lemma cause_step_in_prefix_history:
    forall p h l'' s l l',
      (step_star (init p) (h ++ [l'']) s
       /\ In l h
       /\ In l' h
       /\ cause_step (h ++ [l'']) l l')
      -> cause_step h l l'.

    Proof.
      intros.
      open_conjs.
      inversion H2.

      open_conjs.
      unfold cause_step.
      eauto using prec_in_prefix_history.

      open_conjs.
      unfold cause_step.
      eauto 10 using prec_in_prefix_history.
    Qed.


  Lemma cause_in_prefix_history:
    forall p h l'' s l l',
      (step_star (init p) (h ++ [l'']) s
       /\ In l h
       /\ In l' h
       /\ cause (h ++ [l'']) l l')
      -> cause h l l'.

    Proof.
      intros.
      open_conjs.

      remember (h ++ [l'']) as he eqn: Hh.
      induction H2.


      subst h0.
      apply cause_cause_step.
      eapply cause_step_in_prefix_history.
      split_all; eassumption.


      subst h0.
      assert (A: In l' h).
      eapply cause_in_pre_in.
      split_all.
      eassumption.
      apply H1.
      constructor.
      assumption.      

      depremise IHcause.
      reflexivity.
      depremise IHcause.
      assumption.
      depremise IHcause.
      assumption.
      depremise IHcause.
      assumption.
      
      eapply cause_trans.
      eassumption.
      eapply cause_step_in_prefix_history.
      split_all; eassumption.
      
    Qed.


  Lemma cause_prefix_history_one:
    forall p h s l l' l'',
      (step_star (init p) (h ++ [l]) s
       /\ In l'' h
       /\ cause (h ++ [l]) l' l'')
      -> cause h l' l''.

    Proof.
      intros.
      open_conjs.
      assert (A: In l' h).
      eapply cause_in_pre_in.
      split_all; eassumption.

      eapply cause_in_prefix_history.
      split_all; eassumption.

    Qed.

  Lemma cause_pre_cause:
    forall p h s l l' l'',
      (step_star (init p) (h++[l]) s
      /\ cause (h ++ [l]) l' l''
       /\ (not (l = l'')))
      -> cause h l' l''.
    
    Proof.
      intros.
      destruct H as [H1 [H2 H3]].
      
      assert (A1: In l'' h).
        apply cause_in in H2. destruct H2 as [_ H2]. apply in_app_iff in H2. destruct H2. assumption. simpl in H. destruct H; try contradiction.

      eapply cause_prefix_history_one. split_all.
        eassumption. assumption. assumption.      
    Qed.


  Lemma cause_prefix_history:
    forall p h h' s  l l',
      (step_star (init p) (h ++ h') s
       /\ In l' h
       /\ cause (h ++ h') l l')
      -> cause h l l'.

    Proof.
      intros.
      open_conjs.
      generalize dependent s.
      induction h' using rev_ind.

      intros.
      rewrite app_nil_r in H1.
      assumption.

      intros.
      depremise IHh'.      
      eapply cause_prefix_history_one. split_all.
        rewrite <- app_assoc. eassumption.
        apply in_app_iff. left. assumption.
        rewrite <- app_assoc. assumption.

      rewrite app_assoc in H. apply step_star_app in H. destruct H as [s2 [N1 N2]].
      specialize (IHh' s2). depremise IHh'. assumption.

      assumption.
    Qed.

End InstConcExec.



Module SeqExec (SyntaxArg: SyntaxPar).
  Import SysPredefs.
  
  Module Syntax := Syntax SyntaxArg.
  Import Syntax.
  
  Definition Store := Key -> Val.
  Definition State := NId -> Store.

  Definition init: State := 
    fun n k => init_val.

  (*
  Inductive Label :=
  | put_label: NId -> Key -> Val -> Label
  | get_label: NId -> Key -> Val -> Label.
  *)

  Inductive step: State -> ExtLabel -> State -> Prop :=
  | put_step: 
      forall s n st k v,
      step (override s n st)
           (ext_put_label _ n k v)
           (override s n (override st k v))


  | get_step:
      forall s n k st,
      step (override s n st)
           (ext_get_label _ n k (st k))
           (override s n st)

  | fault_step:
      forall s n st,
      step (override s n st)
           (ext_fault_label _ n)
           (override s n st).

  Module StepStarArgs <: StepStarParams.
    Definition State := State.
    Definition Label := ExtLabel.
    Definition step := step.
  End StepStarArgs.
  Module StepStar := StepStar StepStarArgs.
  Export StepStar.

  Definition history := StepStar.history.

End SeqExec.


Module Type CauseObl (AlgDef: AlgDef)(SyntaxArg: SyntaxPar).

  Export SysPredefs.
  Module CExec := ConcExec SyntaxArg AlgDef.
  Import CExec.
  Module SExec := SeqExec SyntaxArg.
  Import SExec.
    
  Parameter ExecToSeqExec:
    forall p h s,
      CExec.StepStar.step_star (CExec.init p) h s
      -> exists h' s',
           SExec.StepStar.step_star (SExec.init) h' s'
           /\ h' = CExec.eff_hist h.

  Module ICExec := InstConcExec SyntaxArg AlgDef.
  (* Module ICExec := ICExec. *)
  Import ICExec.

  Parameter algrec: 
    ICExec.AlgState -> NId -> Clock.

  Parameter algrec_init:
    forall p n n',
      algrec (alg_state (node_states (init p) n)) n' = 0.

  Parameter algrec_step:
    forall p h s l s',
      (ICExec.StepStar.step_star (ICExec.init p) h s
       /\ ICExec.step s l s')
      -> (((ICExec.label_is_get l ->
            let n := ICExec.label_node l in
            forall n',
              algrec (ICExec.alg_state (ICExec.node_states s n)) n' = 
              algrec (ICExec.alg_state (ICExec.node_states s' n)) n'))
          /\ (ICExec.label_is_put l ->
              let n := ICExec.label_node l in
              algrec (ICExec.alg_state (ICExec.node_states s' n)) n = 
              S (algrec (ICExec.alg_state (ICExec.node_states s n)) n)
              /\ forall n', (not (n' = n) ->
                             algrec (ICExec.alg_state (ICExec.node_states s n)) n' = 
                             algrec (ICExec.alg_state (ICExec.node_states s' n)) n'))
          /\ (ICExec.label_is_update l ->
              (let n := ICExec.label_node l in
               let n' := ICExec.label_orig_node l in
               let c' := ICExec.label_clock l in
               S (algrec (ICExec.alg_state (ICExec.node_states s n)) n') = c'
               /\ algrec (ICExec.alg_state (ICExec.node_states s' n)) n' = c'
               /\ (forall n'', not (n'' = label_orig_node l) ->
                               algrec (ICExec.alg_state (ICExec.node_states s n)) n'' = 
                               algrec (ICExec.alg_state (ICExec.node_states s' n)) n'')))).

  Parameter cause_rec:
    forall p h s1 l s2 l',
      let n := label_node l in
      let c := label_clock l in
      let n' := label_node l' in
      let lp := ICExec.msg_label (ICExec.label_message l') in
      (ICExec.StepStar.step_star (ICExec.init p) h s1
       /\ ICExec.step s1 l' s2
       /\ ICExec.label_is_put l
       /\ ICExec.label_is_update l'
       /\ cause h l lp)
      -> c <= algrec (ICExec.alg_state (ICExec.node_states s1 n')) n.

End CauseObl.


Module ExecToAbstExec 
       (AlgDef: AlgDef)
       (Parametric: Parametric AlgDef)
       (CauseObl: CauseObl AlgDef)
       (SyntaxArg: SyntaxPar).

  Import SysPredefs.
  Import AlgDef.
  Module InstSyntaxArg := InstSyntaxArg SyntaxArg.
  Module InstSyntax := Syntax InstSyntaxArg.
  Module Syntax := Syntax SyntaxArg.
  Module I := CauseObl InstSyntaxArg.
  Module N := CauseObl SyntaxArg.

  Module AExec := AbsExec SyntaxArg.
  Module SExec := N.SExec.
  Module SIExec := I.SExec.
  Module CExec := N.CExec.
  Module CIExec := I.CExec.
  Module ICExec := N.ICExec.


Module ExecToInstExec.

  (* Import SysPredefs. *)
  Import SyntaxArg.
  (* Module Syntax := Syntax SyntaxArg. *)
  Import Syntax.
  (* Module Exec := ConcExec SyntaxArg AlgDef. *)
  (* Module Exec := N.CExec. *)
  (* Module InstExec := InstConcExec SyntaxArg AlgDef. *)
  (* 
  Module InstExec := N.IExec.
  Import InstExec.
  *)

  Definition erase_label (l: N.ICExec.Label): N.CExec.Label :=
    match l with
      | N.ICExec.put_label _ n c k v s s' u => 
        N.CExec.put_label n k v
      | N.ICExec.get_label _ n' c n k s s' v => 
        N.CExec.get_label n k v
      | N.ICExec.update_label _ n c n' k v s m s' => 
        N.CExec.update_label n' k v
      | N.ICExec.fault_label _ n s s' => 
        N.CExec.fault_label n
    end.

  Definition erase (h: list N.ICExec.Label): list N.CExec.Label :=
    map erase_label h.

  Lemma erase_app:
    forall h1 h2,
      erase (h1 ++ h2) = (erase h1) ++ (erase h2).
    
    Proof.
      intros.
      unfold erase.
      apply map_app.
    Qed.

  Lemma ext_erase_label:
    forall l,
      N.CExec.ext (erase_label l) = N.ICExec.ext l.
    
    Proof.
      intros.
      destruct l; simpl; reflexivity.     
    Qed.

  Lemma ext_erase:
    forall h,
      N.CExec.ext_hist (erase h) = N.ICExec.ext_hist h.
    
    Proof.
      intros.
      unfold erase.
      induction h.

      simpl. reflexivity.

      simpl.
      rewrite IHh.
      f_equal.
      apply ext_erase_label.
    Qed.

  Import AlgDef.
  Import Parametric.
  (*
  Import AlgDef.
  *)

  Implicit Arguments RState [Val1 Val2].
  Implicit Arguments RUpdate [Val1 Val2].

  Definition R (v1 : N.ICExec.InstVal) (v2 : Val) : Prop :=
    N.ICExec.inst_val_val v1 = v2.

  Inductive Rmessages : N.ICExec.Messages -> N.CExec.Messages -> Prop :=
  | RmNil : Rmessages nil nil
  | RmCons : forall m m' ms ms',
    N.ICExec.msg_key m = N.CExec.msg_key m'
    -> N.ICExec.msg_val m = N.CExec.msg_val m'
    -> RUpdate R (N.ICExec.msg_update m) (N.CExec.msg_update m')
    -> N.ICExec.msg_receiver m = N.CExec.msg_receiver m'
    -> Rmessages ms ms'
    -> Rmessages (m :: ms) (m' :: ms').

  Hint Constructors Rmessages.

  Lemma Rmessages_app : forall ms1 ms2 ms1' ms2',
    Rmessages ms1 ms2
    -> Rmessages ms1' ms2'
    -> Rmessages (ms1 ++ ms1') (ms2 ++ ms2').
  Proof.
    induction 1; simpl; intuition.
  Qed.

  Lemma Rmessages_app_bwd : forall ms2 ms ms1,
    Rmessages ms (ms1 ++ ms2)
    -> exists ms11 ms12, ms = ms11 ++ ms12
                         /\ Rmessages ms11 ms1
                         /\ Rmessages ms12 ms2.
  Proof.
    induction ms; destruct ms1; simpl; inversion 1; subst.
    exists nil; exists nil; eauto.
    exists nil; exists (a :: ms); eauto.
    apply IHms in H8; firstorder subst.
    exists (a :: x); exists x0; eauto.
  Qed.

  Lemma Rmessages_map : forall A f1 f2 (ms : list A),
    (forall x, N.ICExec.msg_key (f1 x) = N.CExec.msg_key (f2 x))
    -> (forall x, N.ICExec.msg_val (f1 x) = N.CExec.msg_val (f2 x))
    -> (forall x, RUpdate R (N.ICExec.msg_update (f1 x)) (N.CExec.msg_update (f2 x)))
    -> (forall x, N.ICExec.msg_receiver (f1 x) = N.CExec.msg_receiver (f2 x))
    -> Rmessages (map f1 ms) (map f2 ms).
  Proof.
    induction ms; simpl; intuition.
  Qed.

  Hint Resolve Rmessages_app Rmessages_map.

  Definition erase_state (s : N.ICExec.State) (s' : N.CExec.State) :=
    (forall n, let ns := N.ICExec.node_states s n in
               let ns' := N.CExec.node_states s' n in
               N.ICExec.prog_state ns = N.CExec.prog_state ns'
               /\ RState R (N.ICExec.alg_state ns) (N.CExec.alg_state ns'))
  /\ Rmessages (N.ICExec.messages s) (N.CExec.messages s').

  Ltac substs := repeat match goal with
                          | [ x : _ |- _ ] => subst x
                        end.

  Lemma R_easy : forall a b c,
    R (N.ICExec.inst_val a b c) c.
  Proof.
    unfold R; auto.
  Qed.

  Hint Resolve R_easy.

  Lemma Erasure'':
    forall s1 l s2,
      N.CExec.step s1 l s2
      -> forall s1', erase_state s1' s1
      -> exists l' s2',
           N.ICExec.step s1' l' s2'
           /\ erase_state s2' s2
           /\ l = erase_label l'.
  Proof.
    destruct 1; substs; destruct s1'; simpl; intuition.

    replace node_states with (override node_states n (N.ICExec.node_state (put k v p) (N.ICExec.alg_state (node_states n)) (N.ICExec.clock_state (node_states n)))).
    do 3 esplit.
    constructor; auto.

    Ltac erase_state := unfold erase_state in *; simpl in *; intuition;
                        try (apply Rmessages_app; auto; apply Rmessages_map; simpl; intuition).

    erase_state.

    Ltac nid_cases :=
      match goal with
      | [ |- context[override _ ?n1 _ ?n2] ] =>
        match n1 with
        | n2 => fail 1
        | _ => destruct (nid_eq_dec n1 n2); subst; intuition;
               try match goal with
                            | [ H : forall n : NId, _ |- _ ] => specialize (H n2)
                   end;
               repeat (autorewrite with core in *; simpl in *; intuition)
        end
      end.
    
    nid_cases.
    nid_cases.

    Ltac use_nid :=
      match goal with
      | [ H : forall n : NId, _ |- context[_ ?n] ] => specialize (H n);
        repeat (simpl in *; autorewrite with core in *; intuition)
    end.

    Ltac put_method :=
      match goal with
      | [ |- context[put_method N.ICExec.InstVal ?n ?s1 ?k ?v1] ] =>
        match goal with
        | [ |- context[put_method Val n ?s2 k ?v2] ] =>
          specialize (put_method_R _ _ R n s1 s2 k v1 v2);
            destruct (put_method N.ICExec.InstVal n s1 k v1),
            (put_method Val n s2 k v2); unfold erase_state in *; simpl in *; destruct 1; intuition; try use_nid; cbv beta;
            try (apply Rmessages_app; auto; apply Rmessages_map; simpl; intuition)
        end
      end.

    put_method.
    put_method.

    erase_state.
    extensionality n0.
    nid_cases.

    Ltac apart :=
      match goal with
      | [ |- N.ICExec.node_state _ _ _ = ?X ] =>
        destruct X; simpl in *; subst; intuition
      end.

    apart.


    (**)
    replace node_states with (override node_states n (N.ICExec.node_state (get k p) (N.ICExec.alg_state (node_states n)) (N.ICExec.clock_state (node_states n)))).
    do 3 esplit.
    constructor; auto.
    erase_state.
    nid_cases.

    f_equal.
    assert (A := get_method_R).
    specialize (A N.ICExec.InstVal Val R n0 (N.ICExec.alg_state (node_states n0)) s k).
    depremise A. assumption.
    destruct (get_method N.ICExec.InstVal n0 (N.ICExec.alg_state (node_states n0)) k).
    destruct (get_method Val n0 s k).
    destruct A as [A _].
    unfold R in A. unfold N.ICExec.inst_val_val in A.
    simpl.
    assumption.

    nid_cases.

    Ltac get_method :=
      match goal with
      | [ |- context[get_method N.ICExec.InstVal ?n ?s1 ?k] ] =>
        match goal with
        | [ |- context[get_method Val n ?s2 k] ] =>
          specialize (get_method_R _ _ R n s1 s2 k);
            destruct (get_method N.ICExec.InstVal n s1 k),
            (get_method Val n s2 k); unfold erase_state in *; simpl in *; destruct 1; intuition; try use_nid
        end
      end.

    get_method. 
    get_method.
    unfold R in H0. unfold N.ICExec.inst_val_val in H0. rewrite H0. reflexivity.

    erase_state.
    extensionality n0.
    nid_cases.
    apart.


    (**)

    generalize H1; destruct 1; simpl in *.
    clear H2.
    apply Rmessages_app_bwd in H3; destruct H3 as [ ? [ ] ]; intuition (subst; simpl in * ).
    inversion_clear H5.
    replace node_states with (override node_states n (N.ICExec.node_state p (N.ICExec.alg_state (node_states n)) (N.ICExec.clock_state (node_states n)))).
    destruct m; simpl in *; subst.
    do 3 esplit.
    constructor; auto.
    erase_state.
    specialize (H3 n); autorewrite with core in *; intuition.
    erewrite guard_method_R; (cbv beta; eauto).

    erase_state.
    nid_cases.
    nid_cases.

    auto using update_method_R.
    
    erase_state.
    extensionality n0.
    subst.
    nid_cases.
    specialize (H5 (N.ICExec.msg_receiver m)); simpl in *; intuition.
    apart.
    autorewrite with core; auto.

    (**)

    generalize H0; destruct 1; simpl in *.
    replace node_states with (override node_states n (N.ICExec.node_state fault (N.ICExec.alg_state (node_states n)) (N.ICExec.clock_state (node_states n)))).
    do 3 esplit.
    constructor; auto.
    erase_state.
    specialize (H3 n); autorewrite with core in *; intuition.   

    erase_state.
    nid_cases.
    nid_cases.
    
    erase_state.
    extensionality n0.
    subst.
    nid_cases.
    specialize (H1 n0).
    open_conjs.        
    apart.
    autorewrite with core; auto.

  Qed.

  Lemma Erasure':
    forall s1 (h: list N.CExec.Label) s2,
      N.CExec.StepStar.step_star s1 h s2
      -> forall s1', erase_state s1' s1
      -> exists (h': list N.ICExec.Label) s2',
           N.ICExec.StepStar.step_star s1' h' s2'
           /\ erase_state s2' s2
           /\ h = erase h'.

  Proof.
    induction 1; simpl; intuition eauto.
    apply IHstep_star in H1; clear IHstep_star; destruct H1 as [ ? [ ] ]; intuition subst.
    generalize H0; intro Hdup.
    eapply Erasure'' in Hdup; eauto.
    destruct Hdup as [ ? [ ] ]; intuition subst.
    do 3 esplit.
    eapply N.ICExec.StepStar.steps; eauto.
    intuition.
    symmetry; apply erase_app.
  Qed.

  Theorem Erasure:
    forall (p: PProg)(h: list N.CExec.Label),
      N.CExec.history (N.CExec.init p) h 
      -> exists (h': list N.ICExec.Label),
           N.ICExec.history (N.ICExec.init p) h' 
           /\ h = erase h'.

  Proof.
    destruct 1.
    eapply Erasure' in H; firstorder subst.
    unfold N.ICExec.history, N.ICExec.StepStar.history.
    eauto.
    auto.
    apply init_method_R; reflexivity.
    constructor.
  Qed.

  Theorem Refinement:
    forall (p: PProg)(h: list N.CExec.Label),
      N.CExec.history (N.CExec.init p) h 
      -> exists (h': list N.ICExec.Label),
           N.ICExec.history (N.ICExec.init p) h' 
           /\ N.CExec.ext_hist h = N.ICExec.ext_hist h'.

    Proof.
      intros.
      apply Erasure in H.
      destruct H as [h' [H1 H2]].
      exists h'.
      split.
      eassumption.
      subv h.
      apply ext_erase.
    Qed.

End ExecToInstExec.



Module InstExecToAbsExec.

  (* Import SysPredefs. *)
  (* Import AlgDef. *)
  (*
  Module InstSyntaxArg := InstSyntaxArg SyntaxArg.
  Module InstSyntax := Syntax InstSyntaxArg.
  *)
  Import InstSyntax.
  (* Module Syntax := Syntax SyntaxArg. *)
  (* Module AExec := AbsExec SyntaxArg. *)
  (*
  Module M := CauseObl InstSyntaxArg.
  Module M' := CauseObl SyntaxArg.
  *)
  (* Module CExec := C.Exec. *)
  (* Module ICExec := InstConcExec SyntaxArg AlgDef. *)
  (* Module SExec := SeqExec InstSyntaxArg. *)


  Definition abs_eff (l: AExec.Label): InstSyntax.ExtLabel :=
    match l with
      | AExec.put_label n c k v => 
        ext_put_label _ n k (InstSyntaxArg.inst_val n c v)
      | AExec.get_label n' c' n k v => 
        ext_get_label _ n k (InstSyntaxArg.inst_val n' c' v)
      | AExec.update_label n' c' n k v => 
        ext_put_label _ n k (InstSyntaxArg.inst_val n' c' v)
      | AExec.fault_label n => 
        ext_fault_label _ n
    end.

  Definition abs_eff_hist (h: list AExec.Label): list InstSyntax.ExtLabel :=
    map abs_eff h.

  Lemma abs_eff_app:
    forall h1 h2,
      abs_eff_hist (h1 ++ h2) = (abs_eff_hist h1) ++ (abs_eff_hist h2).
    
    Proof.
      intros.
      unfold abs_eff_hist.
      apply map_app.
    Qed.

  Definition inst_exec_eff (l: N.ICExec.Label): InstSyntax.ExtLabel :=
    match l with
      | N.ICExec.put_label no n c k v s s' u => 
        ext_put_label _ n k (InstSyntaxArg.inst_val n c v)
      | N.ICExec.get_label no n' c' n k s s' v => 
        ext_get_label _ n k (InstSyntaxArg.inst_val n' c' v)
      | N.ICExec.update_label no n' c' n k v s m s' => 
        ext_put_label _ n k (InstSyntaxArg.inst_val n' c' v)
      | N.ICExec.fault_label no n s s' => 
        ext_fault_label _ n
    end.

  Definition inst_exec_eff_hist (h: list N.ICExec.Label): list InstSyntax.ExtLabel :=
    map inst_exec_eff h.

  Lemma inst_exec_eff_app:
    forall h1 h2,
      inst_exec_eff_hist (h1 ++ h2) = (inst_exec_eff_hist h1) ++ (inst_exec_eff_hist h2).
    
    Proof.
      intros.
      unfold inst_exec_eff_hist.
      apply map_app.
    Qed.

  Definition exec_eff (l: I.CExec.Label): InstSyntax.ExtLabel :=
    match l with
      | I.CExec.put_label n k v => 
        ext_put_label _ n k v
      | I.CExec.get_label n k v => 
        ext_get_label _ n k v
      | I.CExec.update_label n k v => 
        ext_put_label _ n k v
      | I.CExec.fault_label n => 
        ext_fault_label _ n
    end.
  

  Definition exec_eff_hist (h: list I.CExec.Label): list InstSyntax.ExtLabel :=
    map exec_eff h.

  Lemma exec_eff_app:
    forall h1 h2,
      exec_eff_hist (h1 ++ h2) = (exec_eff_hist h1) ++ (exec_eff_hist h2).
    
    Proof.
      intros.
      unfold exec_eff_hist.
      apply map_app.
    Qed.


  Definition msg_map (m: N.ICExec.Message): I.CExec.Message := 
    match m with
      | N.ICExec.message n c k v u n' l => 
        I.CExec.message k (InstSyntaxArg.inst_val n c v) u n'
    end.

  Definition state_map (s: N.ICExec.State): I.CExec.State :=
    I.CExec.state
      (fun n => (I.CExec.node_state
                   (InstSyntaxArg.prog_map
                      (N.ICExec.prog_state (N.ICExec.node_states s n))
                      n
                      (N.ICExec.clock_state (N.ICExec.node_states s n))
                   )
                   (N.ICExec.alg_state (N.ICExec.node_states s n))))
      (map msg_map (N.ICExec.messages s)).

  (*
  Definition prog_struct_map (p: M'.IExec.Syntax.Prog): M.CExec.Syntax.Prog :=
    match p with
      | M'.IExec.Syntax.put k v p => 
        M.CExec.Syntax.put k (InstSyntaxArg.inst_val init_nid 0 v) (prog_struct_map p)
      | M'.IExec.Syntax.get k p =>
        M.CExec.Syntax.get k (fun v => (prog_struct_map (prog_struct_map p (inst_val_val v))))
      | M'.IExec.Syntax.skip =>
          M.CExec.Syntax.skip
    end.
  *)

  Lemma InstExecToExecStep':
    forall s1 l s2,
      N.ICExec.StepStarArgs.step s1 l s2
      -> exists l',
           I.CExec.StepStarArgs.step (state_map s1) l' (state_map s2)
           /\ inst_exec_eff l = exec_eff l'.

    Proof.
      intros.
      inversion H.

      (* put *)
        subst l0.
        pose (l' := (I.CExec.put_label n k (InstSyntaxArg.inst_val n (c + 1) v))).
        exists l'.
        simpl.
        split.
        rewrite H1. rewrite H3.
        unfold I.CExec.StepStarArgs.step.

        assert (A1: state_map s1 =
                   I.CExec.state
                     (override (I.CExec.node_states (state_map s1)) n 
                               (I.CExec.node_state (I.CExec.Syntax.put k (InstSyntaxArg.inst_val n (c + 1) v) (prog_map p n (c + 1))) s))
                     (map msg_map ms)).

          rewrite <- H1 at 1.
          unfold state_map at 1.
          f_equal.
          apply functional_extensionality.
          intro n0.
          destruct (eq_nat_dec n0 n).
          subst n0.
          simpl_override.
          simpl_override.
          f_equal.
          simpl_override.
          simpl_override.
          rewrite <- H1.
          simpl.
          simpl_override.
          reflexivity.

        assert (A2: state_map s2 =
                   I.CExec.state
                     (override (I.CExec.node_states (state_map s1)) n 
                               (I.CExec.node_state (prog_map p n (c + 1)) s'))
                     ((map msg_map ms) ++ (map (fun n' => (I.CExec.message k (InstSyntaxArg.inst_val n (c + 1) v) u n'))
                                               (filter (fun n' => if (nid_eq_dec n n') then false else true) nids)))).
          rewrite <- H3 at 1.
          unfold state_map at 1.
          f_equal.
          apply functional_extensionality.
          intro n0.
          destruct (eq_nat_dec n0 n).
          subst n0.
          simpl_override.
          simpl_override.
          reflexivity.
          simpl_override.
          simpl_override.
          rewrite <- H1.
          simpl.
          simpl_override.
          reflexivity.
          simpl.
          rewrite map_app.
          f_equal.
          rewrite map_map.
          f_equal.

        subv l'.
        rewrite A1.
        rewrite A2.
        constructor.
        assumption.
        unfold Val.
        reflexivity.

      (* get *)
        pose (l' := (I.CExec.get_label n k (InstSyntaxArg.inst_val n' c' v'))).
        exists l'.
        simpl.
        split.
        rewrite H1. rewrite H3.
        unfold I.CExec.StepStarArgs.step.


        assert (A1: state_map s1 =
                   I.CExec.state
                     (override (I.CExec.node_states (state_map s1)) n 
                               (I.CExec.node_state (I.CExec.Syntax.get k (fun v => (prog_map (p (inst_val_val v)) n c))) s))
                     (map msg_map ms)).

          rewrite <- H1 at 1.
          unfold state_map at 1.
          f_equal.
          apply functional_extensionality.
          intro n0.
          destruct (eq_nat_dec n0 n).
          subst n0.
          simpl_override.
          simpl_override.
          f_equal.
          simpl_override.
          simpl_override.
          rewrite <- H1.
          simpl.
          simpl_override.
          reflexivity.

        assert (A2: state_map s2 =
                   I.CExec.state
                     (override (I.CExec.node_states (state_map s1)) n
                               (I.CExec.node_state (prog_map (p (inst_val_val (InstSyntaxArg.inst_val n' c' v'))) n c) s'))
                     (map msg_map ms)).
          rewrite <- H3 at 1.
          unfold state_map at 1.
          f_equal.
          apply functional_extensionality.
          intro n0.
          destruct (eq_nat_dec n0 n).
          subst n0.
          simpl_override.
          simpl_override.
          reflexivity.
          simpl_override.
          simpl_override.
          rewrite <- H1.
          simpl.
          simpl_override.
          reflexivity.

        assert (A3: get_method N.ICExec.InstVal n s k = ((inst_val n' c' v'), s')).
          subv n'. subv c'. subv v'. subv s'. subv u. subv r.
          destruct (get_method N.ICExec.InstVal n s k).
          simpl. f_equal. destruct i. simpl. reflexivity.
        assert (A4: inst_val n' c' v' = fst (get_method N.ICExec.InstVal n s k)).
          rewrite A3. reflexivity.
        assert (A5: s' = snd (get_method N.ICExec.InstVal n s k)).
          rewrite A3. reflexivity.          
        subv l'.
        rewrite A1.
        rewrite A2.
        rewrite A4.
        rewrite A5.       
        constructor.
        assumption.
        unfold Val.
        reflexivity.
        
      (* update *)
        pose (l' := (I.CExec.update_label n k (InstSyntaxArg.inst_val n' c' v))).
        exists l'.
        simpl.
        split.
        rewrite H2. rewrite H4.
        unfold I.CExec.StepStarArgs.step.

        assert (A1: state_map s1 =
                   I.CExec.state
                     (override (I.CExec.node_states (state_map s1)) n 
                               (I.CExec.node_state (prog_map p n c) s))
                     ((map msg_map ms1) ++ (I.CExec.message k (N.ICExec.inst_val n' c' v) u n) :: (map msg_map ms2))).

          rewrite <- H2 at 1.
          unfold state_map at 1.
          f_equal.
          apply functional_extensionality.
          intro n0.
          destruct (eq_nat_dec n0 n).
          subst n0.
          simpl_override.
          simpl_override.
          f_equal.
          simpl_override.
          simpl_override.
          rewrite <- H2.
          simpl.
          simpl_override.
          reflexivity.
          simpl.
          rewrite map_app.
          f_equal.


        assert (A2: state_map s2 =
                   I.CExec.state
                     (override (I.CExec.node_states (state_map s1)) n 
                               (I.CExec.node_state (prog_map p n c) s'))
                     ((map msg_map ms1) ++ (map msg_map ms2))).

          rewrite <- H4 at 1.
          unfold state_map at 1.
          f_equal.
          apply functional_extensionality.
          intro n0.
          destruct (eq_nat_dec n0 n).
          subst n0.
          simpl_override.
          simpl_override.
          reflexivity.
          simpl_override.
          simpl_override.
          rewrite <- H2.
          simpl.
          simpl_override.
          reflexivity.
          simpl.
          rewrite map_app.
          reflexivity.

        assert (A3: s' = update_method Val n s k (inst_val n' c' v) u).
          subv s'. reflexivity.

        subv l'.
        rewrite A1.
        rewrite A2.
        rewrite A3.
        constructor.
        assumption.
        assumption.
        unfold Val.
        reflexivity.
        
      (* fault *)
        pose (l' := (I.CExec.fault_label n)).
        exists l'.
        simpl.
        split.
        rewrite H1. rewrite H3.
        unfold I.CExec.StepStarArgs.step.

        assert (A1: state_map s1 =
                   I.CExec.state
                     (override (I.CExec.node_states (state_map s1)) n 
                               (I.CExec.node_state I.CExec.Syntax.fault s))
                     (map msg_map ms)).

          rewrite <- H1 at 1.
          unfold state_map at 1.
          f_equal.
          apply functional_extensionality.
          intro n0.
          destruct (eq_nat_dec n0 n).
          subst n0.
          simpl_override.
          simpl_override.
          f_equal.
          simpl_override.
          simpl_override.
          rewrite <- H1.
          simpl.
          simpl_override.
          reflexivity.

        assert (A2: state_map s2 =
                   I.CExec.state
                     (override (I.CExec.node_states (state_map s1)) n 
                               (I.CExec.node_state I.CExec.Syntax.skip s))
                     (map msg_map ms)).
          rewrite <- H3 at 1.
          unfold state_map at 1.
          f_equal.
          apply functional_extensionality.
          intro n0.
          destruct (eq_nat_dec n0 n).
          subst n0.
          simpl_override.
          simpl_override.
          simpl.
          reflexivity.
          simpl_override.
          simpl_override.
          rewrite <- H1.
          simpl.
          simpl_override.
          reflexivity.

        subv l'.
        rewrite A1.
        rewrite A2.
        constructor.
        assumption.
        assumption.
        unfold Val.
        reflexivity.

    Qed.

  Lemma InstExecToExec':
    forall h s1 s2,
      N.ICExec.StepStar.step_star s1 h s2
      -> exists h',
           I.CExec.StepStar.step_star (state_map s1) h' (state_map s2)
           /\ inst_exec_eff_hist h = exec_eff_hist h'.

    Proof.
      intros.
      generalize dependent s2.
      generalize dependent s1.
      induction h as [ | l h].

      intros.
      exists nil.
      split.
      inversion H.
      subst s.
      subst s2.
      constructor.
      apply nil_cons_end in H0.
      contradiction.
      simpl. reflexivity.
      

      intros.
      rename s2 into s3.
      apply N.ICExec.StepStar.step_star_end in H.
      destruct H as [s2 [N1 N2]].
      specex_deprem IHh. eassumption.
      clear N2.
      destruct IHh as [h' [IHh1 IHh2]].
      assert (A := InstExecToExecStep').
      specex_deprem A. eassumption.
      destruct A as [l' [A1 A2]].
      exists (l'::h').
      split.
      apply I.CExec.StepStar.step_star_end.
      eexists. split; eassumption.
      simpl.
      f_equal; assumption.
    Qed.


  Lemma InstExecToExec:
    forall p h s,
      N.ICExec.StepStar.step_star (N.ICExec.init p) h s
      -> exists p' h' s',
           I.CExec.StepStar.step_star (I.CExec.init p') h' s'
           /\ inst_exec_eff_hist h = exec_eff_hist h'.

    Proof.
      intros.
      assert (A := InstExecToExec').
      specex_deprem A. eassumption.
      destruct A as [h' [A1 A2]].
      exists (fun n => prog_map (p n) n 0).
      exists h'.
      exists (state_map s).
      split; assumption.
    Qed.


  Lemma InstExecToSeqExec:
    forall p h s,
      N.ICExec.StepStar.step_star (N.ICExec.init p) h s
      -> exists h' s',
           I.SExec.StepStar.step_star (I.SExec.init) h' s'
           /\ h' = inst_exec_eff_hist h.

    Proof.
      intros.
      apply InstExecToExec in H.
      destruct H as [p' [h' [s' [H1 H2]]]].
      apply I.ExecToSeqExec in H1.
      destruct H1 as [h'' [s'' [H11 H12]]].
      exists h''. exists s''.
      split.
      assumption.      
      eapply eq_trans. eassumption. symmetry. assumption.
    Qed.

  
  Lemma AbsExecSeqExecStore:
    forall p h s s' n k, 
      (AExec.StepStar.step_star (AExec.init p) h s
       /\ I.SExec.StepStar.step_star (I.SExec.init) (abs_eff_hist h) s')
      -> (AExec.entry_nid ((AExec.store (s n)) k) = inst_val_nid (s' n k)
          /\ AExec.entry_clock ((AExec.store (s n)) k) = inst_val_clock (s' n k)
          /\ AExec.entry_val ((AExec.store (s n)) k) = inst_val_val (s' n k)).
    
    Proof.
      intros.
      destruct H as [H1 H2].
      remember (AExec.init p) as s0.
      generalize dependent s'.
      induction H1.

      intros.
      subst s.
      simpl in H2.
      inversion H2.
      subst s'.
      simpl.
      split_all; reflexivity.
      apply nil_cons_end in H.
      contradiction.

      intro s3'. intros.
      depremise IHstep_star.
      assumption.
      rewrite abs_eff_app in H2.
      apply I.SExec.StepStar.step_star_app_one in H2.
      destruct H2 as [s2' [H21 H22]].
      specex_deprem IHstep_star.
      eassumption.
      destruct IHstep_star as [N1 [N2 N3]].
      clear H1 H21.
      inversion H.

      (* put *)
        subv_in l H22.
        inversion H22.
        subst n1. subst k1.
        destruct (eq_nat_dec n0 n).
        subst n.
        
          simpl_override.
          simpl_override.
          subv m'.
          destruct (eq_nat_dec k0 k).

            subv k.
            simpl_override.
            simpl_override.
            split_all; reflexivity.

            simpl_override.
            simpl_override.
            subv_in s2 N1. subv_in s2 N2. subv_in s2 N3.
            subv_in s2' N1. subv_in s2' N2. subv_in s2' N3.
            simpl_override_in N1. simpl_override_in N1.
            simpl_override_in N2. simpl_override_in N2.
            simpl_override_in N3. simpl_override_in N3.
            split_all; assumption.

          simpl_override.
          simpl_override.
          subv_in s2 N1. subv_in s2 N2. subv_in s2 N3.
          subv_in s2' N1. subv_in s2' N2. subv_in s2' N3.
          simpl_override_in N1. simpl_override_in N1.
          simpl_override_in N2. simpl_override_in N2.
          simpl_override_in N3. simpl_override_in N3.
          split_all; assumption.

      (* get *)
        subv_in l H22.
        inversion H22.
        subst n1. subst k1.
        destruct (eq_nat_dec n0 n).
        subst n.
        
          simpl_override.
          simpl_override.
          subv_in s2 N1. subv_in s2 N2. subv_in s2 N3.
          subv_in s2' N1. subv_in s2' N2. subv_in s2' N3.
          simpl_override_in N1. simpl_override_in N1.
          simpl_override_in N2. simpl_override_in N2.
          simpl_override_in N3. simpl_override_in N3.
          split_all; assumption.

          simpl_override.
          simpl_override.
          subv_in s2 N1. subv_in s2 N2. subv_in s2 N3.
          subv_in s2' N1. subv_in s2' N2. subv_in s2' N3.
          simpl_override_in N1. simpl_override_in N1.
          simpl_override_in N2. simpl_override_in N2.
          simpl_override_in N3. simpl_override_in N3.
          split_all; assumption.

      (* update *)
        subv_in l H22.
        inversion H22.
        subst n0. subst k1.
        subst m_1'.
        destruct (eq_nat_dec n_1 n).
        subst n.
        
          simpl_override.
          simpl_override.
          destruct (eq_nat_dec k0 k).

            subv k.
            simpl_override.
            simpl_override.
            split_all; reflexivity.

            simpl_override.
            simpl_override.
            subv_in s2 N1. subv_in s2 N2. subv_in s2 N3.
            subv_in s2' N1. subv_in s2' N2. subv_in s2' N3.
            simpl_override_in N1. simpl_override_in N1.
            simpl_override_in N2. simpl_override_in N2.
            simpl_override_in N3. simpl_override_in N3.
            split_all; assumption.


          destruct (eq_nat_dec n_2 n).

            subst n.
            simpl_override.
            simpl_override.
            subv_in s2 N1. subv_in s2 N2. subv_in s2 N3.
            subv_in s2' N1. subv_in s2' N2. subv_in s2' N3.
            simpl_override_in N1. simpl_override_in N1.
            simpl_override_in N2. simpl_override_in N2.
            simpl_override_in N3. simpl_override_in N3.
            split_all; assumption.

            simpl_override.
            simpl_override.
            simpl_override.
            subv_in s2 N1. subv_in s2 N2. subv_in s2 N3.
            subv_in s2' N1. subv_in s2' N2. subv_in s2' N3.
            simpl_override_in N1. simpl_override_in N1. simpl_override_in N1.
            simpl_override_in N2. simpl_override_in N2. simpl_override_in N2.
            simpl_override_in N3. simpl_override_in N3. simpl_override_in N3.
            split_all; assumption.

      (* fault *)
        subv_in l H22.
        inversion H22.
        subst n1.
        destruct (eq_nat_dec n0 n).
        subst n.
        
          simpl_override.
          simpl_override.
          subv_in s2 N1. subv_in s2 N2. subv_in s2 N3.
          subv_in s2' N1. subv_in s2' N2. subv_in s2' N3.
          simpl_override_in N1. simpl_override_in N1.
          simpl_override_in N2. simpl_override_in N2.
          simpl_override_in N3. simpl_override_in N3.
          split_all; assumption.

          simpl_override.
          simpl_override.
          subv_in s2 N1. subv_in s2 N2. subv_in s2 N3.
          subv_in s2' N1. subv_in s2' N2. subv_in s2' N3.
          simpl_override_in N1. simpl_override_in N1.
          simpl_override_in N2. simpl_override_in N2.
          simpl_override_in N3. simpl_override_in N3.
          split_all; assumption.

    Qed.


  Definition label_map (l: N.ICExec.Label): AExec.Label :=
    match l with
      | N.ICExec.put_label _ n' c' k v _ s u => AExec.put_label n' c' k v
      | N.ICExec.get_label _ n' c' n k _ s v => AExec.get_label n' c' n k v
      | N.ICExec.update_label _ n' c' n k v _ _ s => AExec.update_label n' c' n k v
      | N.ICExec.fault_label _ n s s' => AExec.fault_label n
    end.

  Definition hist_map (h: list N.ICExec.Label): list AExec.Label :=
    map label_map h.

  Lemma ext_label_map:
    forall l,
      AExec.ext (label_map l) = N.ICExec.ext l.
    
    Proof.
      intros.
      destruct l; simpl; reflexivity.     
    Qed.

  Lemma ext_hist_map:
    forall h,
      AExec.ext_hist (hist_map h) = N.ICExec.ext_hist h.
    
    Proof.
      intros.
      unfold hist_map.
      induction h.

      simpl. reflexivity.

      simpl.
      rewrite IHh.
      f_equal.
      apply ext_label_map.
    Qed.

  Lemma eff_label_map:
    forall l,
      abs_eff (label_map l) = inst_exec_eff l.
    
    Proof.
      intros.
      destruct l; simpl; reflexivity.     
    Qed.

  Lemma eff_hist_map:
    forall h,
      abs_eff_hist (hist_map h) = inst_exec_eff_hist h.

    Proof.
      intros.
      unfold hist_map.
      induction h.

      simpl. reflexivity.

      simpl.
      rewrite IHh.
      f_equal.
      apply eff_label_map.
    Qed.
                                               
  Lemma hist_map_app:
    forall h1 h2,
      hist_map (h1 ++ h2) = (hist_map h1) ++ (hist_map h2).
    
    Proof.
      intros.
      unfold hist_map.
      apply map_app.
    Qed.

  Lemma Refinement':
    forall p h s,
      N.ICExec.StepStar.step_star (N.ICExec.init p) h s
      -> exists h' s',
           AExec.StepStar.step_star (AExec.init p) h' s'

           /\ h' = hist_map h
              (* InstExec.ext_hist h = AbsExec.ext_hist h' *)

           /\ (forall n,
                 N.ICExec.clock_state (N.ICExec.node_states s n) =
                 length (AExec.ptrace (s' n)))

           /\ (forall n,
                 N.ICExec.prog_state (N.ICExec.node_states s n) =
                 AExec.prog (s' n))

           /\ (forall m c,
                 let n' := N.ICExec.msg_sender m in
                 let c' := N.ICExec.msg_clock m in
                 let k := N.ICExec.msg_key m in
                 let v := N.ICExec.msg_val m in
                 (In m (N.ICExec.messages s)
                  /\ S c = c'
                 -> let tp := nth c (AExec.ptrace (s' n')) AExec.dummy_t_put in
                    (AExec.t_put_key tp = k
                     /\ AExec.t_put_val tp = v)))

           /\ (forall n pid,
                 let d := AExec.dep (s' n) in
                 let n' := AExec.put_id_nid pid in
                 let c' := AExec.put_id_clock pid in
                 In pid d
                 -> (exists l' l,
                       N.ICExec.label_node l = n
                       /\ N.ICExec.label_is_get l
                       /\ N.ICExec.label_is_put l'
                       /\ N.ICExec.label_node l' = n'
                       /\ N.ICExec.label_clock l' = c'
                       /\ N.ICExec.cause h l' l)
                    \/ (exists l, 
                          N.ICExec.label_node l = n
                          /\ N.ICExec.label_node l = n'
                          /\ N.ICExec.label_clock l = c'
                          /\ N.ICExec.label_is_put l
                          /\ In l h))

           /\ (forall l i n' c',
                 let n := N.ICExec.label_node l in
                 let c := N.ICExec.label_clock l in
                 let d  := AExec.t_put_dep (nth i (AExec.ptrace (s' n)) AExec.dummy_t_put) in
                 (N.ICExec.label_is_put l
                  /\ In l h
                  /\ S i = c
                  /\ i < length (AExec.ptrace (s' n))
                  /\ In (AExec.put_id n' c') d)
                 -> exists l', 
                      (N.ICExec.label_is_put l'
                       /\ N.ICExec.label_node l' = n'
                       /\ N.ICExec.label_clock l' = c'
                       /\ N.ICExec.cause h l' l))        

           /\ (forall n n',
                 N.algrec (N.ICExec.alg_state (N.ICExec.node_states s n)) n' =
                 AExec.rec (s' n) n')

           /\ (forall n k n' c',
                 let n'' := AExec.entry_nid ((AExec.store (s' n)) k) in
                 let c'' := AExec.entry_clock ((AExec.store (s' n)) k) in
                 not (n'' = init_nid) ->
                 exists l,
                   N.ICExec.label_is_put l
                   /\ N.ICExec.label_node l = n''
                   /\ N.ICExec.label_clock l = c''
                   /\ In l h
                   /\ let d'' := AExec.entry_dep ((AExec.store (s' n)) k) in
                      In (AExec.put_id n' c') d''
                      -> (exists l',
                            N.ICExec.label_is_put l'
                            /\ N.ICExec.label_node l' = n' 
                            /\ N.ICExec.label_clock l' = c'
                            /\ N.ICExec.cause h l' l)).

    Proof.
      intros.
      remember (N.ICExec.init p) as s0 eqn: Hs.
      induction H as [s | s1 h s2 l s3].
      
      (* Base case *)
        exists nil.
        exists (AExec.init p).
        subst s.
        split_all.
        constructor.
        simpl. reflexivity.
        intros. reflexivity.
        intros. simpl. reflexivity.
        intros. simpl in H. open_conjs. contradiction.
        intros. subst d. simpl in *. contradiction.

        intros. open_conjs. subst d.
        assert (A := nth_in_or_default).
        specialize (A AExec.TPut i (AExec.ptrace (AExec.init p n)) AExec.dummy_t_put).
        destruct A as [A | A].
        simpl in A. contradiction.
        eapply nth_In in H2. instantiate (1 := AExec.dummy_t_put) in H2.
        rewrite A in H2; clear A.
        exfalso.
        simpl in H2.
        assumption.
        intros. simpl.
        assert (A := N.algrec_init).
        specex A. 
        instantiate (3 := p) in A.
        instantiate (2 := n) in A.
        instantiate (1 := n') in A.
        simpl in A.
        assumption.
        intros. exfalso. subst n''. simpl in H. apply H. reflexivity.

      (* Inductive case *)
        depremise IHstep_star. assumption.
        destruct IHstep_star as [h' [s' [N1 [N2 [N3 [N4 [N5 [N6 [N7 [N8 N9]]]]]]]]]].
        inversion H0.

        (* put *)
          subst l0.
          pose (ptrace := AExec.ptrace (s' n)).
          pose (dep := AExec.dep (s' n)).
          pose (rec := AExec.rec (s' n)).
          pose (store := AExec.store (s' n)).
          pose (ptrace' := ptrace ++ [(AExec.t_put k v dep)]).
          pose (dep' := (AExec.put_id n (length ptrace')) :: dep).
          pose (rec' := override rec n (rec n + 1)).
          pose (store' := override store k (AExec.entry v n (length ptrace') nil)).
          exists (h' ++ [AExec.put_label n (length ptrace') k v]).
          exists (override s' n (AExec.node_state p0 ptrace' dep' rec' store')).
          split_all.
          
          (* --- *)
            clear N2 N3 N5 N6 N7 N8 N9.
            eapply AExec.StepStar.steps. eassumption.
            assert (A: s' = override s' n (AExec.node_state (AExec.Syntax.put k v p0) ptrace dep rec store)).
              apply functional_extensionality. intros.
              destruct (eq_nat_dec x n). 
                
                subst x. simpl_override.
                specialize (N4 n). rewrite <- H2 in N4. simpl in N4. simpl_override_in N4. simpl in N4.
                destruct (s' n).
                simpl in N4.
                subst ptrace. subst dep. subst rec. subst store. subst prog. simpl.
                reflexivity.
                
                simpl_override. reflexivity.

            rewrite A at 1. clear A.
            econstructor.
            assumption.

          (* --- *)
            clear N1 N4 N5 N6 N7 N8 N9.
            rewrite N2.
            rewrite hist_map_app.
            simpl.
            f_equal.
            f_equal.
            f_equal.
            unfold ptrace'.
            unfold ptrace.
            rewrite app_length.
            simpl.
            f_equal.
            specex N3.
            instantiate (1 := n) in N3.
            subv_in s2 N3.
            simpl_override_in N3.
            symmetry. assumption.

          (* --- *)
            clear N1 N2 N4 N5 N6 N7 N8.
            intro.
            simpl.
            destruct (eq_nat_dec n0 n).

              simpl_override.
              simpl_override.
              specialize (N3 n).
              subv_in s2 N3.
              simpl_override_in N3.
              subv c. subv ptrace'.
              rewrite app_length.
              simpl.
              reflexivity.

              simpl_override.
              simpl_override.
              specialize (N3 n0).
              subv_in s2 N3.
              simpl_override_in N3.
              assumption.

          (* --- *)
            intros.
            simpl.
            destruct (eq_nat_dec n0 n).

            simpl_override.
            simpl_override.
            simpl.
            reflexivity.

            simpl_override.
            simpl_override.
            specialize (N4 n0). rewrite <- H2 in N4. simpl in N4. simpl_override_in N4.
            assumption.

          (* --- *)
            clear N1 N2 N4 N6 N7 N8.
            intros.
            simpl in H5.
            destruct H5 as [N1 N2].
            apply in_app_iff in N1.
            destruct N1 as [N1 | N1].

              specialize (N5 m c0).
              simpl in N5.
              depremise N5. split.
                subv s2. assumption. assumption.             
              destruct N5 as [N51 N52].
              subst n'. remember (N.ICExec.msg_sender m) as n'.
              subst c'. remember (N.ICExec.msg_clock m) as c'.
              subst k0. remember (N.ICExec.msg_key m) as k0.
              subst v0. remember (N.ICExec.msg_val m) as v0.
              subst tp.
              destruct (eq_nat_dec n n').

                (* -- *)
                rewrite <- e0 in N51.
                rewrite <- e0 in N52.
                simpl_override.                
                subst ptrace'.
                subst ptrace.
                specialize (N3 n).
                rewrite <- H2 in N3.
                simpl in N3.
                simpl_override_in N3.
                assert (A := N.ICExec.msg_clock_lte_state_clock p h s2 m). 
                  simpl in A.
                  depremise A. split.
                  subst s1. assumption.
                  rewrite <- H2. simpl. assumption.
                rewrite <- H2 in A.
                simpl in A.
                subv_in n A.
                subv_in n' A.
                simpl_override_in A.
                subst c'. remember (N.ICExec.msg_clock m) as c'.
                rewrite <- N2 in A; clear N2.
                subv_in c A.
                apply le_S_gt in A.
                split.
                rewrite <- N51. apply f_equal. eapply app_nth1. assumption.
                rewrite <- N52. apply f_equal. eapply app_nth1. assumption.

                (* -- *)
                simpl_override.
                split; assumption.

              (* - *)              
              apply in_map_iff in N1.
              destruct N1 as [tn [N11 N12]].
              subst tp.
              subst n'.
              rewrite <- N11.
              simpl.
              simpl_override.
              subst ptrace'.
              subst ptrace.
              subst c'.
              subv_in m N2.
              rewrite Plus.plus_comm in N2. simpl in N2.
              apply eq_add_S in N2.
              subst c0.
              specialize (N3 n).
              rewrite <- H2 in N3.
              simpl in N3.
              simpl_override_in N3.
              simpl in N3.
              split.
              rewrite app_nth2. rewrite N3. rewrite minus_diag. simpl. subv k0. subv m. reflexivity. subv c. apply le_refl.
              rewrite app_nth2. rewrite N3. rewrite minus_diag. simpl. subv v0. subv m. reflexivity. subv c. apply le_refl.
              
          (* --- *)
            clear N1 N2 N4 N5 N7 N8.
            intros.
            subst d.
            destruct (eq_nat_dec n0 n).
            
              (* - *)
              subst n0.
              simpl_override_in H5.
              simpl in H5.
              destruct H5 as [H5 | H5].

                (* - *)
                right.
                exists l.
                split_all.
                subst l. simpl. reflexivity.
                subst l. simpl. subst n'. subst pid. simpl. reflexivity.
                subst l. simpl. subst c'. subst pid. simpl. 
                subst rec.
                specialize (N3 n).
                rewrite <- H2 in N3.
                simpl in N3.
                simpl_override_in N3.
                simpl in N3.
                rewrite N3.
                unfold ptrace'.
                unfold ptrace.
                rewrite app_length.
                simpl.
                reflexivity.
                subst l. simpl. apply I.
                subst l. apply in_app_iff. right. apply in_eq.

                (* - *)
                specialize (N6 n pid).
                simpl in N6.
                subst dep.
                apply N6 in H5. clear N6.                
                destruct H5.
                destruct H5 as [l1 [l2 H5]]. open_conjs. left. exists l1. exists l2. subst n'. subst c'. split_all; try assumption. apply N.ICExec.cause_ext_cause. assumption.
                destruct H5 as [l1 H5]. open_conjs. right. exists l1. subst n'. subst c'. split_all; try assumption. apply in_app_iff. left. assumption.

              (* - *)
              simpl_override_in H5.
              specialize (N6 n0 pid).
              simpl in N6.
              depremise N6. subst dep. assumption.
              destruct N6 as [N6 | N6].
              destruct N6 as [l1 [l2 N6]]. open_conjs. left. exists l1. exists l2. subst n'. subst c'. split_all; try assumption. apply N.ICExec.cause_ext_cause. assumption.
              destruct N6 as [l1 N6]. open_conjs. right. exists l1. subst n'. subst c'. split_all; try assumption. apply in_app_iff. left. assumption.
                
          (* --- *)
            clear N1 N2 N4 N5 N8.

            intros l' i n' c'.
            intros.
            destruct H5 as [M1 [M2 [M3 [M4 M5]]]].
            subst d.
            destruct (eq_nat_dec n n0).

            (* - *)
            subst n0.
            rewrite <- e0 in M4.
            rewrite <- e0 in M5.
            simpl_override_in M4.
            simpl_override_in M5.
            subv_in ptrace' M4.
            rewrite app_length in M4.
            simpl in M4.
            rewrite Plus.plus_comm in M4. simpl in M4.
            apply lt_n_Sm_le in M4.
            apply le_lt_eq_dec in M4.
            destruct M4 as [M4 | M4].

              (* - *)
              specialize (N7 l' i n' c').
              simpl in N7.
              depremise N7. split_all.
                assumption.
                apply in_app_iff in M2. destruct M2 as [M2 | M2]. assumption. exfalso. simpl in M2. destruct M2 as [M2 | M2]; try contradiction. unfold c0 in M3. rewrite <- M2 in M3. simpl in M3. rewrite Plus.plus_comm in M3. simpl in M3. apply eq_add_S in M3. subst i. subv_in ptrace M4. specex N3. instantiate (1 := n) in N3. subv_in s2 N3. simpl_override_in N3. rewrite N3 in M4. eapply NPeano.Nat.lt_irrefl. eassumption.
                assumption.
                subv_in ptrace M4. subv_in n M4. assumption.              
                subv_in ptrace' M5. rewrite app_nth1 in M5. subv_in ptrace M5. subv_in n M5. assumption. assumption.
              destruct N7 as [l'' N7].
              open_conjs.
              exists l''. split_all; try assumption. apply N.ICExec.cause_ext_cause. assumption.
              
              (* - *)
              rewrite H3 in M2.
              subv_in ptrace M4.
              specex N3. instantiate (1 := n) in N3. 
              subv_in s2 N3. simpl_override_in N3.
              rewrite <- N3 in M4. subst i.
              assert (A := N.ICExec.put_unique).
                specex_deprem A.
                split_all.
                subst s1. instantiate (1 := s3). eapply N.ICExec.StepStar.step_star_app_one. eexists. split. eassumption. eassumption.
                apply in_app_iff. right. apply in_eq.
                eassumption.
                subv l. apply I.
                eassumption.
                subv l. eassumption.
                subv l. subst c0. rewrite plus_comm. simpl. eassumption.
              rewrite <- A in *.

              subv_in ptrace' M5.
              rewrite app_nth2 in M5.
              subv_in c M5.
              rewrite minus_diag in M5.
              simpl in M5.
              subv_in dep M5.
              specex N6. simpl in N6. depremise N6.
              eassumption.
              destruct N6 as [N6 | N6].

                (* - *)
                destruct N6 as [l_1 [l_2 N6]].
                open_conjs.
                simpl in H8.
                simpl in H9.
                exists l_1.
                split_all.
                assumption.
                assumption.
                assumption.
                rewrite H3.
                assert (B: N.ICExec.cause (h++[l]) l_2 l).
                  apply N.ICExec.cause_in in H10. destruct H10 as [_ H10].
                  constructor.
                  unfold N.ICExec.cause_step.
                  left. split_all.
                  eapply N.ICExec.in_prec. assumption.
                  rewrite H5. assumption.
                  left. split; assumption.
                  eapply N.ICExec.cause_ext_cause in H10. instantiate (1 := [l]) in H10.
                eapply N.ICExec.cause_cause_trans. split; eassumption.

                (* - *)
                destruct N6 as [l_1 N6].
                open_conjs.
                simpl in H6.
                simpl in H7.
                exists l_1.
                split_all; try assumption.
                rewrite H3.
                constructor.
                unfold N.ICExec.cause_step.
                left. split_all.
                eapply N.ICExec.in_prec. assumption.
                subst l. simpl. assumption.
                right. split; assumption.

                subv ptrace.
                subv c.
                apply le_refl.
              
            (* - *)
            simpl_override_in M4.
            simpl_override_in M5.
            specialize (N7 l' i n' c').
            simpl in N7.
            depremise N7. split_all.
              assumption.
              apply in_app_iff in M2. destruct M2 as [M2 | M2]. assumption. exfalso. simpl in M2. destruct M2 as [M2 | M2]; try contradiction. 
              apply n1. subv n0. subv l'. reflexivity.
              assumption.
              assumption.
              subst n0. subst c0. assumption.
            destruct N7 as [l'' N7].
            open_conjs.
            exists l''. split_all; try assumption. apply N.ICExec.cause_ext_cause. assumption.

          (* --- *)
            clear N1 N2 N4 N5 N6 N7.
            intros n1 n2.
            intros.
            simpl.
            destruct (eq_nat_dec n n1).
            
              (* - *)
              subst n1.
              simpl_override.
              simpl_override.
              unfold rec.
              assert (A := N.algrec_step).
              specex_deprem A.
                subst s1. split; eassumption.
                destruct A as [_ [A _]].
                depremise A. subst l. simpl. apply I.
                simpl in A.
                destruct A as [A1 A2].                
                specialize (A2 n2).
                subv_in l A1.
                subv_in l A2.
                subv_in s2 A1.
                subv_in s2 A2.
                subv_in s3 A1.
                subv_in s3 A2.
                simpl_override_in A1.
                simpl_override_in A1.
                simpl_override_in A2.
                simpl_override_in A2.
              specex N8.
                instantiate (2 := n) in N8.
                instantiate (1 := n2) in N8.
                subv_in s2 N8.
                simpl_override_in N8.
              unfold rec'.
              unfold rec.
              destruct (eq_nat_dec n n2).
              
              subst n2.
              simpl_override.
              rewrite Plus.plus_comm. simpl. 
              rewrite <- N8.
              rewrite <- A1.
              reflexivity.

              simpl_override.
              rewrite <- N8.
              symmetry. apply A2. apply not_eq_sym. assumption.

              (* - *)
              simpl_override.
              simpl_override.

              specex N8.
                instantiate (2 := n1) in N8.
                instantiate (1 := n2) in N8.
                subv_in s2 N8.
                simpl_override_in N8.
              assumption.

          (* --- *)
            clear N1 N2 N4 N5 N6 N7 N8.
            rewrite H3 in *.            
            intros.

            destruct (eq_nat_dec n0 n).

              
              destruct (eq_nat_dec k k0).

                exists l.
                split_all.              
                subst l. simpl. apply I.
                subst l. simpl. subst n''. simpl_override. unfold store'. simpl_override. reflexivity.
                subst l. simpl. subv c''. simpl_override. unfold store'. simpl_override. 
                unfold ptrace'. unfold ptrace. rewrite app_length. simpl. f_equal. 
                specex N3. instantiate (2 := n0) in N3. subv_in s2 N3. rewrite e0 in N3. simpl_override_in N3. assumption.
                apply in_app_iff. right. apply in_eq.
                intros.
                subv_in d'' H6.
                exfalso.
                rewrite e0 in H6.
                simpl_override_in H6.
                unfold store' in H6.
                rewrite e1 in H6.
                simpl_override_in H6.
                assumption.

                specialize (N9 n k0 n' c').
                simpl in N9.
                depremise N9. subv_in n'' H5. rewrite e0 in H5. simpl_override_in H5. unfold store' in H5. simpl_override_in H5. unfold store in H5. assumption.
                destruct N9 as [l1 N9]. open_conjs. exists l1. split_all; try assumption. 
                subv n''. simpl_override. unfold store'. simpl_override. assumption. 
                subv c''. simpl_override. unfold store'. simpl_override. assumption. 
                apply in_app_iff. left. assumption.
                intros.
                depremise H10. subv_in d'' H11. rewrite e0 in H11. simpl_override_in H11. unfold store' in H11. simpl_override_in H11. unfold store in H11. assumption.                
                destruct H10 as [l2 H10]. open_conjs. exists l2. split_all; try assumption.
                apply N.ICExec.cause_ext_cause. assumption.

              simpl_override_in H5.
              specialize (N9 n0 k0 n' c').
              simpl in N9.
              depremise N9. subv_in n'' H5. simpl_override_in H5. assumption.
              destruct N9 as [l1 N9]. open_conjs. exists l1. split_all; try assumption. 
              subv n''. simpl_override. unfold store'. simpl_override. assumption. 
              subv c''. simpl_override. unfold store'. simpl_override. assumption. 
              apply in_app_iff. left. assumption.
              intros.
              depremise H10. subv_in d'' H11. simpl_override_in H11. assumption.
              destruct H10 as [l2 H10]. open_conjs. exists l2. split_all; try assumption.
              apply N.ICExec.cause_ext_cause. assumption.


        (* get *)
          pose (ptrace := AExec.ptrace (s' n)).
          pose (dep := AExec.dep (s' n)).
          pose (rec := AExec.rec (s' n)).
          pose (store := AExec.store (s' n)).
          pose (val := AExec.entry_val (store k)).
          pose (n'' := AExec.entry_nid (store k)).
          pose (c'' := AExec.entry_clock (store k)).
          pose (dep'' := AExec.entry_dep (store k)).
          pose (dep' := if eq_nat_dec n'' init_nid then
                          dep
                        else
                          dep ++ [AExec.put_id n'' c''] ++ dep'').
          exists (h' ++ [AExec.get_label n'' c'' n k val]).
          exists (override s' n (AExec.node_state (p0 val) ptrace dep' rec store)).

          assert (P: val = v' /\ n'' = n' /\ c'' = c').
            unfold val.
            unfold n''.
            unfold c''.
            unfold store.

            assert (A1 := InstExecToSeqExec).
              specex_deprem A1.
              apply N.ICExec.StepStar.step_star_app_one.
              eexists. split.
              subst s1. eassumption.
              eassumption.
              destruct A1 as [sh' [ss [A11 A12]]].
              rewrite A12 in A11. clear A12.
              rewrite inst_exec_eff_app in A11.
              apply I.SExec.StepStar.step_star_app_one in A11.
              destruct A11 as [ssm [A11 A12]].
              subv_in l A12.

            assert (A2 := AbsExecSeqExecStore).
              specex_deprem A2. split.
              eassumption.
              subv h'. rewrite eff_hist_map.
              eassumption.
              instantiate (2 := n) in A2.
              instantiate (2 := k) in A2.

            inversion A12.
            subst n0.
            subst k0.
            clear H6.
            subv_in ssm A2.
            simpl_override_in A2.
            rewrite H9 in A2.
            simpl in A2.
            destruct A2 as [A21 [A22 A23]].
            split_all;
            try assumption.

          destruct P as [P1 [P2 P3]].
          split_all.

          (* --- *)
            clear N2 N3 N5 N6 N7 N8 N9.
            eapply AExec.StepStar.steps. eassumption.
            assert (A: s' = override s' n (AExec.node_state (AExec.Syntax.get k p0) ptrace dep rec store)).
              apply functional_extensionality. intros.
              destruct (eq_nat_dec x n). 
                
                subst x. simpl_override.
                specialize (N4 n). rewrite <- H2 in N4. simpl in N4. simpl_override_in N4. simpl in N4.
                destruct (s' n).
                simpl in N4.
                subst ptrace. subst dep. subst rec. subst store. rewrite <- N4. simpl.
                reflexivity.
                
                simpl_override. reflexivity.

            rewrite A at 1. clear A.
            econstructor.
            assumption.

          (* --- *)
            clear N3 N4 N5 N6 N7 N8 N9.
            rewrite N2.
            rewrite hist_map_app.
            simpl.
            f_equal.
            f_equal.
            f_equal.
            assumption.
            assumption.
            assumption.

          (* --- *)
            clear N1 N2 N4 N5 N6 N7 N8 N9.
            intro.
            simpl.

            destruct (eq_nat_dec n0 n).

              subst n0.
              simpl_override.
              simpl_override.
              unfold ptrace.
              specialize (N3 n).
              subv_in s2 N3.
              simpl_override_in N3.
              assumption.

              simpl_override.
              simpl_override.
              specialize (N3 n0).
              subv_in s2 N3.
              simpl_override_in N3.
              assumption.

          (* --- *)
            intros.
            simpl.
            destruct (eq_nat_dec n0 n).

            subst n0.
            simpl_override.
            simpl_override.
            subv val.
            reflexivity.

            simpl_override.
            simpl_override.
            specialize (N4 n0). subv_in s2 N4. simpl in N4. simpl_override_in N4.
            assumption.

          (* --- *)
            clear N1 N2 N4 N6 N7 N8 N9.
            intros.
            simpl in H5.
            destruct H5 as [M1 M2].

            specialize (N5 m c0).
              simpl in N5.
              depremise N5. split.
              subv s2. assumption.
              assumption.
            destruct N5 as [N51 N52].
            subst tp.

            subst n'0. remember (N.ICExec.msg_sender m) as n'0.
            subst k0. remember (N.ICExec.msg_key m) as k0.
            subst v. remember (N.ICExec.msg_val m) as v.

            destruct (eq_nat_dec n n'0).

              simpl_override.
              unfold ptrace.
              rewrite e0.
              split; assumption.

              simpl_override.
              split; assumption.                

          (* --- *)
            clear N1 N2 N4 N5 N7 N8.
            rewrite H3.
            intros.
            subst d.
            destruct (eq_nat_dec n0 n).

              subst n0.
              simpl_override_in H5.
              unfold dep' in H5.
              destruct (n'' =_? init_nid).
                
                unfold dep in H5.
                specex N6. simpl in N6.
                depremise N6. eassumption.
                destruct N6 as [N6 | N6].
                destruct N6 as [l1 [l2 N6]]. open_conjs. left. exists l1. exists l2. split_all; try assumption. apply N.ICExec.cause_ext_cause. assumption.
                destruct N6 as [l1 N6]. open_conjs. right. exists l1. split_all; try assumption. apply in_app_iff. left. assumption.

                apply in_app_iff in H5. rewrite in_app_iff in H5. simpl in H5.
                destruct H5. 

                unfold dep in H5.
                specex N6. simpl in N6.
                depremise N6. eassumption.
                destruct N6 as [N6 | N6].
                destruct N6 as [l1 [l2 N6]]. open_conjs. left. exists l1. exists l2. split_all; try assumption. apply N.ICExec.cause_ext_cause. assumption.
                destruct N6 as [l1 N6]. open_conjs. right. exists l1. split_all; try assumption. apply in_app_iff. left. assumption.
                
                unfold dep'' in H5.
                unfold store in H5.
                specex N9. 
                  simpl in N9. depremise N9.
                  instantiate (2 := n).
                  instantiate (1 := k).
                  subst n''. unfold store in *. assumption.

                  destruct N9 as [l' N9].
                  open_conjs.
                  assert (A: N.ICExec.cause (h ++ [l]) l' l).
                    constructor. unfold N.ICExec.cause_step. right. split_all.
                    apply N.ICExec.in_prec. assumption.
                    assumption.
                    subst l. simpl. apply I.
                    subst l. simpl. rewrite <- P2. subst n''. subst store. assumption. 
                    subst l. simpl. rewrite <- P3. subst c''. subst store. assumption. 

                  destruct H5 as [[H5 | H5] | H5]; try contradiction.
                  
                    left. exists l'. exists l.
                    split_all.
                    subst l. simpl. reflexivity.
                    subst l. simpl. apply I.
                    assumption.
                    rewrite H7. subst n'0. subst pid. simpl. subst n''. unfold store. reflexivity.
                    rewrite H8. subst c'0. subst pid. simpl. subst n''. unfold store. reflexivity.
                    assumption.

                    left. 
                    instantiate (2 := AExec.put_id_nid pid) in H10.                    
                    instantiate (1 := AExec.put_id_clock pid) in H10.
                    depremise H10. destruct pid. simpl. assumption.
                    destruct H10 as [l'' H10].
                    open_conjs.
                    exists l''. exists l. split_all.
                    subst l. simpl. reflexivity.
                    subst l. simpl. apply I.
                    assumption.
                    rewrite H11. subst n'0. reflexivity.
                    rewrite H12. subst c'0. reflexivity.
                    eapply N.ICExec.cause_cause_trans. 
                    split. eapply N.ICExec.cause_ext_cause. eassumption. assumption.
                    
            simpl_override_in H5.
            specialize (N6 n0 pid).
            simpl in N6.
            depremise N6. assumption.
            destruct N6 as [N6 | N6].
            destruct N6 as [l1 [l2 N6]]. open_conjs. left. exists l1. exists l2. split_all; try assumption. apply N.ICExec.cause_ext_cause. assumption.
            destruct N6 as [l1 N6]. open_conjs. right. exists l1. split_all; try assumption. apply in_app_iff. left. assumption.
          
          (* --- *)
            clear N1 N2 N3 N4 N5 N6 N8 N9.
            rewrite H3 in *.
            intros l' i n''' c'''.
            intros.
            destruct H5 as [M1 [M2 [M3 [M4 M5]]]].
            subst d.

            assert (A2: i < length (AExec.ptrace (s' n0))).
              clear M5.
              destruct (eq_nat_dec n n0).
              
                rewrite e0 in M4.
                simpl_override_in M4.
                unfold ptrace in M4.
                rewrite e0 in M4.
                assumption.

                simpl_override_in M4.
                assumption.

            assert (A3: In (AExec.put_id n''' c''') (AExec.t_put_dep (nth i (AExec.ptrace (s' n0)) AExec.dummy_t_put))).
              clear A2.
              destruct (eq_nat_dec n n0).
              
                rewrite e0 in M5.
                simpl_override_in M5.
                unfold ptrace in M5.
                rewrite e0 in M5.
                assumption.

                simpl_override_in M5.
                assumption.
            clear M5.

            specialize (N7 l' i n''' c''').
            simpl in N7.
            depremise N7. split_all.
              assumption.
              apply in_app_iff in M2. destruct M2 as [M2 | M2]. assumption. exfalso. simpl in M2. destruct M2 as [M2 | M2]; try contradiction. 
              subv_in l' M1. rewrite <- H3 in M1. simpl in M1. contradiction.
              assumption.
              assumption.
              subst n0. subst c0. assumption.
            destruct N7 as [l'' N7].
            open_conjs.
            exists l''. split_all; try assumption. apply N.ICExec.cause_ext_cause. assumption.

          (* --- *)
            clear N1 N2 N3 N4 N5 N6 N7 N9.
            intros n1 n2.
            simpl.

            specex N8.
              instantiate (2 := n1) in N8.
              instantiate (1 := n2) in N8.
              subv_in s2 N8.

            assert (A2 := N.algrec_step).
              specex A2.
              depremise A2.
              subst s1. split_all; eassumption.
              destruct A2 as [A2 _].
              depremise A2.
              subv l. apply I.
              simpl in A2.
              subv_in l A2.
              subv_in s2 A2.
              subv_in s3 A2.
              simpl_override_in A2.
              simpl_override_in A2.

            destruct (eq_nat_dec n1 n).
                        
              subst n1.
              simpl_override.
              simpl_override.
              simpl_override_in N8.
              specialize (A2 n2).
              eapply eq_trans. symmetry. eassumption. eassumption.

              simpl_override.
              simpl_override.
              simpl_override_in N8.
              assumption.

          (* --- *)
            clear N1 N2 N3 N4 N5 N6 N7 N8.
            rewrite H3 in *.            
            intros.

            specialize (N9 n0 k0 n'0 c'0).
            simpl in N9.
            depremise N9. 
            subst n''0.
            destruct (eq_nat_dec n n0).
              subst n0. simpl_override_in H5. unfold store in H5. assumption.
              simpl_override_in H5. assumption.

            destruct (eq_nat_dec n n0).
            
            rewrite e0 in *.
            destruct N9 as [l1 N9]. open_conjs. exists l1. split_all; try assumption. 
            subv n''0. simpl_override. unfold store. rewrite e0. assumption. 
            subv c''0. simpl_override. unfold store. rewrite e0. assumption. 
            apply in_app_iff. left. assumption.
            intros.
            depremise H10. subv_in d'' H11. simpl_override_in H11. unfold store in H11. rewrite e0 in *. assumption.
            destruct H10 as [l2 H10]. open_conjs. exists l2. split_all; try assumption.
            apply N.ICExec.cause_ext_cause. assumption.

            destruct N9 as [l1 N9]. open_conjs. exists l1. split_all; try assumption. 
            subv n''0. simpl_override. unfold store. assumption. 
            subv c''0. simpl_override. unfold store. assumption. 
            apply in_app_iff. left. assumption.
            intros.
            depremise H10. subv_in d'' H11. simpl_override_in H11. assumption.
            destruct H10 as [l2 H10]. open_conjs. exists l2. split_all; try assumption.
            apply N.ICExec.cause_ext_cause. assumption.

        (* update *)
          pose (ptrace_1 := AExec.ptrace (s' n)).
          pose (dep_1 := AExec.dep (s' n)).
          pose (rec_1 := AExec.rec (s' n)).
          pose (store_1 := AExec.store (s' n)).
          pose (prog_2 := AExec.prog (s' n')).
          pose (ptrace_2 := AExec.ptrace (s' n')).
          pose (dep_2 := AExec.dep (s' n')).
          pose (rec_2 := AExec.rec (s' n')).
          pose (store_2 := AExec.store (s' n')).

          pose (ek := AExec.t_put_key (nth (rec_1 n') ptrace_2 AExec.dummy_t_put)).
          pose (ev := AExec.t_put_val (nth (rec_1 n') ptrace_2 AExec.dummy_t_put)).
          pose (ed := AExec.t_put_dep (nth (rec_1 n') ptrace_2 AExec.dummy_t_put)).
          pose (rec_1' := override rec_1 n' ((rec_1 n') + 1)).
          pose (store_1' := override store_1 ek (AExec.entry ev n' (rec_1' n') ed)).

          exists (h' ++ [AExec.update_label n' (rec_1' n') n ek ev]).
          exists (override (override s'
                           n (AExec.node_state p0 ptrace_1 dep_1 rec_1' store_1'))
                           n' (AExec.node_state prog_2 ptrace_2 dep_2 rec_2 store_2)).
          assert (A1 := N.ICExec.no_self_message).
            specex_deprem A1. split.
            subv_in s1 H. eassumption.
            instantiate (1 := N.ICExec.message n' c' k v u n lp).
            subv s2. apply in_app_iff. right. apply in_eq.
            simpl in A1.

          split_all.

          (* --- *)
            clear N2 N5 N6.
            eapply AExec.StepStar.steps. eassumption.

            assert (A2: s' = (override (override s' 
                              n (AExec.node_state p0 ptrace_1 dep_1 rec_1 store_1))
                              n' (AExec.node_state prog_2 ptrace_2 dep_2 rec_2 store_2))).
              apply functional_extensionality. intros.
              destruct (eq_nat_dec x n).
                subst x. simpl_override. simpl_override.
                specialize (N4 n). subv_in s2 N4. simpl_override_in N4.
                destruct (s' n).
                simpl in N4.
                subst ptrace_1. subst dep_1. subst rec_1. subst store_1. subst prog. simpl.
                reflexivity.
                destruct (eq_nat_dec x n').
                  subst x. simpl_override.
                  specialize (N4 n'). subv_in s2 N4. simpl_override_in N4.
                  destruct (s' n').
                  simpl in N4.
                  subst prog_2. subst ptrace_2. subst dep_2. subst rec_2. subst store_2. simpl.
                  reflexivity.

                  simpl_override.
                  simpl_override.
                  reflexivity.

            rewrite A2 at 1. clear A2.
            assert (C: rec_1 n' < length ptrace_2).
              unfold rec_1.
              unfold ptrace_2.
              specialize (N8 n n').
                subv_in s2 N8.
                simpl_override_in N8.
              assert (A2 := N.algrec_step).
                specex_deprem A2.
                subst s1. split_all; eassumption.
                destruct A2 as [_ [_ A2]].
                depremise A2. subv l. apply I.
                simpl in A2.
                destruct A2 as [A2 _].
                subv_in l A2.
                subv_in s2 A2.
                subv_in s3 A2.
                simpl_override_in A2.
                simpl_override_in A2.
              assert (A3 := N.ICExec.msg_clock_lte_state_clock).
                specex A3. simpl in A3. depremise A3. 
                split. subst s1. eassumption. instantiate (1 := N.ICExec.message n' c' k v u n lp).
                subv s2. apply in_app_iff. right. apply in_eq.
                simpl in A3. subv_in s2 A3. simpl_override_in A3.
              specex N3.
                instantiate (1 := n') in N3.
                subv_in s2 N3. simpl_override_in N3.
              rewrite <- N8. clear N8. rewrite <- N3. clear N3.
              rewrite <- A2 in A3. clear A2.
              apply le_S_gt. assumption.

            econstructor.
            assumption.
            apply not_eq_sym. assumption.

            assumption.

            apply Forall_forall.
            intros pid M.
            assert (A2 := N.ICExec.msg_label_eq_key_val).
              specex_deprem A2. split.
              subst s1. eassumption. 
              instantiate (1 := N.ICExec.message n' c' k v u n lp). subv s2.
              apply in_app_iff. right. apply in_eq.
              simpl in A2.
              destruct A2 as [A21 [A22 [A23 [A24 [A25 A26]]]]].

            specex N7. simpl in N7.
            depremise N7. split_all.
              instantiate (1 := lp). assumption.
              assumption.
              instantiate (1 := rec_1 n'). 
                rewrite <- A25. unfold rec_1.
                subv_in s2 N8. simpl_override_in N8.
                rewrite <- N8. clear N8.
                assert (A3 := N.algrec_step).
                specex_deprem A3. 
                subst s1. split_all; eassumption.
                destruct A3 as [_ [_ A3]]. depremise A3. subv l. apply I.
                simpl in A3. destruct A3 as [A3 _]. subv_in s2 A3. subv_in l A3. 
                simpl_override_in A3.
              simpl_override.
              assumption.
              unfold ptrace_2 in C. rewrite <- A24. assumption.
              instantiate (2 := AExec.put_id_nid pid).
              instantiate (1 := AExec.put_id_clock pid).
              subv_in ptrace_2 M.
              rewrite <- A24.
              destruct pid.
              simpl. unfold AExec.put_id.
              assumption.
            destruct N7 as [l' [N71 [N72 [N73 N74]]]].
            rewrite <- N72. rewrite <- N73.

            assert (A3 := N.cause_rec).
              specex A3. simpl in A3. depremise A3. split_all.
              subst s1. eassumption. eassumption. apply N71. subv l. apply I. subv l. assumption.
            subv_in l A3. subv_in s2 A3. simpl_override_in A3.
            unfold rec_1.

            specex N8. 
              instantiate (1 := N.ICExec.label_node l') in N8. 
              instantiate (1 := n) in N8.
              subv_in s2 N8. simpl_override_in N8.
            rewrite <- N8. clear N8.
            assumption.


          (* --- *)
            clear N1 N3 N4 N6 N7 N9.
            rewrite N2.
            rewrite hist_map_app.
            simpl.

            assert (A2: S (rec_1 n') = c').
              unfold rec_1.
              
              specex N8. 
                instantiate (2 := n) in N8.
                instantiate (1 := n') in N8.
                subv_in s2 N8. simpl_override_in N8.
              rewrite <- N8. clear N8.

              assert (A := N.algrec_step).
                specex_deprem A.
                subst s1. split_all; eassumption.
                destruct A as [_ [_ A]].
                depremise A. 
                subv l. apply I.
                simpl in A.
                destruct A as [A _].
                subv_in s2 A.
                subv_in l A.
                simpl_override_in A.

              assumption.

            specex N5. simpl in N5. depremise N5. split.
              instantiate (1 := N.ICExec.message n' c' k v u n lp).
              subv s2. apply in_app_iff. right. apply in_eq.
              simpl. instantiate (1 := rec_1 n').
              assumption.
            simpl in N5.
            destruct N5 as [N51 N52].

            subv ek.
            subv ev.
            unfold ptrace_2.
            rewrite N51.
            rewrite N52.
            unfold rec_1'. simpl_override.
            rewrite plus_comm. simpl.
            rewrite A2.
            reflexivity.
            
          (* --- *)
            clear N1 N2 N4 N5 N6 N7 N8 N9.
            intro.
            simpl.

            destruct (eq_nat_dec n0 n).

              subst n0.
              simpl_override.
              simpl_override.
              unfold ptrace_1.
              specialize (N3 n).
              subv_in s2 N3.
              simpl_override_in N3.
              assumption.

              simpl_override.
              destruct (eq_nat_dec n0 n').
              
                subst n0.
                simpl_override.
                unfold ptrace_2.
                specialize (N3 n').
                subv_in s2 N3.
                simpl_override_in N3.
                assumption.

                simpl_override.
                simpl_override.
                unfold ptrace_2.
                specialize (N3 n0).
                subv_in s2 N3.
                simpl_override_in N3.
                assumption.

          (* --- *)
            clear N1 N2 N3 N5 N6 N7 N8 N9.
            intros.
            simpl.
            destruct (eq_nat_dec n0 n).

            subst n0.
            simpl_override.
            simpl_override.
            reflexivity.

            simpl_override.
            destruct (eq_nat_dec n' n0).
            
            subst n0.
            simpl_override.
            unfold prog_2.
            specialize (N4 n'). subv_in s2 N4. simpl in N4. simpl_override_in N4.
            assumption.

            simpl_override.
            simpl_override.
            specialize (N4 n0). subv_in s2 N4. simpl in N4. simpl_override_in N4.
            assumption.

          (* --- *)
            clear N1 N2 N4 N6 N7 N8 N9.
            intros.
            destruct H6 as [M1 M2].
            simpl in M1.            
            specialize (N5 m c0).
              simpl in N5.
              depremise N5. split.
              subv s2. apply in_app_iff in M1. destruct M1 as [M1 | M1]. apply in_app_iff. left. assumption. apply in_app_iff. right. apply in_cons. assumption.
              assumption.
            destruct N5 as [N51 N52].
            subst n'0. remember (N.ICExec.msg_sender m) as n'0.
            subst c'0. remember (N.ICExec.msg_clock m) as c'0.
            subst k0. remember (N.ICExec.msg_key m) as k0.
            subst v0. remember (N.ICExec.msg_val m) as v0.
            subst tp.
            simpl.

            destruct (eq_nat_dec n'0 n').

              simpl_override.
              unfold ptrace_2.
              rewrite <- e0.
              split; assumption.

              simpl_override.
              destruct (eq_nat_dec n'0 n).

                simpl_override.
                unfold ptrace_1.
                rewrite <- e0.
                split; assumption.                


                simpl_override.
                split; assumption.                
              
          (* --- *)
            clear N1 N2 N4 N5 N7 N8 N9.
            intros.
            subst d.
            assert (In pid (AExec.dep (s' n0))).
              destruct (eq_nat_dec n0 n').

                subst n0.
                simpl_override_in H6.
                unfold dep_2 in H6.
                assumption.

                simpl_override_in H6.
                destruct (eq_nat_dec n n0).
    
                  subst n0.
                  simpl_override_in H6.
                  unfold dep_1 in H6.
                  assumption.

                  simpl_override_in H6.
                  assumption.
            clear H6.
            specialize (N6 n0 pid).
            simpl in N6.
            depremise N6. assumption.
            destruct N6 as [N6 | N6].
            destruct N6 as [l1 [l2 N6]]. open_conjs. left. exists l1. exists l2. split_all; try assumption. apply N.ICExec.cause_ext_cause. assumption.
            destruct N6 as [l1 N6]. open_conjs. right. exists l1. split_all; try assumption. apply in_app_iff. left. assumption.
                
          (* --- *)
            clear N1 N2 N3 N4 N5 N6 N8 N9.

            intros l' i n'' c''.
            intros.
            destruct H6 as [M1 [M2 [M3 [M4 M5]]]].
            rewrite H4 in *.
            subst d.
            assert (A2: i < length (AExec.ptrace (s' n0))).
              clear M5.
              destruct (eq_nat_dec n' n0).
              
                rewrite e0 in M4.
                simpl_override_in M4.
                unfold ptrace_2 in M4.
                rewrite e0 in M4.
                assumption.

                simpl_override_in M4.
                destruct (eq_nat_dec n n0).
                
                  rewrite e0 in M4.
                  simpl_override_in M4.
                  unfold ptrace_1 in M4.
                  rewrite e0 in M4.
                  assumption.

                  simpl_override_in M4.
                  assumption.
            clear M4.
            assert (A3: In (AExec.put_id n'' c'') (AExec.t_put_dep (nth i (AExec.ptrace (s' n0)) AExec.dummy_t_put))).
              clear A2.
              destruct (eq_nat_dec n' n0).
              
                rewrite e0 in M5.
                simpl_override_in M5.
                unfold ptrace_2 in M5.
                rewrite e0 in M5.
                assumption.

                simpl_override_in M5.
                destruct (eq_nat_dec n n0).
                
                  rewrite e0 in M5.
                  simpl_override_in M5.
                  unfold ptrace_1 in M5.
                  rewrite e0 in M5.
                  assumption.

                  simpl_override_in M5.
                  assumption.
            clear M5.

            specialize (N7 l' i n'' c'').
            simpl in N7.
            depremise N7. split_all.
              assumption.
              apply in_app_iff in M2. destruct M2 as [M2 | M2]. assumption. exfalso. simpl in M2. destruct M2 as [M2 | M2]; try contradiction. 
              subv_in l' M1. rewrite <- H4 in M1. simpl in M1. contradiction.
              assumption.
              assumption.
              subst n0. subst c0. assumption.
            destruct N7 as [l'' N7].
            open_conjs.
            exists l''. split_all; try assumption. apply N.ICExec.cause_ext_cause. assumption.

          (* --- *)
            clear N1 N2 N3 N4 N5 N6 N7 N9.
            intros n1 n2.
            simpl.

            specex N8.
              instantiate (2 := n1) in N8.
              instantiate (1 := n2) in N8.
              subv_in s2 N8.

            assert (A2 := N.algrec_step).
              specex A2.
              depremise A2.
              subst s1. split_all; eassumption.
              destruct A2 as [_ [_ A2]].
              depremise A2.
              subv l. apply I.
              simpl in A2.
              subv_in l A2.
              subv_in s2 A2.
              subv_in s3 A2.
              simpl_override_in A2.
              destruct A2 as [A21 [A22 A23]].              
              rewrite <- A21 in A22. clear A21.

            destruct (eq_nat_dec n1 n).
                        
              subst n1.
              simpl_override.
              simpl_override.
              simpl_override_in N8.
              simpl_override_in A22.
              simpl_override_in A23.
              unfold rec_1'.
              destruct (eq_nat_dec n' n2).
              
                subst n2.
                simpl_override.
                unfold rec_1.
                rewrite Plus.plus_comm. simpl.
                rewrite <- N8.
                assumption.

                simpl_override.
                unfold rec_1.
                rewrite <- N8.
                symmetry.
                apply A23.
                apply not_eq_sym.
                assumption.

              simpl_override.
              simpl_override_in N8.
              simpl_override_in A22.
              simpl_override_in A23.

              destruct (eq_nat_dec n' n1).

                subst n1.
                simpl_override.
                unfold rec_2.
                assumption.

                simpl_override.
                simpl_override.
                assumption.

          (* --- *)
            clear N2 N4 N5 N6.
            rewrite H4 in *.            
            intros.
            destruct (eq_nat_dec n n0).

              assert (A3: not (n0 = n')).
                intro.
                apply A1.
                eapply eq_trans. symmetry. eassumption. symmetry. assumption.

              destruct (eq_nat_dec ek k0).
              
                assert (A2 := N.ICExec.msg_label_eq_key_val).
                  specex_deprem A2. split_all.
                  subst s1. eassumption.
                  subv s2. apply in_app_iff. right. apply in_eq.
                  simpl in A2.
                  destruct A2 as [A21 [A22 [A23 [A24 [A25 A26]]]]].

                assert (A4: S (rec_1 n') = c').
                  unfold rec_1.
                  specialize (N8 n n').
                    subv_in s2 N8.
                    simpl_override_in N8.
                  rewrite <- N8. clear N8.
                  assert (A4 := N.algrec_step).
                    specex_deprem A4.
                    subst s1. split_all; eassumption.
                    destruct A4 as [_ [_ A4]].
                    depremise A4. subv l. apply I.
                    simpl in A4.
                    destruct A4 as [A4 _].
                    subv_in l A4.
                    subv_in s2 A4.
                    subv_in s3 A4.
                    simpl_override_in A4.
                    simpl_override_in A4.
                  assumption.

                exists lp.
                split_all; try assumption.
                subv n''. subv n. simpl_override. simpl_override. unfold store_1'. subv ek. simpl_override. symmetry. assumption.
                subv c''. subv n. simpl_override. simpl_override. unfold store_1'. subv ek. simpl_override. unfold rec_1'. simpl_override. rewrite plus_comm. simpl.  rewrite A4. symmetry. assumption.
                apply in_app_iff. left. assumption.
                intros. subst d''.
                simpl_override_in H7.
                subv_in n H7.
                simpl_override_in H7.
                specialize (N7 lp (rec_1 n') n'0 c'0).
                  simpl in N7. depremise N7.
                  split_all; try assumption.
                  rewrite A4. assumption.
                rewrite <- A24.
                
                unfold rec_1.
                specialize (N8 n n').
                  subv_in s2 N8.
                  simpl_override_in N8.
                assert (A5 := N.algrec_step).
                  specex_deprem A5.
                  subst s1. split_all; eassumption.
                  destruct A5 as [_ [_ A5]].
                  depremise A5. subv l. apply I.
                  simpl in A5.
                  destruct A5 as [A5 _].
                  subv_in l A5.
                  subv_in s2 A5.
                  subv_in s3 A5.
                  simpl_override_in A5.
                  simpl_override_in A5.
                assert (A6 := N.ICExec.msg_clock_lte_state_clock).
                  specex A6. simpl in A6. depremise A6.
                  split. subst s1. eassumption. instantiate (1 := N.ICExec.message n' c' k v u n lp).
                  subv s2. apply in_app_iff. right. apply in_eq.
                  simpl in A6. subv_in s2 A6. simpl_override_in A6.
                specex N3.
                  instantiate (1 := n') in N3.
                  subv_in s2 N3. simpl_override_in N3.
                rewrite <- N8. clear N8. rewrite <- N3. clear N3.
                rewrite <- A5 in A6. clear A5.
                apply le_S_gt. assumption.

                rewrite <- A24.
                unfold store_1' in H7.
                subv_in ek H7.
                simpl_override_in H7.
                unfold ed in H7.
                unfold ptrace_2 in H7.
                assumption.
                destruct N7 as [l'' N7]. open_conjs.
                exists l''. split_all; try assumption.
                apply N.ICExec.cause_ext_cause. assumption.
                
              specialize (N9 n k0 n'0 c'0).
              simpl in N9.
              depremise N9. subst n''. subv_in n H6. simpl_override_in H6. simpl_override_in H6. unfold store_1' in H6. simpl_override_in H6. unfold store_1 in H6. assumption.
              destruct N9 as [l_2 N9]. open_conjs.
              exists l_2. split_all; try assumption.
              rewrite H8. subv n''. simpl_override. simpl_override. unfold store_1'. simpl_override. unfold store_1. reflexivity.
              rewrite H9. subv c''. simpl_override. simpl_override. unfold store_1'. simpl_override. unfold store_1. reflexivity.
              apply in_app_iff. left. assumption.
              simpl. simpl_override. simpl_override. 
              intros.
              depremise H11. unfold store_1' in H12. simpl_override_in H12. unfold store_1 in H12. assumption.
              destruct H11 as [l_1 H11]. open_conjs.
              exists l_1. split_all; try assumption.
              apply N.ICExec.cause_ext_cause. assumption.
                

            destruct (eq_nat_dec n0 n').

              specialize (N9 n' k0 n'0 c'0).
              simpl in N9.
              depremise N9. subst n''. subv_in n0 H6. simpl_override_in H6. unfold store_2 in H6. assumption.
              destruct N9 as [l_2 N9]. open_conjs.
              exists l_2. split_all; try assumption.
              rewrite H8. subv n''. simpl_override. unfold store_2. reflexivity.
              rewrite H9. subv c''. simpl_override. unfold store_2. reflexivity.
              apply in_app_iff. left. assumption.
              simpl. simpl_override.
              intros.
              depremise H11. unfold store_2 in H12. assumption.
              destruct H11 as [l_1 H11]. open_conjs.
              exists l_1. split_all; try assumption.
              apply N.ICExec.cause_ext_cause. assumption.

              specialize (N9 n0 k0 n'0 c'0).
              simpl in N9.
              depremise N9. subst n''. simpl_override_in H6. simpl_override_in H6. assumption.
              destruct N9 as [l_2 N9]. open_conjs.
              exists l_2. split_all; try assumption.
              rewrite H8. subv n''. simpl_override. simpl_override. reflexivity.
              rewrite H9. subv c''. simpl_override. simpl_override. reflexivity.
              apply in_app_iff. left. assumption.
              simpl. simpl_override. simpl_override. 
              intros.
              depremise H11. assumption.
              destruct H11 as [l_1 H11]. open_conjs.
              exists l_1. split_all; try assumption.
              apply N.ICExec.cause_ext_cause. assumption.

              
        (* fault *)
          pose (ptrace := AExec.ptrace (s' n)).
          pose (dep := AExec.dep (s' n)).
          pose (rec := AExec.rec (s' n)).
          pose (store := AExec.store (s' n)).

          exists (h' ++ [AExec.fault_label n]).
          exists (override s' n (AExec.node_state (AExec.Syntax.skip) ptrace dep rec store)).

          split_all.

          (* --- *)
            clear N2 N3 N5 N6 N7 N8 N9.
            eapply AExec.StepStar.steps. eassumption.
            assert (A: s' = override s' n (AExec.node_state (AExec.Syntax.fault) ptrace dep rec store)).
              apply functional_extensionality. intros.
              destruct (eq_nat_dec x n). 
                
                subst x. simpl_override.
                specialize (N4 n). rewrite <- H2 in N4. simpl in N4. simpl_override_in N4. simpl in N4.
                destruct (s' n).
                simpl in N4.
                subst ptrace. subst dep. subst rec. subst store. rewrite <- N4. simpl.
                reflexivity.
                
                simpl_override. reflexivity.

            rewrite A at 1. clear A.
            econstructor.
            assumption.

          (* --- *)
            clear N3 N4 N5 N6 N7 N8 N9.
            rewrite N2.
            rewrite hist_map_app.
            simpl.
            f_equal.

          (* --- *)
            clear N1 N2 N4 N5 N6 N7 N8 N9.
            intro.
            simpl.

            destruct (eq_nat_dec n0 n).

              subst n0.
              simpl_override.
              simpl_override.
              unfold ptrace.
              specialize (N3 n).
              subv_in s2 N3.
              simpl_override_in N3.
              assumption.

              simpl_override.
              simpl_override.
              specialize (N3 n0).
              subv_in s2 N3.
              simpl_override_in N3.
              assumption.

          (* --- *)
            intros.
            simpl.
            destruct (eq_nat_dec n0 n).

            subst n0.
            simpl_override.
            simpl_override.
            subv val.
            reflexivity.

            simpl_override.
            simpl_override.
            specialize (N4 n0). subv_in s2 N4. simpl in N4. simpl_override_in N4.
            assumption.

          (* --- *)
            clear N1 N2 N4 N6 N7 N8 N9.
            intros.
            simpl in H5.
            destruct H5 as [M1 M2].

            specialize (N5 m c0).
              simpl in N5.
              depremise N5. split.
              subv s2. assumption.
              assumption.
            destruct N5 as [N51 N52].
            subst tp.

            destruct (eq_nat_dec n n').

              simpl_override.
              unfold ptrace.
              rewrite e0.
              split; assumption.

              simpl_override.
              split; assumption.                

          (* --- *)
            clear N1 N2 N4 N5 N7 N8.
            rewrite H3.
            intros.
            subst d.
            destruct (eq_nat_dec n0 n).
                    
            subst n0.
            simpl_override_in H5.
            specialize (N6 n pid).
            simpl in N6.
            depremise N6. assumption.
            destruct N6 as [N6 | N6].
            destruct N6 as [l1 [l2 N6]]. open_conjs. left. exists l1. exists l2. split_all; try assumption. apply N.ICExec.cause_ext_cause. assumption.
            destruct N6 as [l1 N6]. open_conjs. right. exists l1. split_all; try assumption. apply in_app_iff. left. assumption.

            simpl_override_in H5.
            specialize (N6 n0 pid).
            simpl in N6.
            depremise N6. assumption.
            destruct N6 as [N6 | N6].
            destruct N6 as [l1 [l2 N6]]. open_conjs. left. exists l1. exists l2. split_all; try assumption. apply N.ICExec.cause_ext_cause. assumption.
            destruct N6 as [l1 N6]. open_conjs. right. exists l1. split_all; try assumption. apply in_app_iff. left. assumption.
          
          (* --- *)
            clear N1 N2 N3 N4 N5 N6 N8 N9.
            rewrite H3 in *.
            intros l' i n''' c'''.
            intros.
            destruct H5 as [M1 [M2 [M3 [M4 M5]]]].
            subst d.

            assert (A2: i < length (AExec.ptrace (s' n0))).
              clear M5.
              destruct (eq_nat_dec n n0).
              
                rewrite e0 in M4.
                simpl_override_in M4.
                unfold ptrace in M4.
                rewrite e0 in M4.
                assumption.

                simpl_override_in M4.
                assumption.

            assert (A3: In (AExec.put_id n''' c''') (AExec.t_put_dep (nth i (AExec.ptrace (s' n0)) AExec.dummy_t_put))).
              clear A2.
              destruct (eq_nat_dec n n0).
              
                rewrite e0 in M5.
                simpl_override_in M5.
                unfold ptrace in M5.
                rewrite e0 in M5.
                assumption.

                simpl_override_in M5.
                assumption.
            clear M5.

            specialize (N7 l' i n''' c''').
            simpl in N7.
            depremise N7. split_all.
              assumption.
              apply in_app_iff in M2. destruct M2 as [M2 | M2]. assumption. exfalso. simpl in M2. destruct M2 as [M2 | M2]; try contradiction. 
              subv_in l' M1. rewrite <- H3 in M1. simpl in M1. contradiction.
              assumption.
              assumption.
              subst n0. subst c0. assumption.
            destruct N7 as [l'' N7].
            open_conjs.
            exists l''. split_all; try assumption. apply N.ICExec.cause_ext_cause. assumption.

          (* --- *)
            clear N1 N2 N3 N4 N5 N6 N7 N9.
            intros n1 n2.
            simpl.

            specex N8.
              instantiate (2 := n1) in N8.
              instantiate (1 := n2) in N8.
              subv_in s2 N8.

            subst l.
            inversion H0.
            subst.

            destruct (eq_nat_dec n1 n).
                        
              subst n1.
              simpl_override.
              simpl_override.
              simpl_override_in N8.
              unfold rec.
              assumption.

              simpl_override.
              simpl_override.
              simpl_override_in N8.
              assumption.

          (* --- *)
            clear N1 N2 N3 N4 N5 N6 N7 N8.
            rewrite H3 in *.            
            intros.

            specialize (N9 n0 k0 n' c').
            simpl in N9.
            depremise N9. 
            subst n''.
            destruct (eq_nat_dec n n0).
              subst n0. simpl_override_in H5. unfold store in H5. assumption.
              simpl_override_in H5. assumption.

            destruct (eq_nat_dec n n0).
            
            rewrite e0 in *.
            destruct N9 as [l1 N9]. open_conjs. exists l1. split_all; try assumption. 
            subv n''. simpl_override. unfold store. rewrite e0. assumption. 
            subv c''. simpl_override. unfold store. rewrite e0. assumption. 
            apply in_app_iff. left. assumption.
            intros.
            depremise H10. subv_in d'' H11. simpl_override_in H11. subst store. rewrite e0 in *. assumption.
            destruct H10 as [l2 H10]. open_conjs. exists l2. split_all; try assumption.
            apply N.ICExec.cause_ext_cause. assumption.

            destruct N9 as [l1 N9]. open_conjs. exists l1. split_all; try assumption. 
            subv n''. simpl_override. unfold store. assumption. 
            subv c''. simpl_override. unfold store. assumption. 
            apply in_app_iff. left. assumption.
            intros.
            depremise H10. subv_in d'' H11. simpl_override_in H11. subst store. assumption.
            destruct H10 as [l2 H10]. open_conjs. exists l2. split_all; try assumption.
            apply N.ICExec.cause_ext_cause. assumption.

    Qed.

  Theorem Refinement:
    forall (p: N.ICExec.Syntax.PProg)(h: list N.ICExec.Label),
      N.ICExec.history (N.ICExec.init p) h
      -> exists (h': list AExec.Label),
           AExec.history (AExec.init p) h'
           /\ N.ICExec.ext_hist h = AExec.ext_hist h'.

    Proof.
      intros.
      unfold N.ICExec.history in H.
      unfold N.ICExec.StepStar.history in H.
      destruct H as [s H].
      apply Refinement' in H.
      destruct H as [h' [s' [H1 [H2 _]]]].
      exists h'.
      split.
      unfold AExec.history.
      unfold AExec.StepStar.history.
      eexists. eassumption.
      subv h'.
      symmetry.
      apply ext_hist_map.
    Qed.

End InstExecToAbsExec.

  Theorem CausallyConsistent:
    forall (p: Syntax.PProg)(h: list N.CExec.Label),
      N.CExec.history (N.CExec.init p) h 
      -> exists (h': list AExec.Label),
           AExec.history (AExec.init p) h'
           /\ N.CExec.ext_hist h = AExec.ext_hist h'.

    Proof.
      intros.
      assert (A1 := ExecToInstExec.Refinement).
      specex_deprem A1. eassumption.
      destruct A1 as [h' [A11 A12]].
      assert (A2 := InstExecToAbsExec.Refinement).
      specex_deprem A2. eassumption.
      destruct A2 as [h'' [A21 A22]].
      exists h''.
      split.
      assumption.
      eapply eq_trans; eassumption.
    Qed.

  Definition CausallyContent program := forall n l ls s,
      AExec.StepStar.step_star (AExec.init program) ls s ->
      List.In l ls ->
      l <> AExec.fault_label n.


  Lemma FaultFreedom: 
    forall program h,
    CausallyContent program ->
    CExec.history (CExec.init program) h ->
    forall n l, List.In l h -> l <> CExec.fault_label n.

  Proof.
    unfold CausallyContent.
    intros program h HcauseContent Hrun.
    intros.
    apply CausallyConsistent in Hrun.
    destruct Hrun as [ls[Hrun Hhist_eq]].
    unfold AExec.history in Hrun.
    destruct Hrun as [s' Hss].
    unfold N.CExec.ext_hist, AExec.ext_hist in Hhist_eq.
    apply List.in_map with (f:=N.CExec.ext) in H.
    rewrite Hhist_eq in H.
    apply List.in_map_iff in H.
    destruct H as [l'[??]].
    cut (l' <> AExec.fault_label n); intros.
    intro; subst l.
    simpl in H.
    apply H1.
    unfold AExec.ext in H.
    destruct l'; inversion H; clear H; subst; reflexivity.
    eapply HcauseContent with (ls:=ls); eauto.
  Qed.

  Module Exec := ConcExec SyntaxArg AlgDef.


End ExecToAbstExec.


