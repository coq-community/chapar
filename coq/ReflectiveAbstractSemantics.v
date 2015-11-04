Require Import Predefs.
Require Import KVStore.


Module Type AbsExecCarrier (SyntaxArg : SyntaxPar).
  Module AbsExec := AbsExec SyntaxArg.
End AbsExecCarrier.

Module ReflAbsSem (SyntaxArg : SyntaxPar) (Import AE : AbsExecCarrier SyntaxArg).
  Export AbsExec.
  Export AbsExec.Syntax.

  Lemma rev_step_star_ind :
    forall (P : StepStarArgs.State -> list StepStarArgs.Label -> StepStarArgs.State -> Prop),
      (forall s, P s nil s) ->
      (forall s1 l s2 ls s3,
        StepStarArgs.step s1 l s2 ->
        step_star s2 ls s3 ->
        P s2 ls s3 ->
        P s1 (l::ls)%list s3) ->
      forall s l s0,
        step_star s l s0 ->
        P s l s0.
  Proof.
    intros P Hnil Hstep.
    intros s l1 s1 Hss1.
    assert (Hss2: step_star s1 nil s1) by auto.
    remember s1 as s0 in Hss2 at 2.
    rewrite <-Heqs0.
    remember nil as l2 in Hss2.
    replace l1 with (l1++l2)%list by (subst; rewrite List.app_nil_r; auto).
    assert (HPl2: P s1 l2 s0) by (subst; auto).
    clear Heqs0 Heql2.
    revert s0 l2 HPl2 Hss2.
    induction Hss1; intros; auto.
    rewrite <-List.app_assoc.
    apply IHHss1.
    eapply Hstep; eauto.
    simpl.
    apply step_star_end.
    eauto.
  Qed.

  Lemma rev_step_star_inv :
    forall s ls s0  (P : StepStarArgs.State -> list StepStarArgs.Label -> StepStarArgs.State -> Prop),
      P s nil s ->
      (forall l s1 ls',
        StepStarArgs.step s l s1 ->
        step_star s1 ls' s0 ->
        P s (l::ls')%list s0) ->
      step_star s ls s0 ->
      P s ls s0.
  Proof.
    intros s ls s0 P Hnil Hstep Hss.
    revert P Hnil Hstep.
    induction Hss using rev_step_star_ind; intros; auto.
    eauto.
  Qed.

  Lemma override_eq: forall {V} n s (v1 v2: V),
    SysPredefs.override (SysPredefs.override s n v1) n v2 = SysPredefs.override s n v2.
  Proof.
    unfold SysPredefs.override; intros.
    apply functional_extensionality; intros.
    case_eq (x =_? n); intros; auto.
  Qed.

  Lemma override_neq: forall {V} n1 n2 s (v1 v2: V),
    n1 <> n2 ->
    SysPredefs.override (SysPredefs.override s n1 v1) n2 v2 = SysPredefs.override (SysPredefs.override s n2 v2) n1 v1.
  Proof.
    unfold SysPredefs.override; intros.
    apply functional_extensionality; intros.
    case_eq (x =_? n2); intros; subst; auto.
    case_eq (n2 =_? n1); intros; subst; auto.
    congruence.
  Qed.

  Ltac simpl_override:=
    repeat match goal with
    | H: context[SysPredefs.override _ ?n _ ?n] |- _ =>
      rewrite SysPredefs.override_new_val with (k:=n) in H
    | H: context[SysPredefs.override _ ?n1 _ ?n2] |- _ =>
      rewrite SysPredefs.override_old_val with (k:=n1) (k':=n2) in H; [ | congruence]
    | H: context[SysPredefs.override (SysPredefs.override _ ?n _) ?n _] |- _ =>
      rewrite @override_eq in H
    | H: context[SysPredefs.override (SysPredefs.override _ ?n1 _) ?n2 _] |- _ =>
      (* sort the overrides so we can eliminate redundencies easily *)
      let Hlt:= fresh "H" in
      assert (Hlt: n1 > n2) by omega;
      rewrite (@override_neq _ n1 n2) in H; [ | omega ];
      clear Hlt
    | |- context[SysPredefs.override _ ?n _ ?n] =>
      rewrite SysPredefs.override_new_val with (k:=n)
    | |- context[SysPredefs.override _ _ _ _] =>
      rewrite SysPredefs.override_old_val; [ | congruence]
    | |- context[SysPredefs.override (SysPredefs.override _ ?n _) ?n _] =>
      rewrite @override_eq
    | |- context[SysPredefs.override (SysPredefs.override _ ?n1 _) ?n2 _] =>
      (* sort the overrides so we can eliminate redundencies easily *)
      let Hlt:= fresh "H" in
      assert (Hlt: n1 > n2) by omega;
      rewrite (@override_neq _ n1 n2); [ | omega ];
      clear Hlt
    end.

  Arguments NPeano.ltb n m : simpl nomatch.
  Arguments NPeano.leb n m : simpl nomatch.

  Lemma ltb_ge: forall n m,
    NPeano.ltb n m = false <-> n >= m.
  Proof.
    unfold NPeano.ltb; intros.
    revert n.
    induction m; destruct n; simpl;
      intuition auto;
      try discriminate || omega.
    apply IHm in H; omega.
    apply IHm; omega.
  Qed.

  Hint Rewrite EqNat.beq_nat_false_iff EqNat.beq_nat_true_iff NPeano.ltb_lt ltb_ge : nat.


  Inductive ScheduleTask : Set :=
  | SchedProc: forall (n: SysPredefs.NId), ScheduleTask
  | SchedUpdate: forall (n1 n2 : SysPredefs.NId), ScheduleTask.

  Lemma NId_eq_dec: forall (x y: SysPredefs.NId), {x=y}+{x<>y}.
  Proof. decide equality. Qed.


  Tactic Notation "do_" constr(n) tactic(tac):=
    let rec do__ n :=
      match n with
      | S ?n' => tac; do__ n'
      | O => idtac
      end
    in do__ n.

  Ltac mcase_eq_term t H:=
    match t with
    | context[match ?t with _=>_ end] =>
      mcase_eq_term t H
    | _ =>
      case_eq t;
      repeat match goal with
      | |- t = _ -> _ => fail 1
      | |- _->_ => intro
      end;
      intro H;
      rewrite ?H in *
    end.
  Tactic Notation "mcase_eq" "as" ident(H') "in" hyp(H):=
    match type of H with
    | ?t => mcase_eq_term t H'
    end.
  Tactic Notation "mcase_eq" "in" hyp(H):=
    let H':= fresh "H" in
    mcase_eq as H' in H.
  Tactic Notation "mcase_eq":=
    let H':= fresh "H" in
    match goal with
    | |- ?t => mcase_eq_term t H'
    end.



  Section A.
(* TEMPORARY *)
(* these are defined here because SysPredefs.MaxNId is currently admitted.
    we need the user to be able to instantiate it with a constant for these
    eflective semantics to work correctly
*)
    Variable max_nid : nat.
    Hypothesis max_nid_eq: max_nid = SysPredefs.MaxNId.

    Definition nids:= (let (l, _, _) := SysPredefs.bnats max_nid in l).

  Lemma nids_eq: nids = SysPredefs.nids.
  Proof. unfold nids, SysPredefs.nids; intros; rewrite max_nid_eq; reflexivity. Qed.



  Definition step_fun task s: option (Label * State) :=
    match task with
    | SchedProc n =>
      if List.existsb (EqNat.beq_nat n) nids then
        match s n with
        | node_state (KVStore.put k v p) u d r m =>
          let u' := u ++ [(t_put k v d)] in
          let d' := (put_id n (List.length u')) :: d in
          let r' := SysPredefs.override r n ((r n) + 1) in
          let m' := SysPredefs.override m k (entry v n (List.length u') nil) in
          Some (put_label n (List.length u') k v, SysPredefs.override s n (node_state p u' d' r' m'))
        | node_state (KVStore.get k p) u d r m =>
          let v := entry_val (m k) in
          let n'' := entry_nid (m k) in
          let c'' := entry_clock (m k) in
          let d'' := entry_dep (m k) in
          let d' := if EqNat.beq_nat n'' max_nid then d
                else d ++ [put_id n'' c''] ++ d'' in
          Some (get_label n'' c'' n k v, SysPredefs.override s n (node_state (p v) u d' r m))
        | node_state (KVStore.fault) u d r m =>
          Some (fault_label n, SysPredefs.override s n (node_state skip u d r m))
        | _ => None
        end
      else None
    | SchedUpdate n1 n2 =>
      match s n1, s n2 with
      | node_state p_1 u_1 d_1 r_1 m_1, node_state p_2 u_2 d_2 r_2 m_2 =>
        let d := t_put_dep (List.nth (r_1 n2) u_2 dummy_t_put) in
        if negb (EqNat.beq_nat n1 n2)
          && List.existsb (EqNat.beq_nat n1) nids
          && NPeano.ltb (r_1 n2) (List.length u_2)
          && List.forallb (fun pid => NPeano.leb (put_id_clock pid) (r_1 (put_id_nid pid))) d then
          let k := t_put_key (List.nth (r_1 n2) u_2 dummy_t_put) in
          let v := t_put_val (List.nth (r_1 n2) u_2 dummy_t_put) in
          let r_1' := SysPredefs.override r_1 n2 ((r_1 n2) + 1) in
          let m_1' := SysPredefs.override m_1 k (entry v n2 (r_1' n2) d) in
          Some (update_label n2 (r_1' n2) n1 k v,
            SysPredefs.override (SysPredefs.override s
              n1 (node_state p_1 u_1 d_1 r_1' m_1'))
              n2 (node_state p_2 u_2 d_2 r_2 m_2))
        else
          None
      end
    end%list%bool.

  Fixpoint step_star_fun tracePrefix (sched : list ScheduleTask) s : option ((list Label) * State) :=
    match sched with
    | task :: sched' =>
      match step_fun task s with
      | Some (l, s') =>
        step_star_fun (tracePrefix++[l]) sched' s'
      | None => None
      end
    | nil => Some (tracePrefix, s)
    end%list.

  Definition fast_step_fun task s: option State :=
    match task with
    | SchedProc n =>
      match s n with
      | node_state (KVStore.put k v p) u d r m =>
        let u' := u ++ [(t_put k v d)] in
        let d' := (put_id n (List.length u')) :: d in
        let r' := SysPredefs.override r n ((r n) + 1) in
        let m' := SysPredefs.override m k (entry v n (List.length u') nil) in
        Some (SysPredefs.override s n (node_state p u' d' r' m'))
      | node_state (KVStore.get k p) u d r m =>
        let n'' := entry_nid (m k) in
        let d' := if EqNat.beq_nat n'' max_nid then d
                else d ++ [put_id n'' (entry_clock (m k))] ++ entry_dep (m k) in
        Some (SysPredefs.override s n (node_state (p (entry_val (m k))) u d' r m))
      | node_state (KVStore.fault) u d r m =>
        Some (SysPredefs.override s n (node_state skip u d r m))
      | _ => None
      end
    | SchedUpdate n1 n2 =>
      match s n1, s n2 with
      | node_state p_1 u_1 d_1 r_1 m_1, node_state p_2 u_2 d_2 r_2 m_2 =>
        let d := t_put_dep (List.nth (r_1 n2) u_2 dummy_t_put) in
        if negb (EqNat.beq_nat n1 n2)
          && NPeano.ltb (r_1 n2) (List.length u_2)
          && List.forallb (fun pid => NPeano.leb (put_id_clock pid) (r_1 (put_id_nid pid))) d then
          let x:= List.nth (r_1 n2) u_2 dummy_t_put in
          let k := t_put_key x in
          let v := t_put_val x in
          let r_1' := SysPredefs.override r_1 n2 ((r_1 n2) + 1) in
          let m_1' := SysPredefs.override m_1 k (entry v n2 (r_1' n2) d) in
          Some (
            SysPredefs.override (SysPredefs.override s
              n1 (node_state p_1 u_1 d_1 r_1' m_1'))
              n2 (node_state p_2 u_2 d_2 r_2 m_2))
        else
          None
      end
    end%list%bool.

  Fixpoint fast_step_star_fun (sched : list ScheduleTask) s : option State :=
    match sched with
    | task :: sched' =>
      match fast_step_fun task s with
      | Some s' =>
        fast_step_star_fun sched' s'
      | None => None
      end
    | nil => Some s
    end%list.

  Lemma nid_in_dec_existsb: forall n l,
    List.existsb (EqNat.beq_nat n) l =
      if List.in_dec NId_eq_dec n l then true else false.
  Proof.
    intros.
    case_eq (List.existsb (EqNat.beq_nat n) l); intros.
    apply List.existsb_exists in H; destruct H as [y[??]].
    apply EqNat.beq_nat_true in H0; subst y.
    case_eq (List.in_dec NId_eq_dec n l); intros; auto.
    contradiction.
    case_eq (List.in_dec NId_eq_dec n l); intros; auto.
    rewrite <-H.
    apply List.existsb_exists.
    exists n; split; auto.
    apply NPeano.Nat.eqb_refl.
  Qed.



  Lemma fast_step_correct: forall task s l s',
    step_fun task s = Some (l, s') ->
    fast_step_fun task s = Some s'.
  Proof.
    unfold step_fun, fast_step_fun; intros.
    clear max_nid_eq.
    rewrite nids_eq in *.
    repeat match goal with
      | H: Some _ = Some _ |- _ => inversion H; clear H; subst
      | _ => rewrite nid_in_dec_existsb in *
      | H: (_ && _ = true)%bool |- _ => rewrite Bool.andb_true_iff in H; destruct H
      | H: (_ && _ = false)%bool |- _ => rewrite Bool.andb_false_iff in H; destruct H
      | H: None = Some _ |- _ => discriminate
      | _ => reflexivity
      | _ => mcase_eq in H
      | _ => mcase_eq
      | _ => congruence
      end.
  Qed.

  Lemma fast_step_star_correct: forall ls sched s ls' s',
    step_star_fun ls sched s = Some (ls', s') ->
    fast_step_star_fun sched s = Some s'.
  Proof.
    intros.
    revert ls s ls' s' H.
    induction sched; simpl; intros.
    * congruence.
    * mcase_eq as Hs in H; try congruence.
    destruct p.
    apply fast_step_correct in Hs; rewrite Hs.
    eauto.
  Qed.

  Lemma step_star_fun_app: forall sched1 sched2 ls1 s,
    step_star_fun ls1 (sched1 ++ sched2)%list s =
    match step_star_fun ls1 sched1 s with
    | Some (ls2, s') => step_star_fun ls2 sched2 s'
    | None => None
    end.
  Proof.
    clear max_nid_eq.
    induction sched1; simpl; intros; auto.
    repeat mcase_eq; subst; auto.
    rewrite IHsched1, H1; reflexivity.
    rewrite IHsched1, H1; reflexivity.
  Qed.

  Lemma prefix_step_star_fun: forall sched ls1 ls2 ls3 s s',
    step_star_fun ls1 sched s = Some (ls2, s') ->
    step_star_fun (ls3++ls1)%list sched s = Some (ls3++ls2, s')%list.
  Proof.
    induction sched; simpl; intros.
    congruence.
    destruct (step_fun a s ) as [ [??] | ]; try discriminate.
    rewrite <-List.app_assoc.
    eauto.
  Qed.


  Lemma prefix_inv_step_star_fun: forall sched ls1 ls2 s s',
    step_star_fun ls1 sched s = Some (ls2, s') ->
    (exists ls3,
      ls2 = ls1 ++ ls3 /\ step_star_fun nil sched s = Some (ls3, s'))%list.
  Proof.
    induction sched; simpl; intros.
    * inversion H; clear H; subst.
    exists nil; rewrite List.app_nil_r; split; reflexivity.
    * destruct (step_fun a s) as [ [??] | ?]; try discriminate.
    edestruct IHsched as [ls3[??]]; eauto; subst ls2.
    exists (l::ls3)%list; split.
    rewrite <-List.app_assoc.
    reflexivity.
    eapply prefix_step_star_fun with (ls3:=[l]) (ls1:=nil).
    assumption.
  Qed.

  Lemma step_ext: forall s1 s3 l s2 s4,
    step s1 l s2 ->
    (forall n, s1 n = s3 n) ->
    (forall n, s2 n = s4 n) ->
    step s3 l s4.
  Proof.
    intros s1 s3 l s2 s4 Hstep Heq1 Heq2.
    apply functional_extensionality in Heq1.
    apply functional_extensionality in Heq2.
    subst; auto.
  Qed.

  Definition valid_schedule nids (sched: list ScheduleTask) :=
    List.Forall
      (fun task => match task with
      | SchedProc n1 => List.In n1 nids
      | SchedUpdate n1 n2 => List.In n1 nids /\ List.In n2 nids
      end)
      sched.

  Lemma valid_schedule_cons: forall nids task sched,
    valid_schedule nids (task::sched) <->
      match task with
      | SchedProc n1 => List.In n1 nids
      | SchedUpdate n1 n2 => List.In n1 nids /\ List.In n2 nids
      end
      /\ valid_schedule nids sched.
  Proof.
    unfold valid_schedule; intros.
    split; intros.
    inversion H; split; auto.
    apply List.Forall_cons; tauto.
  Qed.

  Lemma valid_schedule_app: forall nids sched1 sched2,
    valid_schedule nids (sched1++sched2) <->
    valid_schedule nids sched1 /\ valid_schedule nids sched2.
  Proof.
    unfold valid_schedule; intros.
    rewrite !List.Forall_forall in *.
    setoid_rewrite List.in_app_iff.
    split.
    * intros H.
    split; intros task Hin; specialize (H task); tauto.
    * intros [H1 H2] x.
    specialize (H1 x); specialize (H2 x).
    intros [?|?]; tauto.
  Qed.

  Ltac nid_cases n:=
    try match goal with
    | H: List.In n SysPredefs.nids |- _ =>
      unfold SysPredefs.nids in H;
      rewrite max_nid in H;
      simpl in H;
      repeat match type of H with
        | _ \/ _ => destruct H as [H|H]
        | ?x = ?x => clear H
        | _ = ?n => is_var n; subst n
        | ?n = _ => is_var n; subst n
        | _ = _ => congruence
        | False => contradiction
        end
    end.

  Lemma valid_nid_step_fun_Proc: forall n1 s l s',
    step_fun (SchedProc n1) s = Some (l, s') ->
    List.In n1 nids.
  Proof.
    simpl; intros.
    rewrite nid_in_dec_existsb in *.
    mcase_eq in H; auto.
    discriminate.
  Qed.

  Lemma valid_nid_step_fun_Update: forall n1 n2 s l s',
    step_fun (SchedUpdate n1 n2) s = Some (l, s') ->
    List.In n1 nids.
  Proof.
    simpl; intros.
    rewrite nid_in_dec_existsb in *.
    repeat mcase_eq in H; auto;
      rewrite ?Bool.andb_false_r, ?Bool.andb_false_l in *;
      discriminate.
  Qed.

  Lemma valid_schedule_step_star_fun: forall ls1 sched prog0 hs',
    step_star_fun ls1 sched (init prog0) = Some hs' ->
    valid_schedule nids sched.
  Proof.
    intros.
    clear max_nid_eq.
    assert (forall n1 n2, List.In n1 nids -> ~List.In n2 nids -> ptrace ((init prog0) n2) = nil /\ rec ((init prog0) n1) n2 = 0)
      by (split; reflexivity).
    remember (init prog0) as s.
    rename H into Hss.
    rename H0 into Hbad_nid_clock_zero.
    clear Heqs.
    revert ls1 s Hss Hbad_nid_clock_zero.
    induction sched as [ | [ n1 | n1 n2 ] sched ]; simpl; intros.
    * constructor.
    * rewrite nid_in_dec_existsb in Hss.
    generalize (Hbad_nid_clock_zero n1); intro Hbncz1.
    apply valid_schedule_cons; simpl; split; auto;
      repeat mcase_eq in Hss; auto;
      try discriminate;
      eapply IHsched; eauto;
      clear Hss H0 IHsched;
        intros ? n2; intros;
        generalize (Hbad_nid_clock_zero n2); intro Hbncz2;
        intuition (subst; auto);
        repeat match goal with
        | |- context[SysPredefs.override _ ?n1 _ ?n2] =>
          (is_var n1 || is_var n2);
          destruct (NId_eq_dec n1 n2);
          [ subst;
            rewrite !SysPredefs.override_new_val
          | rewrite SysPredefs.override_old_val with (k:=n1) (k':=n2);
            auto
          ]
        | _ => progress simpl
        | _ => contradiction
        end;
        try solve
        [ eapply Hbad_nid_clock_zero; intuition auto
        | apply Hbncz1; auto
        ].
    * assert (List.In n2 nids).
    { repeat mcase_eq in Hss; try discriminate.
      clear Hss IHsched.
      destruct (List.in_dec NId_eq_dec n2 nids) as [Hin|Hnin]; auto.
      exfalso.
      rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff in H1.
      autorewrite with nat in H1.
      specialize (Hbad_nid_clock_zero n1 n2).
      rewrite H in Hbad_nid_clock_zero.
      rewrite H0 in Hbad_nid_clock_zero.
      simpl in Hbad_nid_clock_zero.
      destruct H1 as [[[??]?]?].
      rewrite nid_in_dec_existsb in *.
      mcase_eq in H2; try discriminate.
      lapply Hbad_nid_clock_zero; clear Hbad_nid_clock_zero;
        [ intro Hbad_nid_clock_zero
        | intuition (subst; auto) ].
      lapply Hbad_nid_clock_zero; clear Hbad_nid_clock_zero; auto.
      intros [Heq1 Heq2]; rewrite ?Heq1, ?Heq2 in *.
      inversion H3.
      }
    generalize (Hbad_nid_clock_zero n2); intro Hbncz2.
    generalize (Hbad_nid_clock_zero n1); intro Hbncz1.
    rewrite nid_in_dec_existsb in *;
    nid_cases n1;
      nid_cases n2; simpl in *;
      repeat mcase_eq in Hss; try discriminate;
      rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff in *;
      intuition auto;
      try discriminate;
      apply valid_schedule_cons; simpl; split_all; auto;
      eapply IHsched; eauto; intros; auto;
        intuition (subst; auto); try discriminate;
        repeat match goal with
        | |- context[SysPredefs.override _ ?n1 _ ?n2] =>
          (is_var n1 || is_var n2);
          destruct (NId_eq_dec n1 n2);
          [ subst;
            rewrite !SysPredefs.override_new_val
          | rewrite SysPredefs.override_old_val with (k:=n1) (k':=n2);
            auto
          ]
        | _ => progress simpl
        | _ => contradiction
        end;
        try solve
          [ eapply Hbad_nid_clock_zero; intuition auto
          | eapply Hbncz2; intuition auto
          | simpl; simpl_override; eapply Hbncz1; intuition auto
          ].
  Qed.


  Lemma step_fun_complete: forall s l s',
    step s l s' -> exists task, step_fun task s = Some (l,s').
  Proof.
    intros s l s' Hstep.
    inversion Hstep; clear Hstep.
    * clear max_nid_eq; subst.
    exists (SchedProc n).
    unfold step_fun.
    rewrite nids_eq in *.
    rewrite nid_in_dec_existsb in *.
    simpl.
    destruct (List.in_dec NId_eq_dec n SysPredefs.nids); try contradiction.
    simpl_override.
    simpl.
    subst u' d' r' m'.
    f_equal.
    f_equal.
    apply functional_extensionality; intros.
    case_eq (n =? x); autorewrite with nat; intros; subst;
      simpl_override; auto.
    * exists (SchedProc n).
    unfold step_fun, SysPredefs.init_nid in *.
    rewrite ?nids_eq in *.
    rewrite ?nid_in_dec_existsb in *.
    rewrite <-?max_nid in *.
    simpl.
    mcase_eq; try contradiction.
    simpl_override.
    simpl.
    subst n'' c'' d'' d' v s l s'.
    f_equal.
    f_equal.
    simpl_override.
    rewrite max_nid_eq.
    destruct Peano_dec.eq_nat_dec as [Heq | Hneq]; auto;
      [ rewrite Heq, NPeano.Nat.eqb_refl; auto
      | apply EqNat.beq_nat_false_iff in Hneq; rewrite Hneq
      ];
      apply functional_extensionality; intros;
      case_eq (n =? x); autorewrite with nat; intros; subst;
        simpl_override; auto.
    * exists (SchedUpdate n_1 n_2).
    unfold step_fun, SysPredefs.init_nid in *.
    rewrite ?nids_eq in *.
    rewrite ?nid_in_dec_existsb in *.
    rewrite <-?max_nid in *.
    simpl.
    destruct (List.in_dec NId_eq_dec n_1 SysPredefs.nids); try contradiction.
    subst k v d r_1' m_1'.
    simpl_override.
    simpl.
    apply EqNat.beq_nat_false_iff in H0; rewrite H0.
    case_eq (NPeano.ltb (r_1 n_2) (Datatypes.length u_2));
      autorewrite with nat; intro; try omega.
    match goal with
      | H: List.Forall ?f ?l |- context[List.forallb _ _] =>
        rewrite List.Forall_forall in H;
        setoid_rewrite <-NPeano.leb_le in H;
        apply <-List.forallb_forall in H;
        rewrite H
      end.
    simpl.
    simpl_override.
    f_equal.
    f_equal.
    apply EqNat.beq_nat_false_iff in H0.
    rewrite override_neq with (n1:=n_1) (n2:=n_2); auto.
    rewrite override_eq.
    rewrite override_neq with (n1:=n_1) (n2:=n_2); auto.
    rewrite override_eq.
    rewrite override_neq with (n1:=n_1) (n2:=n_2); auto.
    * clear max_nid_eq; subst.
    exists (SchedProc n).
    unfold step_fun.
    rewrite nids_eq in *.
    rewrite nid_in_dec_existsb in *.
    simpl.
    destruct (List.in_dec NId_eq_dec n SysPredefs.nids); try contradiction.
    simpl_override.
    simpl.
    f_equal.
    f_equal.
    apply functional_extensionality; intros.
    case_eq (n =? x); autorewrite with nat; intros; subst;
      simpl_override; auto.
  Qed.

  Lemma state_eq_override: forall s n p u d r m,
    s n = node_state p u d r m ->
    s = SysPredefs.override s n (node_state p u d r m).
  Proof.
    intros.
    apply functional_extensionality; intros.
    case_eq (n =? x);
      autorewrite with nat; intros; subst;
      simpl_override;
      auto.
  Qed.

  Lemma nid_eq_equiv: forall {A} (t1 t2: A) n1 n2,
    (if n1 =_? n2 then t1 else t2) = (if n1 =? n2 then t1 else t2).
  Proof.
    intros.
    destruct Peano_dec.eq_nat_dec as [Heq | Hneq]; subst; auto.
    rewrite NPeano.Nat.eqb_refl; auto.
    apply EqNat.beq_nat_false_iff in Hneq; rewrite Hneq; auto.
  Qed.

  Lemma step_fun_sound: forall task s l s',
    step_fun task s = Some (l,s') ->
    step s l s'.
  Proof.
    intros task s l s' Hstep.
    unfold step_fun, SysPredefs.init_nid in *.
    rewrite ?nids_eq in *.
    rewrite ?nid_in_dec_existsb in *.
    rewrite <-?max_nid in *.
    simpl.
    destruct task; simpl in Hstep.
    * case_eq (s n); intros ? ? ? ? ? Heq; rewrite Heq in *.
    rewrite nid_in_dec_existsb in *.
    destruct (List.in_dec NId_eq_dec n SysPredefs.nids); try discriminate.
    destruct prog0;
      inversion Hstep; clear Hstep; subst.
    - apply state_eq_override in Heq.
    rewrite Heq at 1.
    constructor; auto.
    - apply state_eq_override in Heq.
    rewrite Heq at 1.
    rewrite <-nid_eq_equiv in *.
    constructor; auto.
    - apply state_eq_override in Heq.
    rewrite Heq at 1.
    constructor; auto.
    * case_eq (s n1); intros ? ? ? ? ? Heq1; rewrite Heq1 in *.
    case_eq (s n2); intros ? ? ? ? ? Heq2; rewrite Heq2 in *.
    rewrite nid_in_dec_existsb in *.
    destruct (NId_eq_dec n1 n2); subst.
    rewrite NPeano.Nat.eqb_refl in *.
    inversion Hstep; clear Hstep; subst.
    inversion Hstep; clear Hstep; subst.
    apply EqNat.beq_nat_false_iff in n; rewrite n in *.
    apply EqNat.beq_nat_false_iff in n.
    destruct (List.in_dec NId_eq_dec n1 SysPredefs.nids); try discriminate.
    case_eq (NPeano.ltb (rec0 n2) (Datatypes.length ptrace1));
      intro Hltb_eq; rewrite ?Hltb_eq in *;
      case_eq (List.forallb
            (fun pid : PutId =>
             NPeano.leb (put_id_clock pid) (rec0 (put_id_nid pid)))
            (t_put_dep (List.nth (rec0 n2) ptrace1 dummy_t_put)));
      intro Hforall_eq; rewrite ?Hforall_eq in *;
      simpl in *;
      try (inversion H0; clear H0; subst).
    autorewrite with nat in *.
    apply state_eq_override in Heq1.
    apply state_eq_override in Heq2.
    rewrite Heq2 at 1.
    rewrite Heq1 at 1.
    constructor; auto.
    apply List.Forall_forall.
    setoid_rewrite <-NPeano.leb_le.
    apply ->List.forallb_forall.
    auto.
  Qed.

  Lemma step_star_not_in_nids: forall s ls s' n,
    step_star s ls s' ->
    ~List.In n nids ->
    prog (s n) = prog (s' n).
  Proof.
    intros.
    rewrite nids_eq in *.
    induction H using rev_step_star_ind; auto.
    rewrite <-IHstep_star; clear IHstep_star.
    inversion H; clear H; subst.
    * destruct (NId_eq_dec n0 n) as [Heq | Hneq].
    rewrite !Heq in *.
    contradiction.
    simpl_override.
    reflexivity.
    * destruct (NId_eq_dec n0 n) as [Heq | Hneq].
    rewrite !Heq in *.
    contradiction.
    simpl_override.
    reflexivity.
    * destruct (NId_eq_dec n n_1);
      destruct (NId_eq_dec n n_2);
      try subst;
      try contradiction;
      simpl_override;
      reflexivity.
    * destruct (NId_eq_dec n0 n) as [Heq | Hneq].
    rewrite !Heq in *.
    contradiction.
    simpl_override.
    reflexivity.
  Qed.


  Lemma step_star_fun_complete: forall s ls s',
    step_star s ls s' -> exists sched, step_star_fun nil sched s = Some (ls,s').
  Proof.
    intros s ls s' Hss.
    induction Hss using rev_step_star_ind.
    exists nil; reflexivity.
    destruct IHHss as [sched ?].
    edestruct step_fun_complete as [task ?]; eauto.
    exists (task::sched)%list.
    simpl.
    rewrite H1.
    rewrite <-List.app_nil_r with (l:=[l]).
    change (l::ls)%list with ([l]++ls)%list.
    apply prefix_step_star_fun; auto.
  Qed.

  Lemma step_star_fun_sound: forall sched s ls1 ls2 s',
    step_star_fun ls1 sched s = Some (ls1++ls2,s')%list ->
    step_star s ls2 s'.
  Proof.
    intros sched s ls1 ls2 s' Hss.
    revert s ls1 ls2 s' Hss.
    induction sched; simpl; intros.
    inversion Hss; clear Hss; subst s'; try subst.
    * rewrite List.app_nil_end in H0 at 1.
    apply List.app_inv_head in H0; subst ls2.
    constructor.
    * case_eq (step_fun a s).
    intros [??] Hs; rewrite Hs in *.
    edestruct prefix_inv_step_star_fun as [ls3[Heq _]]; eauto.
    rewrite <-List.app_assoc in Heq.
    apply List.app_inv_head in Heq; subst ls2.
    rewrite List.app_assoc in Hss.
    apply IHsched in Hss.
    apply step_fun_sound in Hs.
    eapply step_star_end; eauto.
    intro Hs; rewrite Hs in *; discriminate.
  Qed.


  Fixpoint fast_check_all_schedules (nids: list SysPredefs.NId) (N: nat) s (check: State -> bool) {struct N} : bool :=
    match N with
    | O => true
    | S N' =>
      (* forall n1 \in proceses *)
      List.forallb
        (fun n1 =>
          (* schedule process n1 *)
          match fast_step_fun (SchedProc n1) s with
          | Some s' =>
            check s' &&
            fast_check_all_schedules nids N' s' check
          | None => true
          end
          &&
          (* schedule an update from n1 to any n2 \in processes *)
          List.forallb
            (fun n2 =>
              match fast_step_fun (SchedUpdate n1 n2) s with
              | Some s' =>
                check s' &&
                fast_check_all_schedules nids N' s' check
              | None => true
              end)
            nids)
        nids
    end%bool%list.


  Fixpoint check_all_schedules' (nids: list SysPredefs.NId) (N: nat) s (check: Label -> State -> bool) {struct N} : bool :=
    match N with
    | O => true
    | S N' =>
      (* forall n1 \in proceses *)
      List.forallb
        (fun n1 =>
          (* schedule process n1 *)
          match step_fun (SchedProc n1) s with
          | Some (l', s') =>
            check l' s' &&
            check_all_schedules' nids N' s' check
          | None => true
          end
          &&
          (* schedule an update from n1 to any n2 \in processes *)
          List.forallb
            (fun n2 =>
              match step_fun (SchedUpdate n1 n2) s with
              | Some (l', s') =>
                check l' s' &&
                check_all_schedules' nids N' s' check
              | None => true
              end)
            nids)
        nids
    end%bool%list.

  Lemma fast_check_all_schedules_correct': forall nids N s check check',
    fast_check_all_schedules nids N s check = true ->
    (forall l s, check s = true -> check' l s = true) ->
    check_all_schedules' nids N s check' = true.
  Proof.
    induction N; intros.
    * reflexivity.
    * unfold check_all_schedules'; fold check_all_schedules'.
    unfold fast_check_all_schedules in H; fold fast_check_all_schedules in H.
    rewrite List.forallb_forall in *.
    setoid_rewrite Bool.andb_true_iff.
    setoid_rewrite List.forallb_forall.
    setoid_rewrite Bool.andb_true_iff in H.
    setoid_rewrite List.forallb_forall in H.
    intros n1 Hin1.
    specialize (H n1 Hin1).
    mcase_eq. destruct p.
    apply fast_step_correct in H1.
    rewrite H1 in H.
    rewrite Bool.andb_true_iff in *.
    destruct H as [[??]?].
    split_all; auto.
    eapply IHN; eauto.
    intros n2 Hin2.
    mcase_eq; auto. destruct p.
    apply fast_step_correct in H4.
    specialize (H3 n2 Hin2).
    rewrite H4 in H3.
    rewrite Bool.andb_true_iff in *.
    destruct H3.
    split; eauto.
    split; auto.
    intros n2 Hin2.
    mcase_eq; auto. destruct p.
    apply fast_step_correct in H2.
    destruct H as [_ H].
    specialize (H n2 Hin2).
    rewrite H2 in H.
    rewrite Bool.andb_true_iff in *.
    destruct H.
    split; eauto.
  Qed.

  Fixpoint check_all_schedules (nids: list SysPredefs.NId) (N: nat) ls (prefix:list ScheduleTask) s (check: list Label -> State ->bool) {struct N} : bool :=
    (match step_star_fun ls prefix s with
    | Some (ls', s') =>
      (* chec the current schedule (whatever the length) *)
      check ls' s' &&
      (* add a new step to the schedule *)
      match N with
      | O => true
      | S N' =>
        (* forall n1 \in proceses *)
        List.forallb
          (fun n1 =>
            (* schedule process n1 *)
            check_all_schedules nids N' ls' (SchedProc n1::nil) s' check &&
            (* schedule an update from n1 to any n2 \in processes *)
            List.forallb
              (fun n2 => check_all_schedules nids N' ls' (SchedUpdate n1 n2::nil) s' check)
              nids
          )
          nids
      end
    | None => true
    end)%bool%list.

  Lemma check_all_schedules'_correct_fun_equiv: forall max_steps check s,
    (check_all_schedules' nids max_steps s check = true
    <->
    (forall sched task ls l s' s'',
      valid_schedule nids (sched++[task]) ->
      List.length sched < max_steps ->
      step_star_fun nil sched s = Some (ls,s') ->
      step_fun task s' = Some (l,s'') ->
      check l s'' = true)).
  Proof.
    split; intros.
    * rewrite nids_eq in *.
    rename H into Hperm.
    rename H0 into Hvalid_sched.
    rename H1 into Hsched_len.
    rename H2 into Hss.
    rename H3 into Hs.
    revert sched task ls l Hsched_len s s' s'' Hvalid_sched Hperm Hss Hs.
    clear max_nid_eq.
    induction max_steps; intros; subst.
    destruct sched; inversion Hsched_len.
    apply valid_schedule_app in Hvalid_sched.
    unfold check_all_schedules' in Hperm.
    fold check_all_schedules' in Hperm.
    rewrite List.forallb_forall in Hperm.
    setoid_rewrite Bool.andb_true_iff in Hperm.
    setoid_rewrite List.forallb_forall in Hperm.
    destruct Hvalid_sched as [Hvalid_sched Hin].
    apply valid_schedule_cons in Hin; destruct Hin as [Hin _].    
    destruct sched as [ | task' sched ].
    - simpl in Hss; inversion Hss; clear Hss; subst.
    destruct task as [ n1 | n1 n2 ];
      [ (* SchedProc n1 *)
        specialize (Hperm n1 Hin);
        destruct Hperm as [Hcheck _];
        rewrite Hs in Hcheck;
        apply Bool.andb_true_iff in Hcheck; tauto
      | (* SchedUpdate n1 n2 *)
        destruct Hin as [Hin1 Hin2];
        specialize (Hperm n1 Hin1);
        destruct Hperm as [_ HcheckUpd];
        specialize (HcheckUpd n2 Hin2);
        rewrite Hs in HcheckUpd;
        apply Bool.andb_true_iff in HcheckUpd; tauto
      ].
    - simpl in Hsched_len.
    apply Lt.lt_S_n in Hsched_len.
    simpl in Hss.
    apply valid_schedule_cons in Hvalid_sched.
    destruct Hvalid_sched as [Hin' Hvalid_sched].
    repeat mcase_eq in Hss; try congruence; subst.
    apply prefix_inv_step_star_fun in Hss.
    destruct Hss as [ls3[Heq Hss]]; subst ls.
    destruct task' as [ n1 | n1 n2 ].
    + (* SchedProc n1 *)
    specialize (Hperm n1 Hin').
    destruct Hperm as [Hcheck _].
    rewrite H in Hcheck.
    apply Bool.andb_true_iff in Hcheck.
    destruct Hcheck as [Hcheck Hcheck_all].
    eapply IHmax_steps with (s:=s0) (s':=s'); eauto.
    apply valid_schedule_app; split; auto.
    apply valid_schedule_cons; split; auto; constructor.
    + (* SchedUpdate n1 n2 *)
    destruct Hin' as [Hin1' Hin2'].
    specialize (Hperm n1 Hin1').
    destruct Hperm as [_ HcheckUpd].
    specialize (HcheckUpd n2 Hin2').
    rewrite H in HcheckUpd.
    apply Bool.andb_true_iff in HcheckUpd.
    destruct HcheckUpd as [Hcheck Hcheck_all].
    eapply IHmax_steps with (s:=s0) (s':=s'); eauto.
    apply valid_schedule_app; split; auto.
    apply valid_schedule_cons; split; auto; constructor.

    * rename H into Hss.
    revert s Hss.
    clear max_nid_eq.
    induction max_steps; intros; subst.
    - reflexivity.
    - unfold check_all_schedules'; fold check_all_schedules'.
    rewrite List.forallb_forall.
    setoid_rewrite Bool.andb_true_iff.
    setoid_rewrite List.forallb_forall.
    intros n1 Hin1.
    split.
    + mcase_eq; auto.
    destruct p as [l s'].
    rewrite Bool.andb_true_iff.
    split.
    eapply Hss with (sched:=nil) (ls:=nil); simpl; eauto.
    apply valid_nid_step_fun_Proc in H.
    apply valid_schedule_cons; split; auto; constructor.
    omega.
    eapply IHmax_steps; eauto.
    intros sched task ls l' s'' s''' Hvalid_sched Hsched_len Hss' Hs''.
    eapply Hss with (sched:=([SchedProc n1]++sched)%list) (ls:=([l]++ls)%list); eauto.
    rewrite <-List.app_assoc.
    apply valid_schedule_app; split; auto.
    apply valid_schedule_cons; split; auto; constructor.
    simpl; omega.
    rewrite step_star_fun_app.
    unfold step_star_fun; fold step_star_fun.
    rewrite H.
    simpl.
    apply prefix_step_star_fun with (ls3:=[l]); auto.
    + intros n2 Hin2.
    mcase_eq; auto.
    destruct p as [l s'].
    rewrite Bool.andb_true_iff.
    split.
    eapply Hss with (sched:=nil) (ls:=nil); simpl; eauto.
    apply valid_nid_step_fun_Update in H.
    apply valid_schedule_cons; split; auto; constructor.
    omega.
    eapply IHmax_steps; eauto.
    intros sched task ls l' s'' s''' Hvalid_sched Hsched_len Hss' Hs''.
    eapply Hss with (sched:=([SchedUpdate n1 n2]++sched)%list) (ls:=([l]++ls)%list); eauto.
    rewrite <-List.app_assoc.
    apply valid_schedule_app; split; auto.
    apply valid_schedule_cons; split; auto; constructor.
    simpl; omega.
    rewrite step_star_fun_app.
    unfold step_star_fun; fold step_star_fun.
    rewrite H.
    simpl.
    apply prefix_step_star_fun with (ls3:=[l]); auto.
  Qed.

  Lemma check_all_schedules'_correct: forall max_steps check s,
    check_all_schedules' nids max_steps s check = true ->
    forall task sched ls l' s' s'',
      valid_schedule nids (sched++[task]) ->
      List.length sched < max_steps ->
      step_star_fun nil sched s = Some (ls, s') ->
      step_fun task s' = Some (l', s'') ->
      check l' s'' = true.
  Proof.
    intros.
    eapply check_all_schedules'_correct_fun_equiv; eauto.
  Qed.

  Definition check_no_fault' (l: StepStarArgs.Label) (s: State) :=
    match l with
    | fault_label _ => false
    | _ => true
    end.

  Lemma step_star_fun_cons_inv: forall sched s l ls s'',
    step_star_fun nil sched s = Some (l :: ls, s'')%list ->
    exists task s' sched',
      sched = (task::sched')%list /\
      step_fun task s = Some (l, s') /\
      step_star_fun nil sched' s' = Some (ls, s'').
  Proof.
    intros.
    clear max_nid_eq.
    revert s l ls s'' H.
    destruct sched as [ | task sched]; simpl; intros.
    * inversion H; clear H; subst.
    * mcase_eq as Hs in H; try discriminate.
    destruct p.
    apply prefix_inv_step_star_fun in H as [ls3[Heq Hss]].
    simpl in Heq.
    inversion Heq; clear Heq; subst l0 ls3.
    exists task; exists s0; exists sched; simpl; split_all; auto.
  Qed.

  Lemma step_star_fun_app_inv: forall sched s ls1 ls2 s'',
    step_star_fun nil sched s = Some (ls1 ++ ls2, s'')%list ->
    exists sched1 s' sched2,
      sched = (sched1 ++ sched2)%list /\
      step_star_fun nil sched1 s = Some (ls1, s') /\
      step_star_fun nil sched2 s' = Some (ls2, s'').
  Proof.
    intros.
    clear max_nid_eq.
    revert s sched ls2 s'' H.
    induction ls1; simpl; intros.
    * exists nil; exists s; exists sched; simpl; split; auto.
    * apply step_star_fun_cons_inv in H.
    destruct H as [task[s'[sched'[Heq[Hs Hss]]]]]; subst sched.
    apply IHls1 in Hss.
    destruct Hss as [sched1[s'0[sched2[Heq[Hss1 Hss2]]]]]; subst sched'.
    exists (task::sched1)%list; exists s'0; exists sched2; simpl; split_all; auto.
    rewrite Hs.
    apply prefix_step_star_fun with (ls3:=[a]); auto.
  Qed.

  Lemma prove_no_fault': forall program h s n run_steps,
    StepStar.step_star (init program) h s ->
    (forall sched_length,
      check_all_schedules' nids (run_steps + sched_length)
        (init program) check_no_fault' = true) ->
    (forall l, List.In l h -> l <> fault_label n).
  Proof.
    intros program h s n run_steps Hss Hcheck_scheds.
    generalize (step_star_not_in_nids _ _ _ n Hss);
      intro Hnot_nids_eq.
    apply step_star_fun_complete in Hss.
    destruct Hss as [sched Hss].
    intros l Hin.
    apply List.in_split in Hin.
    destruct Hin as [h1[h2 Heq]]; subst h.
    apply step_star_fun_app_inv in Hss.
    destruct Hss as [sched1[s'[sched2'[Heq[Hss1 Hss2]]]]]; subst sched.
    apply step_star_fun_cons_inv in Hss2.
    destruct Hss2 as [task[s''[sched2[Heq[Hs Hss2]]]]]; subst sched2'.
    eapply check_all_schedules'_correct
      with (check:=check_no_fault') (max_steps:= run_steps + (S (List.length sched1)))
      in Hss1; eauto.
    * unfold check_no_fault' in Hss1.
    destruct l; try discriminate.
    * eapply valid_schedule_step_star_fun
      with (ls1:=nil) (sched:=(sched1++[task])%list) (prog0:=program); eauto.
    rewrite step_star_fun_app, Hss1.
    simpl; rewrite Hs; reflexivity.
    * omega.
  Qed.

  Definition check_no_fault'' nids (s: State) :=
    List.forallb
      (fun n =>
        match prog (s n) with
        | KVStore.fault => false
        | _ => true
        end)
      nids%bool.

  Lemma step_label_check_no_fault'': forall task s l s' n,
    step_fun task s = Some (l, s') ->
    check_no_fault'' nids s = true ->
    l <> fault_label n.
  Proof.
    unfold step_fun, check_no_fault''; intros.
    clear max_nid_eq.
    repeat (
      mcase_eq in H;
      repeat match goal with
      | H: Some _ = Some _ |- _ => inversion H; clear H; subst
      | _ => rewrite nid_in_dec_existsb in *
      | _ => discriminate
      end).
    rewrite List.forallb_forall in H0.
    specialize (H0 n0 i).
    rewrite H3 in H0.
    simpl in H0.
    discriminate.
  Qed.


  Lemma fast_prove_no_fault: forall program h s n run_steps,
    StepStar.step_star (init program) h s ->
    (forall n, program n <> fault) ->
    (forall sched_length,
      fast_check_all_schedules nids (run_steps + sched_length)
        (init program) (check_no_fault'' nids) = true) ->
    (forall l, List.In l h -> l <> fault_label n).
  Proof.
    intros program h s n run_steps Hss Hinit_no_fault Hcheck_scheds.
    intros l Hin.
    generalize (step_star_not_in_nids _ _ _ n Hss);
      intro Hnot_nids_eq.
    apply step_star_fun_complete in Hss.
    destruct Hss as [sched Hss].
    apply List.in_split in Hin.
    destruct Hin as [h1[h2 Heq]]; subst h.
    apply step_star_fun_app_inv in Hss.
    destruct Hss as [sched1[s'[sched2'[Heq[Hss1 Hss2]]]]]; subst sched.
    apply step_star_fun_cons_inv in Hss2.
    destruct Hss2 as [task[s''[sched2[Heq[Hs _]]]]]; subst sched2'.
    eapply step_label_check_no_fault''; eauto.
    clear task Hs.
    clear max_nid_eq.
    destruct (list_end _ sched1) as [Heq | [sched[task Heq]]]; subst sched1.
    * simpl in Hss1.
    inversion Hss1; clear Hss1; subst.
    unfold check_no_fault''.
    apply List.forallb_forall.
    intros n1 Hin1.
    simpl.
    mcase_eq; auto.
    exfalso.
    eapply Hinit_no_fault; eauto.
    * rewrite step_star_fun_app in Hss1.
    mcase_eq as Hss in Hss1; try discriminate.
    destruct p.
    simpl in Hss1.
    mcase_eq as Hs in Hss1; try discriminate.
    destruct p.
    inversion Hss1; clear Hss1; subst h1 s1.
    eapply check_all_schedules'_correct
      with (check:=fun l s => check_no_fault'' nids s) (max_steps:= run_steps + (S (List.length sched)))
        (sched:=sched) (task:=task) (s':=s0);
      eauto.
    - eapply fast_check_all_schedules_correct'; eauto.
    - eapply valid_schedule_step_star_fun
      with (ls1:=nil) (sched:=(sched++[task])%list) (prog0:=program); eauto.
    rewrite step_star_fun_app, Hss.
    simpl; rewrite Hs; reflexivity.
    - omega.
  Qed.

  Lemma check_all_schedules_correct_fun_equiv: forall max_steps ls1 sched1 check s,
    (check_all_schedules nids max_steps ls1 sched1 s check = true
    <->
    (forall sched2 ls s',
      valid_schedule nids sched2 ->
      List.length sched2 <= max_steps ->
      step_star_fun ls1 (sched1 ++ sched2)%list s = Some (ls,s') ->
      check ls s' = true)).
  Proof.
    split; intros.
    rewrite nids_eq in *.
    * rename H0 into Hvalid_sched.
    rename H into Hperm.
    rename H1 into Hsched_len.
    rename H2 into Hss.
    revert ls1 sched2 Hsched_len sched1 s s' Hvalid_sched Hperm Hss.
    clear max_nid_eq.
    induction max_steps; simpl; intros; subst.
    - destruct sched2; inversion Hsched_len.
    rewrite List.app_nil_r in *.
    rewrite Hss in Hperm.
    rewrite !Bool.andb_true_iff in *.
    apply Hperm.
    - repeat mcase_eq in Hperm; subst.
    rewrite !Bool.andb_true_iff in *.
    destruct Hperm as [Heq Hperm].
    rewrite List.forallb_forall in Hperm.
    setoid_rewrite Bool.andb_true_iff in Hperm.
    setoid_rewrite List.forallb_forall in Hperm.
    destruct sched2 as [ | [ n1 | n1 n2 ] sched2 ].
    + rewrite List.app_nil_r in *; intuition (subst; auto).
    rewrite H in Hss; inversion Hss; clear Hss; subst; auto.
    + simpl in Hsched_len; apply le_S_n in Hsched_len.
    apply valid_schedule_cons in Hvalid_sched.
    rewrite step_star_fun_app, H in Hss.
    destruct Hvalid_sched as [Hin Hvalid_sched].
    simpl in Hin.
    rewrite <-nids_eq in *.
    eapply IHmax_steps with (s:=s0) (sched1:=[SchedProc n1]%list) (sched2:=sched2); auto.
    eapply Hperm; eauto.
    intuition (subst; eauto).
    + simpl in Hsched_len; apply le_S_n in Hsched_len.
    apply valid_schedule_cons in Hvalid_sched.
    rewrite step_star_fun_app, H in Hss.
    destruct Hvalid_sched as [Hin Hvalid_sched].
    simpl in Hin.
    eapply IHmax_steps with (sched1:=[SchedUpdate n1 n2]%list); eauto.
    eapply Hperm; apply Hin.
    + rewrite step_star_fun_app, H in Hss; discriminate. 
    * rename H into Hss.
    revert ls1 sched1 s Hss.
    clear max_nid_eq.
    induction max_steps; simpl; intros; subst.
    - repeat mcase_eq; subst; auto.
    rewrite Bool.andb_true_r; auto.
    apply (Hss nil); simpl; auto.
    constructor.
    rewrite List.app_nil_r; auto.
    - repeat mcase_eq; subst; auto.
    rewrite !Bool.andb_true_iff in *.
    rewrite List.forallb_forall.
    setoid_rewrite Bool.andb_true_iff.
    setoid_rewrite List.forallb_forall.
    split; intros; split_all; intros;
      try match goal with
      | Hss: context[_ -> check _ _ = true],
        IH: context[check_all_schedules _ _ _ _ _ _ = true]
        |- check_all_schedules _ _ _ _ _ _ = true =>
        eapply IHmax_steps;
        repeat match goal with |- _->?a => fail 1 | |- forall _:_, _ => intro end;
        intros;
        eapply (Hss (_::_)%list); simpl;
          [ | | rewrite step_star_fun_app, H; eauto];
          [ eapply valid_schedule_cons; split; auto; simpl; auto
          | omega
          ]
      | |- true = true => reflexivity
      end.
    apply (Hss nil); simpl.
    constructor.
    omega.
    rewrite List.app_nil_r; auto.
  Qed.

  Lemma check_all_schedules_correct: forall max_steps ls1 sched1 sched2 check s ls' s',
    valid_schedule nids sched2 ->
    List.length sched2 <= max_steps ->
    step_star_fun ls1 (sched1 ++ sched2)%list s = Some (ls', s') ->
    check_all_schedules nids max_steps ls1 sched1 s check = true ->
    check ls' s' = true.
  Proof.
    intros.
    eapply check_all_schedules_correct_fun_equiv; eauto.
  Qed.

  Definition check_no_fault nids (ls: list StepStarArgs.Label) (s: State) :=
    (List.forallb
      (fun l =>
        match l with
        | fault_label _ => false
        | _ => true
        end)
      ls &&
    List.forallb
      (fun n =>
        match prog (s n) with
        | KVStore.fault => false
        | _ => true
        end)
      nids)%bool.

  Lemma prove_no_fault: forall program h s n run_steps,
    StepStar.step_star (init program) h s ->
    (forall n,
      ~List.In n nids ->
      program n <> fault) ->
    (forall sched_length,
      check_all_schedules nids (run_steps + sched_length) nil
        nil (init program) (check_no_fault nids) = true) ->
    AbsExec.prog (s n) <> fault /\ (forall l, List.In l h -> l <> fault_label n).
  Proof.
    intros program h s n run_steps Hss Hnot_nit_no_fault Hcheck_scheds.
    generalize (step_star_not_in_nids _ _ _ n Hss);
      intro Hnot_nids_eq.
    apply step_star_fun_complete in Hss.
    destruct Hss as [sched Hss].
    eapply check_all_schedules_correct
      with (sched1:=nil) (check:=check_no_fault nids) (max_steps:= run_steps + List.length sched)
      in Hss.
    * unfold check_no_fault in Hss.
    apply Bool.andb_true_iff in Hss.
    destruct Hss as [Hno_fault_label Hnot_fault].
    simpl in *.
    rewrite List.forallb_forall in *.
    specialize (Hnot_nit_no_fault n).
    specialize (Hnot_fault n).
    nid_cases n;
      (split;
      [ intro HH;
        try solve
        [ rewrite HH in Hnot_fault;
          simpl in Hnot_fault;
          rewrite ?Bool.andb_false_r in Hnot_fault;
          discriminate
        ]
      | intros l Hin2;
        specialize (Hno_fault_label l Hin2);
        destruct l; try discriminate
      ]).
    clear max_nid_eq.
    destruct (List.in_dec NId_eq_dec n nids) as [Hin | Hnin].
    - specialize (Hnot_fault Hin).
    rewrite HH in Hnot_fault.
    simpl in Hnot_fault.
    rewrite ?Bool.andb_false_r in Hnot_fault.
    discriminate.
    - rewrite <-Hnot_nids_eq in HH; simpl in *; auto.
    intuition (subst; auto).
    * eapply valid_schedule_step_star_fun; eauto.
    * omega.
    * eapply Hcheck_scheds.
  Qed.


End A.

  Ltac fast_casually_content max_nid max_nid_eq steps:=
    match goal with
    |- ?CausallyContent ?prog =>
      hnf; intros;
      eapply (@fast_prove_no_fault max_nid max_nid_eq) with (run_steps:= steps) (program:=prog);
      [ solve[eauto]
      | let n':= fresh "n" in let Hnin:= fresh "Hin" in
        intros n' Hin;
        try abstract (
          let x:= eval compute in max_nid in
          (do_ x try (destruct n' as [ | n']));
          simpl; discriminate
          )
      | vm_compute; reflexivity
      | auto
      ]
    end.

  Ltac casually_content max_nid max_nid_eq steps:=
    match goal with
    |- ?CausallyContent ?prog =>
      hnf; intros;
      eapply (@prove_no_fault max_nid max_nid_eq) with (run_steps:= steps) (program:=prog);
      [ solve[eauto]
      | let n':= fresh "n" in let Hnin:= fresh "Hin" in
        intros n' Hin;
        try abstract (
          let x:= eval compute in max_nid in
          (do_ x try (destruct n' as [ | n']));
          simpl; discriminate
          )
      | vm_compute; reflexivity
      | auto
      ]
    end.

  Ltac casually_content' max_nid max_nid_eq steps:=
    match goal with
    |- ?CausallyContent ?prog =>
      hnf; intros;
      eapply (@prove_no_fault' max_nid max_nid_eq) with (run_steps:= steps) (program:=prog);
      [ solve[eauto]
      | vm_compute; reflexivity
      | auto
      ]
    end.


End ReflAbsSem.


