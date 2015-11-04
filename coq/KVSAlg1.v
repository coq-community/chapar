Require Import Coq.Unicode.Utf8.

Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.Max.
Require Import Coq.Lists.List.
Require Import Program.Equality.
Require Import Coq.Lists.ListSet.
Require Import Coq.Program.Basics.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.EqNat.

Add LoadPath "Lib".
Require Import Predefs.


Require Import KVStore.


(*
Module AlgDefArgs <: AlgDefParams.

  Definition Val := nat.
  Definition init_val := 0.

End AlgDefArgs.
Module Type KVSAlg1 (AlgDefArgs: AlgDefParams).
*)


(* Module Type KVSAlg1. *)
Module KVSAlg1 <: AlgDef.

  Import SysPredefs.
  (* Import AlgDefArgs. *)

  Definition Clock := nat.

  Record StateRec {Val: Type} := {
    store: Key -> Val;
    clock: NId -> Clock
  }.
  Definition state {Val: Type} := @Build_StateRec Val.
  Definition State {Val: Type} := @StateRec Val.

  Record UpdateRec {Val: Type} := {
    sender_node: NId;
    sender_clock: NId -> Clock
  }.
  Definition update := Build_UpdateRec.
  Definition Update {Val: Type} := @UpdateRec Val.

  Definition dummy_update {Val: Type} := update Val 0 (fun n => 0).

  (*
  Definition State (Val: Type): Type := ((Key -> Val) * (NId -> Clock))%type.
  Definition Update (Val: Type): Type := (NId * (NId -> Clock))%type.
  *)

  Section ValParam.
  Variable Val: Type.
  
  Definition init_method (init_val: Val): State :=
    state (fun (k: Key) => init_val) (fun (n: NId) => 0).

  Definition get_method (n: NId)(this: State)(k: Key): (Val * State) :=
    let s := store this in
    let c := clock this in
    ((s k), (state s c)).

  Definition put_method (n: NId)(this: State)(k: Key)(v: Val): (State * Update) :=
    let s := store this in
    let c := clock this in
    let c' := override c n ((c n) + 1) in
    let s' := override s k v in
    ((state s' c'), (update Val n c')).


  Definition guard_method (n: NId)(this: @State Val)(k: Key)(v: Val)(u: @Update Val): bool :=
    let s := store this in
    let c := clock this in
    let n' := sender_node u in
    let c' := sender_clock u in
    ((c' n') =? ((c n') + 1))
    && (fold_left
          (fun b n => b && ((n =? n') || ((c' n) <=? (c n))))
          nids
          true).

  Definition update_method (n: NId)(this: State)(k: Key)(v: Val)(u: @Update Val): State :=
    let s := store this in
    let c := clock this in
    let n' := sender_node u in
    let c' := sender_clock u in
    let c'' := override c n' (c' n') in
    let s'' := override s k v in
    (state s'' c'').

  End ValParam.

End KVSAlg1.
(* Module Type KVSAlg1Def (AlgDefArgs: AlgDefParams) <: AlgDef := KVSAlg1. *)

(*
Module KVSAlg1Causality (SyntaxInst: Syntax)(KVSAlg1Inst: KVSAlg1).

  Module C := Causality SyntaxInst KVSAlg1Inst.
  Import C.
*)


Module KVSAlg1CauseObl (SyntaxArg: SyntaxPar) <: CauseObl KVSAlg1 SyntaxArg.

  (* Module Type InstExecToAbsExecPar (AlgDef: AlgDef)(SyntaxArg: SyntaxPar). *)

  Export SysPredefs.

  Module CExec := ConcExec SyntaxArg KVSAlg1.
  Import CExec.
  Module SExec := SeqExec SyntaxArg.
  Import SExec.
  Module ICExec := InstConcExec SyntaxArg KVSAlg1.
  Import ICExec.

  Lemma step_star_clock_nondec:
    forall (h: list Label)(s s': State)(n: NId),
        let sc := clock (alg_state ((node_states s) n)) in
        let sc' := clock (alg_state ((node_states s') n)) in
        step_star s h s'
        -> forall n', sc n' <= sc' n'.

    Proof.
      intros.
      induction H.
      apply Le.le_refl.
      rename sc' into sc''.
      pose (sc' := clock (alg_state (node_states s2 n))).
      assert (sc' n' <= sc'' n').
      clear H IHstep_star.
      subst sc.
      subst sc'.
      subst sc''.
      inversion H0; clear H0;
      simpl in *.

      (* put *)
      unfold override. unfold key_eq_dec.
      destruct (eq_nat_dec n n0).
        (* --- *)
        simpl.
        unfold SysPredefs.override.
        destruct (eq_nat_dec n' n0).
          (* --- *)
          subst. 
          rewrite Plus.plus_comm.
          simpl.
          apply Le.le_n_Sn.
          (* --- *)
          apply Le.le_refl.
        (* --- *)
        apply Le.le_refl.

      (* get *)
      unfold override. unfold key_eq_dec.
      destruct (eq_nat_dec n n0).
        (* --- *)
        simpl.
        apply Le.le_refl.
        (* --- *)
        apply Le.le_refl.

      (* update *)
      unfold override.
      destruct (n =_? n0).
        (* --- *)
        simpl.
        unfold override.
        destruct (n' =_? (sender_node u)).
          (* --- *)
          subst. 
          unfold guard_method in H1.
          bool_to_prop_in H1.
          destruct H1 as [H1 H2].
          bool_to_prop_in H1.
          rewrite H1.
          rewrite Plus.plus_comm.
          simpl.
          apply Le.le_n_Sn.
          (* --- *)
          apply Le.le_refl.
        (* --- *)
        apply Le.le_refl.      

      (* fault *)
      destruct (eq_nat_dec n n0).
        simpl_override.
        simpl_override.
        apply Le.le_refl.
        (* --- *)
        simpl_override.
        simpl_override.
        apply Le.le_refl.

      apply Le.le_trans with (m := sc' n');
      assumption.

    Qed.



  Lemma proc_order_clock:
    forall (p: ICExec.Syntax.PProg)(h: list Label)(s: State)(l l': Label)(n: NId),
      (step_star (init p) h s
       /\ prec h l l'
       /\ label_node l = label_node l')
      -> (let c := clock (label_post_state l) n in
          let c' := clock (label_post_state l') n in
          c <= c'
          /\ ((label_node l' = n /\ label_is_put l') -> c < c')).

      Proof.
        intros.
        destruct H as [H1 [H2 H3]].
        assert (L := prec_exec p h s l l').
        depremise L. split.
        assumption.
        assumption.
        destruct L as [h1 L].
        destruct L as [s1 L].
        destruct L as [s' L].
        destruct L as [h2 L].
        destruct L as [s'' L].
        destruct L as [s2 L].
        destruct L as [h3 [L1 [L3 [L4 [L5 L2]]]]].
        assert (M1 := step_star_clock_nondec h2 s' s'' (label_node l) L4 n).
        subst c. subst c'.
        assert (N1 := label_poststate_state s1 s' l L3).
        assert (N2 := label_poststate_state s'' s2 l' L5).
        rewrite N1; clear N1.
        rewrite N2; clear N2.

        assert (L: clock (alg_state (node_states s'' (label_node l))) n
                       ≤ clock (alg_state (node_states s2 (label_node l'))) n
                       ∧ (label_node l' = n ∧ label_is_put l'
                          →  clock (alg_state (node_states s'' (label_node l))) n <
                            clock (alg_state (node_states s2 (label_node l'))) n)).

        clear M1.
        rewrite H3 in *.

        inversion L5.

        (* put *)
        simpl.
        simpl_override.
        simpl.
        simpl_override.
        simpl.
        destruct (eq_nat_dec n n0).
          (* -- *)
          simpl_override.
          split.
          rewrite Plus.plus_comm.
          simpl.
          subst n.
          apply Le.le_n_Sn.
          intro.
          rewrite Plus.plus_comm.
          simpl.
          subst n.
          apply Lt.lt_n_Sn.
          (* -- *)
          simpl_override.
          split.
          apply Le.le_refl.
          intros.
          destruct H6.
          exfalso.
          apply n1.
          symmetry; assumption.

        (* get *)
          simpl.
          simpl_override.
          simpl.
          simpl_override.
          simpl.
          split.
          apply Le.le_refl.
          intros.
          destruct H6.
          contradiction.
          
        
        (* update *)
        simpl.
        split.
        simpl_override.
        simpl.
        simpl_override.
        simpl.
        unfold guard_method in H0.
        bool_to_prop_in H0.
        open_conjs.
        bool_to_prop_in H0.
        destruct (eq_nat_dec (sender_node u) n).
          (* -- *)
          simpl_override.
          rewrite H0.
          rewrite e0.
          rewrite Plus.plus_comm.
          simpl.
          apply Le.le_n_Sn.
          (* -- *)
          simpl_override.
          apply Le.le_refl.
        intro.
        open_conjs.
        contradiction.

        (* fault *)
          simpl.
          simpl_override.
          simpl_override.
          split.
          apply Le.le_refl.
          intros.
          open_conjs.
          contradiction.

        destruct L as [N1 N2].
        split.
          (* -- *)
          rewrite <- H3 in *; clear H3.
          eapply Le.le_trans; eassumption.
          (* -- *)
          clear N1.
          intros.
          depremise N2.
          assumption.
          clear H.
          
          eapply Lt.le_lt_trans; eassumption.
      Qed.

  Lemma get_from_map:
    forall (s s': State)(l: Label),
      (label_is_get l
       /\ step s l s')
      -> let k := label_key l in
         let n' := label_orig_node l in
         let c' := label_clock l in
         let n := label_node l in
         let m := store (alg_state ((node_states s) n)) in
         let iv := m k in
         let ivn := inst_val_nid iv in
         let ivc := inst_val_clock iv in
         (n' = ivn /\ c' = ivc).

    Proof.
      intros.
      open_conjs.
      
      inversion H0.

      (* put *)
        simpl in *.
        rewrite <- H3 in H.
        unfold label_is_get in H.
        contradiction.

      (* get *)
        simpl in *.
        subst n'.
        subst c'.
        subst ivn.
        subst ivc.
        rewrite <- H3.
        simpl.
        subst n'0.
        subst c'0.
        subst u.
        subst iv.
        subst m.
        subst s.
        subst k.
        subst n.
        rewrite <- H3.        
        simpl.
        simpl_override.
        simpl.
        split; reflexivity.

      (* update *)
        simpl in *.
        rewrite <- H4 in H.
        unfold label_is_get in H.
        contradiction.

      (* fault *)
        simpl in *.
        subv_in l H.
        contradiction.

    Qed.

  Lemma put_change:
    forall (s s': State)(l: Label),
      let n := label_node l in
      let c := label_clock l in
      let k := label_key l in
      let m' := store (alg_state (node_states s' n)) in
      let iv := m' k in
      (step s l s'
       /\ label_is_put l)
      -> (inst_val_nid iv = n
          /\ inst_val_clock iv = c).

    Proof.
      intros.
      destruct H as [H1 H2].
      inversion H1.

      clear H2.
      subst iv.
      subst m'.
      subst s'.
      simpl.
      subst n.
      subst c.
      subst k.
      subst l.
      simpl.
      simpl_override.
      simpl.
      simpl_override.
      simpl.
      split; reflexivity.

      rewrite <- H3 in H2; unfold label_is_put in H2; inversion H2.
      rewrite <- H4 in H2; unfold label_is_put in H2; inversion H2.
      rewrite <- H3 in H2; unfold label_is_put in H2; inversion H2.

    Qed.


  Lemma put_nochange:
    forall (s s': State)(l: Label),
      let n := label_node l in
      let k := label_key l in
      let m := store (alg_state (node_states s n)) in
      let m' := store (alg_state (node_states s' n)) in
      (step s l s'
       /\ label_is_put l)
      -> (forall k', 
            (not (k = k'))
            -> m k' = m' k').

    Proof.
      intros.
      open_conjs.

      inversion H.
      subst m.
      subst m'.
      subst s.
      subst s'.
      simpl.
      destruct (eq_nat_dec n n0).
        simpl_override.
        simpl_override.
        simpl.
        subst k.
        rewrite <- H4 in H0. simpl in H0.
        simpl_override.
        reflexivity.
        simpl_override.
        simpl_override.
        reflexivity.

      rewrite <- H4 in H1; unfold label_is_put in H1; inversion H1.
      rewrite <- H5 in H1; unfold label_is_put in H1; inversion H1.
      rewrite <- H4 in H1; unfold label_is_put in H1; inversion H1.
      
    Qed.

  Lemma update_change:
    forall (s s': State)(l: Label),
      let n' := label_orig_node l in
      let c := label_clock l in
      let n := label_node l in
      let k := label_key l in
      let m' := store (alg_state (node_states s' n)) in
      let iv := m' k in
      (step s l s'
       /\ label_is_update l)
      -> (inst_val_nid iv = n'
          /\ inst_val_clock iv = c).

    Proof.
      intros.
      destruct H as [H1 H2].
      inversion H1.

      rewrite <- H3 in H2; unfold label_is_update in H2; inversion H2.
      rewrite <- H3 in H2; unfold label_is_get in H2; inversion H2.

      clear H2.
      subst iv.
      subst m'.
      subst s'.
      simpl.
      subst n'.
      subst c.
      subst k.
      subst n.
      subst l.
      simpl.
      simpl_override.
      simpl.
      simpl_override.
      simpl.
      split; reflexivity.

      rewrite <- H3 in H2; unfold label_is_update in H2; inversion H2.      
    Qed.



  Lemma get_nochange:
    forall (s s': State)(l: Label)(n: NId),
      let m := store (alg_state (node_states s n)) in
      let m' := store (alg_state (node_states s' n)) in
      (step s l s'
       /\ label_is_get l)
      -> m = m'.

    Proof.
      intros.
      open_conjs.
      inversion H.

      rewrite <- H3 in H0; unfold label_is_put in H0; inversion H0.

      subst m.
      subst m'.
      subst s.
      subst s'.
      simpl.
      unfold override.
      destruct (eq_nat_dec n n0).
        simpl. reflexivity.
        reflexivity.

      rewrite <- H4 in H0; unfold label_is_put in H0; inversion H0.

      rewrite <- H3 in H0; unfold label_is_put in H0; inversion H0.      
    Qed.

  Lemma update_nochange:
    forall (s s': State)(l: Label),
      let n := label_node l in
      let k := label_key l in
      let m := store (alg_state (node_states s n)) in
      let m' := store (alg_state (node_states s' n)) in
      (step s l s'
       /\ label_is_update l)
      -> (forall k', 
            (not (k = k'))
            -> m k' = m' k').

    Proof.
      intros.
      open_conjs.
      inversion H.

      rewrite <- H4 in H1; unfold label_is_put in H1; inversion H1.
      rewrite <- H4 in H1; unfold label_is_put in H1; inversion H1.

      subst m.
      subst m'.
      subst s.
      subst s'.
      simpl.
      unfold override.
      destruct (eq_nat_dec n n0).
        simpl.
        subst k. rewrite <- H5 in H0. simpl in H0.
        simpl_override.
        reflexivity.
      reflexivity.      

      rewrite <- H4 in H1; unfold label_is_put in H1; inversion H1.
    Qed.

  Lemma node_nochange:
    forall (s s': State)(l: Label)(n': NId),
      let n := label_node l in
      let m := store (alg_state (node_states s n')) in
      let m' := store (alg_state (node_states s' n')) in
      (step s l s'
      /\ not (n = n'))
      -> m = m'.

    Proof.
      intros.
      open_conjs.

      inversion H;

      subst m;
      subst m';
      subst s;
      subst s';
      simpl;
      subst n;
      subst l;
      simpl in *;
      simpl_override;
      simpl_override;
      reflexivity.
    Qed.

  Lemma in_map_from_put_update:
    forall (p: ICExec.Syntax.PProg)(h: list Label)(s: State)(k: Key)(n: NId),
      step_star (init p) h s
      -> let m := store (alg_state ((node_states s) n)) in
         let iv := m k in
         let ivn := inst_val_nid iv in
         let ivc := inst_val_clock iv in
         (ivn = init_nid /\ ivc = 0)
         \/ (exists (l: Label),
               (In l h
                /\ label_is_put l
                /\ label_node l = ivn
                /\ label_clock l = ivc
                /\ label_node l = n)
               \/ (In l h
                   /\ label_is_update l
                   /\ label_orig_node l = ivn
                   /\ label_clock l = ivc
                   /\ label_node l = n)).

    Proof.
      intros.
      remember (init p) as s0 eqn: H1.
      induction H.

      left.
      subst ivn. subst ivc.
      subst iv.
      subst m.
      subst s.
      unfold init.
      simpl. split; reflexivity.

      depremise IHstep_star. assumption.
      pose (n' := label_node l).
      destruct (eq_nat_dec n n') eqn: N.
      subst n'.
      
      (* The same node *)
      assert (E := H0).
      inversion H0.
      
      (* put *)
        destruct (eq_nat_dec k k0) eqn: K.

          clear IHstep_star.
          right.
          exists l.
          left.
          split.
            (* --- *)
            subst l.
            apply in_or_app.
            right.
            unfold In.
            left. reflexivity.
            (* --- *)
            split.
            subst l.
            unfold label_is_put. apply I.
            rewrite <- H4.
            simpl.
            assert (L := put_change s2 s3 l). 
            simpl in L. depremise L.
            split. assumption. rewrite <- H4. simpl. apply I.
            rewrite <- H4 in L.
            simpl in L.
            open_conjs.
            subst ivn. subst ivc. subst iv. subst m. subst k. subst n.  subst l.
            simpl. split_all.
            symmetry; assumption.
            symmetry; assumption.
            reflexivity.

          clear H2 H5.
          assert (L := put_nochange s2 s3 l).
          simpl in L. depremise L. split. assumption. subst l. simpl. apply I.
          rewrite <- H4 in L. simpl in L.
          specialize (L k). depremise L. apply not_eq_sym. assumption.
          simpl in IHstep_star. rewrite e in IHstep_star. rewrite <- H4 in IHstep_star. simpl in IHstep_star.
          rewrite L in *; clear L.
          destruct IHstep_star. 
          (* --- *)
            left.
            subst ivn.
            subst ivc.
            subst iv.
            subst m.
            subst n.
            subst l.
            simpl.
            assumption.
            right.
            destruct H2 as [l' H2].
            destruct H2; open_conjs; exists l'.
            left.
            split_all.
            apply in_or_app. left. assumption.
            assumption.
            subst ivn. subst iv. subst m. subst n. subst l. simpl. assumption.
            subst ivc. subst iv. subst m. subst n. subst l. simpl. assumption.
            rewrite e. rewrite <- H4. simpl. assumption.
            right.
            split_all.
            apply in_or_app. left. assumption.
            assumption.
            subst ivn. subst iv. subst m. subst n. subst l. simpl. assumption.
            subst ivc. subst iv. subst m. subst n. subst l. simpl. assumption.
            rewrite e. rewrite <- H4. simpl. assumption.

      (* get *)
        assert (L := get_nochange s2 s3 l n).
        simpl in L. depremise L.
        split. assumption. subst l. unfold label_is_get. apply I.
        rewrite L in *.
        destruct IHstep_star.
        (* --- *)
          left. subst ivn. subst ivc. subst iv. subst m. assumption.
        (* --- *)
          right.
          destruct H6 as [l' H6].
          exists l'.
          destruct H6; open_conjs.
          left. 
            split. apply in_or_app. left. assumption.
            split. assumption. subst ivn. subst  ivc. subst iv. subst m. split_all; assumption.
          right.
            split. apply in_or_app. left. assumption.
            split. assumption. subst ivn. subst  ivc. subst iv. subst m. 
            split_all; assumption.

      (* update *)
        clear N.
        rewrite <- H5 in e. simpl in e.
        destruct (eq_nat_dec k k0) eqn: K.

          clear IHstep_star.
          right.
          exists l.
          right.
          split.
            (* --- *)
            subst l.
            apply in_or_app.
            right.
            unfold In.
            left. reflexivity.
            (* --- *)
            split.
            subst l.
            unfold label_is_update. apply I.
            rewrite <- H5.
            simpl.
            assert (L := update_change s2 s3 l). 
            simpl in L. depremise L.
            split. assumption. rewrite <- H5. simpl. apply I.
            rewrite <- H5 in L.
            simpl in L.
            open_conjs.
            subst ivn. subst ivc. subst iv. subst m. subst k. subst n.  subst l.
            simpl. split_all; try reflexivity; symmetry; assumption.

          clear H2 H3 H6.
          assert (L := update_nochange s2 s3 l).
          simpl in L. depremise L. split. assumption. subst l. simpl. apply I.
          rewrite <- H5 in L. simpl in L.
          specialize (L k). depremise L. apply not_eq_sym. assumption.
          simpl in IHstep_star. rewrite e in IHstep_star. (* rewrite <- H4 in IHstep_star. *) simpl in IHstep_star.
          rewrite L in *; clear L.
          destruct IHstep_star. 
          (* --- *)
            left.
            subst ivn.
            subst ivc.
            subst iv.
            subst m.
            subst n.
            subst l.
            simpl.
            assumption.
            right.
            destruct H2 as [l' H2].
            destruct H2; open_conjs; exists l'.
            left.
            split_all.
            apply in_or_app. left. assumption.
            assumption.
            subst ivn. subst iv. subst m. subst n. subst l. simpl. assumption.
            subst ivc. subst iv. subst m. subst n. subst l. simpl. assumption.
            rewrite e. assumption.

            right.
            split_all.
            apply in_or_app. left. assumption.
            assumption.
            subst ivn. subst iv. subst m. subst n. subst l. simpl. assumption.
            subst ivc. subst iv. subst m. subst n. subst l. simpl. assumption.
            rewrite e. assumption.

      (* fault *)
        subst ivn.
        subst ivc.
        subst iv.
        subst m.
        subv s3.
        simpl in IHstep_star.
        subv_in s2 IHstep_star.
        destruct (eq_nat_dec n n0).
        subst n0.
        simpl_override.
        simpl_override_in IHstep_star.
        destruct IHstep_star.
        (* --- *)
          left. assumption.
        (* --- *)
          right.
          destruct H6 as [l' H6].
          exists l'.
          destruct H6; open_conjs.
          left. 
            split. apply in_or_app. left. assumption.
            split. assumption. split_all; assumption.
          right.
            split. apply in_or_app. left. assumption.
            split. assumption.
            split_all; assumption.
        simpl_override.
        simpl_override_in IHstep_star.
        destruct IHstep_star.
        (* --- *)
          left. assumption.
        (* --- *)
          right.
          destruct H6 as [l' H6].
          exists l'.
          destruct H6; open_conjs.
          left. 
            split. apply in_or_app. left. assumption.
            split. assumption. split_all; assumption.
          right.
            split. apply in_or_app. left. assumption.
            split. assumption.
            split_all; assumption.


      (* A different node *)     
      assert (L := node_nochange s2 s3 l n). 
      simpl in L; depremise L. split. assumption. subst n'. apply not_eq_sym. assumption.
      rewrite L in *. clear L.
      destruct IHstep_star.
      left. subst ivn. subst ivc. subst iv. subst m. assumption.
      right. destruct H2 as [l' H2]. exists l'.
      destruct H2; open_conjs.
      left. split_all.
      apply in_or_app. left. assumption.
      assumption.
      subst ivn. subst iv. subst m. assumption.
      subst ivc. subst iv. subst m. assumption.
      assumption.
      right. split_all.
      apply in_or_app. left. assumption.
      assumption.
      subst ivn. subst iv. subst m. assumption.
      subst ivc. subst iv. subst m. assumption.
      assumption.

    Qed.


  Lemma update_sender_eq_msg_sender:
    forall p h s m,
      step_star (init p) h s
      /\ In m (messages s)
      -> sender_node (msg_update m) = msg_sender m.

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
      reflexivity.

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
      assumption.
      assumption.

    Qed.

  Lemma update_no_self_message:
    forall p h s m,
      step_star (init p) h s
      /\ In m (messages s)
      -> not (sender_node (msg_update m) = msg_receiver m).
    
    Proof.
      intros.
      destruct H as [H1 H2].
      assert (A1 := update_sender_eq_msg_sender p h s m). 
        depremise A1. split; assumption.
      assert (A2 := no_self_message p h s m).
        depremise A2. split; assumption.
      rewrite <- A1 in A2.
      assumption.

    Qed.

  Lemma sem_clock_alg_state_clock:
    forall p h s,
      step_star (init p) h s
      -> forall n,
           let sc := clock_state (node_states s n) in
           let ac := clock (alg_state (node_states s n)) n in
           sc = ac.           
    
    Proof.
      intros.
      remember (init p) as s0 eqn: Hi.
      induction H.

      subst sc.
      subst ac.
      subst s.
      simpl.
      reflexivity.

      
      depremise IHstep_star.
      assumption.
      simpl in IHstep_star.
      subst sc.
      subst ac.
      inversion H0.
      
      simpl.
      destruct (eq_nat_dec n n0).
        subst n.
        simpl_override.
        simpl.
        simpl_override.
        rewrite <- H2 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        simpl in IHstep_star.
        rewrite IHstep_star.      
        reflexivity.

        simpl_override.
        rewrite <- H2 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.        
        assumption.


      simpl.
      destruct (eq_nat_dec n n0).
        subst n.
        simpl_override.
        simpl.
        rewrite <- H2 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        simpl in IHstep_star.
        assumption.

        simpl_override.
        rewrite <- H2 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        assumption.

      simpl.
      destruct (eq_nat_dec n n0).
        subst n.
        simpl_override.
        simpl.
        rewrite <- H3 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        simpl in IHstep_star.

        assert (L := update_no_self_message p ls s2 (message n' c' k v u n0 lp)). 
          depremise L.
          split_all.
          subst s1.
          assumption.
          rewrite <- H3.
          simpl.
          apply in_app_iff.
          right.
          apply in_eq.
        simpl in L.
        simpl_override.
        assumption.

        simpl_override.        
        rewrite <- H3 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        assumption.      

      simpl.
      destruct (eq_nat_dec n n0).
        subst n.
        simpl_override.
        simpl.
        rewrite <- H2 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        simpl in IHstep_star.
        assumption.

        simpl_override.
        rewrite <- H2 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        assumption.

    Qed.

  Lemma update_clock_eq_msg_clock:
    forall p h s m,
      step_star (init p) h s
      /\ In m (messages s)
      -> sender_clock (msg_update m) (sender_node (msg_update m))= msg_clock m.

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
      simpl_override.
      assert (A := sem_clock_alg_state_clock).
      specex_deprem A. subst s1. eassumption.
      specialize (A n). simpl in A. subv_in s2 A. simpl_override_in A.
      rewrite A.
      reflexivity.

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
      assumption.
      assumption.

    Qed.

  Lemma msg_update_label:
    forall p h s m,
      step_star (init p) h s
      /\ In m (messages s)
      -> (let lp := msg_label m in
          let u := msg_update m in
          label_is_put lp
          /\ sender_node u = label_node lp
          /\ sender_clock u = clock (label_post_state lp)
          /\ sender_clock u (sender_node u) = label_clock lp).

    Proof.
      intros.
      remember (init p) as s0 eqn: Hs.
      open_conjs.
      induction H.

      subst s.
      simpl in H0.
      contradiction.

      depremise IHstep_star. assumption.
      inversion H1.

      subst l0.
      subst u.
      simpl.
      rewrite <- H5 in H0.
      simpl in H0.
      apply in_app_iff in H0.
      destruct H0.
      depremise IHstep_star.
      rewrite <- H3.
      simpl.
      assumption.
      assumption.
      apply in_map_iff in H0.
      destruct H0 as [n' [N1 N2]].
      rewrite <- N1.
      simpl.
      subst lp.
      rewrite <- N1.
      simpl.
      split.
      reflexivity.
      simpl_override.
      assert (A:= sem_clock_alg_state_clock p ls s2).
        depremise A.
        subst s1. assumption.
        specialize (A n).
        simpl in A.
        rewrite <- H3 in A.
        simpl in A.
        simpl_override_in A.
        simpl in A.
      rewrite A.
      split_all; reflexivity.

      subst u.
      rewrite <- H5 in H0.
      simpl in H0.
      depremise IHstep_star.
      rewrite <- H3.
      simpl.
      assumption.
      assumption.

      subst u.
      rewrite <- H6 in H0.
      simpl in H0.
      apply in_app_iff in H0.
      destruct H0 as [H0 | H0].
      depremise IHstep_star.
      rewrite <- H4.
      simpl.
      apply in_app_iff.
      left.
      assumption.
      assumption.
      depremise IHstep_star.
      rewrite <- H4.
      simpl.
      apply in_app_iff.
      right.
      apply in_cons.
      assumption.
      assumption.

      subst u.
      rewrite <- H5 in H0.
      simpl in H0.
      depremise IHstep_star.
      rewrite <- H3.
      simpl.
      assumption.
      assumption.

    Qed.


  Lemma label_clock_label_post_state_clock:
    forall p h (s: State) (l: Label) (s': State),
      (step_star (init p) h s
       /\ step s l s'
       /\ label_is_put l)
      -> (let n := label_node l in
          let lc := label_clock l in
          let ls := (label_post_state l) in
          let sc := clock ls n in
          lc = sc).
    
    Proof.
      intros.
      destruct H as [H1 [H2 H3]].

      assert (L := sem_clock_alg_state_clock p h s H1 n).
      simpl in L.
      inversion H2.

      subst lc. rewrite <- H4.
      simpl.
      subst sc.
      subst n.
      subst ls.
      rewrite <- H4.
      simpl.
      simpl_override.
      
      rewrite <- H4 in L.
      simpl in L.
      rewrite <- H0 in L.
      simpl in L.
      simpl_override_in L.      
      simpl in L.      
      rewrite <- L.
      reflexivity.

      rewrite <- H4 in H3. simpl in H3. contradiction.
      rewrite <- H5 in H3. simpl in H3. contradiction.
      rewrite <- H4 in H3. simpl in H3. contradiction.
    Qed.


  Lemma label_clock_alg_state_clock:
    forall p h s l s',
      (step_star (init p) h s
       /\ step s l s'
       /\ label_is_put l)
      -> (let n := label_node l in
          let lc := label_clock l in
          let ac := clock (alg_state (node_states s' n)) n in
          lc = ac).

    Proof.
      intros.
      destruct H as [H1 [H2 H3]].

      assert (L := sem_clock_alg_state_clock p h s H1 n).
      inversion H2.

      subst lc. rewrite <- H4.
      simpl.
      subst ac.
      simpl in L.
      rewrite <- H0 in L.
      simpl in L.
      subst n.
      rewrite <- H4 in L.
      rewrite <- H4.
      simpl in *.
      simpl_override_in L.
      rewrite <- H5.
      simpl.
      simpl in L.      
      simpl_override.
      subst s'0.
      simpl in *.
      simpl_override.
      rewrite L.
      reflexivity.

      rewrite <- H4 in H3. simpl in H3. contradiction.
      rewrite <- H5 in H3. simpl in H3. contradiction.
      rewrite <- H4 in H3. simpl in H3. contradiction.      
    Qed.


  Lemma label_clock_leq_alg_state_clock:
    forall p h1 s l s' h2 s'',
      (step_star (init p) h1 s
       /\ step s l s'
       /\ label_is_put l
       /\ step_star s' h2 s'')
      -> (let n := label_node l in
          let lc := label_clock l in
          let c'' := clock (alg_state (node_states s'' n)) n in
          lc <= c'').

    Proof.
      intros.
      open_conjs.

      assert (L := label_clock_alg_state_clock p h1 s l s').
      depremise L.
      split_all.
      assumption.
      assumption.
      assumption.

      
      assert (M := step_star_clock_nondec h2 s' s'' n).
      simpl in M.
      depremise M.
      assumption.
      
      subst lc.
      subst c''.
      simpl in L.
      simpl in M.

      subst n.
      rewrite L.
      apply M.      
    Qed.
    

  Lemma update_clock:
    forall s s' l,
    (step s l s'
     /\ label_is_update l)
    -> let n' := label_orig_node l in
       let c' := label_clock l in
       let n := label_node l in
       let ls := label_post_state l in
       let co := clock ls in
       let ms := messages s in
       exists m,
         let mn' := msg_sender m in
         let mc' := msg_clock m in
         let mn := msg_receiver m in
         let u := msg_update m in
         let mco := sender_clock u in
         In m ms
         /\ n' = mn'
         /\ c' = mc'
         /\ n = mn
         /\ forall n'', In n'' nids -> mco n'' <= co n''.

    Proof.
      intros.
      open_conjs.
      inversion H.

      rewrite <- H3 in H0. unfold label_is_update in H0. contradiction.
      rewrite <- H3 in H0. unfold label_is_update in H0. contradiction.

      exists (message n'0 c'0 k v u n0 lp).
      simpl.
      split_all.

      subst ms.
      subst s.
      simpl.
      apply in_app_iff.
      right.
      apply in_eq.

      subst n'.
      rewrite <- H4. 
      simpl.
      reflexivity.

      subst c'.
      rewrite <- H4. 
      simpl.
      reflexivity.

      subst n.
      rewrite <- H4. 
      simpl.
      reflexivity.

      unfold guard_method in H2.
      bool_to_prop_in H2.
      destruct H2 as [N1 N2].
      intros.
      subst co.
      subst ls.
      rewrite <- H4.
      simpl in *.
      unfold override.
      destruct (eq_nat_dec n'' (sender_node u)).
      subst n''.
      apply Le.le_refl.

      assert (A:= fold_left_and NId nids n''
             (fun n => ((n =? sender_node u) || (sender_clock u n <=? clock s0 n)))).
      depremise A. split; assumption.
      simpl in A.
      bool_to_prop_in A.
      destruct A as [A | A].
      bool_to_prop_in A.
      contradiction.
      bool_to_prop_in A.
      assumption.

      rewrite <- H3 in H0. unfold label_is_update in H0. contradiction.

    Qed.

  Lemma message_pre_put:
    forall p h s m,
      let ms := messages s in
      (step_star (init p) h s
       /\ In m ms)
      -> let mn := msg_sender m in
         let mc := msg_clock m in
         let u := msg_update m in
         let mco := sender_clock u in
         exists l,
           let n := label_node l in
           let c := label_clock l in
           let ls := label_post_state l in
           let co := clock ls in
           In l h
           /\ label_is_put l
           /\ mn = n
           /\ mc = c
           /\ mco = co.

    Proof.
      intros.
      open_conjs.
      remember (init p) as p0 eqn: Hp.
      induction H.

      subst ms. subst s.
      unfold init in H0.
      simpl in H0.
      contradiction.

      simpl in IHstep_star. depremise IHstep_star. assumption.
      inversion H1.

      (* put *)
        subst ms. rewrite <- H5 in H0.
        simpl in H0.
        apply in_app_iff in H0.
        destruct H0.
          
          (* IH *)
            depremise IHstep_star.
            rewrite <- H3.
            simpl.
            assumption.
            destruct IHstep_star as [l' [L1 [L2 [L3 [L4 L5]]]]].
            
            exists l'.
            simpl.
            split_all.
            apply in_app_iff.
            left.
            assumption.
            assumption.
            assumption.
            assumption.
            assumption.

          (* This step *)
            apply in_map_iff in H0.
            destruct H0 as [n' H0].
            open_conjs.

            exists l.
            simpl.
            split_all.
            apply in_app_iff.
            right.
            subst l.
            apply in_eq.

            subst l.
            unfold label_is_put.
            apply I.

            subst mn.
            rewrite <- H4.
            rewrite <- H0.
            simpl.
            reflexivity.

            subst mc.
            rewrite <- H4.
            rewrite <- H0.
            simpl.
            reflexivity.

            subst mco.
            rewrite <- H4.
            simpl.
            apply functional_extensionality.
            intro n''.

            unfold override.
            destruct (eq_nat_dec n'' n).
            subst n''.
            subst u.
            rewrite <- H0.            
            simpl.
            simpl_override.
            reflexivity.
            subst u. rewrite <- H0. simpl.
            simpl_override.
            reflexivity.

      (* get *)
        depremise IHstep_star.
        rewrite <- H3.
        simpl.
        subst ms.
        rewrite <- H5 in H0.
        simpl in H0.
        assumption.
        destruct IHstep_star as [l' [L1 [L2 [L3 [L4 L5]]]]].

        exists l'.
        simpl; split_all.
        apply in_app_iff.
        left. assumption.
        assumption.
        assumption.
        assumption.
        assumption.

      (* update *)
        depremise IHstep_star.
        rewrite <- H4.
        simpl.
        subst ms.
        rewrite <- H6 in H0.
        simpl in H0.
        apply in_app_iff in H0.
        destruct H0.
        apply in_app_iff.
        left. assumption.
        apply in_app_iff.
        right.
        apply in_cons.
        assumption.
        destruct IHstep_star as [l' [L1 [L2 [L3 [L4 L5]]]]].

        exists l'.
        simpl; split_all.
        apply in_app_iff.
        left. assumption.
        assumption.
        assumption.
        assumption.
        assumption.

      (* get *)
        depremise IHstep_star.
        subv s2.
        subv_in ms H0.
        subv_in s3 H0.
        assumption.
        destruct IHstep_star as [l' [L1 [L2 [L3 [L4 L5]]]]].
        exists l'.
        simpl; split_all.
        apply in_app_iff.
        left. assumption.
        assumption.
        assumption.
        assumption.
        assumption.

    Qed.


  Lemma reads_from_clock:
    forall (p: ICExec.Syntax.PProg)(h: list Label)(s: State)(l l': Label)(n: NId),
      (step_star (init p) h s
       /\ prec h l l'
       /\ label_is_put l /\ label_is_get l'
       /\ label_node l = label_orig_node l'
       /\ label_clock l = label_clock l'
       /\ In n nids)
      -> (let c := clock (label_post_state l) n in
          let c' := clock (label_post_state l') n in
          c <= c').

      Proof.
        intros p h s l l' ni.
        intros.
        destruct H as [H [H0 [H2 [H3 [H4 [H5 Hi]]]]]].
        apply prec_in in H0.
        destruct H0 as [H0 H1].

        assert (L := in_exec h (init p) s l' (conj H H1)).
        destruct L as [h1 [s1 [s2 [h2 L]]]].
        open_conjs.

        assert (L := get_from_map s1 s2 l' (conj H3 H8)). (* simpl in L. *)

        pose (k := label_key l').
        pose (n := label_node l').
        assert (M := in_map_from_put_update p h1 s1 k n H7).
        destruct M as [M | M].
          (* Reads the initial value. *)
            simpl in L.
            subst k. remember (label_key l') as k eqn: Hk .
            subst n. remember (label_node l') as n eqn: Hn .
            open_conjs.
            clear H12 H10.
            rewrite H11 in H13.
            clear H11.
            rewrite <- H5 in H13.
            assert (L := put_clock_gtz p h s l). 
            depremise L.
            split_all; assumption.
            rewrite H13 in L. inversion L.

          (* --- *)
          destruct M as [lw [M | M]]; open_conjs.
          
          (* There is a put. *)
          simpl in L.
          open_conjs.
          subst k. remember (label_key l') as k eqn: Hk.
          subst n. remember (label_node l') as n eqn: Hn.
          remember (alg_state (node_states s1 n)) as as1 eqn: A.
          rewrite <- H12 in *. clear H12.
          rewrite <- H13 in *. clear H13.
          rewrite <- H4 in *. (* clear H4. *)
          rewrite <- H5 in *. (* clear H5. *)
          assert (L := put_unique p h s l lw).
          depremise L.
          split_all. assumption. assumption.
          rewrite H6. apply in_app_iff. left. assumption.
          assumption. assumption. assumption. 
          assumption.
          subst lw.
          clear H11 H15 H16.
          subst c. subst c'.
          apply in_split in H10.
          destruct H10 as [h11 [h12 H10]].
          rewrite H10 in H7.
          apply step_star_app in H7.
          destruct H7 as [s0 [H71 H72]].
          apply step_star_end in H72.
          destruct H72 as [s0' [H72 H73]].

          assert (N1 := label_poststate_state s0 s0' l H72).
          assert (N2 := label_poststate_state s1 s2 l' H8).
          rewrite N1; clear N1.
          rewrite N2; clear N2.

          rewrite H14 in *; rewrite <- Hn in *.

          assert (L := step_star_clock_nondec (h12 ++ [l']) s0' s2 n).
          simpl in L.
          depremise L.
          apply step_star_app_one.
          exists s1. split; assumption.
          specialize (L ni).
          assumption.

          (* There is an update. *)
          simpl in L.
          open_conjs.
          subst k. remember (label_key l') as k eqn: Hk.
          subst n. remember (label_node l') as n eqn: Hn.
          remember (alg_state (node_states s1 n)) as as1 eqn: A.
          rewrite <- H12 in *. clear H12.
          rewrite <- H13 in *. clear H13.

          assert (L := in_exec h1 (init p) s1 lw (conj H7 H10)).
          destruct L as [h2' [s2' [s3' [h3' [L1 [L2 [L3 L4]]]]]]].

          assert (M := update_clock s2' s3' lw (conj L3 H11)).
          simpl in M.
          destruct M as [m [M1 [M2 [M3 [M4 M5]]]]].

          assert (N := message_pre_put p h2' s2' m). 
          simpl in N. depremise N. split; assumption.
          destruct N as [lp [N1 [N2 [N3 [N4 N5]]]]].
          
          assert (P := put_unique p h s l lp).
          depremise P.
          split_all.
          assumption.
          assumption.
          rewrite H6. apply in_app_iff. left. rewrite L1. apply in_app_iff. left. assumption.
          assumption.          
          assumption.
          rewrite H4. rewrite H15. rewrite M2. rewrite N3. reflexivity.
          rewrite H5. rewrite H16. rewrite M3. rewrite N4. reflexivity.
          rewrite <- P in *.
          subst c. subst c'.
          rewrite <- N5.
          specialize (M5 ni). depremise M5. assumption.
          assert (E: clock (label_post_state lw) ni <= clock (label_post_state l') ni).
          assert (R := label_poststate_state s2' s3' lw L3); rewrite R; clear R.
          assert (R := label_poststate_state s1 s2 l' H8); rewrite R; clear R.
          rewrite H14. rewrite <- Hn.
          apply step_star_clock_nondec with (h := (h3' ++ [l'])).
          apply step_star_app_one. exists s1. split; assumption.

          eapply Le.le_trans;  eassumption.

    Qed.



  
  Lemma cause_step_clock:
    forall (p: ICExec.Syntax.PProg)(h: list Label)(s: State)(l l': Label)(n: NId),
      (step_star (init p) h s
      /\ cause_step h l l'
      /\ In n nids)
      -> (let c := clock (label_post_state l) n in
          let c' := clock (label_post_state l') n in
          c <= c'
          /\ ((label_node l' = n /\ label_is_put l') -> c < c')).

    Proof.
      intros.
      destruct H as [H' [H1 H2]].
      inversion H1; clear H1.

      (* Case: Process order *)
        open_conjs.
        apply proc_order_clock with (p := p)(h := h)(s := s).
        split_all; assumption.

      (* Case: Reads from *)
        open_conjs.
        split.
          (* -- *)
          apply reads_from_clock with (p := p)(h := h)(s := s).        
          split_all; assumption.
          (* -- *)
          intros.
          open_conjs.
          destruct l';
          simpl in *; contradiction.
    Qed.


  Lemma cause_clock:
    forall (p: ICExec.Syntax.PProg)(h: list Label)(s: State)(l l': Label)(n: NId),
      (step_star (init p) h s
      /\ cause h l l'
      /\ In n nids)
      -> (let c := clock (label_post_state l) n in
          let c' := clock (label_post_state l') n in
          c <= c'
          /\ ((label_node l' = n /\ label_is_put l') -> c < c')).

  Proof.
    intros.
    destruct H as [H' [H1 H2]].
    induction H1.
    apply cause_step_clock with (p := p)(h := h)(s := s).
    split_all; assumption.

    rename c' into c''.
    pose (c' := clock (label_post_state l') n).
    assert (c <= c').
    apply IHcause.
    assumption.
    split.
      (* -- *)
      assert (c' <= c'').
      apply cause_step_clock with (p := p)(h := h)(s := s).
      split_all; assumption. 
      eapply Le.le_trans; eassumption.
      (* -- *)
      intros.
      assert (c' < c'').
      apply cause_step_clock with (p := p)(h := h)(s := s).
      split_all; assumption. 
      assumption.
      eapply Lt.le_lt_trans; eassumption.     
  Qed.

  (* Obligations *)

  Lemma ExecToSeqExec':
    forall p h s,
      CExec.StepStar.step_star (CExec.init p) h s
      -> exists h' s',
           SExec.StepStar.step_star (SExec.init) h' s'
           /\ h' = CExec.eff_hist h
           /\ forall n k, store (CExec.alg_state (CExec.node_states s n)) k = s' n k.

    Proof.
      intros.
      remember (CExec.init p) as s0.
      induction H.
      
      exists nil.
      eexists.
      split_all.
      constructor.
      reflexivity.
      intros.
      subst s.
      reflexivity.

      depremise IHstep_star. assumption.
      destruct IHstep_star as [h' [s' [N1 [N2 N3]]]].
      exists (h' ++ [CExec.eff l]).
      inversion H0.

      (* put *)
      exists (override s' n (override (s' n) k v)).
      split_all.

      apply SExec.StepStar.step_star_app_one.
      eexists.
      split_all.
      eassumption.
      simpl.
      unfold SExec.StepStarArgs.step.
      assert (A: s' = override s' n (s' n)).
        apply functional_extensionality. intro n'.
        destruct (eq_nat_dec n n'). 
        subst n'. simpl_override. reflexivity.
        simpl_override. reflexivity.
      rewrite A at 1.
      apply SExec.put_step.

      simpl.
      subv h'.
      rewrite exec_eff_app.
      f_equal.

      intros.
      simpl.
      destruct (eq_nat_dec n n0).
        subst n0.
        simpl_override.
        simpl_override.

        destruct (eq_nat_dec k k0).
        subst k0.
        simpl_override.
        simpl_override.
        reflexivity.

        simpl_override.
        simpl_override.
        specialize (N3 n k0).
        subv_in s2 N3.
        simpl_override_in N3.
        assumption.
        
      simpl_override.
      simpl_override.
      specialize (N3 n0 k0).
      subv_in s2 N3.
      simpl_override_in N3.
      assumption.

      (* get *)
      exists (override s' n (s' n)).
      split_all.

      apply SExec.StepStar.step_star_app_one.
      eexists.
      split_all.
      eassumption.
      simpl.
      unfold SExec.StepStarArgs.step.
      assert (A: s' = override s' n (s' n)).
        apply functional_extensionality. intro n'.
        destruct (eq_nat_dec n n'). 
        subst n'. simpl_override. reflexivity.
        simpl_override. reflexivity.
      rewrite A at 1.
      subv v'.      
      specialize (N3 n k).
        subv_in s2 N3.
        simpl_override_in N3.
      rewrite N3.
      apply SExec.get_step.

      simpl.
      subv h'.
      rewrite exec_eff_app.
      f_equal.

      intros.
      simpl.
      destruct (eq_nat_dec n n0).
        subst n0.
        simpl_override.
        simpl_override.
        specialize (N3 n k0).
        subv_in s2 N3.
        simpl_override_in N3.
        assumption.
        
        simpl_override.
        simpl_override.
        specialize (N3 n0 k0).
        subv_in s2 N3.
        simpl_override_in N3.
        assumption.

      (* update *)
      simpl.
      exists (override s' n (override (s' n) k v)).
      split_all.

      apply SExec.StepStar.step_star_app_one.
      eexists.
      split_all.
      eassumption.
      unfold SExec.StepStarArgs.step.
      assert (A: s' = override s' n (s' n)).
        apply functional_extensionality. intro n'.
        destruct (eq_nat_dec n n'). 
        subst n'. simpl_override. reflexivity.
        simpl_override. reflexivity.
      rewrite A at 1.
      apply SExec.put_step.

      simpl.
      subv h'.
      rewrite exec_eff_app.
      f_equal.

      intros.
      destruct (eq_nat_dec n n0).
        subst n0.
        simpl_override.
        simpl_override.

        destruct (eq_nat_dec k k0).
        subst k0.
        simpl_override.
        simpl_override.
        reflexivity.

        simpl_override.
        simpl_override.
        specialize (N3 n k0).
        subv_in s2 N3.
        simpl_override_in N3.
        assumption.
        
      simpl_override.
      simpl_override.
      specialize (N3 n0 k0).
      subv_in s2 N3.
      simpl_override_in N3.
      assumption.

      (* fault *)
      exists (override s' n (s' n)).
      split_all.

      apply SExec.StepStar.step_star_app_one.
      eexists.
      split_all.
      eassumption.
      simpl.
      unfold SExec.StepStarArgs.step.
      assert (A: s' = override s' n (s' n)).
        apply functional_extensionality. intro n'.
        destruct (eq_nat_dec n n'). 
        subst n'. simpl_override. reflexivity.
        simpl_override. reflexivity.
      rewrite A at 1.
      constructor.

      simpl.
      subv h'.
      rewrite exec_eff_app.
      f_equal.

      intros.
      simpl.
      destruct (eq_nat_dec n n0).
        subst n0.
        simpl_override.
        simpl_override.
        specialize (N3 n k0).
        subv_in s2 N3.
        simpl_override_in N3.
        assumption.
        
        simpl_override.
        simpl_override.
        specialize (N3 n0 k0).
        subv_in s2 N3.
        simpl_override_in N3.
        assumption.


    Qed.

  Lemma ExecToSeqExec:
    forall p h s,
      CExec.StepStar.step_star (CExec.init p) h s
      -> exists h' s',
           SExec.StepStar.step_star (SExec.init) h' s'
           /\ h' = CExec.eff_hist h.

    Proof.
      intros.
      assert (A := ExecToSeqExec').
      specex_deprem A. eassumption.
      destruct A as [h' [s' [A1 [A2 _]]]].
      exists h'. exists s'. split_all; assumption.
    Qed.


  Definition algrec: ICExec.AlgState -> NId -> Clock :=
    clock.
    

  Lemma algrec_init:
    forall p n n',
      algrec (alg_state (node_states (init p) n)) n' = 0.

    Proof.
      intros;
      reflexivity.      
    Qed.


  Lemma algrec_step:
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

    Proof.
      intros.
      destruct H as [H0 H1].
      split_all.

      (* get *)
      intros.
      unfold algrec.
      destruct l; try contradiction.
      simpl in *. clear H. subst n.
      inversion H1.      
      simpl.
      simpl_override.
      simpl_override.
      subst a.
      reflexivity.

      (* put *)
      intros.
      unfold algrec.
      destruct l; try contradiction.
      simpl in *. clear H. subst n.
      inversion H1.
      simpl.
      simpl_override.
      simpl_override.
      split.      
      subst a.
      rewrite Plus.plus_comm.
      simpl.
      f_equal.
      subv n.
      reflexivity.

      intros.
      subst a.
      rewrite <- H4 in *.
      simpl_override.
      reflexivity.

      (* update *)
      intros.
      unfold algrec.
      destruct l; try contradiction.
      simpl in *. clear H. subst n. subst n'. subst c'.
      inversion H1.
      simpl.
      simpl_override.
      simpl_override.
      subst a.
      subst c.

      unfold guard_method in H13.
      bool_to_prop_in H13.
      destruct H13 as [N _].
      bool_to_prop_in N.

      assert (A1 := update_sender_eq_msg_sender).
        specex_deprem A1. split_all.
        eassumption. subv s. apply in_app_iff. right. apply in_eq.
        simpl in A1.

      assert (A2 := update_clock_eq_msg_clock).
        specex_deprem A2. split_all.
        eassumption. subv s. apply in_app_iff. right. apply in_eq.
        simpl in A2.
      rewrite A2 in N.
      rewrite A2.
      rewrite A1 in N.
      rewrite A1.
      rewrite Plus.plus_comm in N.
      simpl in N.
      subst n'.
      clear A1 A2.

      split_all.

      symmetry.
      assumption.

      simpl_override.
      reflexivity.

      intros.
      simpl_override.
      reflexivity.
      
    Qed.


  Lemma cause_rec:
    forall p h s1 l s2 l',
      let n := label_node l in
      let c := label_clock l in
      let n' := label_node l' in
      let lp := msg_label (label_message l') in
      (step_star (init p) h s1
       /\ step s1 l' s2
       /\ label_is_put l
       /\ label_is_update l'
       /\ cause h l lp)
      -> c <= algrec (alg_state (node_states s1 n')) n.

    Proof.
      intros.
      destruct H as [N1 [N2 [N3 [N4 N5]]]].
      unfold algrec.
      destruct l'; try contradiction.
      remember (update_label n0 n1 c0 n2 k v a m a0) as l' eqn: Hu.

      assert (A1: c = clock (label_post_state l) n).
        subv c. subv n.
        apply cause_in in N5. destruct N5 as [N5 _].
        assert (B1 := in_exec). 
          specex_deprem B1. split; eassumption.
          destruct B1 as [h1 [sm1 [sm2 [h2 [B11 [B12 [B13 B14]]]]]]].
        assert (B2 := label_clock_label_post_state_clock).
          specex_deprem B2.
          split_all. apply B12. eassumption. eassumption.
          simpl in B2.
        assumption.

      rewrite A1. clear A1.
            
      assert (A2 := cause_clock).
        specex_deprem A2. split_all.
        eassumption.
        eassumption.
        eapply label_node_in_nids.
        split. eassumption. apply cause_in in N5. destruct N5 as [N5 _]. eassumption.
        simpl in A2.
        subst n. remember (label_node l) as n eqn: Hn.
        destruct A2 as [A21 A22].


      assert (A3: 
                (clock (label_post_state lp) (label_node lp) = clock (alg_state (node_states s1 n')) (label_node lp) + 1)
                /\ (forall n, In n nids /\ (n <> label_node lp)->
                              clock (label_post_state lp) n ≤ clock (alg_state (node_states s1 n')) n)).
        subv_in l' N2.
        inversion N2; simpl in *; try contradiction.
        subst s'0. subst a. subst s'5. subst s'4. subst s'3. subst s'2. subst v0. subst k0. subst n3. subst c0. subst n'0. subst s'1.
        subv n'. subv l'.
        simpl_override.
        subv lp. subv l'. subv m.

        unfold guard_method in H11.
        bool_to_prop_in H11.
        destruct H11 as [U1 U2].

        bool_to_prop_in U1.
        assert (B1 := msg_update_label).
          specex_deprem B1. split_all. eassumption. subv s1. apply in_app_iff. right. apply in_eq. simpl in B1.
          destruct B1 as [B11 [B12 [B13 B14]]].

        split.

        rewrite B13 in U1.
        rewrite B12 in U1.
        assumption.

        intros.
        open_conjs.
        assert (B2 := fold_left_and NId nids n3 (fun n => ((n =? sender_node u) || (sender_clock u n <=? clock s n)))).
          depremise B2. split. 
          rewrite <- U2 at 2.
          f_equal.
          assumption.
        simpl in B2.
        bool_to_prop_in B2.
        destruct B2 as [B2 | B2].

          exfalso.
          bool_to_prop_in B2.
          subst n3.
          contradiction.

        bool_to_prop_in B2.
        rewrite B13 in B2.
        assumption.

      destruct A3 as [A31 A32].

      destruct (eq_nat_dec n (label_node lp)).

        clear A21 A32.
        subv n.
        depremise A22. split. symmetry. assumption. 
          assert (B := msg_update_label).
            subv_in l' N2. inversion N2.
            specex_deprem B. split_all. eassumption.  subv s1. apply in_app_iff. right. apply in_eq. simpl in B.
            destruct B as [B _].
          subv lp. subv l'. subv m.
          assumption.  
        rewrite e in A22.
        rewrite A31 in A22.
        clear A31.
        rewrite Plus.plus_comm in A22.
        simpl in A22.
        apply Lt.lt_n_Sm_le in A22.
        assumption.

        
        clear A22 A31.
        specialize (A32 n).
        depremise A32.
        assert (B := label_node_in_nids).
          specex_deprem B. split.
          eassumption.
          apply cause_in in N5.
          destruct N5 as [N5 _].
          eassumption.
          simpl in B.
        subv n.
        split.
        assumption.
        subst n. assumption.
        eapply Le.le_trans; eassumption.

    Qed.


End KVSAlg1CauseObl.



Module KVSAlg1Parametric <: Parametric KVSAlg1.

  Import SysPredefs.
  Import KVSAlg1.


  Section ParallelWorlds.

    Definition RState (Val1: Type)(Val2: Type)(R: Val1 -> Val2 -> Prop)(s1: @State Val1)(s2: @State Val2): Prop := 
      (forall k, R (store s1 k) (store s2 k))
      /\ clock s1 = clock s2.


    Definition RUpdate (Val1: Type)(Val2: Type)(R: Val1 -> Val2 -> Prop)(u1: @Update Val1)(u2: @Update Val2): Prop := 
      sender_node u1 = sender_node u2 /\
      sender_clock u1 = sender_clock u2.

    Variables Val1 Val2 : Type.
    Variable R : Val1 -> Val2 -> Prop.

    Lemma init_method_R: 
      forall v1 v2, R v1 v2 -> RState _ _ R (init_method _ v1) (init_method _ v2).
      
      Proof.
        intros.
        unfold RState.
        unfold init_method.
        simpl.
        split.
        intros.
        assumption.
        reflexivity.
      Qed.

    Lemma get_method_R:
      forall n s1 s2 k,
        RState _ _ R s1 s2
        -> let (v1', s1') := get_method _ n s1 k in
           let (v2', s2') := get_method _ n s2 k in
           R v1' v2' /\ RState _ _ R s1' s2'.
      
      Proof.
        intros.
        unfold get_method.
        unfold RState in H.
        split.
        open_conjs.
        specialize (H k).
        open_conjs.
        assumption.
        unfold RState.
        intros.
        simpl.
        open_conjs.
        split;
        assumption.
      Qed.

    Lemma put_method_R:
      forall n s1 s2 k v1 v2,
        RState _ _ R s1 s2
        -> R v1 v2
        -> let (s1', u1) := put_method _ n s1 k v1 in
           let (s2', u2) := put_method _ n s2 k v2 in
           RState _ _ R s1' s2' /\ RUpdate _ _ R u1 u2.

      Proof.
        intros.
        unfold put_method.
        split.
        unfold RState.
        intros.
        simpl.
        split.
        intros.
        destruct (eq_nat_dec k k0).
        subst k.
        simpl_override.
        simpl_override.
        assumption.
        simpl_override.
        simpl_override.
        unfold RState in H.
        open_conjs.
        specialize (H k0).
        open_conjs.
        assumption.
        apply functional_extensionality.
        intro n'.
        destruct (eq_nat_dec n n').
        simpl_override.
        simpl_override.
        unfold RState in H.
        open_conjs.
        rewrite H1.
        reflexivity.
        simpl_override.
        simpl_override.        
        unfold RState in H.
        open_conjs.
        rewrite H1.
        reflexivity.
        unfold RUpdate.
        split.
        simpl. reflexivity.
        simpl.
        unfold RState in H.
        open_conjs.
        apply functional_extensionality.        
        intro n'.
        destruct (eq_nat_dec n n').
        simpl_override.
        simpl_override.
        rewrite H1.
        reflexivity.
        simpl_override.
        simpl_override.
        rewrite H1.
        reflexivity.
      Qed.

    Lemma guard_method_R:
      forall n s1 s2 k v1 v2 u1 u2,
        RState _ _ R s1 s2
        -> R v1 v2
        -> RUpdate _ _ R u1 u2
        -> guard_method _ n s1 k v1 u1 = guard_method _ n s2 k v2 u2.
      
      Proof.
        intros.
        unfold guard_method.
        unfold RState in H.
        unfold RUpdate in H1.
        open_conjs.
        rewrite H1.
        rewrite H2.
        rewrite H3.
        reflexivity.
      Qed.

    Lemma update_method_R:
      forall n s1 s2 k v1 v2 u1 u2,
        RState _ _ R s1 s2
        -> R v1 v2
        -> RUpdate _ _ R u1 u2
        -> RState _ _ R (update_method _ n s1 k v1 u1) (update_method _ n s2 k v2 u2).
      
      Proof.
        intros.
        unfold RState.
        unfold update_method.
        simpl.
        unfold RState in H.
        unfold RUpdate in H1.
        open_conjs.
        rewrite H1.
        rewrite H2.
        rewrite H3.
        split.
        intros.
        destruct (eq_nat_dec k k0).
        simpl_override.
        simpl_override.
        assumption.
        simpl_override.
        simpl_override.
        apply H.
        reflexivity.

      Qed.

  End ParallelWorlds.

End KVSAlg1Parametric.


Module KVSAlg1ExecToAbstExec (SyntaxArg: SyntaxPar).
  
  Module ExecToAbstExec := ExecToAbstExec KVSAlg1 KVSAlg1Parametric KVSAlg1CauseObl SyntaxArg.
  Import ExecToAbstExec.

  Lemma CausallyConsistent: 
    forall (p: Syntax.PProg)(h: list N.CExec.Label),
      N.CExec.history (N.CExec.init p) h 
      -> exists (h': list AExec.Label),
           AExec.history (AExec.init p) h'
           /\ N.CExec.ext_hist h = AExec.ext_hist h'.
      
    Proof.
      apply ExecToAbstExec.CausallyConsistent.
    Qed.

End KVSAlg1ExecToAbstExec.


