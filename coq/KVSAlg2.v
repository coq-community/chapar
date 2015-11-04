Require Import Coq.Unicode.Utf8.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.Max. 
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Le.

Add LoadPath "Lib".
Require Import Predefs.
Require Import extralib.


Require Import KVStore.


Module KVSAlg2 <: AlgDef.

  Import SysPredefs.

  Definition Clock := nat.

  Record Entry {Val: Type} := {
    entry_val: Val;
    entry_node: NId;
    entry_clock: Clock
  }.
  Definition entry {Val: Type} := @Build_Entry Val.

  Record StateRec {Val: Type} := {
    store: Key -> @Entry Val;
    received: NId -> Clock;
    clock: Clock;
    dep: list (NId * Clock)
  }.
  Definition state {Val: Type} := @Build_StateRec Val.
  Definition State {Val: Type} := @StateRec Val.

  Record UpdateRec {Val: Type} := {
    sender_node: NId;
    sender_clock: Clock;
    sender_dep: list (NId * Clock)
  }.
  Definition update {Val: Type} := @Build_UpdateRec Val.
  Definition Update {Val: Type} := @UpdateRec Val.

  Definition dummy_update {Val: Type} := @update Val 0 0 nil.

  Section ValParam.
  Variable Val: Type.
  
  Definition init_method (init_val: Val): State :=
    state (fun (k: Key) => (entry init_val init_nid 0))
          (fun (n: NId) => 0)
          0
          nil.

  Definition get_method (n: NId)(this: State)(k: Key): (Val * State) :=
    let s := store this in
    let r := received this in
    let c := clock this in
    let d := dep this in
    let e := s k in
    let v := entry_val e in
    let n' := entry_node e in
    let c' := entry_clock e in
    (* let d' := (n', c') :: d in *)
    let d' := if (n' <>? init_nid) then (n', c') :: d else d in
    (v, (state s r c d')).

  Definition put_method (n: NId)(this: State)(k: Key)(v: Val): (State * Update) :=
    let s := store this in
    let r := received this in
    let c := clock this in
    let d := dep this in
    let c' := c + 1 in
    let s' := override s k (entry v n c') in
    let d' := [(n, c')] in
    let r' := override r n c' in
    ((state s' r' c' d'), (@update Val n c' d)).

  Definition guard_method (n: NId)(this: @State Val)(k: Key)(v: Val)(u: @Update Val): bool :=
    let r := received this in
    let d' := sender_dep u in
    (fold_left (fun b p =>
                 let n' := fst p in
                 let c' := snd p in
                 b && (c' <=? r n'))
               d'
               true).


  Definition update_method (n: NId)(this: State)(k: Key)(v: Val)(u: @Update Val): State :=
    let s := store this in
    let r := received this in
    let c := clock this in
    let d := dep this in
    let n' := sender_node u in
    let c' := sender_clock u in
    let s' := override s k (entry v n' c') in
    let r' := override r n' c' in
    (* let r' := override r n' ((r n') + 1) in *)
    (state s' r' c d).

  End ValParam.

End KVSAlg2.


Module KVSAlg2CauseObl (SyntaxArg: SyntaxPar) <: CauseObl KVSAlg2 SyntaxArg.

  (* Module Type InstExecToAbsExecPar (AlgDef: AlgDef)(SyntaxArg: SyntaxPar). *)

  Export SysPredefs.

  Module CExec := ConcExec SyntaxArg KVSAlg2.
  Import CExec.
  Module SExec := SeqExec SyntaxArg.
  Import SExec.
  Module ICExec := InstConcExec SyntaxArg KVSAlg2.
  Import ICExec.
    
  Definition label_dep (l: Label) :=
    match l with
      | put_label _ n c k v s s' u => dep s
      | get_label _ n c n' k s s' v => dep s'
      | update_label _ n c n' k v s m s' => dep s'
      | fault_label _ n _ s' => dep s'
    end.

  Lemma sem_clock_alg_state_clock:
    forall p h s n,
      step_star (init p) h s
      -> let sc := clock_state (node_states s n) in
         let ac := clock (alg_state (node_states s n)) in
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
        subv_in s2 IHstep_star.
        simpl_override_in IHstep_star.
        assumption.

        simpl_override.
        subv_in s2 IHstep_star.
        simpl_override_in IHstep_star.
        assumption.

    Qed.

  Lemma message_update_node_clock_eq:
    forall p h s m,
      let ms := messages s in
      (step_star (init p) h s
       /\ In m ms)
      -> let mn := msg_sender m in
         let mc := msg_clock m in
         let u := msg_update m in
         let un := sender_node u in
         let uc := sender_clock u in
         mn = un
         /\ mc = uc.

    Proof.
      intros.
      open_conjs.
      remember (init p) as s0 eqn: Hs.      

      induction H.

      subst ms.
      subst s.
      simpl in *.
      contradiction.

      inversion H1.

      (* put *)

        subst ms.
        rewrite <- H5 in H0.
        simpl in H0.
        apply in_app_iff in H0.
        destruct H0.

          simpl in IHstep_star. depremise IHstep_star.
          assumption. depremise IHstep_star.
          rewrite <- H3. simpl. assumption.
          assumption.

          clear IHstep_star.
          apply in_map_iff in H0.
          destruct H0 as [nt [H01 H02]].
          subst mn.
          subst mc.
          subst un.
          subst uc.
          subst u.
          subst m.
          simpl.
          split. reflexivity.
          assert (A := sem_clock_alg_state_clock p ls s2 n).
          depremise A. subst s1. assumption.
          simpl in A.
          rewrite <- H3 in A.
          simpl in A.
          simpl_override_in A.
          simpl in A.
          rewrite A.
          reflexivity.

      (* get *)
        subst ms.
        rewrite <- H5 in H0.
        simpl in H0.

        simpl in IHstep_star. depremise IHstep_star.
        assumption. depremise IHstep_star.
        rewrite <- H3. simpl. assumption.
        assumption.
        
      (* update *)
        subst ms.
        rewrite <- H6 in H0.
        simpl in H0.

        simpl in IHstep_star. depremise IHstep_star.
        assumption. depremise IHstep_star.
        rewrite <- H4. simpl. apply in_app_iff in H0. destruct H0. apply in_app_iff. left. assumption. apply in_app_iff. right. apply in_cons. assumption.
        assumption.

      (* fault *)
        subst ms.
        subv_in s3 H0.

        simpl in IHstep_star. depremise IHstep_star.
        assumption. depremise IHstep_star.
        subv s2. assumption.
        assumption.

    Qed.


  Lemma inst_entry_eq:
    forall p h s n k,
      step_star (init p) h s
      -> let st := store (alg_state (node_states s n)) k in
         entry_node st = inst_val_nid (entry_val st)
         /\ entry_clock st = inst_val_clock (entry_val st).

    Proof.
      intros.
      remember (init p) as s0 eqn: Hs.      

      induction H.

      subst st. subst s.
      simpl. split; reflexivity.

      depremise IHstep_star. assumption.      

      destruct (eq_nat_dec n (label_node l)).

      (* the same node *)
        inversion H0.

        (* put *)
          subst  l0.
          destruct (eq_nat_dec k k0).

          subst st.
          rewrite  <- H4.
          simpl.
          subst n.
          subst l.
          simpl.
          simpl_override.
          simpl.
          simpl_override.
          simpl.
          split.
          reflexivity.
          assert (A := sem_clock_alg_state_clock p ls s2 n0).
          depremise A. subst s1. assumption.
          simpl in A.
          rewrite <- H2 in A.
          simpl in A.
          simpl_override_in A.
          simpl in A.
          rewrite A.
          reflexivity.

          subst st.
          rewrite <- H4.
          simpl.
          subst n.
          subst l.
          simpl.
          simpl_override.
          simpl.
          simpl_override.
          simpl in IHstep_star.
          rewrite <- H2 in IHstep_star.
          simpl in IHstep_star.
          simpl_override_in IHstep_star.
          simpl in IHstep_star.
          assumption.

        (* get *)
          subst st.
          rewrite <- H4.
          simpl.
          subst n.
          subst l.
          simpl.
          simpl_override.
          simpl.
          simpl_override.
          simpl in IHstep_star.
          rewrite <- H2 in IHstep_star.
          simpl in IHstep_star.
          simpl_override_in IHstep_star.
          simpl in IHstep_star.
          assumption.

        (* update *)
          subst st.
          rewrite <- H5.
          simpl.
          subst n.
          rewrite <- H4.
          simpl.
          simpl_override.
          simpl.
          destruct (eq_nat_dec k k0).
          
          simpl_override.
          simpl.
          assert (A := message_update_node_clock_eq p ls s2 (message n' c' k0 v u n0 lp)).
            simpl in A. depremise A. split.
            subst s1. assumption. rewrite <- H3. simpl. apply in_app_iff. right. apply in_eq.
          open_conjs.
          split; symmetry; assumption.


          simpl_override.
          simpl in IHstep_star.
          rewrite <- H3 in IHstep_star.
          rewrite <- H4 in IHstep_star.
          simpl in IHstep_star.
          simpl_override_in IHstep_star.
          simpl in IHstep_star.
          assumption.

        (* fault *)
          subst st.
          rewrite <- H4.
          simpl.
          subst n.
          subst l.
          simpl.
          simpl_override.
          simpl.
          simpl_override.
          simpl in IHstep_star.
          rewrite <- H2 in IHstep_star.
          simpl in IHstep_star.
          simpl_override_in IHstep_star.
          simpl in IHstep_star.
          assumption.
                   
      (* a different node *)

        subst st.
        simpl in IHstep_star.
        assert (A : alg_state (node_states s3 n) = alg_state (node_states s2 n)).
        destruct H0; clear IHstep_star;
        simpl in *;
        simpl_override;
        simpl_override;
        reflexivity.        
        rewrite A.
        assumption.
    Qed.


  Lemma get_from_map:
    forall p h s s' l,
      (step_star (init p) h s
       /\ label_is_get l
       /\ step s l s')
      -> let k := label_key l in
         let n' := label_orig_node l in
         let c' := label_clock l in
         let n := label_node l in
         let m := store (alg_state ((node_states s) n)) in
         let d := dep (label_post_state l) in
         let iv := entry_val (m k) in
         let ivn := inst_val_nid iv in
         let ivc := inst_val_clock iv in
         (n' = ivn 
          /\ c' = ivc
          /\ (n' <> init_nid -> In (n', c') d)).

    Proof.
      intros.
      open_conjs.
      
      inversion H1.

      (* put *)
        simpl in *.
        subst l0.
        rewrite <- H4 in H0.
        unfold label_is_get in H0.
        contradiction.

      (* get *)
        simpl in *.
        subst n'.
        subst c'.
        subst ivn.
        subst ivc.
        rewrite <- H4.
        simpl.
        subst n'0.
        subst c'0.
        subst u.
        subst iv.
        subst m.
        subst d.
        subst s.
        subst s'.
        subst k.
        subst n.
        rewrite <- H4.
        simpl.
        simpl_override.
        simpl.
        split_all. 
        reflexivity.
        reflexivity.
        intros.
        assert (A := inst_entry_eq p h (state (override nss n0 (node_state (get _ k0 p0) s0 c)) ms e) n0 k0).
        simpl in A. depremise A. assumption.
        simpl_override_in A.
        simpl in A.
        destruct A as [A1 A2].
        rewrite A1.
        rewrite A2.
        destruct (inst_val_nid (entry_val (store s0 k0)) <>? init_nid) eqn: Hn.
        apply in_eq.
        bool_to_prop_in Hn.
        contradiction.

      (* update *)
        simpl in *.
        rewrite <- H5 in H0.
        unfold label_is_get in H0.
        contradiction.

      (* fault *)
        simpl in *.
        subv_in l H0.
        contradiction.

    Qed.


  Lemma put_change:
    forall (s s': State)(l: Label),
      let n := label_node l in
      let c := label_clock l in
      let k := label_key l in
      let m' := store (alg_state (node_states s' n)) in
      let iv := entry_val (m' k) in
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

  Lemma update_change:
    forall (s s': State)(l: Label),
      let n' := label_orig_node l in
      let c := label_clock l in
      let n := label_node l in
      let k := label_key l in
      let m' := store (alg_state (node_states s' n)) in
      let iv := entry_val (m' k) in
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
         let ivn := inst_val_nid (entry_val iv) in
         let ivc := inst_val_clock (entry_val iv) in
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
      destruct (eq_nat_dec n n').
      subst n'.
      
      (* The same node *)
      assert (E := H0).
      inversion H0.
      
      (* put *)
        destruct (eq_nat_dec k k0).
          
          (* the same key *)
          clear IHstep_star.
          right.
          subst l0.
          rewrite H4 in *.
          exists l.
          left.
          split_all.
            (* --- *)
            apply in_or_app.
            right.
            apply in_eq.
            (* --- *)
            subst l.
            unfold label_is_put. apply I.
            (* --- *)
            assert (A1 := put_change s2 s3 l).
            simpl in A1.
            depremise A1. 
            split. assumption. subst l. simpl. apply I.
            destruct A1 as [A1 _].
            subst ivn.
            subst iv.
            subst m.
            subst n.
            subst k.
            rewrite <- H4 in A1 at 2.
            simpl in A1.
            symmetry. 
            assumption.
            (* --- *)
            assert (A1 := put_change s2 s3 l).
            simpl in A1.
            depremise A1. 
            split. assumption. subst l. simpl. apply I.
            destruct A1 as [_ A1].
            subst ivc.
            subst iv.
            subst m.
            subst n.
            subst k.
            rewrite <- H4 in A1 at 2.
            simpl in A1.
            symmetry. 
            assumption.
            (* --- *)
            symmetry.
            assumption.

          (* a different key *)
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
              (* --- *)
              right.
              destruct H2 as [l' H2].
              destruct H2; open_conjs; exists l'.
                (* -- *)
                left.
                split_all.
                apply in_or_app. left. assumption.
                assumption.
                subst ivn. subst iv. subst m. subst n. subst l. simpl. assumption.
                subst ivc. subst iv. subst m. subst n. subst l. simpl. assumption.
                rewrite e. rewrite <- H4. simpl. assumption.
                (* -- *)
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
        rewrite L in *; clear L.
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
        rewrite <- H5 in e. simpl in e.
        destruct (eq_nat_dec k k0).

          (* the same key *)
          clear IHstep_star.
          right.
          exists l.
          right.
          split.
            (* --- *)
            subst l.
            apply in_or_app.
            right.
            apply in_eq.
            (* --- *)
            split.
            subst l.
            unfold label_is_update. apply I.
            (* --- *)
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

          (* a different key *)
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
        simpl in IHstep_star.
        subv_in s2 IHstep_star.
        simpl_override_in IHstep_star.
        subst ivn. subst ivc. subst iv. subst m. subv s3.
        destruct IHstep_star.
          (* --- *)
          left. 
          destruct (eq_nat_dec n0 n). 
          rewrite e1 in *. simpl_override. simpl_override_in H6. assumption.
          simpl_override. simpl_override_in H6. assumption.
          (* --- *)
          right.
          destruct H6 as [l' H6].
          exists l'.
          destruct H6; open_conjs.
          left. 
            split. apply in_or_app. left. assumption.
            split. assumption. destruct (eq_nat_dec n0 n). 
            rewrite e1 in *. simpl_override. simpl_override_in H8. simpl_override_in H9. split_all; assumption.
            simpl_override. simpl_override_in H8. simpl_override_in H9. split_all; assumption.            
          right.
            split. apply in_or_app. left. assumption.
            split. assumption.
            destruct (eq_nat_dec n0 n). 
            rewrite e1 in *. simpl_override. simpl_override_in H8. simpl_override_in H9. split_all; assumption.
            simpl_override. simpl_override_in H8. simpl_override_in H9. split_all; assumption.

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


  Lemma update_dep:
    forall s s' l,
      (step s l s'
       /\ label_is_update l)
      -> let n' := label_orig_node l in
         let c' := label_clock l in
         let k := label_key l in
         let n := label_node l in
         let ls := label_pre_state l in
         let r := received ls in
         let ms := messages s in
         exists m,
           let mn' := msg_sender m in
           let mc' := msg_clock m in
           let mn := msg_receiver m in
           let u := msg_update m in
           let sd := sender_dep u in
           In m ms
           /\ n' = mn'
           /\ c' = mc'
           /\ n = mn
           /\ forall p, In p sd -> 
                        let n'' := fst p in 
                        let c'' := snd p in
                        c'' <= r n''.

    Proof.
      intros.
      open_conjs.
      inversion H.

      rewrite <- H3 in H0. unfold label_is_update in H0. contradiction.
      rewrite <- H3 in H0. unfold label_is_update in H0. contradiction.

      exists (message n'0 c'0 k0 v u n0 lp).
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

      intros.
      unfold guard_method in H2.
      assert (A:= fold_left_and (NId*Clock) (sender_dep u) p0
             (fun p => snd p <=? received s0 (fst p))).
        depremise A. split; assumption.
      simpl in A.
      bool_to_prop_in A.
      subst r.
      subst ls.
      subst l.
      simpl.
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
         let md := sender_dep u in
         exists l,
           let n := label_node l in
           let c := label_clock l in
           let ls := label_pre_state l in
           let d := dep ls in
           In l h
           /\ label_is_put l
           /\ mn = n
           /\ mc = c
           /\ md = d.

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
            subst l0.
            unfold label_is_put.
            apply I.

            subst mn.
            subst l.
            subst l0.
            rewrite <- H0.
            simpl.
            reflexivity.

            subst mc.
            subst l.
            subst l0.
            rewrite <- H0.
            simpl.
            reflexivity.

            subst md.
            subst l.
            subst l0.
            simpl.
            subst u.
            rewrite <- H0.
            simpl.
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

      (* fault *)
        depremise IHstep_star.
        subv s2.
        subst ms.
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

    Lemma reads_from_cause:
      forall p h s1 l s2,
        let n' := label_orig_node l in
        let c' := label_clock l in
        let k := label_key l in
        let n := label_node l in
        (step_star (init p) h s1
         /\ step s1 l s2
         /\ label_is_get l
         /\ n' <> init_nid)
        -> exists l',
             label_is_put l'
             /\ label_node l' = n'
             /\ label_clock l' = c'
             /\ cause (h ++ [l]) l' l.

    Proof.
      intros.
      destruct H as [N1 [N2 [N3 N4]]].

      assert (L := get_from_map p h s1 s2 l).
        depremise L. split_all; assumption.

      assert (M := in_map_from_put_update p h s1 k n).
        depremise M. assumption.

      destruct M as [M | M].

        (* Reads the initial value. *)
          simpl in L.
          subst k. remember (label_key l) as k eqn: Hk .
          subst n. remember (label_node l) as n eqn: Hn .
          destruct L as [L1 [L2 L3]].
          destruct M as [M1 M2].
          clear L2 L3 M2.
          rewrite M1 in L1.
          subst n'.
          contradiction.

          (* --- *)
          destruct M as [lw [M | M]].
          
        (* There is a put. *)
          destruct M as [M1 [M2 [M3 [M4 M5]]]].
          simpl in L.          
          destruct L as [L1 [L2 _]].
          subst k. remember (label_key l) as k eqn: Hk.
          subst n. remember (label_node l) as n eqn: Hn.
          remember (alg_state (node_states s1 n)) as as1 eqn: Ha.

          exists lw. split_all.
          assumption.
          rewrite M3. rewrite <- L1. subst n'. reflexivity.
          rewrite M4. rewrite <- L2. subst c'. reflexivity.

          apply cause_cause_step.
          unfold cause_step. right. split_all.
          apply in_split in M1. destruct M1 as [l1 [l2 M1]]. unfold prec. rewrite M1. exists l1. exists l2. exists nil. rewrite app_assoc. reflexivity.
          assumption.
          assumption.
          rewrite M3. rewrite <- L1. reflexivity.
          rewrite M4. rewrite <- L2. reflexivity.
          
        (* There is an update. *)
          destruct M as [M1 [M2 [M3 [M4 M5]]]].
          simpl in L.
          destruct L as [L1 [L2 _]].
          subst k. remember (label_key l) as k eqn: Hk.
          subst n. remember (label_node l) as n eqn: Hn.
          remember (alg_state (node_states s1 n)) as as1 eqn: Ha.
          
          assert (P := in_exec h (init p) s1 lw).
            depremise P. split; assumption.
            destruct P as [h2'' [s2'' [s3'' [h3'' [P1 [P2 [P3 P4]]]]]]].

          assert (Q := update_dep s2'' s3'' lw).
            depremise Q. split; assumption. simpl in Q.
            destruct Q as [me [Q1 [Q2 [Q3 [Q4 _]]]]].

          assert (R := message_pre_put p h2'' s2'' me). 
            simpl in R. depremise R. split; assumption.
            destruct R as [lp [R1 [R2 [R3 [R4 R5]]]]].

          exists lp. split_all.

          assumption.
          rewrite <- R3. rewrite <- Q2. rewrite M3. rewrite <- L1. subst n'. reflexivity.
          rewrite <- R4. rewrite <- Q3. rewrite M4. rewrite <- L2. subst c'. reflexivity.

          apply cause_cause_step.
          unfold cause_step. right. split_all.
          apply in_split in R1. destruct R1 as [l1 [l2 R1]]. unfold prec. rewrite P1. rewrite R1. exists l1. exists (l2++lw::h3''). exists nil. rewrite app_assoc. rewrite app_comm_cons. rewrite app_assoc. reflexivity.
          assumption.
          assumption.
          rewrite <- R3. rewrite <- Q2. rewrite M3. rewrite <- L1. reflexivity.
          rewrite <- R4. rewrite <- Q3. rewrite M4. rewrite <- L2. reflexivity.
    Qed.


  Lemma in_dep_get_or_put:
    forall p h s n,
      let d := dep (alg_state (node_states s n)) in
      step_star (init p) h s
      -> forall id,
           let n' := fst id in
           let c' := snd id in
           In id d
           -> (exists l' l,
                 label_node l = n
                 /\ label_is_get l
                 /\ label_is_put l'
                 /\ label_node l' = n'
                 /\ label_clock l' = c'
                 /\ cause h l' l)
              \/ (exists l, 
                    label_node l = n
                    /\ label_node l = n'
                    /\ label_clock l = c'
                    /\ label_is_put l
                    /\ In l h).

    Proof.
      intros.
      remember (init p) as s0 eqn: Hs.
      induction H as [s | s1 h s2 l s3 N1 N2 N3].
      
      subst d. subst s. simpl in H0. contradiction.

      simpl in N2. depremise N2. assumption.

      destruct (eq_nat_dec (label_node l) n).

      (* the same node *)

      inversion N3.

      (* put *)
        subst l0.
        rewrite <- H2 in e. simpl in e.
        subst d.
        subst n.
        rewrite <- H3 in H0.
        simpl in H0.
        simpl_override_in H0.
        simpl in H0.
        destruct H0 as [H0 | H0]; try contradiction.
        right.
        clear N2.
        exists l. split_all.
        subst l. simpl. reflexivity.
        subst l. simpl. 
        subst n'. subst id. simpl. reflexivity.
        subst l. simpl. subst c'. subst id. simpl. assert (A := sem_clock_alg_state_clock p h s2 n0). simpl in A. depremise A. subst s1. assumption. rewrite <- H1 in A. simpl in A. simpl_override_in A. simpl in A. rewrite A. reflexivity.
        subst l. simpl. apply I.
        subst l. apply in_app_iff. right. apply in_eq.

      (* get *)
        rewrite <- H2 in e. simpl in e.
        subst d.
        subst n.
        rewrite <- H3 in H0.
        simpl in H0.
        simpl_override_in H0.
        simpl in H0.
        assert (A1: (id = (entry_node (store s k), entry_clock (store s k)) /\ entry_node (store s k) <> init_nid)
                    \/ In id (dep s)).
          destruct (entry_node (store s k) <>? init_nid) eqn: Hn. simpl in H0. destruct H0. left. split. symmetry. assumption. bool_to_prop_in Hn. assumption. right. assumption.
          right. assumption.
        clear H0.
        destruct A1 as [A1 | A1].

          destruct A1 as [A11 A12].
          clear N2.
          left.
          assert (A2 := reads_from_cause p h s2 l s3).          
            simpl in A2. depremise A2. split_all. 
            subst s1. assumption. assumption. subst l. simpl. apply I.
            subst l. simpl. subst n'0. subst u. subst r. simpl. 
            assert (A := inst_entry_eq p h s2 n0 k).
              depremise A. subst s1. assumption.
              simpl in A. rewrite <- H1 in A. simpl in A. simpl_override_in A. simpl in A.
              destruct A as [A1 A2].
          rewrite A1 in A12.
          assumption.

          rewrite  <- H2 in A2.
          simpl in A2.
          destruct A2 as [l' [A21 [A22 [A23 A24]]]].
          assert (A3:= inst_entry_eq p h s2 n0 k). depremise A3. subst s1. assumption. simpl in A3. rewrite <- H1 in A3. simpl in A3. simpl_override_in A3. simpl in A3. destruct A3 as [A31 A32].
          exists l'. exists l. split_all.
          subst l. simpl. reflexivity.
          subst l. simpl. apply I.
          assumption. 
          clear A24. rewrite A22. subst n'0. subst u. subst r. subst n'. subst id. simpl. symmetry. assumption.
          clear A24. rewrite A23. subst c'0. subst u. subst r. subst c'. subst id. simpl. symmetry. assumption.
          rewrite H2 in *. assumption.

          rewrite <- H1 in N2.
          simpl in N2.
          simpl_override_in N2.
          simpl in N2.
          depremise N2. assumption.
          destruct N2 as [N2 | N2].
          destruct N2 as [l' [l'' [N21 [N22 [N23 [N24 [N25 N26]]]]]]].
          left. exists l'. exists l''. split_all. assumption. assumption. assumption. assumption. assumption. eapply cause_ext_cause. assumption.
          destruct N2 as [l' [N21 [N22 [N23 [N24 N25]]]]]. right. exists l'. split_all. assumption. assumption. assumption. assumption. apply in_app_iff. left. assumption.

      (* update *)
        rewrite <- H3 in e. simpl in e.
        subst d.
        subst n.
        rewrite <- H4 in H0.
        simpl in H0.
        simpl_override_in H0.
        simpl in H0.
        rewrite <- H2 in N2.
        simpl in N2.
        simpl_override_in N2.
        simpl in N2.
        depremise N2. assumption.
        destruct N2 as [N2 | N2].
        destruct N2 as [l' [l'' [N21 [N22 [N23 [N24 [N25 N26]]]]]]].
        left. exists l'. exists l''. split_all. assumption. assumption. assumption. assumption. assumption. eapply cause_ext_cause. assumption.
        destruct N2 as [l' [N21 [N22 [N23 [N24 N25]]]]]. right. exists l'. split_all. assumption. assumption. assumption. assumption. apply in_app_iff. left. assumption.
        
      (* put *)
        rewrite <- H2 in e. simpl in e.
        subst d.
        subst n.
        rewrite <- H3 in H0.
        simpl in H0.
        simpl_override_in H0.
        simpl in H0.
        depremise N2.
        subv s2.
        simpl_override.
        assumption.
        destruct N2 as [N2 | N2].
        destruct N2 as [l' [l'' [N21 [N22 [N23 [N24 [N25 N26]]]]]]].
        left. exists l'. exists l''. split_all. assumption. assumption. assumption. assumption. assumption. eapply cause_ext_cause. assumption.
        destruct N2 as [l' [N21 [N22 [N23 [N24 N25]]]]]. right. exists l'. split_all. assumption. assumption. assumption. assumption. apply in_app_iff. left. assumption.



      (* a different node *)
        subst d.
        assert (A: dep (alg_state (node_states s3 n)) = dep (alg_state (node_states s2 n))).
          clear H0 N2.
          inversion N3;
          subst l; simpl in *;
          simpl_override;
          simpl_override;
          reflexivity.
        rewrite A in *. clear A.
        depremise N2. assumption.
        destruct N2 as [N2 | N2].
        destruct N2 as [l' [l'' [N21 [N22 [N23 [N24 [N25 N26]]]]]]].
        left. exists l'. exists l''. split_all. assumption. assumption. assumption. assumption. assumption. eapply cause_ext_cause. assumption.
        destruct N2 as [l' [N21 [N22 [N23 [N24 N25]]]]]. right. exists l'. split_all. assumption. assumption. assumption. assumption. apply in_app_iff. left. assumption.

    Qed.


  Lemma prec_in_dep:
    forall p h0 s1 h s2 l n,
      let as1 := alg_state (node_states s1 n) in
      let as2 := alg_state (node_states s2 n) in
      let lid := (label_node l, label_clock l) in
      (step_star (init p) h0 s1
       /\ step_star s1 h s2
       /\ label_is_put l
       /\ In l h0
       /\ (In lid (dep as1)
           \/ (exists l', let lid' := (label_node l', label_clock l') in
                          label_is_put l' /\ cause h0 l l' /\ In lid' (dep as1) /\ In l' h0)))
       -> (In lid (dep as2)
           \/ (exists l', let lid' := (label_node l', label_clock l') in
                          label_is_put l' /\ cause (h0++h) l l' /\ In lid' (dep as2) /\ In l' (h0++h))).

    Proof.
      intros.
      destruct H as [N1 [N2 [N3 [N4 N5]]]].
      
      induction N2 as [s1 | s1 h s2 lc s3 N21 N22 N23].

      (* Base case *)
        subst as1.
        subst as2.
        rewrite app_nil_r. destruct N5 as [N5 | N5]. left. assumption. right. destruct N5 as [l' [N51 [N52 [N53 N54]]]]. exists l'. simpl. split_all; assumption.

      (* Inductive case *)
        subst as1.
        subst as2.
        simpl in N22. depremise N22. assumption.
        depremise N22. destruct N5 as [N5 | N5].
        left. assumption.

        right. destruct N5 as [l' N5]. simpl in N5. destruct N5 as [N51 [N52 [N53 N54]]].
        exists l'. split_all; assumption.
        clear N5.

        destruct (eq_nat_dec (label_node lc) n).
          
        (* same node transition *)
          inversion N23.

          (* put *)
          subst l0.
          rewrite <- H1 in e. simpl in e.
          subst n.
          rewrite <- H0 in N22.
          simpl in *.
          simpl_override.
          simpl.
          simpl_override_in N22.
          simpl in N22.
          right.
          rewrite H1.
          exists lc.
          split_all.
          subst lc. simpl. apply I. 
          destruct N22 as [N22 | N22].

            (* directly in d *)
              assert (A1 := in_dep_get_or_put p (h0 ++ h) s2 (label_node lc)).
                simpl in A1. depremise A1. apply step_star_app. exists s1. split; assumption.
                specialize (A1 lid). rewrite <- H0 in A1. rewrite <- H1 in A1. simpl in A1. simpl_override_in A1. simpl in A1. depremise A1. assumption. 
              destruct A1 as [A1 | A1].

                (* in dep by a get *)
                  destruct A1 as [l' [l'' [A11 [A12 [A13 [A14 [A15 A16]]]]]]].

                  assert (A2: l' = l).
                    eapply put_unique. split_all.
                    eapply step_star_app. exists s1. split. eassumption. eassumption.
                    apply cause_in in A16. destruct A16. assumption. apply in_app_iff. left. assumption.
                    assumption. assumption. assumption. assumption.
                  subst l'.
                  
                  assert (A3: cause (h0 ++ h ++ [lc]) l'' lc).
                    assert (B1 := cause_in (h0 ++ h) l l''). depremise B1. assumption. destruct B1 as [_ B1].
                    apply in_split in B1. destruct B1 as [l1 [l2 B1]].
                    apply cause_cause_step. unfold cause_step. left. split_all.
                    unfold prec. rewrite app_assoc. rewrite B1. exists l1. exists l2. exists nil. rewrite app_assoc. reflexivity.
                    subst lc. simpl. assumption.
                    left. split. assumption. subst lc. simpl. apply I.

                  eapply cause_cause_trans. split. rewrite app_assoc. apply cause_ext_cause. eassumption. assumption.

                (* in dep by the previous put *)
                  destruct A1 as [l' [A11 [A12 [A13 [A14 A15]]]]].
                  assert (A2: l' = l).
                    eapply put_unique. split_all.
                    eapply step_star_app. exists s1. split. eassumption. eassumption.
                    assumption. apply in_app_iff. left. assumption.
                    assumption. assumption. assumption. assumption. 
                  subst l'.

                  apply cause_cause_step. unfold cause_step.
                  left. split_all. apply in_split in A15. destruct A15 as [l1 [l2 A15]]. rewrite app_assoc. rewrite A15. unfold prec. exists l1. exists l2. exists nil. rewrite app_assoc. reflexivity.
                  subst lc. simpl. assumption.
                  right. split. assumption. subst lc. simpl. apply I.
 
            (* indirectly in d *)
              destruct N22 as [lm [N221 [N222 [N223 N224]]]].

              assert (A1 := in_dep_get_or_put p (h0 ++ h) s2 (label_node lc)).
                simpl in A1. depremise A1. apply step_star_app. exists s1. split; assumption.
                specialize (A1 (label_node lm, label_clock lm)). rewrite <- H0 in A1. rewrite <- H1 in A1. simpl in A1. simpl_override_in A1. simpl in A1. depremise A1. assumption. 
              destruct A1 as [A1 | A1].

                (* in dep by a get *)
                  destruct A1 as [l' [l'' [A11 [A12 [A13 [A14 [A15 A16]]]]]]].

                  assert (A2: l' = lm).
                    eapply put_unique. split_all.
                    eapply step_star_app. exists s1. split. eassumption. eassumption.
                    apply cause_in in A16. destruct A16. assumption. eapply prec_in. eapply cause_prec. split. apply step_star_app. exists s1. split; eassumption. eassumption. 
                    assumption. assumption. assumption. assumption. 
                  subst l'.
                  
                  assert (A3: cause (h0 ++ h ++ [lc]) l'' lc).
                    assert (B1 := cause_in (h0 ++ h) lm l''). depremise B1. assumption. destruct B1 as [_ B1].
                    apply in_split in B1. destruct B1 as [l1 [l2 B1]].
                    apply cause_cause_step. unfold cause_step. left. split_all.
                    unfold prec. rewrite app_assoc. rewrite B1. exists l1. exists l2. exists nil. rewrite app_assoc. reflexivity.
                    subst lc. simpl. assumption.
                    left. split. assumption. subst lc. simpl. apply I.

                  eapply cause_cause_trans. split. rewrite app_assoc. apply cause_ext_cause. eassumption. eapply cause_cause_trans. split. rewrite app_assoc. apply cause_ext_cause. eassumption. eassumption.

                (* in dep by the previous put *)
                  destruct A1 as [l' [A11 [A12 [A13 [A14 A15]]]]].
                  assert (A2: l' = lm).
                    eapply put_unique. split_all.
                    eapply step_star_app. exists s1. split. eassumption. eassumption.
                    assumption. eapply cause_in. eassumption.
                    assumption. assumption. assumption. assumption. 
                  subst l'.
                  
                  assert (A3: cause (h0 ++ h ++ [lc]) lm lc).
                    apply cause_cause_step. unfold cause_step.
                    left. split_all. apply in_split in A15. destruct A15 as [l1 [l2 A15]]. rewrite app_assoc. rewrite A15. unfold prec. exists l1. exists l2. exists nil. rewrite app_assoc. reflexivity.
                    subst lc. simpl. assumption.
                    right. split. assumption. subst lc. simpl. apply I.


                  eapply cause_cause_trans. split. rewrite app_assoc. apply cause_ext_cause. eassumption. eassumption.
               
             left.
             rewrite <- H1.
             simpl.
             assert (A1 := sem_clock_alg_state_clock p (h0++h) s2 n0).
               depremise A1. apply step_star_app. exists s1. split; assumption.
               simpl in A1. rewrite <- H0 in A1. simpl in A1. simpl_override_in A1. simpl in A1.
             rewrite A1.
             reflexivity.

             rewrite app_assoc. apply in_app_iff. right. apply in_eq.

          (* get *)
            simpl in *.
            rewrite <- H1 in e. simpl in e.
            subst n.
            simpl_override.
            simpl.
            rewrite <- H0 in N22.
            simpl in N22.
            simpl_override_in N22.
            simpl in N22.

            destruct N22 as [N22 | N22].
            
              left. destruct (entry_node (store s k) <>? init_nid). apply in_cons. assumption. assumption.

              right. destruct N22 as [l' [N221 [N222 [N223 N224]]]]. exists l'. split_all. assumption. rewrite H1. rewrite app_assoc. apply cause_ext_cause. assumption. destruct (entry_node (store s k) <>? init_nid). apply in_cons. assumption. assumption.
              rewrite app_assoc. apply in_app_iff. left. assumption.

          (* update *)
            simpl.
            rewrite <- H2 in e. simpl in e.
            subst n.
            simpl_override.
            simpl.
            rewrite <- H1 in N22.
            simpl in N22.
            simpl_override_in N22.
            simpl in N22.
            destruct N22 as [N22 | N22].
            left. assumption.
            right. destruct N22 as [l' [N221 [N222 [N223 N224]]]]. exists l'. split_all. assumption. rewrite H2. rewrite app_assoc. eapply cause_ext_cause. assumption. assumption.
            rewrite app_assoc. apply in_app_iff. left. assumption.            

          (* fault *)
            simpl in *.
            rewrite <- H1 in e. simpl in e.
            subst n.
            simpl_override.
            rewrite <- H0 in N22.
            simpl in N22.
            simpl_override_in N22.

            destruct N22 as [N22 | N22].
            
              left. assumption.

              right. destruct N22 as [l' [N221 [N222 [N223 N224]]]]. exists l'. split_all. assumption. rewrite H1. rewrite app_assoc. apply cause_ext_cause. assumption. assumption.
              rewrite app_assoc. apply in_app_iff. left. assumption.

        (* same node transition *)
          
          inversion N23; simpl in *.
          
          (* put *)
            assert (A: alg_state (node_states s2 n) = alg_state (node_states s3 n)).
            subst s2.
            subst s3.
            simpl.
            subst.
            subst.
            simpl in *.
            simpl_override.
            simpl_override.
            reflexivity.
            
            subst lc.
            simpl_override.
            rewrite <- H0 in N22.
            simpl in N22.
            simpl_override_in N22.

            destruct N22 as [N22 | N22].
            left. assumption.
            right. destruct N22 as [l'' [N221 [N222 [N223 N224]]]].
            exists l''. 
            split_all. 
            assumption.
            rewrite app_assoc. eapply cause_ext_cause. assumption.
            assumption.
            rewrite app_assoc. apply in_app_iff. left. assumption.                        

          (* get *)
            assert (A: alg_state (node_states s2 n) = alg_state (node_states s3 n)).
            subst s2.
            subst s3.
            simpl.
            subst.
            simpl in *.
            simpl_override.
            simpl_override.
            reflexivity.
            
            subst lc.
            simpl_override.
            rewrite <- H0 in N22.
            simpl in N22.
            simpl_override_in N22.

            destruct N22 as [N22 | N22].
            left. assumption.
            right. destruct N22 as [l'' [N221 [N222 [N223 N224]]]].
            exists l''. 
            split_all. 
            assumption.
            rewrite app_assoc. eapply cause_ext_cause. assumption.
            assumption.
            rewrite app_assoc. apply in_app_iff. left. assumption.            
              
          (* update *)
            assert (A: alg_state (node_states s2 n) = alg_state (node_states s3 n)).
            subst s2.
            subst s3.
            simpl.
            subst.
            simpl in *.
            simpl_override.
            simpl_override.
            reflexivity.
            
            subst lc.
            simpl_override.
            rewrite <- H1 in N22.
            simpl in N22.
            simpl_override_in N22.

            destruct N22 as [N22 | N22].
            left. assumption.
            right. destruct N22 as [l'' [N221 [N222 [N223 N224]]]].
            exists l''. 
            split_all. 
            assumption.
            rewrite app_assoc. eapply cause_ext_cause. assumption.
            assumption.
            rewrite app_assoc. apply in_app_iff. left. assumption.            

          (* fault *)
            assert (A: alg_state (node_states s2 n) = alg_state (node_states s3 n)).
            subst s2.
            subst s3.
            simpl.
            subst.
            simpl in *.
            simpl_override.
            simpl_override.
            reflexivity.
            
            subst lc.
            simpl_override.
            rewrite <- H0 in N22.
            simpl in N22.
            simpl_override_in N22.

            destruct N22 as [N22 | N22].
            left. assumption.
            right. destruct N22 as [l'' [N221 [N222 [N223 N224]]]].
            exists l''. 
            split_all. 
            assumption.
            rewrite app_assoc. eapply cause_ext_cause. assumption.
            assumption.
            rewrite app_assoc. apply in_app_iff. left. assumption.            

    Qed.



  Lemma reads_from_dep:
    forall p h s l l',
      (step_star (init p) h s
       /\ prec h l l'
       /\ label_is_put l
       /\ label_is_get l'
       /\ label_node l = label_orig_node l'
       /\ label_clock l = label_clock l')
      -> (In (label_node l, label_clock l) (label_dep l')
          \/ (exists l'', 
                label_is_put l''
                /\ cause h l l'' 
                /\ In (label_node l'', label_clock l'') (label_dep l')
                /\ prec h l'' l')).


    Proof.
      intros.
      destruct H as [N1 [N2 [N3 [N4 [N5 N6]]]]].

      assert (A1 := prec_exec p h s l l').
        depremise A1. split; assumption.
        destruct A1 as [h1 [s1 [s1' [h2 [s2' [s2 [h3 [A11 [A12 [A13 [A14 [A15 A16]]]]]]]]]]]].

      assert (A2 := reads_from_cause p (h1++[l]++h2) s2' l' s2).
        simpl in A2. depremise A2. split_all. 
        apply step_star_app. exists s1. split. assumption. apply step_star_end. exists s1'. split; assumption. assumption.
        assumption.
        rewrite <- N5. eapply label_node_not_in_nids. split.
        apply N1. apply prec_in in N2. destruct N2; assumption.

      destruct A2 as [lp [A21 [A22 [A24 A25]]]].

      assert (A3 := put_unique p h s l lp).
        depremise A3. split_all.
        assumption.
        apply prec_in in N2. destruct N2; assumption.
        apply cause_in in A25. destruct A25 as [A25 _]. rewrite A16. 
        rewrite app_comm_cons.
        rewrite app_assoc.
        apply in_app_iff in A25. destruct A25. apply in_app_iff. left. assumption. apply in_app_iff. right. simpl in H. destruct H; try contradiction. subst l'. apply in_eq.
        assumption.
        assumption.
        rewrite N5. rewrite <- A22. reflexivity.
        rewrite N6. rewrite <- A24. reflexivity.

      subst lp.

      destruct (eq_nat_dec (label_node l) (label_node l')).

        (* same node *)
          assert (A4 := prec_in_dep p (h1++[l]) s1' (h2++[l']) s2 l (label_node l)).
            simpl in A4. depremise A4. split_all.
            apply step_star_app_one. exists s1. split; assumption.
            apply step_star_app_one. exists s2'. split; assumption.
            assumption.
            apply in_app_iff. right. apply in_eq.
            left. destruct l; simpl in *; try contradiction. inversion A12. simpl. simpl_override. simpl. left. rewrite H2.
            assert (B1 := sem_clock_alg_state_clock p h1 s1 n1). simpl in B1. depremise B1. assumption. subst s1. simpl in B1. simpl_override_in B1. simpl in B1. rewrite B1. reflexivity.

            assert (B1: dep (alg_state (node_states s2 (label_node l'))) = label_dep l').
              destruct l'; simpl in *; try contradiction. inversion A14. simpl. simpl_override. simpl. reflexivity.

            destruct A4 as [A41 | A42].
            
            left.
            rewrite e in A41 at 2.
            rewrite B1 in A41.
            assumption.

            right.
            destruct A42 as [le [A421 [A422 [A423 A424]]]].
            exists le. split_all.
            assumption.
            rewrite A16. rewrite cons_to_app. assert (B2 := cons_to_app h3 l'). rewrite B2. clear B2. rewrite app_assoc. rewrite app_assoc. rewrite app_assoc. eapply cause_ext_cause. rewrite <- app_assoc. apply A422.
            rewrite e in A423.
            rewrite B1 in A423.
            assumption.

            rewrite app_assoc in A424.
            apply in_app_iff in A424.
            destruct A424 as [A424 | A424].
            rewrite A16. apply in_split in A424. destruct A424 as [l1 [l2 A424]].             rewrite cons_to_app. rewrite app_assoc. rewrite app_assoc. rewrite A424. unfold prec. exists l1. exists l2. exists h3. rewrite app_assoc. reflexivity.
            simpl in A424. destruct A424; try contradiction. subst le. destruct l'; simpl in *; contradiction.
            
        (* a different node *)
          left.

          assert (A3 := label_node_not_in_nids p (h1++[l]) s1' l). 
            depremise A3. split. apply step_star_app_one. exists s1. split; assumption.
            apply in_app_iff. right. apply in_eq.

          assert (A4 := get_from_map p (h1++[l]++h2) s2' s2 l').
            simpl in A4. depremise A4. split_all. apply step_star_app. exists s1. split. assumption. apply step_star_end. exists s1'. split; assumption.
            assumption.
            assumption.

          assert (A5 := inst_entry_eq p (h1++[l]++h2) s2' (label_node l') (label_key l')).
            simpl in A5. depremise A5. split_all. apply step_star_app. exists s1. split. assumption. apply step_star_end. exists s1'. split; assumption.

          destruct l'; simpl in *; try contradiction. inversion A14.

          subst n2.
          subst k.
          
          rewrite <- H0 in A4.
          simpl in A4.
          simpl_override_in A4.
          simpl in A4.
          destruct A4 as [A41 [A42 A43]].

          rewrite <- H0 in A5.
          simpl in A5.
          simpl_override_in A5.
          simpl in A5.
          destruct A5 as [A51 A52].

          subst s'. subst r. simpl.
          rewrite A22. rewrite A24.
          rewrite A41. rewrite A42.
          rewrite A51. rewrite A52. 
          destruct (inst_val_nid (entry_val (store s0 k0)) =? init_nid) eqn: He.
          bool_to_prop_in He. subst n1. subst n'. rewrite <- H2 in A3. subst u. simpl in A3. contradiction.
          bool_to_prop_in He. simpl. left. reflexivity.

    Qed.


  Lemma cause_dep:
    forall p h s l l',
      (step_star (init p) h s
       /\ label_is_put l
       /\ cause h l l')
      -> (In (label_node l, label_clock l) (label_dep l')
          \/ (exists l'', 
                label_is_put l''
                /\ cause h l l''
                /\ In (label_node l'', label_clock l'') (label_dep l')
                /\ prec h l'' l')).

    Proof.
      intros.
      destruct H as [N1 [N2 N3]].

      induction N3.
  
      (* Base case *)
        unfold cause_step in H.
        destruct H as [H | H].

          (* Process order *)
            destruct H as [M1 [M2 M3]].
            destruct M3 as [M3 | M3].     

              (* get, put *)
              destruct M3 as [M31 M32].
              destruct l; simpl in *; try contradiction.

              (* put, put *)            
              destruct M3 as [M31 M32].

              assert (A1 := prec_exec p h s l l').
                depremise A1. split; assumption.
                destruct A1 as [h1 [s1 [s1' [h2 [s2' [s2 [h3 [A11 [A12 [A13 [A14 [A15 A16]]]]]]]]]]]].

              assert (A2 := prec_in_dep p (h1 ++ [l]) s1' h2 s2' l (label_node l)).
                simpl in A2. depremise A2. split_all.
                apply step_star_app_one. exists s1. split; assumption.
                assumption.
                assumption.
                apply in_app_iff. right. apply in_eq.
                left. destruct l; simpl in *; try contradiction. clear M31.
                inversion A12. simpl. simpl_override. simpl. left. rewrite H2. apply f2_equal. split. reflexivity. assert (B1 := sem_clock_alg_state_clock p h1 s1 n1). simpl in B1. depremise B1. assumption. rewrite <- H0 in B1. simpl in B1. simpl_override_in B1. simpl in B1. rewrite B1. reflexivity.

              assert (A3: label_dep l' = dep (alg_state (node_states s2' (label_node l)))).
                destruct l'; simpl in *; try contradiction. clear M32.
                inversion A14. simpl. simpl_override. simpl. reflexivity.            
              rewrite A3. clear A3.

              destruct A2 as [A2 | A2].
              left. assumption.
              right. destruct A2 as [le [A21 [A22 [A23 A24]]]].
              exists le. split_all. assumption. rewrite A16. rewrite cons_to_app. rewrite app_assoc. rewrite app_assoc. apply cause_ext_cause. assumption.
              assumption.
              
              apply cause_in in A22. destruct A22 as [_ A22].
              apply in_split in A24. destruct A24 as [l1 [l2 A24]]. 
              rewrite <- app_assoc in A24. rewrite <- cons_to_app in A24. 
              rewrite app_comm_cons in A16. rewrite app_assoc in A16. rewrite A24 in A16.
              rewrite A16. unfold prec. exists l1. exists l2. exists h3. rewrite app_assoc.
              reflexivity.
             
          (* Reads-from *)
            destruct H as [M1 [M2 [M3 [M4 M5]]]].

            assert (A2 := reads_from_dep p h s l l').
              depremise A2. split_all; assumption.
            assumption.

      (* Inductive case *)
        depremise IHN3. assumption.
        depremise IHN3. assumption.

        assert (H' := H).
        unfold cause_step in H.
        destruct H.

        (* process order *)
          destruct H as [M1 [M2 [M3 | M3]]];
          destruct M3 as [M3 M4].

          (* get, put *)
            assert (A1 := prec_exec p h s l' l'').
              depremise A1. split; assumption.
              destruct A1 as [h1 [s1 [s1' [h2 [s2' [s2 [h3 [A11 [A12 [A13 [A14 [A15 A16]]]]]]]]]]]].

            assert (A2 := prec_in_dep p (h1++[l']) s1' h2 s2' l (label_node l')).
              simpl in A2. depremise A2. split_all.
              apply step_star_app_one. exists s1. split; assumption. assumption.
              assumption.
              apply in_app_iff. left. eapply prec_pre_post_in. split_all.
                subst h. rewrite <- cons_to_app. eassumption. 
                subst h. rewrite <- cons_to_app. eapply cause_prec. split_all. eassumption. assumption.
                
              assert (B1: label_dep l' = dep (alg_state (node_states s1' (label_node l')))).
              destruct l'; simpl in *; try contradiction. clear M3.
              inversion A12. simpl. simpl_override. simpl. reflexivity.
              rewrite B1 in *; clear B1.
              destruct IHN3 as [IHN3 | IHN3].
              left. assumption.
              right. destruct IHN3 as [le [IHN31 [IHN32 [IHN33 IHN34]]]]. exists le. split_all.
              assumption.
              assert (B2 := prec_pre_post_in p h1 (h2 ++ l'' :: h3) s le l').
                depremise B2. split. apply step_star_app. exists s1. split. assumption. apply step_star_app. exists s1'. split. apply step_star_one. assumption. apply step_star_app. exists s2'. split. assumption. apply step_star_end. exists s2. split; assumption.
                rewrite A16 in IHN34. rewrite cons_to_app in IHN34. assumption.

              assert (B3 := cause_prefix_history p h1 (l' :: h2 ++ l'' :: h3) s l le).
                depremise B3. split_all.
                apply step_star_app. exists s1. split. assumption. apply step_star_end. exists s1'. split. assumption. apply step_star_app. exists s2'. split. assumption. apply step_star_end. exists s2. split; assumption.
                assumption.
                rewrite A16 in IHN32. assumption.

              apply cause_ext_cause. assumption.
              assumption.

              rewrite A16 in IHN34.
              assert (A2 := prec_pre_post_in p h1 (h2 ++ l'' :: h3) s le l').
                depremise A2. split_all.
                subst h; assumption.
                assumption.
              apply in_app_iff. left. assumption.

            clear IHN3.

            assert (A3: label_dep l'' = dep (alg_state (node_states s2' (label_node l')))).
            destruct l''; simpl in *; try contradiction. clear M4.
            inversion A14. simpl. simpl_override. simpl. reflexivity.            
            rewrite A3.

            destruct A2 as [A2 | A2].
            left. assumption.
            right. destruct A2 as [le [A21 [A22 [A23 A24]]]]. exists le. split_all. 
            assumption.
            rewrite A16. rewrite cons_to_app. rewrite app_assoc. rewrite app_assoc. eapply cause_ext_cause. assumption.
            assumption.
            apply cause_in in A22. destruct A22 as [_ A22].
            apply in_split in A22. destruct A22 as [l1 [l2 A22]]. 
            rewrite <- app_assoc in A22. rewrite <- cons_to_app in A22. 
            rewrite app_comm_cons in A16. rewrite app_assoc in A16. rewrite A22 in A16.
            rewrite A16. unfold prec. exists l1. exists l2. exists h3. rewrite app_assoc.
            reflexivity.

          (* put, put *)
            assert (A1 := prec_exec p h s l' l'').
              depremise A1. split; assumption.
              destruct A1 as [h1 [s1 [s1' [h2 [s2' [s2 [h3 [A11 [A12 [A13 [A14 [A15 A16]]]]]]]]]]]].

            assert (A2 := prec_in_dep p h1 s1 (l' :: h2) s2' l (label_node l')).
              simpl in A2. depremise A2. split_all.
              assumption. apply step_star_end. exists s1'. split; assumption.
              assumption.
              eapply prec_pre_post_in. split_all.
                subst h. rewrite <- cons_to_app. eassumption. 
                subst h. rewrite <- cons_to_app. eapply cause_prec. split_all. eassumption. assumption.

              assert (B1: label_dep l' = dep (alg_state (node_states s1 (label_node l')))).
              destruct l'; simpl in *; try contradiction. clear M3.
              inversion A12. simpl. simpl_override. simpl. reflexivity.
              rewrite B1 in *; clear B1.
              destruct IHN3 as [IHN3 | IHN3].
              left. assumption.
              right. destruct IHN3 as [le [IHN31 [IHN32 [IHN33 IHN34]]]]. exists le. split_all.

              assumption.

              assert (B2 := prec_pre_post_in p h1 (h2 ++ l'' :: h3) s le l').
                depremise B2. split. apply step_star_app. exists s1. split. assumption. apply step_star_app. exists s1'. split. apply step_star_one. assumption. apply step_star_app. exists s2'. split. assumption. apply step_star_end. exists s2. split; assumption.
                rewrite A16 in IHN34. rewrite cons_to_app in IHN34. assumption.

              assert (B3 := cause_prefix_history p h1 (l' :: h2 ++ l'' :: h3) s l le).
                depremise B3. split_all.
                apply step_star_app. exists s1. split. assumption. apply step_star_end. exists s1'. split. assumption. apply step_star_app. exists s2'. split. assumption. apply step_star_end. exists s2. split; assumption.
                assumption.
                rewrite A16 in IHN32. assumption.                

              assumption.
              assumption.

              rewrite A16 in IHN34.
              assert (A2 := prec_pre_post_in p h1 (h2 ++ l'' :: h3) s le l').
                depremise A2. split_all.
                subst h; assumption.
                assumption.
             assumption.

            clear IHN3.

            assert (A3: label_dep l'' = dep (alg_state (node_states s2' (label_node l')))).
            destruct l''; simpl in *; try contradiction. clear M4.
            inversion A14. simpl. simpl_override. simpl. reflexivity.            
            rewrite A3.

            destruct A2 as [A2 | A2].
            left. assumption.
            right. destruct A2 as [le [A21 [A22 [A23 A24]]]]. exists le. split_all. 
            assumption.
            rewrite A16. rewrite cons_to_app. rewrite app_assoc. rewrite app_assoc. eapply cause_ext_cause. rewrite <- app_assoc. rewrite <- cons_to_app. assumption.
            assumption.
            apply cause_in in A22. destruct A22 as [_ A22].
            apply in_split in A22. destruct A22 as [l1 [l2 A22]].
            rewrite app_comm_cons in A16. rewrite app_assoc in A16.
            rewrite A22 in A16.
            rewrite A16. unfold prec. exists l1. exists l2. exists h3. rewrite app_assoc.
            reflexivity.

        (* reads from *)
          open_conjs.
          clear IHN3.
          right.

          assert (A1 := reads_from_dep p h s l' l'').
            depremise A1. split_all; assumption.
          destruct A1 as [A1 | A1].
          
          exists l'. split_all.
          assumption.
          assumption.
          assumption.
          assumption.
          destruct A1 as [le [A11 [A12 [A13 A14]]]].
          exists le. split_all.
          assumption.
          eapply cause_cause_trans. split; eassumption.
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
      assert (A1 := message_update_node_clock_eq p h s m). 
        simpl in A1. depremise A1. split; assumption.
      destruct A1 as [A1 _].
      assert (A2 := no_self_message p h s m).
        depremise A2. split; assumption.
      rewrite A1 in A2.
      assumption.

    Qed.
  

  Lemma rec_eq_clock:
    forall p h s n,
      let a := alg_state (node_states s n) in
      step_star (init p) h s
      -> received a n = clock a.

    Proof.
      intros.
      remember (init p) as s0 eqn: Hs.
      induction H.
      
      subst a.
      subst s.
      simpl.
      reflexivity.

      subst a.
      simpl in IHstep_star.
      depremise IHstep_star. assumption.

      inversion H0.

      (* put *)
      simpl.
      destruct (eq_nat_dec n0 n).

        simpl_override.
        simpl.
        simpl_override.
        reflexivity.

        simpl_override.
        rewrite <- H2 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        assumption.

      (* get *)
      simpl.
      destruct (eq_nat_dec n0 n).

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
        simpl in IHstep_star.
        assumption.

      (* update *)
      simpl.
      destruct (eq_nat_dec n0 n).
        
        subst n.
        simpl_override.
        simpl.
        assert (A := update_no_self_message p ls s2 (message n' c' k v u n0 lp)).
          depremise A. split. subst s1. assumption. rewrite <- H3. simpl. apply in_app_iff. right. apply in_eq.
          simpl in A.
        simpl_override.
        rewrite <- H3 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        simpl in IHstep_star.
        assumption.

        simpl_override.
        rewrite <- H3 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        simpl in IHstep_star.
        assumption.

      (* fault *)
      simpl.
      destruct (eq_nat_dec n0 n).

        subst n.
        simpl_override.
        rewrite <- H2 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        assumption.

        simpl_override.
        rewrite <- H2 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        assumption.
        
    Qed.

  Lemma msg_update_label:
    forall p h s m,
      step_star (init p) h s
      /\ In m (messages s)
      -> (let lp := msg_label m in
          let u := msg_update m in
          label_is_put lp
          /\ In lp h
          /\ label_node lp = sender_node u
          /\ label_clock lp = sender_clock u
          /\ label_dep lp = sender_dep u
          /\ label_key lp = msg_key m
          /\ label_val lp = msg_val m).

    Proof.
      intros.
      remember (init p) as s0 eqn: Hs.
      destruct H as [H1 H2].
      induction H1.

      subst s.
      simpl in H2.
      contradiction.

      depremise IHstep_star. assumption.
      inversion H.

      subst l0.
      subst u.
      rewrite <- H5 in H2.
      simpl in H2.
      apply in_app_iff in H2.
      destruct H2.
      depremise IHstep_star.
      rewrite <- H3.
      simpl.
      assumption.
      open_conjs.
      split_all; try assumption.
      apply in_app_iff. left. assumption.
      apply in_map_iff in H2.
      destruct H2 as [n' [N1 N2]].
      rewrite <- N1.
      simpl.
      subst lp.
      rewrite <- N1.
      simpl.
      split_all.
      apply I.
      apply in_app_iff. right. apply in_eq. reflexivity.
      assert (A:= sem_clock_alg_state_clock p ls s2 n).
        depremise A.
        subst s1. assumption.
        simpl in A.
        rewrite <- H3 in A.
        simpl in A.
        simpl_override_in A.
        simpl in A.
      rewrite A.
      reflexivity.
      reflexivity.
      reflexivity.
      reflexivity.

      subst u.
      rewrite <- H5 in H2.
      simpl in H2.
      depremise IHstep_star.
      rewrite <- H3.
      simpl.
      assumption.
      open_conjs.
      split_all; try assumption.
      apply in_app_iff. left. assumption.


      subst u.
      rewrite <- H6 in H2.
      simpl in H2.
      apply in_app_iff in H2.
      destruct H2 as [H2 | H2].
      depremise IHstep_star.
      rewrite <- H4.
      simpl.
      apply in_app_iff.
      left.
      assumption.
      open_conjs.
      split_all; try assumption.
      apply in_app_iff. left. assumption.

      depremise IHstep_star.
      rewrite <- H4.
      simpl.
      apply in_app_iff.
      right.
      apply in_cons.
      assumption.
      open_conjs.
      split_all; try assumption.
      apply in_app_iff. left. assumption.

      subst u.
      rewrite <- H5 in H2.
      simpl in H2.
      depremise IHstep_star.
      rewrite <- H3.
      simpl.
      assumption.
      open_conjs.
      split_all; try assumption.
      apply in_app_iff. left. assumption.

    Qed.

  Lemma clock_in_dep:
    forall p h s n,
      let ns := alg_state (node_states s n) in
      let c := clock ns in
      let d := dep ns in
      step_star (init p) h s
      -> c > 0 
      -> In (n, c) d.

  Proof.
    intros.
    remember (init p) as s0 eqn: Hs.

    induction H.

    subst c. subst ns. subst d. subst s. simpl in H0. inversion H0.

    simpl in IHstep_star.
    depremise IHstep_star. assumption.
    inversion H1.

    (* put *)
    subst d.
    subst ns.
    rewrite <- H5.
    simpl.
    destruct (eq_nat_dec n0 n).
      (* -- *)
      rewrite e0 in *.
      simpl_override.
      simpl.
      left.
      rewrite e0 in *.
      apply f2_equal.
      split. reflexivity.
      subst c.
      rewrite <- H5.
      simpl.
      simpl_override.
      simpl.
      reflexivity.
      (* -- *)
      simpl_override.
      subst c.
      rewrite <- H5.
      simpl.
      simpl_override.
      depremise IHstep_star.
        rewrite <- H3. simpl. simpl_override.
        rewrite <- H5 in H0. simpl in H0. simpl_override_in H0.
        assumption.
      rewrite <- H3 in IHstep_star. simpl in IHstep_star. simpl_override_in IHstep_star.
      assumption.

    (* get *)
      subst c.
      subst d.
      subst ns.
      rewrite <- H5.
      simpl.
      destruct (eq_nat_dec n0 n).
        (* -- *)
        subst n.
        simpl_override. 
        simpl.
        depremise IHstep_star.
          rewrite <- H3. simpl. simpl_override. simpl.
          rewrite <- H5 in H0. simpl in H0. simpl_override_in H0. simpl in H0.
          assumption.
        rewrite <- H3 in IHstep_star. simpl in IHstep_star. simpl_override_in IHstep_star. simpl in IHstep_star.
        destruct (entry_node (store s k) <>? init_nid).
        apply in_cons. assumption. assumption.
        (* -- *)
        simpl_override.
        depremise IHstep_star.
          rewrite <- H3. simpl. simpl_override. simpl.
          rewrite <- H5 in H0. simpl in H0. simpl_override_in H0. assumption.
        rewrite <- H3 in IHstep_star. simpl in IHstep_star. simpl_override_in IHstep_star. assumption.

    (* update *)
      subst c.
      subst d.
      subst ns.
      rewrite <- H6.
      simpl.
      destruct (eq_nat_dec n0 n).
        (* -- *)
        subst n.
        simpl_override. 
        simpl.
        depremise IHstep_star.
          rewrite <- H4. simpl. simpl_override. simpl.
          rewrite <- H6 in H0. simpl in H0. simpl_override_in H0. simpl in H0.
          assumption.
        rewrite <- H4 in IHstep_star. simpl in IHstep_star. simpl_override_in IHstep_star. simpl in IHstep_star.
        assumption.
        (* -- *)
        simpl_override.
        depremise IHstep_star.
          rewrite <- H4. simpl. simpl_override. simpl.
          rewrite <- H6 in H0. simpl in H0. simpl_override_in H0. assumption.
        rewrite <- H4 in IHstep_star. simpl in IHstep_star. simpl_override_in IHstep_star. assumption.

    (* fault *)
      subst c.
      subst d.
      subst ns.
      rewrite <- H5.
      simpl.
      destruct (eq_nat_dec n0 n).
        (* -- *)
        subst n.
        simpl_override. 
        depremise IHstep_star.
          rewrite <- H3. simpl. simpl_override.
          rewrite <- H5 in H0. simpl in H0. simpl_override_in H0. simpl in H0.
          assumption.
        rewrite <- H3 in IHstep_star. simpl in IHstep_star. simpl_override_in IHstep_star. 
        assumption.
        (* -- *)
        simpl_override.
        depremise IHstep_star.
          rewrite <- H3. simpl. simpl_override.
          rewrite <- H5 in H0. simpl in H0. simpl_override_in H0. assumption.
        rewrite <- H3 in IHstep_star. simpl in IHstep_star. simpl_override_in IHstep_star. assumption.

  Qed.


  Lemma update_pred:
    forall p h s m,
      (step_star (init p) h s
       /\ In m (messages s))
      -> (let u := msg_update m in
          let n := sender_node u in
          let c := sender_clock u in
          let d := sender_dep u in
          c > 1 -> In (n, pred c) d).

    Proof.
      intros.
      destruct H as [H1 H2].
      remember (init p) as s0 eqn: Hs.      

      induction H1.

      subst s. simpl in H2. contradiction.

      depremise IHstep_star. assumption.
      inversion H.

      (* put *)
      rewrite <- H6 in H2.
      simpl in H2.
      apply in_app_iff in H2.
      destruct H2 as [H2 | H2].

        apply IHstep_star.
        rewrite <- H4.
        simpl.
        assumption.

        apply in_map_iff in H2.
        destruct H2 as [rn [H21 H22]].
        subst d. subst u. subst c. subst n.
        rewrite <- H21.
        simpl.
        rewrite Plus.plus_comm.
        simpl.
        assert (A1 := clock_in_dep p ls s2 n0).
          simpl in A1. depremise A1. subst s1. assumption. 
          rewrite <- H4 in A1. simpl in A1. simpl_override_in A1. simpl in A1.
        rewrite <- H21 in H0. simpl in H0.
        apply A1.
        rewrite Plus.plus_comm in H0. simpl in H0.
        apply Gt.gt_pred in H0.
        rewrite <- pred_Sn in H0.
        assumption.

      (* get *)
        apply IHstep_star.
        rewrite <- H4. simpl.
        rewrite <- H6 in H2. simpl in H2.
        assumption.

      (* update *)
        apply IHstep_star.
        rewrite <- H5. simpl.
        rewrite <- H7 in H2. simpl in H2.
        apply in_app_iff in H2. destruct H2 as [H2 | H2].
        apply in_app_iff. left. assumption. apply in_app_iff. right. apply in_cons. assumption.

      (* fault *)
        apply IHstep_star.
        rewrite <- H4. simpl.
        rewrite <- H6 in H2. simpl in H2.
        assumption.

    Qed.


  Lemma update_sender_clock:
    forall p h s l s',
      (step_star (init p) h s
       /\ step s l s'
       /\ label_is_update l) ->
      (let n := label_node l in
       let n' := label_orig_node l in
       sender_clock (msg_update (label_message l)) <=
       (received (alg_state (node_states s n)) n') + 1).

    Proof.
      intros.
      destruct H as [H1 [H2 H3]].
      
      destruct l; simpl in *; try contradiction; clear H3.
      inversion H2.
      remember (update_label n0 n1 c n2 k v a m a0) as l eqn: Hl.      
      remember (message n'0 c' k0 v0 u n3 lp) as msg eqn: Hm.
      subst s'2.
      subst s'3.
      subst s'4.
      subst s'5.
      subst s'6.
      subst c.
      subst n.
      subst n'.
      subst n2.
      subst k.
      subst v.
      subst a.
      subst n0.
      subst n'0.
      simpl.
      simpl_override.
      simpl.
      assert (A1 := Lt.le_or_lt (sender_clock u) 1).
      destruct A1 as [A1 | A1].

        assert (A2 := Le.le_0_n (received s0 n1)).
        assert (A3 := plus_O_n (sender_clock u)).
        rewrite <- A3.
        eapply Plus.plus_le_compat; eassumption.
      
        assert (A2 := update_pred p h s msg).
          simpl in A2. depremise A2.
          split. assumption. subst s. simpl. apply in_app_iff. right. apply in_eq.
          depremise A2. subst msg. simpl. assumption.
          rewrite Hm in A2. simpl in A2.        
        unfold guard_method in H13.
        assert (A3 := fold_left_and (NId*Clock) (sender_dep u) 
                                    (sender_node u, pred (sender_clock u))
                                    (fun p => snd p <=? received s0 (fst p))).
          depremise A3. split; assumption.
          simpl in A3.
          bool_to_prop_in A3.

        apply Le.le_n_S in A3.

        assert (A4 := NPeano.Nat.succ_pred (sender_clock u)).
          depremise A4. intro. rewrite H in *. inversion A1.
        rewrite A4 in A3. clear A4.        

        assert (A5 := message_update_node_clock_eq p h s msg).
          simpl in A5. depremise A5.
          split. assumption. subst s. simpl. apply in_app_iff. right. apply in_eq.
          destruct A5 as [A5 _].
        rewrite Hm in A5. simpl in A5.
        rewrite A5.
        rewrite Plus.plus_comm.
        simpl.
        assumption.

    Qed.

  Lemma message_clock_le_state_clock:
    forall p h s m,
      let n := msg_sender m in
      let c := msg_clock m in
      let sn := alg_state (node_states s n) in
      (step_star (init p) h s
       /\ In m (messages s))
      -> c <= clock sn.

    Proof.
      intros.
      destruct H as [H1 H2].
      remember (init p) as s0 eqn: Hs.
      induction H1.

      subst sn. subst s. simpl in H2. contradiction.

      simpl in IHstep_star. depremise IHstep_star. assumption.

      inversion H.

      (* put *)
      subst c.
      subst sn.
      rewrite <- H5.
      simpl.
      destruct (eq_nat_dec n0 n).
        (* -- *)
        simpl_override.
        simpl.
        rewrite <- H5 in H2. simpl in H2.
        apply in_app_iff in H2.
        destruct H2 as [H2 | H2].
          (* -- *)
          depremise IHstep_star. rewrite <- H3. simpl. assumption.
          rewrite <- H3 in IHstep_star.
          simpl in IHstep_star.
          rewrite e0 in IHstep_star.
          simpl_override_in IHstep_star.
          simpl in IHstep_star.
          rewrite Plus.plus_comm.
          simpl.
          apply le_S.
          assumption.
          (* -- *)
          apply in_map_iff in H2.
          destruct H2 as [rn [H21 H22]].
          rewrite <- H21.
          simpl.
          assert (A1 := sem_clock_alg_state_clock p ls s2 n0).
            depremise A1. subst s1. assumption. 
            simpl in A1.
            rewrite <- H3 in A1.
            simpl in A1.
            simpl_override_in A1.
            simpl in A1.
          rewrite A1.
          reflexivity.
        (* -- *)
        simpl_override.
        depremise IHstep_star.
          rewrite <- H3.
          simpl.
          rewrite <- H5 in H2.
          simpl in H2.
          apply in_app_iff in H2.
          destruct H2 as [H2 | H2].
          assumption.
          exfalso.
          apply in_map_iff in H2.
          destruct H2 as [rn [H21 H22]].
          subst n.
          rewrite <- H21 in n1.
          simpl in n1.
          apply n1.
          reflexivity.
        rewrite <- H3 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        assumption.


      (* get *)
      subst c.
      subst sn.
      rewrite <- H5.
      simpl.
      destruct (eq_nat_dec n0 n).
        (* -- *)
        simpl_override.
        simpl.
        depremise IHstep_star.
          rewrite <- H3.
          simpl.
          rewrite <- H5 in H2.
          simpl in H2.
          assumption.
        rewrite <- H3 in IHstep_star.
        simpl in IHstep_star.
        rewrite e0 in IHstep_star.
        simpl_override_in IHstep_star.
        simpl in IHstep_star.
        assumption.
        (* -- *)
        simpl_override.
        depremise IHstep_star.
          rewrite <- H3.
          simpl.
          rewrite <- H5 in H2.
          simpl in H2.
          assumption.
        rewrite <- H3 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        simpl in IHstep_star.
        assumption.

      (* update *)
      subst c.
      subst sn.
      rewrite <- H6.
      simpl.
      destruct (eq_nat_dec n0 n).
        (* -- *)
        simpl_override.
        simpl.
        depremise IHstep_star.
          rewrite <- H4.
          simpl.
          rewrite <- H6 in H2.
          simpl in H2.
          apply in_app_iff in H2. destruct H2 as [H2 | H2]. apply in_app_iff. left. assumption. apply in_app_iff. right. apply in_cons. assumption.
        rewrite <- H4 in IHstep_star.
        simpl in IHstep_star.
        rewrite e0 in IHstep_star.
        simpl_override_in IHstep_star.
        simpl in IHstep_star.
        assumption.
        (* -- *)
        simpl_override.
        depremise IHstep_star.
          rewrite <- H4.
          simpl.
          rewrite <- H6 in H2.
          simpl in H2.
          apply in_app_iff in H2. destruct H2 as [H2 | H2]. apply in_app_iff. left. assumption. apply in_app_iff. right. apply in_cons. assumption.
        rewrite <- H4 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        simpl in IHstep_star.
        assumption.

      (* fault *)
      subst c.
      subst sn.
      rewrite <- H5.
      simpl.
      destruct (eq_nat_dec n0 n).
        (* -- *)
        simpl_override.
        depremise IHstep_star.
          rewrite <- H3.
          simpl.
          rewrite <- H5 in H2.
          simpl in H2.
          assumption.
        rewrite <- H3 in IHstep_star.
        simpl in IHstep_star.
        rewrite e0 in IHstep_star.
        simpl_override_in IHstep_star.
        assumption.
        (* -- *)
        simpl_override.
        depremise IHstep_star.
          rewrite <- H3.
          simpl.
          rewrite <- H5 in H2.
          simpl in H2.
          assumption.
        rewrite <- H3 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        assumption.
        
    Qed.



  Lemma received_lt_sent:
    forall p h s n n',
      let sn := alg_state (node_states s n) in
      let sn' := alg_state (node_states s n') in
      step_star (init p) h s
      -> received sn n' <= clock sn'.

    Proof.
      intros.
      remember (init p) as s0 eqn: Hs.
      induction H.
      
      subst sn. subst sn'. subst s. simpl. apply Le.le_refl.

      simpl in IHstep_star. depremise IHstep_star. assumption.
      inversion H0.

      (* put *)
        subst sn. subst sn'. rewrite <- H4. simpl.
        destruct (eq_nat_dec n0 n).
          (* -- *)
          subst n.
          simpl_override. simpl.
          destruct (eq_nat_dec n0 n').
            (* -- *)
            subst n'.
            simpl_override.
            simpl_override.
            simpl.
            reflexivity.
            (* -- *)
            simpl_override.
            simpl_override.
            rewrite <- H2 in IHstep_star.
            simpl in IHstep_star.
            simpl_override_in IHstep_star.
            simpl in IHstep_star.
            assumption.
          (* -- *)
          simpl_override.
          destruct (eq_nat_dec n0 n').
            (* -- *)
            subst n'.
            simpl_override.
            simpl.
            rewrite <- H2 in IHstep_star.
            simpl in IHstep_star.
            simpl_override_in IHstep_star.
            simpl in IHstep_star.
            eapply Plus.le_plus_trans.
            assumption.
            (* -- *)
            simpl_override.
            rewrite <- H2 in IHstep_star.
            simpl in IHstep_star.
            simpl_override_in IHstep_star.
            simpl_override_in IHstep_star.
            assumption.

      (* get *)
        subst sn. subst sn'.
        rewrite <- H4. simpl.
        destruct (eq_nat_dec n0 n).
          (* -- *)
          subst n.
          simpl_override.
          simpl.
          rewrite <- H2 in IHstep_star.
          simpl in IHstep_star.
          simpl_override_in IHstep_star.
          simpl in IHstep_star.
          destruct (eq_nat_dec n0 n').
          subst n'.
          simpl_override. simpl. simpl_override_in IHstep_star. simpl in IHstep_star. assumption.
          simpl_override. simpl. simpl_override_in IHstep_star. simpl in IHstep_star. assumption.
          (* -- *)
          simpl_override.
          rewrite <- H2 in IHstep_star.
          simpl in IHstep_star.
          simpl_override_in IHstep_star.
          destruct (eq_nat_dec n0 n').
          subst n'.
          simpl_override. simpl. simpl_override_in IHstep_star. simpl in IHstep_star. assumption.
          simpl_override. simpl. simpl_override_in IHstep_star. simpl in IHstep_star. assumption.

      (* update *)
        subst sn. subst sn'.
        rewrite <- H5. simpl.
        destruct (eq_nat_dec n0 n).
          (* -- *)
          subst n.
          simpl_override.
          simpl.
          destruct (eq_nat_dec (sender_node u) n').
            (* -- *)
            simpl_override.
            assert (A1 := message_clock_le_state_clock p ls s2 (message n'0 c' k v u n0 lp)).
              simpl in A1. depremise A1. split. subst s1. assumption. rewrite <- H3. apply in_app_iff. right. apply in_eq.
            rewrite <- H3 in A1. simpl in A1.
            assert (A2 := message_update_node_clock_eq p ls s2 (message n'0 c' k v u n0 lp)).
              simpl in A2. depremise A2. split. subst s1. assumption. rewrite <- H3. apply in_app_iff. right. apply in_eq.
            destruct A2 as [A21 A22].
            rewrite A21 in A1. rewrite e0 in A1. rewrite A22 in A1.
            destruct (eq_nat_dec n0 n').
            rewrite e1 in A1.
            simpl_override. simpl. simpl_override_in A1. simpl in A1. assumption.
            simpl_override. simpl. simpl_override_in A1. simpl in A1. assumption.

            (* -- *)
            simpl_override.
            rewrite <- H3 in IHstep_star.
            simpl in IHstep_star.
            simpl_override_in IHstep_star.
            simpl in IHstep_star.
            destruct (eq_nat_dec n0 n').
            rewrite e0 in IHstep_star.
            simpl_override. simpl. simpl_override_in IHstep_star. simpl in IHstep_star. assumption.
            simpl_override. simpl. simpl_override_in IHstep_star. simpl in IHstep_star. assumption.

          (* -- *)
            simpl_override.
            rewrite <- H3 in IHstep_star.
            simpl in IHstep_star.
            simpl_override_in IHstep_star.
            destruct (eq_nat_dec n0 n').
            rewrite e0 in IHstep_star.
            simpl_override. simpl. simpl_override_in IHstep_star. simpl in IHstep_star. assumption.
            simpl_override. simpl. simpl_override_in IHstep_star. simpl in IHstep_star. assumption.

      (* fault *)
        subst sn. subst sn'.
        rewrite <- H4. simpl.
        destruct (eq_nat_dec n0 n).
          (* -- *)
          subst n.
          simpl_override.
          simpl.
          rewrite <- H2 in IHstep_star.
          simpl in IHstep_star.
          simpl_override_in IHstep_star.
          simpl in IHstep_star.
          destruct (eq_nat_dec n0 n').
          subst n'.
          simpl_override. simpl. simpl_override_in IHstep_star. simpl in IHstep_star. assumption.
          simpl_override. simpl. simpl_override_in IHstep_star. simpl in IHstep_star. assumption.
          (* -- *)
          simpl_override.
          rewrite <- H2 in IHstep_star.
          simpl in IHstep_star.
          simpl_override_in IHstep_star.
          destruct (eq_nat_dec n0 n').
          subst n'.
          simpl_override. simpl. simpl_override_in IHstep_star. simpl in IHstep_star. assumption.
          simpl_override. simpl. simpl_override_in IHstep_star. simpl in IHstep_star. assumption.
            
    Qed.

  Lemma message_clock_neq:
    forall p h s m m',
      let n := msg_sender m in
      let c := msg_clock m in
      let rn := msg_receiver m in
      let n' := msg_sender m' in
      let c' := msg_clock m' in
      let rn' := msg_receiver m' in
      (step_star (init p) h s
       /\ In m (messages s)
       /\ In m' (messages s)
       /\ n = n'
       /\ rn = rn'
       /\ not (m = m'))
      -> not (c = c').

    Proof.
      intros.
      destruct H as [H1 [H2 [H3 [H4 [Hr Hn]]]]].
      remember (init p) as s0 eqn: Hs.
      induction H1.

      subst s. simpl in H2. contradiction.

      depremise IHstep_star. assumption.
      inversion H.

      (* put *)
        rewrite <- H7 in H2.
        simpl in H2.
        apply in_app_iff in H2.
        destruct H2 as [H2 | H2].
          (* -- *)
          rewrite <- H7 in H3.
          simpl in H3.
          apply in_app_iff in H3.        
          destruct H3 as [H3 | H3].
            (* -- *)
            apply IHstep_star.
            rewrite <- H5. simpl. assumption.
            rewrite <- H5. simpl. assumption.
            (* -- *)
            apply in_map_iff in H3.
            destruct H3 as [tn [H31 H32]].
            assert (A1 := message_clock_le_state_clock p ls s2 m). 
              simpl in A1. depremise A1. split. subst s1. assumption. rewrite <- H5. simpl. assumption.
            subst n. subst n'. rewrite H4 in A1. rewrite <- H31 in A1. simpl in A1. rewrite <- H5 in A1. simpl in A1. simpl_override_in A1. simpl in A1.
            subst c.
            subst c'.
            rewrite <- H31. simpl.
            assert (A2 := sem_clock_alg_state_clock p ls s2 n0).
              simpl in A2. depremise A2. 
              subst s1. assumption.
              rewrite <- H5 in A2. simpl in A2. simpl_override_in A2. simpl in A2.
            rewrite <- A2 in A1.
            intro.
            rewrite H3 in A1.
            rewrite Plus.plus_comm in A1.
            simpl in A1.
            apply Le.le_Sn_n in A1.
            assumption.

          (* -- *)           
          rewrite <- H7 in H3.
          simpl in H3.
          apply in_app_iff in H3.        
          destruct H3 as [H3 | H3].
            (* -- *)
            apply in_map_iff in H2.
            destruct H2 as [tn [H21 H22]].
            assert (A1 := message_clock_le_state_clock p ls s2 m'). 
              simpl in A1. depremise A1. split. subst s1. assumption. rewrite <- H5. simpl. assumption.
            subst n. subst n'. rewrite <- H4 in A1. rewrite <- H21 in A1. simpl in A1. rewrite <- H5 in A1. simpl in A1. simpl_override_in A1. simpl in A1.
            subst c.
            subst c'.
            rewrite <- H21. simpl.
            assert (A2 := sem_clock_alg_state_clock p ls s2 n0).
              simpl in A2. depremise A2. 
              subst s1. assumption.
              rewrite <- H5 in A2. simpl in A2. simpl_override_in A2. simpl in A2.
            rewrite <- A2 in A1.
            intro.
            rewrite <- H2 in A1.
            rewrite Plus.plus_comm in A1.
            simpl in A1.
            apply Le.le_Sn_n in A1.
            assumption.          
            (* -- *)
            exfalso.
            apply in_map_iff in H2.
            destruct H2 as [tn [H21 H22]].
            apply in_map_iff in H3.
            destruct H3 as [tn' [H31 H32]].
            rewrite <- H21 in Hn.
            rewrite <- H31 in Hn.
            apply Hn.
            f_equal.
            subst rn.
            subst rn'.
            rewrite <- H21 in Hr.
            rewrite <- H31 in Hr.
            simpl in Hr.
            assumption.


      (* get *)
        apply IHstep_star.
        rewrite <- H5. simpl. rewrite <- H7 in H2. simpl in H2. assumption.
        rewrite <- H5. simpl. rewrite <- H7 in H3. simpl in H3. assumption.

      (* update *)
        apply IHstep_star.
        rewrite <- H6. simpl. rewrite <- H8 in H2. simpl in H2. apply in_app_iff in H2. destruct H2 as [H2 | H2]. apply in_app_iff. left. assumption. apply in_app_iff. right. apply in_cons. assumption.
        rewrite <- H6. simpl. rewrite <- H8 in H3. simpl in H3. apply in_app_iff in H3. destruct H3 as [H3 | H3]. apply in_app_iff. left. assumption. apply in_app_iff. right. apply in_cons. assumption.

      (* fault *)
        apply IHstep_star.
        rewrite <- H5. simpl. rewrite <- H7 in H2. simpl in H2. assumption.
        rewrite <- H5. simpl. rewrite <- H7 in H3. simpl in H3. assumption.

    Qed.

  Lemma messages_no_dup:
    forall p h s,
      step_star (init p) h s
      -> NoDup (messages s).

    Proof.
      intros.
      remember (init p) as s0 eqn: Hs.
      induction H.

      subst s. simpl. constructor.

      inversion H0.

      (* put *)
      simpl.
      apply nodup_app.
      split_all.
      
      depremise IHstep_star. assumption.
      rewrite <- H2 in IHstep_star.
      simpl in IHstep_star.
      assumption.

      apply nodup_map.
        apply nodup_filter.
        apply nodup_nids.
        intros x y _ _ N1.
        intro N2.
        inversion N2.
        contradiction.

      unfold disjoint.
      intro m.
      intros.
      apply in_map_iff in IN2.
      destruct IN2 as [rn [IN21 _]].
      assert (A1 := message_clock_le_state_clock p ls s2 m).
        simpl in A1. depremise A1. split. subst s1. assumption. rewrite <- H2. simpl. assumption.
      rewrite <- IN21 in A1. simpl in A1.
      rewrite <- H2 in A1. simpl in A1. simpl_override_in A1. simpl in A1.
      assert (A2 := sem_clock_alg_state_clock p ls s2 n).
        simpl in A2. depremise A2. subst s1. assumption.
      rewrite <- H2 in A2. simpl in A2. simpl_override_in A2. simpl in A2.
      rewrite <- A2 in A1.
      rewrite Plus.plus_comm in A1.
      simpl in A1.
      apply Le.le_Sn_n in A1.
      assumption.

      (* get *)
      simpl.
      rewrite <- H2 in IHstep_star. simpl in IHstep_star.
      apply IHstep_star. assumption.

      (* update *)
      simpl.
      rewrite <- H3 in IHstep_star. simpl in IHstep_star.
      depremise IHstep_star. assumption.
      apply NoDup_remove_1 in IHstep_star.
      assumption.

      (* fault *)
      simpl.
      rewrite <- H2 in IHstep_star. simpl in IHstep_star.
      apply IHstep_star. assumption.

    Qed.

  Lemma message_clock_ge_one:
    forall p h s m,
      (step_star (init p) h s
       /\ In m (messages s))
      -> msg_clock m >= 1.

    Proof.
      intros.
      destruct H as [H1 H2].
      remember (init p) as s0 eqn: Hs.
      induction H1.

      subst s. simpl in H2. contradiction.

      inversion H.

      (* put *)
      rewrite <- H5 in H2.
      simpl in H2.
      apply in_app_iff in H2.
      destruct H2 as [H2 | H2].

        apply IHstep_star. assumption. 
        rewrite <- H3. simpl. assumption.

        apply in_map_iff in H2.
        destruct H2 as [rn [H21 H22]].
        rewrite <- H21. simpl.
        assert (A1 := Le.le_0_n c).
        assert (A2 := Plus.plus_le_compat_r 0 c 1).
        depremise A2. assumption.
        simpl in A2.
        assumption.

      (* get *)
        apply IHstep_star.
        assumption.
        rewrite <- H5 in H2.
        simpl in H2.
        rewrite <- H3.
        simpl.
        assumption.

      (* update *)
        apply IHstep_star.
        assumption.
        rewrite <- H6 in H2.
        simpl in H2.
        rewrite <- H4.
        simpl.
        apply in_app_iff in H2. destruct H2. apply in_app_iff. left. assumption. apply in_app_iff. right. apply in_cons. assumption.

      (* fault *)
        apply IHstep_star.
        assumption.
        rewrite <- H5 in H2.
        simpl in H2.
        rewrite <- H3.
        simpl.
        assumption.

    Qed.

  Lemma received_lt_message_clock:
    forall p h s m n,
      let st := alg_state (node_states s n) in
      let msn := msg_sender m in
      let mc := msg_clock m in
      let mrn := msg_receiver m in
      (step_star (init p) h s
       /\ In m (messages s)
       /\ mrn = n)
      -> received st msn < mc.

    Proof.
      intros.
      destruct H as [H1 [H2 H3]].
      remember (init p) as s0 eqn: Hi.
      induction H1.

      rewrite Hi in H2. simpl in H2. contradiction.

      simpl in IHstep_star.
      depremise IHstep_star. assumption.

      inversion H.

      (* put *)
        subst l0.
        subst st.
        rewrite <- H6.
        simpl.
        destruct (eq_nat_dec n0 n).
          (* -- *)
          subst n.
          simpl_override.
          simpl.
          destruct (eq_nat_dec n0 msn).
            (* -- *)
            simpl_override.
            exfalso.
            rewrite <- H6 in H2.
            simpl in H2.
            apply in_app_iff in H2.
            destruct H2 as [H2 | H2].
              (* -- *)
              assert (A1 := no_self_message p ls s2 m).
                depremise A1. split. subst s1. assumption. rewrite <- H4. simpl. assumption.
              subst msn.
              subst mrn.
              rewrite e1 in e0.
              contradiction.
              (* -- *)
              apply in_map_iff in H2.
              destruct H2 as [mrn' [H21 H22]].
              apply filter_In in H22.
              destruct H22 as [H221 H222].
              subst mrn. subst msn. subst mc. subst m. simpl in *.
              subst mrn'. rewrite eq_nat_dec_eq in H222. inversion H222.
            (* -- *)
            simpl_override.
            rewrite <- H6 in H2. simpl in H2.
            apply in_app_iff in H2.
            destruct H2 as [H2 | H2].
              (* - *)
              depremise IHstep_star.
                rewrite <- H4. simpl. assumption.
              rewrite <- H4 in IHstep_star.
              simpl in IHstep_star.
              rewrite <- e0 in IHstep_star.
              simpl_override_in IHstep_star.
              simpl in IHstep_star.            
              assumption.
              (* - *)
              apply in_map_iff in H2.
              destruct H2 as [mrn' [H21 H22]].
              apply filter_In in H22.
              destruct H22 as [H221 H222].
              subst mrn. subst msn. subst mc. subst m. simpl in *.
              subst mrn'. rewrite eq_nat_dec_eq in H222. inversion H222.
          (* -- *)
          simpl_override.
          rewrite <- H6 in H2. simpl in H2.
          apply in_app_iff in H2.
          destruct H2 as [H2 | H2].
            (* - *)
            depremise IHstep_star.
              rewrite <- H4. simpl. assumption.
            rewrite <- H4 in IHstep_star.
            simpl in IHstep_star.
            simpl_override_in IHstep_star.
            assumption.
            (* - *)
            apply in_map_iff in H2.
            destruct H2 as [mrn' [H21 H22]].
            apply filter_In in H22.
            destruct H22 as [H221 H222].           
            assert (A1 := received_lt_sent p ls s2 n msn).
              simpl in A1. depremise A1. subst s1. assumption.
            rewrite <- H4 in A1. simpl in A1. simpl_override_in A1. simpl in A1.
            subst msn. subst mc. subst mrn. subst m. simpl in *. simpl_override_in A1. simpl in A1.
            assert (A2 := sem_clock_alg_state_clock p ls s2 n0).
              depremise A2. subst s1. assumption.
            simpl in A2.
            rewrite <- H4 in A2.
            simpl in A2. simpl_override_in A2. simpl in A2.
            rewrite <- A2 in A1. clear A2.
            rewrite Plus.plus_comm. simpl.
            apply Lt.le_lt_n_Sm. assumption.

      (* get *)
        subst st. rewrite <- H6. simpl.
        rewrite <- H6 in H2. simpl in H2.
        depremise IHstep_star.
        rewrite <- H4. simpl. assumption.
        rewrite <- H4 in IHstep_star.
        simpl in IHstep_star.
        destruct (eq_nat_dec n0 n).
        simpl_override. simpl. rewrite e0 in IHstep_star. simpl_override_in IHstep_star. simpl in IHstep_star. assumption.
        simpl_override. simpl. simpl_override_in IHstep_star. assumption.

      (* update *)
        subst st.
        rewrite <- H7.
        simpl.
        destruct (eq_nat_dec n0 n).
          (* -- *)
          simpl_override.
          simpl.
          destruct (eq_nat_dec (sender_node u) msn).
            (* -- *)
            simpl_override.
            subst mc.
            assert (A1 := message_update_node_clock_eq p ls s2 (message n' c' k v u n0 lp)).
              simpl in A1. depremise A1. split. subst s1. assumption. rewrite <- H5. simpl. apply in_app_iff. right. apply in_eq.
            destruct A1 as [A11 A12].
            rewrite <- A12.
            assert (A2 := update_pred p ls s2 (message n' c' k v u n0 lp)).
              depremise A2. split. subst s1. assumption. rewrite <- H5. simpl. apply in_app_iff. right. apply in_eq.
            simpl in A2.
            rewrite <- A11 in A2.
            rewrite <- A12 in A2.
            assert (A3 := Lt.le_or_lt c' 1).
            destruct A3 as [A3 | A3].
              (* -- *)
              assert (A4 := message_clock_ge_one p ls s2 m). 
                depremise A4. split. subst s1. assumption. rewrite <- H7 in H2. simpl in H2. apply in_app_iff in H2. rewrite <- H5. simpl. destruct H2 as [H2 | H2]. apply in_app_iff. left. assumption. apply in_app_iff. right. apply in_cons. assumption.
              assert (A5: c' <= msg_clock m).
                eapply Le.le_trans; eassumption.
              apply Lt.le_lt_or_eq in A5.
              destruct A5 as [A5 | A5].
              assumption.
              exfalso.
              assert (A6 := message_clock_neq p ls s2 (message n' c' k v u n0 lp) m).
                simpl in A6. depremise A6. split_all. 
                subst s1. assumption.
                rewrite <- H5. simpl. apply in_app_iff. right. apply in_eq.
                rewrite <- H5. simpl. rewrite <- H7 in H2. simpl in H2. apply in_app_iff in H2. destruct H2 as [H2 | H2]. apply in_app_iff. left. assumption. apply in_app_iff. right. apply in_cons. assumption.
                subst msn. rewrite <- e1. assumption.
                subst mrn. subst n. assumption.
                intro.
                assert (B1 := messages_no_dup p ls s2). depremise B1. subst s1. assumption.
                rewrite <- H5 in B1. simpl in B1. apply NoDup_remove_2 in B1.
                rewrite H8 in B1.
                rewrite <- H7 in H2. simpl in H2.
                contradiction.
              contradiction.
              depremise A2. assumption.
              unfold guard_method in H4.
              assert (A7 := fold_left_and (NId*Clock) (sender_dep u) (n', pred c')
                                        (fun p => snd p <=? received s (fst p))).
              depremise A7. split; assumption.
              simpl in A7.
              bool_to_prop_in A7.
              depremise IHstep_star.
                rewrite <- H7 in H2. simpl in H2. apply in_app_iff in H2. rewrite <- H5. simpl. destruct H2 as [H2 | H2]. apply in_app_iff. left. assumption. apply in_app_iff. right. apply in_cons. assumption.
              rewrite <- H5 in IHstep_star. simpl in IHstep_star. rewrite e0 in IHstep_star. simpl_override_in IHstep_star. simpl in IHstep_star. rewrite <- e1 in IHstep_star. rewrite <- A11 in IHstep_star.
              assert (A8: pred c' < msg_clock m). eapply Lt.le_lt_trans; eassumption.
              apply Lt.S_pred in A3.
              apply Lt.lt_le_S in A8.
              rewrite <- A3 in A8.
              apply Lt.le_lt_or_eq in A8.
              destruct A8 as [A8 | A8].
              assumption.
              exfalso.
              assert (A9 := message_clock_neq p ls s2 (message n' c' k v u n0 lp) m).
                simpl in A9. depremise A9. split_all. subst s1. assumption.
                rewrite <- H5. simpl. apply in_app_iff. right. apply in_eq.
                rewrite <- H5. simpl. rewrite <- H7 in H2. simpl in H2. apply in_app_iff in H2. destruct H2 as [H2 | H2]. apply in_app_iff. left. assumption. apply in_app_iff. right. apply in_cons. assumption.
                subst msn. rewrite <- e1. assumption.
                subst mrn. subst n. assumption.
                intro.
                assert (B1 := messages_no_dup p ls s2). depremise B1. subst s1. assumption.
                rewrite <- H5 in B1. simpl in B1. apply NoDup_remove_2 in B1.
                rewrite H8 in B1.
                rewrite <- H7 in H2. simpl in H2.
                contradiction.
              contradiction.            

            (* -- *)
            simpl_override.            
            rewrite <- H7 in H2. simpl in H2. apply in_app_iff in H2. 
            depremise IHstep_star. rewrite <- H5. simpl. destruct H2 as [H2 | H2]. apply in_app_iff. left. assumption. apply in_app_iff. right. apply in_cons. assumption.
            rewrite <- H5 in IHstep_star. simpl in IHstep_star. rewrite e0 in IHstep_star. simpl_override_in IHstep_star. simpl in IHstep_star.
            assumption.

          (* -- *)
          simpl_override.
          rewrite <- H7 in H2. simpl in H2.
          depremise IHstep_star.
          rewrite <- H5. simpl. 
          apply in_app_iff in H2. destruct H2 as [H2 | H2]. 
          apply in_app_iff. left. assumption.
          apply in_app_iff. right. apply in_cons. assumption.
          rewrite <- H5 in IHstep_star.
          simpl in IHstep_star.
          simpl_override_in IHstep_star.
          assumption.


      (* fault *)
        subst st. rewrite <- H6. simpl.
        rewrite <- H6 in H2. simpl in H2.
        depremise IHstep_star.
        rewrite <- H4. simpl. assumption.
        rewrite <- H4 in IHstep_star.
        simpl in IHstep_star.
        destruct (eq_nat_dec n0 n).
        simpl_override. rewrite e0 in IHstep_star. simpl_override_in IHstep_star. assumption.
        simpl_override. simpl_override_in IHstep_star. assumption.


    Qed.


  Lemma received_plus_one_eq_message_clock:
    forall p h s l s',
      (step_star (init p) h s
       /\ step s l s'
       /\ label_is_update l) ->
      (let n := label_node l in
       let n' := label_orig_node l in       
       (received (alg_state (node_states s n)) n') + 1) =
      msg_clock (label_message l).

    Proof.
      intros.
      simpl.
      destruct H as [N1 [N2 N3]].
      destruct l; simpl in *; try contradiction; clear N3.

      assert (A0 := message_update_node_clock_eq).
        specex A0.
        simpl in A0.
        depremise A0.
        split_all.
        eassumption.
        inversion N2.
        simpl.
        apply in_app_iff.
        right.
        apply in_eq.
        destruct A0 as [A01 A02].

      assert (A1 := update_sender_clock).
        specex_deprem A1. split_all.
        eassumption.
        eassumption.
        simpl. apply I.
        simpl in A1.
      
      assert (A2 := received_lt_message_clock).
        specex A2. simpl in A2. depremise A2. split_all.
        eassumption. 
        inversion N2. simpl. apply in_app_iff. right. apply in_eq.
        inversion N2. simpl. reflexivity.

      rewrite <- A02 in A1.

      assert (A3: msg_sender m = n0).
        inversion N2.
        simpl.
        reflexivity.
      
      rewrite A3 in A2.
      clear A01 A02 A3.

      apply le_lt_eq_dec in A1.
      destruct A1.
      exfalso.
      rewrite Plus.plus_comm in l.
      simpl in l.
      apply lt_n_Sm_le in l.
      apply lt_not_le in A2. apply A2. assumption.
      symmetry.
      assumption.

    Qed.



  Lemma rec_inc:
    forall p h s1 h' s2 n n',
      (step_star (init p) h s1
      /\ step_star s1 h' s2)
      -> received (alg_state (node_states s1 n)) n' <= 
         received (alg_state (node_states s2 n)) n'.

    Proof.
      intros.
      destruct H as [H1 H2].
      induction H2.

      apply Le.le_refl.

      depremise IHstep_star. assumption.
      assert (A1: received (alg_state (node_states s2 n)) n' <= received (alg_state (node_states s3 n)) n').
      clear IHstep_star.

      inversion H.

      (* put *)
        simpl.
        destruct (eq_nat_dec n0 n).

          subst n.
          simpl_override.
          simpl.
          simpl_override.
          simpl.
          destruct (eq_nat_dec n0 n').

            subst n'.
            simpl_override. 
            assert (A := rec_eq_clock p (h++ls) s2 n0).
              simpl in A. depremise A. apply step_star_app. exists s1. split; assumption.
            rewrite <- H3 in A. simpl in A. simpl_override_in A. simpl in A.
            rewrite A.
            rewrite Plus.plus_comm.
            simpl.
            apply le_S.
            apply Le.le_refl.

            simpl_override.
            apply Le.le_refl.

          simpl.
          simpl_override.
          simpl_override.
          reflexivity.

      (* get *)
        simpl.
        destruct (eq_nat_dec n0 n).
        
          subst n.
          simpl_override.
          simpl.
          simpl_override.
          simpl.
          apply Le.le_refl.

          simpl_override.
          simpl.
          simpl_override.
          apply Le.le_refl.         

      (* update *)
        simpl.
        destruct (eq_nat_dec n0 n).
        
          subst n.
          simpl_override.
          simpl.
          simpl_override.
          simpl.
          destruct (eq_nat_dec (sender_node u) n').
          subst n'.
          simpl_override.
          assert (A1 := message_update_node_clock_eq p (h++ls) s2 (message n'0 c' k v u n0 lp)).
            simpl in A1. depremise A1. split_all.
            apply step_star_app. exists s1. split; assumption.
            subst s2. simpl. apply in_app_iff. right. apply in_eq.
          destruct A1 as [A11 A12].
          rewrite <- A11.
          rewrite <- A12.
          assert (A2 := received_lt_message_clock p (h++ls) s2 (message n'0 c' k v u n0 lp) n0).
            simpl in A2. depremise A2. split_all.
            apply step_star_app. exists s1. split; assumption.
            subst s2. simpl. apply in_app_iff. right. apply in_eq.
            reflexivity.
          rewrite <- H4 in A2.
          simpl in A2.
          simpl_override_in A2.
          simpl in A2.
          apply Lt.lt_le_weak.
          assumption.
          
          simpl_override.
          apply Le.le_refl.

          simpl_override.
          simpl.
          simpl_override.
          apply Le.le_refl.


      (* fault *)
        simpl.
        destruct (eq_nat_dec n0 n).
        
          subst n.
          simpl_override.
          simpl_override.
          apply Le.le_refl.

          simpl_override.
          simpl_override.
          apply Le.le_refl.         

      eapply Le.le_trans; eassumption.

    Qed.


  Lemma clock_self_lte_received:
    forall p h s l,
      let n := label_node l in
      (step_star (init p) h s
       /\ label_is_put l
       /\ In l h)
      -> label_clock l ≤ received (alg_state (node_states s n)) n.

    Proof.
      intros.
      destruct H as [H1 [H2 H3]].

      assert (A1 := in_exec h (init p) s l).
        depremise A1. split; assumption.        
        destruct A1 as [h1 [s1 [s2 [h2 [A11 [A12 [A13 A14]]]]]]].

      assert (A2: label_clock l = clock_state (node_states s2 n)).
        destruct l; simpl in *; try contradiction; clear H2.
        inversion A13.
        simpl.
        subst n.
        simpl_override.
        simpl.
        reflexivity.

      assert (A3 := sem_clock_alg_state_clock p (h1++[l]) s2 n).
        simpl in A3. depremise A3. apply step_star_app_one. exists s1. split; assumption.
        
      assert (A4 := rec_eq_clock p (h1++[l]) s2 n).
        simpl in A4. depremise A4. apply step_star_app_one. exists s1. split; assumption.
            
      assert (A5 := rec_inc p (h1++[l]) s2 h2 s n n).
        depremise A5. split. apply step_star_app_one. exists s1. split; assumption. assumption.

      rewrite A2. rewrite A3. rewrite <- A4. assumption.

    Qed.


  Lemma store_received:
    forall p h s n k,
      let st := alg_state (node_states s n) in
      let en := entry_node (store st k) in
      let ec := entry_clock (store st k) in
      step_star (init p) h s
      -> received st en >= ec.

    Proof.
      intros.
      remember (init p) as s0 eqn: Hs.
      induction H.

      subst st. subst en. subst ec. subst s. simpl. apply Le.le_refl.

      simpl in IHstep_star.
      depremise IHstep_star.
      assumption.

      inversion H0.

      (* put *)
      subst st. subst en. subst ec.
      rewrite <- H4.
      simpl.
      destruct (eq_nat_dec n0 n).
      
        subst n.
        simpl_override.
        simpl.

        destruct (eq_nat_dec k0 k).

          subst k.
          simpl_override.
          simpl.
          simpl_override.
          apply Le.le_refl.

          simpl_override.

          (*
          assert (B1: (entry_node (override (store s) k0 (entry (inst_val n0 (c + 1) v) n0 (clock s + 1)) k)) = (entry_node (store s k))).
            simpl_override. reflexivity.
          rewrite B1. clear B1.
          *)
    
          unfold override at 2.
          unfold override at 2.
          rewrite eq_nat_dec_neq.

          rewrite <- H2 in IHstep_star.
          simpl in IHstep_star.

          simpl_override_in IHstep_star.
          simpl in IHstep_star.

          destruct (eq_nat_dec n0 (entry_node (store s k))). 

            simpl_override. rewrite <- e0 in IHstep_star.
            assert (B2 := rec_eq_clock p ls s2 n0).
            simpl in B2. depremise B2. 
            subst s1. assumption.
            rewrite <- H2 in B2. simpl in B2. simpl_override_in B2. simpl in B2.
            rewrite B2 in IHstep_star. clear B2.
            rewrite Plus.plus_comm.
            simpl.
            apply le_S.
            assumption.

            simpl_override.
            assumption.

          apply not_eq_sym. assumption.


        assert (B1: override nss n0 (node_state p0 s' (c + 1)) n = nss n).
          simpl_override. reflexivity.
        rewrite B1. clear B1.
        rewrite <- H2 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        assumption.

      (* get *)
        subst st. subst en. subst ec.
        rewrite <- H4. simpl.
        destruct (eq_nat_dec n0 n).
        
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
          

      (* update *)
        subst st. subst en. subst ec.
        rewrite <- H5. simpl.
        destruct (eq_nat_dec n0 n).

          (* -- *)
          subst n.
          simpl_override.
          simpl.
          destruct (eq_nat_dec k0 k).

            subst k.
            simpl_override.
            simpl.
            simpl_override.
            apply Le.le_refl.
    
            unfold override at 2.
            unfold override at 2.
            rewrite eq_nat_dec_neq.

            (*
            assert (B1: override (store s) k0 (entry (inst_val n' c' v) (sender_node u) (sender_clock u)) k = store s k).
              simpl_override. reflexivity.
            rewrite B1. clear B1.
            *)

            destruct (eq_nat_dec (sender_node u) (entry_node (store s k))).

              (* -- *)
              simpl_override.
              assert (C1 := received_lt_message_clock p ls s2 (message n' c' k0 v u n0 lp) n0).
                simpl in C1. depremise C1. split_all.
                subst s1. assumption.
                rewrite <- H3. simpl. apply in_app_iff. right. apply in_eq.
                reflexivity.
              rewrite <- H3 in C1. simpl in C1. simpl_override_in C1. simpl in C1.
              
              rewrite <- H3 in IHstep_star.
              simpl in IHstep_star.
              simpl_override_in IHstep_star.
              simpl in IHstep_star.
              
              assert (C2 := message_update_node_clock_eq p ls s2 (message n' c' k0 v u n0 lp)).
                simpl in C2. depremise C2. split_all.
                subst s1. assumption.
                rewrite <- H3. simpl. apply in_app_iff. right. apply in_eq.
                destruct C2 as [C21 C22].
              
              rewrite <- e0 in IHstep_star.
              rewrite <- C21 in IHstep_star.
              rewrite C22 in C1.

              apply Lt.lt_le_weak.
              eapply Gt.gt_le_trans; eassumption.

              (* -- *)
              simpl_override.
              rewrite <- H3 in IHstep_star.
              simpl in IHstep_star.
              simpl_override_in IHstep_star.
              simpl in IHstep_star.
              assumption.

            apply not_eq_sym. assumption.

          (* -- *)
          simpl_override.
          rewrite <- H3 in IHstep_star.
          simpl in IHstep_star.
          simpl_override_in IHstep_star.
          assumption.

      (* fault *)
        subst st. subst en. subst ec.
        rewrite <- H4. simpl.
        destruct (eq_nat_dec n0 n).
        
          subst n.
          simpl_override.
          simpl.
          rewrite <- H2 in IHstep_star.
          simpl in IHstep_star.
          simpl_override_in IHstep_star.
          assumption.

          simpl_override.
          rewrite <- H2 in IHstep_star.
          simpl in IHstep_star.
          simpl_override_in IHstep_star.
          assumption.

    Qed.

  Lemma dep_received:
    forall p h s n n' c',
      let st := alg_state (node_states s n) in
      (step_star (init p) h s
       /\ In (n', c') (dep st))
      -> received st n' >= c'.

    Proof.
      intros.
      destruct H as [H1 H2].
      remember (init p) as s0 eqn: Hs.
      induction H1.

      subst st. subst s. simpl in H2. contradiction.

      simpl in IHstep_star. depremise IHstep_star. assumption.
      
      inversion H.

      (* put *)
      subst st.
      rewrite <- H5.
      simpl.
      destruct (eq_nat_dec n0 n).

        subst n.
        simpl_override.
        simpl.
        rewrite <- H5 in H2.
        simpl in H2.
        simpl_override_in H2.
        simpl in H2.
        destruct H2 as [H2 | H2]; try contradiction.
        inversion H2.
        simpl_override.
        apply Le.le_refl.

        simpl_override.
        depremise IHstep_star.
        rewrite <- H3.
        simpl.
        simpl_override.
        rewrite <- H5 in H2.
        simpl in H2.
        simpl_override_in H2.
        assumption.
        rewrite <- H3 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        assumption.

      (* get *)
      subst st.
      rewrite <- H5.
      simpl.
      destruct (eq_nat_dec n0 n).

        (* -- *)
        subst n.
        simpl_override.
        simpl.
        rewrite <- H5 in H2.
        simpl in H2.
        simpl_override_in H2.
        simpl in H2.
        destruct (entry_node (store s k) <>? init_nid).

          (* -- *)
          simpl in H2. destruct H2 as [H2 | H2].
          inversion H2.
          assert (A1 := store_received p ls s2 n0 k).
            simpl in A1. depremise A1.
            subst s1. assumption.
          rewrite <- H3 in A1.
          simpl in A1.
          simpl_override_in A1.
          simpl in A1.
          assumption.

          depremise IHstep_star.
          rewrite <- H3.
          simpl.
          simpl_override.
          simpl.
          assumption.
          rewrite <- H3 in IHstep_star.
          simpl in IHstep_star.
          simpl_override_in IHstep_star.
          simpl in IHstep_star.
          assumption.

          (* -- *)
          depremise IHstep_star.
          rewrite <- H3.
          simpl.
          simpl_override.
          simpl.
          assumption.
          rewrite <- H3 in IHstep_star.
          simpl in IHstep_star.
          simpl_override_in IHstep_star.
          simpl in IHstep_star.
          assumption.


        (* -- *)
        simpl_override.
        depremise IHstep_star.
        rewrite <- H3.
        simpl.
        simpl_override.
        rewrite <- H5 in H2.
        simpl in H2.
        simpl_override_in H2.
        assumption.
        rewrite <- H3 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        assumption.
      
      (* update *)
      subst st.
      rewrite <- H6.
      simpl.
      destruct (eq_nat_dec n0 n).

        subst n.
        simpl_override.
        simpl.
        depremise IHstep_star.
        rewrite <- H4.
        simpl.
        simpl_override.
        simpl.
        rewrite <- H6 in H2.
        simpl in H2.
        simpl_override_in H2.
        simpl in H2.
        assumption.
        rewrite <- H4 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        simpl in IHstep_star.
        destruct (eq_nat_dec (sender_node u) n').

          (* -- *)
          simpl_override.
          assert (B1 := received_lt_message_clock p ls s2 (message n'0 c'0 k v u n0 lp) n0).
            simpl in B1. depremise B1. split_all.
            subst s1. assumption.
            rewrite <- H4. simpl. apply in_app_iff. right. apply in_eq. reflexivity.
          rewrite <- H4 in B1.
          simpl in B1.
          simpl_override_in B1.
          simpl in B1.
          assert (B2 := message_update_node_clock_eq p ls s2 (message n'0 c'0 k v u n0 lp)).
            simpl in B2. depremise B2. split_all.
            subst s1. assumption.
            rewrite <- H4. simpl. apply in_app_iff. right. apply in_eq.
            destruct B2 as [B21 B22].
          rewrite B21 in B1. rewrite e0 in B1.
          rewrite B22 in B1.
          clear B21 B22.
          apply Lt.lt_le_weak.
          eapply Gt.gt_le_trans; eassumption.

          (* -- *)
          simpl_override.
          assumption.

        simpl_override.
        rewrite <- H4 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        apply IHstep_star.
        rewrite <- H6 in H2.
        simpl in H2.
        simpl_override_in H2.
        assumption.

      (* fault *)
      subst st.
      rewrite <- H5.
      simpl.
      destruct (eq_nat_dec n0 n).

        subst n.
        simpl_override.
        rewrite <- H5 in H2.
        simpl in H2.
        simpl_override_in H2.
        depremise IHstep_star.
        rewrite <- H3.
        simpl.
        simpl_override.
        assumption.
        rewrite <- H3 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        assumption.

        simpl_override.
        rewrite <- H5 in H2.
        simpl in H2.
        simpl_override_in H2.
        depremise IHstep_star.
        rewrite <- H3.
        simpl.
        simpl_override.
        assumption.
        rewrite <- H3 in IHstep_star.
        simpl in IHstep_star.
        simpl_override_in IHstep_star.
        assumption.

    Qed.

  Lemma cause_received_received:
    forall p h s l l' n'',
      let rec := received (alg_state (node_states s n'')) in
      let n := label_node l in
      let c := label_clock l in
      let n' := label_node l' in
      let c' := label_clock l' in
      (step_star (init p) h s
       /\ label_is_put l
       /\ label_is_put l'
       /\ cause h l l'
       /\ c' <= rec n'
       /\ In n'' nids)
      ->  c <= rec n.

    Proof.
      intros.
      destruct H as [H1 [H2 [H3 [H4 [H5 Hnid]]]]].
      remember (init p) as s0 eqn: Hi.
      subst c. subst c'. subst n. subst n'. subst rec.
      generalize dependent l'.
      generalize dependent l.
      induction H1 as [s | s1 h s2 lc s3 H11 H12 H13].

      (* base case *)
      intros.
      apply cause_in in H4.  
      open_conjs. unfold In in H. contradiction.

      (* inductive case *)
      intros.
      depremise H12. assumption.

      assert (A1 := H4).
        apply cause_in in A1. destruct A1 as [_ A1].

      assert (A2 := eq_label_dec p (h ++ [lc]) s3 lc l').
        depremise A2. split_all.
        apply step_star_app_one. exists s2. subst s1. split; assumption.
        apply in_app_iff. right. apply in_eq. 
        assumption.
      
      destruct A2 as [A2 | A2].

        (* the same label *)
        subst lc.
        clear A1.
        remember (label_node l) as n eqn: Hn.
        remember (label_clock l) as c eqn: Hc.
        remember (label_node l') as n' eqn: Hn'.
        remember (label_clock l') as c' eqn: Hc'.

        destruct (eq_nat_dec n'' n').
        
        (* -- *)
        assert (A3 := cause_dep p (h++[l']) s3 l l').
          depremise A3.
          split_all.
          apply step_star_app_one. exists s2. subst s1. split; assumption.
          assumption.
          assumption.

        destruct A3 as [A3 | A3].

          (* -- *)
          clear H12.
          subst n''.
          assert (A4 := dep_received p h s2 n' n c).
            simpl in A4. depremise A4. split_all.
            subst s1. assumption.
            assert (B1: label_dep l' = dep (alg_state (node_states s2 n'))).
              destruct l'; simpl in *; try contradiction.
              inversion H13. simpl. simpl_override. simpl. reflexivity.
            rewrite <- B1. 
            subst n. subst c.
            assumption.

          assert (B1 := rec_inc p h s2 [l'] s3 n' n).
            depremise B1. split_all.
            subst s1. assumption.
            apply step_star_one. assumption.

          eapply Le.le_trans; eassumption.

          (* -- *)
          destruct A3 as [lm [A31 [A32 [A33 A34]]]].
          subst n''.
          remember (label_node lm) as nm eqn: Hnm.
          remember (label_clock lm) as cm eqn: Hcm.

          assert (A4 := dep_received p h s2 n' nm cm).
            simpl in A4. depremise A4. split_all.
            subst s1. assumption.
            assert (B1: label_dep l' = dep (alg_state (node_states s2 n'))).
              destruct l'; simpl in *; try contradiction.
              inversion H13. simpl. simpl_override. simpl. reflexivity.
            rewrite <- B1. 
            assumption.

          specialize (H12 l). depremise H12. assumption.
          specialize (H12 lm). depremise H12. assumption.
          depremise H12.
          assert (A5 := prec_pre_in p h s3 l' lm).
            depremise A5. split. apply step_star_app_one. exists s2. subst s1. split; assumption.
            assumption.
          eapply cause_prefix_history_one.
            split_all. 
            subst s1. apply step_star_app_one. exists s2. split; eassumption.
            assumption.
            assumption.
          depremise H12. subst nm. subst cm. assumption.
          subst c. subst n.

          assert (B1 := rec_inc p h s2 [l'] s3 n' (label_node l)).
            depremise B1. split_all.
            subst s1. assumption.
            apply step_star_one. assumption.

          eapply Le.le_trans; eassumption.

          (* -- *)
            exfalso.

            destruct l'; simpl in *; try contradiction.
            inversion H13.
            simpl in *.

            assert (B1: In (message n2 (c1 + 1) k v u0 n'' l1) (messages s3)).
              rewrite <- H1. simpl. apply in_app_iff. right. apply in_map_iff.
              exists n''. split. reflexivity.
              apply filter_In. split. assumption.
              rewrite <- Hn'.
              rewrite eq_nat_dec_neq.
              reflexivity.
              apply not_eq_sym. assumption.

            assert (B2 := received_lt_message_clock p (h++[(put_label n1 n2 c0 k v a a0 u)]) s3 (message n2 (c1 + 1) k v u0 n'' l1) n'').
              simpl in B2. depremise B2. split_all.
              apply step_star_app_one. exists s2. subst s1. split; assumption.
              rewrite <- H1. simpl. apply in_app_iff. right. apply in_map_iff. exists n''. split. reflexivity. apply filter_In. split. assumption. rewrite <- Hn'. rewrite eq_nat_dec_neq. reflexivity.
              apply not_eq_sym. assumption.
              reflexivity.
            rewrite <- H1 in B2. simpl in B2. rewrite <- Hn' in B2. simpl_override_in B2.
            subst c'.
            subst c0.
            rewrite <- H1 in H5. simpl in H5. rewrite <- Hn' in H5. simpl_override_in H5.
            apply Lt.lt_not_le in B2.
            contradiction.                 

        (* a different label *)

        assert (A3 := cause_pre_cause p h s3 lc l l').
          depremise A3. split_all. apply step_star_app_one. exists s2. subst s1. split; assumption.
          assumption.
          assumption.

        apply in_app_iff in A1. simpl in A1. destruct A1 as [A1 | [A1 | A1]]; try contradiction.

        assert (A4 := rec_inc p h s2 [lc] s3 n'' (label_node l)).
          depremise A4. split. subst s1. assumption. apply step_star_one. assumption.

        destruct (eq_nat_dec (label_node lc) n'').

          (* lc affects n'' *)
            destruct lc.
            
            (* put *)
              specialize (H12 l). depremise H12. assumption.
              specialize (H12 l').  depremise H12. assumption. depremise H12. assumption.

              destruct (eq_nat_dec n'' (label_node l')).
                
                (* changing rec of n'. *)
                  clear H5.
                  subst n''. simpl in *.
                  subst n0.
                  assert (A5 := clock_self_lte_received p h s2 l').
                    simpl in A5. depremise A5. split_all.
                    subst s1. assumption. assumption. assumption.
                  depremise H12. assumption.
                  eapply Le.le_trans; eassumption.
                  
                (* not changing rec of n'. *)
                  assert (A5: received (alg_state (node_states s2 n'')) (label_node l') = received (alg_state (node_states s3 n'')) (label_node l')).
                  inversion H13. simpl. subst r. subst l1. subst n''. simpl. simpl_override. simpl_override. simpl. rewrite H6. subst n0. simpl_override. subst a. reflexivity.

                  rewrite A5 in H12.
                  depremise H12. assumption.
                  eapply Le.le_trans; eassumption.            
                   
            (* get *)
              specialize (H12 l). depremise H12. assumption.
              specialize (H12 l').  depremise H12. assumption. depremise H12. assumption.

              assert (A5: received (alg_state (node_states s2 n'')) (label_node l') = received (alg_state (node_states s3 n'')) (label_node l')).
              inversion H13. simpl. subst n1. subst n''. simpl. simpl_override. simpl_override. simpl. subst a. reflexivity.

              rewrite A5 in H12.
              depremise H12. assumption.
              eapply Le.le_trans; eassumption.            

            (* update *)
              destruct (eq_nat_dec n0 (label_node l')).

                (* the orig of the message is l' *)

                  apply Lt.le_lt_or_eq in H5.
                  destruct H5 as [H5 | H5].

                  (* receiving a message after l' *)
                    specialize (H12 l). depremise H12. assumption.
                    specialize (H12 l').  depremise H12. assumption. depremise H12. assumption.

                    (*
                      new c <= pre rec + 1
                      l l' < new c
                      ->
                      l l' < pre rec + 1
                      l l' <= pre rec
                    *)

                    subst n0.                    
                    assert (A5: received (alg_state (node_states s3 n'')) (label_node l') <=
                                S (received (alg_state (node_states s2 n'')) (label_node l'))).
                      inversion H13. 
                      subst s'1.
                      subst s'2.
                      subst s'3.
                      subst s'4.
                      subst s'5.
                      subst c.
                      subst n1.
                      subst k.
                      subst v.
                      subst a.
                      simpl. subst n''. simpl. simpl_override. simpl_override. simpl.
                      assert (B1 := message_update_node_clock_eq p h s2 (message n' c' k0 v0 u n0 lp)).
                        simpl in B1. depremise B1. split_all. subst s1. assumption. rewrite <- H1. simpl. apply in_app_iff. right. apply in_eq.
                      destruct B1 as [B11 B12]. rewrite <- B11. subst n'. simpl_override. 
                                            
                      assert (B2 := update_sender_clock p h s2 (update_label n (label_node l') c' n0 k0 v0 s m a0) s3). 
                        simpl in B2. depremise B2. split_all. subst s1. assumption. assumption. apply I.
                        rewrite <- H1 in B2. simpl in B2. simpl_override_in B2. simpl in B2. subst m. simpl in B2.
                        rewrite Plus.plus_comm in B2. simpl in B2. assumption.

                    assert (A6: label_clock l' < S (received (alg_state (node_states s2 n'')) (label_node l'))).
                      eapply Lt.lt_le_trans; eassumption. 
                    apply Lt.lt_n_Sm_le in A6.
                    depremise H12. assumption.
                    eapply Le.le_trans; eassumption.            
                  
                  (* receiving l' *)
                    assert (A5 := cause_dep p h s2 l l').
                      depremise A5. subst s1. split_all; assumption.
                      destruct A5 as [A5 | A5].

                      (* directly in d *)
                      
                        clear H12.

                        remember (update_label n n0 c n1 k v a m a0) as lc eqn: Hl.
                                            
                        assert (B1 := msg_update_label p h s2 m).
                          depremise B1. split. subst s1. assumption. subst lc. inversion H13. subst s2. simpl. apply in_app_iff. right. apply in_eq.
                          simpl in B1. destruct B1 as [B11 [B12 [B13 [B14 [B15 _]]]]].

                        assert (B2: sender_node (msg_update m) = label_node l').
                          subst lc. inversion H13. simpl. rewrite <- e0. 
                          assert (C1 := message_update_node_clock_eq p h s2 (message n' c' k0 v0 u n2 lp)).
                            simpl in C1. depremise C1. split. subst s1. assumption. subst s2. simpl. apply in_app_iff. right. apply in_eq.
                          destruct C1 as [C1 _].
                          subst n'.
                          symmetry. assumption.
                        
                        assert (B3: sender_clock (msg_update m) = label_clock l').
                          rewrite H5. subst lc. inversion H13. simpl. subst n''. simpl. simpl_override. simpl.
                          assert (C1 := message_update_node_clock_eq p h s2 (message n' c' k0 v0 u n2 lp)).
                            simpl in C1. depremise C1. split. subst s1. assumption. subst s2. simpl. apply in_app_iff. right. apply in_eq.
                          destruct C1 as [C11 C12].
                          rewrite <- C11.
                          rewrite H0.
                          rewrite e0.
                          simpl_override.
                          reflexivity.

                        rewrite B2 in B13. clear B2.
                        rewrite B3 in B14. clear B3.
                       
                        assert (B4 := put_unique p h s2 (msg_label m) l').
                          depremise B4. subst s1. split_all; assumption.
                        rewrite B4 in *; clear B4. clear B11 B12 B13 B14.
                        rewrite B15 in A5; clear B15.

                        assert (B5: label_clock l ≤ received (alg_state (node_states s2 n'')) (label_node l)).
                          subst lc. inversion H13. simpl in *. subst n''. simpl in *. simpl_override. simpl. subst a. 

                          unfold guard_method in H17.
                          assert (A:= fold_left_and (NId*Clock) (sender_dep u) 
                                                    (label_node l, label_clock l)
                                                    (fun p => snd p <=? received s (fst p))).
                            depremise A. split. assumption.
                            subst m. simpl in *. assumption.
                          simpl in A.
                          bool_to_prop_in A.
                          assumption.

                        eapply Le.le_trans; eassumption.
                        
 
                      (* indirectly in d *)
                        destruct A5 as [l'' [A51 [A52 [A53 A54]]]].

                        specialize (H12 l). depremise H12. assumption.
                        specialize (H12 l''). depremise H12. assumption. depremise H12. assumption.

                        remember (update_label n n0 c n1 k v a m a0) as lc eqn: Hl.
                                            
                        assert (B1 := msg_update_label p h s2 m).
                          depremise B1. split. subst s1. assumption. subst lc. inversion H13. subst s2. simpl. apply in_app_iff. right. apply in_eq.
                          simpl in B1. destruct B1 as [B11 [B12 [B13 [B14 [B15 _]]]]].

                        assert (B2: sender_node (msg_update m) = label_node l').
                          subst lc. inversion H13. simpl. rewrite <- e0. 
                          assert (C1 := message_update_node_clock_eq p h s2 (message n' c' k0 v0 u n2 lp)).
                            simpl in C1. depremise C1. split. subst s1. assumption. subst s2. simpl. apply in_app_iff. right. apply in_eq.
                          destruct C1 as [C11 C12].
                          subst n'.
                          symmetry. assumption.
                        
                        assert (B3: sender_clock (msg_update m) = label_clock l').
                          rewrite H5. subst lc. inversion H13. simpl. subst n''. simpl. simpl_override. simpl.
                          assert (C1 := message_update_node_clock_eq p h s2 (message n' c' k0 v0 u n2 lp)).
                            simpl in C1. depremise C1. split. subst s1. assumption. subst s2. simpl. apply in_app_iff. right. apply in_eq.
                          destruct C1 as [C11 C12].
                          rewrite <- C11.
                          rewrite H0.
                          rewrite e0.
                          simpl_override.
                          reflexivity.

                        rewrite B2 in B13. clear B2.
                        rewrite B3 in B14. clear B3.
                       
                        assert (B4 := put_unique p h s2 (msg_label m) l').
                          depremise B4. subst s1. split_all; assumption.
                        rewrite B4 in *; clear B4. clear B11 B12 B13 B14.
                        rewrite B15 in A53; clear B15.

                        assert (B5: label_clock l'' ≤ received (alg_state (node_states s2 n'')) (label_node l'')).
                          subst lc. inversion H13. simpl in *. subst n''. simpl in *. simpl_override. simpl. subst a. 

                          unfold guard_method in H18.
                          assert (A:= fold_left_and (NId*Clock) (sender_dep u) 
                                                    (label_node l'', label_clock l'')
                                                    (fun p => snd p <=? received s (fst p))).
                            depremise A. split. assumption.
                            subst m. simpl in *. assumption.
                          simpl in A.
                          bool_to_prop_in A.
                          assumption.

                        depremise H12. assumption.
                        eapply Le.le_trans; eassumption.

                (* the orig of the message is not l' *)
                  specialize (H12 l). depremise H12. assumption.
                  specialize (H12 l').  depremise H12. assumption. depremise H12. assumption.

                  assert (A5: received (alg_state (node_states s2 n'')) (label_node l') = received (alg_state (node_states s3 n'')) (label_node l')).
                  inversion H13. simpl. subst n1. subst n''. simpl. simpl_override. simpl_override. simpl. 
                  assert (B1 := message_update_node_clock_eq p h s2 (message n' c' k0 v0 u n3 lp)).
                    simpl in B1. depremise B1. split_all. subst s1. assumption. rewrite <- H1. simpl. apply in_app_iff. right. apply in_eq.
                    destruct B1 as [B11 B12]. rewrite <- B11. subst n'. simpl_override. subst a. reflexivity.

                  rewrite A5 in H12.
                  depremise H12. assumption.
                  eapply Le.le_trans; eassumption.            

            (* fault *)
              specialize (H12 l). depremise H12. assumption.
              specialize (H12 l').  depremise H12. assumption. depremise H12. assumption.

              assert (A5: received (alg_state (node_states s2 n'')) (label_node l') = received (alg_state (node_states s3 n'')) (label_node l')).
              inversion H13. simpl. subst n1. subst n''. simpl. simpl_override. simpl_override. simpl. subst a. reflexivity.

              rewrite A5 in H12.
              depremise H12. assumption.
              eapply Le.le_trans; eassumption.            
                   

          (* lc does not affect n'' *)
            specialize (H12 l). depremise H12. assumption.
            specialize (H12 l').  depremise H12. assumption. depremise H12. assumption.

            assert (A5: received (alg_state (node_states s2 n'')) (label_node l') = received (alg_state (node_states s3 n'')) (label_node l')).
            destruct lc; inversion H13; simpl; simpl_override; simpl_override; reflexivity.
            rewrite A5 in H12.
            depremise H12. assumption.
            eapply Le.le_trans; eassumption.            

    Qed.

  (* Obligations *)

  Lemma ExecToSeqExec':
    forall p h s,
      CExec.StepStar.step_star (CExec.init p) h s
      -> exists h' s',
           SExec.StepStar.step_star (SExec.init) h' s'
           /\ h' = CExec.eff_hist h
           /\ forall n k, entry_val (store (CExec.alg_state (CExec.node_states s n)) k) = s' n k.

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
      apply SExec.fault_step.

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
    received.
    

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
      assert (A := rec_eq_clock).
      specex A.
      simpl in A.
      depremise A.
      eassumption.
      instantiate (1 := n1) in A.
      subv_in s A.
      subv_in n A.
      simpl_override_in A.
      symmetry.
      assumption.

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
      split_all.

      assert (A := received_plus_one_eq_message_clock).
        specex_deprem A. split_all.
        eassumption.
        eassumption.
        simpl. apply I.
        simpl in A.
        subv_in s A.
        subv_in m A.
        subv_in n2 A.
        simpl_override_in A.
      rewrite Plus.plus_comm in A.
      simpl in A.
      assumption.
      
      assert (A := message_update_node_clock_eq).
        specex A. simpl in A.
        depremise A. split_all.
        eassumption. 
        subv s. apply in_app_iff. right. apply in_eq.
        simpl in A.
        destruct A as [A1 A2].

      rewrite <- A1.
      rewrite <- A2.
      subv n1.
      simpl_override.
      reflexivity.

      intros.
      assert (A := message_update_node_clock_eq).
        specex A. simpl in A.
        depremise A. split_all.
        eassumption. 
        subv s. apply in_app_iff. right. apply in_eq.
        simpl in A.
        destruct A as [A1 A2].

      rewrite <- A1.
      rewrite <- A2.
      subst n2.
      rewrite <- H2 in H5.
      simpl_override.
      reflexivity.
      
      
    Qed.


  Lemma cause_rec:
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

    Proof.
         intros.
         open_conjs.
         destruct l'; simpl in *; try contradiction.
         inversion H0. 
         subst s'0.
         subst s'1.
         subst s'2.
         subst s'3.
         subst s'4.
         subst s'5.
         subst n'0.
         subst k0.
         subst v0.
         subst n3.
         subst a.
         subst c0.
         remember (update_label n0 n1 c' n2 k v s m a0) as l' eqn: L.

         assert (A2 := cause_dep p (h++[l']) s2 l lp).
           depremise A2. split_all.
           apply step_star_app_one. exists s1. split; assumption.
           assumption.
           apply cause_ext_cause.
           assumption.

         destruct A2 as [A2 | A2].
         
           (* -- *)

             unfold guard_method in H16.
             assert (A3 := fold_left_and (NId*Clock) (sender_dep u)
                                         (label_node l, label_clock l)
                                         (fun p => snd p <=? received s (fst p))).
               depremise A3. split.
               rewrite <- H16 at 2. f_equal. 
               assert (B1 := msg_update_label p h s1 m).
                 depremise B1. split. assumption. subv s1. apply in_app_iff. right. subv m. apply in_eq.
                 simpl in B1. open_conjs.
               subv_in m H11.
               rewrite <- H11. 
               subv_in lp A2.
               subv_in m A2.
               assumption.
             simpl in A3.
             bool_to_prop_in A3.
             subst n'. simpl_override. simpl_override. 
             assumption.

           (* -- *)
             destruct A2 as [l'' [A21 [A22 [A23 A24]]]].
             remember (label_node l'') as n'' eqn: Hn''.
             remember (label_clock l'') as c'' eqn: Hc''.

             unfold guard_method in H16.
             assert (A3 := fold_left_and (NId*Clock) (sender_dep u)
                                         (n'', c'')
                                         (fun p => snd p <=? received s (fst p))).
               depremise A3. split.
               rewrite <- H16 at 2. f_equal. 
               assert (B1 := msg_update_label p h s1 (message n1 c' k v u n2 lp0)).
                 depremise B1. split. assumption. subv s1. apply in_app_iff. right. apply in_eq.
                 simpl in B1. open_conjs.
               rewrite <- H11. subv_in lp A23. subv_in m A23. assumption.
             simpl in A3.
             bool_to_prop_in A3.

             assert (A4 := cause_received_received p h s1 l l'' n2). 
               simpl in A4. depremise A4. split_all.
               assumption.
               assumption.
               assumption.
               assert (B1 := prec_pre_prec h l' l'' lp).
                 depremise B1. split_all. 
                 assumption.
                 intro. subst lp.
                 assert (C1 := msg_update_label p h s1 (message n1 c' k v u n2 lp0)).
                   depremise C1. split. assumption. subv s1. apply in_app_iff. right. apply in_eq.
                 simpl in C1. open_conjs.
                 subv_in m H5. subv_in lp0 H8. rewrite L in H8. simpl in H8. assumption.
               apply prec_in in B1. destruct B1 as [B1 _].
               eapply cause_prefix_history_one. split_all. 
                 apply step_star_app_one. exists s1. split; eassumption.
                 assumption.
                 assumption.
               subst c''. subst n''. subv s1. simpl_override. assumption.
               assumption.

             simpl.
             subst c. subst n. subv_in s1 A4. subst n'.
             assumption.

    Qed.


End KVSAlg2CauseObl.


Module KVSAlg2Parametric <: Parametric KVSAlg2.

  Import SysPredefs.
  Import KVSAlg2.


  Section ParallelWorlds.

    Definition RState (Val1: Type)(Val2: Type)(R: Val1 -> Val2 -> Prop)(s1: @State Val1)(s2: @State Val2): Prop := 
      (forall k, 
         R (entry_val (store s1 k)) (entry_val (store s2 k))
         /\ (entry_node (store s1 k)) = (entry_node (store s2 k))
         /\ (entry_clock (store s1 k)) = (entry_clock (store s2 k)))
      /\ received s1 = received s2
      /\ clock s1 = clock s2
      /\ dep s1 = dep s2.


    Definition RUpdate (Val1: Type)(Val2: Type)(R: Val1 -> Val2 -> Prop)(u1: @Update Val1)(u2: @Update Val2): Prop := 
      sender_node u1 = sender_node u2 
      /\ sender_clock u1 = sender_clock u2
      /\ sender_dep u1 = sender_dep u2.


    Variables Val1 Val2 : Type.
    Variable R : Val1 -> Val2 -> Prop.

    Lemma init_method_R: 
      forall v1 v2, R v1 v2 -> RState _ _ R (init_method _ v1) (init_method _ v2).
      
      Proof.
        intros.
        unfold RState.
        unfold init_method.
        simpl.
        split_all.
        intros.
        split_all.
        assumption.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
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
        split.
        unfold RState in H.
        open_conjs.
        specialize (H k).        
        open_conjs.
        assumption.
        unfold RState.
        simpl.
        unfold RState in H.
        open_conjs.
        split_all.
        assumption.
        assumption.
        assumption.
        specialize (H k).
        open_conjs.
        rewrite H2.
        rewrite H3.
        rewrite H4.
        reflexivity.
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
        unfold RState in H.
        open_conjs.
        split.
        unfold RState.
        simpl.
        split_all.        
        intros.
        destruct (eq_nat_dec k k0).
        subst k.
        simpl_override.
        simpl_override.
        split_all.
        assumption.
        reflexivity.
        rewrite H2. reflexivity.
        simpl_override.
        simpl_override.
        specialize (H k0).
        open_conjs.
        split_all; assumption.
        apply functional_extensionality.
        intro n'.
        destruct (eq_nat_dec n n').
        simpl_override.
        simpl_override.
        rewrite H2.
        reflexivity.
        simpl_override.
        simpl_override.        
        rewrite H1.
        reflexivity.
        rewrite H2.
        reflexivity.
        rewrite H2.
        reflexivity.
        unfold RUpdate.
        rewrite H2.
        rewrite H3.
        split_all; reflexivity.
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
        rewrite H3.
        rewrite H4.
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
        split_all.
        intros.
        destruct (eq_nat_dec k k0).
        simpl_override.
        simpl_override.
        split_all;
        assumption.
        simpl_override.
        simpl_override.
        specialize (H k0).
        open_conjs.
        split_all; assumption.
        rewrite H1.
        rewrite H2.
        rewrite H4.
        reflexivity.
        assumption.
        assumption.
      Qed.

  End ParallelWorlds.

End KVSAlg2Parametric.

Module KVSAlg2ExecToAbstExec (SyntaxArg: SyntaxPar).
  
  Module ExecToAbstExec := ExecToAbstExec KVSAlg2 KVSAlg2Parametric KVSAlg2CauseObl SyntaxArg.
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

End KVSAlg2ExecToAbstExec.




