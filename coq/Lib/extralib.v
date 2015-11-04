(******************************************************************************)
(*      #####    #####   ##     A Formalization of Relaxed Separation Logic   *)
(*     ##  ##  ##       ##                                                    *)
(*    #####    #####   ##       Copyright (c) Viktor Vafeiadis                *)
(*   ##  ##       ##  ##                                                      *)
(*  ##    ##  #####  ########   See LICENSE.txt for license.                  *)
(******************************************************************************)

Require Import List Vbase Varith Vlistbase Vlist.
Require Import Permutation Classical.
Set Implicit Arguments.

Notation sval := (@proj1_sig _ _).
Notation "@ 'sval'" := (@proj1_sig) (at level 10, format "@ 'sval'").


Definition disjoint A (l1 l2 : list A) := 
  forall a (IN1: In a l1) (IN2: In a l2), False. 

Lemma nodup_one A (x: A) : NoDup (x :: nil).
Proof. vauto. Qed.
Hint Resolve NoDup_nil nodup_one.

Lemma nodup_map:
  forall (A B: Type) (f: A -> B) (l: list A),
  NoDup l ->
  (forall x y, In x l -> In y l -> x <> y -> f x <> f y) ->
  NoDup (map f l).
Proof.
  induction 1; ins; vauto. 
  constructor; eauto.
  intro; rewrite In_map in *; desf.
  edestruct H1; try eapply H2; eauto.
  intro; desf.
Qed.

Lemma nodup_append_commut:
  forall (A: Type) (a b: list A),
  NoDup (a ++ b) -> NoDup (b ++ a).
Proof.
  intro A.
  assert (forall (x: A) (b: list A) (a: list A), 
           NoDup (a ++ b) -> ~(In x a) -> ~(In x b) -> 
           NoDup (a ++ x :: b)).
    induction a; simpl; intros.
    constructor; auto.
    inversion H. constructor. red; intro.
    elim (in_app_or _ _ _ H6); intro.
    elim H4. apply in_or_app. tauto.
    elim H7; intro. subst a. elim H0. left. auto. 
    elim H4. apply in_or_app. tauto.
    auto.
  induction a; simpl; intros.
  rewrite <- app_nil_end. auto.
  inversion H0. apply H. auto. 
  red; intro; elim H3. apply in_or_app. tauto.
  red; intro; elim H3. apply in_or_app. tauto.
Qed.

Lemma nodup_cons A (x: A) l:
  NoDup (x :: l) <-> ~ In x l /\ NoDup l.
Proof. split; inversion 1; vauto. Qed.

Lemma nodup_app:
  forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) <->
  NoDup l1 /\ NoDup l2 /\ disjoint l1 l2.
Proof.
  induction l1; ins. 
    by split; ins; desf; vauto.
  rewrite !nodup_cons, IHl1, In_app; unfold disjoint.
  ins; intuition (subst; eauto). 
Qed.

Lemma nodup_append:
  forall (A: Type) (l1 l2: list A),
  NoDup l1 -> NoDup l2 -> disjoint l1 l2 ->
  NoDup (l1 ++ l2).
Proof.
  generalize nodup_app; firstorder.
Qed.

Lemma nodup_append_right:
  forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) -> NoDup l2.
Proof.
  generalize nodup_app; firstorder.
Qed.

Lemma nodup_append_left:
  forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) -> NoDup l1.
Proof.
  generalize nodup_app; firstorder.
Qed.

(* 
Lemma uniq_app (A: eqType) (a b : list A) :
  uniq (a ++ b) <-> uniq a /\ uniq b /\ disjoint a b. 
Proof.
  rewrite app_uniq. 
  assert (negb (has (mem a) b) <-> disjoint a b).
    induction b; ins.
      by split; try done; induction a; ins.
    rewrite negb_or.
    case inP; ins; [by split; ins; exfalso; eauto using In_eq|]. 
    by rewrite IHb; split; red; ins; desf; eauto using In_eq, In_cons.
  rewrite <- H; split; ins; desf.
Qed.
*)

(******************************************************************************)

Definition mupd (A: eqType) B (h : A -> B) y z := 
  fun x => if x == y then z else h x.
Arguments mupd [A B] h y z x.

Lemma mupds (A: eqType) B (f: A -> B) x y : mupd f x y x = y. 
Proof. by unfold mupd; desf; desf. Qed.

Lemma mupdo (A: eqType) B (f: A -> B) x y z : x <> z -> mupd f x y z = f z. 
Proof. by unfold mupd; desf; desf. Qed.


(******************************************************************************)

Lemma In_perm A l l' (P: perm_eq (T:=A) l l') x : In x l <-> In x l'.
Proof. 
  by split; ins; apply/inP; instantiate; 
     [rewrite <- (perm_eq_mem P)|rewrite (perm_eq_mem P)]; apply/inP.
Qed.

Lemma nodup_perm A l l' (P: perm_eq (T:=A) l l') : NoDup l <-> NoDup l'.
Proof.
  by split; ins; apply/uniqP; instantiate; 
     [rewrite <- (perm_eq_uniq P)|rewrite (perm_eq_uniq P)]; apply/uniqP.
Qed.


Lemma In_mem_eq (A: eqType) (l l': list A) (P: l =i l') x : In x l <-> In x l'.
Proof. 
  by split; ins; apply/inP; instantiate; [rewrite <- P | rewrite P]; apply/inP.
Qed.

Lemma NoDup_filter A (l: list A) (ND: NoDup l) f : NoDup (filter f l). 
Proof. 
  induction l; ins; inv ND; desf; eauto using NoDup.
  econstructor; eauto; rewrite In_filter; tauto.
Qed.

Hint Resolve NoDup_filter.

Lemma NoDup_eq_one A (x : A) l : 
   NoDup l -> In x l -> (forall y (IN: In y l), y = x) -> l = x :: nil.
Proof.
  destruct l; ins; f_equal; eauto.
  inv H; desf; clear H H5; induction l; ins; desf; case H4; eauto using eq_sym.
  rewrite IHl in H0; ins; desf; eauto.
Qed.

(*
Lemma nodup_eq_perm :
  forall A (l l' : list A), 
    NoDup l -> NoDup l' -> (forall x, In x l <-> In x l') ->
    Permutation l l'.
Proof.
  induction l; inversion 1; ins; subst.
    destruct l'; ins; specialize (H1 a); tauto.
  assert (X : In a l') by (specialize (H5 a); tauto). 
  eapply In_split in X; desf.
  rewrite nodup_app, nodup_cons in *; desf.
  eapply Permutation_trans, Permutation_middle. 
  eapply Permutation_cons, IHl; ins. 
  rewrite nodup_app; repeat split; ins; red; ins; eauto using In_cons. 
  specialize (H5 x); rewrite In_app in *; ins.
  destruct (classic (a = x)); subst; try tauto.
  split; intro; desf; exfalso; eauto using In_eq. 
Qed.
*)

Lemma map_perm : 
  forall A B (f: A -> B) l l', Permutation l l' -> Permutation (map f l) (map f l').
Proof.
  induction 1; eauto using Permutation.
Qed.

Lemma perm_from_subset : 
  forall A (l : list A) l',
    NoDup l' ->
    (forall x, In x l' -> In x l) ->
    exists l'', Permutation l (l' ++ l''). 
Proof.
  induction l; ins; vauto.
    by destruct l'; ins; vauto; exfalso; eauto.
  destruct (classic (In a l')).

    eapply In_split in H1; desf; rewrite ?nodup_app, ?nodup_cons in *; desf.
    destruct (IHl (l1 ++ l2)); ins. 
      by rewrite ?nodup_app, ?nodup_cons in *; desf; repeat split; ins; red; eauto using In_cons.
      by specialize (H0 x); rewrite In_app in *; ins; desf;
         destruct (classic (a = x)); subst; try tauto; exfalso; eauto using In_eq.
    eexists; rewrite appA in *; ins.
    by eapply Permutation_trans, Permutation_middle; eauto.

  destruct (IHl l'); eauto; ins.
    by destruct (H0 x); auto; ins; subst.
  by eexists (a :: _); eapply Permutation_trans, Permutation_middle; eauto.
Qed.

Lemma Permutation_NoDup A ( l l' : list A) : 
  Permutation l l' -> NoDup l -> NoDup l'.
Proof.
  induction 1; eauto; rewrite !nodup_cons in *; ins; desf; intuition. 
  eby symmetry in H; eapply H0; eapply Permutation_in.
Qed.

Lemma NoDup_mapD A B (f : A-> B) l :
  NoDup (map f l) -> NoDup l.
Proof.
  induction l; ins; rewrite !nodup_cons, In_map in *; desf; eauto 8.
Qed.


Lemma olast_inv A l x : 
  olast (T:=A) l = Some x -> exists prefix, l = prefix ++ x :: nil.
Proof.
  destruct l; ins; desf; induction[a] l; ins; [by exists nil|].
  by specialize (IHl a); desf; exists (a0 :: prefix); ins; f_equal.
Qed.

Lemma In_flatten A (x:A) l : 
  In x (flatten l) <-> exists y, In x y /\ In y l.
Proof.
  induction l; ins. by split; ins; desf. 
  rewrite flatten_cons, In_app, IHl; clear; split; ins; desf; eauto.
Qed.

