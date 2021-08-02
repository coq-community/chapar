(**********************************************************************************)
(* Adapted from "A Formalization of Relaxed Separation Logic" by Viktor Vafeiadis *)
(**********************************************************************************)

From Coq Require Import List.
From Coq Require Import Permutation.

Set Implicit Arguments.

Definition disjoint A (l1 l2 : list A) := 
  forall a (IN1: In a l1) (IN2: In a l2), False.

Lemma In_mapI : forall A B (f: A -> B) x l (IN: In x l), In (f x) (map f l).
Proof.
  induction l; simpl; intros; auto.
  case IN; intros.
  - rewrite H.
    left; auto.
  - right.
    apply IHl; auto.
Qed.

Lemma In_mapD : 
  forall A B (f: A->B) y l, In y (map f l) -> exists x, f x = y /\ In x l.
Proof.
  induction l; simpl in *; intuition; eauto.
  destruct H; destruct H.
  eauto.
Qed.

Lemma In_map : 
  forall A B (f: A->B) y l, In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  split; intros.
  - apply In_mapD; auto.
  - destruct H; destruct H.
    rewrite <- H.
    eapply In_mapI in H0; eauto.
Qed.

Lemma nodup_map:
  forall (A B: Type) (f: A -> B) (l: list A),
  NoDup l ->
  (forall x y, In x l -> In y l -> x <> y -> f x <> f y) ->
  NoDup (map f l).
Proof.
  induction l; simpl; intros; [constructor|].
  inversion H; subst.
  constructor; eauto.
  intro; rewrite In_map in *.
  destruct H1; destruct H1.
  edestruct H0; try eapply H1; eauto.
  intro.
  contradict H3.
  rewrite <- H5.
  auto.
Qed.

Lemma nodup_cons A (x: A) l:
  NoDup (x :: l) <-> ~ In x l /\ NoDup l.
Proof.
  split; intros; inversion H; auto.
  apply NoDup_cons; auto.
Qed.

Lemma In_appI1 : forall A (x:A) l (IN: In x l) l', In x (l++l').
Proof.
  induction l; intros; inversion IN.
  - left; auto.
  - right.
    apply IHl; auto.
Qed.

Lemma In_appI2 : forall A (x:A) l' (IN: In x l') l, In x (l++l').
Proof.
  induction l; intros; auto.
  right; auto.
Qed.

Lemma In_app : forall A (x:A) l l', In x (l++l') <-> In x l \/ In x l'.
Proof. intuition; auto using In_appI1, In_appI2. Qed.

Lemma nodup_app:
  forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) <->
  NoDup l1 /\ NoDup l2 /\ disjoint l1 l2.
Proof.
  induction l1; intros.
  - split.
    * simpl; split; auto using NoDup_nil.
      split; auto.
      unfold disjoint; intuition.
    * simpl; intros.
      destruct H.
      destruct H0.
      assumption.
  - simpl.
    rewrite nodup_cons.
    rewrite IHl1.
    rewrite In_app.
    unfold disjoint.
    split; intuition (subst; eauto).
    * apply NoDup_cons; auto.
    * inversion IN1; subst; auto.
      eauto.
    * inversion H0; subst; auto.
    * inversion H0; subst.
      specialize (H2 a).
      apply H2; auto.
      left; auto.
    * inversion H0; auto.
    * specialize (H2 a0).
      apply H2; auto.
      right; auto.
Qed.

Lemma In_filter :
  forall (A : Type) (x:A) f l, In x (filter f l) <-> In x l /\ f x = true.
Proof.
  induction l; intros; simpl.
  - split; auto; intros.
    destruct H; auto.
  - destruct (f a) eqn:?.
    * simpl; split; intros; intuition (subst; eauto).
    * split; intros; intuition eauto; congruence.
Qed.

Lemma NoDup_filter A (l: list A) (ND: NoDup l) f : NoDup (filter f l).
Proof. 
  induction l; intros; try constructor.
  simpl.
  destruct (f a) eqn:?; simpl; inversion ND; subst; auto.
  apply NoDup_cons; auto.
  rewrite In_filter.
  tauto.
Qed.
