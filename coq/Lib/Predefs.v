From Coq Require Import Bool Arith.EqNat Arith.Peano_dec Arith.Compare_dec List.

Import ListNotations.

Notation "a =_? b" := (eq_nat_dec a b) (at level 20).
Notation "a <>_? b" := (negb (a =_? b)) (at level 20).
Notation "a <_? b" := (lt_dec a b) (at level 20).
Notation "a <=_? b" := (le_dec a b) (at level 20).
Notation "a >_? b" := (gt_dec a b) (at level 20).
Notation "a >=_? b" := (ge_dec a b) (at level 20).

Notation "a <>? b" := (negb (beq_nat a b)) (at level 70).
Notation "a =? b" := (beq_nat a b) (at level 70).
Notation "a <=? b" := (leb a b) (at level 70).

(*
  Programming bools
  &&  ||  =?  <>?  <=?
  ----
  andb_prop
  orb_prop
  beq_nat_true_iff  beq_nat_false_iff
  leb_iff
  negb_true_iff  negb_false_iff
*)

Lemma eq_nat_dec_eq:
  forall (A: Type) n (s1 s2: A),
    (if eq_nat_dec n n then s1 else s2) =
    s1.
Proof.
  intros.
  destruct (eq_nat_dec n n).
  reflexivity.

  exfalso. apply n0. reflexivity.
Qed.

Lemma eq_nat_dec_neq:
  forall (A: Type) n n' (s1 s2: A),
    (not (n = n'))
    -> (if eq_nat_dec n n' then s1 else s2) =
       s2.
Proof.
  intros.

  destruct (eq_nat_dec n n').
  exfalso. apply H in e. assumption.

  reflexivity.    
Qed.

Lemma fold_left_and_false:
  forall (A: Type) ls (f: A -> bool),
    fold_left (fun b l => b && f l) ls false = false.    
Proof.
  intros.
  induction ls.
  simpl.
  reflexivity.
  simpl.
  assumption.
Qed.

Lemma fold_left_and:
  forall (A: Type) ls (l: A) f,
    (fold_left (fun b l => b && f l) ls true = true
     /\ In l ls)
    -> f l = true.
Proof.
  intros.
  destruct H.
  generalize dependent l.
  generalize dependent f.
  induction ls.

  intros. unfold In in H0. contradiction.

  intros.
  apply in_inv in H0.
  destruct H0.

  subst a.
  simpl in H.
  destruct (f l).
  reflexivity.
  simpl in H.
  rewrite fold_left_and_false in H.
  assumption.
  
  apply IHls.
  simpl in H.
  destruct (f a).
  assumption.
  rewrite fold_left_and_false in H.
  inversion H.
  assumption.
Qed.

Theorem call:
  forall {A B : Type} {f g: A -> B} (x: A),
    f = g -> f x = g x.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A), 
 x = y -> f x = f y. 
Proof.
intros A B f x y eq. rewrite eq. reflexivity. 
Qed.

Theorem f2_equal : forall (A B C: Type) (f: A -> B -> C) (x1 x2: A)(y1 y2: B), 
 (x1 = x2 /\ y1 = y2) -> f x1 y1 = f x2 y2. 
Proof.
intros A B C f x1 x2 y1 y2 eq. destruct eq as [eq1 eq2]. rewrite eq1. rewrite eq2. reflexivity. 
Qed.

Theorem f3_equal : forall (A B C D: Type) (f: A -> B -> C -> D)
 (x1 x2: A)(y1 y2: B)(z1 z2: C), 
 (x1 = x2 /\ y1 = y2 /\ z1 = z2) -> f x1 y1 z1 = f x2 y2 z2. 
Proof.
intros A B C D f x1 x2 y1 y2 z1 z2 eq. 
destruct eq as [eq1 [eq2 eq3]].
rewrite eq1. 
rewrite eq2. 
rewrite eq3. 
reflexivity. 
Qed.

Definition nat_dec (n: nat): {n' | n = S n'} + {n = 0}.
  destruct n; eauto.
Defined.

Definition option_dec {A}(n: option A): {n' | n = Some n'} + {n = None}.
  destruct n; eauto.
Defined.

(* ------------------------------------------------------- *)
(* General tactics. *)

Tactic Notation "open_conjs" :=
  repeat(match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
         end).

Tactic Notation "split_all" :=
  repeat(match goal with
           | [ |- _ /\ _ ] => split
         end).


Ltac specex H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             match type of T with
               | Prop =>
                 fail 1
               | _ =>
                 let x := fresh "x" in
                   evar (x : T);
                   let x' := eval unfold x in x in
                     clear x; specialize (H x')
             end
         end.

Ltac depremise H :=
  match type of H with
    | forall x : ?T, _ =>
      let x := fresh "x" in
      assert (x: T);
      [ clear H | specialize (H x); clear x ]                  
  end.

Ltac specex_deprem H :=
  specex H; depremise H.

Ltac subv x :=
  match goal with 
    | H: x = _ |- _ => rewrite H; simpl
    | H: _ = x |- _ => rewrite <- H; simpl
    | _ => try unfold x; simpl
  end.

Ltac subv_in x H' :=
  match goal with 
    | H: x = _ |- _ => rewrite H in H'; simpl in H'
    | H: _ = x |- _ => rewrite <- H in H'; simpl in H'
    | _ => try unfold x in H'; simpl in H'
  end.

Tactic Notation "rewrite_clear" ident(H) ident(H') :=
  rewrite H in H'; clear H.
      
Tactic Notation "r_rewrite_clear" ident(H) ident(H') :=
  rewrite <- H in H'; clear H.


Tactic Notation "bool_to_prop" :=
  try match goal with
    | [ |- negb _ = true ] =>  try apply negb_true_iff
    | [ |- negb _ = false ] =>  try apply negb_false_iff
  end;
  (apply andb_prop ||
   apply orb_prop ||
   apply beq_nat_true_iff ||
   apply beq_nat_false_iff ||
   apply leb_iff).

Tactic Notation "bool_to_prop_in" ident(H) :=
  try match goal with
    | [ H: negb _ = true |- _ ] =>  try apply negb_true_iff in H
    | [ H: negb _ = false |- _ ] =>  try apply negb_false_iff in H
  end;
  (apply andb_prop in H ||
   apply orb_prop in H ||
   apply beq_nat_true_iff in H ||
   apply beq_nat_false_iff in H ||
   apply leb_iff in H).


(* ------------------------------------------------------- *)
(* list set lemmas *)

Lemma nil_cons_end:
  forall (T: Type)(l: list T)(e: T),
    not((l++[e]) = nil).
Proof.
  intros.
  intro.
  destruct l.

    rewrite app_nil_l in H.
    assert (A := @nil_cons T e nil).
    symmetry in H.
    apply A in H.
    assumption.

    rewrite <- app_comm_cons in H.
    assert (A := @nil_cons T t (l ++ [e])). 
    symmetry in H.
    apply A in H.
    assumption.
Qed.

Lemma list_end : forall (T: Type)(l: list T),
 l = nil \/ exists l' e, l = l' ++ [e].
Proof.
  intros.
  destruct l.

    left. reflexivity.
    
    right.
    assert (A1 := @nil_cons T t l).
    apply not_eq_sym in A1.

    assert (A2 := @exists_last T (t :: l) A1). 
    destruct A2. destruct s.
    exists x. exists x0.
    assumption.
Qed.

Lemma cons_to_app:
  forall {T: Type}(ls: list T)(e: T),
    e :: ls = [e] ++ ls.
Proof.
  intros.
  assert (A := app_nil_l ls).
  rewrite <- A at 1.
  rewrite app_comm_cons.
  reflexivity.
Qed.

Lemma filter_filter:
  forall A (f g: A->bool) l,
    filter f (filter g l) = filter (fun x => (andb (f x) (g x))) l.
Proof.
  intros.
  induction l.
  reflexivity.

  unfold filter at 2 3.
  (* unfold compose. *)
  destruct (g a); simpl; destruct (f a);

  simpl;
  try apply f_equal;
  unfold filter in IHl at 2 3;
  rewrite IHl;
  reflexivity.
Qed.

Lemma nodup_filter:
  forall A (l: list A) f,
  NoDup l -> NoDup (filter f l). 
Proof.
  intros.
  induction l.

  simpl. constructor.

  simpl. 
  inversion H.
  subst.
  destruct (f a).
  depremise IHl. assumption.
  constructor.
  intro. apply filter_In in H0. destruct H0. contradiction.
  assumption.

  apply IHl. assumption. 
Qed.
