(** * Lists -- part II *)

(** This development is largely ported from the [seq] library of SSReflect. 
    The names of several operations have been changed to use the standard
    Coq list definitions (e.g., [seq] => [list], [cat] => [app],
    [size] => [length]) and a few lemmas have been added.
    The [map2] definition and its properties are new.
 *)

Require Import Vbase Vlistbase Varith. 
Require Coq.omega.Omega.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope bool_scope.
Open Scope list_scope.



Lemma has_psplit (A : Type) (p : pred A) (s : list A) (x : A) : 
  has p s -> 
  s = take (find p s) s ++ nth x s (find p s) :: drop (S (find p s)) s.
Proof.
 intros.
 rewrite <- (app_take_drop (find p s) s) at 1.
 rewrite (drop_nth x); try done.
 by rewrite <- has_find.
Qed. 


(** Equality and eqType for list *)

Section EqSeq.

Variables (n0 : nat) (T : eqType) (x0 : T).
Notation Local nth := (nth x0).
Implicit Type s : list T.
Implicit Types x y z : T.

Fixpoint eqlist s1 s2 {struct s2} :=
  match s1, s2 with
  | nil, nil => true
  | x1 :: s1', x2 :: s2' => (x1 == x2) && eqlist s1' s2'
  | _, _ => false
  end.

Lemma eqlistP : Equality.axiom eqlist.
Proof.
red; induction x; destruct y; vauto; simpl.
case eqP; intro X; clarify; try (right; congruence). 
destruct (IHx y); vauto; right; congruence.
Qed.

Canonical Structure list_eqMixin := EqMixin eqlistP.
Canonical Structure list_eqType := Eval hnf in EqType _ list_eqMixin. 

Lemma eqlistE : eqlist = eq_op.
Proof. done. Qed.

Lemma eqlist_cons : forall x1 x2 s1 s2,
  (x1 :: s1 == x2 :: s2) = (x1 == x2) && (s1 == s2).
Proof. done. Qed.

Lemma eqlist_app : forall s1 s2 s3 s4,
  length s1 = length s2 -> (s1 ++ s3 == s2 ++ s4) = (s1 == s2) && (s3 == s4).
Proof.
induction s1; destruct s2; clarsimp.
by rewrite !eqlist_cons, <- andbA, IHs1.
Qed.

Lemma eqlist_rev2 : forall l1 l2,
  (rev l1 == rev l2) = (l1 == l2).
Proof.
  intros; do 2 case eqP; clarsimp.
  generalize (f_equal (@rev _) e); clarsimp.
Qed.

Lemma eqlist_snoc : forall s1 s2 x1 x2,
  (snoc s1 x1 == snoc s2 x2) = (s1 == s2) && (x1 == x2).
Proof.
  by intros; rewrite <- eqlist_rev2, !rev_snoc, eqlist_cons, eqlist_rev2, andbC.
Qed.

Lemma has_filter : forall a s, has a s = (filter a s != nil).
Proof. by intros; rewrite has_count, count_filter; case (filter a s). Qed.

Lemma length_eq0 : forall l, (length l == 0) = (l == nil).
Proof. intros []; clarsimp. Qed.

(* mem_list and index. *)
(* mem_list defines a predType for list. *)

Fixpoint mem_list (s : list T) :=
  match s with
    | nil => (fun _ => false)
    | y :: s' => (fun x => (x == y) || mem_list s' x)
  end.

Definition eqlist_class := list T.
Identity Coercion list_of_eqlist : eqlist_class >-> list.

Coercion pred_of_eq_list (s : eqlist_class) : pred_class := (fun x => mem_list s x).

Canonical Structure list_predType := @mkPredType T (list T) pred_of_eq_list.
(* The line below makes mem_list a canonical instance of topred. *)
Canonical Structure mem_list_predType := mkPredType mem_list.

Lemma in_cons : forall y s x, (x \in y :: s) = (x == y) || (x \in s).
Proof. done. Qed.

Hint Rewrite in_cons: vlib. (* Have to repeat outside section! *)

Lemma in_nil : forall x, (x \in nil) = false.
Proof. done. Qed.

Lemma mem_list1 : forall x y, (x \in y :: nil) = (x == y).
Proof. clarsimp. Qed.

 (* to be repeated after the Section discharge. *)
(* Let inE := (mem_list1, in_cons, inE). *)

(*Lemma mem_list2 : forall x y1 y2, (x \in y1 :: y2 :: nil) = xpred2 y1 y2 x.
Proof. clarsimp. Qed.

Lemma mem_list3 :  forall x y1 y2 y3,
  (x \in y1 :: y2 :: y3 :: nil) = xpred3 y1 y2 y3 x.
Proof. clarassoc. Qed.

Lemma mem_list4 :  forall x y1 y2 y3 y4,
  (x \in y1 :: y2 :: y3 :: y4 :: nil) = xpred4 y1 y2 y3 y4 x.
Proof. clarassoc. Qed.*)

Lemma mem_app : forall x s1 s2, (x \in s1 ++ s2) = (x \in s1) || (x \in s2).
Proof. by induction s1; clarsimp; rewrite IHs1, orbA. Qed.

Lemma mem_snoc : forall s y, snoc s y =i y :: s.
Proof. red; clarsimp; rewrite snocE, mem_app, !in_cons, in_nil, orbC; clarsimp. Qed.

Lemma mem_head : forall x s, x \in x :: s.
Proof. by intros; rewrite in_cons, eqxx. Qed.

Lemma mem_last : forall x s, last x s \in x :: s.
Proof. by intros; rewrite lastI, mem_snoc, mem_head. Qed.

Lemma mem_behead : forall s, {subset behead s <= s}.
Proof. by destruct s; clarsimp; intro; rewrite in_cons, orbC; intros ->. Qed.

Lemma mem_belast : forall s y, {subset belast y s <= y :: s}.
Proof. by red; intros; rewrite lastI, mem_snoc, mem_behead. Qed.

Lemma mem_nth : forall s n, n < length s -> nth s n \in s.
Proof. induct s [n]. Qed. 

Lemma mem_take : forall s x, x \in take n0 s -> x \in s.
Proof. by intros; rewrite <-(app_take_drop n0 s), mem_app, H. Qed.

Lemma mem_drop : forall s x, x \in drop n0 s -> x \in s.
Proof. by intros; rewrite <-(app_take_drop n0 s), mem_app, H, orbT. Qed.

Lemma mem_rev : forall s, rev s =i s.
Proof.
by red; induction s; ins; rewrite rev_cons, mem_snoc, !in_cons, IHs.
Qed.

Lemma in_head : forall x l, x \in x :: l.
Proof. clarsimp. Qed.

Lemma in_behead : forall x y l, x \in l -> x \in y :: l.
Proof. clarsimp; clarsimp. Qed.

Lemma in_consE : forall {x y l}, x \in y :: l -> {x = y} + {x \in l}.
Proof. intros x y l; rewrite in_cons; case eqP; auto. Qed.

Lemma in_split : forall x l, x \in l -> exists l1 l2, l = l1 ++ x :: l2.
Proof.
  induction l; ins.
  destruct (in_consE H); clarify; [by exists nil; vauto|].
  specialize (IHl eq_refl); des; exists (a :: l1); vauto.
Qed.

Ltac clarify2 :=
  vlib__clarify1;
  repeat match goal with
    | H1: ?x = Some _, H2: ?x = None   |- _ => rewrite H2 in H1; discriminate
    | H1: ?x = Some _, H2: ?x = Some _ |- _ => rewrite H2 in H1; vlib__clarify1
  end; try done.

Lemma inP : 
  forall x l , reflect (In x l) (x \in l).
Proof.
  induction l; simpls; vauto.
  clarsimp; case eqP; ins; vauto.
  case IHl; constructor; auto; intro; desf.
Qed.

Section Filters.

Variable a : pred T.

Lemma hasP : forall l, reflect (exists2 x, x \in l & a x) (has a l).
Proof.
induction l; simpls; [by right; intro x; case x|].
case_eq (a a0) as A; [by left; exists a0; clarsimp|].
apply (iffP IHl); intros [x ysx ax]; [|destruct (in_consE ysx)]; exists x; do 2 clarsimp.
Qed.

Lemma hasPn : forall l, reflect (forall x, x \in l -> negb (a x)) (negb (has a l)).
Proof.
  induction l; vauto; simpls.
  case_eq (a a0) as A; simpls. 
    by right; intros H; exploit (H a0); clarsimp.
  destruct IHl as [X|X]; constructor; clarsimp.
    by destruct (in_consE H); autos.
  intuition (auto using in_behead).
Qed.

Lemma allP : forall l, reflect (forall x, x \in l -> a x) (all a l).
Proof.
  induction l; vauto; simpls.
  case_eq (a a0) as A; simpls.
  2: by right; intros H; exploit (H a0); clarsimp. 
  destruct IHl as [X|X]; constructor; clarsimp.
    by destruct (in_consE H); autos.
  by intuition (auto using in_behead).
Qed.

Lemma allPn : forall l, reflect (exists2 x, x \in l & negb (a x)) (negb (all a l)).
Proof.
  induction l; simpls; [by right; intro x; case x|].
  case_eq (a a0) as A; simpls; [|by left; exists a0; clarsimp].
  apply (iffP IHl); intros [x ysx ax]; [|destruct (in_consE ysx)]; exists x; clarsimp; clarsimp.
Qed.

Lemma mem_filter : forall x l, (x \in filter a l) = a x && (x \in l).
Proof.
intros; induction l; clarsimp.
case ifP; clarsimp; rewrite IHl; case (eqP x a0); clarsimp.
Qed.

End Filters.

Lemma eq_in_filter : forall (a1 a2 : pred T) s,
  {in s, a1 =1 a2} -> filter a1 s = filter a2 s.
Proof.
  induction s; ins; rewrite H, IHs; try done; clarsimp.
  by red; intros; apply H; eapply mem_behead.
Qed.

Lemma eq_has_r : forall s1 s2 (EQ: s1 =i s2) f, has f s1 = has f s2.
Proof.
  by intros; apply/hasP/hasP; intros [x ? ?]; exists x; simpls;
   [ rewrite EQ | rewrite <- EQ ].
Qed.

Lemma eq_all_r : forall s1 s2 (EQ: s1 =i s2) f, all f s1 = all f s2.
Proof.
  intros; apply/allP/allP; try red; intros; apply H; congruence.
Qed.

Lemma has_sym : forall s1 s2, has (mem s1) s2 = has (mem s2) s1.
Proof.
intros; case (hasP _ s1); case (hasP _ s2); clarsimp; destruct e, n; eauto.
Qed.

Lemma has_pred1 : forall x l, has (fun y => y == x) l = (x \in l).
Proof. by induction l; clarsimp; rewrite IHl, beq_sym. Qed.

(** Constant sequences, i.e., the image of nlist. *)

Definition constant s := 
  match s with
    | nil => true
    | x :: s' => all (fun y => y == x) s'
  end.

Lemma all_pred1P x s : 
  reflect (s = nlist (length s) x) (all (fun y => y == x) s).
Proof.
unfold nlist, ncons; induction s; clarsimp; vauto.
case eqP; clarsimp; destruct IHs; constructor; congruence.
Qed.

Lemma all_pred1_constant x s : all (fun y => y == x) s -> constant s.
Proof. induction s; clarsimp; destruct (eqP a x); clarsimp. Qed.

Implicit Arguments all_pred1_constant [].

Lemma all_pred1_nlist : forall x y n,
  all (fun y => y == x) (nlist n y) = ((n == 0) || (x == y)).
Proof.
  destruct n; clarsimp.
  rewrite beq_sym; case eqP; clarsimp.
  induction n; clarsimp.
Qed.

Lemma constant_nlist : forall n x, constant (nlist n x).
Proof. intros; apply (all_pred1_constant x); rewrite all_pred1_nlist; clarsimp. Qed.

(* Uses x0 *)
Lemma constantP : forall s,
  reflect (exists x, s = nlist (length s) x) (constant s).
Proof.
intros; apply (iffP (idP _)); [|by intros [x ->]; apply constant_nlist].
destruct s; [by exists x0|].
intro X; generalize (all_pred1P _ _ X); unfold nlist, ncons; clarsimp.
exists s; congruence.
Qed.

(* [uniq l]: the list has no duplicate entries. *)

Fixpoint uniq s :=
  match s with
    | nil => true
    | x :: s' => (x \notin s') && uniq s'
  end.

Lemma cons_uniq : forall x s, uniq (x :: s) = (x \notin s) && uniq s.
Proof. done. Qed.

Lemma app_uniq : forall s1 s2,
  uniq (s1 ++ s2) = uniq s1 && negb (has (mem s1) s2) && uniq s2.
Proof.
intros; induction s1; clarsimp.
rewrite has_sym; simpl; rewrite has_sym, IHs1, mem_app, !negb_or.
repeat (case in_mem; clarsimp).
Qed.

Lemma uniq_appC : forall s1 s2, uniq (s1 ++ s2) = uniq (s2 ++ s1).
Proof. intros; rewrite !app_uniq, has_sym; repeat (case uniq; clarsimp). Qed.

Lemma uniq_appCA : forall s1 s2 s3,
  uniq (s1 ++ s2 ++ s3) = uniq (s2 ++ s1 ++ s3).
Proof.
by intros; rewrite <- !appA, <-!(uniq_appC s3), !(app_uniq s3), uniq_appC, !has_app, orbC.
Qed.

Lemma snoc_uniq : forall s x, uniq (snoc s x) = (x \notin s) && uniq s.
Proof. by intros; rewrite <-appl1, uniq_appC. Qed.

Lemma filter_uniq : forall s a, uniq s -> uniq (filter a s).
Proof.
intros; induction s; clarsimp; rewrite fun_if; simpl.
rewrite mem_filter, !IHs; try done; case ifP; ins; clarify. 
Qed.

Lemma rot_uniq : forall s, uniq (rot n0 s) = uniq s.
Proof. by intros; unfold rot; rewrite uniq_appC, app_take_drop. Qed.

Lemma rev_uniq : forall s, uniq (rev s) = uniq s.
Proof. by induction s; clarsimp; rewrite snoc_uniq, mem_rev, IHs. Qed.

Lemma count_uniq_mem : 
  forall s x, uniq s -> count (fun y => y == x) s = if (x \in s) then 1 else 0.
Proof.
induction s; clarsimp; []; des; rewrite beq_sym; case eqP; autos. 
by rewrite IHs; [case ifP|]; clarsimp.
Qed.

Lemma in_split_uniq :
  forall x l, 
    x \in l -> uniq l -> 
    exists l1 l2, l = l1 ++ x ::  l2 /\ 
      uniq (l1 ++ l2) /\ x \notin (l1 ++ l2).
Proof.
 intros; pose proof (in_split H); des; clarify; 
 do 3 eexists; eauto; rewrite app_uniq in *; simpls; clarify.
 rewrite mem_app; apply/norP in H1; desc; clarify. 
Qed. 

(* Removing duplicates *)

Fixpoint undup s :=
  match s with
    | nil => nil
    | x :: s' => if x \in s' then undup s' else x :: undup s'
  end.

Lemma length_undup : forall s, length (undup s) <= length s.
Proof. induction s; clarsimp; case ifP; autos. Qed.

Lemma mem_undup : forall s, undup s =i s.
Proof.
intros s x; induction s; clarsimp; rewrite <- IHs.
case ifP; [case eqP|]; clarsimp.
Qed.

Hint Rewrite mem_undup : vlib.

Lemma undup_uniq : forall s, uniq (undup s).
Proof. by induction s; clarsimp; case ifP; clarsimp. Qed.

Lemma undup_id : forall s, uniq s -> undup s = s.
Proof. induct s. Qed.

Lemma ltn_length_undup : forall s, (length (undup s) < length s) = negb (uniq s).
Proof. 
induction s; clarsimp; case ifP; clarsimp; rewrite length_undup; clarsimp.
Qed. 

(* Lookup *)

Definition index x := find (fun y => y == x).

Lemma index_length : forall x s, index x s <= length s.
Proof. intros; unfold index; apply find_length. Qed.

Lemma index_mem : forall x s, (index x s < length s) = (x \in s).
Proof. by intros; rewrite <- has_pred1, has_find. Qed.

Lemma nth_index : forall x s, x \in s -> nth s (index x s) = x.
Proof. by intros; rewrite <- has_pred1 in H; apply (eqP _ _ (nth_find x0 H)). Qed.

Lemma index_app : forall x s1 s2,
 index x (s1 ++ s2) = if x \in s1 then index x s1 else length s1 + index x s2.
Proof. by unfold index; intros; rewrite find_app, has_pred1. Qed.

Lemma index_uniq : forall i s, i < length s -> uniq s -> index (nth s i) s = i.
Proof.
unfold index; induction[i] s [i]; clarsimp; des.
rewrite IHs; clarsimp; case eqP; clarsimp; rewrite mem_nth in *; clarsimp.
Qed.

Lemma index_head : forall x s, index x (x :: s) = 0.
Proof. unfold index; clarsimp. Qed.

Lemma index_last : forall x s,
  uniq (x :: s) -> index (last x s) (x :: s) = length s.
Proof.
intros x s; rewrite lastI, snoc_uniq, <-appl1, index_app, length_belast.
unfold index; case ifP; clarsimp.
Qed.

Lemma nth_uniq : forall s i j,
   i < length s -> j < length s -> uniq s -> (nth s i == nth s j) = (i == j).
Proof.
intros; case eqP; case eqP; clarsimp.
elim n; rewrite <- (index_uniq H), <- (index_uniq H0); congruence.
Qed.

Lemma mem_rot : forall s, rot n0 s =i s.
Proof. 
by intros s x; unfold rot; rewrite <- (app_take_drop n0 s) at 3; rewrite !mem_app, orbC.
Qed.

Lemma eqlist_rot : forall s1 s2, (rot n0 s1 == rot n0 s2) = (s1 == s2).
Proof. by intros; do 2 case eqP; ins; clarify; eapply rot_inj in e. Qed.

Inductive rot_to_spec (s : list T) (x : T) : Type :=
  RotToSpec i s' (_ : rot i s = x :: s').

Lemma rot_to : forall s x, x \in s -> rot_to_spec s x.
Proof.
intros; pose (i := index x s); exists i (drop (S i) s ++ take i s); subst i.
unfold rot; rewrite <- app_cons.
apply (f_equal (fun s2 => s2 ++ take (index x s) s)).
unfold index; induction s; clarsimp.
rewrite beq_sym; destruct (eqP x a); autos. 
Qed.

End EqSeq.


(* Definition inE := (mem_list1, in_cons, inE). *)

(* Prenex Implicits uniq undup index. *)

Implicit Arguments eqlistP [T x y].
Implicit Arguments all_filterP [T f s].
Implicit Arguments hasP [T a l].
Implicit Arguments hasPn [T a l].
Implicit Arguments allP [T a l].
Implicit Arguments allPn [T a l].
Implicit Arguments index [T].
Implicit Arguments uniq [T].
(* Prenex Implicits eqlistP all_filterP hasP hasPn allP allPn. *)

Hint Rewrite in_cons in_cons mem_app mem_filter mem_rot : vlib.
Hint Resolve in_head in_behead : vlib.
Hint Resolve undup_uniq : vlib. 

Section NlistthTheory.

Lemma nthP : forall (T : eqType) (s : list T) x x0,
  reflect (exists2 i, i < length s & nth x0 s i = x) (x \in s).
Proof.
intros; apply (iffP (idP _)); [|by intros [n Hn <-]; apply mem_nth].
by exists (index x s); [ rewrite index_mem | apply nth_index ].
Qed.

Variable T : Type.

Lemma has_nthP : forall (a : pred T) s x0,
  reflect (exists2 i, i < length s & a (nth x0 s i)) (has a s).
Proof.
intros; induction s; clarsimp; [by right; intros []|].
case_eq (a a0); clarsimp; [by left; exists 0|].
apply (iffP IHs); [intros [i] | intros [[|i]]]; [exists (S i) | | exists i]; clarsimp.
Qed.

Lemma all_nthP : forall (a : pred T) s x0,
  reflect (forall i, i < length s -> a (nth x0 s i)) (all a s).
Proof.
intros; induction s; clarsimp; vauto.
case_eq (a a0); clarsimp.
  by apply (iffP IHs); clarsimp; [destruct i|specialize (H0 (S i))]; autos.
right; intro X; specialize (X 0); autos.
Qed.

End NlistthTheory.

Lemma set_nth_default : forall T s (y0 x0 : T) n,
  n < length s -> nth x0 s n = nth y0 s n.
Proof. induct s [n]; auto. Qed.

Lemma headI : forall T s (x : T),
  snoc s x = head x s :: behead (snoc s x).
Proof. by destruct s. Qed.

Implicit Arguments nthP [T s x].
Implicit Arguments has_nthP [T a s].
Implicit Arguments all_nthP [T a s].
(* Prenex Implicits nthP has_nthP all_nthP. *)

(*
Definition bitlist := list bool.
Canonical Structure bitlist_eqType := Eval hnf in [eqType of bitlist].
Canonical Structure bitlist_predType := Eval hnf in [predType of bitlist].
*)

(* Incrementing the ith nat in a list nat, padding with 0's if needed. This  *)
(* allows us to use nat lists as bags of nats.                               *)

Fixpoint incr_nth (v : list nat) (i : nat) {struct i} : list nat :=
  match v, i with
    | n :: v', 0 => S n :: v'
    | n :: v', S i' => n :: incr_nth v' i'
    | nil, _ => ncons i 0 (1 :: nil)
  end.

Lemma nth_incr_nth : forall v i j,
  nth 0 (incr_nth v i) j = (if i == j then 1 else 0) + nth 0 v j.
Proof.
induction v; intros [|i] [|j]; clarsimp. 
induction[j] i [j]; clarsimp.
Qed.

Lemma length_incr_nth : forall v i,
  length (incr_nth v i) = if i < length v then length v else S i.
Proof.
 induction v; intros [|i]; clarsimp; f_equal.
 - induction i; simpls; congruence.
 - by rewrite <- fun_if, IHv.
Qed.

(* equality up to permutation *)

Section PermSeq.

Variable T : eqType.

Notation cou1 := (fun x => count (fun y => y == x)). 

Definition same_count1 (s1 s2 : list T) x :=
   count (fun y => y == x) s1 == count (fun y => y == x) s2.

Definition perm_eq (s1 s2 : list T) := all (same_count1 s1 s2) (s1 ++ s2).

Lemma perm_eqP_weak : forall s1 s2,
  reflect (cou1 ^~ s1 =1 cou1 ^~ s2) (perm_eq s1 s2).
Proof.
  intros; apply (iffP allP); try red; intros.
  2: by unfold same_count1; rewrite H; case eqP.
  unfold same_count1 in *.
    destruct (has (fun y => y == x) s1) as [] _eqn: E1.
      rewrite has_pred1 in *; exploit (H x); 
      [by clarsimp|by case eqP].
    destruct (has (fun y => y == x) s2) as [] _eqn: E2.
      rewrite has_pred1 in *; exploit (H x); 
      [by clarsimp|by case eqP].
    rewrite has_filter in *.
    by rewrite !count_filter, (eqP _ _ (negbFE E1)), (eqP _ _ (negbFE E2)).
Qed.

Lemma perm_eq_refl : forall s, perm_eq s s.
Proof. by intros; apply/perm_eqP_weak. Qed.
Hint Resolve perm_eq_refl.

Lemma perm_eq_sym : symmetric perm_eq.
Proof. intros s1 s2; apply/perm_eqP_weak/perm_eqP_weak; red; auto using fsym. Qed.

Lemma perm_eq_trans : transitive perm_eq.
Proof.
  red; intros; apply/perm_eqP_weak; intros.
  eapply ftrans, (perm_eqP_weak _ _ H0).
  eapply (perm_eqP_weak _ _ H).
Qed.

Notation perm_eql := (fun s1 s2 => perm_eq s1 =1 perm_eq s2).
Notation perm_eqr := (fun s1 s2 => perm_eq^~ s1 =1 perm_eq^~ s2).

Lemma perm_eqlP : forall s1 s2, reflect (perm_eql s1 s2) (perm_eq s1 s2).
Proof.
  intros; apply (iffP (idP _)); [|by intros X; rewrite X].
  split/; [rewrite perm_eq_sym in H|]; eauto using perm_eq_trans. 
Qed.

Lemma perm_eqrP : forall s1 s2, reflect (perm_eqr s1 s2) (perm_eq s1 s2).
Proof.
  intros; apply (iffP (idP _)); [|by intros X; rewrite <- X].
  split/; rewrite !(perm_eq_sym x); 
    [rewrite perm_eq_sym in H|]; eauto using perm_eq_trans. 
Qed.

Lemma perm_appC : forall s1 s2, perm_eql (s1 ++ s2) (s2 ++ s1).
Proof.
  ins; apply (elimT (perm_eqlP _ _)); apply/perm_eqP_weak; intro.
  rewrite ?count_app; omega.
Qed.

Lemma perm_app2l : forall s1 s2 s3,
  perm_eq (s1 ++ s2) (s1 ++ s3) = perm_eq s2 s3.
Proof.
  intros; apply/perm_eqP_weak/perm_eqP_weak; intros eq23 a.
    by rewrite !count_app, eq23.
  generalize (eq23 a); rewrite !count_app; intros; omega.
Qed.

Lemma perm_cons x s1 s2 : perm_eq (x :: s1) (x :: s2) = perm_eq s1 s2.
Proof. apply (perm_app2l (cons x nil)). Qed.

Lemma perm_app2r s1 s2 s3 : perm_eq (s2 ++ s1) (s3 ++ s1) = perm_eq s2 s3.
Proof. do 2 (rewrite perm_eq_sym, perm_appC); apply perm_app2l. Qed.

Lemma perm_appAC s1 s2 s3 : perm_eql ((s1 ++ s2) ++ s3) ((s1 ++ s3) ++ s2).
Proof.
  apply (elimT (perm_eqlP _ _)); apply/perm_eqP_weak; intro; rewrite !count_app; omega.
Qed.

Lemma perm_appCA s1 s2 s3 : perm_eql (s1 ++ s2 ++ s3) (s2 ++ s1 ++ s3).
Proof.
  apply (elimT (perm_eqlP _ _)); apply/perm_eqP_weak; intro; rewrite !count_app; omega.
Qed.

Lemma perm_snoc : forall x s, perm_eql (snoc s x) (x :: s).
Proof. by simpl; red; intros; rewrite snocE, perm_appC. Qed.

Lemma perm_rot : forall n s, perm_eql (rot n s) s.
Proof. by simpl; red; intros; unfold rot; rewrite perm_appC, app_take_drop. Qed.

Lemma perm_rotr : forall n s, perm_eql (rotr n s) s.
Proof. intros; apply perm_rot. Qed.

Lemma perm_eq_mem : forall s1 s2, perm_eq s1 s2 -> s1 =i s2.
Proof.
  by intros ? ?; move/perm_eqP_weak; intros eq12 x;
     rewrite <-!has_pred1, !has_count, eq12.
Qed.


(* NEW *)
Lemma perm_eq_nilD : forall s, perm_eq nil s -> s = nil.
Proof.
  destruct s; unfold perm_eq, same_count1; simpls; clarsimp.
Qed.

(* NEW *)
Lemma perm_eq_consD : forall x s1 s2,
  perm_eq (x :: s1) s2 -> exists sa sb, s2 = sa ++ x :: sb /\ perm_eq s1 (sa ++ sb).
Proof.
  intros; exploit (@in_split _ x s2).
    apply/@allP in H; exploit (H x); [by clarsimp|].
    unfold same_count1; simpl; rewrite eqxx; intro M; clarify.
    by rewrite <- has_pred1, has_count, <- M.
  intros; des; clarify; repeat eexists.
  rewrite perm_eq_sym, perm_appC in H; simpls.
  by rewrite perm_cons, perm_appC, perm_eq_sym in H.
Qed.

(* NEW / because of weaker perm_eqP *)
Lemma perm_eqD : forall s1 s2 (EQ: perm_eq s1 s2) f, count f s1 = count f s2.
Proof.
  induction[] s1; ins.
    eapply perm_eq_nilD in EQ; clarify.
  apply perm_eq_consD in EQ; desc; clarify.
  rewrite (IHs1 _ EQ0), !count_app; simpl; desf.
Qed.

Lemma perm_eq_length : forall s1 s2, perm_eq s1 s2 -> length s1 = length s2.
Proof. by intros; rewrite <-!count_predT; apply perm_eqD. Qed.


Lemma perm_eqP s1 s2 :
  reflect ((@count _) ^~ s1 =1 (@count _) ^~ s2) (perm_eq s1 s2).
Proof.
  generalize (@perm_eqD s1 s2). 
  case (perm_eqP_weak s1 s2); ins; constructor; intro; auto.
  by destruct n; intro; auto.
Qed.


Lemma uniq_leq_length : forall s1 s2 : list T,
  uniq s1 -> {subset s1 <= s2} -> length s1 <= length s2.
Proof.
  induction s1; ins; desc.
  case (@rot_to _ s2 a); try by apply H0.
  intros i ? EQ; rewrite <- (length_rot i s2), EQ; simpls.
  apply IHs1; red; ins.
  eapply (f_equal (fun y => x \in y)) in EQ.
  rewrite mem_rot, in_cons, H0 in EQ; try rewrite in_cons; vauto.
  destruct (eqP x a); vauto.
  case eqP; eauto.
Qed.

Lemma leq_length_uniq : forall s1 s2 : list T,
  uniq s1 -> {subset s1 <= s2} -> length s2 <= length s1 -> uniq s2.
Proof.
  induction s1; ins; desc; [by destruct s2|].
  case (@rot_to _ s2 a); try by apply H0.
  intros i ? EQ; rewrite <- (rot_uniq i), EQ; simpls.
  rewrite <- (length_rot i s2), EQ in *; simpls; split/.
    apply/negP; intro.
    assert (X: {subset a :: s1 <= s'}).
      red; ins; apply (f_equal (fun y => x \in y)) in EQ.
      rewrite in_cons in *; destruct (eqP x a); simpls; clarsimp.
      by rewrite <- EQ; apply H0; clarsimp; clarsimp.
    eapply uniq_leq_length in X; simpls; vauto.
    by generalize (len_trans H1 X); rewrite leSn, ltnn.
  eapply IHs1 in H1; red; ins; vauto. 
  eapply (f_equal (fun y => x \in y)) in EQ.
  rewrite mem_rot, in_cons, H0 in EQ; try rewrite in_cons; repeat clarsimp; vauto.
  destruct (eqP x a); repeat clarsimp; vauto.
Qed.

Lemma uniq_length_uniq : forall s1 s2 : list T,
  uniq s1 -> s1 =i s2 -> uniq s2 = (length s2 == length s1).
Proof.
  ins; rewrite eqn_leAle, andbC, uniq_leq_length; vauto; [|by intro; rewrite H0].
  apply/idP/idP.
    by eapply leq_length_uniq; auto; intro; rewrite H0. 
  by ins; eapply uniq_leq_length; auto; intro; rewrite H0. 
Qed.

Lemma leq_length_perm : forall s1 s2 : list T,
  uniq s1 -> {subset s1 <= s2} -> 
  length s2 <= length s1 ->
  s1 =i s2 /\ length s1 = length s2.
Proof.
  ins; assert (U2: uniq s2) by eauto using leq_length_uniq.
  cut (s1 =i s2).
    by split; [|apply/eqP; instantiate; rewrite <- uniq_length_uniq].
  intro x; apply/idP/idP; auto. 
  induction [s2 H0 H1 U2] s1; ins; [by destruct s2|]; clarify.
  pose proof (in_split_uniq (H0 _ (mem_head _ _)) U2); desf.
  clarsimp; revert H2; case eqP; ins. 
  eapply (IHs1 eq_refl (l1 ++ l2)); auto; clarsimp.
  by intro y; specialize (H0 y); clarsimp; revert H0; case eqP; ins; auto; clarsimp. 
Qed.

Lemma perm_uniq : forall s1 s2 : list T,
  s1 =i s2 -> length s1 = length s2 -> uniq s1 = uniq s2.
Proof.
  by ins; apply/idP/idP; intro Us; rewrite (uniq_length_uniq Us), ?H0.
Qed.

Lemma perm_eq_uniq : forall s1 s2, perm_eq s1 s2 -> uniq s1 = uniq s2.
Proof.
  by ins; apply perm_uniq; [apply perm_eq_mem | apply perm_eq_length].
Qed.

Lemma uniq_perm_eq : forall s1 s2,
  uniq s1 -> uniq s2 -> s1 =i s2 -> perm_eq s1 s2.
Proof.
  ins; apply/(@allP); intros x _.
  by unfold same_count1; rewrite !count_uniq_mem, H1. 
Qed.

Lemma count_mem_uniq : forall s : list T,
  (forall x, count (fun y => y == x) s = if (x \in s) then 1 else 0) -> uniq s.
Proof.
  ins.
  cut (perm_eq s (undup s)); [by move/perm_eq_uniq; intros ->|].
  apply/@allP; intros x _; unfold same_count1.
  by rewrite H, count_uniq_mem, mem_undup.
Qed.

End PermSeq.
(*
Notation perm_eql := (fun s1 s2 => perm_eq s1 =1 perm_eq s2).
Notation perm_eqr := (fun s1 s2 => perm_eq^~ s1 =1 perm_eq^~ s2).

Implicit Arguments perm_eqP [T s1 s2].
Implicit Arguments perm_eqlP [T s1 s2].
Implicit Arguments perm_eqrP [T s1 s2].
Prenex Implicits perm_eqP perm_eqlP perm_eqrP.
Hint Resolve perm_eq_refl.
*)

Section RotrLemmas.

Variables (n0 : nat) (T : Type) (T' : eqType).

Lemma length_rotr : forall s : list T, length (rotr n0 s) = length s.
Proof. by intros; unfold rotr; rewrite length_rot. Qed.

Lemma mem_rotr : forall s : list T', rotr n0 s =i s.
Proof. intros; apply mem_rot. Qed.

Lemma rotr_size_app : forall s1 s2 : list T,
  rotr (length s2) (s1 ++ s2) = s2 ++ s1.
Proof. intros; unfold rotr; clarsimp; rewrite <- addn_subA; clarsimp. Qed. 

Lemma rotr1_snoc : forall x (s : list T), rotr 1 (snoc s x) = x :: s.
Proof. by intros; rewrite <- rot1_cons, rotK. Qed.

Lemma has_rotr : forall f (s : list T), has f (rotr n0 s) = has f s.
Proof. intros; apply has_rot. Qed.

Lemma rotr_uniq : forall s : list T', uniq (rotr n0 s) = uniq s.
Proof. intros; apply rot_uniq. Qed.

Lemma rotrK : cancel (rotr n0) (@rot T n0).
Proof.
  intros s; case (ltnP n0 (length s)); intro Hs. 
  - rewrite <-(subKn (ltnW Hs)) at 1.
    by rewrite <-(length_rotr) at 1; apply rotK.
  - rewrite <-(rot_overlength Hs) at 2.
    by unfold rotr; rewrite <-subn_eq0 in Hs; rewrite (eqP _ _ Hs), rot0.
Qed.

Lemma rotr_inj : injective (@rotr T n0).
Proof. exact (can_inj rotrK). Qed.

Lemma rev_rot : forall s : list T, rev (rot n0 s) = rotr n0 (rev s).
Proof.
  unfold rotr; intros; clarsimp.
  rewrite <- (app_take_drop n0 s) at 3; unfold rot at 1.
  by rewrite !rev_app, <- length_drop, <- length_rev, rot_length_app.
Qed.

Lemma rev_rotr : forall s : list T, rev (rotr n0 s) = rot n0 (rev s).
Proof. intros; rewrite <- (rev_rev s), <- rev_rot; clarsimp. Qed.

End RotrLemmas.

Hint Rewrite length_rotr rotr_size_app rotr1_snoc has_rotr : vlib.

(*
Section RotCompLemmas.

Variable T : Type.

Lemma rot_addn : forall m n (s : list T), m + n <= length s ->
  rot (m + n) s = rot m (rot n s).
Proof.
move=> m n s; rewrite leq_eqVlt; case/predU1P=> [Emn|Hmn].
  by rewrite Emn rot_size -{1}(rotrK m s) /rotr -Emn addKn.
rewrite -{1}(cat_take_drop n s) /rot !take_cat !drop_cat.
rewrite addnC in Hmn; have Hn := leq_trans (leq_addr _ _) (ltnW Hmn).
rewrite (size_takel Hn) ltnNge leq_addl addnK /= catA.
by rewrite ltnNge size_drop leq_sub_add -ltnNge Hmn.
Qed.

Lemma rotS : forall n (s : list T), n < size s -> rot n.+1 s = rot 1 (rot n s).
Proof. exact: rot_addn 1. Qed.

Lemma rot_add_mod : forall m n (s : list T), n <= size s -> m <= size s ->
  rot m (rot n s) = rot (if m + n <= size s then m + n else m + n - size s) s.
Proof.
move=> m n s Hn Hm; case: leqP; [by move/rot_addn | move/ltnW=> Hmn].
symmetry.
by rewrite -{2}(rotK n s) /rotr -rot_addn size_rot addn_subA ?subnK ?addnK.
Qed.

Lemma rot_rot : forall m n (s : list T), rot m (rot n s) = rot n (rot m s).
Proof.
move=> m n s; case: (ltnP (size s) m) => Hm.
  by rewrite !(@rot_oversize T m) ?size_rot 1?ltnW.
case: (ltnP (size s) n) => Hn.
  by rewrite !(@rot_oversize T n) ?size_rot 1?ltnW.
by rewrite !rot_add_mod 1?addnC.
Qed.

Lemma rot_rotr : forall m n (s : list T), rot m (rotr n s) = rotr n (rot m s).
Proof. by move=> *; rewrite {2}/rotr size_rot rot_rot. Qed.

Lemma rotr_rotr : forall m n (s : list T),
  rotr m (rotr n s) = rotr n (rotr m s).
Proof. by move=> *; rewrite /rotr !size_rot rot_rot. Qed.

End RotCompLemmas.
*)

Section Sieve.

Variables (n0 : nat) (T : Type).

Implicit Types l s : list T.

Lemma sieve_false : forall s n, sieve (nlist n false) s = nil.
Proof. by induction s; destruct n; simpl; try apply IHs. Qed.

Lemma sieve_true : forall s n, length s <= n -> sieve (nlist n true) s = s.
Proof.
  induction s; destruct n; simpl; try done; intros; (try by inv H).
  f_equal; apply IHs; auto with arith.
Qed.

Lemma sieve0 : forall m, sieve m nil = (@nil T).
Proof. by intros []. Qed.

(*
Lemma sieve1 : forall b x, sieve (b :: nil) (x :: nil) = nlist b x.
Proof. by case. Qed.
*)

Lemma sieve_cons : forall b m x s,
  sieve (b :: m) (x :: s) = (if b then (x :: nil) else nil) ++ sieve m s.
Proof. by intros []. Qed.

Lemma length_sieve : forall m s,
  length m = length s -> length (sieve m s) = count id m.
Proof. induct[] m [s]. Qed.

Lemma sieve_app : forall m1 s1, length m1 = length s1 ->
  forall m2 s2, sieve (m1 ++ m2) (s1 ++ s2) = sieve m1 s1 ++ sieve m2 s2.
Proof. induct[] m1 [s1]. Qed.

Lemma has_sieve_cons : forall a b m x s,
  has a (sieve (b :: m) (x :: s)) = b && a x || has a (sieve m s).
Proof. by destruct b. Qed.

Lemma sieve_rot : forall m s, length m = length s ->
 sieve (rot n0 m) (rot n0 s) = rot (count id (take n0 m)) (sieve m s).
Proof.
 intros.
  assert (length (take n0 m) = length (take n0 s)).
  by rewrite !length_take, H.
  rewrite <- (length_sieve H0).
  unfold rot at 1 2; rewrite sieve_app; rewrite ?length_drop; eauto.
  rewrite <- (app_take_drop n0 m) at 4.
  rewrite <- (app_take_drop n0 s) at 4.
  by rewrite sieve_app, rot_length_app.
Qed.

End Sieve.

Section EqSieve.

Variables (n0 : nat) (T : eqType).

Lemma mem_sieve_cons x b m y (s : list T) :
  (x \in sieve (b :: m) (y :: s)) = b && (x == y) || (x \in sieve m s).
Proof. by case b. Qed.

Lemma mem_sieve : forall x m (s : list T), (x \in sieve m s) -> (x \in s).
Proof.
  induct[x m] s [m]; desf; rewrite ?in_cons in *; clarsimp;
  [case/: H|]; intros; clarify; erewrite IHs; eauto; clarsimp.
Qed.

Lemma sieve_uniq : forall s : list T, uniq s -> forall m, uniq (sieve m s).
Proof.
  induction[] s [m]; ins; desf; simpl; eauto.
  apply/andP; split; eauto.
  by apply/negP; intro X; rewrite (mem_sieve X) in *.
Qed.

Lemma mem_sieve_rot : forall m (s : list T), length m = length s ->
  sieve (rot n0 m) (rot n0 s) =i sieve m s.
Proof. by red; ins; rewrite sieve_rot, mem_rot. Qed.

End EqSieve.

Section Map.

Variables (n0 : nat) (T1 : Type) (x1 : T1).
Variables (T2 : Type) (x2 : T2) (f : T1 -> T2).

Fixpoint map (l : list T1) : list T2 :=
  match l with
    | nil => nil
    | x :: l => f x :: map l
  end.

Lemma map_cons : forall x s, map (x :: s) = f x :: map s.
Proof. done. Qed.

Lemma map_nlist : forall x, map (nlist n0 x) = nlist n0 (f x).
Proof. unfold nlist, ncons; induction n0; simpl; congruence. Qed.

Lemma map_app : forall s1 s2, map (s1 ++ s2) = map s1 ++ map s2.
Proof. by intros; induction s1; simpl; [|rewrite IHs1]. Qed.

Lemma map_snoc : forall s x, map (snoc s x) = snoc (map s) (f x).
Proof. by intros; rewrite !snocE, map_app. Qed.

Lemma length_map : forall l, length (map l) = length l.
Proof. by induction l; simpl; [|rewrite IHl]. Qed.

Lemma behead_map : forall l, behead (map l) = map (behead l).
Proof. by intros[]. Qed.

Lemma nth_map : forall n l, n < length l -> nth x2 (map l) n = f (nth x1 l n).
Proof.
  induction[n] l; destruct n; simpl; try (by inversion 1).
  auto with arith.
Qed.

Lemma last_map : forall s x, last (f x) (map s) = f (last x s).
Proof. by induction s; simpl. Qed.

Lemma belast_map : forall s x, belast (f x) (map s) = map (belast x s).
Proof. by induction s; simpl; [|rewrite IHs]. Qed.

Lemma filter_map a s : filter a (map s) = map (filter (preim f a) s).
Proof. by induction s; simpls; rewrite (fun_if map), IHs. Qed.

Lemma find_map a s : find a (map s) = find (preim f a) s.
Proof. induct s. Qed. 

Lemma has_map a s : has a (map s) = has (preim f a) s.
Proof. induct s. Qed. 

Lemma count_map a s : count a (map s) = count (preim f a) s.
Proof. induct s. Qed.

Lemma map_take s : map (take n0 s) = take n0 (map s).
Proof. induct[s] n0 [s]. Qed.

Lemma map_drop s : map (drop n0 s) = drop n0 (map s).
Proof. induct[s] n0 [s]. Qed.

Lemma map_rot s : map (rot n0 s) = rot n0 (map s).
Proof. by unfold rot; rewrite map_app, map_take, map_drop. Qed.

Lemma map_rotr s : map (rotr n0 s) = rotr n0 (map s).
Proof. by apply (canRL (@rotK n0 T2)); rewrite <-map_rot, rotrK. Qed.

Lemma map_rev s : map (rev s) = rev (map s).
Proof. by induction s; ins; rewrite !rev_cons, !snocE, map_app, IHs. Qed.

Lemma map_sieve m s : map (sieve m s) = sieve m (map s).
Proof. by induction[s] m [s]; simpls; case a; simpl; rewrite IHm. Qed.

Lemma inj_map (Hf : injective f) : injective map.
Proof. induction x0; intros []; clarsimp; f_equal; autos. Qed.

End Map.

Hint Rewrite map_nlist map_app map_snoc length_map 
  behead_map last_map belast_map map_take map_drop
  map_rot map_rev map_sieve map_rotr : vlib. 


(** * [map2] and its properties *) 

Section Map2.

Variables (n0 : nat) (T1 : Type) (x1 : T1).
Variables (T2 : Type) (x2 : T2).
Variables (T3 : Type) (f : T1 -> T2 -> T3).

Fixpoint map2 (l1 : list T1) (l2 : list T2) {struct l1}: list T3 :=
  match l1, l2 with
    | nil, _             => nil
    | x1 :: l1, nil      => nil
    | x1 :: l1, x2 :: l2 => f x1 x2 :: map2 l1 l2
  end.

Lemma map2_0l : forall l, map2 nil l = nil.
Proof. done. Qed.
Lemma map2_l0 : forall l, map2 l nil = nil.
Proof. by destruct l. Qed.

Lemma map2_cons : forall x1 l1 x2 l2, map2 (x1 :: l1) (x2 :: l2) = f x1 x2 :: map2 l1 l2.
Proof. done. Qed.

Lemma map2_nlist : forall x y, map2 (nlist n0 x) (nlist n0 y) = nlist n0 (f x y).
Proof. unfold nlist, ncons; intros; induction n0; simpl; congruence. Qed.

Lemma map2_app : forall s1 s2 t1 t2 (Leq: length s1 = length t1),
  map2 (s1 ++ s2) (t1 ++ t2) = map2 s1 t1 ++ map2 s2 t2.
Proof. by induction[] s1 [t1]; ins; clarify; rewrite IHs1. Qed.

Lemma length_map2_eq : forall l1 l2, length l1 = length l2 -> 
  length (map2 l1 l2) = (length l1).
Proof. by induction[] l1 [l2]; ins; clarify; rewrite IHl1. Qed.

Lemma map2_take :
  forall l1 l2, map2 (take n0 l1) (take n0 l2) = take n0 (map2 l1 l2).
Proof.
  by induction n0; destruct l1; destruct l2; simpl; try done; rewrite IHn.
Qed.

Lemma map2_drop :
  forall l1 l2, map2 (drop n0 l1) (drop n0 l2) = drop n0 (map2 l1 l2).
Proof.
  by induction n0; destruct l1; destruct l2; simpl; rewrite ?map2_l0.
Qed.

Lemma map2_rot l1 l2 (Leq: length l1 = length l2) :
    map2 (rot n0 l1) (rot n0 l2) = rot n0 (map2 l1 l2).
Proof.
  intros; unfold rot; rewrite map2_app, map2_take, map2_drop; try done.
  rewrite ?length_drop; congruence.
Qed.

End Map2.

Lemma map2I : 
  forall {T1} {f: T1 -> T1 -> T1} (Cf: forall x, f x x = x) x,
    map2 f x x = x.
Proof. by induction x; try done; simpl; f_equal. Qed.

Lemma map2C : 
  forall {T1 T2} {f: T1 -> T1 -> T2} (Cf: forall x y, f x y = f y x) x y,
    map2 f x y = map2 f y x.
Proof. by induction x; destruct y; try done; simpl; f_equal. Qed.

Lemma map2A : 
  forall {T1} {f: T1 -> T1 -> T1} (Cf: forall x y z, f x (f y z) = f (f x y) z) x y z,
    map2 f x (map2 f y z) = map2 f (map2 f x y) z.
Proof. by induction x; destruct y; destruct z; try done; simpl; f_equal. Qed.

Lemma map2K : 
  forall {T1 T2} {f: T1 -> T1 -> T2} {v} (Cf: forall x, f x x = v) x,
    map2 f x x = nlist (length x) v.
Proof. by unfold nlist, ncons; induction x; try done; simpl; f_equal. Qed.

Lemma map2Kl : 
  forall {T1 T2 T3} {f: T1 -> T2 -> T3} {v1 v2} (Cf: forall x, f v1 x = v2) 
    n x (Leq: length x = n),
    map2 f (nlist n v1) x = nlist n v2.
Proof. 
  unfold nlist, ncons; induction n; destruct x; simpl; 
  intros; clarify; f_equal; auto.
Qed.

Lemma map2Il : 
  forall {T1 T2} {f: T1 -> T2 -> T2} {v1} (Cf: forall x, f v1 x = x)
    n x (Leq: length x = n),
    map2 f (nlist n v1) x = x.
Proof. 
  unfold nlist, ncons; induction n; destruct x; simpl; 
  intros; clarify; f_equal; auto.
Qed.

Lemma map2Sl : 
  forall {T1 T2} {f: T1 -> T1 -> T2} {v g} (Cf: forall x, f v x = g x)
    n x (Leq: length x = n),
    map2 f (nlist n v) x = map g x.
Proof.
  unfold nlist, ncons; induction n; destruct x; simpl; 
  intros; clarify; f_equal; auto.
Qed.


Section EqMap.

Variables (n0 : nat) (T1 : eqType) (x1 : T1).
Variables (T2 : eqType) (x2 : T2) (f : T1 -> T2).

Lemma map_f : forall (s : list T1) x, x \in s -> f x \in map f s.
Proof.
induction s; clarsimp.
destruct (eqP x a); clarsimp.
rewrite IHs; clarsimp.
Qed.

Lemma mapP : forall (s : list T1) y,
  reflect (exists2 x, x \in s & y = f x) (y \in map f s).
Proof.
induction s; clarsimp; [by right; intros []|].
case (eqP); clarsimp.
  by left; exists a; clarsimp.
apply (iffP (IHs y)); intros []; clarsimp; exists x; clarsimp;
destruct (eqP x a); clarsimp.
Qed.

Lemma map_uniq : forall s, uniq (map f s) -> uniq s.
Proof.
induction s; clarsimp; des. 
split/; [apply/; intro; rewrite map_f in *|]; intuition.
Qed.

Lemma map_inj_in_uniq : forall s : list T1,
  {in s &, injective f} -> uniq (map f s) = uniq s.
Proof.
  split/; eauto using map_uniq.
  induction s; ins; desf.
  apply/andP; split.
    apply/negP; intro X. generalize (mapP _ _ X).
    by intros [? ? M]; eapply H in M; repeat clarsimp.
  apply IHs; eauto; red; intros; apply H; repeat clarsimp.
Qed.

Hypothesis Hf : injective f.

Lemma mem_map : forall s x, (f x \in map f s) = (x \in s).
Proof. 
  induct s; rewrite IHs; repeat case eqP; ins; clarify; exfalso; eauto. 
Qed.

Lemma index_map : forall s x, index (f x) (map f s) = index x s.
Proof. unfold index; induction s; clarsimp; desf; clarify; eauto; exfalso; eauto. Qed.

Lemma map_inj_uniq : forall s, uniq (map f s) = uniq s.
Proof. by induction s; clarsimp; rewrite mem_map, IHs. Qed.

End EqMap.

Implicit Arguments mapP [T1 T2 f s y].
(* Prenex Implicits mapP. *)

Lemma filter_sieve : forall T a (s : list T), filter a s = sieve (map a s) s.
Proof. by induction s; clarsimp; rewrite IHs. Qed.

Section MapComp.

Variable T1 T2 T3 : Type.

Lemma map_id : forall s : list T1, map id s = s.
Proof. by induction s; simpls; rewrite IHs. Qed.

Lemma eq_map : forall f1 f2 : T1 -> T2, f1 =1 f2 -> map f1 =1 map f2.
Proof. red; induction x; clarsimp; f_equal; clarsimp. Qed.

Lemma map_comp : forall (f1 : T2 -> T3) (f2 : T1 -> T2) s,
  map (f1 \o f2) s = map f1 (map f2 s).
Proof. induction s; clarsimp; f_equal; clarsimp. Qed. 

Lemma mapK : forall (f1 : T1 -> T2) (f2 : T2 -> T1),
  cancel f1 f2 -> cancel (map f1) (map f2).
Proof. red; induction x; clarsimp; f_equal; clarsimp. Qed.

End MapComp.

Lemma eq_in_map : forall (T1 : eqType) T2 (f1 f2 : T1 -> T2) (s : list T1),
  {in s, f1 =1 f2} -> map f1 s = map f2 s.
Proof.
  by induction s; ins; f_equal; try apply IHs; try red; intros; apply H; clarsimp; clarsimp. 
Qed.

Lemma map_id_in : forall (T : eqType) f (s : list T),
  {in s, f =1 id} -> map f s = s.
Proof. intros; apply eq_in_map in H; rewrite H; apply map_id. Qed.

(* Map a partial function *)

Section Pmap.

Variables (aT rT : Type) (f : aT -> option rT) (g : rT -> aT).

Fixpoint pmap s :=
  match s with
    | nil => nil
    | x :: s' => oapp ((@cons _)^~ (pmap s')) (pmap s') (f x)
  end.

Lemma map_pK : pcancel g f -> cancel (map g) pmap.
Proof. by red; induction x; ins; rewrite H, IHx. Qed.

Lemma length_pmap s : 
  length (pmap s) = count (fun x => match f x with None => false | Some _ => true end) s.
Proof. induction s; ins; desf; simpls; auto. Qed.

Lemma pmapS_filter s : 
  map some (pmap s) 
  = map f (filter (fun x => match f x with None => false | Some _ => true end) s).
Proof. induction s; ins; desf; simpls; congruence. Qed.

Lemma pmap_filter (fK : ocancel f g) s : 
  map g (pmap s) = filter (fun x => match f x with None => false | Some _ => true end) s.
Proof. induction s; ins; specialize (fK a); desf; simpls; congruence. Qed.

End Pmap.

(*
Section EqPmap.

Variables (aT rT : eqType) (f : aT -> option rT) (g : rT -> aT).

Lemma eq_pmap : forall (f1 f2 : aT -> option rT),
 f1 =1 f2 -> pmap f1 =1 pmap f2.
Proof. by induction x; ins; rewrite IHx, H. Qed.

Lemma mem_pmap s u : (u \in pmap f s) = (Some u \in map f s).
Proof.
  induction s; ins; rewrite in_cons; case (f a); ins.
  rewrite in_cons; do 2 case eqP; ins; clarify.
Qed.

Hypothesis fK : ocancel f g.

Lemma can2_mem_pmap (gK : pcancel g f) s u : (u \in pmap f s) = (g u \in s).
Proof.
  by ins; rewrite <-(mem_map (pcan_inj gK)), pmap_filter, mem_filter, gK.
Qed.

Lemma pmap_uniq s : uniq s -> uniq (pmap f s).
Proof.
  move/(@filter_uniq); rewrite <-(pmap_filter fK); apply map_uniq.
Qed.
 
End EqPmap.
*)
(*
Section Pmapub.

Variables (T : Type) (p : pred T) (sT : subType p).

Let insT : T -> option sT := insub.

Lemma size_pmap_sub s : size (pmap insT s) = count p s.
Proof. by rewrite size_pmap (eq_count (isSome_insub _)). Qed.

End Pmapub.

Section EqPmapSub.

Variables (T : eqType) (p : pred T) (sT : subType p).

Let insT : T -> option sT := insub.

Lemma mem_pmap_sub (s : list T) u : (u \in pmap insT s) = (val u \in s).
Proof. apply: (can2_mem_pmap (insubK _)); exact: valK. Qed.

Lemma pmap_sub_uniq : forall s : list T, uniq s -> uniq (pmap insT s).
Proof. exact: (pmap_uniq (insubK _)). Qed.

End EqPmapSub.
*)

(** ** Index sequence *)

Lemma length_iota : forall m n, length (iota m n) = n.
Proof. by induction[m] n; intros; simpl; try done; rewrite IHn. Qed.

Lemma iota_add : forall m n1 n2,
  iota m (n1 + n2) = iota m n1 ++ iota (m + n1) n2.
Proof. by induction[m] n1; clarsimp; rewrite IHn1. Qed.

Lemma iota_addl : forall m1 m2 n,
  iota (m1 + m2) n = map (plus m1) (iota m2 n).
Proof.
induction[m2] n; clarsimp; rewrite <- IHn; clarsimp.
Qed.

Lemma nth_iota : forall n0 m n i, i < n -> nth n0 (iota m n) i = m + i.
Proof. by induction[m] n; destruct i; clarsimp; apply IHn. Qed.

Lemma mem_iota : forall m n i, (i \in iota m n) = (m <= i) && (i < m + n).
Proof.
induction[m] n; clarsimp; [by case cmpP|].
rewrite IHn; case (cmpP i m); clarsimp.
by rewrite ltnE, ltnW.
Qed.

Lemma iota_uniq : forall m n, uniq (iota m n).
Proof. induction[m] n; clarsimp; rewrite mem_iota; clarsimp. Qed.

Hint Resolve iota_uniq : vlib.
Hint Rewrite length_iota mem_iota iota_uniq : vlib.

(* Making a list of a specific length, using indexes to compute items. *)

Section MakeSeq.

Variables (T : Type) (x0 : T).

Definition mklist f n : list T := map f (iota 0 n).

Lemma length_mklist : forall f n, length (mklist f n) = n.
Proof. by intros; unfold mklist; rewrite length_map, length_iota. Qed.

Lemma eq_mklist : forall f g, f =1 g -> mklist f =1 mklist g.
Proof. by red; intros; apply eq_map. Qed.

Lemma nth_mklist : forall f n i, i < n -> nth x0 (mklist f n) i = f i.
Proof.
by intros; unfold mklist; rewrite (nth_map 0), nth_iota; rewrite ?length_iota.
Qed.

Lemma mklist_nth : forall s, mklist (nth x0 s) (length s) = s.
Proof.
  intros; apply (@eq_from_nth _ x0); rewrite length_mklist; try done.
  by intros; apply nth_mklist.
Qed.

End MakeSeq.

Lemma mklist_uniq : forall (T : eqType) (f : nat -> T) n,
  injective f -> uniq (mklist f n).
Proof. by unfold mklist; ins; rewrite map_inj_uniq, iota_uniq. Qed.

Section FoldRight.

Variables (T R : Type) (f : T -> R -> R).

Fixpoint foldr (l : list T) (z0: R) : R := 
  match l with
    | nil => z0
    | x :: l => f x (foldr l z0) 
  end.

End FoldRight.

Section FoldRightComp.

Variables (T1 T2 : Type) (h : T1 -> T2).
Variables (R : Type) (f : T2 -> R -> R) (z0 : R).

Lemma foldr_app :
  forall s1 s2, foldr f (s1 ++ s2) z0 = foldr f s1 (foldr f s2 z0).
Proof. by intros; induction s1; simpls; rewrite IHs1. Qed.

Lemma foldr_map :
  forall s : list T1, foldr f (map h s) z0 = foldr (fun x z => f (h x) z) s z0.
Proof. by induction s; simpls; rewrite IHs. Qed.

End FoldRightComp.

Definition sumn l := foldr plus l 0.

Lemma sumn_nil : sumn nil = 0.
Proof. done. Qed.

Lemma sumn_cons : forall n l, sumn (n :: l) = n + sumn l.
Proof. done. Qed.

Hint Rewrite sumn_nil sumn_cons : vlib.

Lemma sumn_nlist : forall x n : nat, sumn (nlist n x) = x * n.
Proof. 
intros; rewrite mulnC; unfold nlist, ncons, sumn.
by induction n; clarsimp; rewrite IHn.
Qed.

Lemma sumn_app : forall s1 s2, sumn (s1 ++ s2) = sumn s1 + sumn s2.
Proof. by unfold sumn; induction s1; clarsimp; rewrite IHs1, addnA. Qed.

Lemma natnlist0P : forall s : list nat,
  reflect (s = nlist (length s) 0) (sumn s == 0).
Proof.
unfold sumn, nlist, ncons.
induction s; clarsimp; [by constructor; clarsimp|].
rewrite <- eqnE in *; destruct IHs; clarsimp.
case eqnP; constructor; congruence.
constructor; congruence.
Qed.

Section FoldLeft.

Variables (T R : Type) (f : R -> T -> R).

Fixpoint foldl z (l : list T) :=
  match l with
    | nil => z
    | x :: l => (foldl (f z x) l) 
  end.

Lemma foldl_rev : forall z s, foldl z (rev s) = foldr (fun x z => f z x) s z.
Proof.
  intros; revert z; pattern s; apply (last_ind); intros; simpl; try done.
  by rewrite rev_snoc, <- appl1, foldr_app, <- H.
Qed.

Lemma foldl_app : forall z s1 s2, foldl z (s1 ++ s2) = foldl (foldl z s1) s2.
Proof.
  intros; rewrite <- (rev_rev (s1 ++ s2)), foldl_rev, rev_app. 
  by rewrite foldr_app, <- !foldl_rev, !rev_rev.
Qed.

End FoldLeft.

Section Scan.

Variables (T1 : Type) (x1 : T1) (T2 : Type) (x2 : T2).
Variables (f : T1 -> T1 -> T2) (g : T1 -> T2 -> T1).

Fixpoint pairmap x (s : list T1) {struct s} :=
  match s with
    | nil => nil
    | y :: s' => f x y :: pairmap y s' 
  end.

Lemma length_pairmap : forall x s, length (pairmap x s) = length s.
Proof. induct[x] s. Qed.

Lemma nth_pairmap : forall s n, n < length s ->
  forall x, nth x2 (pairmap x s) n = f (nth x1 (x :: s) n) (nth x1 s n).
Proof. induct s [n]. Qed.

Fixpoint scanl x (s : list T2) {struct s} :=
  match s with
    | nil => nil
    | y :: s' => let x' := g x y in x' :: scanl x' s' 
  end.

Lemma length_scanl : forall x s, length (scanl x s) = length s.
Proof. induct[x] s. Qed. 

Lemma nth_scanl : forall s n, n < length s ->
  forall x, nth x1 (scanl x s) n = foldl g x (take (S n) s).
Proof. induct s [n]. Qed.

Lemma scanlK :
  (forall x, cancel (g x) (f x)) -> forall x, cancel (scanl x) (pairmap x).
Proof. induct[x] x0; rewrite H; hacksimp. Qed. 

Lemma pairmapK : 
  (forall x, cancel (f x) (g x)) -> forall x, cancel (pairmap x) (scanl x).
Proof. induct[x] x0; rewrite H; hacksimp. Qed. 

End Scan.

(* Prenex Implicits sieve map pmap foldr foldl scanl pairmap. *)

Section Zip.

Variables T1 T2 : Type.

Fixpoint zip (s1 : list T1) (s2 : list T2) {struct s2} :=
  match s1, s2 with
  | x1 :: s1', x2 :: s2' => (x1,x2) :: zip s1' s2'
  | _, _ => nil
  end.

Definition unzip1 := map (@fst T1 T2).
Definition unzip2 := map (@snd T1 T2).

Lemma zip_unzip : forall s, zip (unzip1 s) (unzip2 s) = s.
Proof. by induction s as [|[x1 x2] s IH]; simpl; [|rewrite IH]. Qed.

Lemma unzip1_zip : forall s1 s2,
  length s1 <= length s2 -> unzip1 (zip s1 s2) = s1.
Proof. induct s1 [s2]. Qed.

Lemma unzip2_zip : forall s1 s2,
  length s2 <= length s1 -> unzip2 (zip s1 s2) = s2.
Proof. induct s1 [s2]. Qed.

Lemma length1_zip : forall s1 s2,
  length s1 <= length s2 -> length (zip s1 s2) = length s1.
Proof. induct s1 [s2]. Qed.

Lemma length2_zip : forall s1 s2,
  length s2 <= length s1 -> length (zip s1 s2) = length s2.
Proof. induct s1 [s2]. Qed.

End Zip.

(* Prenex Implicits zip unzip1 unzip2. *)

Section Flatten.

Variable T : Type.

Definition flatten l := foldr (@app _) l (@nil T).
Definition shape := map (@length T).
Fixpoint reshape (sh : list nat) (s : list T) {struct sh} :=
  match sh with
    | nil => nil
    | n :: sh' => take n s :: reshape sh' (drop n s)
  end.

Lemma flatten_cons : forall l ll, flatten (l :: ll) = l ++ flatten ll.
Proof. done. Qed.

Lemma flatten_app : forall l l', flatten (l ++ l') = flatten l ++ flatten l'.
Proof. by induction l; ins; rewrite !flatten_cons, IHl, appA. Qed.

Hint Rewrite flatten_cons flatten_app : vlib.

Lemma length_flatten : forall ss, length (flatten ss) = sumn (shape ss).
Proof. induct ss. Qed.

Lemma flattenK : forall ss, reshape (shape ss) (flatten ss) = ss.
Proof.
by unfold flatten; induction ss; simpls; rewrite take_length_app, drop_length_app, IHss.
Qed.

Lemma reshapeKr : forall sh s, length s <= sumn sh -> flatten (reshape sh s) = s.
Proof.
induction sh; clarsimp; [by destruct s|rewrite IHsh, app_take_drop; clarsimp].
Qed.

Lemma reshapeKl : forall sh s, length s >= sumn sh -> shape (reshape sh s) = sh.
Proof.
  induction sh; clarsimp.
  case (ltnP); clarsimp.
  rewrite IHsh; clarsimp.
  rewrite <- (len_add2l a), subnKC; autos.
  assert (X := len_sub2 H H0); clarsimp. 
  rewrite X in *; clarsimp.
  destruct (cmpP a (length s)); hacksimp. 
Qed.

End Flatten.

(* Prenex Implicits flatten shape reshape. *)

Inductive has_spec T (f : T -> bool) (l : list T) : Prop :=
  HasSpec (l1 l2: list T) (n : T) (EQ: l = l1 ++ n :: l2) (HOLDS : f n) (PREV: has f l1 = false).

Lemma hasD T (f : T -> bool) l (H: has f l): has_spec f l.
Proof.
  induction l; clarsimp.
  case_eq (f a); clarsimp.
    by eapply (HasSpec (l1:=nil)); simpls.
  destruct IHl; clarsimp.
  eapply (HasSpec (l1 := a :: l1)); clarsimp.
Qed.

Inductive in_spec {T : eqType} (x : T) (l : list T) : Prop :=
  InSpec (l1 l2: list T) (EQ: l = l1 ++ x :: l2) (PREV: x \notin l1).

Lemma inD {T: eqType} {x: T} {l} (H: x \in l): in_spec x l.
Proof.
  induction l; clarsimp.
  destruct (eqP x a); clarsimp. 
    by eapply (InSpec (l1 := nil)); simpls.
  destruct IHl; try eapply (InSpec (l1 := a :: l1)); clarsimp. 
  case eqP; clarsimp.
Qed.

Lemma uniqE (T: eqType) (l : list T) : 
  uniq l <-> (forall n l1 l2 l3, l = l1 ++ n :: l2 ++ n :: l3 -> False).
Proof.
  induction l; split; clarsimp.
  - by destruct l1.
  - destruct l1; simpls; clarify; [|eby eapply IHl].
    by clarsimp; simpls; rewrite eqnn in *; clarsimp.
  - apply/andP; split.
    * by apply/negP; intro X; case (inD X); clarsimp; eapply (H a nil).
    * by apply IHl; clarsimp; eapply (H _ (a :: l1)).
Qed.



(** Properties of [In] *)

Lemma In_eq : forall A (a:A) (l:list A), In a (a :: l).
Proof. vauto. Qed.

Lemma In_cons : forall A (a b:A) (l:list A), In b l -> In b (a :: l).
Proof. vauto. Qed.


Lemma In_nil : forall A (a:A), ~ In a nil.
Proof. by red. Qed.

Lemma In_split : forall A x (l:list A), In x l -> exists l1 l2, l = l1++x::l2.
Proof.
  induction l; simpl; intros; des; vauto.
  - exists nil; vauto.
  - destruct IHl; des; try done; eexists (_ :: _); vauto.
Qed.

Lemma In_dec :
  forall A (D: forall x y:A, {x = y} + {x <> y}) (a: A) l, {In a l} + {~ In a l}.
Proof.
  induction l; vauto; simpl; destruct (D a a0); intuition.
Qed.

Lemma In_appI1 : forall A (x:A) l (IN: In x l) l', In x (l++l').
Proof. induction l; ins; desf; eauto. Qed.

Lemma In_appI2 : forall A (x:A) l' (IN: In x l') l, In x (l++l').
Proof. induction l; ins; desf; eauto. Qed.

Lemma In_appD : forall A (x:A) l l' (IN: In x (l++l')), In x l \/ In x l'.
Proof. induction l; intuition. Qed.

Lemma In_app : forall A (x:A) l l', In x (l++l') <-> In x l \/ In x l'.
Proof. intuition; auto using In_appI1, In_appI2. Qed.

Lemma In_rev : forall A (x: A) l, In x (rev l) <-> In x l.
Proof.
  intros; unfold rev; symmetry; rewrite <- appl0 at 1; generalize (@nil A).
  induction l; simpl; intros; try rewrite <- IHl, !In_app; simpl; tauto.
Qed.

Lemma In_revI : forall A (x: A) l (IN: In x l), In x (rev l).
Proof. by intros; apply In_rev. Qed.

Lemma In_revD : forall A (x: A) l (IN: In x (rev l)), In x l.
Proof. by intros; apply In_rev. Qed.

Lemma In_mapI : forall A B (f: A -> B) x l (IN: In x l), In (f x) (map f l).
Proof.
  induction l; simpl; intros; intuition vauto. 
Qed.

Lemma In_mapD : 
  forall A B (f: A->B) y l, In y (map f l) -> exists x, f x = y /\ In x l.
Proof.
  induction l; simpl in *; intuition; des; eauto.
Qed.

Lemma In_map : 
  forall A B (f: A->B) y l, In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  split; intros; des; clarify; auto using In_mapI, In_mapD.
Qed.

Lemma In_filter :
  forall A (x:A) f l,  In x (filter f l) <-> In x l /\ f x.
Proof. induction l; ins; desf; simpls; intuition; clarify. Qed.

Lemma In_filterI :
  forall A x l (IN: In x l) (f: A->bool) (F: f x), In x (filter f l).
Proof. by intros; apply In_filter. Qed.

Lemma In_filterD :
  forall A (x:A) f l (D: In x (filter f l)), In x l /\ f x.
Proof. by intros; apply In_filter. Qed.

Hint Resolve In_eq In_cons In_appI1 In_appI2 In_mapI In_revI In_filterI : vlib. 

Lemma uniqP : forall (T : eqType) (l: list T), reflect (List.NoDup l) (uniq l).
Proof.
  induction l; simpl; vauto.
  case (inP a l); ins; vauto; [|case IHl; vauto];
    by constructor; inversion 1; clarify.
Qed. 

Lemma In_dec_strong :
  forall {A : Type} (P Q : A -> Prop)
    (dP: forall i:A, {P i} + {Q i})
    (l : list A),
      {e | In e l /\ P e} + {(forall e, In e l -> Q e)}.
Proof.
  intros; induction l as [|h t [(e & IH & inP)|IH]]; vauto.
    by left; exists e; simpl; tauto.
  destruct (dP h) as [hdP | nhdP].
  - by left; exists h; simpl; tauto.
  - by right; intros e [H|H]; clarify; apply (IH e).
Qed.

Lemma In_dec_strong_prop :
  forall {A : Type} (P : A -> Prop)
    (dP: forall i:A, P i \/ ~ P i)
    (l : list A),
      (exists e, In e l /\ P e) \/ (forall e, ~ (In e l /\ P e)).
Proof.
  intros; induction l as [|h t [(e & IH & inP)|IH]].
  - by right; intros e [H _].
  - by left; exists e; simpl; tauto.
  - destruct (dP h) as [hdP | nhdP].
    + by left; exists h; simpl; tauto.
    + by right; intros e [[] Pe]; clarify; elim (IH e).
Qed.

Lemma In_dec_strong_neg :
  forall {A : Type} (P : A -> Prop)
    (dP: forall i:A, {P i} + {~ P i})
    (l : list A),
      {e | In e l /\ ~ P e} + {(forall e, In e l -> P e)}.
Proof.
  intros; induction l as [|h t [(e & IH & inP)|IH]]; vauto.
    by left; exists e; simpl; tauto.
  destruct (dP h) as [hdP | nhdP].
  - by right; intros e [H|H]; clarify; apply IH.
  - by left; exists h; simpl; tauto.
Qed.


(* ************************************************************************** *)
(** * Setoid rewriting for equality up to permutation *)
(* ************************************************************************** *)

Require Import Setoid.

Add Parametric Relation (T: eqType) : (list T) (@perm_eq T)
  reflexivity proved by (@perm_eq_refl T)
  symmetry proved by (pre_from_symmetric (@perm_eq_sym T))
  transitivity proved by (@perm_eq_trans T)
  as perm_rel.

Lemma perm_eq_map (T U : eqType) (f : T -> U) : 
  forall xs ys (PE : perm_eq xs ys), perm_eq (map f xs) (map f ys).
Proof.
  induction xs; intros; [apply perm_eq_nilD in PE; subst; apply perm_eq_refl |].
  apply perm_eq_consD in PE; des; subst; rewrite map_app; simpl.
  rewrite perm_eq_sym, perm_appC; simpl; 
  rewrite perm_cons, perm_appC, perm_eq_sym, <- map_app; auto.
Qed.

Lemma perm_eq_flatten (T : eqType) : 
  forall (xs ys: list (list T)) (PE : perm_eq xs ys), perm_eq (flatten xs) (flatten ys).
Proof.
  induction xs; intros; [apply perm_eq_nilD in PE; subst; apply perm_eq_refl |].
  apply perm_eq_consD in PE; des; subst; rewrite flatten_app, !flatten_cons. 
  rewrite perm_eq_sym, perm_appCA, perm_app2l, <- flatten_app, perm_eq_sym; auto.
Qed.

Lemma perm_eq_map2 (T U : eqType) (f g : T -> U) : 
  forall xs ys (PE : perm_eq xs ys) (EQ: forall x (IN: In x xs), f x = g x), 
    perm_eq (map f xs) (map g ys).
Proof.
  induction xs; intros; [apply perm_eq_nilD in PE; subst; apply perm_eq_refl |].
  apply perm_eq_consD in PE; des; subst; rewrite map_app; simpl.
  rewrite perm_eq_sym, perm_appC; ins.
  rewrite EQ; vauto.
  rewrite perm_cons, perm_appC, perm_eq_sym, <- map_app; eauto. 
Qed.



Add Parametric Morphism A : (@perm_eq A)
  with signature (@perm_eq A) ==> (@perm_eq A) ==> (@eq bool) as perm_morph. 
Proof. 
  ins; apply/perm_eqP in H; apply/perm_eqP in H0; apply/perm_eqP/perm_eqP; congruence.
Qed.

Add Parametric Morphism A a : (cons a)
  with signature (@perm_eq A) ==> (@perm_eq _) as cons_morph. 
Proof. by ins; rewrite perm_cons. Qed.

Add Parametric Morphism A : (@app A)
  with signature (@perm_eq A) ==> (@perm_eq _) ==> (@perm_eq _) as app_morph. 
Proof. by etransitivity; [rewrite perm_app2l|rewrite perm_app2r]. Qed.

Add Parametric Morphism A B f : (@map A B f)
  with signature (@perm_eq A) ==> (@perm_eq B) as map_morph. 
Proof. apply perm_eq_map. Qed.

Add Parametric Morphism A : (@flatten A)
  with signature (@perm_eq _) ==> (@perm_eq A) as flatten_morph. 
Proof. apply perm_eq_flatten. Qed.

Add Parametric Morphism T : (@uniq T)
  with signature (@perm_eq T) ==> (@eq bool) as uniq_morph. 
Proof. apply perm_eq_uniq. Qed.

