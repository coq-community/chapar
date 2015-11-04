(** * Lists *)

(** This development is largely ported from the [seq] library of SSReflect. 
    The names of several operations have been changed to use the standard
    Coq list definitions (e.g., [seq] => [list], [cat] => [app],
    [size] => [length]) and a few lemmas have been added.
 *)

Require Import Vbase Varith. 
Require Coq.omega.Omega.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope bool_scope.
Open Scope list_scope.

(** ** List operations *)

Section Operations.

Variable n0 : nat.  (**r numerical parameter for take, drop et al *)
Variable T : Type.  (**r must come before the implicit Type     *)
Variable x0 : T.    (**r default for head/nth *)

Implicit Types x y z : T.
Implicit Types m n : nat.
Implicit Type l : (list T).

Definition ohead l := 
  match l with 
    | nil => None
    | x :: _ => Some x
  end. 

Definition head l :=
  match l with 
    | nil => x0
    | x :: _ => x
  end. 

Definition behead l := 
  match l with 
    | nil => nil
    | _ :: x => x
  end. 

Definition ncons n x := iter n (cons x).
Definition nlist n x := ncons n x nil.

Fixpoint snoc l z :=
  match l with
    | nil => z :: nil
    | x :: l => x :: snoc l z
  end. 

Fixpoint last x l := 
  match l with 
    | nil => x
    | x' :: l' => last x' l'
  end.

Fixpoint olast l := 
  match l with 
    | nil => None
    | x' :: l' => Some (last x' l')
  end.

Fixpoint belast x l := 
  match l with 
    | nil => nil
    | x' :: l' => x :: belast x' l'
  end.

(** Indexing *)

Fixpoint onth l n {struct n} :=
  match l, n with 
    | nil, _ => None
    | x :: l, O => Some x
    | x :: l, S n => onth l n
  end.

Fixpoint oset_nth l n y {struct n} :=
  match l, n with 
    | nil, _ => None
    | x :: l, O => Some (y :: l)
    | x :: l, S n => match oset_nth l n y with
                       | None => None 
                       | Some l' => Some (x :: l')
                     end
  end.

Fixpoint nth l n {struct n} :=
  match l, n with 
    | nil, _ => x0
    | x :: l, O => x
    | x :: l, S n => nth l n
  end.

Fixpoint set_nth l n y {struct n} :=
  match l, n with 
    | nil, _ => ncons n x0 (y :: nil)
    | x :: l, O => y :: l
    | x :: l, S n => x :: set_nth l n y
  end.

(** Searching for elements *)

Fixpoint In x l :=
  match l with
    | nil => False
    | y :: l => y = x \/ In x l
  end.

Fixpoint find f l := 
  match l with 
    | nil => 0
    | x :: l' => if (f x : bool) then 0 else S (find f l')
  end.

Fixpoint filter f l :=
  match l with 
    | nil => nil
    | x :: l' => if (f x : bool) then x :: filter f l' else filter f l'
  end.

Fixpoint count f l := 
  match l with 
    | nil => 0
    | x :: l' => if (f x : bool) then S (count f l') else count f l'
  end.

Fixpoint has f l := 
  match l with 
    | nil => false
    | x :: l' => f x || has f l'
  end.

Fixpoint all f l := 
  match l with 
    | nil => true
    | x :: l' => f x && all f l'
  end.

Fixpoint sieve (m : list bool) (s : list T) {struct m} : list T :=
  match m, s with
  | b :: m', x :: s' => if b then x :: sieve m' s' else sieve m' s'
  | _, _ => nil
  end.

(** Surgery *)

Fixpoint drop n l {struct l} :=
  match l, n with
  | _ :: l, S n' => drop n' l
  | _, _ => l
  end.

Fixpoint take n l {struct l} :=
  match l, n with
  | x :: l, S n' => x :: take n' l
  | _, _ => nil
  end.

Definition rot n l := drop n l ++ take n l.

Definition rotr n l := rot (length l - n) l.

Fixpoint rev_append l1 l2 :=
  match l1 with
    | nil => l2
    | x :: l1 => rev_append l1 (x :: l2)
  end.

(** Index sequence: the list [[m; m + 1; ... m + n]]. *)

Fixpoint iota (m n : nat) : list nat :=
  match n with
    | O => nil
    | S n => m :: iota (S m) n
  end.

End Operations.

(* rev must be defined outside a Section because Coq's end of section *)
(* "cooking" removes the nosimpl guard.                               *)

Definition rev T s := 
  match tt with tt => (* nosimpl hack *)
    rev_append s (@nil T)
  end.

(** ** Basic properties *)

Section SequencesBasic.

Variable n0 : nat.  (* numerical parameter for take, drop et al *)
Variable T : Type.  (* must come before the implicit Type     *)
Variable x0 : T.    (* default for head/nth *)

Implicit Types x y z : T.
Implicit Types m n : nat.
Implicit Types s l : (list T).

Lemma length0nil : forall s, length s = 0 -> s = nil. 
Proof. by destruct s. Qed.

Lemma length_behead : forall s, length (behead s) = (length s) - 1.
Proof. by destruct s; simpl; [|destruct (length s)]. Qed.

Lemma length_ncons : forall n x s, length (ncons n x s) = n + length s.
Proof. intros; induct n. Qed.

Lemma length_nlist : forall n x, length (nlist n x) = n.
Proof. by intros; unfold nlist; rewrite length_ncons. Qed.

Lemma length_app : forall s1 s2, length (s1 ++ s2) = length s1 + length s2.
Proof. induct s1. Qed. 

Lemma app0l : forall s, nil ++ s = s.
Proof. done. Qed.

Lemma app1l : forall x s, (x :: nil) ++ s = x :: s.
Proof. done. Qed.

Lemma app_cons : forall x s1 s2, (x :: s1) ++ s2 = x :: s1 ++ s2.
Proof. done. Qed.

Lemma app_ncons : forall n x s1 s2, ncons n x s1 ++ s2 = ncons n x (s1 ++ s2).
Proof. unfold ncons; induct n. Qed.

Lemma app_nlist : forall n x s, nlist n x ++ s = ncons n x s.
Proof. intros; unfold ncons; induct n. Qed.

Lemma appl0 : forall s, s ++ nil = s.
Proof. induct s. Qed.

Lemma appA : forall s1 s2 s3, (s1 ++ s2) ++ s3 = s1 ++ (s2 ++ s3).
Proof. induct s1. Qed.

Lemma nconsE : forall n x s, ncons n x s = nlist n x ++ s. 
Proof. by symmetry; apply app_nlist. Qed. 

(** last, belast, rcons, and last induction. *)

Lemma snoc_cons : forall x s z, snoc (x :: s) z = x :: snoc s z.
Proof. done. Qed.

Lemma appl1 : forall l x, l ++ (x :: nil) = snoc l x.
Proof. induct l. Qed.

Lemma snocE : forall l x, snoc l x = l ++ (x :: nil).
Proof. by symmetry; apply appl1. Qed.

Lemma lastI : forall x s, x :: s = snoc (belast x s) (last x s).
Proof. induct[x] s. Qed.

Lemma last_cons : forall x y s, last x (y :: s) = last y s.
Proof. done. Qed.

Lemma length_snoc : forall s x, length (snoc s x) = S (length s).
Proof. by intros; rewrite snocE, length_app, addnC. Qed.

Lemma length_belast : forall x s, length (belast x s) = length s.
Proof. induct[x] s. Qed.

Lemma last_app : forall x s1 s2, last x (s1 ++ s2) = last (last x s1) s2.
Proof. induct[x] s1. Qed.

Lemma last_snoc : forall x s z, last x (snoc s z) = z.
Proof. by intros; rewrite snocE, last_app. Qed.

Lemma belast_app : forall x s1 s2,
  belast x (s1 ++ s2) = belast x s1 ++ belast (last x s1) s2.
Proof. induct[x] s1. Qed.

Lemma belast_snoc : forall x s z, belast x (snoc s z) = x :: s.
Proof. by intros; rewrite lastI, !snocE, belast_app. Qed.

Lemma app_snoc : forall x s1 s2, snoc s1 x ++ s2 = s1 ++ x :: s2.
Proof. by intros; rewrite snocE, appA. Qed.

Lemma snoc_app : forall x s1 s2,
  snoc (s1 ++ s2) x = s1 ++ snoc s2 x.
Proof. by intros; rewrite !snocE, appA. Qed.

Inductive last_spec : list T -> Type :=
  | LastNil        : last_spec nil
  | LastRcons s x  : last_spec (snoc s x).

Lemma lastP : forall s, last_spec s.
Proof. destruct s; [ left | rewrite lastI; right ]. Qed.

Lemma last_ind : 
  forall P (Hnil: P nil) (Hlast: forall s x, P s -> P (snoc s x)) s, P s.
Proof.
intros; rewrite <-(app0l s); revert Hnil; generalize (@nil T).
by induction s; intros; [rewrite appl0|rewrite <- app_snoc; auto].
Qed.

Inductive last_spec_eq (y : list T): Type :=
  | LastEqNil        : y = nil -> last_spec_eq y
  | LastEqRcons s x  : y = snoc s x -> last_spec_eq y.

Lemma last_eqP : forall (s: list T), last_spec_eq s.
Proof. destruct s; [|rewrite lastI]; vauto. Qed.

(** Sequence indexing. *)

Lemma nth0 : forall l, nth x0 l 0 = head x0 l.
Proof. done. Qed.

Lemma nth_default : forall s n, length s <= n -> nth x0 s n = x0.
Proof. induct s [n]. Qed.

Lemma nth_nil : forall n, nth x0 nil n = x0.
Proof. by destruct n. Qed.

Lemma last_nth : forall x s, last x s = nth x0 (x :: s) (length s).
Proof. induct[x] s. Qed.

Lemma nth_last : forall s, nth x0 s (length s - 1) = last x0 s.
Proof. by destruct s; simpl; [|rewrite last_nth; destruct (length s)]. Qed.

Lemma nth_behead : forall s n, nth x0 (behead s) n = nth x0 s (S n).
Proof. by intros [] []. Qed.

Lemma nth_app : forall s1 s2 n,
 nth x0 (s1 ++ s2) n = if ltn n (length s1) then nth x0 s1 n else nth x0 s2 (n - length s1).
Proof. induct s1 [n]. Qed.

Lemma nth_snoc : forall s x n,
  nth x0 (snoc s x) n = (if n < length s then nth x0 s n else if n == length s then x else x0).
Proof. induct s [n]; apply nth_nil. Qed.

Lemma nth_ncons : forall m x s n,
  nth x0 (ncons m x s) n = (if ltn n m then x else nth x0 s (n - m)).
Proof. induct m [n]. Qed.

Lemma nth_nlist : forall m x n, nth x0 (nlist m x) n = (if ltn n m then x else x0).
Proof. by intros; unfold nlist; rewrite nth_ncons, nth_nil. Qed.

Lemma eq_from_nth : forall s1 s2
  (EQlength: length s1 = length s2)
  (EQnth: forall i, i < length s1 -> nth x0 s1 i = nth x0 s2 i),
  s1 = s2.
Proof.
  induction s1; destruct s2; clarsimp.
  rewrite (IHs1 s2); try done;
    [f_equal; apply (EQnth 0)| intros; apply (EQnth (S i))]; auto.
Qed.

Lemma length_set_nth : 
  forall s n y, length (set_nth x0 s n y) = (if ltn n (length s) then length s else S n).
Proof.
induction s; destruct n; intros; simpl; try done. 
- change (iter n (cons x0)) with (ncons n x0).
  rewrite length_ncons; simpl; omega. 
- by rewrite <- fun_if with (f := S); f_equal; apply IHs.
Qed.

Lemma set_nth_nil : forall n y, set_nth x0 nil n y = ncons n x0 (y :: nil).
Proof. by destruct n. Qed.

(*Lemma nth_set_nth : forall s n y,
  nth x0 (set_nth x0 s n y) =1 [eta nth x0 s with n |-> y].
Proof.
  red; induction[] s [n x]; simpls; rewrite ?nth_nil, ?IHs; simpls.
  assert (H := nth_ncons); unfold ncons in H; rewrite H; clear H. 
  clarsimp; case cmpP; ins; clarsimp.
  rewrite nth_default; simpls.
  eapply ltn_complete in H; eapply ltn_correct; omega.
Qed.

Lemma set_set_nth : forall s n1 y1 n2 y2,
  set_nth x0 (set_nth x0 s n1 y1) n2 y2 =
   let s2 := set_nth x0 s n2 y2 in if n1 == n2 then s2 else set_nth x0 s2 n1 y1.
Proof.
  intros; simpls.
  eapply eq_from_nth; ins.
    rewrite (fun_if (@length _)), !length_set_nth, !ltnE_sub.
    repeat case eqP; ins; clarify; omega.
  repeat (rewrite nth_set_nth; simpl).
  repeat case eqP; ins; clarify;
  repeat (rewrite nth_set_nth; simpl; rewrite ?eqxx); try done;
  repeat case eqP; ins; clarify.
Qed.*)

Lemma onth0 : forall l, onth l 0 = ohead l.
Proof. done. Qed.

Lemma onth_none : forall s n, length s <= n -> onth s n = None.
Proof. induct s [n]. Qed.

Lemma onth_nil : forall n, onth nil n = None (A:=T).
Proof. by destruct n. Qed.

Lemma olast_nth : forall s, olast s = onth s (length s - 1).
Proof. destruct s as [|x s]; simpls; induct[x] s. Qed.

Lemma onth_last : forall s, onth s (length s - 1) = olast s.
Proof. by intros; rewrite olast_nth. Qed. 

Lemma onth_behead : forall s n, onth (behead s) n = onth s (S n).
Proof. by intros [] []. Qed.

Lemma onth_app : forall s1 s2 n,
 onth (s1 ++ s2) n = if n < (length s1) then onth s1 n else onth s2 (n - length s1).
Proof. induct s1 [n]. Qed.

Lemma onth_snoc : forall s x n,
  onth (snoc s x) n = (if n < length s then onth s n else if n == length s then Some x else None).
Proof. induct s [n]; apply onth_nil. Qed.

Lemma onth_ncons : forall m x s n,
  onth (ncons m x s) n = (if n < m then Some x else onth s (n - m)).
Proof. induct m [n]. Qed.

Lemma onth_nlist : forall m x n, onth (nlist m x) n = (if n < m then Some x else None).
Proof. by intros; unfold nlist; rewrite onth_ncons, onth_nil. Qed.

Lemma eq_from_onth : forall s1 s2
  (EQnth: forall i, onth s1 i = onth s2 i),
  s1 = s2.
Proof.
  induction[] s1 [s2]; intros; clarsimp;
    try by specialize (EQnth 0).
  rewrite (IHs1 s2); try done;
    [f_equal; specialize (EQnth 0); clarsimp| intros; apply (EQnth (S i))]; auto.
Qed.

Lemma length_oset_nth : 
  forall s n y s' (EQ: oset_nth s n y = Some s'), length s' = length s.
Proof.
  induct s [n]; des_if; simpls; eauto.
Qed.

Lemma oset_nth_nil : forall n y, oset_nth nil n y = None.
Proof. by destruct n. Qed.

End SequencesBasic.

(** Automation support *)

Hint Rewrite 
  length_behead length_ncons length_nlist length_app length_snoc length_belast
  appl0 last_app last_snoc belast_app belast_snoc app_snoc snoc_app : vlib.

Hint Rewrite 
  nth_nil nth_behead nth_app nth_snoc nth_ncons nth_nlist
  length_set_nth set_nth_nil : vlib.

(** ** Properties of [find], [count], [has], [all] *)

Section SeqFind.

Variable T : Type.  (* must come before the implicit Type     *)
Variable x0 : T.    (* default for head/nth *)

Implicit Types x y z : T.
Implicit Types m n : nat.
Implicit Types s l : (list T).

Variable f : pred T. 

Lemma count_filter : forall l, count f l = length (filter f l).
Proof. induct l. Qed. 

Lemma has_count : forall l, has f l = ltn 0 (count f l).
Proof. induct l. Qed. 

Lemma count_length : forall l, count f l <= length l.
Proof. induction l; simpls; case f; autos. Qed.

Lemma all_count : forall l, all f l = (count f l == length l).
Proof.
  induction l; clarsimp; case f; clarsimp.
  generalize (count_length l); case (count f l); clarsimp. 
  case eqP; clarsimp. 
Qed.

Lemma all_filterP : forall s, reflect (filter f s = s) (all f s).
Proof.
intros; apply introP; [by induct s|].
rewrite all_count, count_filter.
by intros X Y; revert X; rewrite Y, eqnn. 
Qed.

Lemma has_find : forall l, has f l = ltn (find f l) (length l).
Proof. induct l. Qed. 

Lemma find_length : forall l, find f l <= length l.
Proof. induct l. Qed. 

Lemma find_app : forall s1 s2,
  find f (s1 ++ s2) = if has f s1 then find f s1 else length s1 + find f s2.
Proof.
 induction s1; ins; case f; try done.
 by rewrite IHs1, (fun_if S).
Qed.

Lemma has_nil : has f nil = false.
Proof. done. Qed.

Lemma has_list1 : forall x, has f (x :: nil) = f x.
Proof. clarsimp. Qed.

Lemma all_nil : all f nil = true.
Proof. done. Qed.

Lemma all_list1 : forall x, all f (x :: nil) = f x.
Proof. clarsimp. Qed.

Lemma nth_find : forall s, has f s -> f (nth x0 s (find f s)).
Proof. by induction s; simpls; case_eq (f a); simpl. Qed.

Lemma before_find : forall s i, i < find f s -> f (nth x0 s i) = false.
Proof.
induction s; clarsimp; case_eq (f a) as X; clarsimp; destruct i; autos.
Qed.

Lemma filter_app:
  forall l1 l2, filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof. induct l1. Qed.

Lemma filter_snoc : forall s x,
  filter f (snoc s x) = if f x then snoc (filter f s) x else filter f s.
Proof.
by intros; rewrite !snocE, filter_app; simpl; case f; rewrite ?appl0.
Qed.

Lemma count_app : forall s1 s2, count f (s1 ++ s2) = count f s1 + count f s2.
Proof. by intros; rewrite !count_filter, filter_app, length_app. Qed.

Lemma has_app : forall s1 s2, has f (s1 ++ s2) = has f s1 || has f s2.
Proof. by intros; induction s1; simpl; try done; rewrite IHs1, orbA. Qed.

Lemma has_snoc : forall s x, has f (snoc s x) = f x || has f s.
Proof. by intros; rewrite <- appl1, has_app, has_list1, orbC. Qed.

Lemma all_app : forall s1 s2, all f (s1 ++ s2) = all f s1 && all f s2.
Proof. by intros; induction s1; simpl; try done; rewrite IHs1, andbA. Qed.

Lemma all_snoc : forall s x, all f (snoc s x) = f x && all f s.
Proof. by intros; rewrite <- appl1, all_app, all_list1, andbC. Qed.


Lemma filter_pred0 : forall s, filter pred0 s = nil.
Proof. by induction s. Qed.

Lemma filter_predT : forall s, filter predT s = s.
Proof. induction s; clarsimp; congruence. Qed.

Lemma filter_predI : forall a1 a2 s,
  filter (predI a1 a2) s = filter a1 (filter a2 s).
Proof. induct s. Qed.

Lemma count_pred0 : forall s, count pred0 s = 0.
Proof. by induction s. Qed.

Lemma count_predT : forall s, count predT s = length s.
Proof. induct s. Qed. 

Lemma count_predUI : forall a1 a2 l,
 count (predU a1 a2) l + count (predI a1 a2) l = count a1 l + count a2 l.
Proof. induction l; clarsimp; case (a1 a); case (a2 a); simpl; omega. Qed.

Lemma count_predC : forall a l, count a l + count (predC a) l = length l.
Proof. induct l. Qed. 

Lemma has_pred0 : forall s, has pred0 s = false.
Proof. by induction s. Qed.

Lemma has_predT : forall s, has predT s = (0 < length s).
Proof. induct s. Qed. 

Lemma has_predC : forall a l, has (predC a) l = negb (all a l).
Proof. induction l; clarsimp; case (a a0); clarsimp. Qed.

Lemma has_predU : forall a1 a2 l, has (predU a1 a2) l = has a1 l || has a2 l.
Proof. induction l; clarsimp; case (a1 a); case (a2 a); clarsimp. Qed.

Lemma all_pred0 : forall l, all pred0 l = (length l == 0).
Proof. induct l. Qed.

Lemma all_predT : forall s, all predT s = true.
Proof. induct s. Qed.

Lemma all_predC : forall a s, all (predC a) s = negb (has a s).
Proof. induction s; clarsimp; case (a a0); clarsimp. Qed.

Lemma all_predI : forall a1 a2 s, all (predI a1 a2) s = all a1 s && all a2 s.
Proof. induction s; clarsimp; case (a1 a); case (a2 a); clarsimp. Qed.

Section EqLemmas.

Variables (a1 a2 : pred T).
Variable (EQ : a1 =1 a2).

Lemma eq_find : find a1 =1 find a2.
Proof. intro s; induction s; clarsimp; rewrite EQ; case (a2 a); congruence. Qed.

Lemma eq_filter : filter a1 =1 filter a2.
Proof. intro s; induction s; clarsimp; rewrite EQ; case (a2 a); congruence. Qed.

Lemma eq_count : count a1 =1 count a2.
Proof. intro s; induction s; clarsimp; rewrite EQ; case (a2 a); congruence. Qed.

Lemma eq_has : has a1 =1 has a2.
Proof. intro s; induction s; clarsimp; rewrite EQ; case (a2 a); congruence. Qed.

Lemma eq_all : all a1 =1 all a2.
Proof. intro s; induction s; clarsimp; rewrite EQ; case (a2 a); congruence. Qed.

End EqLemmas.

End SeqFind.

(** Automation support *)

Hint Rewrite 
  count_length find_length filter_app filter_snoc
  count_app has_app has_snoc all_app all_snoc : vlib.

Hint Rewrite has_pred0 : vlib.

(** ** Surgery: drop, take, rot, rotr.  *)

Section SequenceSurgery.

Variable n0 : nat.  (* numerical parameter for take, drop et al *)
Variable T : Type.  (* must come before the implicit Type     *)
Variable x0 : T.    (* default for head/nth *)

Implicit Types x y z : T.
Implicit Types m n : nat.
Implicit Types s l : (list T).

Lemma drop_behead : drop n0 =1 iter n0 (@behead T).
Proof. intro x; rewrite <- iter_recE; induct[x] n0 [x]. Qed.

Lemma drop0 : forall s, drop 0 s = s.
Proof. by intros []. Qed.

Hint Rewrite drop0 : vlib. (* repeat outside section *)

Lemma drop1 : forall l, drop 1 l = behead l. 
Proof. by intros [|x [|y s]]. Qed.

Lemma drop_overlength : forall n s, length s <= n -> drop n s = nil.
Proof. induct n [s]. Qed.
Implicit Arguments drop_overlength [n s].

Lemma drop_length : forall s, drop (length s) s = nil.
Proof. auto using drop_overlength. Qed.

Lemma drop_cons : forall x s,
  drop n0 (x :: s) = (match n0 with O => x :: s | S n => drop n s end).
Proof. done. Qed.

Lemma length_drop : forall s, length (drop n0 s) = length s - n0.
Proof. induct[n0] s [n0]. Qed. 

Lemma drop_app : forall s1 s2,
 drop n0 (s1 ++ s2) =
   if ltn n0 (length s1) then drop n0 s1 ++ s2 else drop (n0 - length s1) s2.
Proof. induct[n0] s1 [n0]. Qed.

Lemma drop_length_app : forall n s1 s2, length s1 = n -> drop n (s1 ++ s2) = s2.
Proof. intros; subst; induct s1. Qed. 

Lemma nconsK : forall n x, cancel (ncons n x) (drop n).
Proof. by intros; induction n; clarsimp; intros []. Qed.

Lemma take0 : forall s, take 0 s = nil.
Proof. by intros []. Qed.

Hint Rewrite take0 : vlib. (* repeat outside section *)

Lemma take_overlength : forall n s, length s <= n -> take n s = s.
Proof. induct n [s]. Qed. 
Implicit Arguments take_overlength [n s].

Lemma take_length : forall s, take (length s) s = s.
Proof. by intros; rewrite take_overlength. Qed. 

Lemma take_cons : forall x s,
  take n0 (x :: s) = (match n0 with O => nil | S n => x :: take n s end).
Proof. done. Qed.

Lemma drop_snoc : forall s, n0 <= length s ->
  forall x, drop n0 (snoc s x) = snoc (drop n0 s) x.
Proof. induct[n0] s [n0]. Qed.

Lemma app_take_drop : forall s, take n0 s ++ drop n0 s = s.
Proof. induct[n0] s [n0]. Qed.

Lemma length_takel : forall s (H: n0 <= length s), length (take n0 s) = n0.
Proof. induct n0 [s]. Qed.

Lemma length_take : forall s,
  length (take n0 s) = if ltn n0 (length s) then n0 else length s.
Proof.
  intros; case ltnP; intro; [|by rewrite take_overlength].
  apply length_takel; auto.
Qed.

Lemma take_app : forall s1 s2,
 take n0 (s1 ++ s2) =
   if ltn n0 (length s1) then take n0 s1 else s1 ++ take (n0 - length s1) s2.
Proof.
  intros; induction[n0] s1 [n0]; simpls. 
  by rewrite IHs1; apply fun_if. 
Qed.

Lemma take_length_app : forall n s1 s2, length s1 = n -> take n (s1 ++ s2) = s1.
Proof. intros; subst; induct s1. Qed.

Lemma takel_app : forall s1, n0 <= length s1 ->
  forall s2, take n0 (s1 ++ s2) = take n0 s1.
Proof.
  intros; rewrite take_app; case ltnP; try done.
  intros; replace n0 with (length s1); clarsimp. 
    by rewrite take_length.
  by apply len_anti.
Qed.

Lemma nth_drop : forall s i, nth x0 (drop n0 s) i = nth x0 s (n0 + i).
Proof.
  intros; case_eq (ltn n0 (length s)); intro Hn.
    rewrite <- (app_take_drop s) at 2; rewrite nth_app, length_take, Hn.
    case ltP; intro; try (elimtype False; omega); f_equal; omega.
  rewrite !nth_default; try done.
    revert Hn; case ltnP; clarsimp; eauto with vlib. 
  rewrite length_drop; revert Hn; case ltnP; clarsimp; eauto with vlib.
Qed.

Lemma nth_take : forall i, i < n0 -> forall s, nth x0 (take n0 s) i = nth x0 s i.
Proof.
  intros; case_eq (ltn n0 (length s)); intro Hn.
    by rewrite <- (app_take_drop s) at 2; rewrite nth_app, length_take, Hn, H.
  by rewrite <- (appl0 s) at 1; rewrite take_app, Hn; simpl; rewrite appl0.
Qed.

(* drop_nth and take_nth below do NOT use the default n0, because the "n"  *)
(* can be inferred from the condition, whereas the nth default value x0    *)
(* will have to be given explicitly (and this will provide "d" as well).   *)

Lemma drop_nth : forall n s, n < length s -> drop n s = nth x0 s n :: drop (S n) s.
Proof. induct [n] s [n]. Qed.

Lemma take_nth : forall n s, n < length s ->
  take (S n) s = snoc (take n s) (nth x0 s n).
Proof. induct[n] s [n]. Qed.

Lemma rot0 : forall s, rot 0 s = s.
Proof. unfold rot; clarsimp. Qed.

Lemma length_rot : forall s, length (rot n0 s) = length s.
Proof.
by intros; rewrite <-(app_take_drop s) at 2; unfold rot; 
   rewrite !length_app, addnC.
Qed.

Lemma rot_overlength : forall n s (H: length s <= n), rot n s = s.
Proof. by intros; unfold rot; rewrite (take_overlength H), (drop_overlength H). Qed.

Lemma rot_length : forall s, rot (length s) s = s.
Proof. auto using rot_overlength. Qed.

Lemma has_rot : forall l f, has f (rot n0 l) = has f l.
Proof. by intros; unfold rot; rewrite has_app, orbC, <- has_app, app_take_drop. Qed.

Lemma all_rot : forall l f, all f (rot n0 l) = all f l.
Proof. by intros; unfold rot; rewrite all_app, andbC, <- all_app, app_take_drop. Qed.

Lemma rot_length_app : forall s1 s2, rot (length s1) (s1 ++ s2) = s2 ++ s1.
Proof. by intros; unfold rot; rewrite take_length_app, ?drop_length_app. Qed.

Lemma rotK : forall l, rotr n0 (rot n0 l) = l.
Proof.
intros; unfold rotr; rewrite length_rot, <- length_drop.
by unfold rot at 2; rewrite rot_length_app, app_take_drop.
Qed.

Lemma rot_inj : injective (@rot T n0).
Proof. exact (can_inj rotK). Qed.

Lemma rot1_cons : forall x s, rot 1 (x :: s) = snoc s x.
Proof. by intros; unfold rot; simpl; rewrite take0, drop0, <-appl1. Qed.

End SequenceSurgery.

(** ** Automation support *)

Hint Rewrite drop0 drop_length length_drop : vlib.
Hint Rewrite take0 take_length length_take : vlib.
Hint Rewrite nth_drop : vlib.
Hint Rewrite rot0 length_rot rot_length has_rot all_rot rot_length_app rotK rot1_cons : vlib.


Section Rev.

Variable T : Type.
Implicit Type s : list T.

Lemma rev_nil : rev nil = (@nil T).
Proof. done. Qed.

Lemma rev_snoc : forall s x, rev (snoc s x) = x :: (rev s).
Proof.
  intros; unfold rev; rewrite <- appl1. 
  by generalize (@nil T) at -1; induction s; simpl.
Qed.

Lemma rev_cons : forall x s, rev (x :: s) = snoc (rev s) x.
Proof.
  intros x. apply last_ind; intros; simpl; try done.
  by rewrite rev_snoc; simpl; rewrite <- H, <- rev_snoc. 
Qed.

Lemma length_rev : forall s, length (rev s) = length s.
Proof. by induction s; try done; rewrite rev_cons, length_snoc, IHs. Qed.

Lemma rev_app : forall s1 s2, rev (s1 ++ s2) = rev s2 ++ rev s1.
Proof.
  induction s1; simpl; intros; [by rewrite appl0|].
  by rewrite !rev_cons, IHs1, <-!appl1, appA.
Qed.

Lemma rev_rev : forall s, rev (rev s) = s.
Proof. by induction s; simpls; rewrite rev_cons, rev_snoc, IHs. Qed.

Lemma nth_rev : forall x0 n s,
  n < length s -> nth x0 (rev s) n = nth x0 s (length s - S n).
Proof.
  intros x0 n s; revert n. 
  apply (last_ind) with (s := s); simpl; intros. by clarsimp.
  rewrite rev_snoc, length_snoc, snocE, nth_app in *; simpl. 
  case ltnP; intro.
    destruct n; [elimtype False|apply H]; clarsimp. 
  clarsimp; replace n with 0; clarsimp.
  destruct n; destruct (length s0); clarsimp.
Qed.

End Rev.

Hint Rewrite rev_snoc rev_cons length_rev rev_app rev_rev : vlib.
