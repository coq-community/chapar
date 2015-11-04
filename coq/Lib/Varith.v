(** Lemmas about . Most of the rewriting support is ported from ss-reflect. *)

(** Symbols starting with [vlib__] are internal. *)

Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import String.
Require Import Vbase.
(* Require Import Veq. *)

Set Implicit Arguments.
Unset Strict Implicit.


(** Comparison for [nat] *)

Fixpoint eqn_rec (x y: nat) {struct x} :=
   match x, y with
     | O, O => true
     | S x, S y => eqn_rec x y
     | _, _ => false
   end.

Definition eqn := match tt with tt => eqn_rec end.

Lemma eqnP: forall x y, reflect (x = y) (eqn x y).
Proof.
  induction[] x [y]; vauto. 
  change (eqn (S x) (S y)) with (eqn x y).
  case IHx; constructor; congruence.
Qed.

Canonical Structure nat_eqMixin := EqMixin eqnP.
Canonical Structure nat_eqType := Eval hnf in EqType nat nat_eqMixin.

Lemma eqnE : eqn = (@eq_op _).
Proof. done. Qed.



(* ************************************************************************** *)
(** * Three-valued logic *)
(* ************************************************************************** *)


(** * Three-valued Logic *) 

Inductive bool3 := B3tt | B3ff | B3un.

Definition bool3_beq (x y : bool3) :=
  match x, y with
    | B3tt, B3tt => true
    | B3ff, B3ff => true
    | B3un, B3un => true
    | _, _ => false
  end.

Lemma bool3P : forall x y, reflect (x = y) (bool3_beq x y).
Proof. intros[][]; vauto. Qed.

Definition negb3 (b:bool3) : bool3 :=
  match b with 
   | B3tt => B3ff
   | B3ff => B3tt
   | B3un => B3un
  end.

Definition andb3 (b1 b2:bool3) : bool3 := 
  match b1, b2 with 
    | B3tt, _    => b2 
    | B3ff, _    => B3ff
    | B3un, B3ff => B3ff
    | B3un, _    => B3un
  end.

Definition orb3 (b1 b2:bool3) : bool3 :=
  match b1, b2 with 
    | B3tt, _    => B3tt
    | B3ff, _    => b2
    | B3un, B3tt => B3tt
    | B3un, _    => B3un
  end.

Definition bool2bool3 (b: bool) : bool3 :=
  if b then B3tt else B3ff.

Definition b3_moredef (b1 : bool3) (b2: bool) : bool :=
  match b1 with
    | B3tt => b2
    | B3ff => negb b2
    | B3un => false
  end.

Lemma andb3T: forall b, andb3 b B3tt = b.
Proof. by intros[]. Qed.
Lemma andb3F: forall b, andb3 b B3ff = B3ff.
Proof. by intros[]. Qed.
Lemma orb3T: forall b, orb3 b B3tt = B3tt.
Proof. by intros[]. Qed.
Lemma orb3F: forall b, orb3 b B3ff = b.
Proof. by intros[]. Qed.

Lemma negb3P: forall x, bool2bool3 (negb x) = negb3 (bool2bool3 x).
Proof. by destruct x. Qed.

Lemma andb3P: forall x y, bool2bool3 (andb x y) = andb3 (bool2bool3 x) (bool2bool3 y).
Proof. by intros [] []. Qed.

Lemma orb3P: forall x y, bool2bool3 (orb x y) = orb3 (bool2bool3 x) (bool2bool3 y).
Proof. by intros [] []. Qed.

Lemma negb3_neg : forall x, negb3 (negb3 x) = x.
Proof. by intros []. Qed.

Lemma negb3_and : forall b1 b2, negb3 (andb3 b1 b2) = orb3 (negb3 b1) (negb3 b2).
Proof. by intros [] []. Qed.

Lemma negb3_or : forall b1 b2, negb3 (orb3 b1 b2) = andb3 (negb3 b1) (negb3 b2).
Proof. by intros [] []. Qed.

Hint Rewrite negb3_neg negb3_and negb3_or negb3P andb3P orb3P : vlib.

(* ************************************************************************** *)
(** * Natural numbers *)
(* ************************************************************************** *)

Delimit Scope coq_nat_scope with coq_nat.

(*
Notation "m + n" := (plus m n) : coq_nat_scope.
Notation "m - n" := (minus m n) : coq_nat_scope.
Notation "m * n" := (mult m n) : coq_nat_scope.
*)
Notation "m <= n" := (le m n) : coq_nat_scope.
Notation "m < n" := (lt m n) : coq_nat_scope.
Notation "m >= n" := (ge m n) : coq_nat_scope.
Notation "m > n" := (gt m n) : coq_nat_scope.


(** Support for case analysis *)

Inductive LtSpec (A : Type) (le lt : A -> A -> Prop) (x y: A): bool -> Prop := 
  | LtSpecLt : lt x y -> LtSpec le lt x y true
  | LtSpecGe : le y x -> LtSpec le lt x y false.

Inductive CmpSpecFull (A : Type) (lt : A -> A -> Prop) (x y: A)
  : bool -> bool -> bool -> bool -> bool -> bool -> comparison -> Prop := 
  | CmpSpecLt : lt x y -> CmpSpecFull lt x y true  true  false false false false Lt
  | CmpSpecEq : x = y  -> CmpSpecFull lt x y false true  true  true  false true  Eq
  | CmpSpecGt : lt y x -> CmpSpecFull lt x y false false false false true  true  Gt.

(** Boolean [<=] on [nat] *)
Definition len (m n:nat) := match tt with tt => leb m n end.

(** Boolean [<] on [nat]. *)
Definition ltn m n := len (S m) n.

(* NB: [ssrnat] instead treats [ltn x y] as notation for [len (S x) y]. *)

(** Overwrite Coq's standard notations *)

Notation "m <= n" := (len m n) : nat_scope.
Notation "m < n"  := (ltn m n) : nat_scope.
Notation "m >= n" := (n <= m) (only parsing) : nat_scope.
Notation "m > n"  := (n < m)  (only parsing) : nat_scope.


(** Shorter names for properties of [plus] and [minus]. *)

Lemma add0n : forall n, 0 + n = n.
Proof. done. Qed.
Lemma addSn : forall m n, S m + n = S (m + n).
Proof. done. Qed.
Lemma add1n : forall n, 1 + n = S n.
Proof. done. Qed.
Lemma addn0 : forall x, x + 0 = x.
Proof. auto with arith. Qed. 
Lemma addnS : forall m n, m + (S n) = S (m + n).
Proof. auto with arith. Qed.
Lemma addn1 : forall n, n + 1 = S n.
Proof. intros; omega. Qed.
Lemma addSnnS : forall m n, S m + n = m + (S n).
Proof. intros; omega. Qed.

Lemma addnC : forall x y, x + y = y + x.
Proof. intros; omega. Qed.
Lemma addnA : forall x y z, x + (y + z) = x + y + z.
Proof. intros; omega. Qed.
Lemma addnCA : forall x y z, x + (y + z) = y + (x + z).
Proof. intros; omega. Qed.
Lemma addnAC : forall x y z, x + y + z = x + z + y.
Proof. intros; omega. Qed.

Lemma addn_eq0 : forall m n, (m + n == 0) = (m == 0) && (n == 0). 
Proof. by intros; induction m. Qed.

Lemma eqn_addl : forall p m n, (p + m == p + n) = (m == n).
Proof. by intros; induction p. Qed.

Lemma eqn_addr : forall p m n, (m + p == n + p) = (m == n).
Proof. by intros; rewrite (addnC m), (addnC n), eqn_addl. Qed.

Lemma sub0n : forall x, 0 - x = 0.
Proof. intros; omega. Qed.
Lemma subn0 : forall x, x - 0 = x.
Proof. intros; omega. Qed.
Lemma subnn : forall x, x - x = 0.
Proof. intros; omega. Qed.
Lemma subSS : forall n m, S m - S n = m - n.
Proof. intros; omega. Qed.

Lemma subn_add2l : forall p m n, (p + m) - (p + n) = m - n.
Proof. intros; omega. Qed.
Lemma subn_add2r : forall p m n, (m + p) - (n + p) = m - n.
Proof. intros; omega. Qed.

Lemma subSnn : forall n, S n - n = 1.
Proof. intros; omega. Qed.
Lemma subn_sub : forall m n p, (n - m) - p = n - (m + p).
Proof. intros; omega. Qed.
Lemma subnAC : forall x y z, x - y - z = x - z - y.
Proof. intros; omega. Qed.

Hint Rewrite
  add0n addSn addn0 addnS addn_eq0 eqn_addl eqn_addr
  sub0n subn0 subnn subSS subn_add2l subn_add2r (* subn_sub *) : vlib.


(** ** Basic properties of comparisons *)

Lemma eq0S : forall n, (O == S n) = false.
Proof. done. Qed.
Lemma eqS0 : forall n, (S n == O) = false.
Proof. done. Qed.
Lemma eqSS : forall m n, (S m == S n) = (m == n).
Proof. done. Qed.
Lemma eqnn : forall n : nat, (n == n).
Proof. induction n; simpls. Qed.
Lemma eqnC : forall x y : nat, (x == y) = (y == x).
Proof. induct x [y]; apply IHx. Qed.

Hint Resolve eqnn.
Hint Rewrite eqnn eqSS eq0S eqS0 : vlib.

Lemma ltnE : forall m n, (m < n) = negb (n <= m).
Proof. induction m; destruct n; simpls; apply IHm. Qed.

Lemma lenE : forall m n, (m <= n) = negb (n < m).
Proof. induction m; destruct n; simpls; apply IHm. Qed.

Lemma lenE_sub : forall m n, (m <= n) = (m - n == 0).
Proof. induction m; destruct n; simpls; apply IHm. Qed.

Lemma ltnE_sub : forall m n, (m < n) = (m + 1 - n == 0).
Proof. induction m; destruct n; simpls; apply IHm. Qed.

Lemma leP : forall x y, LtSpec lt le x y (x <= y).
Proof.
  unfold len; intros x y; case (le_lt_dec x y); intro X;
  [rewrite leb_correct | rewrite leb_correct_conv]; vauto.
Qed.

Lemma ltP : forall x y, LtSpec le lt x y (x < y).
Proof. intros; rewrite ltnE; case leP; vauto. Qed.

Lemma ltn_correct: forall x y, (x < y)%coq_nat -> x < y.
Proof. by intros; case ltP; [|intro X; apply le_not_lt in X]. Qed. 

Lemma len_correct: forall x y, (x <= y)%coq_nat -> x <= y.
Proof. by intros; case leP; [|intro X; apply lt_not_le in X]. Qed. 

Lemma ltn_complete: forall x y, x < y -> (x < y)%coq_nat.
Proof. by intros ? ?; case ltP. Qed.

Lemma len_complete: forall x y, x <= y -> (x <= y)%coq_nat.
Proof. by intros ? ?; case leP. Qed.

Lemma lenP : forall x y, LtSpec ltn len x y (x <= y).
Proof. by intros; case_eq (x <= y) as H; vauto; right; rewrite ltnE, H. Qed.

Lemma ltnP : forall x y, LtSpec len ltn x y (x < y).
Proof. intros; rewrite ltnE; case lenP; vauto. Qed.

Lemma le0n : forall n, 0 <= n.
Proof. done. Qed.
Lemma len0 : forall n, (n <= 0) = (n == 0).
Proof. induction n; simpls. Qed.
Lemma lenn : forall n, n <= n.
Proof. induction n; simpls. Qed.
Lemma lenSn : forall n, n <= S n.
Proof. induction n; simpls. Qed.

Lemma lt0Sn : forall n, 0 < S n.
Proof. done. Qed.
Lemma ltn0  : forall n, (n < 0) = false.
Proof. intros []; simpls. Qed.
Lemma ltnn  : forall n, (n < n) = false.
Proof. induction n; simpls. Qed. 
Lemma ltnSn : forall n, (n < S n).
Proof. induction n; simpls. Qed.

Lemma leSS : forall m n, (S m <= S n) = (m <= n).
Proof. done. Qed.
Lemma ltSS :  forall m n, (S m < S n) = (m < n).
Proof. done. Qed.

Hint Resolve lenn lenSn ltnn ltnSn.

Lemma eq_len : forall m n, m = n -> m <= n.
Proof. by intros; subst. Qed.

Lemma ltnS : forall m n, (m < S n) = (m <= n).
Proof. induction m; destruct n; simpls. Qed.

Lemma leSn : forall m n, (S m <= n) = (m < n).
Proof. induction m; destruct n; simpls. Qed.

Hint Rewrite leSS le0n len0 lenn lenSn ltSS lt0Sn ltn0 ltnn ltnSn ltnS leSn : vlib.

Lemma lt0n : forall n, (0 < n) = negb (n == 0).
Proof. induction n; simpls. Qed.
Lemma lt0n_neq0 : forall n, 0 < n -> negb (n == 0).
Proof. by intro; rewrite lt0n. Qed.
Lemma eqn0_Nlt0n : forall n, n == 0 = negb (0 < n).
Proof. by intros[]. Qed.
Lemma neq0_lt0n : forall n, n == 0 = false -> 0 < n.
Proof. by intros; rewrite lt0n, H. Qed.
Hint Resolve lt0n_neq0 neq0_lt0n.

Lemma len_anti : forall m n, m <= n -> n <= m -> n = m.
Proof. induction m; destruct n; ins; auto. Qed.
Hint Immediate len_anti : lib.

Lemma eqn_leAle : forall m n, (m == n) = (m <= n) && (n <= m).
Proof. induct m [n]. Qed.

Lemma neqn_ltVlt : forall m n, negb (m == n) = (m < n) || (n < m).
Proof. induct m [n]. Qed. 

Lemma len_eqVlt : forall m n, len m n = (m == n) || (m < n).
Proof. induct m [n]. Qed. 

Lemma ltn_neqAle : forall m n, (m < n) = negb (m == n) && (m <= n).
Proof. induct m [n]. Qed. 

Lemma len_trans : forall n m p, m <= n -> n <= p -> m <= p.
Proof. induct n [m p]. Qed. 

Lemma len_ltn_trans : forall n m p, m <= n -> n < p -> m < p.
Proof. induct n [m p]. Qed. 

Lemma ltn_len_trans : forall n m p, m < n -> n <= p -> m < p.
Proof. induct n [m p]. Qed. 

Lemma ltn_trans : forall n m p, m < n -> n < p -> m < p.
Proof. induct n [m p]. Qed. 

Lemma ltnW : forall m n, m < n -> m <= n.
Proof. induct m [n]. Qed. 
Hint Resolve ltnW.

Lemma lenW : forall m n, m <= n -> m <= (S n).
Proof. induct m [n]. Qed. 

Lemma len_total : forall m n, (m <= n) || (n <= m).
Proof. induct m [n]. Qed. 

Lemma nat_comparenn: forall x, nat_compare x x = Eq. 
Proof. by induction x; [|rewrite nat_compare_S]. Qed.

Lemma cmpP : forall x y, 
  CmpSpecFull ltn x y (x < y) (x <= y) (x == y) (y == x) (y < x) (y <= x) (nat_compare x y).
Proof.
  intros; rewrite (ltnE y x), eqnC, len_eqVlt, lenE.
  case_eq (nat_compare x y); intro N.
  - by apply nat_compare_eq in N; subst; rewrite ltnn, eqnn; vauto.
  - apply nat_compare_lt, ltn_correct in N.
    rewrite N, orbT; simpl.
    by case eqnP; vauto; intros; clarify; autorewrite with vlib in N.
  - apply nat_compare_gt, ltn_correct in N.
    rewrite <-len_eqVlt, <- lenE; rewrite ltnE, len_eqVlt, lenE.
    rewrite N, orbT; simpl.
    by case eqnP; vauto; intros; clarify; autorewrite with vlib in N.
Qed.


(** Monotonicity lemmata *)

Lemma len_add2l : forall p m n, (p + m <= p + n) = (m <= n).
Proof. induction p; simpls. Qed.

Lemma ltn_add2l : forall p m n, (p + m < p + n) = (m < n).
Proof. induction p; simpls. Qed.

Lemma len_add2r : forall p m n, (m + p <= n + p) = (m <= n).
Proof. intros; rewrite (addnC n), (addnC m); apply len_add2l. Qed.

Lemma ltn_add2r : forall p m n, (m + p < n + p) = (m < n).
Proof. intros; rewrite (addnC n), (addnC m); apply ltn_add2l. Qed.

Lemma len_add : forall m1 m2 n1 n2,
  m1 <= n1 -> m2 <= n2 -> m1 + m2 <= n1 + n2.
Proof. intros????; repeat (case leP; simpls); intros; elimtype False; omega. Qed.

Lemma len_addr : forall m n, n <= n + m.
Proof. induction n; simpls. Qed.

Lemma len_addl : forall m n, n <= m + n.
Proof. by intros; rewrite addnC; apply len_addr. Qed.

Lemma ltn_addr : forall m n p, m < n -> m < n + p.
Proof. induction m; destruct n; intros; clarify; autorewrite with vlib; auto. Qed.

Lemma ltn_addl : forall m n p, m < n -> m < p + n.
Proof. by intros; rewrite addnC; apply ltn_addr. Qed.

Lemma lt0_addn : forall m n, (0 < m + n) = (0 < m) || (0 < n).
Proof. by intros [] []. Qed.

Lemma lt0_subn : forall m n, (0 < n - m) = (m < n).
Proof. induction m; destruct n; autorewrite with vlib; simpls. Qed.

Lemma subn_eq0 : forall m n, (m - n == 0) = (m <= n).
Proof. induction m; destruct n; autorewrite with vlib; simpls. Qed.

Lemma len_sub_add : forall m n p, (m - n <= p) = (m <= n + p).
Proof. induction m; destruct n; intros; autorewrite with vlib; simpls. Qed.

Lemma len_subr : forall m n, n - m <= n.
Proof. eby induction m; destruct n; simpls; eapply len_trans. Qed.

Lemma subnKC : forall m n, m <= n -> m + (n - m) = n.
Proof. induction m; destruct n; simpls; auto. Qed.

Lemma subnK : forall m n, m <= n -> (n - m) + m = n.
Proof. by intros; rewrite addnC; apply subnKC. Qed.

Lemma addn_subA : forall m n p, p <= n -> m + (n - p) = m + n - p.
Proof. intros???; case leP; ins; omega. Qed.

Lemma subn_subA : forall m n p, p <= n -> m - (n - p) = m + p - n.
Proof. intros???; case leP; ins; omega. Qed.

Lemma subKn : forall m n, m <= n -> n - (n - m) = m.
Proof. intros??; case leP; ins; omega. Qed.

Lemma len_subS : forall m n, m <= n -> S n - m = S (n - m).
Proof. induct m [n]. Qed.

Lemma ltn_subS : forall m n, m < n -> n - m = S (n - S m).
Proof. induct m [n]. Qed.

Lemma len_sub2r : forall p m n, (m <= n) -> (m - p <= n - p).
Proof. intros ???; case leP; case leP; ins; omega. Qed.

Lemma len_sub2l : forall p m n, m <= n -> p - n <= p - m.
Proof. intros ???; case leP; case leP; ins; omega. Qed.

Lemma len_sub2 : forall m1 m2 n1 n2,
  m1 <= m2 -> n2 <= n1 -> m1 - n1 <= m2 - n2.
Proof. intros????; repeat (case leP; simpls); ins; omega. Qed.

Lemma ltn_sub2r : forall p m n, p < n -> m < n -> m - p < n - p.
Proof. intros???; repeat (case ltP; simpls); ins; omega. Qed.

Lemma ltn_sub2l : forall p m n, m < p -> m < n -> p - n < p - m.
Proof. intros???; repeat (case ltP; simpls); ins; omega. Qed.

Lemma ltn_add_sub : forall m n p, (m + n < p) = (n < p - m).
Proof. intros???; repeat (case ltP; simpls); ins; omega. Qed.

Lemma lenE_diff: forall m n, m <= n -> exists k, n = m + k.
Proof.
  induction m; destruct n; ins; [by exists 0|by exists (S n)|].
  by destruct (IHm _ H) as [x ?]; exists x; f_equal.
Qed.

Lemma ltnE_diff: forall m n, m < n -> exists k, n = S (m + k).
Proof.
  induction m; destruct n; ins; [by exists n|].
  by destruct (IHm _ H) as [x ?]; exists x; f_equal.
Qed.

Lemma len_subnE : forall m n, (m <= m - n) = (n == 0) || (m == 0).
Proof.
  by intros[][]; intros; clarify; autorewrite with vlib; clarify; 
    rewrite <- ltn_add_sub, ltnE, len_addl.
Qed.


(** ** Properties concerning multiplication *)

Lemma mul0n : forall n, 0 * n = 0.
Proof. done. Qed.
Lemma muln0 : forall n, n * 0 = 0.
Proof. induction n; simpls. Qed.
Lemma mul1n : forall n, 1 * n = n.
Proof. intros; simpl; apply addn0. Qed.
Lemma muln1 : forall n, n * 1 = n.
Proof. induction n; simpls; auto. Qed.

Lemma mulSn : forall m n, S m * n = n + m * n.
Proof. done. Qed.
Lemma mulSnr : forall m n, S m * n = m * n + n.
Proof. intros; simpl; apply addnC. Qed.
Lemma mulnS : forall m n, m * S n = m + m * n.
Proof. by induction m; ins; rewrite IHm, addnCA. Qed.
Lemma mulnSr : forall m n, m * S n = m * n + m.
Proof. intros; rewrite mulnS; apply addnC. Qed.

Lemma mulnC : forall m n, m * n = n * m.
Proof. by induction n; simpls; rewrite mulnS, IHn. Qed.

Lemma muln_addl : forall x y z, (x + y) * z = x * z + y * z.
Proof. by intros; induction x; simpls; rewrite IHx, addnA. Qed.

Lemma muln_addr : forall x y z, x * (y + z) = x * y + x * z.
Proof. intros; rewrite mulnC, muln_addl; f_equal; apply mulnC. Qed.

Lemma muln_subl : forall x y z, (x - y) * z = x * z - y * z.
Proof. auto with arith. Qed.

Lemma muln_subr : forall x y z, x * (y - z) = x * y - x * z.
Proof. auto with arith. Qed. 

Lemma mulnA : forall x y z, x * (y * z) = x * y * z.
Proof. auto with arith. Qed.

Lemma mulnCA : forall x y z, x * (y * z) = y * (x * z).
Proof. by intros; rewrite mulnA, (mulnC x), mulnA. Qed.

Lemma mulnAC : forall x y z, x * y * z = x * z * y.
Proof. by intros; rewrite <- mulnA, (mulnC y), mulnA. Qed.

Lemma eqn_mul0 : forall m n, (m * n == 0) = (m == 0) || (n == 0).
Proof. by intros[][]; simpls; rewrite muln0. Qed.

Lemma eqn_mul1 : forall m n, (m * n == 1) = (m == 1) && (n == 1).
Proof. by intros[|[]][|[]]; simpls; rewrite ?muln0. Qed.

Lemma lt0_muln : forall m n, (0 < m * n) = (0 < m) && (0 < n).
Proof. by intros[][]; simpls; rewrite muln0. Qed.

Lemma len_pmull : forall m n, 0 < n -> m <= n * m.
Proof. destruct n; ins; apply len_addr. Qed.

Lemma len_pmulr : forall m n, 0 < n -> m <= m * n.
Proof. intros[][]; ins; rewrite mulnS, addnCA; apply len_addr. Qed.

Lemma len_mul2l : forall m n1 n2, (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof. 
intros; rewrite !lenE_sub, <- muln_subr; destruct m; simpls. 
by destruct (n1 - n2); simpls; rewrite muln0.
Qed.

Lemma len_mul2r : forall m n1 n2, (n1 * m <= n2 * m) = (m == 0) || (n1 <= n2).
Proof. by intros; rewrite <- len_mul2l, !(mulnC m). Qed.

Lemma len_mul : forall m1 m2 n1 n2, m1 <= n1 -> m2 <= n2 -> m1 * m2 <= n1 * n2.
Proof.
intros; destruct (lenE_diff H); destruct (lenE_diff H0); subst.
rewrite muln_addl; eapply len_trans, len_addr.
by rewrite muln_addr; eapply len_trans, len_addr.
Qed.

Lemma eqn_mul2l : forall m n1 n2, (m * n1 == m * n2) = (m == 0) || (n1 == n2).
Proof.
destruct m; simpls; intros; rewrite !(mulnC m).
revert n2; induction n1; destruct n2; autorewrite with vlib; simpls.
by rewrite <- IHn1, !(addnC m), !addnA, eqn_addr.
Qed. 

Lemma eqn_mul2r : forall m n1 n2, (n1 * m == n2 * m) = (m == 0) || (n1 == n2).
Proof. by intros; rewrite <- !(mulnC m), eqn_mul2l. Qed. 

Lemma len_pmul2l : forall m n1 n2, 0 < m -> (m * n1 <= m * n2) = (n1 <= n2).
Proof. by intros; rewrite len_mul2l; destruct m. Qed. 
Implicit Arguments len_pmul2l [m n1 n2].

Lemma len_pmul2r : forall m n1 n2, 0 < m -> (n1 * m <= n2 * m) = (n1 <= n2).
Proof. by intros; rewrite len_mul2r; destruct m. Qed. 
Implicit Arguments len_pmul2r [m n1 n2].

Lemma eqn_pmul2l : forall m n1 n2, 0 < m -> (m * n1 == m * n2) = (n1 == n2).
Proof. by intros; rewrite eqn_mul2l; destruct m. Qed. 
Implicit Arguments eqn_pmul2l [m n1 n2].

Lemma eqn_pmul2r : forall m n1 n2, 0 < m -> (n1 * m == n2 * m) = (n1 == n2).
Proof. by intros; rewrite eqn_mul2r; destruct m. Qed. 
Implicit Arguments eqn_pmul2r [m n1 n2].

Lemma ltn_mul2l : forall m n1 n2, (m * n1 < m * n2) = (0 < m) && (n1 < n2).
Proof.
destruct m; simpls; intros; rewrite !(mulnC m).
revert n2; induction n1; destruct n2; autorewrite with vlib; simpls.
by rewrite <- IHn1, !(addnC m), !addnA; rewrite ltn_add2r.
Qed. 

Lemma ltn_mul2r : forall m n1 n2, (n1 * m < n2 * m) = (0 < m) && (n1 < n2).
Proof. by intros; rewrite <- !(mulnC m), ltn_mul2l. Qed. 

Lemma ltn_pmul2l : forall m n1 n2, 0 < m -> (m * n1 < m * n2) = (n1 < n2).
Proof. by intros; rewrite ltn_mul2l; destruct m. Qed. 
Implicit Arguments ltn_pmul2l [m n1 n2].

Lemma ltn_pmul2r : forall m n1 n2, 0 < m -> (n1 * m < n2 * m) = (n1 < n2).
Proof. by intros; rewrite ltn_mul2r; destruct m. Qed. 
Implicit Arguments ltn_pmul2r [m n1 n2].

Lemma ltn_mul : forall m1 m2 n1 n2, m1 < n1 -> m2 < n2 -> m1 * m2 < n1 * n2.
Proof. 
intros; rewrite <- leSn in *; eapply len_trans, len_mul; try eassumption.
by simpls; autorewrite with vlib; eapply len_trans, len_addl; rewrite len_mul2l, lenSn, orbT.
Qed.

Lemma ltn_Pmull : forall m n, 1 < n -> 0 < m -> m < n * m.
Proof. by intros; rewrite <- (mul1n m) at 1; rewrite ltn_mul2r, H, H0. Qed.

Lemma ltn_Pmulr : forall m n, 1 < n -> 0 < m -> m < m * n.
Proof. by intros; rewrite <- (muln1 m) at 1; rewrite ltn_mul2l, H, H0. Qed.

(** auto setup *)

Lemma lenS : forall m n, n <= m -> n <= S m.
Proof. eauto using len_trans. Qed.

Lemma ltn_of_leS : forall n m : nat, (n < m) -> (S n <= m). 
Proof. by intros; rewrite leSn. Qed.

Lemma leSn_of_lt : forall n m : nat, (S n <= m) -> (n < m). 
Proof. by intros; rewrite <- leSn. Qed.

Lemma len_mul2l_imp : forall m n1 n2, n1 <= n2 -> (m * n1 <= m * n2).
Proof. by intros; rewrite len_mul2l, H, orbT. Qed.

Lemma len_mul2r_imp : forall m n1 n2, n1 <= n2 -> (n1 * m <= n2 * m).
Proof. by intros; rewrite len_mul2r, H, orbT. Qed.

Hint Resolve lenS len_addl len_addr len_trans len_add2r len_add2l len_sub2r len_sub2l
             len_mul2l_imp len_mul2r_imp : vlib.
Hint Immediate ltn_of_leS leSn_of_lt: vlib.

Hint Rewrite add0n addSn addn0 addnS addn_eq0 eqn_addl eqn_addr
  sub0n subn0 subnn subSS subn_add2l subn_add2r (* subn_sub *)
  nat_comparenn
  len_add2l ltn_add2l len_add2r ltn_add2r len_addr len_addl
  lt0_addn lt0_subn len_sub_add len_subnE
  mul0n muln0 mul1n muln1
(* left out the mulnS rules; unsure about the next 4 *)
  muln_addl muln_addr muln_subl muln_subr 
  eqn_mul0 eqn_mul1 lt0_muln
  len_mul2l len_mul2r eqn_mul2l eqn_mul2r ltn_mul2l ltn_mul2r : vlib.

Hint Rewrite addnA mulnA : vlibA.


(** [iter f n] applies [n] times the function [f].
    This definition is not-tail-recursive: it is more convenient for proofs. *)
Fixpoint iter (A : Type) n (f : A -> A) (v : A): A :=
  match n with 
    | O => v
    | S n => f (iter n f v)
  end.

(** Tail-recursive version *)

Fixpoint iter_rec (A : Type) n (f : A -> A) (v : A): A :=
  match n with 
    | O => v
    | S n => iter_rec n f (f v)
  end.

Lemma iter_recS: forall A n f (v: A), iter_rec (S n) f v = f (iter_rec n f v).
Proof. by induction n; intros; simpl; [|rewrite <- IHn]. Qed.

Lemma iter_recE: forall A n f (v: A), iter_rec n f v = iter n f v.
Proof. by induction n; intros; [|rewrite iter_recS, IHn]. Qed.


(* ************************************************************************** *)
(** * Integers *)
(* ************************************************************************** *)

Section ZZZ.

Local Open Scope Z_scope.

Lemma Zplus_mod_same: forall a n : Z, (a + n) mod n = a mod n.
Proof.
  by intros; rewrite Zplus_mod, Z_mod_same_full, Zplus_0_r, Zmod_mod.
Qed.

Lemma Zmod_too_small:
  forall a n, -n <= a < 0 -> a mod n = n + a.
Proof.
  intros. rewrite <- Zplus_mod_same, Zmod_small; omega.
Qed.

Lemma Zmod_too_big:
  forall a n, n <= a < n + n -> a mod n = a - n.
Proof.
  intros; rewrite <- (Zminus_0_r a) at 1;
  rewrite <- (Z_mod_same_full n), Zminus_mod_idemp_r, Zmod_small; omega.
Qed.

Lemma Zopp_mod_idemp: forall a m, - (a mod m) mod m = - a mod m.
Proof. by apply (Zminus_mod_idemp_r 0). Qed.

Lemma Zmod_opp_expand: forall a b, - a mod b = (b - a) mod b.
Proof.
intros; rewrite <- (Zplus_mod_same); f_equal; omega.
Qed.

Lemma Zmod_eqD :
  forall a b m (H: a mod m = b mod m) (NEQ: m <> 0), exists k, a = b + k * m.
Proof.
  intros; apply Zeq_minus, (f_equal (fun x => Zmod x m)) in H.
  rewrite <- Zminus_mod, Zmod_0_l in H.
  exists ((a - b) / m).
  pose proof (Z.div_mod (a - b) _ NEQ); rewrite H in *.
  rewrite Z.mul_comm; omega.
Qed.

Lemma ZdoubleE: forall x, Zdouble x = x * 2.
Proof. by intros; rewrite Zmult_comm. Qed.

Lemma ZltP:
  forall x y, LtSpec Zle Zlt x y (Zlt_bool x y).
Proof.
  intros; unfold Zlt_bool, Zle_bool.
  by case_eq (Zcompare x y); simpl; constructor; try done;
     (unfold Zle; rewrite <- (Zcompare_antisym), H). 
Qed.

Lemma ZleP:
  forall x y, LtSpec Zlt Zle x y (Zle_bool x y).
Proof.
  intros; unfold Zlt_bool, Zle_bool.
  case_eq (Zcompare x y); simpl; constructor;
    try (by unfold Zle; rewrite H);
    try (by unfold Zlt; rewrite <- (Zcompare_antisym), H). 
Qed.

Lemma ZcmpP:
  forall x y, CmpSpecFull Zlt x y 
    (Zlt_bool x y) (Zle_bool x y) (Zeq_bool x y) (Zeq_bool y x)
    (Zlt_bool y x) (Zle_bool y x) (Zcompare x y).
Proof.
  intros; unfold Zlt_bool, Zle_bool, Zeq_bool; rewrite <- (Zcompare_antisym x).
  case_eq (Zcompare x y); simpl; constructor; try done.
    by eapply Zcompare_Eq_eq.
  by unfold Zlt; rewrite <- (Zcompare_antisym), H.
Qed.

End ZZZ.

(* Basic rewrites about modular arithmetic *)
Hint Rewrite 
  Zmod_0_l Z_mod_same_full
  Zplus_mod_idemp_l Zplus_mod_idemp_r 
  Zminus_mod_idemp_l Zminus_mod_idemp_r Zopp_mod_idemp : vlib.
