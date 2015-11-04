Require Import Predefs.
Require Import KVStore.
Require Import Coq.Strings.String.
Require Import ReflectiveAbstractSemantics.
Require KVSAlg1 KVSAlg2 KVSAlg3.

Import NPeano.

Open Scope string_scope.

Definition max_nid:= 2.

Axiom max_nid_eq: max_nid = SysPredefs.MaxNId.

Module SyntaxArg <: SyntaxPar.
  Definition Val := nat.
  Definition init_val : nat := 10.
End SyntaxArg.


Module ListClient (AlgDef: AlgDef) (Parametric: Parametric AlgDef) (CauseObl: CauseObl AlgDef).
  Module Import Alg := ExecToAbstExec AlgDef Parametric CauseObl SyntaxArg.

  Module Import AECarrier <: AbsExecCarrier SyntaxArg.
    Module AbsExec:= Alg.AExec.
  End AECarrier.

  Module Import RAS:= ReflAbsSem SyntaxArg AECarrier.
  Delimit Scope Prog with Prog.
  Bind Scope Prog with Prog.
  Bind Scope Prog with PProg.

  Notation "'put' '(' k ',' v ')' ;; c" := (put k v c%Prog) (right associativity, at level 100) : Prog.
  Notation "x <- 'get' '(' k ')' ;; c" := (get k (fun x => c%Prog)) (right associativity, at level 100) : Prog.
  Notation "'assert' '(' t ')' ;; c" := (if t%bool then c%Prog else fault) (right associativity, at level 100, t at level 0) : Prog.

  (* Linked list layout

  Address:    3   4         5   6         1   2
            ---------     ---------     ---------
  Value:    | 1 | 5 +---->| 2 | 1 +---->| 3 | 0 X
            ---------     ---------     ---------
              ^             ^             ^
     7        |             |             |
   --------   |             |             |
   | head +---+-------------+-------------+-----= 0
   --------
  *)

  Let null := 0.
  Let head := 7.
  Let init := 10.

  Definition prog1: PProg := 
    fun n =>
      match n with
        | 0 =>
          (* first node *)
          put (2,null);;
          put (1,3);;
          put (head,1);; (* update head *)
          (* second node *)
          put (6,1);;
          put (5,2);;
          put (head,5);; (* update head *)
          (* third node *)
          put (4,5);;
          put (3,1);;
          put (head,3);; (* update head *)
          skip

        | 1 =>
          node1 <- get(head);;
          if (node1 =? init) || (node1 =? null) then
            skip
          else
            item1 <- get(node1);;
            node2 <- get(S node1);;
            if node2 =? null then
              skip
            else
              item2 <- get(node2);;
              node3 <- get(S node2);;
              assert (item1 <? item2);;
              if node3 =? null then
                skip
              else
                item3 <- get(node3);;
                node4 <- get(S node3);;
                assert (item2 <? item3);;
                assert (node4 =? null);;
                skip
        | _ => skip
      end%Prog%bool.


  Lemma CausallyContent_Prog1: CausallyContent prog1.
  Proof. (* Note: "fast" is a relative term. This will take a few minutes... *)
    fast_casually_content max_nid max_nid_eq 50.
  Qed.

  Lemma CauseConsistent_Prog1: forall h n,
    Alg.CExec.history (Alg.CExec.init prog1) h ->
    forall l, List.In l h -> l <> Alg.CExec.fault_label n.
  Proof.
    intros h n Hrun; intros.
    eapply FaultFreedom; eauto.
    eapply CausallyContent_Prog1; eauto.
  Qed.


End ListClient.




(* Corollary: causally-consistent for Alg1 *)
Module Alg1.
  Import KVSAlg1.
  Module C:= ListClient KVSAlg1.KVSAlg1 KVSAlg1Parametric KVSAlg1CauseObl.

  Lemma CauseConsistent_Prog1: forall h n,
    C.Alg.CExec.history (C.Alg.CExec.init C.prog1) h ->
    forall l, List.In l h -> l <> C.Alg.CExec.fault_label n.
  Proof.
    exact C.CauseConsistent_Prog1.
  Qed.

End Alg1.


(* Corollary: causally-consistent for Alg2 *)
Module Alg2.
  Import KVSAlg2.
  Module C:= ListClient KVSAlg2.KVSAlg2 KVSAlg2Parametric KVSAlg2CauseObl.

  Lemma CauseConsistent_Prog1: forall h n,
    C.Alg.CExec.history (C.Alg.CExec.init C.prog1) h ->
    forall l, List.In l h -> l <> C.Alg.CExec.fault_label n.
  Proof.
    exact C.CauseConsistent_Prog1.
  Qed.

End Alg2.


(* Corollary: causally-consistent for Alg3 *)
Module Alg3.
  Import KVSAlg3.
  Module C:= ListClient KVSAlg3.KVSAlg3 KVSAlg1Parametric KVSAlg3CauseObl.

  Lemma CauseConsistent_Prog1: forall h n,
    C.Alg.CExec.history (C.Alg.CExec.init C.prog1) h ->
    forall l, List.In l h -> l <> C.Alg.CExec.fault_label n.
  Proof.
    exact C.CauseConsistent_Prog1.
  Qed.

End Alg3.




