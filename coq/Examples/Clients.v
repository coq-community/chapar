Require Import Predefs.
Require Import KVStore.
Require Import Coq.Strings.String.
Require Import ReflectiveAbstractSemantics.
Require KVSAlg1 KVSAlg2 KVSAlg3.

Open Scope string_scope.

Definition max_nid:= 3.
(* PERFORMANCE:
  The following gives a very rough example of how performance will scale as we add threads to check
  (even the prog1 and prog2 use at most 3 threads, the nondeterministic update will apply to all N threads)
  Threads  Prog1 (sec)   Prog2 (sec)
  3         0.015625      0.03125
  4         0.96875       0.96875
  5        82
*)

Axiom max_nid_eq: max_nid = SysPredefs.MaxNId.

Module SyntaxArg <: SyntaxPar.
  Definition Val := string.
  Definition init_val := "".
End SyntaxArg.


Module Clients (AlgDef: AlgDef) (Parametric: Parametric AlgDef) (CauseObl: CauseObl AlgDef).
  Module Import Alg := ExecToAbstExec AlgDef Parametric CauseObl SyntaxArg.

  Module Import AECarrier <: AbsExecCarrier SyntaxArg.
    Module AbsExec:= Alg.AExec.
    Definition CausallyContent := CausallyContent.
  End AECarrier.

  Module Import RAS:= ReflAbsSem SyntaxArg AECarrier.
  Delimit Scope Prog with Prog.
  Bind Scope Prog with Prog.
  Bind Scope Prog with PProg.

  Notation "'put' '(' k ',' v ')' ;; c" := (put k v c%Prog) (right associativity, at level 100) : Prog.
  Notation "x <- 'get' '(' k ')' ;; c" := (get k (fun x => c%Prog)) (right associativity, at level 100) : Prog.
  Notation "'assert' '(' t ')' ;; c" := (if t%bool then c%Prog else fault) (right associativity, at level 100, t at level 0) : Prog.

  Definition Photo := 1.
  Definition Post := 2.

  Definition prog_photo_upload: PProg := 
    fun n =>
      match n with
        | 0 =>
          put (Photo, "NewPhoto");;
          put (Post, "Uploaded");;
          skip

        | 1 =>
          post <- get (Post);;
          if (string_dec post "Uploaded") then
             photo <- get (Photo);;
             if string_dec post "" then
               fault
             else
               skip
          else
            skip

        | _ => skip
      end%Prog.

  Lemma CausallyContent_Prog_PhotoUpload: CausallyContent prog_photo_upload.
  Proof.
    fast_casually_content max_nid max_nid_eq 50.
  Qed.

  Lemma CauseConsistent_Prog_PhotoUpload: forall h n,
    Alg.CExec.history (Alg.CExec.init prog_photo_upload) h ->
    forall l, List.In l h -> l <> Alg.CExec.fault_label n.
  Proof.
    intros h n Hrun; intros.
    eapply FaultFreedom; eauto.
    eapply CausallyContent_Prog_PhotoUpload; eauto.
  Qed.

  Definition prog_lost_ring: PProg := 
    fun n =>
      match n with
        | 0 =>
          put (1, "I Lost my ring!");;
          put (1, "Nevermind -- I just found it. :)");;
          skip

        | 1 =>
          post <- get (1);;
          if (string_dec post "Nevermind -- I just found it. :)") then
             put (2, "Glad to hear!");;
             skip
          else
            skip

        | 2 =>
          postB <- get (2);;
          if (string_dec postB "Glad to hear!") then
             postA <- get (1);;
             if (string_dec postA "Nevermind -- I just found it. :)") then
               skip
             else
               fault
          else
            skip

        | _ => skip
      end%Prog.

  Lemma CausallyContent_Prog_LostRing: CausallyContent prog_lost_ring.
  Proof.
    fast_casually_content max_nid max_nid_eq 50.
  Qed.

  Lemma CauseConsistent_Prog_LostRing: forall h n,
    Alg.CExec.history (Alg.CExec.init prog_lost_ring) h ->
    forall l, List.In l h -> l <> Alg.CExec.fault_label n.
  Proof.
    intros h n Hrun; intros.
    eapply FaultFreedom; eauto; intros.
    eapply CausallyContent_Prog_LostRing; eauto.
  Qed.

  Definition string_beq (s1 s2: string):= if string_dec s1 s2 then true else false.

  Definition prog_photo_album: PProg := 
    fun n =>
      match n with
        | 0 =>
          put (1, "uploads photos");;
          put (2, "creates album");;
          put (3, "adds photos to album");;
          skip

        | 1 =>
          z <- get (3);;
          y <- get (2);;
          x <- get (1);;
          assert (if string_beq z "adds photos to album" then string_beq y "creates album" else true);;
          assert (if string_beq y "creates album" then string_beq x "uploads photos" else true);;
          skip

        | _ => skip
      end%Prog.

  Lemma CausallyContent_Prog_PhotoAlbum: CausallyContent prog_photo_album.
  Proof.
    fast_casually_content max_nid max_nid_eq 50.
  Qed.

  Lemma CauseConsistent_Prog_PhotoAlbum: forall h n,
    Alg.CExec.history (Alg.CExec.init prog_photo_album) h ->
    forall l, List.In l h -> l <> Alg.CExec.fault_label n.
  Proof.
    intros h n Hrun; intros.
    eapply FaultFreedom; eauto; intros.
    eapply CausallyContent_Prog_PhotoAlbum; eauto.
  Qed.

End Clients.



(* Corollary: causally-consistent for Alg1 *)
Module Alg1.
  Import KVSAlg1.
  Module C:= Clients KVSAlg1.KVSAlg1 KVSAlg1Parametric KVSAlg1CauseObl.

  Lemma CauseConsistent_Prog1: forall h n,
    C.Alg.CExec.history (C.Alg.CExec.init C.prog_photo_upload) h ->
    forall l, List.In l h -> l <> C.Alg.CExec.fault_label n.
  Proof.
    exact C.CauseConsistent_Prog_PhotoUpload.
  Qed.

  Lemma CauseConsistent_Prog_LostRing: forall h n,
    C.Alg.CExec.history (C.Alg.CExec.init C.prog_lost_ring) h ->
    forall l, List.In l h -> l <> C.Alg.CExec.fault_label n.
  Proof.
    exact C.CauseConsistent_Prog_LostRing.
  Qed.
  
  Lemma CauseConsistent_Prog_PhotoAlbum: forall h n,
    C.Alg.CExec.history (C.Alg.CExec.init C.prog_photo_album) h ->
    forall l, List.In l h -> l <> C.Alg.CExec.fault_label n.
  Proof.
    exact C.CauseConsistent_Prog_PhotoAlbum.
  Qed.
  
End Alg1.


(* Corollary: causally-consistent for Alg2 *)
Module Alg2.
  Import KVSAlg2.
  Module C:= Clients KVSAlg2.KVSAlg2 KVSAlg2Parametric KVSAlg2CauseObl.

  Lemma CauseConsistent_Prog_PhotoUpload: forall h n,
    C.Alg.CExec.history (C.Alg.CExec.init C.prog_photo_upload) h ->
    forall l, List.In l h -> l <> C.Alg.CExec.fault_label n.
  Proof.
    exact C.CauseConsistent_Prog_PhotoUpload.
  Qed.

  Lemma CauseConsistent_Prog2: forall h n,
    C.Alg.CExec.history (C.Alg.CExec.init C.prog_lost_ring) h ->
    forall l, List.In l h -> l <> C.Alg.CExec.fault_label n.
  Proof.
    exact C.CauseConsistent_Prog_LostRing.
  Qed.
  
  Lemma CauseConsistent_Prog_PhotoAlbum: forall h n,
    C.Alg.CExec.history (C.Alg.CExec.init C.prog_photo_album) h ->
    forall l, List.In l h -> l <> C.Alg.CExec.fault_label n.
  Proof.
    exact C.CauseConsistent_Prog_PhotoAlbum.
  Qed.
  
End Alg2.


(* Corollary: causally-consistent for Alg3 *)
Module Alg3.
  Import KVSAlg3.
  Module C:= Clients KVSAlg3.KVSAlg3 KVSAlg1Parametric KVSAlg3CauseObl.

  Lemma CauseConsistent_Prog_PhotoUpload: forall h n,
    C.Alg.CExec.history (C.Alg.CExec.init C.prog_photo_upload) h ->
    forall l, List.In l h -> l <> C.Alg.CExec.fault_label n.
  Proof.
    exact C.CauseConsistent_Prog_PhotoUpload.
  Qed.

  Lemma CauseConsistent_Prog2: forall h n,
    C.Alg.CExec.history (C.Alg.CExec.init C.prog_lost_ring) h ->
    forall l, List.In l h -> l <> C.Alg.CExec.fault_label n.
  Proof.
    exact C.CauseConsistent_Prog_LostRing.
  Qed.
  
  Lemma CauseConsistent_Prog_PhotoAlbum: forall h n,
    C.Alg.CExec.history (C.Alg.CExec.init C.prog_photo_album) h ->
    forall l, List.In l h -> l <> C.Alg.CExec.fault_label n.
  Proof.
    exact C.CauseConsistent_Prog_PhotoAlbum.
  Qed.
  
End Alg3.









