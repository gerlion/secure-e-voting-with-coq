Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
From Groups Require Import groups module vectorspace dualvectorspaces matrices 
  matricesF matricesField modulevectorspace groupfromring.
Require Import sigmaprotocolPlus.
Require Import sigmaprotocolPlus5.
Require Import List.
Require Import Field.
Require Import cryptoprim.
Require Coq.Classes.RelationClasses.
From Coq Require Import Basics Morphisms Setoid.
From CoLoR Require Import RelDec OrdSemiRing LogicUtil RelExtras EqUtil NatUtil ZUtil SemiRing.
Require Import Coq.Vectors.Vector.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import CoLoR.Util.Vector.VecArith.
Require Import CoLoRmatrix.
Require Import VectorUtil.
Require Import BayerGrothSupport.
Require Import BGZero.
Require Import BGHadProduct.
Require Import BGSingleProd.
Set Implicit Arguments.


Module Type ProdArg 
    (* First all the modules related to Hadamard product *)
    (Message Ciphertext Commitment : GroupSig)(Ring : RingSig)
    (Field : FieldSig)(VS2 : VectorSpaceSig Commitment Field)
    (VS1 : VectorSpaceSig Ciphertext Field)(Chal : GroupFromRing Field)
    (MVS : VectorSpaceModuleSameGroup Ciphertext Ring Field VS1)
    (VS3 : VectorSpaceSig Message Field)(Hack : Nat)(M : Nat)
    (enc : EncryptionSchemePlus Message Ciphertext Ring Field VS1 VS3 MVS)
    (support : BGSupport Message Ciphertext Commitment Ring Field VS2 VS1 MVS VS3 
    Hack M enc)(sig2 : BGZeroArg Message Ciphertext Commitment Ring Field VS2 VS1 Chal 
    MVS VS3 Hack M enc support) 
    (bgHadProdBase : BGHadProd Message Ciphertext Commitment Ring Field VS2 VS1 Chal MVS
    VS3 Hack M enc support sig2)
    (bgHadProd : SigmaPlusTo5simTofull Chal sig2 bgHadProdBase)
    (sig5 : SigmaPlus5Comp Chal sig2 bgHadProd)
    (* Now Single Vector prod  *)
    (sig : BGSingleProd Commitment Field VS2 Chal Hack)
    <: SigmaPlus5To5 Chal sig sig5.

  Import support.

  (* N = nm *)
  Let n := S (S (S Hack.N)).      (* n *)
  Let m := S (S M.N).             (* m *)
  Import Field.

  Import Mo.
  Import Mo.mat.

  Module EPC := ExtendComScheme Commitment Field VS2 mat.
  Import EPC.
  Import EPC.MoM.
  Import PC.

  Module ALenc := EncryptionSchemeProp Message Ciphertext Ring Field VS1 MVS enc. 
  Import ALenc.
  Import HardProb.

  Module ALR := RingAddationalLemmas Ring.

  Import VS2.
  Import Commitment.

  Module G2 := GroupFromFieldIns Field. 

  (* ck cA b *)
  Definition St:Type := G*(VG n)*(VG m)*F.  

  (* A r *)
  Definition W:Type := (vector (VF n) m)*(VF m).

  Definition Rel (s : St)(w : W) : bool :=
    (* let '(h,hs,cA,b) := s in *)
    let h := s.1.1.1 in
    let hs := s.1.1.2 in
    let cA := s.1.2 in
    let b := s.2 in
    (* let '(A,r) := w in *)
    let A := w.1 in
    let r := w.2 in
    
    (VG_eq cA (comEPC h hs A r)) && 
        (Fbool_eq (VF_prod (Vfold_left (VF_mult (n:=n)) (VF_one n) A)) b).

  Definition C : Type := G.

  Definition R : Type := F.

  Definition P0 (s : St)(rand : R)(w : W) : (St*C) :=
    let '(h,hs,cA,b) := s in
    let '(A,r) := w in
    
    (s, EPC h hs (Vfold_left (VF_mult (n:=n)) (VF_one n) A) rand).

  (* sig.St is  h hs c b *)
  Definition ToStSig  (sc : St*C) : sig.St :=
    let '(h,hs,cA,b,c) := sc in
    (h, hs, c, b).

  (* a r *)   
  Definition ToWitSig (sc : St*C)(rand : R)(w : W) : sig.W :=
    let '(h,hs,cA,b,c) := sc in
    let '(A,r) := w in
  
    ((Vfold_left (VF_mult (n:=n)) (VF_one n) A), rand).
    

  Definition ToStSig5 (s : St*C) : sig5.St :=
    let '(h,hs,cA,b,c) := s in
    (h, hs, cA, c).

  Definition ToWitSig5 (sc : St*C)(rand : R)(w : W) : sig5.W :=
    let '(h,hs,cA,b,c) := sc in
    let '(A,r) := w in

    (A,r,(Vfold_left (VF_mult (n:=n)) (VF_one n) A),rand).

  Lemma ToValid : forall s w r,
    Rel s w ->
   sig.Rel (ToStSig (P0 s r w)) (ToWitSig (P0 s r w) r w) /\
   sig5.Rel (ToStSig5 (P0 s r w)) (ToWitSig5 (P0 s r w) r w).
  Proof.
    pose module_abegrp.
    intros. unfold Rel, sig.Rel, sig5.Rel, bgHadProd.Rel, bgHadProdBase.Rel,  
    ToStSig, ToStSig5, ToWitSig, ToWitSig5, P0 in *. destruct s, p, p. destruct w.
    apply andb_true_iff in H. destruct H.  apply F_bool_eq_corr in H0.
    apply VGeq in H. split.
    + apply andb_true_iff. split.
    ++ apply bool_eq_corr. rewrite Prod_right_replace. trivial.
    ++ apply F_bool_eq_corr. rewrite Prod_right_replace in H0.
     rewrite <- H0. trivial.
    + apply andb_true_iff. split. apply andb_true_iff. split. 
    ++ apply VGeq. do 3 rewrite Prod_right_replace. do 2 rewrite Prod_left_replace.
    apply H.
    ++ apply bool_eq_corr. do 4 rewrite Prod_right_replace. 
    rewrite Prod_left_replace. trivial. 
    ++ apply VF_beq_true. rewrite Prod_right_replace. rewrite Prod_left_replace.
    trivial.
  Qed.

  Definition TE : Type := F. 

  Lemma pres_p0 : forall (s : St)(r : R)(w : W), 
      (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. unfold P0. destruct s, w, p, p. trivial.
  Qed.

  Definition extractor (w : sig5.W)(w' : sig.W) :  W :=
    let '(A,r,B,s) := w in
    (A,r).

  Definition argument (s : St)(c: C) : Prop :=
    let '(h,hs,cA,b) := s in
    exists a b c f, a <> b /\ EPC h hs a c = EPC h hs b f.

  Lemma M1_nonzero : sig5.M1 > 0. (* This is an edge case we had to take care of *) 
  Proof.
     intros. unfold sig5.M1, sig2.M . lia.
  Qed.

  Lemma special_soundness : forall s c (w : sig.W)(w1 : sig5.W),
    sig.Rel (ToStSig (s,c)) w ->
    sig5.Rel (ToStSig5 (s,c)) w1 ->
    Rel s (extractor w1 w) \/ argument s c.
  Proof.
    pose module_abegrp. 
    intros. unfold sig.Rel, sig5.Rel, Rel, extractor, bgHadProd.Rel,
    bgHadProdBase.Rel, ToStSig, ToStSig5 in *. destruct s, w, p, p, w1, p, p.
    apply andb_true_iff in H0. destruct H0. apply andb_true_iff in H0. destruct H0. 
    apply VGeq in H0. do 3 rewrite Prod_right_replace in H0. 
    do 4 rewrite Prod_left_replace in H0. apply VF_beq_true in H1. 
    apply andb_true_iff in H. destruct H. apply bool_eq_corr in H. 
    apply F_bool_eq_corr in H3. apply bool_eq_corr in H2.
    rewrite Prod_right_replace in H. do 4 rewrite Prod_right_replace in H2.
    rewrite Prod_right_replace in H1. do 3 rewrite Prod_left_replace in H1.
    rewrite Prod_left_replace in H2. case_eq (VF_beq v v2); intros.
    + left. apply andb_true_iff.  apply VF_beq_true in H4. split. 
    ++ apply VGeq. apply H0. 
    ++ apply F_bool_eq_corr. unfold bgHadProdBase.n in *. unfold n. symmetry in H1.
    rewrite H1. rewrite H3. rewrite H4. trivial.
    + right. exists v, v2, f0, f1. split. apply VF_beq_false in H4.  trivial.
    unfold sig.n, bgHadProdBase.n, n in *. symmetry in H. unfold sig.EPC.EPC,
    EPC, support.EPC.EPC in *. rewrite H. symmetry in H2. rewrite H2. trivial.
  Qed.

  Definition X : Type := VF n.

  Definition simulator (s : St)(t : TE) : C := 
    let '(h,hs,cA,b) := s in
    EPC h hs (VF_zero n) t.
    
  Definition simMap   (s : St)(w : W)(x : X)(r : R) : TE :=
    let '(A, r') := w in
    r + (VF_inProd x (Vfold_left (VF_mult (n:=n)) (VF_one n) A)).

  Definition simMapInv (s : St)(w : W)(x : X)(t : TE) : R :=
    let '(A, r') := w in
    t - (VF_inProd x (Vfold_left (VF_mult (n:=n)) (VF_one n) A)).

  Definition simMapHelp (s : St)(x : X) : Prop :=
    let '(h,hs,cA,b) := s in
    hs = Vmap (op h) x.

  Definition sigXcomp  (s : St)(x : X) : sig.X := x.
  Definition sig5Xcomp (s : St)(x : X) : sig5.X := x.

  Lemma simMapInvValid :  forall (st : St)(w : W)(x : X)(r : R)(t : TE),
     Rel st w ->
     simMapHelp st x ->
    simMap st w x (simMapInv st w x t) = t /\
    simMapInv st w x (simMap st w x r) = r.
  Proof.
    intros. unfold simMap, simMapInv, simMapHelp in *. destruct st, p, p, w. 
    unfold TE, R in *. split.
    + ring.
    + ring.
  Qed.

  (* This may need more preconditions otherwise it might be too strong *)
  Lemma simMapHelpValid : forall (st : St)(x : X)(c : C),
    simMapHelp st x ->
    sig.simMapHelp  (ToStSig (st,c)) (sigXcomp st x) /\
    sig5.simMapHelp (ToStSig5 (st,c)) (sig5Xcomp st x).
  Proof.
    intros. unfold sig.simMapHelp, sig5.simMapHelp, simMapHelp, ToStSig, ToStSig5,
    sigXcomp, sig5Xcomp, bgHadProd.simMapHelp, bgHadProdBase.simMapHelp in *. 
    destruct st, p, p.  rewrite H. split; trivial.
  Qed.

  Lemma simulatorZK1 : forall s w r x,
     Rel s w ->
     simMapHelp s x ->
     (P0 s r w).2 = (simulator s (simMap s w x r)).
  Proof.
    intros. unfold simulator, simMap, simMapHelp, Rel, P0 in *.
    destruct s, p, p, w. rewrite <- trapdoorEPC. trivial. apply H0.
  Qed.

End ProdArg.


Module ProdArgIns
    (* First all the modules related to Hadamard product *)
    (Message Ciphertext Commitment : GroupSig)(Ring : RingSig)
    (Field : FieldSig)(VS2 : VectorSpaceSig Commitment Field)
    (VS1 : VectorSpaceSig Ciphertext Field)(Chal : GroupFromRing Field)
    (MVS : VectorSpaceModuleSameGroup Ciphertext Ring Field VS1)
    (VS3 : VectorSpaceSig Message Field)(Hack : Nat)(M : Nat)
    (enc : EncryptionSchemePlus Message Ciphertext Ring Field VS1 VS3 MVS)
    (support : BGSupport Message Ciphertext Commitment Ring Field VS2 VS1 MVS VS3
    Hack M enc)(sig2 : BGZeroArg Message Ciphertext Commitment Ring Field VS2 VS1 Chal
    MVS VS3 Hack M enc support)
    (bgHadProdBase : BGHadProd Message Ciphertext Commitment Ring Field VS2 VS1 Chal MVS
    VS3 Hack M enc support sig2)
    (bgHadProd : SigmaPlusTo5simTofull Chal sig2 bgHadProdBase)
    (sig5 : SigmaPlus5Comp Chal sig2 bgHadProd)
    (* Now Single Vector prod  *)
    (sig : BGSingleProd Commitment Field VS2 Chal Hack)
    <: ProdArg Message Ciphertext Commitment Ring Field VS2 VS1 Chal MVS VS3 Hack M enc support sig2 bgHadProdBase bgHadProd sig5 sig.

  Import support.

  (* N = nm *)
  Let n := S (S (S Hack.N)).      (* n *)
  Let m := S (S M.N).             (* m *)
  Import Field.

  Import Mo.
  Import Mo.mat.

  Module EPC := ExtendComScheme Commitment Field VS2 mat.
  Import EPC.
  Import EPC.MoM.
  Import PC.

  Module ALenc := EncryptionSchemeProp Message Ciphertext Ring Field VS1 MVS enc.
  Import ALenc.
  Import HardProb.

  Module ALR := RingAddationalLemmas Ring.

  Import VS2.
  Import Commitment.

  Module G2 := GroupFromFieldIns Field.

  (* ck cA b *)
  Definition St:Type := G*(VG n)*(VG m)*F.

  (* A r *)
  Definition W:Type := (vector (VF n) m)*(VF m).

  Definition Rel (s : St)(w : W) : bool :=
    (* let '(h,hs,cA,b) := s in *)
    let h := s.1.1.1 in
    let hs := s.1.1.2 in
    let cA := s.1.2 in
    let b := s.2 in
    (* let '(A,r) := w in *)
    let A := w.1 in
    let r := w.2 in
    
    (VG_eq cA (comEPC h hs A r)) &&
        (Fbool_eq (VF_prod (Vfold_left (VF_mult (n:=n)) (VF_one n) A)) b).

  Definition C : Type := G.

  Definition R : Type := F.

  Definition P0 (s : St)(rand : R)(w : W) : (St*C) :=
    let '(h,hs,cA,b) := s in
    let '(A,r) := w in
    
    (s, EPC h hs (Vfold_left (VF_mult (n:=n)) (VF_one n) A) rand).

  (* sig.St is  h hs c b *)
  Definition ToStSig  (sc : St*C) : sig.St :=
    let '(h,hs,cA,b,c) := sc in
    (h, hs, c, b).

  (* a r *)
  Definition ToWitSig (sc : St*C)(rand : R)(w : W) : sig.W :=
    let '(h,hs,cA,b,c) := sc in
    let '(A,r) := w in
  
    ((Vfold_left (VF_mult (n:=n)) (VF_one n) A), rand).
    

  Definition ToStSig5 (s : St*C) : sig5.St :=
    let '(h,hs,cA,b,c) := s in
    (h, hs, cA, c).

  Definition ToWitSig5 (sc : St*C)(rand : R)(w : W) : sig5.W :=
    let '(h,hs,cA,b,c) := sc in
    let '(A,r) := w in

    (A,r,(Vfold_left (VF_mult (n:=n)) (VF_one n) A),rand).

  Lemma ToValid : forall s w r,
    Rel s w ->
   sig.Rel (ToStSig (P0 s r w)) (ToWitSig (P0 s r w) r w) /\
   sig5.Rel (ToStSig5 (P0 s r w)) (ToWitSig5 (P0 s r w) r w).
  Proof.
    pose module_abegrp.
    intros. unfold Rel, sig.Rel, sig5.Rel, bgHadProd.Rel, bgHadProdBase.Rel,
    ToStSig, ToStSig5, ToWitSig, ToWitSig5, P0 in *. destruct s, p, p. destruct w.
    apply andb_true_iff in H. destruct H.  apply F_bool_eq_corr in H0.
    apply VGeq in H. split.
    + apply andb_true_iff. split.
    ++ apply bool_eq_corr. rewrite Prod_right_replace. trivial.
    ++ apply F_bool_eq_corr. rewrite Prod_right_replace in H0.
     rewrite <- H0. trivial.
    + apply andb_true_iff. split. apply andb_true_iff. split.
    ++ apply VGeq. do 3 rewrite Prod_right_replace. do 2 rewrite Prod_left_replace.
    apply H.
    ++ apply bool_eq_corr. do 4 rewrite Prod_right_replace.
    rewrite Prod_left_replace. trivial.
    ++ apply VF_beq_true. rewrite Prod_right_replace. rewrite Prod_left_replace.
    trivial.
  Qed.

  Definition TE : Type := F.

  Lemma pres_p0 : forall (s : St)(r : R)(w : W),
      (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. unfold P0. destruct s, w, p, p. trivial.
  Qed.

  Definition extractor (w : sig5.W)(w' : sig.W) :  W :=
    let '(A,r,B,s) := w in
    (A,r).

  Definition argument (s : St)(c: C) : Prop :=
    let '(h,hs,cA,b) := s in
    exists a b c f, a <> b /\ EPC h hs a c = EPC h hs b f.

  Lemma M1_nonzero : sig5.M1 > 0. (* This is an edge case we had to take care of *)
  Proof.
     intros. unfold sig5.M1, sig2.M . lia.
  Qed.

  Lemma special_soundness : forall s c (w : sig.W)(w1 : sig5.W),
    sig.Rel (ToStSig (s,c)) w ->
    sig5.Rel (ToStSig5 (s,c)) w1 ->
    Rel s (extractor w1 w) \/ argument s c.
  Proof.
    pose module_abegrp.
    intros. unfold sig.Rel, sig5.Rel, Rel, extractor, bgHadProd.Rel,
    bgHadProdBase.Rel, ToStSig, ToStSig5 in *. destruct s, w, p, p, w1, p, p.
    apply andb_true_iff in H0. destruct H0. apply andb_true_iff in H0. destruct H0.
    apply VGeq in H0. do 3 rewrite Prod_right_replace in H0.
    do 4 rewrite Prod_left_replace in H0. apply VF_beq_true in H1.
    apply andb_true_iff in H. destruct H. apply bool_eq_corr in H.
    apply F_bool_eq_corr in H3. apply bool_eq_corr in H2.
    rewrite Prod_right_replace in H. do 4 rewrite Prod_right_replace in H2.
    rewrite Prod_right_replace in H1. do 3 rewrite Prod_left_replace in H1.
    rewrite Prod_left_replace in H2. case_eq (VF_beq v v2); intros.
    + left. apply andb_true_iff.  apply VF_beq_true in H4. split.
    ++ apply VGeq. apply H0.
    ++ apply F_bool_eq_corr. unfold bgHadProdBase.n in *. unfold n. symmetry in H1.
    rewrite H1. rewrite H3. rewrite H4. trivial.
    + right. exists v, v2, f0, f1. split. apply VF_beq_false in H4.  trivial.
    unfold sig.n, bgHadProdBase.n, n in *. symmetry in H. unfold sig.EPC.EPC,
    EPC, support.EPC.EPC in *. rewrite H. symmetry in H2. rewrite H2. trivial.
  Qed.

  Definition X : Type := VF n.

  Definition simulator (s : St)(t : TE) : C :=
    let '(h,hs,cA,b) := s in
    EPC h hs (VF_zero n) t.
    
  Definition simMap   (s : St)(w : W)(x : X)(r : R) : TE :=
    let '(A, r') := w in
    r + (VF_inProd x (Vfold_left (VF_mult (n:=n)) (VF_one n) A)).

  Definition simMapInv (s : St)(w : W)(x : X)(t : TE) : R :=
    let '(A, r') := w in
    t - (VF_inProd x (Vfold_left (VF_mult (n:=n)) (VF_one n) A)).

  Definition simMapHelp (s : St)(x : X) : Prop :=
    let '(h,hs,cA,b) := s in
    hs = Vmap (op h) x.

  Definition sigXcomp  (s : St)(x : X) : sig.X := x.
  Definition sig5Xcomp (s : St)(x : X) : sig5.X := x.

  Lemma simMapInvValid :  forall (st : St)(w : W)(x : X)(r : R)(t : TE),
     Rel st w ->
     simMapHelp st x ->
    simMap st w x (simMapInv st w x t) = t /\
    simMapInv st w x (simMap st w x r) = r.
  Proof.
    intros. unfold simMap, simMapInv, simMapHelp in *. destruct st, p, p, w.
    unfold TE, R in *. split.
    + ring.
    + ring.
  Qed.

  (* This may need more preconditions otherwise it might be too strong *)
  Lemma simMapHelpValid : forall (st : St)(x : X)(c : C),
    simMapHelp st x ->
    sig.simMapHelp  (ToStSig (st,c)) (sigXcomp st x) /\
    sig5.simMapHelp (ToStSig5 (st,c)) (sig5Xcomp st x).
  Proof.
    intros. unfold sig.simMapHelp, sig5.simMapHelp, simMapHelp, ToStSig, ToStSig5,
    sigXcomp, sig5Xcomp, bgHadProd.simMapHelp, bgHadProdBase.simMapHelp in *.
    destruct st, p, p.  rewrite H. split; trivial.
  Qed.

  Lemma simulatorZK1 : forall s w r x,
     Rel s w ->
     simMapHelp s x ->
     (P0 s r w).2 = (simulator s (simMap s w x r)).
  Proof.
    intros. unfold simulator, simMap, simMapHelp, Rel, P0 in *.
    destruct s, p, p, w. rewrite <- trapdoorEPC. trivial. apply H0.
  Qed.

End ProdArgIns.

