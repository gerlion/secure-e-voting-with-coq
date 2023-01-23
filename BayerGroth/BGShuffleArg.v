Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
From Groups Require Import groups module vectorspace dualvectorspaces matrices 
  matricesF matricesField modulevectorspace groupfromring genprodvectorspaces.
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
Require Import BGProdArg.
Require Import BGMultiexpArg.
Require Import sigmaprotocolPlus9.
Set Implicit Arguments.

Module ShuffleArg (Message Ciphertext Commitment : GroupSig)(Ring : RingSig)
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
    (sig : BGSingleProd Commitment Field VS2 Chal Hack)
    (prodArg : ProdArg Message Ciphertext Commitment Ring Field VS2 VS1 Chal MVS VS3 Hack M
    enc support sig2 bgHadProdBase bgHadProd sig5 sig)
    (progArg2 : SigmaPlus5to5Comp Chal sig sig5 prodArg)
    (bGMultiArg : BGMultiArg Message Ciphertext Commitment Ring Field VS2 
    VS1 Chal MVS VS3 Hack M enc support)  <: SigmaPlus5plus3to9 Chal bGMultiArg progArg2.

  Import support.

  Module G2 := GroupFromFieldIns Field. 

  Module Chal2 := ProdGroupSigIns G2 Chal.

  Let n := S ( S (S Hack.N)).    (* n *)
  Let m := S (S M.N).            (* m *)
  Import Field.

  Import Mo.
  Import Mo.mat.

  Import EPC.
  Import EPC.MoM.

  Import PC.

  Import ALenc.
  (* Module HardProb := HardProblems Commitment Field VS2. *)
  Import HardProb.

  Module MP := MixablePropIns Message Ciphertext Ring Field VS1 MVS enc.

  Module ALR := RingAddationalLemmas Field.

  Import VS2.
  Import Commitment.

  Definition E0 : Set := Chal.G.
  Definition E1 : Set := Chal2.G.

  Definition add0 : E0 -> E0 -> E0 := Chal.Gdot.                   
  Definition zero0 : E0 := Chal.Gone.      
  Definition inv0 : E0 -> E0 := Chal.Ginv.
  Definition bool_eq0 : E0 -> E0 -> bool := Chal.Gbool_eq.
  Definition disjoint0 : E0 -> E0 -> bool := Chal.Gdisjoint.           

  Definition add1 : E1 -> E1 -> E1 := Chal2.Gdot.                   
  Definition zero1 : E1 := Chal2.Gone.      
  Definition inv1 : E1 -> E1 := Chal2.Ginv.
  Definition bool_eq1 : E1 -> E1 -> bool := Chal2.Gbool_eq.
  Definition disjoint1 : E1 -> E1 -> bool := Chal2.Gdisjoint.

  Definition St:Type := (* pk ck=(h,hs),Cbar,Cbar' *)
  enc.PK*G*(VG n)*(vector Ciphertext.G (n*m))*(vector Ciphertext.G (n*m)).

  (* pi, rho *)
  Definition W:Type := (vector (VF (n*m)) (n*m))*(vector Ring.F (n*m)).

  Definition relReEnc(pk : enc.PK)(e e' : vector Ciphertext.G (n*m))(mat : MF (n*m))
      (r : vector Ring.F (n*m)) : bool :=
      let e'' := MoC.PexpMatrix e mat in
      let r'' := r in 
      bVforall3 (fun e e' r' => bIsReEnc pk e e' r') e''  e' r''.

  Lemma relReEncMat : forall (pk : enc.PK)(e e' : vector Ciphertext.G (n*m))(mat : MF (n*m))
      (r : vector Ring.F (n*m)),
    relReEnc pk e e' mat r = true <-> e' = Vmap2 (reenc pk) (MoC.PexpMatrix e mat) r.
  Proof.
    pose Ciphertext.module_abegrp. 
    intros. unfold relReEnc, bIsReEnc. split; intros.
    + apply Veq_nth. intros. apply (bVforall3_elim_nth ip) in H. 
    apply bool_eq_corr in H. rewrite H. rewrite Vnth_map2. trivial.
    + rewrite H. apply (bVforall3_nth_intro). intros. apply bool_eq_corr.
    rewrite Vnth_map2. trivial.
  Qed.

  Definition Rel (s : St)(w : W) : bool :=   
    let '(pk, h, hs, cBar, cBar') := s in
    let '(mat, rho) := w in
    MFisPermutation mat && relReEnc pk cBar cBar' mat rho.
    
  Definition C0 : Type := VG m.                            
  Definition C1 : Type := VG m.

  Definition R0 : Type := VF m.                            
  Definition R1 : Type := VF m.

  Definition P0 (s : St)(r : R0)(w : W) : (St*C0) :=
    let '(pk, h, hs, cBar, cBar') := s in
    let '(mat, rho) := w in

    (* This aVec starts at zero where the paper says to start at one *)
    let aVec := (MF_CVmult mat (Vbuild (fun i (ip : i < n*m) => VF_sum (Vconst 1 i)))) in
    (s, comEPCvec h hs aVec r).
         
  Definition P1 (s : St*C0*E0)(r : R0*R1)(w : W) : (St*C0*E0*C1) :=
    let '(pk, h, hs, cBar, cBar',c0 ,e0) := s in
    let '(mat, rho) := w in

    let aVec := MF_CVmult mat (Vbuild (fun i (ip : i < n*m) => VF_sum (Vconst 1 i))) in
    let bVec := MF_CVmult mat (Vbuild (fun i (ip : i < n*m) => VF_prod (Vconst e0 i))) in
    (s, comEPCvec h hs bVec r.2).

  Lemma pres_p0 : forall (s : St)(r : R0)(w : W), 
      (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. unfold P0. destruct s, w, p, p, p. simpl. trivial.
  Qed.

  Lemma pres_p1 : forall (s : St*C0*E0)(r : R0*R1)(w : W), 
      (P1 s r w) = (s,(P1 s r w).2).
  Proof.
    intros. unfold P1. destruct s, w, p, s, p, p, p. simpl. trivial.
  Qed.

  (* enc.PK*G*(VG n)*(vector (vector Ciphertext.G n) m)*
        Ciphertext.G*(VG m)*enc.M.  *)
  Definition ToStSig (s : St*C0*E0*C1*E1) : bGMultiArg.St :=
    let '(pk, h, hs, cBar, cBar', c0, e0, c1, e1) := s in

  (pk, h, hs, VecToMat n m cBar', 
    MoC.VG_prod (MoC.VG_Pexp cBar (VandermondeCol (n*m) e0)),
     c1, Message.Ggen).

  (* (vector (VF n) m)*(VF m)*Ring.F *)
  Definition ToWitSig (s : St*C0*E0*C1*E1)(r : R0*R1)(w : W) : bGMultiArg.W :=
    let '(pk, h, hs, cBar, cBar', c0, e0, c1, e1) := s in
    (* let '(mat, rho) := w in *)
    let mat := w.1 in
    let rho := w.2 in
  
    let aVec := MF_CVmult mat (Vbuild (fun i (ip : i < n*m) => VF_sum (Vconst 1 i))) in
    let bVec := MF_CVmult mat (Vbuild (fun i (ip : i < n*m) => VF_prod (Vconst e0 i))) in

    (VecToMat n m bVec, r.2, MoR.VF_sum (MoR.VF_neg (Vmap2 MVS.op3 rho bVec))).

  (*  G*(VG n)*(VG m)*F *)
  Definition ToStSig5 (s : St*C0*E0*C1*E1) : progArg2.St :=
    let '(pk, h, hs, cBar, cBar', c0, x, c1, e2) := s in
    let y := e2.1 in
    let z := e2.2 in
    
    (h, hs, VG_mult (VG_mult (VG_Sexp c0 (sval y)) c1)
       (VG_inv (comEPC h hs (Vconst (Vconst z n) m) (VF_zero m))),
   VF_prod (Vbuild (fun i (ip : i < n*m) => (sval y)*(VF_sum (Vconst 1 i))+
    (VF_prod (Vconst x i))-z))).
    
  (* (vector (VF n) m)*(VF m) *)
  Definition ToWitSig5 (s : St*C0*E0*C1*E1)(r : R0*R1)(w : W) : progArg2.W :=
    let '(pk, h, hs, cBar, cBar', c0, x, c1, (y,z)) := s in
    (* let '(mat, rho) := w in *)
    let mat := w.1 in
    let rho := w.2 in

    let aVec := MF_CVmult mat (Vbuild (fun i (ip : i < n*m) => VF_sum (Vconst 1 i))) in
    let bVec := MF_CVmult mat (Vbuild (fun i (ip : i < n*m) => VF_prod (Vconst x i))) in
  
    let dVec := VF_sub (VF_add (VF_scale aVec (sval y)) bVec) (Vconst z (n*m))  in

    (VecToMat n m dVec, VF_add (VF_scale r.1 (sval y)) r.2).

  Lemma ToValid : forall s w r e e1,
    Rel s w ->
   bGMultiArg.Rel (ToStSig (P1 (P0 s r.1 w, e) r w,e1))
           (ToWitSig (P1 (P0 s r.1 w, e) r w, e1) r w) /\
   progArg2.Rel (ToStSig5 (P1 (P0 s r.1 w, e) r w,e1))
           (ToWitSig5 (P1 (P0 s r.1 w, e) r w, e1) r w).
  Proof.
    pose Ciphertext.module_abegrp. pose Message.module_abegrp.
    intros. unfold bGMultiArg.Rel, progArg2.Rel, ToStSig, ToWitSig, ToStSig5, 
    ToWitSig5, P1, P0, prodArg.Rel. destruct s, w, p, p, p, e1.
    unfold Rel in H. apply andb_true_iff in H. destruct H. split.
    (* sig relation *)
    + apply andb_true_iff. split.
    (* first part of sig relation *)
    ++ apply VGeq. unfold comEPCvec. apply f_equal2. trivial. trivial.
    (* second part of sig relation *) 
    ++ apply bool_eq_corr. apply relReEncMat in H0. 
    assert (Vfold_left enc.Mop enc.Mzero (Vconst enc.Mzero (n*m)) = enc.Mzero). 
    apply Vfold_left_Vconst_acc. intros. 
    apply one_left. rewrite <- H1. rewrite MP.comHomomorphism. 
    pose MoC.VG_Prod_mult_dist. unfold MoC.VG_prod in *.
    rewrite EncZeroZeroIsOne. symmetry in e0. pose MoC.VG_prod_pexp_VecToMat.
    unfold MoC.VG_prod in *. rewrite e1. rewrite MoC.Vfold_Gdot_dob.
    pose (MoC.PexpMatrix_Prod (MoC.VG_Pexp t2 (VandermondeCol (n * m) e)) t0 H).
    unfold MoC.VG_prod in *. rewrite <- e2. apply f_equal. 
    apply Veq_nth. intros. do 3 rewrite Vnth_map2. rewrite H0. do 2 rewrite Vnth_map. 
    do 2 rewrite Vnth_map2. unfold reenc. rewrite VS1.mod_dist_Gdot. 
    rewrite enc.encOfOnePrec. rewrite dot_assoc. rewrite enc.homomorphism. 
    do 2 rewrite Vnth_map. destruct Ring.module_ring. rewrite Ropp_def. rewrite Vnth_const. 
    rewrite one_right. rewrite EncZeroZeroIsOne. rewrite one_left.
    (* The randomness has now been removed *)
    rewrite MoC.VG_Pexp_Pexp. rewrite MoC.Sexp_dist. apply f_equal. apply f_equal.
    rewrite FMatrix.mat_build_nth. rewrite FMatrix.get_col_col_mat.
    unfold MFisPermutation in H. clear e2. apply andb_true_iff in H. 
    destruct H. apply (bVforall_elim_nth ip) in H. apply bVexists_eq in H.
    elim H. intros. elim H3. intros. apply VF_beq_true in H4. rewrite Vbuild_nth in H4.
    unfold FMatrix.get_row. rewrite H4. rewrite FMatrix.VA.dot_product_id.
    rewrite Vbuild_nth. apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_map.
    unfold FMatrix.VA.id_vec. destruct (Nat.eq_dec x i0). subst. rewrite Vnth_replace. 
    rewrite Vbuild_nth. destruct Field.module_ring. apply Rmul_comm0.
    rewrite Vnth_replace_neq; auto. rewrite Vnth_const. unfold FSemiRingT.A0. field; auto.
    (* Sig5 relation *)
    + apply andb_true_iff. split.
    (* first part of sig5 relation *)
    ++ apply VGeq. rewrite comEPCDis2. unfold VG_mult. apply Veq_nth. intros.
    do 5 rewrite Vnth_map2. do 3 rewrite Vnth_map. rewrite Vnth_map2. 
    rewrite <- EPC_add. rewrite EPCneg. rewrite <- EPC_add. apply f_equal2.
    +++ apply Veq_nth. intros. do 2 rewrite Vnth_map2. do 3 rewrite Vbuild_nth.
    rewrite Vnth_map. do 3 rewrite Vnth_sub. do 2 rewrite Vnth_map2.
    rewrite Vnth_const. apply f_equal2. apply f_equal2. 
    ++++ symmetry. rewrite Vnth_map. trivial.
    ++++ trivial. 
    ++++ do 2 rewrite Vnth_map. do 2 rewrite Vnth_const. trivial.
    +++ rewrite Vnth_map2. rewrite Vnth_map. rewrite Vnth_const. unfold FSemiRingT.Aplus.
    unfold Chal.G, R0, R1 in *. pose Field.vs_field. destruct f. destruct F_R. rewrite <- Radd_assoc.
    apply f_equal2; auto. apply ALVS1.FsubZero. 
    (* Second part of sig5 relation *)
    ++ apply F_bool_eq_corr. unfold VF_prod. rewrite Vfold_left_map2_VecToMat; intros.
    symmetry. pose (permutationInnerProd_sub t0 (Vbuild
     (fun i : nat => fun=> (sval g0) * VF_sum (Vconst 1 i) + 
    Vfold_left Fmul 1 (Vconst e i) - g1)) H).
    unfold VF_prod in e0. do 2 rewrite Prod_right_replace. 
    rewrite Prod_left_replace. rewrite <- e0. apply f_equal. apply Veq_nth. intros.
    do 2 rewrite Vnth_map2. do 2 rewrite MF_getRow_prod.
    unfold FSemiRingT.Aplus. rewrite Vnth_map. unfold MFisPermutation in H.
    clear e0. apply andb_true_iff in H. destruct H. apply (bVforall_elim_nth ip) in H. 
    apply bVexists_eq in H. elim H. intros. elim H2. intros. apply VF_beq_true in H3.
    rewrite Vbuild_nth in H3. unfold VF_inProd. rewrite Vnth_map. 
    rewrite FMatrix.mat_build_nth. rewrite FMatrix.get_col_col_mat.
    unfold FMatrix.get_row. rewrite H3. do 3 rewrite FMatrix.VA.dot_product_id.
    do 3 rewrite Vbuild_nth. rewrite Vnth_map. rewrite Vnth_const. field; auto.
    field; auto. field; auto. field; auto. 
  Qed.

  Definition TE0 : Type := VF m.                           
  Definition TE1 : Type := VF m. 

  Definition X  : Type := VF n*vector (VF n) m*vector (vector Ring.F n) m.
  Definition simMapHelp (s : St)(x : X) : Prop :=
    let '(pk, h, hs, cBar, cBar') := s in
    hs = Vmap (op h) x.1.1 /\
    VecToMat n m cBar' = Vmap2 (fun y z => Vmap2 (fun w v => enc.enc pk (VS3.op Message.Ggen w) v) y z) x.1.2 x.2 .
    
  Definition sigXcomp (s : St)(x : X) : bGMultiArg.X := x.
  Definition sig5Xcomp (s : St)(x : X) : progArg2.X := x.1.1.

  Definition simulator (s : St)(t : TE0*TE1)(e : E0*E1) : (C0*C1) :=
    let '(pk, h, hs, cBar, cBar') := s in
    (comEPC h hs (Vconst (VF_zero n) m) t.1, comEPC h hs (Vconst (VF_zero n) m) t.2).

  Definition simMap (s : St)(w : W)(e: E0*E1)(x : X)(r : R0*R1) : (TE0*TE1) :=
      let '(pk, h, hs, cBar, cBar') := s in
      let '(mat, rho) := w in
      let aVec := MF_CVmult mat (Vbuild (fun i (ip : i < n*m) => VF_sum (Vconst 1 i))) in
      let bVec := MF_CVmult mat (Vbuild (fun i (ip : i < n*m) => VF_prod (Vconst e.1 i))) in

      (VF_add r.1 (Vmap (fun a=> VF_inProd x.1.1 a) (VecToMat n m aVec)),
      VF_add r.2 (Vmap (fun a=> VF_inProd x.1.1 a) (VecToMat n m bVec))).

  Definition simMapInv (s : St)(w : W)(e : E0*E1)(x : X)(t : TE0*TE1) : (R0*R1) :=
      let '(pk, h, hs, cBar, cBar') := s in
      let '(mat, rho) := w in
      let aVec := MF_CVmult mat (Vbuild (fun i (ip : i < n*m) => VF_sum (Vconst 1 i))) in
      let bVec := MF_CVmult mat (Vbuild (fun i (ip : i < n*m) => VF_prod (Vconst e.1 i))) in

      (VF_sub t.1 (Vmap (fun a=> VF_inProd x.1.1 a) (VecToMat n m aVec)),
      VF_sub t.2 (Vmap (fun a=> VF_inProd x.1.1 a) (VecToMat n m bVec))).

 
  Lemma simMapInvValid :  forall (st : St)(w : W)(e : E0*E1)(x : X)
          (r : R0*R1)(t : TE0*TE1),
     Rel st w ->
     simMapHelp st x ->
    simMap st w e x (simMapInv st w e x t) = t /\
    simMapInv st w e x (simMap st w e x r) = r. 
  Proof.
    intros. unfold simMap, simMapInv. destruct st, p, p, w, p. split.
    + rewrite Prod_left_replace. rewrite Prod_right_replace. apply injective_projections.
    ++ rewrite Prod_left_replace. rewrite VF_sub_corr. rewrite VF_add_neg2. trivial.
    ++ rewrite Prod_right_replace. rewrite VF_sub_corr. rewrite VF_add_neg2. trivial.
    + rewrite Prod_left_replace. rewrite Prod_right_replace. apply injective_projections.
    ++ rewrite Prod_left_replace. rewrite VF_sub_corr. rewrite VF_add_neg. trivial.
    ++ rewrite Prod_right_replace. rewrite VF_sub_corr. rewrite VF_add_neg. trivial.
  Qed.

  (* This may need more preconditions otherwise it might be too strong *)
  Lemma simMapHelpValid : forall (st : St)(x : X)(c : C0*C1)(e : E0*E1),
    simMapHelp st x ->
    bGMultiArg.simMapHelp  (ToStSig (st,c.1,e.1,c.2,e.2)) (sigXcomp st x) /\
    progArg2.simMapHelp (ToStSig5 (st,c.1,e.1,c.2,e.2)) (sig5Xcomp st x).
  Proof.
    intros. unfold simMapHelp in H. destruct st, p, p, p.  destruct H. split.
    + unfold simMapHelp, bGMultiArg.simMapHelp, ToStSig, sigXcomp. 
    split. apply H. apply H0.
    + unfold progArg2.simMapHelp, ToStSig5, sig5Xcomp, prodArg.simMapHelp. 
    destruct e.2. apply H.
  Qed.

  Lemma simulatorZK1 : forall s w r x e,
     Rel s w ->
     simMapHelp s x ->
     (P0 s r.1 w).2 = (simulator s (simMap s w e x r) e).1.
  Proof.
    intros. unfold P0, simulator, simMap. destruct s, w, p, p, p. rewrite Prod_right_replace.
    rewrite Prod_left_replace. apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    unfold simMapHelp in *. destruct H0.
    rewrite (trapdoorEPC g x.1.1 H0). rewrite Vnth_const. rewrite Vnth_map2.
    rewrite Vnth_map. unfold FSemiRingT.Aplus. trivial.
  Qed.

  Lemma simulatorZK2 : forall s w r x e,
     Rel s w ->
     simMapHelp s x ->
     (P1 (P0 s r.1 w,e.1) r w).2 = (simulator s (simMap s w e x r) e).2.
  Proof.
    intros. unfold P0, P1, simulator, simMap. destruct s, w, p, p, p.
    do 3 rewrite Prod_right_replace.  apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    unfold simMapHelp in *. destruct H0. rewrite (trapdoorEPC g x.1.1 H0).
    rewrite Vnth_const. rewrite Vnth_map2.
    rewrite Vnth_map. unfold FSemiRingT.Aplus. trivial.
  Qed.

  Lemma e_abgrp0 : AbeGroup E0 add0 zero0 bool_eq0 disjoint0 inv0.
  Proof.
    apply Chal.module_abegrp.
  Qed.

  Lemma e_abgrp1 : AbeGroup E1 add1 zero1 bool_eq1 disjoint1 inv1.
  Proof.
    apply Chal2.module_abegrp.
  Qed.

  Definition M0 :nat := n*m.
  Definition M1 :nat := 1.

  Lemma M3_nonzero : sig5.M1 > 0.
  Proof.
    intros. unfold sig5.M1, sig2.M. lia.
  Qed.

  (* prodArg (vector (VF n) m)*(VF m), bGMultiArg (vector (VF n) m)*(VF m)*Ring.F *)
  (* (vector (VF (n*m)) (n*m))*(vector Ring.F (n*m)) *)
  Definition extractor (w : vector (vector (progArg2.W*bGMultiArg.W) M1) M0)
     (e : vector (E0*vector E1 M1) M0) : W := 
  let mat := matRecover (MatToVec (Vbuild (fun (i : nat) (ip : i < m) =>
       VF_scale (VF_add (VF_add (Vnth (Vhead (Vhead w)).1.1 ip)
                          (Vconst (Vhead (Vhead e).2).2 n))
                       (VF_neg (Vnth (Vhead (Vhead w)).2.1.1 ip)))
                    (FmulInv (sval (Vhead (Vhead e).2).1))))) in
  (mat, Vmap (fun a=> MoR.VF_sum (Vmap2 MVS.op3 
    (Vmap (fun a => Ring.Finv (Vhead a).2.2) w) a))
        (MF_mult mat (VandermondeInv (UnzipLeft e)))).
    
  Definition argument (s : St)(c : C0*vector C1 M0)(e : vector (E0*vector E1 M1) M0) : Prop :=
    let '(pk, h, hs, cBar, cBar') := s in    
    (* If there exists a and b such that they were precommited to *)
    exists aM aR bM bR,
    c.2 = Vmap2 (fun a => [eta comEPC h hs a]) bM bR /\
    Vconst c.1 (n*m) = Vmap2 (fun a => [eta comEPC h hs a]) aM aR  /\
    (* and prod ya + b - z = yi + xi - z *)
    Vforall3 (fun e b a => VF_prod (Vmap2 (fun a b => VF_prod (VF_sub (VF_add 
    (VF_scale a (sval (Vhead e.2).1)) b) (Vconst (Vhead e.2).2 n))) a b) =
    VF_prod (Vbuild (fun i (ip : i < n * m) => 
    sval (Vhead e.2).1 * VF_sum (Vconst 1 i) +
    (VF_prod (Vconst e.1 i)) - (Vhead e.2).2))) e bM aM /\
    (* then given some permutation (pi) we computed off a *)
    let mat := matRecover (MatToVec (Vhead aM)) in
    (* a_i = pi(i) and b_i = x^pi(i) *)
    ((MFisPermutation mat && VF_beq (MatToVec (Vhead aM)) 
      (MF_CVmult mat (Vbuild (fun i (ip : i < n*m) => VF_sum (Vconst 1 i)))) &&
    bVforall2 (fun (b : vector (VF n) m) e => VF_beq (MatToVec b) (MF_CVmult mat (Vbuild (fun i (ip : i < n*m) => 
    VF_prod (Vconst e.1 i))))) bM e)
     = false).

    (* A proof is being really weird so I added this silly lemma *)
  Lemma MFisPermutationDec : forall n (mat : MF n),
    MFisPermutation mat = true \/ MFisPermutation mat = false.
  Proof.
    intros. case_eq (MFisPermutation mat); intros; auto.
  Qed. 

 
  Lemma special_soundness : forall s c0 (e : vector (E0*vector E1 M1) M0)
        (c1 : vector C1 M0)(w : vector (vector (progArg2.W*bGMultiArg.W) M1) M0),
    bVforall3 (fun e c1 w =>
      bVforall2 (fun e2 d =>
          progArg2.Rel (ToStSig5 (s,c0,e.1,c1,e2)) d.1 &&
          bGMultiArg.Rel (ToStSig (s,c0,e.1,c1,e2)) d.2 
      ) e.2 w
    ) e c1 w ->

    PairwisePredicate (fun a b => disjoint0 a b) (UnzipLeft e)  ->
    bVforall (fun a => PairwisePredicate disjoint1 a) (UnzipRight e) ->
    Rel s (extractor w e) \/ argument s (c0,c1) e.
  Proof.
    pose Ciphertext.module_abegrp. pose Commitment.module_abegrp.
    intros. destruct s, p, p, p. 
    (* Start by getting the commitments ready *)
    unfold progArg2.Rel, bGMultiArg.Rel, Rel, prodArg.Rel, extractor in *.
    unfold ToStSig,  ToStSig5 in *.
    (* cB *)
    assert (c1 = Vmap2 (fun a b => comEPC g v a b) (Vmap (fun a => (Vhead a).2.1.1) w)
    (Vmap (fun a => (Vhead a).2.1.2) w)) as cB.
    apply Veq_nth. intros. apply (bVforall3_elim_nth ip) in H.
    apply bVforall2_elim_head in H. apply andb_true_iff in H. destruct H.
    apply andb_true_iff in H2. destruct H2. apply VGeq in H2. rewrite H2.
    rewrite Vnth_map2. do 2 rewrite Vnth_map. trivial.
    (* cA *)
    assert (Vconst c0 (n*m) = Vmap2 (fun a b => comEPC g v a b)
    (Vmap2 (fun w e => (Vbuild (fun i (ip : i < m) => (VF_scale 
    (VF_add (VF_add (Vnth (Vhead w).1.1 ip) (Vconst (Vhead e.2).2 n))
     (VF_neg (Vnth (Vhead w).2.1.1 ip))) (FmulInv (sval (Vhead e.2).1)))))) w e)
     (Vmap2 (fun w e => (VF_scale (VF_sub (Vhead w).1.2 (Vhead w).2.1.2) 
    (FmulInv (sval (Vhead e.2).1)))) w e)) as cA. apply Veq_nth. intros.
    apply (bVforall3_elim_nth ip) in H. apply bVforall2_elim_head in H.
    apply andb_true_iff in H. destruct H. do 3 rewrite Prod_right_replace in H.
    rewrite Prod_left_replace in H. apply andb_true_iff in H. destruct H.
    apply VGeq in H. rewrite cB in H. apply VG_shift in H.
    apply (VG_shift (VG_Sexp c0 (sval (Vhead (Vnth e ip).2).1))) in H.
    apply (VG_Sexp_eq (FmulInv (sval (Vhead (Vnth e ip).2).1))) in H.
    rewrite VG_Sexp_Sexp in H. rewrite VG_Sexp_id_gen in H. rewrite H.
    apply Veq_nth. intros. rewrite Vnth_const. rewrite Vnth_map. 
    do 2 rewrite Vnth_map2. do 3 rewrite Vnth_map. do 2 rewrite Vnth_map2. 
    do 2 rewrite EPCneg. rewrite EPCMult. rewrite Vnth_map2. 
    do 2 rewrite Vnth_map. rewrite VF_neg_neg. do 5 rewrite Vnth_map2. 
    rewrite Vbuild_nth. rewrite EPCneg. rewrite EPCMult.
    rewrite <- EPCExp. apply f_equal2. apply f_equal2; auto. apply f_equal2; auto.
    rewrite Vnth_const. trivial. rewrite Vnth_map. apply f_equal2; auto.
    rewrite Vnth_const. rewrite Vnth_map2. unfold FSemiRingT.Aplus.
    rewrite ALR.Finv_inv. destruct Field.module_ring. rewrite <- (Radd_comm 0). 
    rewrite Radd_0_l. trivial. rewrite Vnth_map. trivial.
     field; auto.   apply (proj2_sig (Vhead (Vnth e ip).2).1). 
    (* Lets remember the witness *)
    remember (Vmap2 (fun w e => Vbuild (fun (i : nat) (ip : i < m) =>
      VF_scale (VF_add (VF_add (Vnth (Vhead w).1.1 ip) (Vconst (Vhead e.2).2 n))
        (VF_neg (Vnth (Vhead w).2.1.1 ip))) (FmulInv (sval (Vhead e.2).1)))) w e)
     as vecA.
    remember (Vmap (fun a => (Vhead a).2.1.1) w) as vecB.
    (* I need to case on a bunch of things here *)
    destruct (bool_dec (MFisPermutation (matRecover (MatToVec (Vhead vecA))) &&
    VF_beq (MatToVec (Vhead vecA))
  (MF_CVmult (matRecover (MatToVec (Vhead vecA)))
     (Vbuild (fun i : nat => fun=> VF_sum (Vconst 1 i))))  &&
   bVforall2 (fun (b : vector (VF n) m) (e1 : F * vector E1 M1) =>
   VF_beq (MatToVec b)
     (MF_CVmult (matRecover (MatToVec (Vhead vecA)))
        (Vbuild (fun i : nat => fun=> VF_prod (Vconst e1.1 i))))) vecB e) true).
    (* Starting main relation *)
    + left. apply andb_true_iff. split. 
    (* It's a permutation matrix *)
    ++ apply andb_true_iff in e0. destruct e0. rewrite HeqvecA in H2.
    rewrite Vhead_map2 in H2. apply andb_true_iff in H2. destruct H2. trivial.
    (* Which we used to mix *)
    ++ assert (t0 = MoC.PexpMatrix (Vmap2 (fun a0 e =>
      Ciphertext.Gdot (enc.enc p enc.Mzero (Vhead a0).2.2)
        (MoC.VG_prod (Vmap2 (fun (x : MoC.VG bGMultiArg.n) (y : VF bGMultiArg.n) =>
               MoC.VG_prod (MoC.VG_Pexp x y)) (VecToMat n m t) 
              (VecToMat n m (MF_CVmult (matRecover (MatToVec (Vhead vecA)))
       (Vbuild (fun i0 : nat => fun=> VF_prod (Vconst e.1 i0)))))))) w e) (VandermondeInv (UnzipLeft e))). 
    rewrite <- (MoC.PexpMatrixId t0). unfold M0 in *. rewrite <- (invVandermondeLeft H0).
    rewrite <- MoC.PexpMatrix_MF_mult_base.
    assert (MoC.PexpMatrix t0 (Vandermonde (UnzipLeft e)) = 
    Vmap2 (fun a e => Ciphertext.Gdot (enc.enc p enc.Mzero (Vhead a).2.2)
       (MoC.VG_prod (Vmap2 (fun x y =>
       MoC.VG_prod (MoC.VG_Pexp x y)) (VecToMat n m t) (VecToMat n m
       (MF_CVmult (matRecover (MatToVec (Vhead vecA))) (Vbuild
         (fun i0 : nat => fun=> VF_prod (Vconst e.1 i0)))))))) w e). apply Veq_nth. intros.
    rewrite Vnth_map. apply (bVforall3_elim_nth ip) in H.
    apply bVforall2_elim_head in H. apply andb_true_iff in H. destruct H. 
    apply andb_true_iff in H2. destruct H2. apply bool_eq_corr in H3.
    clear H. apply andb_true_iff in e0. destruct e0. clear H. rewrite HeqvecB in H4.
    clear cA. clear HeqvecA. clear cB. clear HeqvecB. apply (bVforall2_elim_nth ip) in H4.
    apply VF_beq_true in H4. rewrite Vnth_map in H4. apply VecToMat_eq in H4. 
    rewrite H4 in H3. (* That is the first big equation on page 4 *)
    rewrite Vnth_map2. do 2 rewrite Vnth_map. apply H3. rewrite H2. trivial.
    (* We now have a nice summary of what the underlying relationship means *)
    rewrite H2. apply relReEncMat. (* First I went to get rid of VectorToMat *)
    assert (Vmap2 (fun a1 e2 => Ciphertext.Gdot (enc.enc p enc.Mzero (Vhead a1).2.2)
    (MoC.VG_prod (Vmap2 (fun x y => MoC.VG_prod (MoC.VG_Pexp x y))(VecToMat n m t)
    (VecToMat n m (MF_CVmult (matRecover (MatToVec (Vhead vecA))) (Vbuild (fun i0 : nat =>
       fun=> VF_prod (Vconst e2.1 i0))) ))))) w e = 
    MoC.VG_mult (Vmap (fun a =>  (enc.enc p enc.Mzero a)) (
      Vmap (fun a => (Vhead a).2.2) w))
    (MoC.PexpMatrix t (MF_mult (Vandermonde (UnzipLeft e)) (MF_trans 
    (matRecover (MatToVec (Vhead vecA))))))).
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. unfold MoC.VG_prod. 
    rewrite Vfold_left_nest_VecToMat; intros.
    do 3 rewrite Vnth_map. rewrite MF_getRow_VCmul. 
    rewrite MF_CVmult_MF_VCmult_perm. do 2 rewrite Vnth_map. trivial.
     rewrite dot_assoc. trivial. 
   apply comm. apply a. rewrite H3. 
   (*That's a bit cleaner at least *)
   do 2 rewrite MoC.PexpMatrix_mult. do 3 rewrite MoC.PexpMatrix_MF_mult_base. 
   rewrite MF_assoc. rewrite <- (MF_assoc (VandermondeInv (UnzipLeft e))).
   rewrite invVandermondeLeft. rewrite <- Id_comm. rewrite MF_one. rewrite HeqvecA. 
   apply andb_true_iff in e0. destruct e0. apply andb_true_iff in H4. destruct H4.
   rewrite HeqvecA in H4. rewrite Vhead_map2 in H4. rewrite permTranInv. trivial.
   rewrite MoC.PexpMatrixId. (* Just need to do the randomness now *) unfold reenc.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map.
   assert (forall a b c, b = Ciphertext.Ginv c ->  a = Ciphertext.Gdot b
    (Ciphertext.Gdot c a)). intros. rewrite dot_assoc. rewrite H7. rewrite <- inv_left. 
   rewrite one_left. trivial. apply H7. unfold MoC.VG_Pexp, MoC.VG_prod. 
   rewrite ALenc.encOfOnePrec_map. rewrite ALenc.foldZero. rewrite <- EncInv.
   apply f_equal. rewrite MoR.VF_neg_sum. apply f_equal. apply Veq_nth. intros.
   rewrite Vnth_map. do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map. rewrite MVS.RopInvDis.
    trivial.  trivial. trivial.

    (* The argument case *)
    + right. unfold argument. exists vecA. exists (Vmap2 (fun w e=>
    VF_scale (VF_sub (Vhead w).1.2 (Vhead w).2.1.2) (FmulInv (sval (Vhead e.2).1)))
          w e). exists vecB. exists (Vmap (fun a => 
    (Vhead a).2.1.2) w). split. rewrite Prod_right_replace. apply cB.
    rewrite Prod_left_replace. split. apply cA. apply not_true_is_false in n0.
    split. apply Vforall3_nth_intro. 
    intros. apply (bVforall3_elim_nth ip) in H.
    apply (bVforall2_elim_head) in H. apply andb_true_iff in H. destruct H.
    apply andb_true_iff in H. destruct H. apply F_bool_eq_corr in H3.
    rewrite Prod_right_replace in H3. assert (VF_prod (Vmap2 (fun a1 b =>
    VF_prod (VF_sub (VF_add (VF_scale a1 (sval (Vhead (Vnth e ip).2).1)) b)
           (Vconst (Vhead (Vnth e ip).2).2 n))) (Vnth vecA ip) 
     (Vnth vecB ip)) = VF_prod (Vfold_left (VF_mult (n:=prodArg.n)) 
    (VF_one prodArg.n) (Vhead (Vnth w ip)).1.1)). rewrite HeqvecB. rewrite HeqvecA.
    (* We have done the commits now we need the equality *)
    rewrite VF_prod_prod. apply f_equal. rewrite Vnth_map2. rewrite Vnth_map.
    apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vbuild_nth.
    rewrite Vnth_map. apply f_equal. rewrite VF_scale_scale.
    destruct Field.vs_field. rewrite VF_scale_1_gen. rewrite VF_add_neg2.
    rewrite VF_sub_corr. rewrite VF_add_neg. trivial.  apply Finv_l.
    apply (proj2_sig  (Vhead (Vnth e ip).2).1). rewrite H4. rewrite H3.
    trivial. apply n0.
  Qed.


  
End ShuffleArg.
