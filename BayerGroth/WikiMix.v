 Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
From Groups Require Import groups module vectorspace dualvectorspaces matrices 
  matricesF modulevectorspace groupfromring matricesField.
Require Import sigmaprotocolPlus.
Require Import sigmaprotocolPlus5.
Require Import basicSigmasPlus.
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
Require Import WikiSigma.
Require Import VectorUtil.
Set Implicit Arguments.

Module WikstromMixnet (G G1 G2 : GroupSig)(Ring : RingSig)(Field : FieldSig)
    (VS2 : VectorSpaceSig G2 Field)
    (VS1 : VectorSpaceSig G1 Field)
    (MVS : VectorSpaceModuleSameGroup G1 Ring Field VS1)
    (enc : EncryptionScheme G G1 Ring Field VS1 MVS)(Hack : Nat).

  Module Chal := GroupFromRingIns Field.

  Module dLogSig := DLogSig G2 Field VS2 Chal.

  Module WS := wikSigma G G1 G2 Ring Field Chal VS2 VS1 MVS enc Hack.
  
  Module WikstromSigmaUnderlying := genAndSigmaProtocol Chal dLogSig dLogSig.
  Module WikstromSigma := genAndSigmaProtocol Chal WikstromSigmaUnderlying WS.

  Import Hack.
  Import Field.

  Module Mo := MatricesFieldIns Field.
  Import Mo.
  Import Mo.mat.
  Module MoC := MatricesG G1 Field VS1 Mo.mat.

  Module MoR := MatricesFIns Ring.

    (* Make commitment scheme and matrix *)
  Module EPC := ExtendComScheme G2 Field VS2 Mo.mat.
  Import EPC.
  Import MoM.
  Module PC := BasicComScheme G2 Field VS2 Mo.mat.
  Import PC.
    

  Definition randomnessVector : nat -> Set := vector Ring.F.

  (* Addational vector lemma *)
  Module ALVS1 := VectorSpaceAddationalLemmas G1 Field VS1.
  Module ALVS2 := VectorSpaceAddationalLemmas G2 Field VS2.

  Module ALenc := EncryptionSchemeProp G G1 Ring Field VS1 MVS enc.
  Import ALenc.
  Module HardProb := HardProblems G2 Field VS2.
  Import HardProb.

  Module ALR := RingAddationalLemmas Ring.

  Import VS2.
  Import G2.

  Module ToWikstromMatrix : SigmaPlusTo5 Chal WikstromSigma.
    
    Definition E := Chal.G.
    Definition St : Type := enc.PK*G*(VG (1+N))*
      (vector G1.G (1+N)*vector G1.G (1+N)).
    Definition W : Type := randomnessVector (1+N)*MF (1+N).

    Definition RF_inProd (N : nat)(a : VF N)(b : randomnessVector N) : Ring.F :=
      Vfold_left Ring.Fadd Ring.Fzero (Vmap2 MVS.op3 b a).

    Definition RF_CVmult (N : nat)(M : MF N)(v : randomnessVector N) : randomnessVector N :=
      Vmap (fun a => RF_inProd a v) M.

    (* Defination of shuffling *) (* e2_i = e1_p_i * r_p_i *)
    Definition relReEnc(pk : enc.PK)(e e' : vector G1.G (1+N))(m : MF (1+N))
      (r : randomnessVector (1+N)) : bool :=
      let e'' := MoC.PexpMatrix e' (MF_trans m) in
      let r'' := r in 
      bVforall3 (fun e e' r' => bIsReEnc pk e e' r') e  e'' r''.

    Lemma relReEnc_equiv : forall (pk : enc.PK)(e e' : vector G1.G (1+N))
      (m : MF (1+N))(r : randomnessVector (1+N)),
    relReEnc pk e e' m r = true <->
    (MoC.PexpMatrix e' (MF_trans m)) = Vmap2 G1.Gdot (Vmap (enc.enc pk enc.Mzero) r) e.
    Proof.
      pose G1.module_abegrp. intros. split; intros. 
      + unfold relReEnc in H. apply Veq_nth. intros. apply (bVforall3_elim_nth ip) in H.
      unfold bIsReEnc in H. apply bool_eq_corr in H. unfold reenc in H. rewrite Vnth_map2.
      rewrite Vnth_map. trivial.
      + apply bVforall3_nth_intro. intros. unfold bIsReEnc. apply bool_eq_corr.
      rewrite H. rewrite Vnth_map2. unfold reenc. rewrite Vnth_map. trivial.
    Qed.
     
    Definition Rel (s : St)(w : W) := 
      let pk := s.1.1.1 in
      let g :=  s.1.1.2 in
      let hs := s.1.2 in
      let e := s.2.1 in
      let e' := s.2.2 in

      let r  := w.1 in 
      let m := w.2 in

      relReEnc pk e e' m r && MFisPermutation m. 
    
    Definition C : Type := VG (1+N).

    Definition R : Type := VF (1+N).

    Definition add : E -> E -> E := Chal.Gdot.               
    Definition zero : E := Chal.Gone.     
    Definition inv : E -> E := Chal.Ginv.
    Definition bool_eq := Chal.Gbool_eq.
    Definition disjoint := Chal.Gdisjoint.  

    Definition P0 (s : St)(r : R)(w : W) : (St*C) :=   
      let pk := s.1.1.1 in
      let g :=  s.1.1.2 in
      let hs := s.1.2 in
      let e := s.2.1 in
      let e' := s.2.2 in

      let m := w.2 in
    
      (s, com  g hs (MF_trans m) r). 
  
    Definition C1 : Type := VG (1+N).                             
    Definition R1 : Type := VF (1+N).

    Lemma trans : forall j n n',
      j < S n -> n < n' -> j < n'.
    Proof.
      intros. lia.
    Qed.

    Lemma transSimpl : forall n (a : VG (S n)) j (jp: j < S n), 
      Vnth a (trans jp (Nat.lt_succ_diag_r n)) = Vnth a jp.
    Proof.
      intros. apply Vnth_eq. trivial.
    Qed.
    
    Lemma u'Sub : forall j n n',
      j <= n -> n <= n' -> j+(n-j) <= n'.
    Proof.
      intros. lia.
    Qed.

    Fixpoint computeRhat n : VF (S n) -> VF n -> F :=
      match n with 
        | 0 => fun r => fun u => Vhead r
        | S a => fun r => fun u => Vhead r + (Vhead u * computeRhat (Vtail r)(Vtail u))
      end.

    Lemma computeRhatInd : forall n (m : VF (S (S n)))(v : VF (S n)),
       computeRhat m v = Vhead m + (Vhead v * computeRhat (Vtail m)(Vtail v)).
    Proof.
      intros. simpl. trivial.
    Qed.

    Fixpoint computeRhatInv n : VF (S n) -> VF n -> VF (S n) :=
      match n with 
        | 0 => fun r => fun u => Vcons (Vhead r) Vnil
        | S a => fun r => fun u => 
          Vcons (Vhead r - (Vhead u * 
            computeRhat (computeRhatInv (Vtail r)(Vtail u)) (Vtail u)))
                (computeRhatInv (Vtail r)(Vtail u))
      end.

    Lemma computeRhatInvInd : forall n (m : VF (S (S n)))(v : VF (S n)),
       computeRhatInv m v = Vcons (Vhead m - (Vhead v * 
            computeRhat (computeRhatInv (Vtail m)(Vtail v)) (Vtail v)))
                (computeRhatInv (Vtail m)(Vtail v)).
    Proof.
      intros. simpl. trivial.
    Qed.

    Lemma computeRhatInvInd2 : forall n (m : VF (S (S n)))(v : VF (S n)),
       Vtail (computeRhatInv m v) = computeRhatInv (Vtail m)(Vtail v).
    Proof.
      intros. simpl. trivial.
    Qed.

   Lemma computRhatInvHead : forall n (x : VF (S n))(v : VF n),
    Vhead (rev (computeRhatInv x v)) = Vhead (rev x).
   Proof.
      intros. induction n. rewrite (VSn_eq x). rewrite (Vector_0_is_nil (Vtail x)).
      simpl. trivial.
      rewrite computeRhatInvInd. rewrite rev_Vhead. rewrite VlastS_cons.
      rewrite <- rev_Vhead. rewrite IHn. rewrite rev_Vtail. 
      rewrite Vhead_Vremove_last. trivial.
   Qed.
  
    Lemma computRhatInvVlastS : forall n (x : VF (S n))(v : VF n),
    VlastS (computeRhatInv x v) = VlastS x.
   Proof.
      intros. induction n. rewrite (VSn_eq x). rewrite (Vector_0_is_nil (Vtail x)).
      simpl. trivial.
      rewrite computeRhatInvInd. rewrite VlastS_cons.
      rewrite IHn. rewrite VlastS_tail. trivial.
   Qed.

   Lemma computRhatInvsub : forall  n i (x : VF (S n))(v : VF (S n))
          (ip : S i <= S n),
      computeRhatInv (Vsub (rev x) (le_sub2 ip)) (Vremove_last (Vsub v (le_sub2 ip))) =
      Vsub (computeRhatInv (rev x) (Vremove_last v)) (le_sub2 ip).
    Proof.
      (* Discharged the case where sub was redudent *)
      intros n. induction n. intros. 
      + (* Base case *)
      assert (i = 0%nat). lia. subst. simpl. rewrite <- Vnth0Head. trivial.
      + (* Induction step *)
      intros. destruct (Nat.eq_dec i (S n)). 
      ++ (* Case where we take the whole vector *)
      subst. do 3 rewrite le_sub2_eq. trivial.
      ++ (* Case where we don't take the whole vector *)
      symmetry. rewrite computeRhatInvInd. rewrite Vsub_cons2s. lia. intros. 
      +++ (* Main game *)
      rewrite rev_tail_last. rewrite <- Vremove_last_Vtail. rewrite <- IHn.
      apply f_equal2.
      ++++ (* x *)
      apply Veq_nth. intros. do 2 rewrite Vnth_sub. do 2 rewrite Vbuild_nth. 
      rewrite Vnth_remove_last. apply Vnth_eq. lia.
      ++++ (* v *)
      apply Veq_nth. intros. do 4 rewrite Vnth_sub. rewrite Vnth_tail.
      apply Vnth_eq. lia.
    Qed.

    Lemma RhatInvCorr : forall n (m : VF (S n))(v : VF (S n)),
      computeRhatInv (rev (Vbuild (fun (i0 : nat) (ip0 : i0 < S n) =>
        computeRhat (rev (Vsub m (le_sub ip0))) 
                    (rev (Vtail (Vsub v (le_sub ip0)))))))
         (rev (Vtail v)) = rev m.
    Proof.
      intros. induction n. 
      + do 2 rewrite rev_one. rewrite rev_zero.
      unfold computeRhatInv. simpl. rewrite <- Vnth0Head.
       apply Lenght0Recon.
      (* Start case 2 *)
      + rewrite computeRhatInvInd. rewrite rev_tail_last.
      rewrite Vbuild_remove_last. rewrite rev_tail_last. rewrite Vremove_last_Vtail.
      replace (computeRhatInv
        (rev
           (Vbuild
              (fun (j : nat) (jp : j < S n) =>
               computeRhat (rev (Vsub m (le_sub (Nat.lt_lt_succ_r jp))))
                 (rev (Vtail (Vsub v (le_sub (Nat.lt_lt_succ_r jp))))))))
        (rev (Vtail (Vremove_last v)))) with 
    (computeRhatInv (rev (Vbuild
              (fun (i0 : nat) (ip0 : i0 < S n) =>
               computeRhat (rev (Vsub (Vremove_last m) (le_sub ip0)))
      (rev (Vtail (Vsub (Vremove_last v) (le_sub ip0))))))) 
      (rev (Vtail (Vremove_last v)))). rewrite IHn.
      apply Veq_nth; intros. rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
      (* Handling tail *)
      ++ do 2 rewrite Vbuild_nth. rewrite Vnth_remove_last. apply Vnth_eq. lia.
      (* Handeling head *)      
      ++ rewrite rev_Vhead. rewrite VlastS_nth. rewrite Vbuild_nth.
      rewrite computeRhatInd. assert (forall a b c d e f,
        a = f -> b = d -> c = e ->
        a + b * c - d * e = f). intros. subst. ring; auto. apply H.
      +++ (* Proving the none cancelling elements are equal *)
      rewrite Vhead_nth. do 2 rewrite Vbuild_nth. rewrite Vnth_sub.
      apply Vnth_eq. lia.
      +++ (* Proving u *)
      do 2 rewrite Vhead_nth. do 2 rewrite Vbuild_nth. rewrite Vnth_sub.
      rewrite Vnth_tail. apply Vnth_eq. lia.
      +++ (* Proving m equal *)
      apply f_equal2. apply Veq_nth. intros; rewrite Vbuild_nth.
      rewrite Vbuild_nth. do 2 rewrite Vnth_sub. apply Vnth_eq. lia.
      apply Veq_nth. intros; rewrite Vbuild_nth. rewrite Vnth_tail.
      rewrite Vbuild_nth. rewrite Vnth_sub. rewrite Vnth_tail. 
      rewrite Vnth_remove_last. apply Vnth_eq. lia.
      ++ (* The ones we left behind *)
      apply f_equal2. apply f_equal. apply Veq_nth. intros. do 2 rewrite Vbuild_nth.
      apply f_equal2. apply f_equal. apply Veq_nth. intros. do 2 rewrite Vnth_sub.
      rewrite Vnth_remove_last. apply Vnth_eq. lia. apply f_equal. apply f_equal.
      apply Veq_nth. intros. do 2 rewrite Vnth_sub. rewrite Vnth_remove_last. 
      apply Vnth_eq. lia. trivial.
    Qed.

    Lemma RhatInvCorr2 : forall n (m : VF (S n))(v : VF n),
      computeRhat (computeRhatInv m v) v = (Vhead m).
    Proof.
      intros n. induction n.
      + intros. cbn. trivial.
      + intros. rewrite computeRhatInd. rewrite computeRhatInvInd2.
      rewrite IHn. rewrite computeRhatInvInd. rewrite Vhead_cons.
      rewrite IHn. ring; auto.
    Qed.

    Definition P1 (sce : St*C*E)(r : R1)(w : W) : St*C*E*C1 :=
      let s := sce.1.1 in
    
      let pk := s.1.1.1 in
      let g :=  s.1.1.2 in
      let hs := s.1.2 in
      let e := s.2.1 in
      let e' := s.2.2 in
    
      let u := VandermondeCol (S N) sce.2 in
      let u' := MF_CVmult w.2 u in 

      (sce, Vbuild (fun i (ip : i < S N) => 
        PC g (Vhead hs)
        (VF_prod (Vbuild (fun j (jp : j < S i) => Vnth u' (trans jp ip)))) 
        (computeRhat (rev (Vsub r (le_sub ip))) (rev (Vtail (Vsub u' (le_sub ip))))))). 
  
    Definition ToSt : St*C*E*C1 -> WikstromSigma.St.  
    Proof.
      intros. destruct X. destruct p. destruct p. unfold WikstromSigma.St, 
      WikstromSigmaUnderlying.St. unfold WS.St.
      pose (VandermondeCol (S N) e) as u.
      pose (s.1.1.2) as g. pose s.1.2 as hs.
      exact ((g, Gdot (VG_prod c0) (Ginv (VG_prod hs))), 
      (g, Gdot (VlastS c) (Ginv (Vhead hs) ^ (VF_prod u)))
      , (s.1,s.2.2,(VG_prod (VG_Pexp c0 u),MoC.VG_prod (MoC.VG_Pexp s.2.1 u) ,c))).
    Defined.

    Definition ToWit : St*C*E -> R -> R1 -> W -> WikstromSigma.W.
    Proof.
      intros.  destruct X. destruct p. unfold WikstromSigma.W, 
      WikstromSigmaUnderlying.W, WS.W. 
      pose (VandermondeCol (S N) e) as u.
      pose (MF_CVmult X2.2 u) as u'.
      exact (VF_sum X0, computeRhat
  (rev X1)
  (rev (Vtail (MF_CVmult X2.2 (VandermondeCol (S N) e)))),
       (u', VF_inProd u X0, RF_inProd u X2.1, X1)).
    Defined.

    Lemma ToValid : forall s w r r1 e,
      Rel s w ->
      WikstromSigma.Rel (ToSt (P1 (P0 s r w, e) r1 w)) (ToWit (P0 s r w, e) r r1 w).
    Proof.
      pose module_abegrp. pose G1.module_abegrp. pose G.module_abegrp. pose vs_field.
      intros. unfold WikstromSigma.Rel, ToSt, P1, P0, ToWit, 
      WikstromSigmaUnderlying.Rel. 
      do 6 rewrite Prod_left_replace. do 4 rewrite Prod_right_replace.
      unfold Rel in H. apply andb_true_iff in H. destruct H.
      apply andb_true_iff. split. apply andb_true_iff. split.
      (* First dLog *)
      + unfold dLogSig.Rel, dLogSig.HardProb.dLog. apply bool_eq_corr. simpl.
      unfold VG_prod, com. rewrite <- EPCMultExt. rewrite permutationSum.
      unfold EPC. rewrite VG_One_exp. rewrite <- dot_assoc.
      rewrite <- inv_right. rewrite one_right. trivial.
       apply MF_perm_inv. trivial.
      trivial. 
      (* Second dLog *)
      + unfold dLogSig.Rel, dLogSig.HardProb.dLog. apply bool_eq_corr.
      rewrite Prod_right_replace. rewrite Prod_left_replace.
      unfold VlastS. rewrite Vlast_nth. rewrite Vbuild_nth. unfold PC.
      assert (Vbuild (fun (j : nat) (jp : j < S N) =>
      Vnth (MF_CVmult w.2 (VandermondeCol (S N) e)) (trans jp (Nat.lt_succ_diag_r N)))
      = Vbuild (fun (j : nat) (jp : j < S N) => Vnth 
      (MF_CVmult w.2 (VandermondeCol (S N) e)) jp)). apply Veq_nth. intros. 
      do 2 rewrite Vbuild_nth. apply Vnth_eq. trivial. rewrite H1.
      rewrite permutationInnerProd. trivial. rewrite <- dot_assoc. 
      rewrite ALVS2.neg_eq2.
      rewrite <- ALVS2.neg_eq. rewrite <- inv_right. rewrite one_right.
      apply f_equal. apply f_equal2. apply f_equal. apply Veq_nth. intros.
      rewrite Vnth_cons. destruct (lt_ge_dec 0 i). rewrite Vnth_sub. apply Vnth_eq.
      lia. apply Vnth_eq. lia. apply Veq_nth. intros.
      do 2 rewrite Vbuild_nth.  do 2 rewrite Vnth_tail.
      rewrite Vnth_sub. apply Vnth_eq. trivial. trivial.
      (* Remaining *)
      + unfold WS.Rel. do 7 rewrite Prod_left_replace. 
      do 6 rewrite Prod_right_replace.  apply andb_true_iff. split. 
      apply andb_true_iff. split. apply andb_true_iff. split.
      (* matrix commitment *)
      ++ apply bool_eq_corr. unfold VG_Pexp. rewrite comEPCDis. unfold VG_prod.
      rewrite <- EPCMultExt. apply f_equal2.
      +++ apply Veq_nth. intros. rewrite Vfold_left_VF_add. rewrite MF_getRow_prod.
      rewrite VF_scale_multi. unfold MF_trans. rewrite FMatrix.mat_transpose_row_col.
      rewrite InProd_Sum. unfold VF_sum, VF_mult, FMatrix.get_row. trivial.
      +++ rewrite InProd_Sum. unfold VF_sum. apply f_equal. apply Veq_nth.
      intros. do 2 rewrite Vnth_map2. field; auto.
      (* encryption *)
      ++ apply bool_eq_corr. unfold relReEnc in H. 
      assert (s.2.1 = Vmap2 (reenc s.1.1.1) (MoC.PexpMatrix s.2.2 (MF_trans w.2))
        (Vmap Ring.Finv w.1)).
      apply Veq_nth. intros. apply (bVforall3_elim_nth ip) in H. unfold bIsReEnc in H.
      apply bool_eq_corr in H. rewrite Vnth_map2. rewrite H. rewrite Vnth_map.
      unfold reenc. rewrite dot_assoc. rewrite enc.homomorphism. 
      destruct Ring.module_ring. rewrite Ropp_def. rewrite one_right. 
      rewrite enc.encZero. rewrite one_left. trivial. rewrite H1. unfold reenc.
      assert (Vmap2
        (fun (c : G1.G) (r0 : Ring.F) => G1.Gdot (enc.enc s.1.1.1 enc.Mzero r0) c)
        (MoC.PexpMatrix s.2.2 (MF_trans w.2)) (Vmap Ring.Finv w.1) = 
      MoC.VG_mult (Vmap (fun r0 => enc.enc s.1.1.1 enc.Mzero r0) (Vmap Ring.Finv w.1))
        (MoC.PexpMatrix s.2.2 (MF_trans w.2))). apply Veq_nth. intros. do 2 rewrite Vnth_map2.
      do 3 rewrite Vnth_map. trivial. rewrite H2. rewrite MoC.VG_Pexp_mult.
      rewrite MoC.VG_Prod_mult_dist. rewrite comm. apply f_equal2. 
      +++ rewrite MoC.PexpMatrix_Pexp. 
      unfold MF_trans. rewrite FMatrix.mat_transpose_idem. rewrite MoC.PexpMatrix_Prod.
     trivial. apply MF_perm_inv. trivial. apply MF_perm_inv. trivial.
      +++ unfold RF_inProd. assert (MoC.VG_Pexp
     (Vmap [eta enc.enc s.1.1.1 enc.Mzero] (Vmap Ring.Finv w.1))
     (VandermondeCol (S N) e) =
      Vmap [eta enc.enc s.1.1.1 enc.Mzero] (Vmap Ring.Finv 
      (Vmap2 MVS.op3 w.1 (VandermondeCol (S N) e)))). apply Veq_nth. intros.
      rewrite Vnth_map2. do 3 rewrite Vnth_map. rewrite enc.encOfOnePrec.
      apply f_equal. rewrite Vnth_map. rewrite Vnth_map2. rewrite MVS.RopInvDis.
      trivial. rewrite H3.
      unfold MoC.VG_prod. rewrite ALenc.foldZero. apply f_equal. rewrite MoR.VF_neg_sum.
      unfold MoR.VF_sum, MoR.VF_neg.  trivial.
      (* Chat 0 *)
      ++ apply bool_eq_corr. rewrite Vbuild_nth. apply f_equal2.
      +++ rewrite Vbuild_1. rewrite VF_prod_1. apply Vnth_eq. trivial.
      +++ simpl. apply Vnth_eq. trivial.
      (* C hat i *)
      ++ apply VGeq. apply Veq_nth. intros. rewrite Vnth_tail. 
      do 2 rewrite Vnth_map2. rewrite Vbuild_nth. rewrite Vnth_remove_last.
      rewrite Vbuild_nth. unfold WS.PC.PC, PC. pose PC_up0. unfold PC in e0.
      rewrite e0. apply f_equal2.
      +++ apply f_equal. rewrite computeRhatInd. apply f_equal2.
      rewrite Vhead_nth. rewrite Vbuild_nth. rewrite Vnth_sub. rewrite Vnth_tail.
      apply Vnth_eq. lia. destruct f. destruct F_R. rewrite Rmul_comm. apply f_equal2.
      apply f_equal2. apply Veq_nth. intros. rewrite Vnth_tail. do 2 rewrite Vbuild_nth.
      do 2 rewrite Vnth_sub. apply Vnth_eq. lia. apply Veq_nth. intros. rewrite Vnth_tail. 
      do 2 rewrite Vbuild_nth. do 2 rewrite Vnth_sub. apply Vnth_eq. lia.
      rewrite Vhead_nth. rewrite Vbuild_nth. do 2 rewrite Vnth_tail. rewrite Vnth_sub. 
      apply Vnth_eq. lia.
      +++ apply f_equal. unfold VF_prod. rewrite Vfold_left_build. apply f_equal2. 
      ++++ apply f_equal. apply Veq_nth. intros. do 2 rewrite Vbuild_nth.
      apply Vnth_eq. trivial.
      ++++ rewrite Vnth_tail. apply Vnth_eq. trivial.
       intros; field; auto.
      intros; field; auto.
    Qed.

    Lemma pres_p0 : forall (s : St)(r : R)(w : W), 
        (P0 s r w) = (s,(P0 s r w).2).
    Proof.
      intros. unfold P0. trivial.
    Qed.

    Lemma pres_p1 : forall (s : St*C*E)(r : R1)(w : W), 
        (P1 s r w) = (s,(P1 s r w).2).
    Proof.
      intros. unfold P1. trivial.
    Qed.

    Definition M := S N.

    Definition extractor (resp : vector WikstromSigma.W M)(chal : vector E M) : W :=
      (RF_CVmult (VandermondeInv chal) (Vmap (fun x => x.2.1.2) resp),
      MF_trans (MF_mult (VandermondeInv chal) (Vmap (fun x => x.2.1.1.1) resp))).

    (* This is Theorem 1 from Proofs of Restricted Shuffles *)
    Lemma Theorem1 : forall N (m : MF N),
      MFisPermutation m <-> (MF_CVmult m (VF_one N) = (VF_one N) /\
      forall a, VF_prod (MF_CVmult m a) = VF_prod a).
    Proof.
      intros. split; intros. 
      + split; intros. apply Veq_nth. intros. rewrite MF_getRow_prod.
      unfold MFisPermutation in H. apply andb_true_iff in H. destruct H.
      apply (bVforall_elim_nth ip) in H. unfold VF_an_id in H. apply bVexists_eq in H.
      elim H. intros. elim H1.  intros. apply VF_beq_true in H2. rewrite H2.
      rewrite Vbuild_nth. unfold VF_inProd. rewrite FMatrix.VA.dot_product_id.
      do 2 rewrite Vnth_const. trivial. apply permutationInnerProd_sub. trivial.
      + (* Now for the difficult implication that two equalities imply the result *)
      case_eq (MFisPermutation m); intros. trivial. unfold MFisPermutation in H0.
      apply andb_false_iff in H0. destruct H. 
      (* We need to remove the case where the matrix is of size zero *)
      destruct N0. destruct H0.
      ++ apply bVforall_false in H0. elim H0. intros. elim H2; intros. lia.
      ++ apply bVforall_false in H0. elim H0. intros. elim H2; intros. lia.
      ++ case_eq (bVforall   (* Now we consider if all rows are non-zero *)
    (fun x => Bool.eqb (VF_beq (VF_zero (S N0)) x) false) m); intros.
      +++ (* This is the main case of the origional proof of the theorem *)
      destruct H0. (* The real difficulty is because we are not working over a ring
      of variables we need to find a concrete example rather than appealing to 
      unique factorisation domain *)
      ++++ (* Row case *)
      admit.
      ++++ (* Col case *)
      admit.
      (* One little side case remaining *)
      +++ apply bVforall_false in H2. elim H2; intros. elim H3; intros.
      apply eqb_false_iff in H4. apply not_false_is_true in H4. 
      apply VF_beq_true in H4. assert (VF_prod (MF_CVmult m (VF_one (S N0))) = 0).
      apply (VF_prod_MF_CVmult_zero m (VF_one (S N0)) x0 H4).
      assert (VF_prod (MF_CVmult m (VF_one (S N0))) = VF_prod (VF_one (S N0))). 
      apply (H1 (VF_one (S N0))). rewrite H6 in H5. rewrite VF_prod_one in H5.
      destruct Field.vs_field. unfold not in F_1_neq_0. assert False. apply F_1_neq_0.
      trivial. auto. 
    Admitted. 

    (* The implication if a matrix isn't a permutation *)
    Lemma Theorem1_consq : forall N (m : MF N),
      MFisPermutation m = false <-> (MF_CVmult m (VF_one N) <> (VF_one N)) \/
      ((forall a, VF_prod (MF_CVmult m a) = VF_prod a) -> False).
    Proof.
      intros. split; intros.
      + apply not_true_iff_false in H. 
      case_eq (VF_beq (MF_CVmult m (VF_one N0)) (VF_one N0)); intros. 
      ++ right. intros. apply H. apply Theorem1.  apply VF_beq_true in H0.
      split; auto.
      ++ left. apply VF_beq_false. trivial.
      + apply not_true_iff_false. unfold not. intros. apply Theorem1 in H0.
      destruct H. apply H. apply H0. apply H. apply H0.
    Qed.

    Definition fail_event (s : St)(c : C)(v : vector E M) : Prop :=
      let h   := s.1.1.2 in
      let hs  := s.1.2 in
      (* Commitments broken *)
      (exists c m0 m1 r0 r1, relComEPC h hs c m0 m1 r0 r1) \/
      (* Or schwartz zippel lemma *)
      (exists c m r,
        c = comEPC h hs (MF_trans m) r /\ (* If you commit to the polynomial before the challenge *)
        ((forall a, VF_prod (MF_CVmult m a) = VF_prod a) -> False) /\ (* And the polynomial is not equal *)
        VF_prod (MF_CVmult m (VandermondeCol (S N) (Vhead v))) = (* but it is equal when samples *)
        VF_prod (VandermondeCol (S N) (Vhead v))                 (* at the challenge the extract is free *)
      ).

    Definition RandCon (n : nat)(v : vector (F*F) n) :=
    Vfold_left (fun ac x => x.2 + x.1 * ac) 0 v.

    Lemma RandConSucc : forall (n : nat)(v : vector (F*F) (1+n))(np : Nat.lt n (1+n)),
    RandCon v = (Vnth v np).2 + (Vnth v np).1 * (RandCon (Vremove_last v)).
    Proof.
      intros. unfold RandCon. rewrite Vfold_left_remove_last. trivial.
    Qed.

   Lemma takeRemoveLast : forall(A : Type)(i n : nat)(np : Nat.le (0+i) n)
    (np' : Nat.le (0+(1+i)) n)(v : vector A n),
    Vsub v np = Vremove_last (Vsub v np' ).
    Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_remove_last.
      do 2 rewrite Vnth_sub. apply Vnth_eq. trivial.
    Qed.


      Lemma takeMult : forall(n : nat)(u' : VF n),
        forall (i : nat),
        forall (ip : Nat.le (Nat.add 0 i) n),
        forall (ip' : Nat.le (Nat.add 0 (1+i)) n),
        forall (ip'' : Nat.lt i n),
        Vfold_left Fmul 1 (Vsub u' ip')
        = Vfold_left Fmul 1 (Vsub u' ip) *
         Vnth u' ip''.
    Proof.
      intros. rewrite Vfold_left_remove_last. intros. 
      assert (forall a a' b b', a =a' -> b=b' -> a*b=a'*b').
      intros. rewrite H. rewrite H0. trivial. lia. intros.
      rewrite <- (takeRemoveLast ip). trivial. rewrite Vnth_sub. apply f_equal.
      apply Vnth_eq.
      lia. 
    Qed. 

    Lemma EPC_PC_equiv : forall n h hs m r,
      EPC h hs (Vcons m (VF_zero n)) r = PC h (Vhead hs) m r.
    Proof.
      pose module_abegrp.
      intros. unfold EPC, PC. apply f_equal2; auto. simpl. rewrite VG_Zero_exp.
      rewrite VG_prod_Vcons. rewrite VG_Zero_prod. pose one_left. apply e.
    Qed.

    Lemma Statment4_cruch :
    forall (h h1 : G)(cHat : VG (1+N))(u' rHat : VF (1+N)),
    let comb := Vmap2 (fun x y => (x,y)) u' rHat in
    WS.MoG.VG_eq (Vtail cHat)
       (Vmap2 (fun x : F -> G => [eta x])
          (Vmap2 (fun (h1 : G) (u : F) => [eta WS.PC.PC h h1 u])
             (Vremove_last cHat) (Vtail u'))
          (Vtail rHat)) = true ->
    Gbool_eq (Vnth cHat (Nat.lt_0_succ N))
       (WS.PC.PC h h1 (Vnth u' (Nat.lt_0_succ N))
          (Vnth rHat (Nat.lt_0_succ N))) = true ->
    VlastS cHat = PC h h1 (VF_prod u') 
     (RandCon comb).
    Proof.
      destruct Field.vs_field. destruct F_R. pose G2.module_abegrp.
      intros.
      assert (forall (i :nat)(ip : Nat.le (0+(1+i)) (1+N))(ip' : Nat.lt i (1+N)),
          let u'sub := Vsub u' ip  in 
          let rHatSub := Vsub rHat ip in 
          let combSub := Vmap2 (fun x y => (x,y)) u'sub rHatSub in
          Vnth cHat ip' = PC h h1 (VF_prod u'sub) (RandCon combSub)).
      (* beginning induction *)
      intros. induction i. rewrite (VSn_eq u'sub). rewrite (VSn_eq combSub).
      rewrite (Vector_0_is_nil (Vtail u'sub)). rewrite (Vector_0_is_nil (Vtail combSub)).
      simpl. assert (Vnth cHat ip' = Vhead cHat). rewrite Vhead_nth.
      apply Vnth_eq. trivial. rewrite H1. apply bool_eq_corr in H0. 
      rewrite Vhead_nth. rewrite H0.
      apply PC_m_r_eq. unfold VF_prod. rewrite Vfold_left_Vcons_Fmul.
      simpl. rewrite Rmul_1_l. apply Vnth_eq.
      trivial. unfold RandCon. simpl. assert (forall a, a * 0 = 0). intros.
      rewrite Rmul_comm. apply FSRth.
      rewrite H2. rewrite Radd_comm. rewrite Radd_0_l. apply Vnth_eq. trivial. 
      (* induction part 2 *)
      assert (Nat.lt i N). apply lt_S_n. apply ip'. apply VGeq in H.
      apply (Veq_nth4 H1) in H. assert (Vnth cHat ip' = Vnth (Vtail cHat) H1).
      rewrite Vnth_tail. apply Vnth_eq. trivial.
      rewrite H2. rewrite H. do 2 rewrite Vnth_map2.
      assert (Nat.lt i (1 + N)). apply le_S. apply H1.
      pose (IHi H3). assert ((Vnth (Vremove_last cHat) H1) = 
      Vnth cHat H3). rewrite Vnth_remove_last_intro. trivial.
      rewrite H4. rewrite e. replace WS.PC.PC with PC. rewrite PC_up0. 
      apply PC_m_r_eq. 
      (* proving message equal *) 
      unfold VF_prod. symmetry. unfold u'sub. rewrite takeMult. intros. 
      symmetry. assert (forall a b b', b =b' -> a*b = a*b').
      intros. rewrite H5. trivial. apply H5. rewrite Vnth_tail. apply Vnth_eq. trivial.
      (* proving randomness equal *)
      unfold combSub, u'sub, rHatSub. symmetry. rewrite RandConSucc. lia. intros. 
      rewrite Vnth_map2. unfold fst. unfold snd. assert (forall a a' b b' c c', 
      a=a' -> b=b' -> c=c' -> a+b*c = a'+c'*b'). intros.  rewrite H5. rewrite H6.
      rewrite H7. rewrite Rmul_comm. trivial. apply H5. rewrite Vnth_tail.
      rewrite Vnth_sub. apply Vnth_eq. trivial. rewrite Vnth_tail. rewrite Vnth_sub. 
      apply Vnth_eq. trivial. assert (forall n (a b : vector (F*F) n),
       a=b -> RandCon a = RandCon b). intros. rewrite H6. trivial. apply H6. 
       rewrite Vremove_last_vmap2. apply Vmap2_eq. rewrite <- (takeRemoveLast H3).
      trivial. rewrite <- (takeRemoveLast H3). trivial. auto. auto.
     (* Finsing up *) 
      rewrite VlastS_nth. rewrite H1. lia. intros. apply PC_m_r_eq. 
      rewrite Vsub_id. trivial. do 2 rewrite Vsub_id. trivial. 
    Qed.

    Lemma special_soundness : forall s c (e : vector E M)(c1 : vector C1 M)
          (w : vector WikstromSigma.W M),
      bVforall3 (fun a b d => WikstromSigma.Rel (ToSt (s,c,a,b)) d) e c1 w ->
      PairwisePredicate (fun a b => disjoint a b) e  ->
      Rel s (extractor w e) \/ fail_event s c e.
    Proof.
      pose module_abegrp. pose G1.module_abegrp. pose G.module_abegrp. pose vs_field. intros. 
      (********************************************)      
      (* We are going to do some basic equalities *)
      (********************************************)
      (* prod u' = prod u *)
      case_eq (Fbool_eq (VF_prod (Vhead w).2.1.1.1) (VF_prod (VandermondeCol M (Vhead e))));
     intros prod.
      (* We need to do the basic permutation *)
     + assert (c = comEPC s.1.1.2 s.1.2 (MF_mult (VandermondeInv e)
     (Vmap (fun x : WikstromSigmaUnderlying.W *
               (WS.Mo.VF (S N) * F * Ring.F * WS.Mo.VF (S N)) => x.2.1.1.1) w))
      (MF_CVmult (VandermondeInv e) (Vmap (fun x => x.2.1.1.2) w))).
    unfold WikstromSigma.Rel in H. unfold WS.Rel in H. unfold ToSt in H.
    apply Veq_nth. intros. rewrite Vnth_map2. rewrite MF_getRow_VCmul.
    rewrite MF_getRow_prod. 
    assert (Vnth c ip = Vnth (PexpMatrix c (MF_mult (VandermondeInv e) (Vandermonde e) )) ip).
    rewrite invVandermondeLeft. rewrite (PexpMatrix_nth c (MF_id M) ip ip). trivial.
    rewrite MF_Vnth_id. trivial. trivial. rewrite H1. rewrite PexpMatrix_MF_mult.
    assert (Vbuild (fun (j : nat) (jp : j < 1 + N) => VG_prod (VG_Pexp c (Vnth 
        (Vandermonde e) jp))  ^ Vnth (Vnth (VandermondeInv e) ip) jp) = 
      Vbuild (fun (j : nat) (jp : j < 1 + N) => WS.EPC.EPC s.1.1.2 s.1.2 
      (Vnth w jp).2.1.1.1 (Vnth w jp).2.1.1.2 ^ Vnth (Vnth (VandermondeInv e) ip) jp)).
    apply Veq_nth. intros. do 2 rewrite Vbuild_nth.
    apply (bVforall3_elim_nth ip0) in H.
    do 5 rewrite Prod_left_replace in H. do 3 rewrite Prod_right_replace in H.
    apply andb_true_iff in H. destruct H. apply andb_true_iff in H2. destruct H2.
    apply andb_true_iff in H2. destruct H2. apply andb_true_iff in H2. destruct H2.
    apply bool_eq_corr in H2. rewrite Vnth_map. rewrite H2. trivial. clear H.
    rewrite H2. rewrite VG_Pexp_build. unfold VG_Pexp. rewrite comEPCDis_build.
    unfold VG_prod. rewrite <- EPCMultExt_build. apply f_equal2. 
    apply Veq_nth. intros. rewrite MF_getCol_prod. rewrite Vfold_left_VF_add.
    rewrite InProd_Sum. apply f_equal. apply Veq_nth. intros. rewrite Vnth_map.
    rewrite Vbuild_nth. rewrite Vnth_map2. do 3 rewrite Vnth_map. destruct f.
    destruct F_R. rewrite Rmul_comm. trivial. rewrite InProd_Sum. apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vbuild_nth. 
    rewrite Vnth_map. destruct f. destruct F_R. rewrite Rmul_comm. trivial.
    (* End permutation commitment *)
    case_eq (MFisPermutation (MF_mult (VandermondeInv e) (Vmap (fun x : WikstromSigmaUnderlying.W *
      (WS.Mo.VF (S N) * F * Ring.F * WS.Mo.VF (S N)) => x.2.1.1.1) w))). 
    (* Case where we opened to a permutation matrix *)
    ++ intros. left. unfold extractor, Rel. apply andb_true_iff. split.
    +++ apply relReEnc_equiv. rewrite Prod_right_replace. rewrite Prod_left_replace.
    assert (s.2.1 = MoC.PexpMatrix s.2.1 (MF_mult (VandermondeInv e) (Vandermonde e))).
    rewrite invVandermondeLeft. rewrite MoC.PexpMatrixId. trivial. trivial.
    rewrite H3. rewrite <- MoC.PexpMatrix_MF_mult_base.
    (* Lets use the sigma relationship *)    
    assert (MoC.PexpMatrix s.2.1 (Vandermonde e) = 
      Vmap (fun x => G1.Gdot (WS.MoC.VG_prod (WS.MoC.VG_Pexp s.2.2 x.2.1.1.1))
  (enc.enc s.1.1.1 enc.Mzero (Ring.Finv x.2.1.2))) w).
    apply Veq_nth. intros. unfold WikstromSigma.Rel in H. 
    unfold WS.Rel in H. unfold ToSt in H. apply (bVforall3_elim_nth ip) in H.
    do 5 rewrite Prod_left_replace in H. do 3 rewrite Prod_right_replace in H.
    apply andb_true_iff in H. destruct H. apply andb_true_iff in H4. destruct H4.
    apply andb_true_iff in H4. destruct H4. apply andb_true_iff in H4. destruct H4.
    apply bool_eq_corr in H7. do 3 rewrite Vnth_map. rewrite H7. trivial.
    (* Resuming encryption *)
    rewrite H4. assert (Vmap (fun x => G1.Gdot (WS.MoC.VG_prod (WS.MoC.VG_Pexp 
    s.2.2 x.2.1.1.1)) (enc.enc s.1.1.1 enc.Mzero (Ring.Finv x.2.1.2))) w = 
    MoC.VG_mult (Vmap (fun x => WS.MoC.VG_prod (WS.MoC.VG_Pexp 
    s.2.2 x.2.1.1.1)) w) (Vmap (fun x => enc.enc s.1.1.1 enc.Mzero (Ring.Finv x.2.1.2))
    w)). apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_map. trivial.
    rewrite H5. rewrite MoC.PexpMatrix_mult. rewrite MoC.VG_comm. pose MoC.VG_assoc.
    unfold MoC.VG_mult in *. rewrite <- e0. assert (Vmap2 G1.Gdot
     (Vmap (enc.enc s.1.1.1 enc.Mzero)
        (RF_CVmult (VandermondeInv e)
           (Vmap
              (fun
                 x : WikstromSigmaUnderlying.W *
                     (WS.Mo.VF (1 + N) * F * Ring.F * WS.Mo.VF (1 + N)) => x.2.1.2) w)))
     (MoC.PexpMatrix
        (Vmap
           (fun
              x : WikstromSigmaUnderlying.W *
                  (WS.Mo.VF (1 + N) * F * Ring.F * WS.Mo.VF (1 + N)) =>
            enc.enc s.1.1.1 enc.Mzero (Ring.Finv x.2.1.2)) w) 
        (VandermondeInv e)) = Vconst G1.Gone (1+N)). apply Veq_nth. intros.
    rewrite Vnth_map2. do 3 rewrite Vnth_map. rewrite Vnth_const. 
    unfold MoC.VG_Pexp, MoC.VG_prod. replace (Vmap (fun x =>
            enc.enc s.1.1.1 enc.Mzero (Ring.Finv x.2.1.2)) w) with
   (Vmap (fun x => enc.enc s.1.1.1 enc.Mzero x) (Vmap (fun x=> Ring.Finv x.2.1.2) w)).
   rewrite encOfOnePrec_map. rewrite <- comHomomorphism_map. rewrite enc.homomorphism.
   rewrite one_right. assert (forall a, a= Ring.Fzero -> enc.enc s.1.1.1 enc.Mzero a = G1.Gone).
   intros. rewrite H6. apply EncZeroZeroIsOne. apply H6. pose MoR.VF_sum_add.
   unfold MoR.VF_sum. rewrite e1.  assert (forall a, a= Vconst Ring.Fzero (S N) -> MoR.VF_sum a = Ring.Fzero).
    intros. rewrite H7. apply MoR.VF_sum_VF_zero. apply H7. apply Veq_nth. intros.
    do 3 rewrite Vnth_map2. do 2 rewrite Vnth_map. rewrite MVS.RopInvDis.
    destruct Ring.module_ring. rewrite Radd_comm. rewrite Ropp_def. rewrite Vnth_const.
    trivial. apply Veq_nth. intros. do 3 rewrite Vnth_map. trivial.
    rewrite H6.
    pose MoC.VG_comm. pose MoC.VG_one. unfold MoC.VG_mult in *. rewrite e1. 
    rewrite e2. pose MoC.PexpMatrix_MF_mult_base. 
    assert (Vmap (fun x => WS.MoC.VG_prod (WS.MoC.VG_Pexp s.2.2 x.2.1.1.1)) w =  
    MoC.PexpMatrix s.2.2 (Vmap (fun x=>x.2.1.1.1) w)). apply Veq_nth. intros.
    do 3 rewrite Vnth_map. trivial. rewrite H7. rewrite e3. unfold MF_trans. 
    rewrite FMatrix.mat_transpose_idem. trivial.
    +++ simpl. apply MF_perm_inv. trivial.
    (* Other case / Argument broken - we have discharged the case where it is a permutation *)
    ++ intros. right. unfold fail_event. 
    case_eq (VF_beq (MF_CVmult (MF_trans (MF_mult (VandermondeInv e)
          (Vmap (fun x => x.2.1.1.1) w))) (VF_one (S N))) (VF_one (S N))); intros.

    (* Option 2 from res. proofs of shuffle *)    
    +++ (* We case on if the Schwartz-Zippel lemma faield use *)
    case_eq (Fbool_eq (VF_prod (MF_CVmult (MF_trans (MF_mult (VandermondeInv e)
          (Vmap (fun x => x.2.1.1.1) w))) (VandermondeCol (S N) (Vhead e))))
   (VF_prod (VandermondeCol (S N) (Vhead e)))); intros.
    (* We in the case where the schwartz zippel lemma is broken *)
    ++++ right. apply MF_not_perm_inv in H2. apply Theorem1_consq in H2. destruct H2. 
    apply VF_beq_true in H3. assert False. apply H2. trivial. contradiction.
    exists c.
    exists (MF_trans (MF_mult (VandermondeInv e)
                 (Vmap
                    (fun
                       x : WikstromSigmaUnderlying.W *
                           (WS.Mo.VF (S N) * F * Ring.F * WS.Mo.VF (S N)) =>
                     x.2.1.1.1) w))). exists (MF_CVmult (VandermondeInv e)
          (Vmap
             (fun
                x : WikstromSigmaUnderlying.W *
                    (WS.Mo.VF (1 + N) * F * Ring.F * WS.Mo.VF (1 + N)) => x.2.1.1.2)
             w)). split.
    (* We need to show the lemma failed on a polynomial commited to early *)
    +++++ unfold MF_trans. rewrite FMatrix.mat_transpose_idem. trivial.
    +++++ split. 
    ++++++ trivial. 
    ++++++ apply F_bool_eq_corr in H4. apply H4. 
    (* Resume option 2 in the case where the SZ lemma held *)
    ++++ apply bVforall3_elim_head in H. unfold WikstromSigma.Rel, ToSt,  
    WikstromSigmaUnderlying.Rel, WS.Rel in H. 
    do 5 rewrite Prod_left_replace in H. do 3 rewrite Prod_right_replace in H.
    apply andb_true_iff in H. destruct H. clear H. apply andb_true_iff in H5. 
    destruct H5. clear H5. apply andb_true_iff in H. destruct H.  clear H5.
    apply andb_true_iff in H. destruct H. clear H5. apply bool_eq_corr in H.
    apply VF_beq_true in H3.
    left. exists (VG_prod (VG_Pexp c (VandermondeCol M (Vhead e)))). exists (Vhead w).2.1.1.1.
    exists (MF_CVmult (MF_trans (MF_mult (VandermondeInv e) (Vmap (fun  x =>
    x.2.1.1.1) w))) (VandermondeCol M (Vhead e))). exists (Vhead w).2.1.1.2.
    exists (VF_inProd (MF_CVmult (VandermondeInv e) (Vmap (fun x => x.2.1.1.2)
             w)) (VandermondeCol M (Vhead e))). unfold relComEPC.
    split. unfold not. intros. apply F_bool_neq_corr in H4. apply H4. unfold M in *. 
    rewrite <- H5. apply F_bool_eq_corr in prod.
    trivial. split. rewrite H. trivial. rewrite H1. unfold VG_Pexp. 
    rewrite comEPCDis. unfold VG_prod. rewrite <- EPCMultExt. apply f_equal2.
    +++++
    apply Veq_nth. intros. rewrite Vnth_map. rewrite Vfold_left_VF_add.
    rewrite FMatrix.mat_build_nth. rewrite FMatrix.mat_transpose_col_row.
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq. apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_map. rewrite Vnth_map2.
    rewrite FMatrix.get_col_col_mat. rewrite Vnth_map. apply f_equal2. rewrite Vnth_map.
    trivial. trivial.
    +++++ rewrite InProd_Sum. trivial.


    (* Option 1 for res. proofs of shuffle *)
    +++ apply VF_beq_false in H3. left. exists (VG_prod c).
    exists (MF_CVmult (MF_trans (MF_mult (VandermondeInv e) (Vmap (fun  x => x.2.1.1.1) w))) (VF_one (S N))).
    exists (VF_one (S N)).  apply (bVforall3_elim_nth (lt_0_Sn N)) in H. unfold WikstromSigma.Rel, ToSt,
    WikstromSigmaUnderlying.Rel, WS.Rel, dLogSig.Rel, dLogSig.HardProb.dLog in H.
    do 5 rewrite Prod_left_replace in H. do 3 rewrite Prod_right_replace in H.
    apply andb_true_iff in H. destruct H. apply andb_true_iff in H. destruct H.
    apply bool_eq_corr in H. clear H4. 
    exists (VF_sum (MF_CVmult (VandermondeInv e) (Vmap (fun x => x.2.1.1.2)  w))).
    exists ((Vnth w (Nat.lt_0_succ N)).1.1). unfold relComEPC.
    (* First we prove the message are not equal *)
    split.  trivial.
    (* Now we need to prove it opens the commitments *)
    split. 
    ++++ rewrite H1. unfold VG_prod. rewrite <- EPCMultExt. rewrite <- MF_CVmult_one. apply f_equal2.
    (* Message *)    
    +++++ apply Veq_nth. intros. rewrite Vnth_map. rewrite Vfold_left_VF_add. 
    pose FMatrix.mat_transpose_col_row. unfold FMatrix.get_row in e0. rewrite e0. trivial.
    (* Randomness *)
    +++++ trivial.
    ++++ apply b_equal in H. rewrite H. unfold EPC. rewrite VG_One_exp. trivial.

    (* We now deal with the case where prod u' <> prod u *)
    + right. left. apply bVforall3_elim_head in H. unfold WikstromSigma.Rel, ToSt,  
    WikstromSigmaUnderlying.Rel, WS.Rel, dLogSig.Rel, dLogSig.HardProb.dLog   in H. 
    do 6 rewrite Prod_left_replace in H. do 5 rewrite Prod_right_replace in H.
    apply andb_true_iff in H. destruct H. apply andb_true_iff in H. destruct H. 
    clear H. apply andb_true_iff in H1. destruct H1. apply andb_true_iff in H. 
    destruct H. clear H. unfold St, C, M, E, C1, WikstromSigma.W, WikstromSigmaUnderlying.W,
    dLogSig.W, WS.W in *. unfold WS.index0. assert (WS.index0 = lt_0_Sn N). 
    apply le_unique. rewrite H in H3. clear H.
    (* We need to prove a lemma on the way *)
    pose (@Statment4_cruch s.1.1.2 (Vhead s.1.2) (Vhead c1) (Vhead w).2.1.1.1 
      (Vhead w).2.2 H1 H3). exists (VlastS (Vhead c1)). 
    exists (Vcons (VF_prod (Vhead w).2.1.1.1) (VF_zero N)). 
    exists (Vcons (VF_prod (VandermondeCol (S N) (Vhead e))) (VF_zero N)). 
    exists (RandCon (Vmap2 (fun x : F => [eta pair x]) (Vhead w).2.1.1.1 (Vhead w).2.2)).
    exists (Vhead w).1.2. unfold relComEPC. split.
    (* Prove messages are not equal *)
    unfold not. intros. apply not_true_iff_false in prod. apply prod.
    apply F_bool_eq_corr. apply Vcons_eq in H. destruct H. trivial. split.
    (* Prove commitment openings *)
    rewrite e0. rewrite EPC_PC_equiv. trivial. apply bool_eq_corr in H2.
    rewrite ALVS2.neg_eq2 in H2. rewrite <- ALVS2.neg_eq in H2. apply b_equal in H2.
    rewrite H2. rewrite EPC_PC_equiv. trivial.
    Qed.

    Definition TE : Set := VF (1+N)*VF (1+N). 

    Lemma e_abgrp : AbeGroup E add zero bool_eq disjoint inv.
    Proof.
      apply Chal.module_abegrp.
    Qed.

    Definition X := VF (1+N). 

    Definition simulator (s : St)(t : TE)(e : E) : C*C1 :=
      let pk := s.1.1.1 in
      let g :=  s.1.1.2 in
      let hs := s.1.2 in
      (Vmap (fun x => EPC g hs (VF_zero (S N)) x) t.1, 
          Vmap (fun x => PC g (Vhead hs) 0 x) t.2).


    Definition simMap    (s : St)(w : W)(e : E)(x : X)(r : R*R1) : TE :=
      let pk := s.1.1.1 in
      let g :=  s.1.1.2 in
      let hs := s.1.2 in
    
      let u := VandermondeCol (S N) e in
      let u' := MF_CVmult w.2 u in 

      (VF_add r.1 (Vmap (fun y => VF_inProd x y) (MF_trans w.2)), 
        Vbuild (fun i (ip : i < S N) => 
          computeRhat (rev (Vsub r.2 (le_sub ip))) (rev (Vtail (Vsub u' (le_sub ip)))) +
           (Vhead x) * 
              (VF_prod (Vbuild (fun j (jp : j < S i) => Vnth u' (trans jp ip)))))). 

    Definition simMapInv (s : St)(w : W)(e : E)(x : X)(t :  TE) : R*R1 :=
      let pk := s.1.1.1 in
      let g :=  s.1.1.2 in
      let hs := s.1.2 in
    
      let u := VandermondeCol (S N) e in
      let u' := MF_CVmult w.2 u in 

      let t2sim := Vbuild (fun i (ip : i < S N) => Vnth t.2 ip - (Vhead x) * 
              (VF_prod (Vbuild (fun j (jp : j < S i) => Vnth u' (trans jp ip))))) in 

      (VF_sub t.1 (Vmap (fun y => VF_inProd x y) (MF_trans w.2)), 
        rev (computeRhatInv (rev t2sim) (rev (Vtail u')))). 

    Definition simMapHelp (s : St)(x : X) : Prop :=
      let pk := s.1.1.1 in
      let g :=  s.1.1.2 in
      let hs := s.1.2 in
      hs = Vmap (op g) x.

    Definition sigXcomp (s : St)(x : X) : WikstromSigma.X := (0,0,0).
 
    Lemma VbuildSubtract : forall n (gen gen1 : (forall i, i<n -> F)),
      Vbuild (fun i ip => Vnth (Vbuild (fun j jp => gen j jp))
              ip - gen1 i ip) = Vbuild (fun i ip => gen i ip - gen1 i ip).
    Proof.
      intros. apply Veq_nth. intros. do 3 rewrite Vbuild_nth. trivial. 
    Qed.

    Lemma VbuildMinus : forall n (gen gen1 : (forall i, i<n -> F)),
      Vbuild (fun i ip => gen i ip + gen1 i ip - gen1 i ip) =
      Vbuild (fun i ip => gen i ip).
    Proof.
      intros. apply Veq_nth. intros. do 2 rewrite Vbuild_nth. ring; auto.  
    Qed.

    Lemma simMapInvValid :  forall (st : St)(w : W)(x : X)
          (e : E)(r : R*R1)(t : TE),
       Rel st w ->
       simMapHelp st x ->
      simMap st w e x (simMapInv st w e x t) = t /\
      simMapInv st w e x (simMap st w e x r) = r.
    Proof.
      intros. split.
      + unfold simMap, simMapInv. rewrite Prod_left_replace.
      rewrite Prod_right_replace. apply injective_projections.
      ++ rewrite VF_sub_corr. rewrite VF_add_neg2. trivial.
      ++ rewrite Prod_right_replace. apply Veq_nth. intros.
      rewrite Vbuild_nth. rewrite Vsub_rev. rewrite rev_rev.
      do 2 rewrite rev_Vtail. rewrite Vsub_rev. 
      rewrite <- computRhatInvsub. rewrite RhatInvCorr2.
      rewrite Vhead_nth. rewrite Vnth_sub. do 2 rewrite Vbuild_nth.
      assert (forall a b c d,
        a = d -> b = c -> 
        a - b + c = d). intros. subst. ring; auto. apply H1.
      apply Vnth_eq. lia. apply f_equal.
      assert (S (S N - (S N - S i + 0) - 1) = S i). lia.
      apply (Vfold_left_eq_gen H2). apply Veq_nth. intros. rewrite Vnth_cast.
      do 2 rewrite Vbuild_nth. apply Vnth_eq. trivial.
      + unfold simMap, simMapInv. rewrite Prod_left_replace.
      rewrite Prod_right_replace. apply injective_projections.
      ++ rewrite Prod_left_replace. rewrite VF_sub_corr. 
      rewrite VF_add_neg. trivial.
      ++ rewrite Prod_right_replace. rewrite (VbuildSubtract). 
      rewrite VbuildMinus. rewrite RhatInvCorr. rewrite rev_rev. trivial.
    Qed. 

    (* This may need more preconditions otherwise it might be too strong *)
    Lemma simMapHelpValid : forall (st : St)(x : X)(c : C)(c1 : C1)(e : E),
      simMapHelp st x ->
      WikstromSigma.simMapHelp (ToSt (st,c,e,c1)) (sigXcomp st x).
    Proof.
      intros. unfold WikstromSigma.simMapHelp. split. split. unfold dLogSig.simMapHelp. trivial.
      unfold dLogSig.simMapHelp. trivial. unfold WS.simMapHelp. trivial.
    Qed. 

    Lemma simulatorZK1 : forall s w r e x,
       Rel s w ->
       simMapHelp s x ->
       (P0 s r.1 w).2 = (simulator s (simMap s w e x r) e).1.
    Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. unfold simMap. do 2 rewrite Vnth_map2.
      rewrite Vnth_map. unfold simMapHelp in H0. apply trapdoorEPC. trivial.
    Qed.

    Lemma simulatorZK2 : forall s w r e x,
       Rel s w ->
       simMapHelp s x ->
        (P1 (P0 s r.1 w, e) r.2 w).2 = 
        (simulator s (simMap s w e x r) e).2.
    Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. rewrite Vbuild_nth. unfold simMap. 
      rewrite Vbuild_nth. apply trapdoorPC. unfold simMapHelp in H0. apply Vhead_eq in H0.
      rewrite Vhead_map in H0. trivial.
    Qed.

  End ToWikstromMatrix.


End WikstromMixnet.


