Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import ArithRing.
From Groups Require Import groups module vectorspace dualvectorspaces 
  modulevectorspace groupfromring.
Require Import sigmaprotocolPlus.
Require Import Coq.Lists.List.
Require Import Ring.
Require Import Field. 
Require Import Field_theory.
Require Import cryptoprim.
Require Import VectorUtil.
Require Import Lia.
From CoLoR Require Import VecUtil VecArith.
Require Import matrices matricesF.

(* Dirty hack to paramtise the next module *)
Module Type Nat.
  Parameter N : nat.
End Nat.

(* By convention we assume tVS contains the ciphertext space in VS1 and 
  the commitment space in VS2 *)
Module wikSigma (G G1 G2 : GroupSig)(Ring : RingSig)(Field : FieldSig)
    (Chal : GroupFromRing Field)(VS2 : VectorSpaceSig G2 Field)
    (VS1 : VectorSpaceSig G1 Field)
    (MVS : VectorSpaceModuleSameGroup G1 Ring Field VS1)
    (enc : Mixable G G1 Ring Field VS1 MVS)(Hack : Nat) <: SigmaPlus Chal.

  Import Hack.
  Import G2.
  Import Field.

  Module Mo := MatricesFIns Field.
  Import Mo.

  (* Make commitment scheme and matrix *)
  Module EPC := ExtendComScheme G2 Field VS2 Mo.
  Import EPC.
  Module PC := BasicComScheme G2 Field VS2 Mo.
  Import PC.

  Module MoG := MatricesG G2 Field VS2 Mo.
  Import MoG.
  Module MoC := MatricesG G1 Field VS1 Mo.

  (* Addational vector lemma *)
  Module ALVS1 := VectorSpaceAddationalLemmas G1 Field VS1.
  Module ALVS2 := VectorSpaceAddationalLemmas G2 Field VS2.

  Module ALenc := MixablePropIns G G1 Ring Field VS1 MVS enc.
  Import ALenc.

  Module ALR := RingAddationalLemmas Ring.

  Theorem index0 : Nat.lt 0%nat (1+N).
  Proof.
    cbn. apply neq_0_lt. auto.
  Defined. 

  Theorem indexN : Nat.lt N (1+N).
  Proof.
    induction N. cbn.
    apply neq_0_lt. auto. apply lt_n_S. apply IHn.
  Defined. 

  Lemma index0eq : forall(A : Type)(v : vector A (1+N)), 
    (Vnth v (Nat.lt_0_succ N)) = Vnth v index0.
  Proof.
    intros. apply Vnth_eq. trivial.
  Qed.
  (* (Public key, commitment parameterts),(output ciphertexts),
      (Prod c^u, Prod e^u, cHat) *)
  Definition St : Type := (enc.PK*G*(VG (1+N))*(vector G1.G (1+N)))*
        (G*G1.G*(VG (1+N))).
  (* u', rTil, rStar, rHat *)
  Definition W : Type := (VF (1+N)*F*Ring.F*(VF (1+N))).
  Definition R : Type := (VF (1+N)*F*Ring.F*(VF (1+N))).
  Definition T : Type := (VF (1+N)*F*Ring.F*(VF (1+N))).
  Definition TE : Type := (VF (1+N)*F*Ring.F*(VF (1+N))).
  (* t3, t4, tHat i *)
  Definition C : Type := (G*G1.G*(VG (1+N))).

  Definition Rel (s : St)(w : W) := 
    let parm := s.1 in
    let pk := parm.1.1.1 in
    let g := parm.1.1.2 in
    let hs := parm.1.2 in
    let e' := parm.2 in

    let stat := s.2 in
    let a := stat.1.1 in
    let b := stat.1.2 in  (* *)
    let cHat := stat.2 in

    let u' := w.1.1.1 in
    let rTil := w.1.1.2 in
    let rStar := w.1.2 in
    let rHat := w.2 in

    (*Both rBar and rDimond are dealt with elsewhere *)

    (* Prod c^u = EPC u' rTil *)
    Gbool_eq a (EPC g hs u' rTil) &&
      (* Prod e^u = Prod e'^u' * E(1,r) *) 
    G1.Gbool_eq b (G1.Gdot (MoC.VG_prod (MoC.VG_Pexp e' u')) 
                      (enc.enc pk enc.Mzero (Ring.Finv rStar))) &&
      (* ^c_0 = PC_(h,hs))(u',^r)  *)  
    Gbool_eq (Vnth cHat index0) (PC g (Vhead hs) (Vnth u' index0) (Vnth rHat index0)) &&
    (* ^c_i = PC_(h,^c_(i-1))(u',^r)  *)  
    VG_eq (Vtail cHat) (Vmap2 (fun x y => x y)
       (Vmap2 (fun h1 u r => PC g h1 u r) (Vremove_last cHat) (Vtail u')) (Vtail rHat)). 
   
  (** Begin Sigma Proper *)
  (* We pass why to allow branching in disjunction *)
  Definition P0 (s : St)(r w : W) :St*C :=
    let parm := s.1 in
    let pk := parm.1.1.1 in
    let g := parm.1.1.2 in
    let hs := parm.1.2 in
    let e' := parm.2 in

    let stat := s.2 in
    let a := stat.1.1 in
    let b := stat.1.2 in
    let cHat := stat.2 in

    let u' := w.1.1.1 in
    let rTil := w.1.1.2 in
    let rStar := w.1.2 in
    let rHat := w.2 in

    let w' := r.1.1.1 in 
    let w3 := r.1.1.2 in
    let w4 := r.1.2 in 
    let wHat := r.2 in

    let t3 := EPC g hs w' w3 in 
    let t4 := G1.Gdot (MoC.VG_prod (MoC.VG_Pexp e' w')) (enc.enc pk enc.Mzero (Ring.Finv w4)) in
    let tHat1 := PC g (Vhead hs) (Vnth w' index0) (Vnth wHat index0) in
    let tHat2 := (Vmap2 (fun x y => x y)
       (Vmap2 (fun h1 u r => PC g h1 u r) (Vremove_last cHat) (Vtail w')) (Vtail wHat)) in

    (s, (t3, t4, Vapp [tHat1] tHat2)).

  Definition V0 (ggtoxgtor: St*C) 
      (c: F): (St*C*F)
    := (ggtoxgtor, c).

  Definition P1 (ggtoxgtorc: St*C*F) 
      (r w: W) : St*C*F*W :=
    let c    :=  snd (ggtoxgtorc) in

    let u' := w.1.1.1 in
    let rTil := w.1.1.2 in
    let rStar := w.1.2 in
    let rHat := w.2 in

    let w' := r.1.1.1 in 
    let w3 := r.1.1.2 in
    let w4 := r.1.2 in 
    let wHat := r.2 in

    let s3  := w3+rTil*c in
    let s4  := Ring.Fadd w4 (MVS.op3 rStar c) in

    let sHat := VF_add wHat (VF_scale rHat c) in
    let s' := VF_add w' (VF_scale u' c) in
    
    (ggtoxgtorc, (s', s3, s4, sHat)).

  Definition V1 (transcript : St*C*F*W) :=
    
    let s := transcript.1.1.1 in
    let c := transcript.1.1.2 in
    let e := transcript.1.2 in
    let t := transcript.2 in

    let parm := s.1 in
    let pk := parm.1.1.1 in
    let g :=  parm.1.1.2 in
    let hs := parm.1.2 in
    let e' := parm.2 in

    let stat := s.2 in
    let a := stat.1.1 in
    let b := stat.1.2 in
    let cHat := stat.2 in

    let t3 := c.1.1 in
    let t4 := c.1.2 in
    let tHat :=  c.2 in

    let s3  := t.1.1.2 in 
    let s4  := t.1.2 in 
    let sHat := t.2 in 
    let s' := t.1.1.1 in

    (* t3 o a^e = EPC s' s3 *) 
    Gbool_eq (t3 o a^e) (EPC g hs s' s3) && 
    (* t4 o b^e = Prod e'^s' o Enc Gone s4*) 
    G1.Gbool_eq (G1.Gdot t4 (VS1.op b e)) 
      (G1.Gdot (MoC.VG_prod (MoC.VG_Pexp e' s')) (enc.enc pk enc.Mzero (Ring.Finv s4))) &&
    (* tHat o cHat^e = PC h hs s' sHat *) 
    Gbool_eq ((Vnth tHat index0) o (Vnth cHat index0) ^ e)
      (PC g (Vhead hs) (Vnth s' index0) (Vnth sHat index0)) &&
    (* tHat_i o cHat_i^e = PC cHat_{i-1} s' sHat *) 
    VG_eq (Vmap2 (fun tHat cHat => tHat o cHat ^ e) (Vtail tHat) (Vtail cHat)) 
    (Vmap2 (fun x y => x y)(Vmap2 (fun h1 u r => PC g h1 u r) (Vremove_last cHat) (Vtail s')) (Vtail sHat)).

  Definition X := F.

  Definition simMap (s : St)(w : W)(c :F)(x : X)(r  :  W) 
    : W:=

    let u' := w.1.1.1 in
    let rTil := w.1.1.2 in
    let rStar := w.1.2 in
    let rHat := w.2 in

    let w' := r.1.1.1 in 
    let w3 := r.1.1.2 in
    let w4 := r.1.2 in 
    let wHat := r.2 in

    let s3  := w3+rTil*c in
    let s4  := Ring.Fadd w4 (MVS.op3 rStar c) in


    let sHat := VF_add wHat (VF_scale rHat c) in
    let s' := VF_add w' (VF_scale u' c) in
    
    (s', s3, s4, sHat).

  Definition simMapInv (s : St)(w : W)(c :F)(x : X)
    (r  :  W) : W:=

    let u' := w.1.1.1 in
    let rTil := w.1.1.2 in
    let rStar := w.1.2 in
    let rHat := w.2 in

    let w' := r.1.1.1 in 
    let w3 := r.1.1.2 in
    let w4 := r.1.2 in 
    let wHat := r.2 in

    let s3  := w3-rTil*c in
    let s4  := Ring.Fadd w4 (Ring.Finv (MVS.op3 rStar c)) in


    let sHat := VF_sub wHat (VF_scale rHat c) in
    let s' := VF_sub w' (VF_scale u' c) in
    
    (s', s3, s4, sHat).

  Definition simulator (s :St)(z : W)(e : F) :
    (St*C*F*W) :=
    let parm := s.1 in
    let pk := parm.1.1.1 in
    let g := parm.1.1.2 in
    let hs := parm.1.2 in
    let e' := parm.2 in

    let stat := s.2 in
    let a := stat.1.1 in
    let b := stat.1.2 in
    let cHat := stat.2 in

    let s3  := z.1.1.2 in 
    let s4  := z.1.2 in 
    let sHat := z.2 in 
    let s' := z.1.1.1 in

    let t3 := EPC g hs s' s3 o - a^e in 
    let t4 := G1.Gdot (G1.Gdot (MoC.VG_prod (MoC.VG_Pexp e' s')) (enc.enc pk enc.Mzero (Ring.Finv s4))) 
      (G1.Ginv (VS1.op b e)) in
    let tHat1 := PC g (Vhead hs) (Vnth s' index0) (Vnth sHat index0)
       o - Vnth (VG_Sexp cHat e) index0 in
    let tHat := Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) 
    (Vmap2 (fun cHat1 s' sHat cHat2 => PC g cHat1 s' sHat o - cHat2 ^ e) (Vremove_last cHat)
      (Vtail s')) (Vtail sHat)) (Vtail cHat) in 

    (* let tHat := PC h (Vnth cHat index1) (Vnth s' index2) (Vnth sHat index2) o \ Vnth (V2G_Sexp cHat e) index2 in *)

    (s, (t3, t4, Vapp [tHat1] tHat), e, z).

  Definition simMapHelp (st : St)(x : X) : Prop := True.

  Definition M := 2.

  Definition extractor (s : vector W M)(c : vector F M) : W :=
    
    let s3_1  := (Vhead s).1.1.2 in 
    let s4_1  := (Vhead s).1.2 in 
    let sHat_1 := (Vhead s).2 in 
    let s'_1 := (Vhead s).1.1.1 in

    let s3_2  := (Vhead (Vtail s)).1.1.2 in 
    let s4_2  := (Vhead (Vtail s)).1.2 in 
    let sHat_2 := (Vhead (Vtail s)).2 in 
    let s'_2 := (Vhead (Vtail s)).1.1.1 in

    let c1 := (Vhead c) in
    let c2 := (Vhead (Vtail c)) in

    let w' := VF_scale (VF_add s'_1  (VF_neg s'_2)) (FmulInv (c1 - c2)) in
    let w3 := (s3_1 - s3_2) / (c1 - c2) in

    let w4 := (MVS.op3 (Ring.Fadd s4_1 (Ring.Finv s4_2)) (FmulInv (c1 - c2))) in
    let wHat := VF_scale (VF_add sHat_1 (VF_neg sHat_2)) (FmulInv (c1 - c2)) in


    (* (F*(VF (N)))*F*F*(F*(VF (N)))*)
    (w', w3, w4, wHat).

  Definition disjoint (c1 c2 : F) :=
    negb (Fbool_eq c1 c2).

  Lemma disjointSim : forall a b, disjoint a b = disjoint b a.
  Proof.
    pose Chal.module_abegrp. intros. unfold disjoint. rewrite bool_eq_sym. trivial.
  Qed.

  Definition fail_event (St : St)(c : C)(t : (vector Chal.G M)) : Prop := False.

  Lemma pres_p0 : forall (s : St)(r : R)(w : W), (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. trivial.
  Qed.

  Lemma pres_p1 : forall (sce : St*C*Chal.G)(r : R)(w : W), 
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Proof.
    intros. trivial.
  Qed.

  Lemma pres_sim : forall (s: St)(t : TE)(e : Chal.G),
      s = (simulator s t e).1.1.1.
  Proof.
    intros. trivial.
  Qed.

  Lemma chal_sim : forall (s: St)(t : TE)(e : Chal.G),
    e = (simulator s t e).1.2.  
  Proof.
    intros. trivial.
  Qed.

  (** Properties *)
  Lemma correctness : forall (s :St)(w:W)(r:R)(c: Chal.G),
    Rel s w ->
    V1 (P1 ((P0 s r w), c) r w) = true.
  Proof.
    pose G1.module_abegrp. pose G2.module_abegrp. pose enc.M_abgrp.
    intros.  unfold Rel, V1, P1, P0 in *. do 4 rewrite Prod_left_replace.
    do 6 rewrite Prod_right_replace. apply andb_true_iff in H. destruct H.
    apply andb_true_iff in H. destruct H. apply andb_true_iff in H. destruct H.
    apply andb_true_iff. split. apply andb_true_iff. split. apply andb_true_iff. split.
    apply bool_eq_corr. apply bool_eq_corr in H. rewrite H. simpl.
    rewrite <- EPCExp. rewrite EPCMult.
    apply EPC_m_eq. unfold VF_add. unfold FMatrix.VA.vector_plus.
    unfold FSemiRingT.Aplus. apply Veq_nth. intros.
    induction i. cbn. trivial. cbn. trivial.
    (* part 2 *)  
    apply bool_eq_corr in H2. apply bool_eq_corr.
    rewrite H2. rewrite VS1.mod_dist_Gdot. rewrite enc.encOfOnePrec.
    replace (enc.Mzero) with (enc.Mop enc.Mzero enc.Mzero). 
    rewrite ALR.inv_dis. rewrite <- enc.homomorphism. replace (enc.Mop enc.Mzero enc.Mzero) 
    with enc.Mzero. rewrite comm. do 2 rewrite dot_assoc.
    apply right_cancel. rewrite comm. rewrite dot_assoc.
    rewrite MVS.RopInvDis.
    apply right_cancel. rewrite MoC.Sexp_dist. rewrite comm. 
    rewrite MoC.VF_add_product. trivial.
     rewrite one_right. trivial.
     rewrite one_right. trivial.
    (* part 3 *)
    apply bool_eq_corr. apply bool_eq_corr in H1. rewrite H1.
    rewrite Vnth_app. destruct (le_gt_dec 1 0). lia. rewrite Vnth_cons.
    destruct (NatUtil.lt_ge_dec 0 0). lia. rewrite PCExp. rewrite PCMult.
    do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map. apply f_equal2;
    unfold FSemiRingT.Aplus; trivial.
    
    (* part 4 *)
    apply VGeq. apply bool_eq_corr in H1. apply VGeq in H0.
    apply Veq_nth. intros. do 7 rewrite Vnth_map2.  do 5 rewrite Vnth_tail.
    do 2 rewrite Vnth_map. unfold FSemiRingT.Aplus. 
    rewrite <- PCMult. apply left_cancel. rewrite <- Vnth_tail. rewrite H0.
    rewrite <- PCExp. do 2 rewrite Vnth_map2. do 2 rewrite <- Vnth_tail.
    trivial.
  Qed.

  Definition allDifferent (e : vector Chal.G M) := PairwisePredicate disjoint e.

  Lemma special_soundness : forall (s : St)(c : C)(e : vector Chal.G M)(t : vector T M),
    (* Forall e it is disjoint from all e *)
    allDifferent e ->
    bVforall2 (fun e1 t1 => V1 (s, c, e1, t1)) e t -> 
    Rel s (extractor t e) = true \/ fail_event s c e.
  Proof.
    pose G1.module_abegrp. pose G2.module_abegrp. pose enc.M_abgrp. pose Chal.module_abegrp.
    intros. unfold disjoint, V1, Rel, extractor in *. left. 
    do 3 rewrite Prod_left_replace. do 3 rewrite Prod_right_replace.
    rewrite (VSn_eq e) in H0. rewrite (VSn_eq t) in H0. simpl in H0.
    apply andb_true_iff in H0. destruct H0. apply bVforall2_elim_head in H1.
    apply andb_true_iff in H0. destruct H0. apply andb_true_iff in H0. destruct H0.
    apply andb_true_iff in H0. destruct H0. apply andb_true_iff in H1. destruct H1.
    apply andb_true_iff in H1. destruct H1. apply andb_true_iff in H1. destruct H1.
    apply bool_eq_corr in H0. apply bool_eq_corr in H4. apply bool_eq_corr in H3.
    apply VGeq in H2. apply bool_eq_corr in H7. apply bool_eq_corr in H1.
    apply VGeq in H5. apply bool_eq_corr in H6. assert (Vhead e - Vhead (Vtail e) <> 0).
    rewrite (VSn_eq e) in H. simpl in H. apply andb_true_iff in H.
    apply (zero2 (dot:=Fadd)(Aone:=Fzero)(bool_equal:=Fbool_eq)(Ainv:=Finv)).
    destruct H. apply  bVforall_elim_head in H. unfold disjoint in H.
    apply negb_true_iff in H. apply F_bool_neq_corr in H. trivial.
    (* Setup complete *)
    apply andb_true_iff. split.
     apply andb_true_iff. split. apply andb_true_iff. split. 
    (* part 1 *)
    + apply bool_eq_corr. rewrite EPCExp. rewrite <- EPCMult.
    rewrite <- EPCneg. simpl. symmetry in H0. rewrite H0. 
    symmetry in H1. rewrite H1. apply ALVS2.ExtractorHelper. trivial.
    (* part 2 *) 
    + apply bool_eq_corr. rewrite <- MoC.Sexp_dist.
    rewrite <- MoC.VF_add_product. rewrite <- MVS.RopInvDis.
    rewrite <- enc.encOfOnePrec. rewrite <- VS1.mod_dist_Gdot.
    assert (enc.Mzero = (enc.Mop enc.Mzero enc.Mzero)). 
    rewrite one_right. intuition.
    rewrite H9. rewrite ALR.inv_dis. rewrite <- enc.homomorphism. 
    assert (forall a b c d, G1.Gdot (G1.Gdot a b) (G1.Gdot c d) = 
      G1.Gdot (G1.Gdot a c) (G1.Gdot b d)). intros. apply commHack.
    rewrite H10. rewrite MoC.VF_neg_inv. rewrite EncInv. 
    assert (forall a b : G1.G, G1.Gdot (G1.Ginv a) (G1.Ginv b) = 
        G1.Ginv (G1.Gdot a b)). apply inv_dist.
    rewrite H11. rewrite <- MoC.VG_Pexp_Vcons in H7. 
    do 2 rewrite <- VSn_eq in H7.  symmetry in H7. rewrite H7.
    rewrite <- MoC.VG_Pexp_Vcons in H4. 
    do 2 rewrite <- VSn_eq in H4.  symmetry in H4. rewrite H4.
    rewrite <- (inv_dist (H:= a)). rewrite H10. rewrite <- inv_left.
    rewrite one_left. rewrite ALVS1.neg_eq. rewrite <- VS1.mod_dist_Fadd.
    rewrite <- VS1.mod_dist_Fmul. symmetry. rewrite <- VS1.mod_id.
    apply f_equal. unfold Chal.G in *. field; auto.
    (* part 3 *)
    + apply bool_eq_corr. do 2 rewrite Vnth_map. rewrite <- PCExp. 
    do 2 rewrite Vnth_map2. rewrite <- PCMult. do 2 rewrite Vnth_map.
    rewrite <- PCneg. symmetry in H3. rewrite H3.  symmetry in H6. rewrite H6.   
    apply ALVS2.ExtractorHelper. trivial.
    (* part 4 *)
    + apply VGeq. apply Veq_nth. intros. do 2 rewrite Vnth_map2. 
    do 2 rewrite Vnth_map. rewrite <- PCExp. do 2 rewrite Vnth_map2.  rewrite <- PCMult. 
    do 5 rewrite Vnth_tail. do 2 rewrite Vnth_map. rewrite <- PCneg.
    apply (Veq_nth4 ip) in H5. apply (Veq_nth4 ip) in H2. do 3 rewrite Vnth_map2 in H5.
    symmetry in H5. do 2 rewrite Vnth_tail in H5. rewrite H5.
    do 3 rewrite Vnth_map2 in H2. symmetry in H2. do 2 rewrite Vnth_tail in H2.
    rewrite H2. do 2 rewrite Vnth_tail. apply ALVS2.ExtractorHelper. trivial.
  Qed. 

  Lemma honest_verifier_ZK :
    forall (s : St)(w : W)(e : Chal.G)(x : X)(r : R)(t : TE),
      simMapHelp s x ->
      Rel s w ->
      ((P1((P0 s r w), e) r w) =
      simulator s (simMap s w e x r) e) /\ 
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.
  Proof.
    pose G1.module_abegrp. pose G2.module_abegrp. pose enc.M_abgrp. pose Chal.module_abegrp.
     pose vs_field. intros. unfold Rel, P1, P0, simulator, simMap, simMapInv in *. 
    apply andb_true_iff in H0.
    destruct H0. apply andb_true_iff in H0. destruct H0. 
    apply andb_true_iff in H0. destruct H0. apply bool_eq_corr in H0. 
    apply VGeq in H1. apply bool_eq_corr in H2. apply bool_eq_corr in H3. split.
    simpl in *. 
    (* Part 1 - Proving transcripts are equal *)  
    + apply injective_projections. simpl.
    apply injective_projections. simpl. apply injective_projections. simpl.
    (* part 1.1 - Proving s is eqal.*)
    trivial.
    (* part 1.2 - Proving c is equal. (G*V2G*(VG (1+N))) *)
    ++ simpl. apply injective_projections. simpl. apply injective_projections. simpl.
    (* part 1.2.1 *)
    +++ rewrite H0. rewrite <- EPCExp. rewrite EPCneg. rewrite EPCMult.
    apply f_equal2. apply Veq_nth. intros. rewrite Vnth_map2. unfold VF_add,
    FSemiRingT.Aplus, FMatrix.VA.vector_plus.
    rewrite <- Vcons_map2. do 2 rewrite <- VSn_eq. rewrite Vnth_map2. 
    do 3 rewrite Vnth_map. unfold FSemiRingT.Aplus. destruct f.
    destruct F_R. rewrite <- Radd_assoc. rewrite Ropp_def. rewrite Radd_comm.
    rewrite Radd_0_l. trivial. field; auto.
    (* part 1.2.2 *)
    +++ do 2 rewrite Prod_right_replace. rewrite H3. rewrite VS1.mod_dist_Gdot.
    rewrite <- (inv_dist (H:=a)). unfold abegop. rewrite <- (commHack (H:= a)).
    unfold MoC.VG_Pexp. do 3 rewrite <- Vcons_map2. do 3 rewrite <- VSn_eq.
    unfold VF_add, FMatrix.VA.vector_plus. rewrite <- Vcons_map2.
    do 2 rewrite <- VSn_eq. apply f_equal2. rewrite ALVS1.neg_eq.
    rewrite MoC.Sexp_dist0. unfold MoC.VG_prod, abegop. rewrite MoC.Vfold_Gdot_dob.
    apply f_equal. apply Veq_nth. intros. do 4 rewrite Vnth_map2.
    do 2 rewrite Vnth_map. rewrite Vnth_map2. rewrite <- VS1.mod_dist_Fmul.
    rewrite <- VS1.mod_dist_Fadd. apply f_equal. destruct f, F_R.
    rewrite <- Radd_assoc. rewrite Rmul_comm. assert (Finv e * Vnth w.1.1.1 ip =
    Finv (e * Vnth w.1.1.1 ip)). field; auto. rewrite H4. rewrite Ropp_def.
    rewrite Radd_comm. rewrite Radd_0_l. trivial. rewrite inv_dist3.
    rewrite enc.encOfOnePrec. unfold abegop. rewrite <- EncInv.
    rewrite enc.homomorphism. rewrite one_right. rewrite <- EncInv. apply f_equal.
    pose Ring.module_ring. rewrite MVS.RopInvDis.  Add Ring r4 : Ring.module_ring.
    ring; auto.
    (* part 1.2.3 *)
    +++ simpl. apply Vcons_eq_intro. rewrite <- PCMult.
    do 3 rewrite <- Vnth0Head in H2. do 2 rewrite Vhead_map.
    rewrite <- PCExp. rewrite <- H2. do 3 rewrite <- Vnth0Head.
    rewrite Vhead_map. rewrite <- dot_assoc. rewrite <- inv_right.
    rewrite one_right. trivial.
    apply Veq_nth. intros. do 5 rewrite Vnth_map2. rewrite H1.
    do 2 rewrite Vnth_map2. rewrite PCExp. rewrite PCneg. rewrite PCMult.
    apply f_equal2. rewrite Vnth_map2. do 3 rewrite Vnth_tail. rewrite Vnth_map.
    unfold FSemiRingT.Aplus. field; auto. rewrite Vnth_map2. do 3 rewrite Vnth_tail. 
    rewrite Vnth_map. unfold FSemiRingT.Aplus. field; auto. 

    (* part 1.3.1 proving challenges are equal *)
    ++ simpl. trivial.

    (* part 1.4 proving responses are equal *)
    ++ apply injective_projections. simpl. apply injective_projections. simpl. 
    apply injective_projections. simpl.
    (* part 1.4.1 *)
    trivial.
    (* part 1.4.2 *)
    simpl. trivial.
    (* part 1.4.3 *)
    simpl. trivial.
    (* part 1.4.4 *)
    simpl. trivial.

    (* part 2 - bijection. *)
    +  do 6 rewrite Prod_left_replace. do 6 rewrite Prod_right_replace. split. 
    ++ apply injective_projections; simpl; auto. unfold VF_add, FSemiRingT.Aplus,
    FMatrix.VA.vector_plus. rewrite <- Vcons_map2. do 2 rewrite <- VSn_eq.
    apply injective_projections. apply injective_projections. 
    do 2 rewrite Prod_left_replace. rewrite VF_sub_corr. rewrite VF_add_ass. 
    rewrite VF_neg_corr. rewrite VF_add_zero. trivial. rewrite Prod_right_replace.
    field; auto. rewrite Prod_right_replace. ring; auto. rewrite VF_sub_corr. 
    rewrite VF_add_ass. rewrite VF_neg_corr. rewrite VF_add_zero. trivial.
    ++ apply injective_projections; simpl; auto. unfold VF_add, FSemiRingT.Aplus,
    FMatrix.VA.vector_plus. do 2 rewrite <- Vcons_map2. do 3 rewrite <- VSn_eq.
    apply injective_projections. apply injective_projections. 
    do 2 rewrite Prod_left_replace. pose VF_add_ass. unfold VF_add,FMatrix.VA.vector_plus in e0. 
    rewrite e0. pose VF_neg_corr. unfold VF_add,FMatrix.VA.vector_plus in e1. 
    pose VF_comm. unfold VF_add,FMatrix.VA.vector_plus in e2. rewrite (e2 (Nat.add 1 N) (VF_neg (VF_scale w.1.1.1 e))).
    rewrite e1. pose VF_add_zero. unfold VF_add,FMatrix.VA.vector_plus in e3.
    rewrite e3.  trivial. 
    rewrite Prod_right_replace.
    field; auto. rewrite Prod_right_replace. ring; auto. unfold VF_add, FMatrix.VA.vector_plus.
    rewrite <- Vcons_map2. rewrite <- VSn_eq. rewrite <- Vcons_map2.
    do 2 rewrite <- VSn_eq. pose VF_add_ass. unfold VF_add,FMatrix.VA.vector_plus in e0. 
    rewrite e0. pose VF_neg_corr. unfold VF_add,FMatrix.VA.vector_plus in e1. 
    pose VF_comm. unfold VF_add,FMatrix.VA.vector_plus in e2. rewrite (e2 (Nat.add 1 N) (VF_neg (VF_scale w.2 e))).
    rewrite e1. pose VF_add_zero. unfold VF_add,FMatrix.VA.vector_plus in e3.
    rewrite e3.  trivial. 
  Qed.
  
  Lemma simulator_correct : forall (s : St)(t : TE)(e : Chal.G),
    V1(simulator s t e) = true.
  Proof.
    pose G1.module_abegrp. pose G2.module_abegrp. pose enc.M_abgrp. pose Chal.module_abegrp.
    intros. unfold V1, simulator. apply andb_true_iff. split.
    apply andb_true_iff. split. apply andb_true_iff. split.
    + simpl. apply bool_eq_corr. rewrite <- dot_assoc. rewrite <- inv_left.
    rewrite one_right. trivial.
    + simpl. apply bool_eq_corr. rewrite <- dot_assoc. rewrite <- inv_left.
    rewrite one_right. trivial.
    + simpl. apply bool_eq_corr. rewrite <- dot_assoc. rewrite Vnth_map.
    rewrite <- inv_left. rewrite one_right. trivial.
    + simpl. apply VGeq. apply Veq_nth. intros. do 6 rewrite Vnth_map2.
    rewrite <- dot_assoc. rewrite <- inv_left. 
    rewrite one_right. trivial.
  Qed.
  
End wikSigma. 
