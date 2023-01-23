Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import ArithRing.
From Groups Require Import groups module vectorspace dualvectorspaces modulevectorspace.
Require Import sigmaprotocol.
Require Import Coq.Lists.List.
Require Import Ring.
Require Import Field. 
Require Import Field_theory.
Require Import cryptoprim.
Require Import VectorUtil.
From CoLoR Require Import VecUtil VecArith.
Require Import matrices matricesF.

Set implicit arguments.

(* Module includes various DLog Sigmas and other basic sigma protocols *)
Module BasicSigmas (Group : GroupSig)(Field : FieldSig)(VS : VectorSpaceSig Group Field).
  Import VS.
  Module HardProb := HardProblems Group Field VS.
  Import HardProb.
  Module Mo := MatricesFIns Field.
  Module PC := BasicComScheme Group Field VS Mo.
  Import PC.
  Module AddVSLemmas := VectorSpaceAddationalLemmas Group Field VS.
  Import AddVSLemmas.

  (** Begin Sigma Proper *)
  (* We pass why to allow branching in disjunction *)
  Definition valid_P0 (ggtox : G*G)(r : F)(w : F) : (G*G*G) :=
    (* (g, h) = ggtox, g^w = h *)
    let g := ggtox.1 in 
    (ggtox, g^r).

  Definition valid_V0 (ggtoxgtor: G*G*G) (c: F): (G*G*G*F)
    := (ggtoxgtor, c).

  Definition valid_P1 (ggtoxgtorc: G*G*G*F) (r x: F) : G*G*G*F*F :=
    let c    :=  snd (ggtoxgtorc) in
    let s:= (r + c*x) in (ggtoxgtorc, s).

  Definition valid_V1 (ggtoxgtorcs : G*G*G*F*F) :=

    let g    :=  fst (fst (fst (fst ggtoxgtorcs))) in
    let gtox :=  snd (fst (fst (fst ggtoxgtorcs))) in
    let gtor :=  snd (fst (fst ggtoxgtorcs)) in
    let c    :=  snd (fst ggtoxgtorcs) in
    let s    :=  snd ggtoxgtorcs in 
    Gbool_eq (g^s) ((gtox^c) o gtor).

  Definition simulator_mapper (s : G*G)(x c r :F):=
    (r+x*c).

  Definition simulator_mapper_inv (s : G*G)(x c t :F):=
    (t-x*c).

  Definition simulator (ggtox :G*G)(z e : F) :=
  let g := fst ggtox in
  let gtox := snd ggtox in
    (ggtox, g^(z) o - gtox^e, e, z).

  Definition extractor (s1 s2 c1 c2 : F) :=
    (s1 - s2) / (c1 - c2).

  Definition disjoint (c1 c2 : F) :=
    negb (Fbool_eq c1 c2).

  Definition dLogForm : Sigma.form F := Sigma.mkForm dLog
    Fadd Fzero Finv Fbool_eq disjoint valid_P0 valid_V0 valid_P1 valid_V1
   simulator simulator_mapper simulator_mapper_inv extractor.

  Theorem dLogSigma
    :CompSigmaProtocol dLogForm. 
  Proof.
    pose vs_field. pose module_abegrp.
    assert (AbeGroup F Fadd 0 Fbool_eq (fun a b => negb (Fbool_eq a b)) Finv).
      apply (field_additive_abegrp (F)(Fadd)(Fzero)
    (Fbool_eq) (Fsub)(Finv)(Fmul) (Fone)(FmulInv)(Fdiv)). apply f. 
    apply F_bool_eq_corr. apply F_bool_eq_sym. apply F_bool_neq_corr.
     destruct f. destruct F_R. 
     constructor. constructor. constructor.  unfold dLogForm. cbn in *. apply H.
    + intros. trivial.
  (* Comp and prev prop *)
    + intros. unfold valid_P0. trivial.
    + intros. unfold valid_V0.  trivial.
    + intros. unfold valid_P1. trivial.
    + intros. unfold valid_V0. trivial.
    + intros. unfold valid_P1. trivial. 
    + intros. unfold simulator. trivial.
    + intros. unfold dLogForm. simpl. trivial.

  (* Correctness *)
  + intros. cbn in *.
    unfold valid_V1, valid_P1, valid_V0, valid_P0.
    cbn.  unfold dLog in H0. assert (s.2 = (s.1 ^ w)). rewrite <- bool_eq_corr.
    apply H0. rewrite H1.
    rewrite <- mod_dist_Fmul, <- mod_dist_Fadd, comm, bool_eq_corr. 
    trivial.
   
  (* Special soundness *)
  + cbn. intros.  unfold extractor. unfold dLog. rewrite bool_eq_corr. 
    rewrite Radd_comm. rewrite mod_dist_Fmul.  assert ((e1 - e2) <> 0). 
    apply (zero2 (dot:=Fadd)(Aone:=Fzero)(bool_equal:=Fbool_eq)(Ainv:=Finv)).  
    rewrite <- bool_neq_corr. cbn in H0. unfold dLogForm in H0. simpl in H0. unfold disjoint in H0. 
    apply negb_false_iff in H0. rewrite negb_involutive in H0. apply H0. cbn in *.
    apply op_cancel with (x:= (e1 - e2)).  apply H3.
    do 2 rewrite <- mod_dist_Fmul. rewrite Rmul_comm.
    rewrite Rmul_assoc. rewrite Finv_l. apply H3. rewrite Rmul_1_l. 
    (** We have now proved g^(s1 - s2) = gtox ^ (c1 - c2) *)
    rewrite mod_dist_Fadd. rewrite <- neg_eq. unfold dLogForm in H1. unfold dLogForm in H2.
    unfold valid_V1 in H1.  unfold valid_V1 in H2. simpl in *.  rewrite mod_dist_Fadd.
    apply bool_eq_corr in H1. apply bool_eq_corr in H2. symmetry. rewrite <- neg_eq. symmetry.
    rewrite H1. rewrite H2.  remember (s.2^e1) as d. remember (s.2^e2) as e.
    symmetry. rewrite comm. rewrite <- dot_assoc. apply left_cancel.
    assert (-(e o c) = (-e o -c)). symmetry. apply inv_dist. rewrite H4. rewrite comm.
    rewrite <- dot_assoc. rewrite <- inv_left. rewrite one_right. rewrite <- one_right.
    symmetry. rewrite <- one_right. apply left_cancel. intuition. (* Again, I am surprised that auto,
    trivial is not working. This project is literally testing the Coq internals *)

  (* honest verifier ZK *)
    + intros. cbn in *. unfold dLogForm. simpl.
    unfold simulator_mapper, simulator_mapper_inv,  simulator. unfold valid_V1 in *. 
    unfold valid_P1 in *. unfold valid_V0 in *. unfold valid_P0 in *.
    simpl in *. split. intros. apply bool_eq_corr in H0. rewrite Rmul_comm in H0. 
    rewrite H0.  apply injective_projections; auto. apply injective_projections; 
    auto. apply injective_projections; auto. simpl. rewrite comm. rewrite dot_assoc.
    rewrite <- inv_left. rewrite one_left. trivial.  rewrite Rmul_comm. trivial.
    split. ring; auto. ring; auto.
    
    + intros. cbn in *. unfold dLogForm. simpl. unfold valid_V1. cbn. unfold simulator. simpl. 
    replace (s.1 ^ t o - s.2 ^ e) with (- s.2 ^ e o s.1 ^ t) by apply comm.
    rewrite dot_assoc. rewrite <- inv_right. rewrite one_left. 
    rewrite bool_eq_corr. trivial.

    + intros. unfold valid_P1. trivial.
    
    + intros. unfold simulator_mapper. trivial.
  Qed. 

  (* We have now defined and proved the sigma protocol for discrete log *)

  (*We now define an empty sigma form though with real types for some reason
    we need this to define the later generaters nicely*)
  Definition emptyRel (s : G)(w : F): bool := 
    true.

  Definition empty_P0 (g : G)(r : F)(w : F) : (G*G) :=
    (g,g).
    
  Definition empty_V0 (g: G*G) (c: F): (G*G*F):=
     (g, c).

  Definition empty_P1 (g: G*G*F) (r x: F) : G*G*F*F :=
    (g, g.2).

  Definition empty_V1 (g : G*G*F*F) :=
    true.

  Definition empty_simulator_mapper (s : G)(x c r:F):=
    (r).

  Definition empty_simulator_mapper_inv (s : G)(x c t :F):=
    (t).

  Definition empty_simulator (g :G)(z e : F) :=
    (g, g, e, e).

  Definition empty_mapper (s1 s2 c1 c2 : F) :=
    (s1 - s2) / (c1 - c2).

  Definition emptyForm : Sigma.form F := Sigma.mkForm emptyRel 
    Fadd Fzero Finv Fbool_eq disjoint empty_P0 empty_V0 empty_P1 empty_V1
   empty_simulator empty_simulator_mapper empty_simulator_mapper_inv empty_mapper.

  Theorem emptySigma
    :CompSigmaProtocol emptyForm.
  Proof.
    pose vs_field. pose module_abegrp.
    assert (AbeGroup F Fadd 0 Fbool_eq (fun a b => negb (Fbool_eq a b)) Finv). 
    apply (field_additive_abegrp (F)(Fadd)(Fzero)
    (Fbool_eq) (Fsub)(Finv)(Fmul) (Fone)(FmulInv)(Fdiv)). apply f. 
    apply F_bool_eq_corr. apply F_bool_eq_sym. apply F_bool_neq_corr.
    destruct f. destruct F_R.  
     constructor. constructor. constructor.  unfold emptyForm. cbn in *. apply H. trivial.
    (*Begining main lemmas *)
    + intros. trivial.
    + intros. trivial.
    + intros. trivial.
    + intros. trivial.
    + intros. trivial.
    + intros. trivial.
    + intros. trivial.
    + intros. trivial.
    + intros. trivial.  
    + intros. unfold emptyForm. cbn. split.
    ++ intros. trivial.
    ++ intros. split; auto. 
    + intros. trivial. 
    + intros. trivial.
    + intros. trivial.
  Qed. 

  Definition dLog2 (s :G*G*G)(w : F*F) := 
    let g     := s.1.1 in
    let h     := s.1.2 in
    let gtox  := s.2 in 
    Gbool_eq gtox (PC g h w.1 w.2).


  (** Begin Sigma Proper *)
  (* We pass why to allow branching in disjunction *)
  Definition dLog2_P0 (ggtox : G*G*G)(r : F*F)(w : F*F) : (G*G*G*G) :=
    let g := ggtox.1.1 in 
    let h := ggtox.1.2 in 
    (ggtox, PC g h r.1 r.2).

  Definition dLog2_V0 (ggtoxgtor: G*G*G*G) (c: F): (G*G*G*G*F)
    := (ggtoxgtor, c).

  Definition dLog2_P1 (ggtoxgtorc: G*G*G*G*F) (r x: F*F) : G*G*G*G*F*(F*F) :=
    let c    :=  snd (ggtoxgtorc) in
    let s1  := (r.1 + x.1*c) in 
    let s2  := (r.2 + x.2*c) in 
    (ggtoxgtorc, (s1, s2)).

  Definition dLog2_V1 (ggtoxgtorcs :  G*G*G*G*F*(F*F)) :=
    let g    :=  ggtoxgtorcs.1.1.1.1.1 in
    let h    :=  ggtoxgtorcs.1.1.1.1.2 in
    let gtox :=  ggtoxgtorcs.1.1.1.2 in
    let gtor :=  ggtoxgtorcs.1.1.2 in
    let c    :=  ggtoxgtorcs.1.2 in
    let s1   :=  ggtoxgtorcs.2.1 in
    let s2   :=  ggtoxgtorcs.2.2 in
    Gbool_eq (PC g h s1 s2) ((gtox^c) o gtor).

  Definition dLog2_simulator_mapper (s : G*G*G)(x :F*F)(c :F)(r : F*F):=
    ((r.1+x.1*c),(r.2+x.2*c)).

  Definition dLog2_simulator_mapper_inv (s : G*G*G)(x :F*F)(c :F)(t : F*F):=
    ((t.1-x.1*c),(t.2-x.2*c)).

  Definition dLog2_simulator (ggtox :G*G*G)(z : F*F)(e : F) :=
  let g :=  ggtox.1.1 in
  let h :=  ggtox.1.2 in
  let gtox := snd ggtox in
    (ggtox, PC g h z.1 z.2 o - gtox^e, e, z).

  Definition dLog2_extractor (s1 s2 :F*F)(c1 c2 : F) :=
    ((s1.1 - s2.1) / (c1 - c2),(s1.2 - s2.2) / (c1 - c2)).

  Definition dLog2Form : Sigma.form F := Sigma.mkForm dLog2
    Fadd Fzero Finv Fbool_eq disjoint dLog2_P0 dLog2_V0 dLog2_P1
    dLog2_V1 dLog2_simulator dLog2_simulator_mapper dLog2_simulator_mapper_inv
    dLog2_extractor.

  Theorem dLogSigma2
    :CompSigmaProtocol dLog2Form. 
  Proof.
    pose vs_field. pose module_abegrp. simpl in *.
    assert (AbeGroup F Fadd 0 Fbool_eq (fun a b => negb (Fbool_eq a b)) Finv).  
    apply (field_additive_abegrp (F)(Fadd)(Fzero)
    (Fbool_eq) (Fsub)(Finv)(Fmul) (Fone)(FmulInv)(Fdiv)). apply f.
    apply F_bool_eq_corr. apply F_bool_eq_sym. apply F_bool_neq_corr.
    destruct f. destruct F_R.   
     constructor. constructor. constructor. cbn in *. apply H.
    + intros. trivial.
  (* Comp and prev prop *)
    + intros. unfold valid_P0. trivial.
    + intros. unfold valid_V0.  trivial.
    + intros. unfold valid_P1. trivial.
    + intros. unfold valid_V0. trivial.
    + intros. unfold valid_P1. trivial. 
    + intros. unfold simulator. trivial.
    + intros. unfold dLogForm. simpl. trivial.

  (* Correctness *)
  + intros. unfold dLog2Form in *. simpl in *.
    unfold dLog2_V1, dLog2_P1, dLog2_V0, dLog2_P0. simpl.
    unfold dLog2 in H0. assert (s.2 = PC s.1.1 s.1.2 w.1 w.2). 
    rewrite <- bool_eq_corr. apply H0. rewrite H1.
    rewrite bool_eq_corr. rewrite PCExp. symmetry. rewrite comm. 
    rewrite PCMult. intuition.
    
  (* Special soundness *)
  + intros.
    unfold dLog2_V1 in *. simpl in *. unfold dLog2_extractor.
    unfold dLog2. simpl. rewrite bool_eq_corr. apply bool_eq_corr in H1.
    apply bool_eq_corr in H2. rewrite <- PCExp. rewrite <- PCMult.
    rewrite <- PCneg. rewrite H1. rewrite H2. apply ExtractorHelper2.
    unfold disjoint in H0. apply negb_false_iff in H0. rewrite negb_involutive in H0.
    apply F_bool_neq_corr in H0.  unfold not in *. intros. 
    apply shift in H3. rewrite H3 in H0. apply H0. trivial.

  (* honest verifier ZK *)
    + intros. cbn in *. unfold dLog2Form. simpl.
    split. unfold dLog2_simulator_mapper. unfold dLog2_simulator.
    unfold dLog2_P1. unfold dLog2_V0. unfold dLog2_P0.
    simpl. intros. unfold dLog2_V1 in H0. apply bool_eq_corr in H0.
    simpl in *. rewrite H0. symmetry. apply injective_projections; auto; simpl.
    apply injective_projections; auto; simpl. apply injective_projections; auto; simpl.
    rewrite comm. rewrite dot_assoc. rewrite <- inv_left. rewrite one_left. trivial.
    unfold dLog2_simulator_mapper_inv, dLog2_simulator_mapper. simpl. split.
    rewrite (surjective_pairing r). apply injective_projections; simpl; field; auto.
    rewrite (surjective_pairing t). apply injective_projections; simpl; field; auto.

    + intros. simpl in *. unfold dLog2_V1. simpl. rewrite bool_eq_corr.
     rewrite comm.  rewrite <- dot_assoc. rewrite <- inv_left.
      rewrite one_right. trivial.

    + intros. unfold valid_P1. trivial.
    
    + intros. unfold simulator_mapper. trivial.
  Qed.

End BasicSigmas.

(* Dirty hack to paramtise the next module *)
Module Type Nat.
  Parameter N : nat.
End Nat.

(* By convention we assume tVS contains the ciphertext space in VS1 and 
  the commitment space in VS2 *)
Module wikSigma (G G1 G2 : GroupSig)(Ring : RingSig)(Field : FieldSig)
    (VS2 : VectorSpaceSig G2 Field)
    (VS1 : VectorSpaceSig G1 Field)
    (MVS : VectorSpaceModuleSameGroup G1 Ring Field VS1)
    (enc : Mixable G G1 Ring Field VS1 MVS)(Hack : Nat).

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
  Definition S : Type := (enc.PK*G*G*(VG (1+N))*(vector G1.G (1+N)))*
        (G*G1.G*(VG (1+N))).
  (* u', rTil, rStar, rHat *)
  Definition W : Type := (VF (1+N)*F*Ring.F*(VF (1+N))).
  (* t3, t4, tHat i *)
  Definition C : Type := (G*G1.G*(VG (1+N))).

  Definition u'_Rel (s : S)(w : W) := 
    let parm := s.1 in
    let pk := parm.1.1.1.1 in
    let g := parm.1.1.1.2 in
    let h := parm.1.1.2 in
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
    Gbool_eq (Vnth cHat index0) (PC g h (Vnth u' index0) (Vnth rHat index0)) &&
    (* ^c_i = PC_(h,^c_(i-1))(u',^r)  *)  
    VG_eq (Vtail cHat) (Vmap2 (fun x y => x y)
       (Vmap2 (fun h1 u r => PC g h1 u r) (Vremove_last cHat) (Vtail u')) (Vtail rHat)). 
   
  (** Begin Sigma Proper *)
  (* We pass why to allow branching in disjunction *)
  Definition u'_P0 (s : S)(r w : W) :S*C :=
    let parm := s.1 in
    let pk := parm.1.1.1.1 in
    let g := parm.1.1.1.2 in
    let h := parm.1.1.2 in
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
    let tHat1 := PC g h (Vnth w' index0) (Vnth wHat index0) in
    let tHat2 := (Vmap2 (fun x y => x y)
       (Vmap2 (fun h1 u r => PC g h1 u r) (Vremove_last cHat) (Vtail w')) (Vtail wHat)) in

    (s, (t3, t4, Vapp [tHat1] tHat2)).

  Definition u'_V0 (ggtoxgtor: S*C) 
      (c: F): (S*C*F)
    := (ggtoxgtor, c).

  Definition u'_P1 (ggtoxgtorc: S*C*F) 
      (r w: W) : S*C*F*W :=
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

  Definition u'_V1 (transcript : S*C*F*W) :=
    
    let s := transcript.1.1.1 in
    let c := transcript.1.1.2 in
    let e := transcript.1.2 in
    let t := transcript.2 in

    let parm := s.1 in
    let pk := parm.1.1.1.1 in
    let g :=  parm.1.1.1.2 in
    let h := parm.1.1.2 in
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
      (PC g h (Vnth s' index0) (Vnth sHat index0)) &&
    (* tHat_i o cHat_i^e = PC cHat_{i-1} s' sHat *) 
    VG_eq (Vmap2 (fun tHat cHat => tHat o cHat ^ e) (Vtail tHat) (Vtail cHat)) 
    (Vmap2 (fun x y => x y)(Vmap2 (fun h1 u r => PC g h1 u r) (Vremove_last cHat) (Vtail s')) (Vtail sHat)).

  Definition u'_simulator_mapper (s : S)(w : W)(c :F)(r  :  W) 
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

  Definition u'_simulator_mapper_inv (s : S)(w : W)(c :F)
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

  Definition u'_simulator (s :S)(z : W)(e : F) :
    (S*C*F*W) :=
    let parm := s.1 in
    let pk := parm.1.1.1.1 in
    let g := parm.1.1.1.2 in
    let h := parm.1.1.2 in
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
    let tHat1 := PC g h(Vnth s' index0) (Vnth sHat index0)
       o - Vnth (VG_Sexp cHat e) index0 in
    let tHat := Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) 
    (Vmap2 (fun cHat1 s' sHat cHat2 => PC g cHat1 s' sHat o - cHat2 ^ e) (Vremove_last cHat)
      (Vtail s')) (Vtail sHat)) (Vtail cHat) in 

    (* let tHat := PC h (Vnth cHat index1) (Vnth s' index2) (Vnth sHat index2) o \ Vnth (V2G_Sexp cHat e) index2 in *)

    (s, (t3, t4, Vapp [tHat1] tHat), e, z).

  Definition u'_extractor (s1 s2 : W)(c1 c2 : F): W :=
    
    let s3_1  := s1.1.1.2 in 
    let s4_1  := s1.1.2 in 
    let sHat_1 := s1.2 in 
    let s'_1 := s1.1.1.1 in

    let s3_2  := s2.1.1.2 in 
    let s4_2  := s2.1.2 in 
    let sHat_2 := s2.2 in 
    let s'_2 := s2.1.1.1 in

    let w' := VF_scale (VF_add s'_1  (VF_neg s'_2)) (FmulInv (c1 - c2)) in
    let w3 := (s3_1 - s3_2) / (c1 - c2) in

    let w4 := (MVS.op3 (Ring.Fadd s4_1 (Ring.Finv s4_2)) (FmulInv (c1 - c2))) in
    let wHat := VF_scale (VF_add sHat_1 (VF_neg sHat_2)) (FmulInv (c1 - c2)) in


    (* (F*(VF (N)))*F*F*(F*(VF (N)))*)
    (w', w3, w4, wHat).

  Definition disjoint (c1 c2 : F) :=
    negb (Fbool_eq c1 c2).

  Definition u'Form : Sigma.form F := Sigma.mkForm u'_Rel 
    Fadd Fzero Finv Fbool_eq 
    disjoint u'_P0 u'_V0 u'_P1
    u'_V1 u'_simulator u'_simulator_mapper u'_simulator_mapper_inv u'_extractor.

  Theorem u'Sigma
    :CompSigmaProtocol u'Form. 
  Proof.
    pose G1.module_abegrp. pose G2.module_abegrp. pose enc.M_abgrp.
    unfold u'Form in *. 
    assert (AbeGroup F Fadd 0 Fbool_eq (fun a b => negb (Fbool_eq a b)) Finv).  
    apply (field_additive_abegrp (F)(Fadd)(Fzero)
    (Fbool_eq) (Fsub)(Finv)(Fmul) (Fone)(FmulInv)(Fdiv)). apply Field.vs_field.
    apply Field.F_bool_eq_corr. apply Field.F_bool_eq_sym. 
    apply Field.F_bool_neq_corr.
    destruct Field.vs_field. destruct F_R.   
     constructor. constructor. constructor. apply H. 
    + intros. trivial.
  (* Comp and prev prop *)
    + intros. trivial.
    + intros. trivial.
    + intros. trivial.
    + intros. trivial.
    + intros. trivial. 
    + intros. trivial.
    + intros. simpl. trivial.

    (* correctness *)
    + intros.  unfold u'_P0. unfold u'_V0. unfold u'_Rel in H0. unfold u'_P1.
    unfold u'_V1. simpl in *. apply andb_true_iff in H0. destruct H0.
    apply andb_true_iff in H0. destruct H0. apply andb_true_iff in H0. destruct H0.
    apply andb_true_iff. split. apply andb_true_iff. split. apply andb_true_iff. split.
    apply bool_eq_corr. apply bool_eq_corr in H0. rewrite H0. simpl.
    rewrite <- EPCExp. rewrite EPCMult.
    apply EPC_m_eq. unfold VF_add. unfold FMatrix.VA.vector_plus.
    unfold FSemiRingT.Aplus. apply Veq_nth. intros.
    induction i. cbn. trivial. cbn. trivial.
    (* part 2 *)  
    simpl in *. apply bool_eq_corr in H3. apply bool_eq_corr.
    rewrite H3. rewrite VS1.mod_dist_Gdot. rewrite enc.encOfOnePrec.
    replace (enc.Mzero) with (enc.Mop enc.Mzero enc.Mzero). 
    rewrite ALR.inv_dis. rewrite <- enc.homomorphism. replace (enc.Mop enc.Mzero enc.Mzero) 
    with enc.Mzero. rewrite comm. do 2 rewrite dot_assoc.
    apply right_cancel. rewrite comm. rewrite dot_assoc.
    rewrite MVS.RopInvDis.
    apply right_cancel. do 3 rewrite <- MoC.VG_Pexp_Vcons. 
    rewrite MoC.Sexp_dist. rewrite comm. 
    rewrite MoC.VF_add_product. apply Vfold_left_eq. apply Veq_nth.
    intros. do 4 rewrite Vnth_map2. do 3 rewrite <- VSn_eq.
    rewrite Vnth_map. trivial.
     rewrite one_right. trivial.
     rewrite one_right. trivial.
    (* part 3 *)
    simpl in *. apply bool_eq_corr. apply bool_eq_corr in H2. do 4 rewrite Vhead_nth.
    do 2 rewrite Vnth_map. do 4 rewrite index0eq. rewrite H2. rewrite <- PCMult.
    apply left_cancel. rewrite <- PCExp. intuition. 
    (* part 4 *)
    simpl. apply VGeq. apply bool_eq_corr in H2. apply VGeq in H1.
    apply Veq_nth. intros. do 7 rewrite Vnth_map2.  do 5 rewrite Vnth_tail.
    do 2 rewrite Vnth_map. unfold FSemiRingT.Aplus. 
    rewrite <- PCMult. apply left_cancel. rewrite <- Vnth_tail. rewrite H1.
    rewrite <- PCExp. do 2 rewrite Vnth_map2. do 2 rewrite <- Vnth_tail.
    trivial.

    (* Special soundness *)
    + intros. unfold u'_Rel. unfold u'_extractor. simpl in *.
    unfold u'_V1 in *. apply andb_true_iff in H1. destruct H1.
    apply andb_true_iff in H1. destruct H1. apply andb_true_iff in H1. 
    destruct H1. apply andb_true_iff in H2. destruct H2. simpl in *.
    apply andb_true_iff in H2. destruct H2. apply andb_true_iff in H2. 
    destruct H2. apply bool_eq_corr in H1. apply VGeq in H6.
    apply bool_eq_corr in H7. apply bool_eq_corr in H2. 
    apply VGeq in H3. apply bool_eq_corr in H4. 
    apply bool_eq_corr in H8. apply bool_eq_corr in H5. unfold disjoint in H0. 
    apply negb_false_iff in H0. rewrite negb_involutive in H0.
    apply F_bool_neq_corr in H0. apply andb_true_iff. split.
     apply andb_true_iff. split. apply andb_true_iff. split. 
    (* part 1 *)
    apply bool_eq_corr. simpl. unfold FSemiRingT.Aplus. rewrite EPC_vcons2.
    rewrite EPCExp. rewrite <- EPCMult. rewrite Vapp_map.
    rewrite <- EPCneg. do 2 rewrite Vcons_Vapp. do 2 rewrite <- VSn_eq.
    simpl. rewrite <- H1.  rewrite <- H2. apply ALVS2.ExtractorHelper.
    unfold not in *. intros. apply shift in H9.
    rewrite H9 in H0. apply H0. trivial. 
    (* part 2 *) 
    apply bool_eq_corr. rewrite <- MoC.VG_Pexp_Vcons. rewrite <- VSn_eq. 
    rewrite VF_scale_vcons2. do 2 rewrite Vcons_Vapp. 
    do 2 rewrite <- VSn_eq. rewrite <- MoC.Sexp_dist.
    rewrite <- MoC.VF_add_product. rewrite <- MVS.RopInvDis.
    rewrite <- enc.encOfOnePrec. rewrite <- VS1.mod_dist_Gdot.
    assert (enc.Mzero = (enc.Mop enc.Mzero enc.Mzero)). 
    rewrite one_right. intuition.
    rewrite H9. rewrite ALR.inv_dis. rewrite <- enc.homomorphism. 
    assert (forall a b c d, G1.Gdot (G1.Gdot a b) (G1.Gdot c d) = 
      G1.Gdot (G1.Gdot a c) (G1.Gdot b d)). intros. apply commHack.
    rewrite H10.
    rewrite <- MoC.VG_Pexp_Vcons in H5. do 2 rewrite <- VSn_eq in H5.
    rewrite MoC.VF_neg_inv. rewrite EncInv. 
    assert (forall a b : G1.G, G1.Gdot (G1.Ginv a) (G1.Ginv b) = 
        G1.Ginv (G1.Gdot a b)). apply inv_dist.
    rewrite H11. rewrite <- MoC.VG_Pexp_Vcons in H8. 
    do 2 rewrite <- VSn_eq in H8. 
    simpl in *.
    (* pose (inv_dist (A:=G1.G) (dot:=G1.Gdot)(Aone:=G1.Gone) 
      (Ainv:= G1.Ginv) (bool_equal:=G1.Gbool_eq)).
    rewrite <- e0. admit. *)
     rewrite <- H8. simpl in *. assert (G1.Gdot (MoC.VG_prod
             (Vcons (VS1.op (Vhead s.1.2) (Vhead t1.1.1.1))
                (MoC.VG_Pexp (Vtail s.1.2) (Vtail t1.1.1.1)))) 
        (enc.enc s.1.1.1.1.1 enc.Mzero (Ring.Finv t1.1.2)) = 
        G1.Gdot c.1.2 (VS1.op s.2.1.2 e1)). symmetry. 
    rewrite H5. trivial. rewrite H12.  rewrite <- H11. 
    rewrite H10. rewrite <- inv_left. rewrite one_left.
    rewrite ALVS1.neg_eq. rewrite <- VS1.mod_dist_Fadd.
    rewrite <- VS1.mod_dist_Fmul.
    replace (FmulInv (e1 - e2) * (Finv e2 + e1)) with Fone.
    symmetry. apply VS1.mod_id. field; auto.
    unfold not in *. intros. apply H0.
    apply ALVS1.shift in H13. apply H13. 
    (* part 3 *)
    apply bool_eq_corr. rewrite <- PCExp. rewrite <- PCMult. 
    do 4 rewrite Vhead_nth. do 2 rewrite Vnth_map.
    rewrite <- PCneg. do 4 rewrite index0eq. 
    symmetry in H4. rewrite  H4.
    symmetry in H7. rewrite H7.   apply ALVS2.ExtractorHelper.
    unfold not in *. intros. apply shift in H9. apply H0. apply H9.
    (* part 4 *)
    apply VGeq. apply Veq_nth. intros. do 2 rewrite Vnth_map2. 
    do 2 rewrite Vnth_map. rewrite <- PCExp. do 2 rewrite Vnth_map2.  rewrite <- PCMult. 
    do 5 rewrite Vnth_tail. do 2 rewrite Vnth_map. rewrite <- PCneg. cbn in *.
    assert (Vnth (Vmap2 (fun tHat cHat : G => tHat o cHat ^ e2) 
         (Vtail c.2) (Vtail s.2.2)) ip =
       Vnth (Vmap2 (fun x : F -> G => [eta x])
         (Vmap2 (fun (h1 : G) (u : F) => [eta PC s.1.1.1.1.2 h1 u])
            (Vremove_last s.2.2) (Vtail t2.1.1.1)) 
         (Vtail t2.2)) ip). rewrite H6. trivial. do 3 rewrite Vnth_map2 in H9.
    do 4 rewrite Vnth_tail in H9. symmetry in H9. rewrite H9. 
    assert (Vnth (Vmap2 (fun tHat cHat : G => tHat o cHat ^ e1) 
         (Vtail c.2) (Vtail s.2.2)) ip =
       Vnth (Vmap2 (fun x : F -> G => [eta x])
         (Vmap2 (fun (h1 : G) (u : F) => [eta PC s.1.1.1.1.2 h1 u])
            (Vremove_last s.2.2) (Vtail t1.1.1.1)) 
         (Vtail t1.2)) ip). 
    rewrite H3. trivial. do 3 rewrite Vnth_map2 in H10. do 4 rewrite Vnth_tail in H10.
    symmetry in H10. rewrite H10. 
    apply ALVS2.ExtractorHelper.
    unfold not in *. intros. apply shift in H11. apply H0. apply H11.

    (* honest verifier ZK *)
    + intros. simpl in *. split.
    (* Part 1 - Proving transcripts are equal *)  
    unfold u'_simulator_mapper. 
    unfold u'_simulator. unfold u'_P0. unfold u'_V0. unfold u'_P1.
    simpl in *. intros. unfold u'_Rel in H0. apply andb_true_iff in H0.
    destruct H0. apply andb_true_iff in H0. destruct H0. 
    apply andb_true_iff in H0. destruct H0. apply bool_eq_corr in H0. 
    apply VGeq in H1. apply bool_eq_corr in H2. apply bool_eq_corr in H3.
    simpl in *. rewrite <- H0. apply injective_projections. simpl.
    apply injective_projections. simpl. apply injective_projections. simpl.
    (* part 1.1 - Proving s is eqal.*)
    trivial.
    (* part 1.2 - Proving c is equal. (G*V2G*(VG (1+N))) *)
    simpl. apply injective_projections. simpl. apply injective_projections. simpl.
    (* part 1.2.1 *)
    rewrite <- dot_assoc. rewrite <- inv_right. rewrite one_right. trivial.
    (* part 1.2.2 *)
    simpl. rewrite <- H3. rewrite <- dot_assoc. rewrite <- inv_right. 
    rewrite one_right. trivial.
    (* part 1.2.3 *)
    simpl. rewrite <- H2. apply Vcons_eq_intro. rewrite <- dot_assoc.
    rewrite Vnth_map. rewrite <- inv_right. rewrite one_right. trivial.
    apply Veq_nth. intros. do 7 rewrite Vnth_map2. apply (Veq_nth4 ip) in H1.
    do 7 rewrite Vnth_map2 in H1. rewrite <- H1. rewrite <- dot_assoc.
    rewrite <- inv_right. rewrite one_right. trivial.

    (* part 1.3.1 proving challenges are equal *)
    simpl. trivial.

    (* part 1.4 proving responses are equal *)
    apply injective_projections. simpl. apply injective_projections. simpl. 
    apply injective_projections. simpl.
    (* part 1.4.1 *)
    trivial.
    (* part 1.4.2 *)
    simpl. trivial.
    (* part 1.4.3 *)
    simpl. trivial.
    (* part 1.4.4 *)
    simpl. trivial.

    (* part 2 *)
    intros. unfold u'_simulator_mapper_inv, u'_simulator_mapper.
    split. do 3 rewrite Prod_left_replace. do 3 rewrite Prod_right_replace.
    do 2 rewrite VF_sub_corr. do 2 rewrite VF_add_neg. rewrite (surjective_pairing r).
    rewrite (surjective_pairing r.1). simpl. apply injective_projections; simpl; auto.
    apply injective_projections; simpl. apply injective_projections; simpl; auto; field; auto.
    symmetry. apply ALR.whenAutoFails1. do 3 rewrite Prod_left_replace.  
    do 3 rewrite Prod_right_replace.  do 2 rewrite VF_sub_corr. do 2 rewrite VF_add_neg2.
    rewrite (surjective_pairing t). rewrite (surjective_pairing t.1). simpl.
    apply injective_projections; simpl; auto. apply injective_projections; simpl.
    apply injective_projections; simpl; auto; field; auto. symmetry. apply ALR.whenAutoFails2.
    
    
    + intros. simpl in *. unfold u'_V1. unfold u'_simulator. simpl.
      apply andb_true_iff. split. apply andb_true_iff. split. 
      apply andb_true_iff. split.  
      (* part 1 *)
      rewrite bool_eq_corr. rewrite <- dot_assoc. rewrite <- inv_left.
      rewrite one_right. trivial.
      (* part 2 *)
      apply bool_eq_corr. rewrite <- dot_assoc. rewrite <- inv_left.
      rewrite one_right. trivial.
      (* part 3 *)
      rewrite bool_eq_corr. rewrite <- dot_assoc.
      rewrite Vnth_map. rewrite <- inv_left.
      rewrite one_right. trivial.
      (* part 4 *)  
      rewrite VGeq. apply Veq_nth. intros. do 6 rewrite Vnth_map2.
      unfold PC. do 2 rewrite  <- dot_assoc.  apply left_cancel.
      rewrite <- inv_left. rewrite one_right.
     trivial.

    + intros. unfold u'_P1. trivial.
    
    + intros. trivial.
  Qed.
  
End wikSigma.


