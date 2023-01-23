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
From CoLoR Require Import VecUtil VecArith.
Require Import matrices matricesF.

Set implicit arguments.

(* Module includes various DLog Sigmas and other basic sigma protocols *)
Module DLogSig (Group : GroupSig)(Field : FieldSig)
  (VS : VectorSpaceSig Group Field)(Chal : GroupFromRing Field) <: SigmaPlus Chal.
  Import VS.
  Module HardProb := HardProblems Group Field VS.
  Import HardProb.
  Module Mo := MatricesFIns Field.
  Module PC := BasicComScheme Group Field VS Mo.
  Import PC.
  Module AddVSLemmas := VectorSpaceAddationalLemmas Group Field VS.
  Import AddVSLemmas.

  Definition St := prod G G.
  Definition W := F.

  Definition Rel := dLog.

  Definition C := G.

  Definition R := F.
  Definition T := F.

  (** Begin Sigma Proper *)
  (* We pass why to allow branching in disjunction *)
  Definition P0 (ggtox : G*G)(r : F)(w : F) : (G*G*G) :=
    (* (g, h) = ggtox, g^w = h *)
    let g := ggtox.1 in 
    (ggtox, g^r).

  Definition V0 (ggtoxgtor: G*G*G) (c: F): (G*G*G*F)
    := (ggtoxgtor, c).

  Definition P1 (ggtoxgtorc: G*G*G*F) (r x: F) : G*G*G*F*F :=
    let c    :=  snd (ggtoxgtorc) in
    let s:= (r + c*x) in (ggtoxgtorc, s).

  Definition V1 (ggtoxgtorcs : G*G*G*F*F) :=

    let g    :=  fst (fst (fst (fst ggtoxgtorcs))) in
    let gtox :=  snd (fst (fst (fst ggtoxgtorcs))) in
    let gtor :=  snd (fst (fst ggtoxgtorcs)) in
    let c    :=  snd (fst ggtoxgtorcs) in
    let s    :=  snd ggtoxgtorcs in 
    Gbool_eq (g^s) ((gtox^c) o gtor).

  Definition simMap (s : G*G)(w c x r :F):=
    (r+c*w).

  Definition simMapInv (s : G*G)(w c x t :F):=
    (t-c*w).

  Definition simulator (ggtox :G*G)(z e : F) :=
  let g := fst ggtox in
  let gtox := snd ggtox in
    (ggtox, g^(z) o - gtox^e, e, z).

  Definition extractor (s : vector F 2)(c : vector F 2) :=
    ((Vhead s) - (Vhead (Vtail s))) / ((Vhead c) - (Vhead (Vtail c))).

  Definition TE := T.

  Definition X := F.

  Definition simMapHelp (st : St)(x : X) : Prop := True.

  Definition M := 2.

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
    pose module_abegrp. intros. cbn in *.
    unfold V1, P1, P0.
    cbn.  unfold Rel, dLog in H. apply bool_eq_corr in H. apply bool_eq_corr.
    rewrite H. rewrite <- mod_dist_Fmul, <- mod_dist_Fadd. apply f_equal.
    field; auto.
  Qed.

  Definition allDifferent (e : vector Chal.G M) :=  PairwisePredicate Chal.Gdisjoint e.

  Lemma special_soundness : forall (s : St)(c : C)(e : vector Chal.G M)(t : vector T M),
    (* Forall e it is disjoint from all e *)
    PairwisePredicate Chal.Gdisjoint e ->
    bVforall2 (fun e1 t1 => V1 (s, c, e1, t1)) e t -> 
    Rel s (extractor t e) = true \/ fail_event s c e.
  Proof.
    pose module_abegrp. pose vs_field. pose Chal.module_abegrp.  destruct f. destruct F_R.
    intros. left. unfold Rel, extractor, dLog, V1, M in *.
    cbn in H0. apply bool_eq_corr. rewrite (VSn_eq e) in H0.
    rewrite (VSn_eq t) in H0. cbn in H0. apply andb_true_iff in H0.
    destruct H0. apply bVforall2_elim_head in H1. apply bool_eq_corr in H0.
    apply bool_eq_corr in H1. assert (Vhead e - Vhead (Vtail e) <> 0).
    rewrite (VSn_eq e) in H. simpl in H. apply andb_true_iff in H.
    apply (zero2 (dot:=Fadd)(Aone:=Fzero)(bool_equal:=Fbool_eq)(Ainv:=Finv)).
    destruct H. apply  bVforall_elim_head in H. apply disjoint_corr in H.
    trivial. apply (op_cancel (Vhead e - Vhead (Vtail e))). trivial.
    rewrite <- mod_dist_Fmul. rewrite Rmul_comm.
    rewrite <- Rmul_assoc. rewrite Finv_l. trivial. rewrite Rmul_comm.
    rewrite Rmul_1_l. symmetry. rewrite mod_dist_Fadd. rewrite <- neg_eq.
    rewrite H0. rewrite H1. rewrite (comm (s.2 ^ Vhead e) c). rewrite comm.
    pose (inv_dist (H:=a)). symmetry in e0. rewrite e0. rewrite <- dot_assoc.
    rewrite (dot_assoc (- c)). rewrite <- inv_left. rewrite one_left.
    rewrite neg_eq. rewrite comm. rewrite <- mod_dist_Fadd. trivial.
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
    pose module_abegrp. pose vs_field. intros. split.
    (* Main *)
    unfold P1, P0, simulator, simMap. simpl. unfold Rel, dLog in H0.
    apply bool_eq_corr in H0. apply injective_projections; simpl.
    apply injective_projections; simpl. apply injective_projections; simpl.
    trivial. rewrite H0. rewrite neg_eq. rewrite <- mod_dist_Fmul.
    rewrite <- mod_dist_Fadd. apply f_equal. unfold R, Chal.G in *. field; auto.
    trivial. trivial.
    (* Bijective *)
    unfold simMap, simMapInv. split; field; auto.
  Qed.

  Lemma simulator_correct : forall (s : St)(t : TE)(e : Chal.G),
    V1(simulator s t e) = true.
  Proof.
    pose module_abegrp. intros. unfold V1, simulator. apply bool_eq_corr.
    simpl. rewrite comm. rewrite <- dot_assoc. rewrite <- inv_left.
    rewrite one_right. trivial.
  Qed.
End DLogSig.

Module DLogSig2 (Group : GroupSig)(Field : FieldSig)
  (VS : VectorSpaceSig Group Field)(Chal : GroupFromRing Field) <: SigmaPlus Chal.
  Import VS.
  Module HardProb := HardProblems Group Field VS.
  Import HardProb.
  Module Mo := MatricesFIns Field.
  Module PC := BasicComScheme Group Field VS Mo.
  Import PC.
  Module AddVSLemmas := VectorSpaceAddationalLemmas Group Field VS.
  Import AddVSLemmas.

  Definition St := prod (prod G G) G.
  Definition W  := prod F F.

  Definition Rel (s :G*G*G)(w : F*F) := 
    let g     := s.1.1 in
    let h     := s.1.2 in
    let gtox  := s.2 in 
    Gbool_eq gtox (PC g h w.1 w.2).

  Definition disjoint (c1 c2 : F) :=
    negb (Fbool_eq c1 c2).

  Lemma disjointSim : forall a b, disjoint a b = disjoint b a.
  Proof.
    pose Chal.module_abegrp. intros. unfold disjoint. rewrite bool_eq_sym. trivial.
  Qed.

  Definition T := prod F F.

  (** Begin Sigma Proper *)
  (* We pass why to allow branching in disjunction *)
  Definition P0 (ggtox : G*G*G)(r : F*F)(w : F*F) : (G*G*G*G) :=
    let g := ggtox.1.1 in 
    let h := ggtox.1.2 in 
    (ggtox, PC g h r.1 r.2).

  Definition R := prod F F.
  Definition C := G.

  Definition P1 (ggtoxgtorc: G*G*G*G*F) (r x: F*F) : G*G*G*G*F*(F*F) :=
    let c    :=  snd (ggtoxgtorc) in
    let s1  := (r.1 + x.1*c) in 
    let s2  := (r.2 + x.2*c) in 
    (ggtoxgtorc, (s1, s2)).

  Definition V1 (ggtoxgtorcs :  G*G*G*G*F*(F*F)) :=
    let g    :=  ggtoxgtorcs.1.1.1.1.1 in
    let h    :=  ggtoxgtorcs.1.1.1.1.2 in
    let gtox :=  ggtoxgtorcs.1.1.1.2 in
    let gtor :=  ggtoxgtorcs.1.1.2 in
    let c    :=  ggtoxgtorcs.1.2 in
    let s1   :=  ggtoxgtorcs.2.1 in
    let s2   :=  ggtoxgtorcs.2.2 in
    Gbool_eq (PC g h s1 s2) ((gtox^c) o gtor).

  Definition simMap (s : G*G*G)(w :F*F)(c :F)(x : F)(r : F*F):=
    ((r.1+w.1*c),(r.2+w.2*c)).

  Definition simMapInv (s : G*G*G)(w :F*F)(c :F)(x : F)(t : F*F):=
    ((t.1-w.1*c),(t.2-w.2*c)).

  Definition simulator (ggtox :G*G*G)(z : F*F)(e : F) :=
  let g :=  ggtox.1.1 in
  let h :=  ggtox.1.2 in
  let gtox := snd ggtox in
    (ggtox, PC g h z.1 z.2 o - gtox^e, e, z).

  Definition TE := prod F F.

  Definition X := F.

  Definition simMapHelp (st : St)(x : X) : Prop := False.

  Definition M := 2.

  Definition fail_event (St : St)(c : C)(t : (vector Chal.G M)) : Prop := False.

  Definition extractor (s : vector T 2)(c : vector F 2) :=
    (((Vhead s).1 - (Vhead (Vtail s)).1) / ((Vhead c) - (Vhead (Vtail c))),
    ((Vhead s).2 - (Vhead (Vtail s)).2) / ((Vhead c) - (Vhead (Vtail c)))).

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
    pose module_abegrp. intros. cbn in *.
    unfold V1, P1, P0.
    cbn.  unfold Rel, dLog in H. apply bool_eq_corr in H. apply bool_eq_corr.
    rewrite H. rewrite PCExp. symmetry. rewrite comm. 
    rewrite PCMult. trivial.
  Qed.

  Definition allDifferent (e : vector Chal.G M) :=  PairwisePredicate Chal.Gdisjoint e.

  Lemma special_soundness : forall (s : St)(c : C)(e : vector Chal.G M)(t : vector T M),
    (* Forall e it is disjoint from all e *)
    allDifferent e  ->
    bVforall2 (fun e1 t1 => V1 (s, c, e1, t1)) e t -> 
    Rel s (extractor t e) = true \/ fail_event s c e.
  Proof.
    pose module_abegrp. pose vs_field. pose Chal.module_abegrp.  destruct f. destruct F_R.
    intros. left. unfold Rel, extractor, dLog, V1, M in *.
    cbn in H0. apply bool_eq_corr. rewrite (VSn_eq e) in H0.
    rewrite (VSn_eq t) in H0. cbn in H0. apply andb_true_iff in H0.
    destruct H0. apply bVforall2_elim_head in H1. apply bool_eq_corr in H0.
    apply bool_eq_corr in H1. assert (Vhead e - Vhead (Vtail e) <> 0).
    rewrite (VSn_eq e) in H. simpl in H. apply andb_true_iff in H.
    apply (zero2 (dot:=Fadd)(Aone:=Fzero)(bool_equal:=Fbool_eq)(Ainv:=Finv)).
    destruct H. apply  bVforall_elim_head in H. unfold disjoint in H.
    apply negb_true_iff in H. apply F_bool_neq_corr in H. trivial. simpl.
    (* Cleaned up *)
    rewrite <- PCExp. rewrite <- PCMult.
    rewrite <- PCneg. rewrite H0. rewrite H1. apply ExtractorHelper2. trivial.
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
    pose module_abegrp. pose vs_field. intros. split.
    (* Main *)
    unfold P1, P0, simulator, simMap. simpl. unfold Rel, dLog in H0.
    apply bool_eq_corr in H0. apply injective_projections; simpl.
    apply injective_projections; simpl. apply injective_projections; simpl.
    trivial. rewrite H0. rewrite PCExp. rewrite PCneg. rewrite PCMult.
    apply f_equal2; field; auto. trivial. apply injective_projections; field; auto.
    (* Bijective *)
    unfold simMap, simMapInv. split; apply injective_projections; simpl. field; auto.
    field; auto. field; auto. field; auto.
  Qed.

  Lemma simulator_correct : forall (s : St)(t : TE)(e : Chal.G),
    V1(simulator s t e) = true.
  Proof.
    pose module_abegrp. intros. unfold V1, simulator. apply bool_eq_corr.
    simpl. rewrite comm. rewrite <- dot_assoc. rewrite <- inv_left.
    rewrite one_right. trivial.
  Qed.
End DLogSig2.


