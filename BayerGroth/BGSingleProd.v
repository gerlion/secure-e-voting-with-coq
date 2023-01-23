Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
From Groups Require Import groups module vectorspace dualvectorspaces matrices 
  matricesF matricesField modulevectorspace groupfromring.
Require Import sigmaprotocolPlus.
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
Set Implicit Arguments.

(*                                                              *)
(*  Proof of the single value product arg from BG               *)

Module Type BGSingleProd (Commitment : GroupSig)
    (Field : FieldSig)(VS2 : VectorSpaceSig Commitment Field)
    (Chal : GroupFromRing Field)(Hack : Nat) <: SigmaPlus Chal.

  (* N = nm *)
  Let n := S (S (S Hack.N)).      (* n *)
  Import Field.

  Module Mo := MatricesFieldIns Field.
  Import Mo.
  Import Mo.mat.

  (* Make commitment scheme and matrix *)
  Module EPC := ExtendComScheme Commitment Field VS2 mat.
  Import EPC.
  Import EPC.MoM.
  Module PC := BasicComScheme Commitment Field VS2 mat.
  Import PC.

  Module HardProb := HardProblems Commitment Field VS2.
  Import HardProb.

  Import VS2.
  Import Commitment.

  Module RAL := RingAddationalLemmas Field.
  
  (* h hs c b *)
  Definition St : Type := G*(VG n)*G*F.  
  
  (* a r *)                          
  Definition W : Type := (VF n)*F.                            
  Definition Rel (s : St)(w : W) : bool :=
    let '(h, hs, c, b) := s in
    let '(a, r) := w in
    Gbool_eq s.1.2 (EPC h hs a r) && Fbool_eq b (VF_prod a).
    
  Definition  C : Type := G*G*G.

  (* d, r, dleta, s1, sx *)
  Definition  R : Type := VF n*F*VF (S Hack.N)*F*F.
  
  (* a, b, r, s *)
  Definition T : Type := VF n*VF n*F*F.

  Definition vecb (a : VF n) : VF n := Vbuild (fun i (ip : i < n) => 
      VF_prod (Vsub a (le_sub ip) )). 

  Lemma vecb_head : forall (a : VF n),
    Vhead (vecb a) = Vhead a.
  Proof.
    intros. rewrite Vbuild_head. unfold VF_prod.
    rewrite Vfold_left_head. rewrite Vhead_sub. trivial.  intros. field.
  Qed.

  Definition P0 (s : St)(r : R)(w : W) : (St*C) :=
    let '(h, hs, c, b) := s in
    let '(d, randr, delta, s1, sx) := r in
    let '(a, witr) := w in
    let delta1 := Vhead d in 
    let deltan := 0 in

    (s, (EPC h hs d randr, 
    (* EPC (-delta_1 * d_2, ...., - delta_(n-1) * d_n *)
    EPC h (Vremove_last hs) (Vcons (Finv delta1 * Vhead(Vtail d))
    (Vbuild (fun i (ip : i < S Hack.N) => Finv (Vnth delta ip) * Vnth (Vtail (Vtail d)) ip)))
   s1,
    (* EPC (delta_2-a_2*delta_1-b_1*d_2, ...., detlta_n-a_n*delta_(n-1)-b_(n-1)*d_n *)
    EPC h (Vremove_last hs) 
    (Vcons 
      (Vhead delta - Vhead (Vtail a)*delta1-(Vhead (vecb a))*Vhead(Vtail d)) 
    (Vadd (Vbuild (fun i (ip : i < Hack.N) => 
    Vnth (Vtail delta) ip - Vnth (Vtail (Vtail (Vremove_last a))) ip * Vnth (Vremove_last delta) ip - 
      Vnth (Vtail (Vremove_last (Vremove_last (vecb a)))) ip * Vnth (Vtail (Vtail (Vremove_last d))) ip))
    (Finv (VlastS a) * VlastS delta - VlastS (Vremove_last (vecb a)) * VlastS d))
    ) sx)).
   

  Definition P1 (sce : St*C*F)(r : R)(w : W): (St*C*F*T) :=
    let '(d, rd, delta, s1, sx) := r in
    let '(a, r) := w in
    (* a b r s *)
    (sce,
    (VF_add (VF_scale a sce.2) d,
    VF_add (VF_scale (vecb a) sce.2) (Vcons (Vhead d) (Vadd delta 0)),
    sce.2*r + rd,
    sce.2*sx + s1)).
      
  Definition V1 (scet : St*C*F*T) : bool :=
    let '(h, hs, c, b) := scet.1.1.1 in
    let '(cd, cdelta, cDelta) := scet.1.1.2 in
    let '(a, bvec, r, s) := scet.2 in
    let x := scet.1.2 in

    Gbool_eq (c^x o cd) (EPC h hs a r) &&
    Gbool_eq (cDelta^x o cdelta) (EPC h 
          (Vremove_last hs) (VF_sub (VF_scale (Vtail bvec) x) 
                            (VF_mult (Vremove_last bvec) (Vtail a))) s) &&
    Fbool_eq (Vhead bvec) (Vhead a) &&
    Fbool_eq (VlastS bvec) (x*b).

   Definition TE : Type := VF n*F*VF (S Hack.N)*F*F.                         
   Definition X  : Type := VF n.
   Definition simMapHelp (s : St)(x : X) : Prop := 
    let '(h, hs, c, b) := s in

    hs = Vmap (op h) x.
                                       
   Definition simulator (s : St)(t : TE)(x : F) : (St*C*F*T) :=
    let '(h, hs, c, b) := s in
    let '(d, randr, delta, s1, sx) := t in
  
      (s, (EPC h hs d randr o - c^x,
          EPC h 
          (Vremove_last hs) 
        (Vcons (x * (Vhead delta) - (Vhead d) * (Vhead (Vtail d)))
        (Vadd (Vbuild (fun i (ip : i < Hack.N) => x*(Vnth (Vtail delta) ip) - 
       Vnth (Vremove_last delta) ip * Vnth (Vtail (Vtail (Vremove_last d))) ip))
        (x * x * b - (VlastS delta) * (VlastS d)))) s1 o h^(Finv sx*x),
          EPC h (Vremove_last hs) (VF_zero (S (S Hack.N))) sx),
         x, (d,(Vcons (Vhead d) (Vadd delta (x*b))),randr,s1)).

   Definition simMap    (s : St)(w : W)(x : F)(xx : X)(r : R) : TE :=
    let '(h, hs, c, b) := s in
    let '(a, witr) := w in
    let '(d, randr, delta, s1, sx) := r in
    let delta1 := Vhead d in 
    let deltan := 0 in

    (VF_add (VF_scale a x) d, x*witr+randr, VF_add (VF_scale 
      (Vtail (Vremove_last (vecb a))) x) 
     delta, 
    x*sx+s1, 
    (* We compress the message of cDelta into the randomness *)
    sx+VF_inProd (Vremove_last xx) (Vcons 
      (Vhead delta - Vhead (Vtail a)*delta1-(Vhead (vecb a))*Vhead(Vtail d)) 
    (Vadd (Vbuild (fun i (ip : i < Hack.N) => 
    Vnth (Vtail delta) ip - Vnth (Vtail (Vtail (Vremove_last a))) ip * Vnth (Vremove_last delta) ip - 
      Vnth (Vtail (Vremove_last (Vremove_last (vecb a)))) ip * Vnth (Vtail (Vtail (Vremove_last d))) ip))
    (Finv (VlastS a) * VlastS delta - VlastS (Vremove_last (vecb a)) * VlastS d))
    )).

   Definition simMapInv (s : St)(w : W)(x : F)(xx : X)(t : TE) : R :=
    let '(h, hs, c, b) := s in
    let '(a, witr) := w in
    let '(d, randr, delta, s1, sx) := t in


    let org_d := VF_sub d (VF_scale a x) in 
    let org_r  := randr-x*witr in 
    let org_delta := VF_sub delta (VF_scale (Vtail (Vremove_last (vecb a))) x) in 
    let delta1 := Vhead org_d in 
    let deltan := 0 in

    let org_sx := sx-VF_inProd (Vremove_last xx) (Vcons 
      (Vhead org_delta - Vhead (Vtail a)*delta1-(Vhead (vecb a))*Vhead(Vtail org_d)) 
    (Vadd (Vbuild (fun i (ip : i < Hack.N) => 
    Vnth (Vtail org_delta) ip - Vnth (Vtail (Vtail (Vremove_last a))) ip * Vnth (Vremove_last org_delta) ip - 
      Vnth (Vtail (Vremove_last (Vremove_last (vecb a)))) ip * Vnth (Vtail (Vtail (Vremove_last org_d))) ip))
    (Finv (VlastS a) * VlastS org_delta - VlastS (Vremove_last (vecb a)) * VlastS org_d))) in

    (org_d,org_r, org_delta, s1-x*org_sx, 
     org_sx).

   Definition M : nat := 2.
   Definition extractor (t : vector T M)(e : vector F M) : W :=
    (VF_scale (VF_sub (Vhead t).1.1.1 (VlastS t).1.1.1) 
    (FmulInv (Vhead e - VlastS e)), ((Vhead t).1.2-(VlastS t).1.2) * FmulInv
    (Vhead e-VlastS e)).
  
  (** We require the functions do not modifiy the previous transcript *)
  Lemma pres_p0 : forall (s : St)(r : R)(w : W), (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. destruct s. destruct p. destruct p. destruct r. destruct p.
    destruct p. destruct p. destruct w. unfold P0. rewrite Prod_right_replace.
    trivial.
  Qed.

  Lemma pres_p1 : forall (sce : St*C*F)(r : R)(w : W), 
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Proof.
    intros. destruct sce. destruct p. destruct s. destruct p. destruct p.
    destruct r. destruct p. destruct p. destruct p. destruct w. unfold P1. 
    rewrite Prod_right_replace. trivial.
  Qed.

  Lemma pres_sim : forall (s: St)(t : TE)(e : F),
      s = (simulator s t e).1.1.1.
  Proof.
    intros.  unfold simulator. destruct s. destruct p. destruct p. 
    destruct t. destruct p. destruct p. destruct p. simpl. trivial.
  Qed. 
  
  Lemma chal_sim : forall (s: St)(t : TE)(e : F),
    e = (simulator s t e).1.2.  
  Proof.
    intros. unfold simulator. destruct s. destruct p. destruct p. 
    destruct t. destruct p. destruct p. destruct p. simpl. trivial.
  Qed.

  (** Properties *)
  Lemma correctness : forall (s :St)(w:W)(r:R)(c: F),
    Rel s w ->
    V1 (P1 ((P0 s r w), c) r w) = true.
  Proof.
    pose module_abegrp. destruct vs_field. destruct F_R.
    intros. unfold V1, P1, P0. destruct s. destruct p. destruct p.
    destruct r. destruct p. destruct p. destruct p. destruct w.
    do 3 rewrite Prod_right_replace. rewrite Prod_left_replace.
    unfold Rel in *. apply andb_true_iff in H. destruct H.
    apply bool_eq_corr in H. apply F_bool_eq_corr in H0. simpl in H.
    apply andb_true_iff. split.  apply andb_true_iff. split.
    apply andb_true_iff. split.
    + (* First commit open *)
    apply bool_eq_corr. rewrite H. rewrite EPC_add. rewrite Rmul_comm.
    rewrite EPCExp. trivial.
    + (* Second commit open *)
    apply bool_eq_corr. rewrite <- EPCExp. rewrite <- EPC_add. apply f_equal2.
    (* This corresponses to line 4 of the paper proof *)
    ++ unfold VF_scale. rewrite Vcons_map. unfold VF_add, FMatrix.VA.vector_plus.
    rewrite Vcons_map2. apply Vcons_eq_elim_gen. split.
    (* Head case *)
    +++ rewrite Vhead_map2. unfold VF_neg. do 2 rewrite Vhead_map.
    rewrite <- Vtail_map2. do 2 rewrite Vhead_map2.
    rewrite Vhead_Vremove_last. do 2 rewrite Vhead_map2.
    rewrite Vtail_cons. do 2 rewrite Vhead_cons. unfold FSemiRingT.Aplus.
    do 3 rewrite Rdistr_l. rewrite Vhead_Vadd. rewrite <- Radd_0_l.
    do 2 rewrite Radd_assoc. apply RAL.cancel_1_3; auto. rewrite Radd_0_l.
    rewrite RAL.bi_exp. do 2 rewrite Vhead_cons. rewrite Vtail_map. rewrite Vhead_map.
    do 3 rewrite ALR.inv_dis. do 3 rewrite Radd_assoc. 
    rewrite VF_prod_1_head. rewrite Vhead_sub.
    symmetry. do 2 rewrite <- Radd_assoc. assert (forall a b c, b = c ->
    a = 0 -> a + b = c). intros. rewrite H1. rewrite H2. ring.
    apply H1. rewrite Radd_assoc. apply f_equal2. rewrite Radd_comm. apply f_equal2.
    ring. do 2 rewrite move_neg. do 2 rewrite <- Rmul_assoc. apply f_equal2.
    trivial. apply Rmul_comm. rewrite Rmul_comm. rewrite move_neg. apply Rmul_comm. 
    rewrite VF_prod_2_head.
    rewrite Vhead_sub. rewrite Vhead_tail_sub. ring.
    +++ rewrite Vadd_map. rewrite (VSn_addS (Vbuild
     (fun (i : nat) (ip : i < S Hack.N) => Finv (Vnth v0 ip) * Vnth (Vtail (Vtail v1)) ip))).
    rewrite Vadd_map2. apply Vadd_eq_elim_gen. split.
    (* Last *)
    ++++ rewrite VlastS_tail. rewrite VlastS_map2. do 2 rewrite VlastS_map.
         rewrite VlastS_tail. do 2 rewrite VlastS_map2. rewrite VlastS_tail. 
         rewrite VlastS_build. rewrite Vmap2_remove_last. do 2 rewrite VlastS_map2.
    rewrite Vmap_remove_last. do 2 rewrite VlastS_map. unfold FSemiRingT.Aplus.
    rewrite (Vremove_last_cons (Vhead v1)). rewrite Vremove_last_add.
    do 2 rewrite (VlastS_cons (Vhead v1)). rewrite VlastS_map. rewrite VlastS_add.
    do 3 rewrite Rdistr_l. rewrite VlastS_build. rewrite le_sub_eq. 
    assert (forall x y z, z * (x+y) = (z * x)+(z*y)). intros. field; auto.
    do 2 rewrite H1.  symmetry. do 3 rewrite RAL.inv_dis. rewrite <- Radd_0_l. 
    do 5 rewrite Radd_assoc. symmetry. apply RAL.cancel_2_3. rewrite Rmul_assoc. 
    rewrite <- Rmul_assoc. rewrite Rmul_comm. rewrite  <- move_neg. apply f_equal.
    rewrite Rmul_comm. rewrite Rmul_assoc. apply f_equal2; auto. symmetry.
    rewrite <- Radd_0_l. do 2 rewrite Radd_assoc. apply RAL.cancel_3_3.
    do 2 rewrite RAL.move_neg. 
    do 2 rewrite <- Rmul_assoc. apply f_equal2; auto. do 2 rewrite Radd_0_l.
    assert (forall a b c, b = c -> a = 0 -> a + b = c). intros. rewrite H3. 
    rewrite H2. ring. apply H2. rewrite Rmul_comm. rewrite RAL.move_neg.
    rewrite Rmul_comm. apply f_equal2. rewrite VlastS_nth. apply f_equal.
    apply Vnth_eq. trivial. rewrite VlastS_nth. do 2 rewrite Vnth_tail.
    apply Vnth_eq. trivial. 
    rewrite VlastS_nth. rewrite Vnth_remove_last. rewrite Vbuild_nth.  
    replace (0 * c) with 0. rewrite <- Radd_assoc. rewrite Radd_0_l. 
    apply -> shift. rewrite Rmul_assoc. apply f_equal2. symmetry.
    rewrite Rmul_comm. rewrite Rmul_assoc. apply f_equal2. rewrite Rmul_comm.
    unfold VF_prod. rewrite <- Vfold_left_Vadd_Fmul. rewrite le_sub_eq_last. 
    trivial. trivial. trivial. ring. 
    (* Body *) 
    ++++ apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_map.
    do 2 rewrite Vnth_remove_last. do 2 rewrite Vbuild_nth. symmetry. 
    rewrite Vnth_tail. rewrite Vnth_map2. do 2 rewrite Vnth_map. 
    rewrite <- Vtail_map2. rewrite (Vtail_cons (Vhead v1)). rewrite Vmap2_remove_last. 
    rewrite (Vremove_last_cons (Vhead v1)). rewrite Vremove_last_add. symmetry.
    unfold FSemiRingT.Aplus. do 2 rewrite Vnth_map2. rewrite <- Vtail_map2.
    do 2 rewrite Vtail_map. do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map.
    assert (forall x y z, z * (x+y) = (z * x)+(z*y)). intros. field; auto.
    rewrite H1. do 5 rewrite Rdistr_l. do 5 rewrite <- Vnth_tail. rewrite Vtail_cons.
    do 5 rewrite <- Vnth_remove_last. do 5 rewrite Vremove_last_Vtail.
    rewrite Vremove_last_add. do 2 rewrite <- Vnth_remove_last.
    do 3 rewrite RAL.inv_dis. do 3 rewrite Radd_assoc. apply f_equal2.
    +++++ apply f_equal2.
    ++++++ apply f_equal2.
    +++++++ assert (forall a b c d, a = c -> b = d -> a = b + c - d). intros.
    rewrite H2. rewrite H3. ring. apply H2. trivial. do 2 rewrite Vnth_remove_last.
    do 5 rewrite Vnth_tail. do 2 rewrite Vnth_remove_last. rewrite Vnth_map.
    rewrite Rmul_assoc. apply f_equal2; auto. symmetry. rewrite Rmul_comm.
    rewrite Rmul_assoc. apply f_equal2; auto. do 2 rewrite Vbuild_nth.
    rewrite Rmul_comm. unfold VF_prod. rewrite <- Vfold_left_Vadd_Fmul.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_add.
    destruct (Nat.eq_dec i0 (S (S i))). rewrite Vnth_sub. apply Vnth_eq. rewrite e.
    lia. do 2 rewrite Vnth_sub. apply Vnth_eq. trivial.
    +++++++ rewrite RAL.move_neg. rewrite RAL.move_neg2. rewrite Rmul_assoc. 
    apply f_equal2. rewrite Rmul_comm. apply f_equal2. trivial.
    rewrite Vnth_remove_last. do 2 rewrite Vnth_tail. rewrite Vnth_sub.
    apply Vnth_eq. trivial. trivial. 
    ++++++ do 4 rewrite Vnth_tail. do 4 rewrite Vnth_remove_last.
    rewrite Vnth_tail. rewrite Vnth_remove_last. rewrite Vnth_map.
    do 3 rewrite RAL.move_neg2. rewrite Rmul_comm. rewrite Rmul_assoc.
    apply f_equal2. rewrite Rmul_comm. apply f_equal2.  apply f_equal.
    apply Vnth_eq. trivial. trivial. apply Vnth_eq. trivial. 
    +++++ rewrite RAL.move_neg2. apply f_equal. do 3 rewrite Vnth_tail.
    rewrite Vnth_remove_last. apply Vnth_eq. trivial.
    ++ field.
    (* Remaining too *)
    + apply F_bool_eq_corr. do 2 rewrite Vhead_map2. do 2 rewrite Vhead_map.
    rewrite Vbuild_head. rewrite Vhead_cons. apply f_equal2; auto.
    unfold VF_prod. rewrite Vfold_left_head.
    rewrite Vhead_sub. trivial. intros; field.
    + apply F_bool_eq_corr. rewrite VlastS_map2. rewrite (VlastS_cons (Vhead v1)).
    rewrite VlastS_add. rewrite VlastS_map. rewrite VlastS_build.
    rewrite le_sub_eq. rewrite H0. unfold FSemiRingT.Aplus. rewrite Radd_comm.
    rewrite Radd_0_l. apply Rmul_comm.
  Qed.

  Definition Polynomial N (w u : VF (S N))(e : F)(a : VF N) : F.
      induction N. apply (e*Vhead w+Vhead u).
      apply ((IHN (Vremove_last w)(Vremove_last u)(Vremove_last a)) * VlastS a +
      (VF_prod (Vconst e (S (S N)))) * VlastS w + 
      (VF_prod (Vconst e (S N))) * VlastS u).    
  Defined.

  Lemma Polynomial_ind : forall N (w u : VF (S (S N)))(e : F)(a : VF (S N)),
    Polynomial w u e a = 
    Polynomial (Vremove_last w)(Vremove_last u)e(Vremove_last a) * VlastS a +
      (VF_prod (Vconst e (S (S N))))*VlastS w+(VF_prod (Vconst e (S N)))* VlastS u.
  Proof.
    intros. simpl. trivial.
  Qed.    

 Definition fail_event (s : St)(com : C)(e : vector F M) : Prop := 
    let '(h, hs, c, b) := s in
    let '(cd, cdelta, cDelta) := com in
   
    (exists a heada lasta r r' w u r'' r''',
    (* First we show that all the coefficents were commited to *)
    c = EPC h hs a ((r - r') / (Vhead e - VlastS e)) /\
    c ^ Vhead e o cd = EPC h hs heada r /\
    c ^ VlastS e o cd = EPC h hs lasta r' /\
    cdelta = EPC h (Vremove_last hs) u r'' /\
    cDelta = EPC h (Vremove_last hs) w r''' /\
    (* If the polynomial sampled at (Vhead e) is zero *)
    b * VF_prod (Vconst (Vhead e) n) = VF_prod (VF_add
      (VF_scale a (Vhead e - VlastS e)) lasta) +
      Polynomial w u (Vhead e) (Vtail (Vtail heada)) /\
    (* But the polynomial is not zero *)
      b <> VF_prod a).

   Definition allDifferent (e : vector F M) := PairwisePredicate Chal.Gdisjoint e.

  Lemma special_soundness : forall (s : St)(c : C)(e : vector F M)(t : vector T M),
    (* Forall e it is disjoint from all e *)
    allDifferent e ->
    bVforall2 (fun e1 t1 => V1 (s, c, e1, t1)) e t -> 
    Rel s (extractor t e) = true \/ fail_event s c e.
  Proof.
    pose module_abegrp. destruct vs_field. destruct F_R.
    intros. unfold Rel, extractor. (* First we will get the verification equations unpacked *)
    destruct s as [p b]. destruct p as [p ca]. destruct p as [h hs].
    destruct c as [p cDelta]. destruct p as [cd cdelta].
    apply bVforall2_elim_2 in H0. destruct H0. unfold V1 in *. 
    do 3 rewrite Prod_left_replace in H0. do 3 rewrite Prod_right_replace in H0.
    destruct (Vhead t) as [p heads]. destruct p as [p headr]. 
    destruct p as [heada headb]. apply andb_true_iff  in H0. destruct H0.
    apply andb_true_iff  in H0. destruct H0. apply andb_true_iff  in H0. destruct H0.
    apply bool_eq_corr in H0. do 3 rewrite Prod_left_replace in H1. 
    do 3 rewrite Prod_right_replace in H1. destruct (VlastS t) as [p lasts]. 
    destruct p as [p lastr]. destruct p as [lasta lastb]. apply andb_true_iff in H1.
    destruct H1. apply andb_true_iff in H1. destruct H1. apply andb_true_iff in H1.
    destruct H1. apply bool_eq_corr in H1. apply PairwisePredict_2 in H.
    unfold Chal.Gdisjoint in H. apply negb_true_iff in H.
    apply F_bool_neq_corr in H. apply bool_eq_corr in H7. apply bool_eq_corr in H4.
    (* ca = EPC n h hs .... *) 
    assert (ca = EPC h hs (VF_scale (VF_sub heada lasta) 
    (FmulInv (Vhead e - VlastS e))) ((headr-lastr) * FmulInv
    (Vhead e-VlastS e))). rewrite EPCExp. unfold VF_sub. rewrite <- EPCMult.
    rewrite <- H0. rewrite <- EPCneg. rewrite <- H1. rewrite <- (inv_dist (dot:=Gdot)).
    unfold abegop. rewrite (comm (-ca ^ VlastS e)). rewrite dot_assoc.
    rewrite <- (dot_assoc (ca ^ Vhead e)). rewrite <- inv_right. rewrite one_right.
    rewrite neg_eq. rewrite <- mod_dist_Fadd. rewrite <- mod_dist_Fmul. 
    symmetry. rewrite <- mod_id. apply f_equal. field. unfold not. intros.
    apply H. apply RAL.shift. trivial. 
    (* c_Delta *)
    assert (cDelta = EPC h (Vremove_last hs) 
    (VF_scale (VF_add (VF_sub (VF_sub (VF_scale (Vtail headb) (Vhead e)) 
      (VF_mult (Vremove_last headb)  (Vtail heada)))
          (VF_scale (Vtail lastb) (VlastS e) )) (VF_mult (Vremove_last lastb) (Vtail lasta)))
    (FmulInv (Vhead e - VlastS e)))
       ((heads - lasts) / (Vhead e - VlastS e))).
    rewrite EPCExp.  unfold VF_sub in *. rewrite VF_add_ass. rewrite <- EPCMult.
    rewrite <- H4. rewrite (dob_neg (EPC h (Vremove_last hs)
     (VF_add (VF_neg (VF_scale (Vtail lastb) (VlastS e)))
        (VF_mult (Vremove_last lastb) (Vtail lasta))) (Finv lasts))).
   rewrite EPCneg. rewrite VF_neg_move. rewrite VF_neg_neg. rewrite RAL.Finv_inv.
    rewrite <- H7. pose (inv_dist (A:=G)). rewrite <- e0. pose (commHack (A:=G)(dot:=Gdot)).
    unfold abegop  in e1. rewrite e1. rewrite <- inv_right. rewrite one_right.
    rewrite neg_eq. rewrite <- mod_dist_Fadd. rewrite <- mod_dist_Fmul.
    assert (forall g a, a = 1 -> g^a = g). intros. subst. rewrite  mod_id.
    trivial. rewrite H9. trivial. field. unfold not. intros. apply H.
    apply shift; auto. auto.
    (* c_delta *)
    assert (cdelta = EPC h (Vremove_last hs) (VF_add
          (VF_sub (VF_scale (Vtail headb) (Vhead e))
             (VF_mult (Vremove_last headb) (Vtail heada)))
          (VF_scale
             (VF_scale
                (VF_add
                   (VF_sub
                      (VF_sub (VF_scale (Vtail headb) (Vhead e))
                         (VF_mult (Vremove_last headb) (Vtail heada)))
                      (VF_scale (Vtail lastb) (VlastS e)))
                   (VF_mult (Vremove_last lastb) (Vtail lasta)))
                (FmulInv (Vhead e - VlastS e))) (Finv (Vhead e))))
       (heads + (heads - lasts) / (Vhead e - VlastS e) * Finv (Vhead e))).
    rewrite H9 in H4. rewrite EPCExp in H4. assert (forall a b c, a o b = c ->
    b = c o - a). intros. rewrite <- H10. rewrite comm. rewrite dot_assoc. 
    rewrite <- inv_left. rewrite one_left. trivial. apply H10 in H4.
    rewrite neg_eq in H4. do 2 rewrite <- EPCExp in H4. rewrite EPCMult in H4. trivial.
    remember (VF_scale
          (VF_add
             (VF_sub
                (VF_sub (VF_scale (Vtail headb) (Vhead e))
                   (VF_mult (Vremove_last headb) (Vtail heada)))
                (VF_scale (Vtail lastb) (VlastS e)))
             (VF_mult (Vremove_last lastb) (Vtail lasta)))
          (FmulInv (Vhead e - VlastS e))) as w. remember (VF_add
           (VF_sub (VF_scale (Vtail headb) (Vhead e))
              (VF_mult (Vremove_last headb) (Vtail heada))) 
           (VF_scale w (Finv (Vhead e)))) as u.
    (* Now ready to prove that xb_i = b_i-1 a_i + x w_i + u_i *)
    assert (VF_scale (Vtail headb) (Vhead e) = VF_add (VF_add 
        (VF_mult (Vremove_last headb) (Vtail heada)) (VF_scale w (Vhead e))) u).
    rewrite Hequ. rewrite Heqw. assert (forall a b c d : VF (S (S Hack.N)), c = VF_neg d
    -> a = VF_add (VF_add b c) (VF_add (VF_sub a b) d)). intros. rewrite H11.
    rewrite VF_comm_hack. rewrite VF_sub_corr. rewrite VF_add_neg3.
    rewrite <- VF_add_ass. rewrite VF_add_neg2. trivial. apply H11.
    apply Veq_nth. intros. do 5 rewrite Vnth_map. do 4 rewrite Vnth_map2.   
    do 3 rewrite Vnth_map. unfold FSemiRingT.Aplus. rewrite move_neg.
    apply f_equal2. trivial. rewrite RAL.Finv_inv. trivial.
    (* assert x^n b = prod a_i + .... *)
    assert (Vhead e * b * VF_prod (Vconst (Vhead e) (S (S Hack.N))) = 
      VF_prod heada + (Polynomial w u (Vhead e) (Vtail (Vtail heada)))).
    apply F_bool_eq_corr in H2. rewrite <- H2.
    assert (VlastS headb * VF_prod (Vconst (Vhead e) (S (S Hack.N)))
      = Vhead headb * VF_prod (Vtail heada) + (Polynomial w u (Vhead e)
         (Vtail (Vtail heada)))).
    + clear H10. clear Hequ H9 Heqw H8 H5 H7 H4 H1 H2 H6 H0 H H3.
    clear h hs ca b cd cdelta cDelta lasta lastb lastr lasts. unfold n in *. 
    induction (S Hack.N). apply VlastS_intro in H11.
    rewrite VlastS_map in H11. rewrite VlastS_tail in H11. unfold VF_prod, VF_sum.
    rewrite Vfold_left_head. intros.  rewrite Vfold_left_head. intros. 
    simpl. rewrite H11. do 2 rewrite VlastS_map2. unfold FSemiRingT.Aplus. 
    rewrite Radd_assoc. apply f_equal2. apply f_equal2. rewrite VlastS_map2.
    rewrite VlastS_remove_last_2. rewrite VlastS_Vhead. trivial. rewrite VlastS_Vhead.
    trivial. rewrite VlastS_map. apply Rmul_comm. rewrite VlastS_Vhead. trivial.
    intros; field. intros; field.
    (* Starting induction step. *)
    apply Veq_elim_gen2 in H11. destruct H11. rewrite VlastS_map in H. 
    rewrite VlastS_tail in H. unfold VF_prod. rewrite Vconst_cons. 
    rewrite Vfold_left_Vcons_Fmul.  rewrite <- (Rmul_comm (Vhead e)). 
    rewrite Rmul_assoc. rewrite H. do 3 rewrite VlastS_map2. unfold FSemiRingT.Aplus.
    do 2 rewrite Rdistr_l. assert (forall a b c, a *b*c = a*c*b). intros. field. 
    rewrite H1. rewrite (IHn0 (Vremove_last heada) (Vremove_last headb) 
                           (Vremove_last w) (Vremove_last u)).
    (* We are in the induction step cleaning up *)
    rewrite Vhead_Vremove_last. rewrite Rdistr_l. 
    do 2 rewrite <- Radd_assoc. apply f_equal2. rewrite <- Rmul_assoc.
    unfold VF_prod. rewrite <- Vfold_left_Vadd_Fmul. rewrite <- Vremove_last_Vtail.
    rewrite <- VSn_addS. trivial.
    (* Need to show the polynomails are equal *)
    symmetry. rewrite Polynomial_ind. rewrite <- Radd_assoc. apply f_equal2.
    do 2 rewrite Vremove_last_Vtail. rewrite VlastS_tail. trivial.
    rewrite VlastS_map. apply f_equal2. rewrite H1. rewrite <- Rmul_assoc.
    rewrite <- Vfold_left_Vcons_Fmul. apply Rmul_comm. apply Rmul_comm.
     rewrite Vmap_remove_last in H0.
    rewrite Vremove_last_Vtail in H0. unfold VF_scale. rewrite H0.
    do 3 rewrite Vmap2_remove_last. apply f_equal2; auto. 
    rewrite Vmap_remove_last. apply f_equal2; auto. rewrite Vremove_last_Vtail.
    trivial. 
    (* Now we can finally prove the main lemma that x^n b = prod a_i + .... *)    
    + rewrite H12. apply F_bool_eq_corr in H3. rewrite H3. apply f_equal2.
    rewrite Rmul_comm. unfold VF_prod. rewrite <- Vfold_left_Vcons_Fmul.
    rewrite <- VSn_eq. trivial. trivial.
    (* Start main relationship *)
    + assert (heada = VF_add 
      (VF_scale (VF_scale (VF_sub heada lasta) (FmulInv (Vhead e - VlastS e)))
      (Vhead e - VlastS e)) lasta). rewrite VF_scale_scale. rewrite VF_scale_1_gen. 
     rewrite VF_sub_corr.
     rewrite VF_add_neg2. trivial.
     field. unfold not. intros. apply H. apply shift. trivial. 

     remember (Vtail heada) as c.
      rewrite H13 in H12. rewrite Heqc in H12. 
    case_eq (Fbool_eq b (VF_prod (VF_scale (VF_sub heada lasta) 
    (FmulInv (Vhead e - VlastS e))))); intros.
    ++ apply F_bool_eq_corr in H14. left. apply andb_true_iff. split.
    apply bool_eq_corr. apply H8. apply F_bool_eq_corr. trivial.
    ++ right. apply F_bool_neq_corr in H14. unfold fail_event.
    exists (VF_scale (VF_sub heada lasta) (FmulInv (Vhead e - VlastS e))).
    exists heada. exists lasta. exists headr. exists lastr. exists w. exists u.
    exists (heads + (heads - lasts) / (Vhead e - VlastS e) * (Finv (Vhead e))).
    exists ((heads - lasts) / (Vhead e - VlastS e)). split. rewrite H8. trivial.
    split; auto. split; auto. split; auto. split; auto. split; auto. rewrite <-
    H12. rewrite <- Rmul_assoc. symmetry. rewrite Rmul_comm. rewrite <- Rmul_assoc.
    unfold VF_prod. rewrite <- Vfold_left_Vcons_Fmul. trivial.
  Qed.

  Lemma honest_verifier_ZK :
    forall (s : St)(w : W)(e : F)(x : X)(r : R)(t : TE),
      simMapHelp s x ->
      Rel s w ->
      ((P1((P0 s r w), e) r w) =
      simulator s (simMap s w e x r) e) /\ 
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.
  Proof.
    pose module_abegrp. destruct vs_field. destruct F_R.
    intros. destruct s. destruct p. destruct p. 
    destruct t. destruct p. destruct p. destruct p. destruct w. 
    destruct r. destruct p.  destruct p. destruct p. unfold Rel in H0.
    apply andb_true_iff in H0. destruct H0. apply bool_eq_corr in H0.
    apply F_bool_eq_corr in H1. split. 
    + (*Time to prove simulator produces the same things *)
    unfold P1, P0, simulator, simMap. rewrite Prod_right_replace.
    apply injective_projections. apply injective_projections. 
    apply injective_projections.  
    ++ do 2 rewrite Prod_left_replace. trivial. 
    (* Proving commitments are equal *)
    ++ do 2 rewrite Prod_right_replace. apply injective_projections. 
       apply injective_projections.
    (* cd *)
    +++ do 4 rewrite Prod_left_replace. rewrite <- EPCMult. rewrite Rmul_comm.
    rewrite EPCExp. rewrite <- H0. rewrite Prod_right_replace. rewrite comm.
    rewrite dot_assoc. rewrite <- inv_left. rewrite one_left. trivial.
    (* c delta *)
    +++ do 2 rewrite Prod_right_replace. do 3 rewrite Vhead_map2. 
    do 2 rewrite Vhead_map. do 2 rewrite VlastS_map2. do 2 rewrite VlastS_map. 
    unfold FSemiRingT.Aplus. rewrite <- (EPCfall g0 (Vremove_last v)). 
    rewrite <- VF_neg_zero. do 3 rewrite <- RAL.move_neg2. rewrite <- EPCneg. 
    replace (VF_zero (S (S Hack.N))) with (VF_scale (VF_zero (S (S Hack.N))) e).
    rewrite EPCExp. rewrite <- trapdoorEPC. rewrite <- EPCExp. 
    rewrite EPCneg. rewrite EPCMult. apply f_equal2.
    (*  c delta message  *)
    ++++  unfold VF_scale, VF_neg, VF_add, FMatrix.VA.vector_plus.
     do 2 rewrite Vcons_map. rewrite Vcons_map2.
    assert (forall a b c, a * ( b + c) = a*b+a*c). intros. field.
    assert (forall a b c d e f g h i , b = g -> d = Finv i -> e = Finv h -> 
      a = c ->
    a + b - (c + d + (e + f)) - (g + h + i) =  Finv f). intros. subst. field.
    apply Vcons_eq_intro.
    (* Proving the first part of the c delta message *)
    +++++ do 3 rewrite Rdistr_l. do 3 rewrite H2. unfold FSemiRingT.Aplus. 
    rewrite H3; trivial. rewrite vecb_head. rewrite RAL.move_neg2.
    rewrite RAL.Finv_inv. rewrite Rmul_comm. rewrite Rmul_assoc. apply f_equal2.
    apply Rmul_comm. trivial. rewrite RAL.move_neg2. rewrite Vtail_map. 
    rewrite Vhead_map. rewrite RAL.Finv_inv. rewrite Rmul_assoc. apply f_equal2. 
    apply Rmul_comm. trivial. rewrite Vtail_map. rewrite Vhead_map. 
    do 2 rewrite Rmul_assoc. apply f_equal2. rewrite Vbuild_remove_last.
    rewrite Vbuild_tail. rewrite Vbuild_head. rewrite VF_prod_2_head.
    rewrite Vhead_sub. rewrite Vhead_tail_sub. rewrite Rmul_comm.
    do 2 rewrite <- Rmul_assoc. apply f_equal. apply Rmul_comm.  trivial.
    (* proving the second part of the c delta message *)
    +++++ apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vnth_map.
    do 2 rewrite Vnth_add. destruct (Nat.eq_dec i Hack.N). rewrite Vbuild_nth.
    do 2 rewrite Rdistr_l. do 2 rewrite H2. unfold FSemiRingT.Aplus. 
    assert (forall a c d e f h i, d = Finv i -> e = Finv h -> 
      a = c ->
      a - (c + d + (e + f)) - (h + i) =  Finv f). intros. subst. field.
    rewrite H4. rewrite RAL.move_neg2. apply f_equal2. apply f_equal.
    rewrite VlastS_nth. apply Vnth_eq. auto. do 2 rewrite Vnth_tail.
    rewrite VlastS_nth. apply Vnth_eq. auto.
    rewrite RAL.move_neg2. rewrite RAL.Finv_inv. rewrite VlastS_tail.
    do 2 rewrite <- Rmul_assoc. apply f_equal. apply Rmul_comm. 
    rewrite RAL.move_neg2. rewrite RAL.Finv_inv. rewrite Rmul_comm. 
    do 2 rewrite <- Rmul_assoc. apply f_equal. apply Rmul_comm.
    rewrite VlastS_tail. rewrite Rmul_comm. do 2 rewrite Rmul_assoc.
    apply f_equal2. symmetry. rewrite Rmul_comm. rewrite Rmul_assoc.
    apply f_equal2. rewrite Vbuild_remove_last. rewrite VlastS_build.
    rewrite Rmul_comm. unfold VF_prod. rewrite <- Vfold_left_Vadd_Fmul.
    rewrite le_sub_eq_last. rewrite H1. trivial. trivial. trivial.
    
    (* we have now discharges the tail now we need the body *)
    do 3 rewrite Vbuild_nth. do 2 rewrite Vmap2_remove_last. do 3 rewrite <- Vtail_map2.
    do 3 rewrite Vnth_map2. unfold FSemiRingT.Aplus. do 3 rewrite Rdistr_l. 
    do 3 rewrite H2. rewrite H3.
     rewrite RAL.move_neg2. apply f_equal2. apply f_equal.
    rewrite Vnth_remove_last. apply Vnth_eq. trivial. do 4 rewrite Vnth_tail.
    rewrite Vnth_remove_last.  apply Vnth_eq. trivial.  

    apply Rmul_comm. rewrite RAL.move_neg2.
    rewrite RAL.Finv_inv. rewrite Vmap_remove_last. rewrite Vnth_map.
    rewrite Rmul_comm. rewrite Rmul_assoc. apply f_equal2. 
    rewrite Vremove_last_Vtail. apply Rmul_comm. trivial. rewrite RAL.move_neg2.
    rewrite RAL.Finv_inv. rewrite Vmap_remove_last. do 2 rewrite Vtail_map.
    rewrite Vnth_map. rewrite Rmul_assoc. apply f_equal2. apply Rmul_comm.
    trivial. do 2 rewrite Vmap_remove_last. do 3 rewrite Vtail_map. 
    do 3 rewrite Vnth_map. do 2 rewrite Rmul_assoc. apply f_equal2. rewrite Rmul_comm.
    symmetry. rewrite Rmul_comm. rewrite Rmul_assoc. apply f_equal2. 
    do 4 rewrite Vnth_tail. do 3 rewrite Vnth_remove_last. rewrite Vnth_tail.
    rewrite Vnth_remove_last. do 2 rewrite Vbuild_nth. unfold VF_prod.
    rewrite Rmul_comm. rewrite <- Vfold_left_Vadd_Fmul. apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_add. destruct (Nat.eq_dec i0 (S (S i))).
    rewrite Vnth_sub. apply Vnth_eq. lia. do 2 rewrite Vnth_sub. 
    apply Vnth_eq. lia. trivial.
    trivial.
    (* c delta randomness *)
    ++++ field.
    ++++ rewrite H. rewrite Vmap_remove_last. trivial.
    ++++ apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_const. field. 
    (* c Delta *)
    +++ do 2 rewrite Prod_right_replace. rewrite <- trapdoorEPC. trivial.
    rewrite H. rewrite Vmap_remove_last. trivial.
    (* Proving challenges are equal *)
    ++ do 2 rewrite Prod_right_replace. trivial.
    ++ do 2 rewrite Prod_right_replace. apply injective_projections. 
    apply injective_projections. apply injective_projections.
    do 4 rewrite Prod_left_replace. trivial. do 2 rewrite Prod_right_replace. 
    apply Veq_nth. intros. rewrite Vnth_map2. remember vecb as d. do 2 rewrite Vnth_cons.
    destruct (lt_ge_dec 0 i). do 2 rewrite Vnth_add. destruct (Nat.eq_dec (i - 1) (S Hack.N)).
    rewrite Vnth_map. rewrite Heqd. rewrite Vbuild_nth. rewrite le_sub_eq_gen.
    unfold n. lia.
    intros.
    unfold VF_prod. rewrite <- Vfold_left_cast. rewrite H1. unfold VF_prod,
    FSemiRingT.Aplus. field.  rewrite Vnth_map2.
    apply f_equal2. do 2 rewrite Vnth_map. apply f_equal2. rewrite Vnth_tail. 
    rewrite Vnth_remove_last. apply Vnth_eq. lia. trivial. trivial. rewrite Vhead_nth.
    rewrite Vhead_map2. assert (i = 0%nat). lia. subst. apply f_equal2. rewrite Vnth_map.
    rewrite Vbuild_nth. unfold VF_prod. rewrite Vfold_left_head. intros.
    rewrite Vhead_sub. rewrite Vhead_map. trivial. intros. field.
    rewrite Vhead_nth. apply Vnth_eq.
    trivial. do 2 rewrite Prod_right_replace. 
    trivial. do 2 rewrite Prod_right_replace. 
    trivial.
    
    (* Bijection *)
    + split.
    ++ unfold simMapInv, simMap.  apply injective_projections. 
    apply injective_projections. apply injective_projections. apply injective_projections.
    +++ do 8 rewrite Prod_left_replace. rewrite VF_sub_corr. rewrite VF_add_ass. 
    apply VF_add_neg3. 
    +++ do 2 rewrite Prod_right_replace. field.
    +++ do 2 rewrite Prod_right_replace. rewrite VF_sub_corr. rewrite VF_add_ass. 
    apply VF_add_neg3. 
    +++ do 2 rewrite Prod_right_replace. assert (forall a b c d e, d = e ->
     a*b+c-a*(b+d-e)=c). intros. subst. field. apply H2. apply f_equal.
    apply Vcons_eq_intro. do 2 rewrite VF_sub_corr. do 2 rewrite VF_add_ass. 
    do 2 rewrite VF_add_neg3. trivial. apply f_equal2. apply Veq_nth. intros.
    do 2 rewrite Vbuild_nth. do 2 rewrite VF_sub_corr. do 2 rewrite VF_add_ass. 
    do 2 rewrite VF_add_neg3. trivial. do 2 rewrite VF_sub_corr. do 2 rewrite VF_add_ass. 
    do 2 rewrite VF_add_neg3. trivial.
    +++ do 2 rewrite Prod_right_replace. assert (forall a b c, b= c ->
     a+b-c=a). intros. subst. field. apply H2. apply f_equal.
    apply Vcons_eq_intro. do 2 rewrite VF_sub_corr. do 2 rewrite VF_add_ass. 
    do 2 rewrite VF_add_neg3. trivial. apply f_equal2. apply Veq_nth. intros.
    do 2 rewrite Vbuild_nth. do 2 rewrite VF_sub_corr. do 2 rewrite VF_add_ass. 
    do 2 rewrite VF_add_neg3. trivial. do 2 rewrite VF_sub_corr. do 2 rewrite VF_add_ass. 
    do 2 rewrite VF_add_neg3. trivial.
    (* Other direction *)
    ++ unfold simMapInv, simMap.  apply injective_projections. 
    apply injective_projections. apply injective_projections. apply injective_projections.
    +++ do 8 rewrite Prod_left_replace. rewrite VF_sub_corr. rewrite VF_add_neg3.
    trivial.
    +++ do 2 rewrite Prod_right_replace.  field.
    +++ do 2 rewrite Prod_right_replace.  rewrite VF_sub_corr. rewrite VF_add_neg3.
    trivial.
    +++ do 2 rewrite Prod_right_replace. assert (forall a b c, a = c -> a+(b-c)=b).
    intros. subst. field. apply H2. trivial.
    +++ do 2 rewrite Prod_right_replace. assert (forall a b c, a = c -> b-a+c=b).
    intros. subst. field. apply H2. trivial.
  Qed.

  Lemma simulator_correct : forall (s : St)(t : TE)(e : F),
    V1(simulator s t e) = true.
  Proof.
    pose module_abegrp.
    intros. unfold V1, simulator.  destruct s. destruct p. destruct p. 
    destruct t. destruct p. destruct p. destruct p. apply andb_true_iff.
    split. apply andb_true_iff. split. apply andb_true_iff. split. 
    + apply bool_eq_corr. rewrite Prod_right_replace. rewrite comm.
    rewrite <- dot_assoc. rewrite <- inv_left. apply one_right.
    + apply bool_eq_corr. rewrite Prod_right_replace. rewrite EPCfall.
    rewrite comm. rewrite <- dot_assoc. rewrite <- RAL.move_neg2.
    rewrite <- neg_eq. rewrite <- mod_dist_FMul2. rewrite <- inv_left. 
    rewrite one_right. apply f_equal2.
    ++ apply Vcons_eq_elim_gen. split.
    +++ rewrite Vhead_map2. do 2 rewrite Vhead_map. rewrite Vtail_cons. 
    rewrite Vhead_map2. rewrite Vhead_Vadd. rewrite Vhead_Vremove_last.
    rewrite Vhead_cons. unfold FSemiRingT.Aplus. apply f_equal2. field.
    trivial. 
    +++ apply Vadd_eq_elim_gen. split.
    ++++ rewrite VlastS_tail. rewrite VlastS_map2. do 2 rewrite VlastS_map. 
    rewrite Vtail_cons. rewrite Vremove_last_cons. rewrite Vremove_last_add.
    rewrite VlastS_map2. rewrite VlastS_cons. rewrite VlastS_add. apply f_equal2.
    field. rewrite VlastS_tail. trivial.
    ++++ apply Veq_nth. intros. rewrite Vbuild_nth. unfold VF_sub, VF_add, FMatrix.VA.vector_plus.
    rewrite <- Vtail_map2. do 2 rewrite Vtail_map. rewrite Vmap2_remove_last.
    rewrite Vnth_map2. do 2 rewrite Vmap_remove_last. do 2 rewrite Vnth_map.
    unfold FSemiRingT.Aplus. apply f_equal2.
    +++++ rewrite Vtail_cons. rewrite Vremove_last_Vtail. rewrite Vremove_last_add.
    field.
    +++++ unfold VF_mult. rewrite <- Vtail_map2. rewrite Vmap2_remove_last.
    rewrite Vnth_map2. apply f_equal. apply f_equal2. rewrite Vremove_last_cons.
    rewrite Vremove_last_add. rewrite Vtail_cons. trivial. 
    do 2 rewrite Vremove_last_Vtail. trivial.
    ++ trivial.
    + apply F_bool_eq_corr. trivial.
    + apply F_bool_eq_corr. rewrite Prod_right_replace. rewrite VlastS_cons.
    rewrite VlastS_add. trivial.
  Qed.

End BGSingleProd.

Module BGSingleProdIns (Commitment : GroupSig)
    (Field : FieldSig)(VS2 : VectorSpaceSig Commitment Field)
    (Chal : GroupFromRing Field)(Hack : Nat) <: SigmaPlus Chal.

  (* N = nm *)
  Let n := S (S (S Hack.N)).      (* n *)
  Import Field.

  Module Mo := MatricesFieldIns Field.
  Import Mo.
  Import Mo.mat.

  (* Make commitment scheme and matrix *)
  Module EPC := ExtendComScheme Commitment Field VS2 mat.
  Import EPC.
  Import EPC.MoM.
  Module PC := BasicComScheme Commitment Field VS2 mat.
  Import PC.

  Module HardProb := HardProblems Commitment Field VS2.
  Import HardProb.

  Import VS2.
  Import Commitment.

  Module RAL := RingAddationalLemmas Field.
  
  (* h hs c b *)
  Definition St : Type := G*(VG n)*G*F.
  
  (* a r *)
  Definition W : Type := (VF n)*F.
  Definition Rel (s : St)(w : W) : bool :=
    let '(h, hs, c, b) := s in
    let '(a, r) := w in
    Gbool_eq s.1.2 (EPC h hs a r) && Fbool_eq b (VF_prod a).
    
  Definition  C : Type := G*G*G.

  (* d, r, dleta, s1, sx *)
  Definition  R : Type := VF n*F*VF (S Hack.N)*F*F.
  
  (* a, b, r, s *)
  Definition T : Type := VF n*VF n*F*F.

  Definition vecb (a : VF n) : VF n := Vbuild (fun i (ip : i < n) =>
      VF_prod (Vsub a (le_sub ip) )).

  Lemma vecb_head : forall (a : VF n),
    Vhead (vecb a) = Vhead a.
  Proof.
    intros. rewrite Vbuild_head. unfold VF_prod.
    rewrite Vfold_left_head. rewrite Vhead_sub. trivial.  intros. field.
  Qed.

  Definition P0 (s : St)(r : R)(w : W) : (St*C) :=
    let '(h, hs, c, b) := s in
    let '(d, randr, delta, s1, sx) := r in
    let '(a, witr) := w in
    let delta1 := Vhead d in
    let deltan := 0 in

    (s, (EPC h hs d randr,
    (* EPC (-delta_1 * d_2, ...., - delta_(n-1) * d_n *)
    EPC h (Vremove_last hs) (Vcons (Finv delta1 * Vhead(Vtail d))
    (Vbuild (fun i (ip : i < S Hack.N) => Finv (Vnth delta ip) * Vnth (Vtail (Vtail d)) ip)))
   s1,
    (* EPC (delta_2-a_2*delta_1-b_1*d_2, ...., detlta_n-a_n*delta_(n-1)-b_(n-1)*d_n *)
    EPC h (Vremove_last hs)
    (Vcons
      (Vhead delta - Vhead (Vtail a)*delta1-(Vhead (vecb a))*Vhead(Vtail d))
    (Vadd (Vbuild (fun i (ip : i < Hack.N) =>
    Vnth (Vtail delta) ip - Vnth (Vtail (Vtail (Vremove_last a))) ip * Vnth (Vremove_last delta) ip -
      Vnth (Vtail (Vremove_last (Vremove_last (vecb a)))) ip * Vnth (Vtail (Vtail (Vremove_last d))) ip))
    (Finv (VlastS a) * VlastS delta - VlastS (Vremove_last (vecb a)) * VlastS d))
    ) sx)).
   

  Definition P1 (sce : St*C*F)(r : R)(w : W): (St*C*F*T) :=
    let '(d, rd, delta, s1, sx) := r in
    let '(a, r) := w in
    (* a b r s *)
    (sce,
    (VF_add (VF_scale a sce.2) d,
    VF_add (VF_scale (vecb a) sce.2) (Vcons (Vhead d) (Vadd delta 0)),
    sce.2*r + rd,
    sce.2*sx + s1)).
      
  Definition V1 (scet : St*C*F*T) : bool :=
    let '(h, hs, c, b) := scet.1.1.1 in
    let '(cd, cdelta, cDelta) := scet.1.1.2 in
    let '(a, bvec, r, s) := scet.2 in
    let x := scet.1.2 in

    Gbool_eq (c^x o cd) (EPC h hs a r) &&
    Gbool_eq (cDelta^x o cdelta) (EPC h
          (Vremove_last hs) (VF_sub (VF_scale (Vtail bvec) x)
                            (VF_mult (Vremove_last bvec) (Vtail a))) s) &&
    Fbool_eq (Vhead bvec) (Vhead a) &&
    Fbool_eq (VlastS bvec) (x*b).

   Definition TE : Type := VF n*F*VF (S Hack.N)*F*F.
   Definition X  : Type := VF n.
   Definition simMapHelp (s : St)(x : X) : Prop :=
    let '(h, hs, c, b) := s in

    hs = Vmap (op h) x.
                                       
   Definition simulator (s : St)(t : TE)(x : F) : (St*C*F*T) :=
    let '(h, hs, c, b) := s in
    let '(d, randr, delta, s1, sx) := t in
  
      (s, (EPC h hs d randr o - c^x,
          EPC h
          (Vremove_last hs)
        (Vcons (x * (Vhead delta) - (Vhead d) * (Vhead (Vtail d)))
        (Vadd (Vbuild (fun i (ip : i < Hack.N) => x*(Vnth (Vtail delta) ip) -
       Vnth (Vremove_last delta) ip * Vnth (Vtail (Vtail (Vremove_last d))) ip))
        (x * x * b - (VlastS delta) * (VlastS d)))) s1 o h^(Finv sx*x),
          EPC h (Vremove_last hs) (VF_zero (S (S Hack.N))) sx),
         x, (d,(Vcons (Vhead d) (Vadd delta (x*b))),randr,s1)).

   Definition simMap    (s : St)(w : W)(x : F)(xx : X)(r : R) : TE :=
    let '(h, hs, c, b) := s in
    let '(a, witr) := w in
    let '(d, randr, delta, s1, sx) := r in
    let delta1 := Vhead d in
    let deltan := 0 in

    (VF_add (VF_scale a x) d, x*witr+randr, VF_add (VF_scale
      (Vtail (Vremove_last (vecb a))) x)
     delta,
    x*sx+s1,
    (* We compress the message of cDelta into the randomness *)
    sx+VF_inProd (Vremove_last xx) (Vcons
      (Vhead delta - Vhead (Vtail a)*delta1-(Vhead (vecb a))*Vhead(Vtail d))
    (Vadd (Vbuild (fun i (ip : i < Hack.N) =>
    Vnth (Vtail delta) ip - Vnth (Vtail (Vtail (Vremove_last a))) ip * Vnth (Vremove_last delta) ip -
      Vnth (Vtail (Vremove_last (Vremove_last (vecb a)))) ip * Vnth (Vtail (Vtail (Vremove_last d))) ip))
    (Finv (VlastS a) * VlastS delta - VlastS (Vremove_last (vecb a)) * VlastS d))
    )).

   Definition simMapInv (s : St)(w : W)(x : F)(xx : X)(t : TE) : R :=
    let '(h, hs, c, b) := s in
    let '(a, witr) := w in
    let '(d, randr, delta, s1, sx) := t in


    let org_d := VF_sub d (VF_scale a x) in
    let org_r  := randr-x*witr in
    let org_delta := VF_sub delta (VF_scale (Vtail (Vremove_last (vecb a))) x) in
    let delta1 := Vhead org_d in
    let deltan := 0 in

    let org_sx := sx-VF_inProd (Vremove_last xx) (Vcons
      (Vhead org_delta - Vhead (Vtail a)*delta1-(Vhead (vecb a))*Vhead(Vtail org_d))
    (Vadd (Vbuild (fun i (ip : i < Hack.N) =>
    Vnth (Vtail org_delta) ip - Vnth (Vtail (Vtail (Vremove_last a))) ip * Vnth (Vremove_last org_delta) ip -
      Vnth (Vtail (Vremove_last (Vremove_last (vecb a)))) ip * Vnth (Vtail (Vtail (Vremove_last org_d))) ip))
    (Finv (VlastS a) * VlastS org_delta - VlastS (Vremove_last (vecb a)) * VlastS org_d))) in

    (org_d,org_r, org_delta, s1-x*org_sx,
     org_sx).

   Definition M : nat := 2.
   Definition extractor (t : vector T M)(e : vector F M) : W :=
    (VF_scale (VF_sub (Vhead t).1.1.1 (VlastS t).1.1.1)
    (FmulInv (Vhead e - VlastS e)), ((Vhead t).1.2-(VlastS t).1.2) * FmulInv
    (Vhead e-VlastS e)).
  
  (** We require the functions do not modifiy the previous transcript *)
  Lemma pres_p0 : forall (s : St)(r : R)(w : W), (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. destruct s. destruct p. destruct p. destruct r. destruct p.
    destruct p. destruct p. destruct w. unfold P0. rewrite Prod_right_replace.
    trivial.
  Qed.

  Lemma pres_p1 : forall (sce : St*C*F)(r : R)(w : W),
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Proof.
    intros. destruct sce. destruct p. destruct s. destruct p. destruct p.
    destruct r. destruct p. destruct p. destruct p. destruct w. unfold P1.
    rewrite Prod_right_replace. trivial.
  Qed.

  Lemma pres_sim : forall (s: St)(t : TE)(e : F),
      s = (simulator s t e).1.1.1.
  Proof.
    intros.  unfold simulator. destruct s. destruct p. destruct p.
    destruct t. destruct p. destruct p. destruct p. simpl. trivial.
  Qed.
  
  Lemma chal_sim : forall (s: St)(t : TE)(e : F),
    e = (simulator s t e).1.2.
  Proof.
    intros. unfold simulator. destruct s. destruct p. destruct p.
    destruct t. destruct p. destruct p. destruct p. simpl. trivial.
  Qed.

  (** Properties *)
  Lemma correctness : forall (s :St)(w:W)(r:R)(c: F),
    Rel s w ->
    V1 (P1 ((P0 s r w), c) r w) = true.
  Proof.
    pose module_abegrp. destruct vs_field. destruct F_R.
    intros. unfold V1, P1, P0. destruct s. destruct p. destruct p.
    destruct r. destruct p. destruct p. destruct p. destruct w.
    do 3 rewrite Prod_right_replace. rewrite Prod_left_replace.
    unfold Rel in *. apply andb_true_iff in H. destruct H.
    apply bool_eq_corr in H. apply F_bool_eq_corr in H0. simpl in H.
    apply andb_true_iff. split.  apply andb_true_iff. split.
    apply andb_true_iff. split.
    + (* First commit open *)
    apply bool_eq_corr. rewrite H. rewrite EPC_add. rewrite Rmul_comm.
    rewrite EPCExp. trivial.
    + (* Second commit open *)
    apply bool_eq_corr. rewrite <- EPCExp. rewrite <- EPC_add. apply f_equal2.
    (* This corresponses to line 4 of the paper proof *)
    ++ unfold VF_scale. rewrite Vcons_map. unfold VF_add, FMatrix.VA.vector_plus.
    rewrite Vcons_map2. apply Vcons_eq_elim_gen. split.
    (* Head case *)
    +++ rewrite Vhead_map2. unfold VF_neg. do 2 rewrite Vhead_map.
    rewrite <- Vtail_map2. do 2 rewrite Vhead_map2.
    rewrite Vhead_Vremove_last. do 2 rewrite Vhead_map2.
    rewrite Vtail_cons. do 2 rewrite Vhead_cons. unfold FSemiRingT.Aplus.
    do 3 rewrite Rdistr_l. rewrite Vhead_Vadd. rewrite <- Radd_0_l.
    do 2 rewrite Radd_assoc. apply RAL.cancel_1_3; auto. rewrite Radd_0_l.
    rewrite RAL.bi_exp. do 2 rewrite Vhead_cons. rewrite Vtail_map. rewrite Vhead_map.
    do 3 rewrite ALR.inv_dis. do 3 rewrite Radd_assoc.
    rewrite VF_prod_1_head. rewrite Vhead_sub.
    symmetry. do 2 rewrite <- Radd_assoc. assert (forall a b c, b = c ->
    a = 0 -> a + b = c). intros. rewrite H1. rewrite H2. ring.
    apply H1. rewrite Radd_assoc. apply f_equal2. rewrite Radd_comm. apply f_equal2.
    ring. do 2 rewrite move_neg. do 2 rewrite <- Rmul_assoc. apply f_equal2.
    trivial. apply Rmul_comm. rewrite Rmul_comm. rewrite move_neg. apply Rmul_comm.
    rewrite VF_prod_2_head.
    rewrite Vhead_sub. rewrite Vhead_tail_sub. ring.
    +++ rewrite Vadd_map. rewrite (VSn_addS (Vbuild
     (fun (i : nat) (ip : i < S Hack.N) => Finv (Vnth v0 ip) * Vnth (Vtail (Vtail v1)) ip))).
    rewrite Vadd_map2. apply Vadd_eq_elim_gen. split.
    (* Last *)
    ++++ rewrite VlastS_tail. rewrite VlastS_map2. do 2 rewrite VlastS_map.
         rewrite VlastS_tail. do 2 rewrite VlastS_map2. rewrite VlastS_tail.
         rewrite VlastS_build. rewrite Vmap2_remove_last. do 2 rewrite VlastS_map2.
    rewrite Vmap_remove_last. do 2 rewrite VlastS_map. unfold FSemiRingT.Aplus.
    rewrite (Vremove_last_cons (Vhead v1)). rewrite Vremove_last_add.
    do 2 rewrite (VlastS_cons (Vhead v1)). rewrite VlastS_map. rewrite VlastS_add.
    do 3 rewrite Rdistr_l. rewrite VlastS_build. rewrite le_sub_eq.
    assert (forall x y z, z * (x+y) = (z * x)+(z*y)). intros. field; auto.
    do 2 rewrite H1.  symmetry. do 3 rewrite RAL.inv_dis. rewrite <- Radd_0_l.
    do 5 rewrite Radd_assoc. symmetry. apply RAL.cancel_2_3. rewrite Rmul_assoc.
    rewrite <- Rmul_assoc. rewrite Rmul_comm. rewrite  <- move_neg. apply f_equal.
    rewrite Rmul_comm. rewrite Rmul_assoc. apply f_equal2; auto. symmetry.
    rewrite <- Radd_0_l. do 2 rewrite Radd_assoc. apply RAL.cancel_3_3.
    do 2 rewrite RAL.move_neg.
    do 2 rewrite <- Rmul_assoc. apply f_equal2; auto. do 2 rewrite Radd_0_l.
    assert (forall a b c, b = c -> a = 0 -> a + b = c). intros. rewrite H3.
    rewrite H2. ring. apply H2. rewrite Rmul_comm. rewrite RAL.move_neg.
    rewrite Rmul_comm. apply f_equal2. rewrite VlastS_nth. apply f_equal.
    apply Vnth_eq. trivial. rewrite VlastS_nth. do 2 rewrite Vnth_tail.
    apply Vnth_eq. trivial.
    rewrite VlastS_nth. rewrite Vnth_remove_last. rewrite Vbuild_nth.
    replace (0 * c) with 0. rewrite <- Radd_assoc. rewrite Radd_0_l.
    apply -> shift. rewrite Rmul_assoc. apply f_equal2. symmetry.
    rewrite Rmul_comm. rewrite Rmul_assoc. apply f_equal2. rewrite Rmul_comm.
    unfold VF_prod. rewrite <- Vfold_left_Vadd_Fmul. rewrite le_sub_eq_last.
    trivial. trivial. trivial. ring.
    (* Body *)
    ++++ apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_map.
    do 2 rewrite Vnth_remove_last. do 2 rewrite Vbuild_nth. symmetry.
    rewrite Vnth_tail. rewrite Vnth_map2. do 2 rewrite Vnth_map.
    rewrite <- Vtail_map2. rewrite (Vtail_cons (Vhead v1)). rewrite Vmap2_remove_last.
    rewrite (Vremove_last_cons (Vhead v1)). rewrite Vremove_last_add. symmetry.
    unfold FSemiRingT.Aplus. do 2 rewrite Vnth_map2. rewrite <- Vtail_map2.
    do 2 rewrite Vtail_map. do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map.
    assert (forall x y z, z * (x+y) = (z * x)+(z*y)). intros. field; auto.
    rewrite H1. do 5 rewrite Rdistr_l. do 5 rewrite <- Vnth_tail. rewrite Vtail_cons.
    do 5 rewrite <- Vnth_remove_last. do 5 rewrite Vremove_last_Vtail.
    rewrite Vremove_last_add. do 2 rewrite <- Vnth_remove_last.
    do 3 rewrite RAL.inv_dis. do 3 rewrite Radd_assoc. apply f_equal2.
    +++++ apply f_equal2.
    ++++++ apply f_equal2.
    +++++++ assert (forall a b c d, a = c -> b = d -> a = b + c - d). intros.
    rewrite H2. rewrite H3. ring. apply H2. trivial. do 2 rewrite Vnth_remove_last.
    do 5 rewrite Vnth_tail. do 2 rewrite Vnth_remove_last. rewrite Vnth_map.
    rewrite Rmul_assoc. apply f_equal2; auto. symmetry. rewrite Rmul_comm.
    rewrite Rmul_assoc. apply f_equal2; auto. do 2 rewrite Vbuild_nth.
    rewrite Rmul_comm. unfold VF_prod. rewrite <- Vfold_left_Vadd_Fmul.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_add.
    destruct (Nat.eq_dec i0 (S (S i))). rewrite Vnth_sub. apply Vnth_eq. rewrite e.
    lia. do 2 rewrite Vnth_sub. apply Vnth_eq. trivial.
    +++++++ rewrite RAL.move_neg. rewrite RAL.move_neg2. rewrite Rmul_assoc.
    apply f_equal2. rewrite Rmul_comm. apply f_equal2. trivial.
    rewrite Vnth_remove_last. do 2 rewrite Vnth_tail. rewrite Vnth_sub.
    apply Vnth_eq. trivial. trivial.
    ++++++ do 4 rewrite Vnth_tail. do 4 rewrite Vnth_remove_last.
    rewrite Vnth_tail. rewrite Vnth_remove_last. rewrite Vnth_map.
    do 3 rewrite RAL.move_neg2. rewrite Rmul_comm. rewrite Rmul_assoc.
    apply f_equal2. rewrite Rmul_comm. apply f_equal2.  apply f_equal.
    apply Vnth_eq. trivial. trivial. apply Vnth_eq. trivial.
    +++++ rewrite RAL.move_neg2. apply f_equal. do 3 rewrite Vnth_tail.
    rewrite Vnth_remove_last. apply Vnth_eq. trivial.
    ++ field.
    (* Remaining too *)
    + apply F_bool_eq_corr. do 2 rewrite Vhead_map2. do 2 rewrite Vhead_map.
    rewrite Vbuild_head. rewrite Vhead_cons. apply f_equal2; auto.
    unfold VF_prod. rewrite Vfold_left_head.
    rewrite Vhead_sub. trivial. intros; field.
    + apply F_bool_eq_corr. rewrite VlastS_map2. rewrite (VlastS_cons (Vhead v1)).
    rewrite VlastS_add. rewrite VlastS_map. rewrite VlastS_build.
    rewrite le_sub_eq. rewrite H0. unfold FSemiRingT.Aplus. rewrite Radd_comm.
    rewrite Radd_0_l. apply Rmul_comm.
  Qed.

  Definition Polynomial N (w u : VF (S N))(e : F)(a : VF N) : F.
      induction N. apply (e*Vhead w+Vhead u).
      apply ((IHN (Vremove_last w)(Vremove_last u)(Vremove_last a)) * VlastS a +
      (VF_prod (Vconst e (S (S N)))) * VlastS w +
      (VF_prod (Vconst e (S N))) * VlastS u).
  Defined.

  Lemma Polynomial_ind : forall N (w u : VF (S (S N)))(e : F)(a : VF (S N)),
    Polynomial w u e a =
    Polynomial (Vremove_last w)(Vremove_last u)e(Vremove_last a) * VlastS a +
      (VF_prod (Vconst e (S (S N))))*VlastS w+(VF_prod (Vconst e (S N)))* VlastS u.
  Proof.
    intros. simpl. trivial.
  Qed.

 Definition fail_event (s : St)(com : C)(e : vector F M) : Prop :=
    let '(h, hs, c, b) := s in
    let '(cd, cdelta, cDelta) := com in
   
    (exists a heada lasta r r' w u r'' r''',
    (* First we show that all the coefficents were commited to *)
    c = EPC h hs a ((r - r') / (Vhead e - VlastS e)) /\
    c ^ Vhead e o cd = EPC h hs heada r /\
    c ^ VlastS e o cd = EPC h hs lasta r' /\
    cdelta = EPC h (Vremove_last hs) u r'' /\
    cDelta = EPC h (Vremove_last hs) w r''' /\
    (* If the polynomial sampled at (Vhead e) is zero *)
    b * VF_prod (Vconst (Vhead e) n) = VF_prod (VF_add
      (VF_scale a (Vhead e - VlastS e)) lasta) +
      Polynomial w u (Vhead e) (Vtail (Vtail heada)) /\
    (* But the polynomial is not zero *)
      b <> VF_prod a).

   Definition allDifferent (e : vector F M) := PairwisePredicate Chal.Gdisjoint e.

  Lemma special_soundness : forall (s : St)(c : C)(e : vector F M)(t : vector T M),
    (* Forall e it is disjoint from all e *)
    allDifferent e ->
    bVforall2 (fun e1 t1 => V1 (s, c, e1, t1)) e t ->
    Rel s (extractor t e) = true \/ fail_event s c e.
  Proof.
    pose module_abegrp. destruct vs_field. destruct F_R.
    intros. unfold Rel, extractor. (* First we will get the verification equations unpacked *)
    destruct s as [p b]. destruct p as [p ca]. destruct p as [h hs].
    destruct c as [p cDelta]. destruct p as [cd cdelta].
    apply bVforall2_elim_2 in H0. destruct H0. unfold V1 in *.
    do 3 rewrite Prod_left_replace in H0. do 3 rewrite Prod_right_replace in H0.
    destruct (Vhead t) as [p heads]. destruct p as [p headr].
    destruct p as [heada headb]. apply andb_true_iff  in H0. destruct H0.
    apply andb_true_iff  in H0. destruct H0. apply andb_true_iff  in H0. destruct H0.
    apply bool_eq_corr in H0. do 3 rewrite Prod_left_replace in H1.
    do 3 rewrite Prod_right_replace in H1. destruct (VlastS t) as [p lasts].
    destruct p as [p lastr]. destruct p as [lasta lastb]. apply andb_true_iff in H1.
    destruct H1. apply andb_true_iff in H1. destruct H1. apply andb_true_iff in H1.
    destruct H1. apply bool_eq_corr in H1. apply PairwisePredict_2 in H.
    unfold Chal.Gdisjoint in H. apply negb_true_iff in H.
    apply F_bool_neq_corr in H. apply bool_eq_corr in H7. apply bool_eq_corr in H4.
    (* ca = EPC n h hs .... *)
    assert (ca = EPC h hs (VF_scale (VF_sub heada lasta)
    (FmulInv (Vhead e - VlastS e))) ((headr-lastr) * FmulInv
    (Vhead e-VlastS e))). rewrite EPCExp. unfold VF_sub. rewrite <- EPCMult.
    rewrite <- H0. rewrite <- EPCneg. rewrite <- H1. rewrite <- (inv_dist (dot:=Gdot)).
    unfold abegop. rewrite (comm (-ca ^ VlastS e)). rewrite dot_assoc.
    rewrite <- (dot_assoc (ca ^ Vhead e)). rewrite <- inv_right. rewrite one_right.
    rewrite neg_eq. rewrite <- mod_dist_Fadd. rewrite <- mod_dist_Fmul.
    symmetry. rewrite <- mod_id. apply f_equal. field. unfold not. intros.
    apply H. apply RAL.shift. trivial.
    (* c_Delta *)
    assert (cDelta = EPC h (Vremove_last hs)
    (VF_scale (VF_add (VF_sub (VF_sub (VF_scale (Vtail headb) (Vhead e))
      (VF_mult (Vremove_last headb)  (Vtail heada)))
          (VF_scale (Vtail lastb) (VlastS e) )) (VF_mult (Vremove_last lastb) (Vtail lasta)))
    (FmulInv (Vhead e - VlastS e)))
       ((heads - lasts) / (Vhead e - VlastS e))).
    rewrite EPCExp.  unfold VF_sub in *. rewrite VF_add_ass. rewrite <- EPCMult.
    rewrite <- H4. rewrite (dob_neg (EPC h (Vremove_last hs)
     (VF_add (VF_neg (VF_scale (Vtail lastb) (VlastS e)))
        (VF_mult (Vremove_last lastb) (Vtail lasta))) (Finv lasts))).
   rewrite EPCneg. rewrite VF_neg_move. rewrite VF_neg_neg. rewrite RAL.Finv_inv.
    rewrite <- H7. pose (inv_dist (A:=G)). rewrite <- e0. pose (commHack (A:=G)(dot:=Gdot)).
    unfold abegop  in e1. rewrite e1. rewrite <- inv_right. rewrite one_right.
    rewrite neg_eq. rewrite <- mod_dist_Fadd. rewrite <- mod_dist_Fmul.
    assert (forall g a, a = 1 -> g^a = g). intros. subst. rewrite  mod_id.
    trivial. rewrite H9. trivial. field. unfold not. intros. apply H.
    apply shift; auto. auto.
    (* c_delta *)
    assert (cdelta = EPC h (Vremove_last hs) (VF_add
          (VF_sub (VF_scale (Vtail headb) (Vhead e))
             (VF_mult (Vremove_last headb) (Vtail heada)))
          (VF_scale
             (VF_scale
                (VF_add
                   (VF_sub
                      (VF_sub (VF_scale (Vtail headb) (Vhead e))
                         (VF_mult (Vremove_last headb) (Vtail heada)))
                      (VF_scale (Vtail lastb) (VlastS e)))
                   (VF_mult (Vremove_last lastb) (Vtail lasta)))
                (FmulInv (Vhead e - VlastS e))) (Finv (Vhead e))))
       (heads + (heads - lasts) / (Vhead e - VlastS e) * Finv (Vhead e))).
    rewrite H9 in H4. rewrite EPCExp in H4. assert (forall a b c, a o b = c ->
    b = c o - a). intros. rewrite <- H10. rewrite comm. rewrite dot_assoc.
    rewrite <- inv_left. rewrite one_left. trivial. apply H10 in H4.
    rewrite neg_eq in H4. do 2 rewrite <- EPCExp in H4. rewrite EPCMult in H4. trivial.
    remember (VF_scale
          (VF_add
             (VF_sub
                (VF_sub (VF_scale (Vtail headb) (Vhead e))
                   (VF_mult (Vremove_last headb) (Vtail heada)))
                (VF_scale (Vtail lastb) (VlastS e)))
             (VF_mult (Vremove_last lastb) (Vtail lasta)))
          (FmulInv (Vhead e - VlastS e))) as w. remember (VF_add
           (VF_sub (VF_scale (Vtail headb) (Vhead e))
              (VF_mult (Vremove_last headb) (Vtail heada)))
           (VF_scale w (Finv (Vhead e)))) as u.
    (* Now ready to prove that xb_i = b_i-1 a_i + x w_i + u_i *)
    assert (VF_scale (Vtail headb) (Vhead e) = VF_add (VF_add
        (VF_mult (Vremove_last headb) (Vtail heada)) (VF_scale w (Vhead e))) u).
    rewrite Hequ. rewrite Heqw. assert (forall a b c d : VF (S (S Hack.N)), c = VF_neg d
    -> a = VF_add (VF_add b c) (VF_add (VF_sub a b) d)). intros. rewrite H11.
    rewrite VF_comm_hack. rewrite VF_sub_corr. rewrite VF_add_neg3.
    rewrite <- VF_add_ass. rewrite VF_add_neg2. trivial. apply H11.
    apply Veq_nth. intros. do 5 rewrite Vnth_map. do 4 rewrite Vnth_map2.
    do 3 rewrite Vnth_map. unfold FSemiRingT.Aplus. rewrite move_neg.
    apply f_equal2. trivial. rewrite RAL.Finv_inv. trivial.
    (* assert x^n b = prod a_i + .... *)
    assert (Vhead e * b * VF_prod (Vconst (Vhead e) (S (S Hack.N))) =
      VF_prod heada + (Polynomial w u (Vhead e) (Vtail (Vtail heada)))).
    apply F_bool_eq_corr in H2. rewrite <- H2.
    assert (VlastS headb * VF_prod (Vconst (Vhead e) (S (S Hack.N)))
      = Vhead headb * VF_prod (Vtail heada) + (Polynomial w u (Vhead e)
         (Vtail (Vtail heada)))).
    + clear H10. clear Hequ H9 Heqw H8 H5 H7 H4 H1 H2 H6 H0 H H3.
    clear h hs ca b cd cdelta cDelta lasta lastb lastr lasts. unfold n in *.
    induction (S Hack.N). apply VlastS_intro in H11.
    rewrite VlastS_map in H11. rewrite VlastS_tail in H11. unfold VF_prod, VF_sum.
    rewrite Vfold_left_head. intros.  rewrite Vfold_left_head. intros.
    simpl. rewrite H11. do 2 rewrite VlastS_map2. unfold FSemiRingT.Aplus.
    rewrite Radd_assoc. apply f_equal2. apply f_equal2. rewrite VlastS_map2.
    rewrite VlastS_remove_last_2. rewrite VlastS_Vhead. trivial. rewrite VlastS_Vhead.
    trivial. rewrite VlastS_map. apply Rmul_comm. rewrite VlastS_Vhead. trivial.
    intros; field. intros; field.
    (* Starting induction step. *)
    apply Veq_elim_gen2 in H11. destruct H11. rewrite VlastS_map in H.
    rewrite VlastS_tail in H. unfold VF_prod. rewrite Vconst_cons.
    rewrite Vfold_left_Vcons_Fmul.  rewrite <- (Rmul_comm (Vhead e)).
    rewrite Rmul_assoc. rewrite H. do 3 rewrite VlastS_map2. unfold FSemiRingT.Aplus.
    do 2 rewrite Rdistr_l. assert (forall a b c, a *b*c = a*c*b). intros. field.
    rewrite H1. rewrite (IHn0 (Vremove_last heada) (Vremove_last headb)
                           (Vremove_last w) (Vremove_last u)).
    (* We are in the induction step cleaning up *)
    rewrite Vhead_Vremove_last. rewrite Rdistr_l.
    do 2 rewrite <- Radd_assoc. apply f_equal2. rewrite <- Rmul_assoc.
    unfold VF_prod. rewrite <- Vfold_left_Vadd_Fmul. rewrite <- Vremove_last_Vtail.
    rewrite <- VSn_addS. trivial.
    (* Need to show the polynomails are equal *)
    symmetry. rewrite Polynomial_ind. rewrite <- Radd_assoc. apply f_equal2.
    do 2 rewrite Vremove_last_Vtail. rewrite VlastS_tail. trivial.
    rewrite VlastS_map. apply f_equal2. rewrite H1. rewrite <- Rmul_assoc.
    rewrite <- Vfold_left_Vcons_Fmul. apply Rmul_comm. apply Rmul_comm.
     rewrite Vmap_remove_last in H0.
    rewrite Vremove_last_Vtail in H0. unfold VF_scale. rewrite H0.
    do 3 rewrite Vmap2_remove_last. apply f_equal2; auto.
    rewrite Vmap_remove_last. apply f_equal2; auto. rewrite Vremove_last_Vtail.
    trivial.
    (* Now we can finally prove the main lemma that x^n b = prod a_i + .... *)
    + rewrite H12. apply F_bool_eq_corr in H3. rewrite H3. apply f_equal2.
    rewrite Rmul_comm. unfold VF_prod. rewrite <- Vfold_left_Vcons_Fmul.
    rewrite <- VSn_eq. trivial. trivial.
    (* Start main relationship *)
    + assert (heada = VF_add
      (VF_scale (VF_scale (VF_sub heada lasta) (FmulInv (Vhead e - VlastS e)))
      (Vhead e - VlastS e)) lasta). rewrite VF_scale_scale. rewrite VF_scale_1_gen.
     rewrite VF_sub_corr.
     rewrite VF_add_neg2. trivial.
     field. unfold not. intros. apply H. apply shift. trivial.

     remember (Vtail heada) as c.
      rewrite H13 in H12. rewrite Heqc in H12.
    case_eq (Fbool_eq b (VF_prod (VF_scale (VF_sub heada lasta)
    (FmulInv (Vhead e - VlastS e))))); intros.
    ++ apply F_bool_eq_corr in H14. left. apply andb_true_iff. split.
    apply bool_eq_corr. apply H8. apply F_bool_eq_corr. trivial.
    ++ right. apply F_bool_neq_corr in H14. unfold fail_event.
    exists (VF_scale (VF_sub heada lasta) (FmulInv (Vhead e - VlastS e))).
    exists heada. exists lasta. exists headr. exists lastr. exists w. exists u.
    exists (heads + (heads - lasts) / (Vhead e - VlastS e) * (Finv (Vhead e))).
    exists ((heads - lasts) / (Vhead e - VlastS e)). split. rewrite H8. trivial.
    split; auto. split; auto. split; auto. split; auto. split; auto. rewrite <-
    H12. rewrite <- Rmul_assoc. symmetry. rewrite Rmul_comm. rewrite <- Rmul_assoc.
    unfold VF_prod. rewrite <- Vfold_left_Vcons_Fmul. trivial.
  Qed.

  Lemma honest_verifier_ZK :
    forall (s : St)(w : W)(e : F)(x : X)(r : R)(t : TE),
      simMapHelp s x ->
      Rel s w ->
      ((P1((P0 s r w), e) r w) =
      simulator s (simMap s w e x r) e) /\
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.
  Proof.
    pose module_abegrp. destruct vs_field. destruct F_R.
    intros. destruct s. destruct p. destruct p.
    destruct t. destruct p. destruct p. destruct p. destruct w.
    destruct r. destruct p.  destruct p. destruct p. unfold Rel in H0.
    apply andb_true_iff in H0. destruct H0. apply bool_eq_corr in H0.
    apply F_bool_eq_corr in H1. split.
    + (*Time to prove simulator produces the same things *)
    unfold P1, P0, simulator, simMap. rewrite Prod_right_replace.
    apply injective_projections. apply injective_projections.
    apply injective_projections.
    ++ do 2 rewrite Prod_left_replace. trivial.
    (* Proving commitments are equal *)
    ++ do 2 rewrite Prod_right_replace. apply injective_projections.
       apply injective_projections.
    (* cd *)
    +++ do 4 rewrite Prod_left_replace. rewrite <- EPCMult. rewrite Rmul_comm.
    rewrite EPCExp. rewrite <- H0. rewrite Prod_right_replace. rewrite comm.
    rewrite dot_assoc. rewrite <- inv_left. rewrite one_left. trivial.
    (* c delta *)
    +++ do 2 rewrite Prod_right_replace. do 3 rewrite Vhead_map2.
    do 2 rewrite Vhead_map. do 2 rewrite VlastS_map2. do 2 rewrite VlastS_map.
    unfold FSemiRingT.Aplus. rewrite <- (EPCfall g0 (Vremove_last v)).
    rewrite <- VF_neg_zero. do 3 rewrite <- RAL.move_neg2. rewrite <- EPCneg.
    replace (VF_zero (S (S Hack.N))) with (VF_scale (VF_zero (S (S Hack.N))) e).
    rewrite EPCExp. rewrite <- trapdoorEPC. rewrite <- EPCExp.
    rewrite EPCneg. rewrite EPCMult. apply f_equal2.
    (*  c delta message  *)
    ++++  unfold VF_scale, VF_neg, VF_add, FMatrix.VA.vector_plus.
     do 2 rewrite Vcons_map. rewrite Vcons_map2.
    assert (forall a b c, a * ( b + c) = a*b+a*c). intros. field.
    assert (forall a b c d e f g h i , b = g -> d = Finv i -> e = Finv h ->
      a = c ->
    a + b - (c + d + (e + f)) - (g + h + i) =  Finv f). intros. subst. field.
    apply Vcons_eq_intro.
    (* Proving the first part of the c delta message *)
    +++++ do 3 rewrite Rdistr_l. do 3 rewrite H2. unfold FSemiRingT.Aplus.
    rewrite H3; trivial. rewrite vecb_head. rewrite RAL.move_neg2.
    rewrite RAL.Finv_inv. rewrite Rmul_comm. rewrite Rmul_assoc. apply f_equal2.
    apply Rmul_comm. trivial. rewrite RAL.move_neg2. rewrite Vtail_map.
    rewrite Vhead_map. rewrite RAL.Finv_inv. rewrite Rmul_assoc. apply f_equal2.
    apply Rmul_comm. trivial. rewrite Vtail_map. rewrite Vhead_map.
    do 2 rewrite Rmul_assoc. apply f_equal2. rewrite Vbuild_remove_last.
    rewrite Vbuild_tail. rewrite Vbuild_head. rewrite VF_prod_2_head.
    rewrite Vhead_sub. rewrite Vhead_tail_sub. rewrite Rmul_comm.
    do 2 rewrite <- Rmul_assoc. apply f_equal. apply Rmul_comm.  trivial.
    (* proving the second part of the c delta message *)
    +++++ apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vnth_map.
    do 2 rewrite Vnth_add. destruct (Nat.eq_dec i Hack.N). rewrite Vbuild_nth.
    do 2 rewrite Rdistr_l. do 2 rewrite H2. unfold FSemiRingT.Aplus.
    assert (forall a c d e f h i, d = Finv i -> e = Finv h ->
      a = c ->
      a - (c + d + (e + f)) - (h + i) =  Finv f). intros. subst. field.
    rewrite H4. rewrite RAL.move_neg2. apply f_equal2. apply f_equal.
    rewrite VlastS_nth. apply Vnth_eq. auto. do 2 rewrite Vnth_tail.
    rewrite VlastS_nth. apply Vnth_eq. auto.
    rewrite RAL.move_neg2. rewrite RAL.Finv_inv. rewrite VlastS_tail.
    do 2 rewrite <- Rmul_assoc. apply f_equal. apply Rmul_comm.
    rewrite RAL.move_neg2. rewrite RAL.Finv_inv. rewrite Rmul_comm.
    do 2 rewrite <- Rmul_assoc. apply f_equal. apply Rmul_comm.
    rewrite VlastS_tail. rewrite Rmul_comm. do 2 rewrite Rmul_assoc.
    apply f_equal2. symmetry. rewrite Rmul_comm. rewrite Rmul_assoc.
    apply f_equal2. rewrite Vbuild_remove_last. rewrite VlastS_build.
    rewrite Rmul_comm. unfold VF_prod. rewrite <- Vfold_left_Vadd_Fmul.
    rewrite le_sub_eq_last. rewrite H1. trivial. trivial. trivial.
    
    (* we have now discharges the tail now we need the body *)
    do 3 rewrite Vbuild_nth. do 2 rewrite Vmap2_remove_last. do 3 rewrite <- Vtail_map2.
    do 3 rewrite Vnth_map2. unfold FSemiRingT.Aplus. do 3 rewrite Rdistr_l.
    do 3 rewrite H2. rewrite H3.
     rewrite RAL.move_neg2. apply f_equal2. apply f_equal.
    rewrite Vnth_remove_last. apply Vnth_eq. trivial. do 4 rewrite Vnth_tail.
    rewrite Vnth_remove_last.  apply Vnth_eq. trivial.

    apply Rmul_comm. rewrite RAL.move_neg2.
    rewrite RAL.Finv_inv. rewrite Vmap_remove_last. rewrite Vnth_map.
    rewrite Rmul_comm. rewrite Rmul_assoc. apply f_equal2.
    rewrite Vremove_last_Vtail. apply Rmul_comm. trivial. rewrite RAL.move_neg2.
    rewrite RAL.Finv_inv. rewrite Vmap_remove_last. do 2 rewrite Vtail_map.
    rewrite Vnth_map. rewrite Rmul_assoc. apply f_equal2. apply Rmul_comm.
    trivial. do 2 rewrite Vmap_remove_last. do 3 rewrite Vtail_map.
    do 3 rewrite Vnth_map. do 2 rewrite Rmul_assoc. apply f_equal2. rewrite Rmul_comm.
    symmetry. rewrite Rmul_comm. rewrite Rmul_assoc. apply f_equal2.
    do 4 rewrite Vnth_tail. do 3 rewrite Vnth_remove_last. rewrite Vnth_tail.
    rewrite Vnth_remove_last. do 2 rewrite Vbuild_nth. unfold VF_prod.
    rewrite Rmul_comm. rewrite <- Vfold_left_Vadd_Fmul. apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_add. destruct (Nat.eq_dec i0 (S (S i))).
    rewrite Vnth_sub. apply Vnth_eq. lia. do 2 rewrite Vnth_sub.
    apply Vnth_eq. lia. trivial.
    trivial.
    (* c delta randomness *)
    ++++ field.
    ++++ rewrite H. rewrite Vmap_remove_last. trivial.
    ++++ apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_const. field.
    (* c Delta *)
    +++ do 2 rewrite Prod_right_replace. rewrite <- trapdoorEPC. trivial.
    rewrite H. rewrite Vmap_remove_last. trivial.
    (* Proving challenges are equal *)
    ++ do 2 rewrite Prod_right_replace. trivial.
    ++ do 2 rewrite Prod_right_replace. apply injective_projections.
    apply injective_projections. apply injective_projections.
    do 4 rewrite Prod_left_replace. trivial. do 2 rewrite Prod_right_replace.
    apply Veq_nth. intros. rewrite Vnth_map2. remember vecb as d. do 2 rewrite Vnth_cons.
    destruct (lt_ge_dec 0 i). do 2 rewrite Vnth_add. destruct (Nat.eq_dec (i - 1) (S Hack.N)).
    rewrite Vnth_map. rewrite Heqd. rewrite Vbuild_nth. rewrite le_sub_eq_gen.
    unfold n. lia.
    intros.
    unfold VF_prod. rewrite <- Vfold_left_cast. rewrite H1. unfold VF_prod,
    FSemiRingT.Aplus. field.  rewrite Vnth_map2.
    apply f_equal2. do 2 rewrite Vnth_map. apply f_equal2. rewrite Vnth_tail.
    rewrite Vnth_remove_last. apply Vnth_eq. lia. trivial. trivial. rewrite Vhead_nth.
    rewrite Vhead_map2. assert (i = 0%nat). lia. subst. apply f_equal2. rewrite Vnth_map.
    rewrite Vbuild_nth. unfold VF_prod. rewrite Vfold_left_head. intros.
    rewrite Vhead_sub. rewrite Vhead_map. trivial. intros. field.
    rewrite Vhead_nth. apply Vnth_eq.
    trivial. do 2 rewrite Prod_right_replace.
    trivial. do 2 rewrite Prod_right_replace.
    trivial.
    
    (* Bijection *)
    + split.
    ++ unfold simMapInv, simMap.  apply injective_projections.
    apply injective_projections. apply injective_projections. apply injective_projections.
    +++ do 8 rewrite Prod_left_replace. rewrite VF_sub_corr. rewrite VF_add_ass.
    apply VF_add_neg3.
    +++ do 2 rewrite Prod_right_replace. field.
    +++ do 2 rewrite Prod_right_replace. rewrite VF_sub_corr. rewrite VF_add_ass.
    apply VF_add_neg3.
    +++ do 2 rewrite Prod_right_replace. assert (forall a b c d e, d = e ->
     a*b+c-a*(b+d-e)=c). intros. subst. field. apply H2. apply f_equal.
    apply Vcons_eq_intro. do 2 rewrite VF_sub_corr. do 2 rewrite VF_add_ass.
    do 2 rewrite VF_add_neg3. trivial. apply f_equal2. apply Veq_nth. intros.
    do 2 rewrite Vbuild_nth. do 2 rewrite VF_sub_corr. do 2 rewrite VF_add_ass.
    do 2 rewrite VF_add_neg3. trivial. do 2 rewrite VF_sub_corr. do 2 rewrite VF_add_ass.
    do 2 rewrite VF_add_neg3. trivial.
    +++ do 2 rewrite Prod_right_replace. assert (forall a b c, b= c ->
     a+b-c=a). intros. subst. field. apply H2. apply f_equal.
    apply Vcons_eq_intro. do 2 rewrite VF_sub_corr. do 2 rewrite VF_add_ass.
    do 2 rewrite VF_add_neg3. trivial. apply f_equal2. apply Veq_nth. intros.
    do 2 rewrite Vbuild_nth. do 2 rewrite VF_sub_corr. do 2 rewrite VF_add_ass.
    do 2 rewrite VF_add_neg3. trivial. do 2 rewrite VF_sub_corr. do 2 rewrite VF_add_ass.
    do 2 rewrite VF_add_neg3. trivial.
    (* Other direction *)
    ++ unfold simMapInv, simMap.  apply injective_projections.
    apply injective_projections. apply injective_projections. apply injective_projections.
    +++ do 8 rewrite Prod_left_replace. rewrite VF_sub_corr. rewrite VF_add_neg3.
    trivial.
    +++ do 2 rewrite Prod_right_replace.  field.
    +++ do 2 rewrite Prod_right_replace.  rewrite VF_sub_corr. rewrite VF_add_neg3.
    trivial.
    +++ do 2 rewrite Prod_right_replace. assert (forall a b c, a = c -> a+(b-c)=b).
    intros. subst. field. apply H2. trivial.
    +++ do 2 rewrite Prod_right_replace. assert (forall a b c, a = c -> b-a+c=b).
    intros. subst. field. apply H2. trivial.
  Qed.

  Lemma simulator_correct : forall (s : St)(t : TE)(e : F),
    V1(simulator s t e) = true.
  Proof.
    pose module_abegrp.
    intros. unfold V1, simulator.  destruct s. destruct p. destruct p.
    destruct t. destruct p. destruct p. destruct p. apply andb_true_iff.
    split. apply andb_true_iff. split. apply andb_true_iff. split.
    + apply bool_eq_corr. rewrite Prod_right_replace. rewrite comm.
    rewrite <- dot_assoc. rewrite <- inv_left. apply one_right.
    + apply bool_eq_corr. rewrite Prod_right_replace. rewrite EPCfall.
    rewrite comm. rewrite <- dot_assoc. rewrite <- RAL.move_neg2.
    rewrite <- neg_eq. rewrite <- mod_dist_FMul2. rewrite <- inv_left.
    rewrite one_right. apply f_equal2.
    ++ apply Vcons_eq_elim_gen. split.
    +++ rewrite Vhead_map2. do 2 rewrite Vhead_map. rewrite Vtail_cons.
    rewrite Vhead_map2. rewrite Vhead_Vadd. rewrite Vhead_Vremove_last.
    rewrite Vhead_cons. unfold FSemiRingT.Aplus. apply f_equal2. field.
    trivial.
    +++ apply Vadd_eq_elim_gen. split.
    ++++ rewrite VlastS_tail. rewrite VlastS_map2. do 2 rewrite VlastS_map.
    rewrite Vtail_cons. rewrite Vremove_last_cons. rewrite Vremove_last_add.
    rewrite VlastS_map2. rewrite VlastS_cons. rewrite VlastS_add. apply f_equal2.
    field. rewrite VlastS_tail. trivial.
    ++++ apply Veq_nth. intros. rewrite Vbuild_nth. unfold VF_sub, VF_add, FMatrix.VA.vector_plus.
    rewrite <- Vtail_map2. do 2 rewrite Vtail_map. rewrite Vmap2_remove_last.
    rewrite Vnth_map2. do 2 rewrite Vmap_remove_last. do 2 rewrite Vnth_map.
    unfold FSemiRingT.Aplus. apply f_equal2.
    +++++ rewrite Vtail_cons. rewrite Vremove_last_Vtail. rewrite Vremove_last_add.
    field.
    +++++ unfold VF_mult. rewrite <- Vtail_map2. rewrite Vmap2_remove_last.
    rewrite Vnth_map2. apply f_equal. apply f_equal2. rewrite Vremove_last_cons.
    rewrite Vremove_last_add. rewrite Vtail_cons. trivial.
    do 2 rewrite Vremove_last_Vtail. trivial.
    ++ trivial.
    + apply F_bool_eq_corr. trivial.
    + apply F_bool_eq_corr. rewrite Prod_right_replace. rewrite VlastS_cons.
    rewrite VlastS_add. trivial.
  Qed.

End BGSingleProdIns.
