Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
From Groups Require Import groups module vectorspace 
    dualvectorspaces matrices matricesF matricesField modulevectorspace groupfromring.
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
Set Implicit Arguments.

(*                                              *)
(*  Proof of the zero arg from BG               *)

Module Type BGHadProd (Message Ciphertext Commitment : GroupSig)(Ring : RingSig)
    (Field : FieldSig)(VS2 : VectorSpaceSig Commitment Field)
    (VS1 : VectorSpaceSig Ciphertext Field)(Chal : GroupFromRing Field)
    (MVS : VectorSpaceModuleSameGroup Ciphertext Ring Field VS1)
    (VS3 : VectorSpaceSig Message Field)(Hack : Nat)(M : Nat)
    (enc : EncryptionSchemePlus Message Ciphertext Ring Field VS1 VS3 MVS)
    (support : BGSupport Message Ciphertext Commitment Ring Field VS2 VS1 MVS VS3 
    Hack M enc)(sig : BGZeroArg Message Ciphertext Commitment Ring Field VS2 VS1 Chal 
    MVS VS3 Hack M enc support) <: SigmaPlusTo5sim Chal sig. 

  Import sig.
  Import support.

  (* N = nm *)
  Let n := S (S (S Hack.N)).      (* n *)
  Let m := S (S M.N).     (* m *)
  Import Field.

  (*Module Mo := MatricesFieldIns Field.*)
  Import Mo.
  Import Mo.mat.
  (*Module MoR := MatricesFIns Ring.
  Module MoC := MatricesG Ciphertext Field VS1 mat.
  Module MoM := MatricesG Message Field VS3 mat.

  (* Make commitment scheme and matrix *)
  Module EPC := ExtendComScheme Commitment Field VS2 mat.*)
  Import EPC.
  Import EPC.MoM.
  (*Module PC := BasicComScheme Commitment Field VS2 mat. *)
  Import PC.

  (* Addational vector lemma *)
  (* Module ALVS1 := VectorSpaceAddationalLemmas Ciphertext Field VS1.
  Module ALVS2 := VectorSpaceAddationalLemmas Commitment Field VS2.
  Module ALVS3 := VectorSpaceAddationalLemmas Message Field VS3.

  Module ALenc := EncryptionSchemeProp Message Ciphertext Ring Field VS1 MVS enc. *)
  Import ALenc.
  (* Module HardProb := HardProblems Commitment Field VS2. *)
  Import HardProb.

  Module ALR := RingAddationalLemmas Ring.

  Import VS2.
  Import Commitment.

  Module G2 := GroupFromFieldIns Field. 

  Definition E := prod (G2.G) F.

  (* pk ck=(h,hs) C_A c_B *)
  Definition St : Type := G*VG n*VG m*G.

  (* A, r, B, s *)
  Definition W := prod (prod (prod (vector (VF n) m) (VF m)) (VF n)) F. 

  Definition Rel (s : St)(w : W) : bool := 
    let h   := s.1.1.1 in
    let hs  := s.1.1.2 in
    let CA  := s.1.2 in
    let cB  := s.2 in
    let A := w.1.1.1 in
    let r := w.1.1.2 in
    let B := w.1.2 in
    let s := w.2 in
      VG_eq CA (comEPC h hs A r) && 
      Gbool_eq cB (EPC h hs B s) &&
      VF_beq B (Vfold_left (@VF_mult n) (VF_one n) A).

  Definition C := VG M.N.                             

  Definition R := VF M.N. 

  Definition add (e1 e2 : E) := (G2.Gdot e1.1 e2.1,e1.2+e2.2).                  
  Definition zero := (G2.Gone,0). 
  Definition inv (e : E) := (G2.Ginv e.1, Finv e.2).
  Definition bool_eq (e1 e2 : E) := G2.Gbool_eq e1.1 e2.1 && Fbool_eq e1.2 e2.2.
  Definition disjoint  (e1 e2 : E) : bool := negb (G2.Gbool_eq e1.1 e2.1) &&
      negb (Fbool_eq e1.2 e2.2).

  Lemma IndexCB : forall i,
    i < M.N -> 0+(S (S i)) <= m.
  Proof.
    intros. unfold m. lia.
  Qed.

  Lemma IndexCB2 : forall i,
    i < S M.N -> 0+(S (S i)) <= m.
  Proof.
    intros. unfold m. lia.
  Qed.

  (* We don't send the redudent c_A1 c_b *)
  Definition P0 (st : St)(r : R)(w : W) : St*C  :=
    let h   := st.1.1.1 in
    let hs  := st.1.1.2 in
    let CA  := st.1.2 in
    let cB  := st.2 in
    let A := w.1.1.1 in
    let B := w.1.2 in
    let s := w.2 in 
    (st, comEPC h hs
      (Vbuild (fun i (ip: i < M.N) => 
      Vfold_left (@VF_mult n) (VF_one n) (Vsub A (IndexCB ip))))
    r).

  Definition ToSt (sce : St*C*E) : sig.St :=
    let s := sce.1.1 in
    let c := sce.1.2 in
    let e := sce.2 in 

    let h   := s.1.1.1 in
    let hs  := s.1.1.2 in
    let CA  := s.1.2 in
    let cB  := s.2 in
    let CB  := c in
    let x   := e.1 in
    let y   := e.2 in

    (* pk, ck, y, C_A, C_B *)
    (h,hs,y,(Vadd (Vtail CA) (EPC h hs (VF_neg (VF_one n)) 0)),
    (Vadd (VG_Pexp (Vcons (Vhead CA) CB) (Vtail (VandermondeCol m (sval x)))))
      (VG_prod (VG_Pexp (Vadd CB cB) (Vtail (VandermondeCol m (sval x)))))).

  Definition ToWit (sce : St*C*E)(r : R)(w : W) : sig.W :=
    let s   := sce.1.1 in
    let h   := s.1.1.1 in
    let hs  := s.1.1.2 in
    let CA  := s.1.2 in
    let cB  := s.2 in
    let CB  := sce.1.2 in
    let x   := sce.2.1 in
    let y   := sce.2.2 in
    let A  := w.1.1.1 in
    let r' := w.1.1.2 in
    let B := w.1.2 in
    let s := w.2 in 

    (Vadd (Vtail A) (VF_neg (VF_one n)), Vadd (Vtail r') 0, 
      Vadd (Vcons (VF_scale (Vhead A) (sval x)) 
        (Vmap2 (@VF_scale n) (Vbuild (fun i (ip: i < M.N) => 
        (Vfold_left (@VF_mult n) (VF_one n) (Vsub A (IndexCB ip))))) (Vtail (Vtail (VandermondeCol m (sval x))))))
       (Vfold_left (@VF_add n) (VF_zero n) (Vmap2 (@VF_scale n) (Vbuild (fun i (ip: i < S M.N) => 
        (Vfold_left (@VF_mult n) (VF_one n) (Vsub A (IndexCB2 ip))))) (Vtail (VandermondeCol m (sval x))))),
      Vadd (Vcons (Vhead r' * (sval x)) (VF_mult r (Vtail (Vtail (VandermondeCol m (sval x)))))) 
      (VF_sum (VF_mult (Vadd r s) (Vtail (VandermondeCol m (sval x)))))).

  Lemma ToValid : forall (s : St)(w : W)(r : R)(e : E),
    Rel s w ->
   sig.Rel (ToSt (P0 s r w, e)) (ToWit (P0 s r w, e) r w).
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.  
    pose Commitment.module_abegrp. 
    intros. unfold Rel, sig.Rel, ToSt, ToWit, P0 in *. do 2 rewrite Prod_left_replace. 
    do 2 rewrite Prod_right_replace.  apply andb_true_iff in H. destruct H. 
    apply andb_true_iff in H. destruct H.
    apply VGeq in H. apply bool_eq_corr in H1. apply VF_beq_true in H0. 
    apply andb_true_iff. split. apply andb_true_iff. split. apply VGeq.  
    rewrite H.  unfold comEPC. rewrite <- Vtail_map2. rewrite Vadd_map2. trivial.
    (* Second element of the realtionship *)
    + apply VGeq. rewrite H. rewrite H1. rewrite Vhead_map2. unfold comEPC.
    assert ((sval e.1) =  Vhead (Vtail (VandermondeCol m (sval e.1)))).
    rewrite Vhead_nth. 
    rewrite Vnth_tail. rewrite Vbuild_nth. simpl. rewrite VF_prod_1. trivial.
    rewrite <- Vadd_map2. rewrite <- Vcons_map2. unfold VG_Pexp. rewrite comEPCDis.
    apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_add.
    destruct (Nat.eq_dec i (S M.N)). 
    ++ rewrite comEPCDis. unfold VG_prod. rewrite <- EPCMultExt. apply f_equal2.
    apply f_equal. apply Veq_nth. intros. do 2 rewrite Vnth_map2. rewrite Vnth_add.
    destruct (Nat.eq_dec i0 M.N). rewrite Vbuild_nth. rewrite H0. apply f_equal2.
    subst. apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_sub.
    apply Vnth_eq. lia. trivial. apply f_equal2; trivial. do 2 rewrite Vbuild_nth.
    apply Vfold_left_eq. trivial. apply Veq_nth. intros. do 2 rewrite Vnth_sub.
    apply Vnth_eq. trivial. trivial.
    ++ do 3 rewrite Vnth_map2. do 5 rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
       +++ apply f_equal2. rewrite Vnth_map2.  do 2 rewrite Vbuild_nth. trivial.
    rewrite Vbuild_nth. rewrite Vnth_map2. apply f_equal. do 2 rewrite Vnth_tail.
    rewrite Vbuild_nth. trivial.       
    +++ apply f_equal2. apply f_equal; trivial. cbn. field; auto. cbn. field; auto.
    
    (* Third element of the relationship *)
    + apply F_bool_eq_corr. remember (VandermondeCol m (sval e.1)) as b. 
    assert (sval e.1 = Vhead (Vtail b)). rewrite Vhead_nth. rewrite Vnth_tail. 
    rewrite Heqb. rewrite Vbuild_nth. simpl. rewrite VF_prod_1. trivial. rewrite H2.
    rewrite <- Vcons_map2. rewrite <- VSn_eq. rewrite Vadd_map2. 
    unfold VF_sum. rewrite Vfold_left_Vadd_Fadd. rewrite sig.BM_neg.
    rewrite BM_VF_add_r_com. symmetry. rewrite <- shift. apply f_equal.
    apply Veq_nth. intros. rewrite Vbuild_nth. do 3 rewrite Vnth_map2.
    apply BM_simp. apply Veq_nth. intros. do 2 rewrite Vnth_map2. 
    rewrite Vnth_const. do 2 rewrite Vnth_map. destruct vs_field. destruct F_R.
    rewrite Rmul_1_l. rewrite Rmul_assoc. apply f_equal2; trivial.
    rewrite Vbuild_nth. rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    rewrite Vbuild_nth. rewrite Rmul_comm. rewrite <- Vnth_Vfold_left_cons_Fmul.
    apply Veq_nth4. rewrite <- Vfold_VFmul_const. rewrite <- Vfold_left_Vadd_VFmul.
    unfold n, sig.n. assert (S (S (S (i - 1))) = S (S i)). lia.
     apply (Vfold_left_eq_gen H3). apply Veq_nth. intros. rewrite Vnth_cast.
    rewrite Vnth_add. destruct (Nat.eq_dec i1 (S (S (i - 1)))). rewrite Vnth_sub.
    rewrite Vnth_tail. apply Vnth_eq. lia. do 2 rewrite Vnth_sub. apply Vnth_eq.  
    trivial.
    (* Part 2 *)
    rewrite (VSn_eq (Vsub w.1.1.1 (IndexCB2 ip))).
    rewrite Vfold_left_Vcons_VFmult. rewrite Vhead_sub. rewrite Vnth_map2.
    apply f_equal2; trivial. rewrite Vfold_left_VF_mult. assert (i = 0%nat). lia.
    subst. pose VF_prod_1_head. unfold VF_prod in e0. rewrite e0. rewrite Vhead_map.
    rewrite Vhead_nth. apply Veq_nth4. do 2 rewrite Vnth_tail. rewrite Vnth_sub.
    apply Vnth_eq. lia.
  Qed.

  Definition TE := VF M.N.
  
  Lemma pres_p0 : forall (s : St)(r : R)(w : W), 
      (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. trivial.
  Qed. 

  (* W: A, r, B, s : prod (prod (prod (vector (VF n) m) (VF m)) (VF n)) F*)
  (* UW : A, r, B, s : (vector (VF n) m)*(VF m)*(vector (VF n) m)*(VF m) *)
  Definition extractor (w : sig.W)(e : E) : W :=
    let A := w.1.1.1 in
    let r := w.1.1.2 in
    let B := w.1.2 in
    let s := w.2 in

    (Vcons (VF_scale (Vhead B) (FmulInv (sval e.1))) (Vremove_last A), 
    Vcons (Vhead s / (sval e.1)) (Vremove_last r),
    VF_scale (VF_add (VlastS B)
        (VF_neg
           (Vfold_left (VF_add (n:=sig.n)) (VF_zero sig.n)
              (Vmap2 (VF_scale (n:=sig.n)) (Vtail (Vremove_last B))
                 (Vconst (FmulInv (sval e.1)) M.N)))))
     (FmulInv (VlastS (Vtail (VandermondeCol m (sval e.1))))),
     (VlastS s - Vfold_left Fadd 0 (Vmap2 Fmul (Vtail (Vremove_last s))
         (Vconst (FmulInv (sval e.1)) M.N))) /
            VlastS (Vtail (VandermondeCol m (sval e.1)))).

  Definition argument (s : St)(c : C)(v : E) : Prop :=
      let h  := s.1.1.1 in
      let hs := s.1.1.2 in
      let CA := s.1.2 in 
      let cB := s.2 in 
      (* The commitments are broken *)
      (exists c m0 m1 r0 r1, relComEPC h hs c m0 m1 r0 r1) \/ 

      (* Schwartz Zipple lemma failed (Two matrices a and b), vector d and opening *)
      (* The big idea is that prover commits to the coefficents, which determine the
       polynomial, before the challenge. If the polynomial sampled at the challenge
      is zero we conclude the polynomial is zero *)
      (exists (a b : vector (VF n) m) d r, 
      (* pk ck=(h,hs) y C_A C_B *)
      let s := ToSt (s,c,v) in

        (* Check to that polynomials are commited hence are indepedent from challenges
         under binding *)
      s.1.2 = comEPC h hs a d /\
      s.2 = comEPC h hs b r /\ 

        (* If the commited polyonimals are evaluate to zero at the challenge but not equal then 
        we allow soundness not to hold (The Schwatz Zippel Lemma says this occurs with 
        negligble probabilty). *)
      0 = (VF_sum (Vmap2 (BM v.2) a b)) /\ 
      VF_zero n <> Vfold_left (VF_add (n:=n)) (VF_zero n) (Vmap2 (VF_mult (n:=n)) a b)) \/

      (* Second SZ lemma *)
      (exists (a b : vector (VF n) m) d r,
      
      CA = comEPC h hs a r /\
      (Vcons (Vhead CA) (Vadd c cB)) = comEPC h hs b d /\
      
      (Vfold_left (VF_add (n:=n)) (VF_zero n) 
          (Vmap2 (VF_scale (n:=n)) (Vtail b) (Vtail (VandermondeCol m (sval v.1)))) =
      Vfold_left (VF_add (n:=n)) (VF_zero n) 
          (Vmap2 (VF_mult (n:=n)) (Vtail a) (Vmap2 (VF_scale (n:=n))
              (Vremove_last b) (Vtail (VandermondeCol m (sval v.1)))))) /\
      Vtail b <> Vmap2 (VF_mult (n:=n)) (Vtail a) (Vremove_last b)).
    
  Lemma special_soundness : forall s c (e : E)
        (w : sig.W),
    sig.Rel (ToSt (s,c,e)) w ->
    Rel s (extractor w e) \/ argument s c e.
  Proof.
    
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.  
    pose Commitment.module_abegrp. intros. 
    unfold Rel, extractor. unfold sig.Rel in H. unfold ToSt in H.
    destruct w, p, p.
     apply andb_true_iff in H. destruct H.
    apply andb_true_iff in H. destruct H. apply VGeq in H. apply VGeq in H1.
    apply F_bool_eq_corr in H0. unfold ToSt in *. do 2 rewrite Prod_left_replace in H.
    do 2 rewrite Prod_right_replace in H1.
    do 2 rewrite Prod_left_replace in H1. rewrite Prod_right_replace in H0.  
    (* We prove the opening of the commits before proceding with the bulk of the proof *)
    (* Now about to prove CA = (comEPC n m h hs A r) *)
    assert (s.1.2 = comEPC s.1.1.1 s.1.1.2
  (Vcons (VF_scale (Vhead t) (FmulInv (sval e.1)))
     (Vremove_last t0))
  (Vcons (Vhead v / sval e.1) (Vremove_last v0))).
    + rewrite (VSn_eq s.1.2). apply Vadd_eq_elim_gen in H.
    apply Vadd_eq_elim_gen in H1. destruct H. destruct H1. rewrite H2.
    rewrite (VSn_eq (Vtail (VandermondeCol m (sval e.1)))) in H3.
    unfold VG_Pexp in H3. rewrite Vcons_map2 in H3. unfold comEPC. 
    rewrite Vcons_map2. apply Vcons_eq_intro.
    (* We now deal with the head which has nearly all the complexity *)
    - assert (Vhead (Vtail (VandermondeCol m (sval e.1))) =
    (sval e.1)).
    rewrite Vbuild_tail. rewrite Vbuild_head. cbn. field; auto. rewrite H4 in H3.
    apply Vcons_eq_elim_gen in H3. destruct H3. assert (forall c a b, a=b ->
    a^c = b^c). intros. rewrite H6. trivial.
    apply (H6 (FmulInv (sval e.1))) in H3. rewrite <- mod_dist_Fmul in H3.
    assert (FmulInv (sval e.1) * (sval e.1) = 1). field; auto.
    apply (proj2_sig e.1).
    rewrite H7 in H3. rewrite mod_id in H3. rewrite H3. rewrite Vhead_Vremove_last.
    rewrite Vhead_map2. rewrite <- EPCExp. trivial. 
    - apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_remove_last. 
    rewrite Vnth_map2. trivial.
    (* Time to prove (Vcons (Vhead CA) (Vadd c cB)) = comEPC n m h hs b d  *)
    + assert (Vcons (Vhead s.1.2) (Vadd c s.2) = comEPC s.1.1.1 s.1.1.2
    (* First the message *)
    (Vadd (Vmap2 (VF_scale (n:=n)) (Vremove_last t) 
                                   (Vtail (VandermondeCol m (FmulInv (sval e.1)))))
    (VF_scale (VF_add (VlastS t) (VF_neg
           (Vfold_left (VF_add (n:=sig.n)) (VF_zero sig.n)
              (Vmap2 (VF_scale (n:=sig.n)) (Vtail (Vremove_last t))
                 (Vconst (FmulInv (sval e.1)) M.N)))))
     (FmulInv (VlastS (Vtail (VandermondeCol m (sval e.1)))))))
    (* Now the randomness *)
     (Vadd (VF_mult (Vremove_last v) (Vtail (VandermondeCol m  (FmulInv (sval e.1)))))
      ((VlastS v - Vfold_left Fadd 0 (Vmap2 Fmul (Vtail (Vremove_last v))
         (Vconst (FmulInv (sval e.1)) M.N))) /
            VlastS (Vtail (VandermondeCol m (sval e.1)))))).
    ++ apply Vcons_eq_elim_gen. split.
    +++ rewrite Vhead_map2. do 2 rewrite Vhead_Vadd. rewrite H2.
    do 2 rewrite Vhead_map2. do 2 rewrite Vhead_cons. apply f_equal2.  
    rewrite Vhead_Vremove_last. apply f_equal. rewrite Vhead_nth.
    rewrite Vnth_tail. rewrite Vbuild_nth. cbn. field; auto. apply (proj2_sig e.1).
    rewrite Vhead_map2. rewrite Vhead_Vremove_last. apply f_equal.  rewrite Vhead_nth. 
    rewrite Vnth_tail. rewrite Vbuild_nth. cbn. field; auto. apply (proj2_sig e.1).
    +++ apply Vadd_eq_elim_gen. apply Vadd_eq_elim_gen in H1. destruct H1. 
    apply Veq_elim_gen in H3. destruct H3.  assert (forall c a b, a=b -> a^c = b^c).
    intros. rewrite H5. trivial.
    assert (forall n (c : VF n) a b, a = b -> VG_Pexp a c = VG_Pexp b c). 
    intros. rewrite H6. trivial. split.
    ++++ 
    (* We will also need to know what the product of the c is *)
    unfold VG_Pexp in H4. rewrite <- Vtail_map2 in H4.
    rewrite Vtail_cons in H4. 
    apply (H6 M.N (VF_inv (Vtail (Vtail (VandermondeCol m (sval e.1))))))
     in H4.
    rewrite VG_Pexp_Pexp in H4. rewrite VF_inv_corr in H4.
    rewrite VG_One_exp in H4.
    (* Resuming main *)
    rewrite (VSn_addS (Vtail (VandermondeCol m (sval e.1)))) in H1.
    unfold VG_Pexp in H1. rewrite Vadd_map2 in H1. rewrite VG_prod_add in H1.
    assert (forall a b c, a o b = c -> b = c o - a). intros. rewrite <- H7.
    rewrite comm. rewrite dot_assoc. rewrite <- inv_left. rewrite one_left.
    trivial. apply H7 in H1. 
    apply (H5 (FmulInv (VlastS (Vtail (VandermondeCol m (sval e.1)))))) in H1.
     rewrite <- mod_dist_Fmul in H1.
    assert (FmulInv (VlastS (Vtail (VandermondeCol m (sval e.1)))) *
        VlastS (Vtail (VandermondeCol m (sval e.1))) = 1). 
    field; auto. rewrite VlastS_nth. rewrite Vnth_tail. rewrite Vbuild_nth.
    apply VF_prod_const_Nzero. apply (proj2_sig e.1).
    rewrite H8 in H1. rewrite mod_id in H1. rewrite H1.
    rewrite VlastS_map2. rewrite H4. clear H1.
    rewrite Vmap2_remove_last. rewrite <- Vmap2_tail. 
    unfold VG_Pexp. rewrite comEPCDis. rewrite comEPCDis. pose VF_mult_ass.
    unfold VF_mult in e0. rewrite e0. rewrite VandermondeColDiv. 
    rewrite VF_scale_map2.
    unfold VF_mult. rewrite VandermondeColDiv. 
    unfold VG_prod. rewrite <- EPCMultExt. rewrite EPCneg. rewrite EPCMult.
    rewrite <- EPCExp. do 2 rewrite VlastS_tail. rewrite VlastS_map2. do 2 rewrite VlastS_add.
    trivial.  apply (proj2_sig e.1). apply (proj2_sig e.1). 
     apply Vforall_nth_intro.
    intros. rewrite Vnth_tail. rewrite Vnth_tail. rewrite Vbuild_nth.
    apply VF_prod_const_Nzero. apply (proj2_sig e.1).
    ++++ unfold VG_Pexp in H4. rewrite <- Vtail_map2 in H4. rewrite Vtail_cons in H4.
    apply (H6 M.N (VF_inv (Vtail (Vtail (VandermondeCol m (sval e.1)))))) in H4.
    rewrite VG_Pexp_Pexp in H4. rewrite VF_inv_corr in H4. 
    rewrite VG_One_exp in H4. rewrite H4. rewrite Vremove_last_Vtail.
    do 2 rewrite Vmap2_remove_last. do 2 rewrite Vremove_last_add. rewrite <- Vtail_map2. 
    unfold VG_Pexp. rewrite comEPCDis. rewrite <- Vtail_map2. apply f_equal2. 
    rewrite <- Vtail_map2. trivial. apply f_equal. apply Veq_nth. intros.
    rewrite Vnth_map.  do 4 rewrite Vnth_tail. do 2 rewrite Vbuild_nth.
    apply FmulInv_VF_prod_Vconst. apply (proj2_sig e.1).
    unfold VF_mult. rewrite <- Vtail_map2. apply f_equal. apply Veq_nth. intros.
    rewrite Vnth_map.  do 4 rewrite Vnth_tail. do 2 rewrite Vbuild_nth.
    apply FmulInv_VF_prod_Vconst. apply (proj2_sig e.1).

    apply Vforall_nth_intro.
    intros. rewrite Vnth_tail. rewrite Vnth_tail. rewrite Vbuild_nth.
    apply VF_prod_const_Nzero. apply (proj2_sig e.1).
    
    (* Commitments done time to start casing *)
    (* SZ case 1 *)
    ++ case_eq (VF_beq (VF_zero n) (Vfold_left (VF_add (n:=n)) (VF_zero n) 
      (Vmap2 (VF_mult (n:=n)) t0 t))); intros.
    (* Commitment case *)
    case_eq (VF_beq (VlastS t0) (VF_neg (VF_one n))); intros.
    (* SZ case 2 *)
    case_eq (bVforall2 (VF_beq (n:=n)) (Vtail (Vadd (Vmap2 (VF_scale (n:=n)) (Vremove_last t)
             (Vtail (VandermondeCol m (FmulInv (sval e.1)))))
          (VF_scale (VF_add (VlastS t) (VF_neg
          (Vfold_left (VF_add (n:=sig.n)) (VF_zero sig.n)
          (Vmap2 (VF_scale (n:=sig.n)) (Vtail (Vremove_last t))
          (Vconst (FmulInv (sval e.1)) M.N)))))
          (FmulInv (VlastS (Vtail (VandermondeCol m (sval e.1))))))))
    (* Second part *)
    (Vmap2 (VF_mult (n:=n)) (Vtail (Vcons
          (VF_scale (Vhead t) (FmulInv (sval e.1)))
          (Vremove_last t0))) 
        (Vremove_last (Vadd (Vmap2 (VF_scale (n:=n)) (Vremove_last t)
             (Vtail (VandermondeCol m (FmulInv (sval e.1)))))
          (VF_scale (VF_add (VlastS t) (VF_neg
          (Vfold_left (VF_add (n:=sig.n)) (VF_zero sig.n)
          (Vmap2 (VF_scale (n:=sig.n)) (Vtail (Vremove_last t))
          (Vconst (FmulInv (sval e.1)) M.N)))))
          (FmulInv (VlastS (Vtail (VandermondeCol m (sval e.1)))))))))).
    (* Resuming main *)
    left. apply andb_true_iff. split. apply andb_true_iff. split.
    +++ apply VGeq. rewrite Prod_right_replace.  rewrite Prod_left_replace. apply H2.
    (* Now proving cB =  (EPC n h hs B s) *)
    +++ apply bool_eq_corr. do 2 rewrite Prod_right_replace.
    (* We need to get s.2 out of H2 *)
    apply Vadd_eq_elim_gen in H1. apply Vcons_eq_elim_gen in H3.
    destruct H3. apply Vadd_eq_elim_gen in H7. destruct H7. rewrite H7.
    unfold comEPC. rewrite <- Vtail_map2. rewrite VlastS_map2. 
    do 2 rewrite VlastS_tail. do 2 rewrite VlastS_add. trivial.

    (* Now proving VF_beq B (Vfold_left (@VF_mult n) (VF_one n) A) *)
    +++ rewrite Prod_right_replace. rewrite Prod_left_replace. apply VF_beq_true.
    (* We will start by getting the hypotisis ready *)
    apply VF_beq_true in H4. apply VF_beq_true in H5.
    apply VF_beq_true_forall in H6.
    clear H5 H4 H3 H1 H2 H. rewrite Vtail_cons in H6. rewrite Vremove_last_add in H6.
    rewrite Vtail_Vadd in H6. apply Vadd_eq_elim_gen in H6. destruct H6.
    rewrite <- Vtail_map2 in H1. do 2 rewrite Vmap2_remove_last in H1.
    (* We need to prove that we can express the a_is as b *)
    assert (VF_scale (VlastS (Vremove_last t)) (VlastS (VandermondeCol m (FmulInv (sval e.1)))) = 
      Vfold_left (VF_mult (n:=n)) (VF_one n)
       (Vcons (VF_scale (Vhead t) (FmulInv (sval e.1))) 
       (Vremove_last (Vremove_last t0)))). unfold sig.W, m, M, sig.m in *.  
    clear H0 H. 
    induction M.N.
    ++++ (* Base case *) 
    rewrite Vfold_left_Vcons_VFmult. rewrite Vfold_left_nil. rewrite VF_comm_mult.
    rewrite VF_mult_one. apply f_equal2.
    rewrite VlastS_nth. rewrite Vhead_nth. rewrite Vnth_remove_last. apply Vnth_eq. 
    trivial. rewrite VlastS_nth. rewrite Vbuild_nth. unfold VF_prod.
    rewrite Vfold_left_head.  rewrite Vhead_const. trivial. intros. field; auto.
    ++++ (* Inductive cast *)
    apply Veq_elim_gen2 in H1. destruct H1. do 3 rewrite VlastS_map2 in H.
    do 3 rewrite VlastS_tail in H. rewrite H. 
    rewrite Vremove_last_Vtail. rewrite VlastS_tail. rewrite VandermondeCol_remove.
    rewrite (IHn0 (Vremove_last t0) (Vremove_last v0) (Vremove_last t) 
      (Vremove_last v)). 
    do 2 rewrite Vfold_left_Vcons_VFmult. rewrite <- VF_mult_ass. apply f_equal2.
    rewrite VF_comm_mult. rewrite <- Vfold_left_Vadd_VFmul. 
    rewrite <- VSn_addS. trivial. rewrite Vhead_Vremove_last. trivial.
    rewrite Vmap2_remove_last in H0.
    do 3 rewrite Vremove_last_Vtail in H0. rewrite VandermondeCol_remove in H0.   
    rewrite H0. do 2 rewrite Vmap2_remove_last. trivial.
    ++++ rewrite H. do 2 rewrite VlastS_map2. rewrite VlastS_tail.
    rewrite H2. do 2 rewrite Vfold_left_Vcons_VFmult. rewrite <- VF_mult_ass.
    do 2 rewrite Prod_right_replace.
    apply f_equal2. rewrite VF_comm_mult. rewrite <- Vfold_left_Vadd_VFmul. 
    rewrite <- VSn_addS. trivial. trivial.

    (* What if SW failed 1 *)
    +++ right. unfold argument. right. right. exists (Vcons (VF_scale (Vhead t) (FmulInv (sval e.1)))
          (Vremove_last t0)). exists (Vadd
          (Vmap2 (VF_scale (n:=n)) (Vremove_last t)
             (Vtail (VandermondeCol m (FmulInv (sval e.1)))))
          (VF_scale
             (VF_add (VlastS t)
                (VF_neg
                   (Vfold_left (VF_add (n:=sig.n)) (VF_zero sig.n)
                      (Vmap2 (VF_scale (n:=sig.n))
                         (Vtail (Vremove_last t))
                         (Vconst (FmulInv (sval e.1)) M.N)))))
             (FmulInv (VlastS (Vtail (VandermondeCol m (sval e.1))))))).
    exists (Vadd
          (VF_mult (Vremove_last v)
             (Vtail (VandermondeCol m (FmulInv (sval e.1)))))
          ((VlastS v -
            Vfold_left Fadd 0
              (Vmap2 Fmul (Vtail (Vremove_last v))
                 (Vconst (FmulInv (sval e.1)) M.N))) /
           VlastS (Vtail (VandermondeCol m (sval e.1))))).
    exists (Vcons (Vhead v / sval e.1)
          (Vremove_last v0)).
    split. trivial. split. trivial. split.
    ++++ trivial. symmetry. rewrite Vtail_cons. rewrite Vremove_last_add. clear H3.
    rewrite Vtail_Vadd. rewrite <- Vtail_map2. apply VF_beq_true in H4.
    rewrite VF_scale_map2. replace (VF_mult (Vtail (VandermondeCol m (FmulInv (sval e.1))))
           (Vtail (VandermondeCol m (sval e.1)))) with (VF_one (S M.N)).
    rewrite VF_scale_1_map. rewrite (VSn_addS (Vmap2 (VF_mult (n:=n)) t0 t)) in H4.
    rewrite Vfold_left_Vadd_VFadd in H4. rewrite <- Vmap2_remove_last.
    apply VF_add_move in H4. symmetry in H4. rewrite H4. rewrite VF_comm.
    rewrite VF_add_zero. rewrite VlastS_map2. 
    rewrite (VSn_addS (Vtail (VandermondeCol m (sval e.1)))). rewrite Vadd_map2.
    rewrite Vfold_left_Vadd_VFadd. rewrite VlastS_add. rewrite VF_scale_scale.
    rewrite VF_scale_1_gen.  rewrite VF_scale_map2.
    unfold VF_mult. rewrite VandermondeColDiv2.
    rewrite VF_add_neg3. apply VF_beq_true in H5. rewrite H5.
    rewrite VF_neg_mul. rewrite VF_neg_neg. rewrite VF_comm_mult. rewrite VF_mult_one.
    trivial.  apply (proj2_sig e.1).
    field; auto. rewrite VlastS_tail. rewrite VlastS_build.
    apply VF_prod_const_Nzero. apply (proj2_sig e.1).
    (* Need to clean up the replace form before *)
    apply Veq_nth. intros. rewrite Vnth_const. rewrite Vnth_map2. do 2 rewrite Vnth_tail.
    do 2 rewrite Vbuild_nth. rewrite <- FmulInv_VF_prod_Vconst. field; auto.
    apply VF_prod_const_Nzero. apply (proj2_sig e.1).  apply (proj2_sig e.1).
    ++++ unfold not.  intros. apply not_true_iff_false in H6. apply H6.
    apply VF_beq_true_forall. trivial.
     (* What if the commitments failed *)
    +++ right. left. exists (EPC s.1.1.1 s.1.1.2 (VF_neg (VF_one n)) 0).
    exists (VlastS t0). exists (VF_neg (VF_one n)). 
    exists (VlastS v0). exists 0. unfold relComEPC. split. 
    apply VF_beq_false in H5. trivial. split. apply Vadd_eq_elim_gen in H.
    destruct H. rewrite H. rewrite VlastS_map2. trivial. trivial.
    (* What if SW failed 2 *)
    +++ right. unfold argument. right. left. exists t0. exists t.
    exists v0. exists v. split. apply H.
    split. apply H1. split. apply H0. apply VF_beq_false in H4. trivial.
  Qed.

  Lemma e_abgrp : AbeGroup E add zero bool_eq disjoint inv.
  Proof.
    pose G2.module_abegrp.
    intros. constructor; intros. constructor; intros. constructor; intros.
    apply injective_projections; simpl. apply dot_assoc. field; auto.
    apply injective_projections; unfold add, zero. rewrite Prod_left_replace.
    apply one_left. do 2 rewrite Prod_right_replace. field; auto.
    apply injective_projections; simpl. apply one_right. field; auto.
    split; intros. apply andb_true_iff in H. destruct H.
    apply bool_eq_corr in H. apply F_bool_eq_corr in H0.
    apply injective_projections; auto.
    apply andb_true_iff. split. apply bool_eq_corr; rewrite H; auto.
    apply F_bool_eq_corr; rewrite H; auto.
    unfold bool_eq. rewrite bool_eq_sym. apply f_equal. apply F_bool_eq_sym.
    split; intros. apply andb_false_iff in H. destruct H. apply bool_neq_corr in H.
    unfold not. intros.  apply H. rewrite H0. auto. apply F_bool_neq_corr in H.
    unfold not. intros.  apply H. rewrite H0. auto. apply andb_false_iff.
    case_eq (G2.Gbool_eq a0.1 b.1); intros. right. apply F_bool_neq_corr.
    unfold not. intros. apply H. apply injective_projections. apply bool_eq_corr.
    trivial. trivial. left. trivial.
    unfold disjoint. rewrite bool_eq_sym. apply f_equal. rewrite F_bool_eq_sym.
    trivial.
    apply andb_true_iff in H. destruct H. apply negb_true_iff in H.
    apply bool_neq_corr in H. unfold not. intros. apply H. rewrite H1. trivial. 
    apply injective_projections; simpl. apply inv_left. field; auto.
    apply injective_projections; simpl. apply inv_right. field; auto.
    apply injective_projections; simpl. apply comm. field; auto.
  Qed.

  Definition X := sig.X.

  Definition simulator (s : St)(t : TE)(e : E) : C :=
    let h   := s.1.1.1 in
    let hs  := s.1.1.2 in
    let CA  := s.1.2 in
    let cB  := s.2 in

     (Vmap (fun x => EPC h hs (VF_zero n) x) t).

  Definition simMap    (s : St)(w : W)(e : E)(x : X)(r : R) : TE := 
     VF_add r (Vbuild (fun i (ip : i < M.N) => VF_inProd x
     (Vfold_left (VF_mult (n:=n)) (VF_one n) (Vsub w.1.1.1 (IndexCB ip))))).
  Definition simMapInv (s : St)(w : W)(e : E)(x : X)(t : TE) : R := 
      (VF_sub t (Vbuild (fun i (ip : i < M.N) => VF_inProd x
     (Vfold_left (VF_mult (n:=n)) (VF_one n) (Vsub w.1.1.1 (IndexCB ip)))))).

  Definition simMapHelp (st: St)(x: X) : Prop :=
    let h   := st.1.1.1 in
    let hs  := st.1.1.2 in

    hs = Vmap (op h) x.

  Definition sigXcomp (s : St)(x : X) : sig.X := x.

  (* This may need more preconditions otherwise it might be too strong *)
  Lemma simMapHelpValid : forall (st : St)(x : X)(c : C)(e : E),
    simMapHelp st x ->
    sig.simMapHelp (ToSt (st,c,e)) (sigXcomp st x).
  Proof.
    intros. unfold sig.simMapHelp, ToSt, sigXcomp. simpl. apply H.
  Qed.

  Lemma simulatorZK1 : forall s w r e x,
     Rel s w ->
     simMapHelp s x ->
     (P0 s r w).2 = simulator s (simMap s w e x r) e.
  Proof.
    intros. unfold P0, simulator, simMap. rewrite Prod_right_replace. apply Veq_nth. 
    intros. rewrite Vnth_map. rewrite Vnth_map2.
    rewrite Vbuild_nth. rewrite (trapdoorEPC s.1.1.1 x H0). rewrite Vnth_map2.
    rewrite Vbuild_nth. trivial.
  Qed.

  Lemma simMapInvValid : forall (st : St)(w : W)(x : X)
        (e : E)(r : R)(t : TE),
     Rel st w ->
     simMapHelp st x ->
    simMap st w e x (simMapInv st w e x t) = t /\
    simMapInv st w e x (simMap st w e x r) = r.
  Proof.
    intros. split.
    + unfold simMap, simMapInv. rewrite VF_add_neg2. trivial.
    + unfold simMap, simMapInv. rewrite VF_sub_corr. rewrite VF_add_neg. trivial. 
  Qed.

End BGHadProd. 

Module BGHadProdIns (Message Ciphertext Commitment : GroupSig)(Ring : RingSig)
    (Field : FieldSig)(VS2 : VectorSpaceSig Commitment Field)
    (VS1 : VectorSpaceSig Ciphertext Field)(Chal : GroupFromRing Field)
    (MVS : VectorSpaceModuleSameGroup Ciphertext Ring Field VS1)
    (VS3 : VectorSpaceSig Message Field)(Hack : Nat)(M : Nat)
    (enc : EncryptionSchemePlus Message Ciphertext Ring Field VS1 VS3 MVS)
    (support : BGSupport Message Ciphertext Commitment Ring Field VS2 VS1 MVS VS3
    Hack M enc)(sig : BGZeroArg Message Ciphertext Commitment Ring Field VS2 VS1 Chal
    MVS VS3 Hack M enc support) <: SigmaPlusTo5sim Chal sig.

  Import sig.
  Import support.

  (* N = nm *)
  Let n := S (S (S Hack.N)).      (* n *)
  Let m := S (S M.N).     (* m *)
  Import Field.

  (*Module Mo := MatricesFieldIns Field.*)
  Import Mo.
  Import Mo.mat.
  (*Module MoR := MatricesFIns Ring.
  Module MoC := MatricesG Ciphertext Field VS1 mat.
  Module MoM := MatricesG Message Field VS3 mat.

  (* Make commitment scheme and matrix *)
  Module EPC := ExtendComScheme Commitment Field VS2 mat.*)
  Import EPC.
  Import EPC.MoM.
  (*Module PC := BasicComScheme Commitment Field VS2 mat. *)
  Import PC.

  (* Addational vector lemma *)
  (* Module ALVS1 := VectorSpaceAddationalLemmas Ciphertext Field VS1.
  Module ALVS2 := VectorSpaceAddationalLemmas Commitment Field VS2.
  Module ALVS3 := VectorSpaceAddationalLemmas Message Field VS3.

  Module ALenc := EncryptionSchemeProp Message Ciphertext Ring Field VS1 MVS enc. *)
  Import ALenc.
  (* Module HardProb := HardProblems Commitment Field VS2. *)
  Import HardProb.

  Module ALR := RingAddationalLemmas Ring.

  Import VS2.
  Import Commitment.

  Module G2 := GroupFromFieldIns Field.

  Definition E := prod (G2.G) F.

  (* pk ck=(h,hs) C_A c_B *)
  Definition St : Type := G*VG n*VG m*G.

  (* A, r, B, s *)
  Definition W := prod (prod (prod (vector (VF n) m) (VF m)) (VF n)) F.

  Definition Rel (s : St)(w : W) : bool :=
    let h   := s.1.1.1 in
    let hs  := s.1.1.2 in
    let CA  := s.1.2 in
    let cB  := s.2 in
    let A := w.1.1.1 in
    let r := w.1.1.2 in
    let B := w.1.2 in
    let s := w.2 in
      VG_eq CA (comEPC h hs A r) &&
      Gbool_eq cB (EPC h hs B s) &&
      VF_beq B (Vfold_left (@VF_mult n) (VF_one n) A).

  Definition C := VG M.N.

  Definition R := VF M.N.

  Definition add (e1 e2 : E) := (G2.Gdot e1.1 e2.1,e1.2+e2.2).
  Definition zero := (G2.Gone,0).
  Definition inv (e : E) := (G2.Ginv e.1, Finv e.2).
  Definition bool_eq (e1 e2 : E) := G2.Gbool_eq e1.1 e2.1 && Fbool_eq e1.2 e2.2.
  Definition disjoint  (e1 e2 : E) : bool := negb (G2.Gbool_eq e1.1 e2.1) &&
      negb (Fbool_eq e1.2 e2.2).

  Lemma IndexCB : forall i,
    i < M.N -> 0+(S (S i)) <= m.
  Proof.
    intros. unfold m. lia.
  Qed.

  Lemma IndexCB2 : forall i,
    i < S M.N -> 0+(S (S i)) <= m.
  Proof.
    intros. unfold m. lia.
  Qed.

  (* We don't send the redudent c_A1 c_b *)
  Definition P0 (st : St)(r : R)(w : W) : St*C  :=
    let h   := st.1.1.1 in
    let hs  := st.1.1.2 in
    let CA  := st.1.2 in
    let cB  := st.2 in
    let A := w.1.1.1 in
    let B := w.1.2 in
    let s := w.2 in
    (st, comEPC h hs
      (Vbuild (fun i (ip: i < M.N) =>
      Vfold_left (@VF_mult n) (VF_one n) (Vsub A (IndexCB ip))))
    r).

  Definition ToSt (sce : St*C*E) : sig.St :=
    let s := sce.1.1 in
    let c := sce.1.2 in
    let e := sce.2 in

    let h   := s.1.1.1 in
    let hs  := s.1.1.2 in
    let CA  := s.1.2 in
    let cB  := s.2 in
    let CB  := c in
    let x   := e.1 in
    let y   := e.2 in

    (* pk, ck, y, C_A, C_B *)
    (h,hs,y,(Vadd (Vtail CA) (EPC h hs (VF_neg (VF_one n)) 0)),
    (Vadd (VG_Pexp (Vcons (Vhead CA) CB) (Vtail (VandermondeCol m (sval x)))))
      (VG_prod (VG_Pexp (Vadd CB cB) (Vtail (VandermondeCol m (sval x)))))).

  Definition ToWit (sce : St*C*E)(r : R)(w : W) : sig.W :=
    let s   := sce.1.1 in
    let h   := s.1.1.1 in
    let hs  := s.1.1.2 in
    let CA  := s.1.2 in
    let cB  := s.2 in
    let CB  := sce.1.2 in
    let x   := sce.2.1 in
    let y   := sce.2.2 in
    let A  := w.1.1.1 in
    let r' := w.1.1.2 in
    let B := w.1.2 in
    let s := w.2 in

    (Vadd (Vtail A) (VF_neg (VF_one n)), Vadd (Vtail r') 0,
      Vadd (Vcons (VF_scale (Vhead A) (sval x))
        (Vmap2 (@VF_scale n) (Vbuild (fun i (ip: i < M.N) =>
        (Vfold_left (@VF_mult n) (VF_one n) (Vsub A (IndexCB ip))))) (Vtail (Vtail (VandermondeCol m (sval x))))))
       (Vfold_left (@VF_add n) (VF_zero n) (Vmap2 (@VF_scale n) (Vbuild (fun i (ip: i < S M.N) =>
        (Vfold_left (@VF_mult n) (VF_one n) (Vsub A (IndexCB2 ip))))) (Vtail (VandermondeCol m (sval x))))),
      Vadd (Vcons (Vhead r' * (sval x)) (VF_mult r (Vtail (Vtail (VandermondeCol m (sval x))))))
      (VF_sum (VF_mult (Vadd r s) (Vtail (VandermondeCol m (sval x)))))).

  Lemma ToValid : forall (s : St)(w : W)(r : R)(e : E),
    Rel s w ->
   sig.Rel (ToSt (P0 s r w, e)) (ToWit (P0 s r w, e) r w).
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.
    pose Commitment.module_abegrp.
    intros. unfold Rel, sig.Rel, ToSt, ToWit, P0 in *. do 2 rewrite Prod_left_replace.
    do 2 rewrite Prod_right_replace.  apply andb_true_iff in H. destruct H.
    apply andb_true_iff in H. destruct H.
    apply VGeq in H. apply bool_eq_corr in H1. apply VF_beq_true in H0.
    apply andb_true_iff. split. apply andb_true_iff. split. apply VGeq.
    rewrite H.  unfold comEPC. rewrite <- Vtail_map2. rewrite Vadd_map2. trivial.
    (* Second element of the realtionship *)
    + apply VGeq. rewrite H. rewrite H1. rewrite Vhead_map2. unfold comEPC.
    assert ((sval e.1) =  Vhead (Vtail (VandermondeCol m (sval e.1)))).
    rewrite Vhead_nth.
    rewrite Vnth_tail. rewrite Vbuild_nth. simpl. rewrite VF_prod_1. trivial.
    rewrite <- Vadd_map2. rewrite <- Vcons_map2. unfold VG_Pexp. rewrite comEPCDis.
    apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_add.
    destruct (Nat.eq_dec i (S M.N)).
    ++ rewrite comEPCDis. unfold VG_prod. rewrite <- EPCMultExt. apply f_equal2.
    apply f_equal. apply Veq_nth. intros. do 2 rewrite Vnth_map2. rewrite Vnth_add.
    destruct (Nat.eq_dec i0 M.N). rewrite Vbuild_nth. rewrite H0. apply f_equal2.
    subst. apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_sub.
    apply Vnth_eq. lia. trivial. apply f_equal2; trivial. do 2 rewrite Vbuild_nth.
    apply Vfold_left_eq. trivial. apply Veq_nth. intros. do 2 rewrite Vnth_sub.
    apply Vnth_eq. trivial. trivial.
    ++ do 3 rewrite Vnth_map2. do 5 rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
       +++ apply f_equal2. rewrite Vnth_map2.  do 2 rewrite Vbuild_nth. trivial.
    rewrite Vbuild_nth. rewrite Vnth_map2. apply f_equal. do 2 rewrite Vnth_tail.
    rewrite Vbuild_nth. trivial.
    +++ apply f_equal2. apply f_equal; trivial. cbn. field; auto. cbn. field; auto.
    
    (* Third element of the relationship *)
    + apply F_bool_eq_corr. remember (VandermondeCol m (sval e.1)) as b.
    assert (sval e.1 = Vhead (Vtail b)). rewrite Vhead_nth. rewrite Vnth_tail.
    rewrite Heqb. rewrite Vbuild_nth. simpl. rewrite VF_prod_1. trivial. rewrite H2.
    rewrite <- Vcons_map2. rewrite <- VSn_eq. rewrite Vadd_map2.
    unfold VF_sum. rewrite Vfold_left_Vadd_Fadd. rewrite sig.BM_neg.
    rewrite BM_VF_add_r_com. symmetry. rewrite <- shift. apply f_equal.
    apply Veq_nth. intros. rewrite Vbuild_nth. do 3 rewrite Vnth_map2.
    apply BM_simp. apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    rewrite Vnth_const. do 2 rewrite Vnth_map. destruct vs_field. destruct F_R.
    rewrite Rmul_1_l. rewrite Rmul_assoc. apply f_equal2; trivial.
    rewrite Vbuild_nth. rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    rewrite Vbuild_nth. rewrite Rmul_comm. rewrite <- Vnth_Vfold_left_cons_Fmul.
    apply Veq_nth4. rewrite <- Vfold_VFmul_const. rewrite <- Vfold_left_Vadd_VFmul.
    unfold n, sig.n. assert (S (S (S (i - 1))) = S (S i)). lia.
     apply (Vfold_left_eq_gen H3). apply Veq_nth. intros. rewrite Vnth_cast.
    rewrite Vnth_add. destruct (Nat.eq_dec i1 (S (S (i - 1)))). rewrite Vnth_sub.
    rewrite Vnth_tail. apply Vnth_eq. lia. do 2 rewrite Vnth_sub. apply Vnth_eq.
    trivial.
    (* Part 2 *)
    rewrite (VSn_eq (Vsub w.1.1.1 (IndexCB2 ip))).
    rewrite Vfold_left_Vcons_VFmult. rewrite Vhead_sub. rewrite Vnth_map2.
    apply f_equal2; trivial. rewrite Vfold_left_VF_mult. assert (i = 0%nat). lia.
    subst. pose VF_prod_1_head. unfold VF_prod in e0. rewrite e0. rewrite Vhead_map.
    rewrite Vhead_nth. apply Veq_nth4. do 2 rewrite Vnth_tail. rewrite Vnth_sub.
    apply Vnth_eq. lia.
  Qed.

  Definition TE := VF M.N.
  
  Lemma pres_p0 : forall (s : St)(r : R)(w : W),
      (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. trivial.
  Qed.

  (* W: A, r, B, s : prod (prod (prod (vector (VF n) m) (VF m)) (VF n)) F*)
  (* UW : A, r, B, s : (vector (VF n) m)*(VF m)*(vector (VF n) m)*(VF m) *)
  Definition extractor (w : sig.W)(e : E) : W :=
    let A := w.1.1.1 in
    let r := w.1.1.2 in
    let B := w.1.2 in
    let s := w.2 in

    (Vcons (VF_scale (Vhead B) (FmulInv (sval e.1))) (Vremove_last A),
    Vcons (Vhead s / (sval e.1)) (Vremove_last r),
    VF_scale (VF_add (VlastS B)
        (VF_neg
           (Vfold_left (VF_add (n:=sig.n)) (VF_zero sig.n)
              (Vmap2 (VF_scale (n:=sig.n)) (Vtail (Vremove_last B))
                 (Vconst (FmulInv (sval e.1)) M.N)))))
     (FmulInv (VlastS (Vtail (VandermondeCol m (sval e.1))))),
     (VlastS s - Vfold_left Fadd 0 (Vmap2 Fmul (Vtail (Vremove_last s))
         (Vconst (FmulInv (sval e.1)) M.N))) /
            VlastS (Vtail (VandermondeCol m (sval e.1)))).

  Definition argument (s : St)(c : C)(v : E) : Prop :=
      let h  := s.1.1.1 in
      let hs := s.1.1.2 in
      let CA := s.1.2 in
      let cB := s.2 in
      (* The commitments are broken *)
      (exists c m0 m1 r0 r1, relComEPC h hs c m0 m1 r0 r1) \/

      (* Schwartz Zipple lemma failed (Two matrices a and b), vector d and opening *)
      (* The big idea is that prover commits to the coefficents, which determine the
       polynomial, before the challenge. If the polynomial sampled at the challenge
      is zero we conclude the polynomial is zero *)
      (exists (a b : vector (VF n) m) d r,
      (* pk ck=(h,hs) y C_A C_B *)
      let s := ToSt (s,c,v) in

        (* Check to that polynomials are commited hence are indepedent from challenges
         under binding *)
      s.1.2 = comEPC h hs a d /\
      s.2 = comEPC h hs b r /\

        (* If the commited polyonimals are evaluate to zero at the challenge but not equal then
        we allow soundness not to hold (The Schwatz Zippel Lemma says this occurs with
        negligble probabilty). *)
      0 = (VF_sum (Vmap2 (BM v.2) a b)) /\
      VF_zero n <> Vfold_left (VF_add (n:=n)) (VF_zero n) (Vmap2 (VF_mult (n:=n)) a b)) \/

      (* Second SZ lemma *)
      (exists (a b : vector (VF n) m) d r,
      
      CA = comEPC h hs a r /\
      (Vcons (Vhead CA) (Vadd c cB)) = comEPC h hs b d /\
      
      (Vfold_left (VF_add (n:=n)) (VF_zero n)
          (Vmap2 (VF_scale (n:=n)) (Vtail b) (Vtail (VandermondeCol m (sval v.1)))) =
      Vfold_left (VF_add (n:=n)) (VF_zero n)
          (Vmap2 (VF_mult (n:=n)) (Vtail a) (Vmap2 (VF_scale (n:=n))
              (Vremove_last b) (Vtail (VandermondeCol m (sval v.1)))))) /\
      Vtail b <> Vmap2 (VF_mult (n:=n)) (Vtail a) (Vremove_last b)).
    
  Lemma special_soundness : forall s c (e : E)
        (w : sig.W),
    sig.Rel (ToSt (s,c,e)) w ->
    Rel s (extractor w e) \/ argument s c e.
  Proof.
    
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.
    pose Commitment.module_abegrp. intros.
    unfold Rel, extractor. unfold sig.Rel in H. unfold ToSt in H.
    destruct w, p, p.
     apply andb_true_iff in H. destruct H.
    apply andb_true_iff in H. destruct H. apply VGeq in H. apply VGeq in H1.
    apply F_bool_eq_corr in H0. unfold ToSt in *. do 2 rewrite Prod_left_replace in H.
    do 2 rewrite Prod_right_replace in H1.
    do 2 rewrite Prod_left_replace in H1. rewrite Prod_right_replace in H0.
    (* We prove the opening of the commits before proceding with the bulk of the proof *)
    (* Now about to prove CA = (comEPC n m h hs A r) *)
    assert (s.1.2 = comEPC s.1.1.1 s.1.1.2
  (Vcons (VF_scale (Vhead t) (FmulInv (sval e.1)))
     (Vremove_last t0))
  (Vcons (Vhead v / sval e.1) (Vremove_last v0))).
    + rewrite (VSn_eq s.1.2). apply Vadd_eq_elim_gen in H.
    apply Vadd_eq_elim_gen in H1. destruct H. destruct H1. rewrite H2.
    rewrite (VSn_eq (Vtail (VandermondeCol m (sval e.1)))) in H3.
    unfold VG_Pexp in H3. rewrite Vcons_map2 in H3. unfold comEPC.
    rewrite Vcons_map2. apply Vcons_eq_intro.
    (* We now deal with the head which has nearly all the complexity *)
    - assert (Vhead (Vtail (VandermondeCol m (sval e.1))) =
    (sval e.1)).
    rewrite Vbuild_tail. rewrite Vbuild_head. cbn. field; auto. rewrite H4 in H3.
    apply Vcons_eq_elim_gen in H3. destruct H3. assert (forall c a b, a=b ->
    a^c = b^c). intros. rewrite H6. trivial.
    apply (H6 (FmulInv (sval e.1))) in H3. rewrite <- mod_dist_Fmul in H3.
    assert (FmulInv (sval e.1) * (sval e.1) = 1). field; auto.
    apply (proj2_sig e.1).
    rewrite H7 in H3. rewrite mod_id in H3. rewrite H3. rewrite Vhead_Vremove_last.
    rewrite Vhead_map2. rewrite <- EPCExp. trivial.
    - apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_remove_last.
    rewrite Vnth_map2. trivial.
    (* Time to prove (Vcons (Vhead CA) (Vadd c cB)) = comEPC n m h hs b d  *)
    + assert (Vcons (Vhead s.1.2) (Vadd c s.2) = comEPC s.1.1.1 s.1.1.2
    (* First the message *)
    (Vadd (Vmap2 (VF_scale (n:=n)) (Vremove_last t)
                                   (Vtail (VandermondeCol m (FmulInv (sval e.1)))))
    (VF_scale (VF_add (VlastS t) (VF_neg
           (Vfold_left (VF_add (n:=sig.n)) (VF_zero sig.n)
              (Vmap2 (VF_scale (n:=sig.n)) (Vtail (Vremove_last t))
                 (Vconst (FmulInv (sval e.1)) M.N)))))
     (FmulInv (VlastS (Vtail (VandermondeCol m (sval e.1)))))))
    (* Now the randomness *)
     (Vadd (VF_mult (Vremove_last v) (Vtail (VandermondeCol m  (FmulInv (sval e.1)))))
      ((VlastS v - Vfold_left Fadd 0 (Vmap2 Fmul (Vtail (Vremove_last v))
         (Vconst (FmulInv (sval e.1)) M.N))) /
            VlastS (Vtail (VandermondeCol m (sval e.1)))))).
    ++ apply Vcons_eq_elim_gen. split.
    +++ rewrite Vhead_map2. do 2 rewrite Vhead_Vadd. rewrite H2.
    do 2 rewrite Vhead_map2. do 2 rewrite Vhead_cons. apply f_equal2.
    rewrite Vhead_Vremove_last. apply f_equal. rewrite Vhead_nth.
    rewrite Vnth_tail. rewrite Vbuild_nth. cbn. field; auto. apply (proj2_sig e.1).
    rewrite Vhead_map2. rewrite Vhead_Vremove_last. apply f_equal.  rewrite Vhead_nth.
    rewrite Vnth_tail. rewrite Vbuild_nth. cbn. field; auto. apply (proj2_sig e.1).
    +++ apply Vadd_eq_elim_gen. apply Vadd_eq_elim_gen in H1. destruct H1.
    apply Veq_elim_gen in H3. destruct H3.  assert (forall c a b, a=b -> a^c = b^c).
    intros. rewrite H5. trivial.
    assert (forall n (c : VF n) a b, a = b -> VG_Pexp a c = VG_Pexp b c).
    intros. rewrite H6. trivial. split.
    ++++
    (* We will also need to know what the product of the c is *)
    unfold VG_Pexp in H4. rewrite <- Vtail_map2 in H4.
    rewrite Vtail_cons in H4.
    apply (H6 M.N (VF_inv (Vtail (Vtail (VandermondeCol m (sval e.1))))))
     in H4.
    rewrite VG_Pexp_Pexp in H4. rewrite VF_inv_corr in H4.
    rewrite VG_One_exp in H4.
    (* Resuming main *)
    rewrite (VSn_addS (Vtail (VandermondeCol m (sval e.1)))) in H1.
    unfold VG_Pexp in H1. rewrite Vadd_map2 in H1. rewrite VG_prod_add in H1.
    assert (forall a b c, a o b = c -> b = c o - a). intros. rewrite <- H7.
    rewrite comm. rewrite dot_assoc. rewrite <- inv_left. rewrite one_left.
    trivial. apply H7 in H1.
    apply (H5 (FmulInv (VlastS (Vtail (VandermondeCol m (sval e.1)))))) in H1.
     rewrite <- mod_dist_Fmul in H1.
    assert (FmulInv (VlastS (Vtail (VandermondeCol m (sval e.1)))) *
        VlastS (Vtail (VandermondeCol m (sval e.1))) = 1).
    field; auto. rewrite VlastS_nth. rewrite Vnth_tail. rewrite Vbuild_nth.
    apply VF_prod_const_Nzero. apply (proj2_sig e.1).
    rewrite H8 in H1. rewrite mod_id in H1. rewrite H1.
    rewrite VlastS_map2. rewrite H4. clear H1.
    rewrite Vmap2_remove_last. rewrite <- Vmap2_tail.
    unfold VG_Pexp. rewrite comEPCDis. rewrite comEPCDis. pose VF_mult_ass.
    unfold VF_mult in e0. rewrite e0. rewrite VandermondeColDiv.
    rewrite VF_scale_map2.
    unfold VF_mult. rewrite VandermondeColDiv.
    unfold VG_prod. rewrite <- EPCMultExt. rewrite EPCneg. rewrite EPCMult.
    rewrite <- EPCExp. do 2 rewrite VlastS_tail. rewrite VlastS_map2. do 2 rewrite VlastS_add.
    trivial.  apply (proj2_sig e.1). apply (proj2_sig e.1).
     apply Vforall_nth_intro.
    intros. rewrite Vnth_tail. rewrite Vnth_tail. rewrite Vbuild_nth.
    apply VF_prod_const_Nzero. apply (proj2_sig e.1).
    ++++ unfold VG_Pexp in H4. rewrite <- Vtail_map2 in H4. rewrite Vtail_cons in H4.
    apply (H6 M.N (VF_inv (Vtail (Vtail (VandermondeCol m (sval e.1)))))) in H4.
    rewrite VG_Pexp_Pexp in H4. rewrite VF_inv_corr in H4.
    rewrite VG_One_exp in H4. rewrite H4. rewrite Vremove_last_Vtail.
    do 2 rewrite Vmap2_remove_last. do 2 rewrite Vremove_last_add. rewrite <- Vtail_map2.
    unfold VG_Pexp. rewrite comEPCDis. rewrite <- Vtail_map2. apply f_equal2.
    rewrite <- Vtail_map2. trivial. apply f_equal. apply Veq_nth. intros.
    rewrite Vnth_map.  do 4 rewrite Vnth_tail. do 2 rewrite Vbuild_nth.
    apply FmulInv_VF_prod_Vconst. apply (proj2_sig e.1).
    unfold VF_mult. rewrite <- Vtail_map2. apply f_equal. apply Veq_nth. intros.
    rewrite Vnth_map.  do 4 rewrite Vnth_tail. do 2 rewrite Vbuild_nth.
    apply FmulInv_VF_prod_Vconst. apply (proj2_sig e.1).

    apply Vforall_nth_intro.
    intros. rewrite Vnth_tail. rewrite Vnth_tail. rewrite Vbuild_nth.
    apply VF_prod_const_Nzero. apply (proj2_sig e.1).
    
    (* Commitments done time to start casing *)
    (* SZ case 1 *)
    ++ case_eq (VF_beq (VF_zero n) (Vfold_left (VF_add (n:=n)) (VF_zero n)
      (Vmap2 (VF_mult (n:=n)) t0 t))); intros.
    (* Commitment case *)
    case_eq (VF_beq (VlastS t0) (VF_neg (VF_one n))); intros.
    (* SZ case 2 *)
    case_eq (bVforall2 (VF_beq (n:=n)) (Vtail (Vadd (Vmap2 (VF_scale (n:=n)) (Vremove_last t)
             (Vtail (VandermondeCol m (FmulInv (sval e.1)))))
          (VF_scale (VF_add (VlastS t) (VF_neg
          (Vfold_left (VF_add (n:=sig.n)) (VF_zero sig.n)
          (Vmap2 (VF_scale (n:=sig.n)) (Vtail (Vremove_last t))
          (Vconst (FmulInv (sval e.1)) M.N)))))
          (FmulInv (VlastS (Vtail (VandermondeCol m (sval e.1))))))))
    (* Second part *)
    (Vmap2 (VF_mult (n:=n)) (Vtail (Vcons
          (VF_scale (Vhead t) (FmulInv (sval e.1)))
          (Vremove_last t0)))
        (Vremove_last (Vadd (Vmap2 (VF_scale (n:=n)) (Vremove_last t)
             (Vtail (VandermondeCol m (FmulInv (sval e.1)))))
          (VF_scale (VF_add (VlastS t) (VF_neg
          (Vfold_left (VF_add (n:=sig.n)) (VF_zero sig.n)
          (Vmap2 (VF_scale (n:=sig.n)) (Vtail (Vremove_last t))
          (Vconst (FmulInv (sval e.1)) M.N)))))
          (FmulInv (VlastS (Vtail (VandermondeCol m (sval e.1)))))))))).
    (* Resuming main *)
    left. apply andb_true_iff. split. apply andb_true_iff. split.
    +++ apply VGeq. rewrite Prod_right_replace.  rewrite Prod_left_replace. apply H2.
    (* Now proving cB =  (EPC n h hs B s) *)
    +++ apply bool_eq_corr. do 2 rewrite Prod_right_replace.
    (* We need to get s.2 out of H2 *)
    apply Vadd_eq_elim_gen in H1. apply Vcons_eq_elim_gen in H3.
    destruct H3. apply Vadd_eq_elim_gen in H7. destruct H7. rewrite H7.
    unfold comEPC. rewrite <- Vtail_map2. rewrite VlastS_map2.
    do 2 rewrite VlastS_tail. do 2 rewrite VlastS_add. trivial.

    (* Now proving VF_beq B (Vfold_left (@VF_mult n) (VF_one n) A) *)
    +++ rewrite Prod_right_replace. rewrite Prod_left_replace. apply VF_beq_true.
    (* We will start by getting the hypotisis ready *)
    apply VF_beq_true in H4. apply VF_beq_true in H5.
    apply VF_beq_true_forall in H6.
    clear H5 H4 H3 H1 H2 H. rewrite Vtail_cons in H6. rewrite Vremove_last_add in H6.
    rewrite Vtail_Vadd in H6. apply Vadd_eq_elim_gen in H6. destruct H6.
    rewrite <- Vtail_map2 in H1. do 2 rewrite Vmap2_remove_last in H1.
    (* We need to prove that we can express the a_is as b *)
    assert (VF_scale (VlastS (Vremove_last t)) (VlastS (VandermondeCol m (FmulInv (sval e.1)))) =
      Vfold_left (VF_mult (n:=n)) (VF_one n)
       (Vcons (VF_scale (Vhead t) (FmulInv (sval e.1)))
       (Vremove_last (Vremove_last t0)))). unfold sig.W, m, M, sig.m in *.
    clear H0 H.
    induction M.N.
    ++++ (* Base case *)
    rewrite Vfold_left_Vcons_VFmult. rewrite Vfold_left_nil. rewrite VF_comm_mult.
    rewrite VF_mult_one. apply f_equal2.
    rewrite VlastS_nth. rewrite Vhead_nth. rewrite Vnth_remove_last. apply Vnth_eq.
    trivial. rewrite VlastS_nth. rewrite Vbuild_nth. unfold VF_prod.
    rewrite Vfold_left_head.  rewrite Vhead_const. trivial. intros. field; auto.
    ++++ (* Inductive cast *)
    apply Veq_elim_gen2 in H1. destruct H1. do 3 rewrite VlastS_map2 in H.
    do 3 rewrite VlastS_tail in H. rewrite H.
    rewrite Vremove_last_Vtail. rewrite VlastS_tail. rewrite VandermondeCol_remove.
    rewrite (IHn0 (Vremove_last t0) (Vremove_last v0) (Vremove_last t)
      (Vremove_last v)).
    do 2 rewrite Vfold_left_Vcons_VFmult. rewrite <- VF_mult_ass. apply f_equal2.
    rewrite VF_comm_mult. rewrite <- Vfold_left_Vadd_VFmul.
    rewrite <- VSn_addS. trivial. rewrite Vhead_Vremove_last. trivial.
    rewrite Vmap2_remove_last in H0.
    do 3 rewrite Vremove_last_Vtail in H0. rewrite VandermondeCol_remove in H0.
    rewrite H0. do 2 rewrite Vmap2_remove_last. trivial.
    ++++ rewrite H. do 2 rewrite VlastS_map2. rewrite VlastS_tail.
    rewrite H2. do 2 rewrite Vfold_left_Vcons_VFmult. rewrite <- VF_mult_ass.
    do 2 rewrite Prod_right_replace.
    apply f_equal2. rewrite VF_comm_mult. rewrite <- Vfold_left_Vadd_VFmul.
    rewrite <- VSn_addS. trivial. trivial.

    (* What if SW failed 1 *)
    +++ right. unfold argument. right. right. exists (Vcons (VF_scale (Vhead t) (FmulInv (sval e.1)))
          (Vremove_last t0)). exists (Vadd
          (Vmap2 (VF_scale (n:=n)) (Vremove_last t)
             (Vtail (VandermondeCol m (FmulInv (sval e.1)))))
          (VF_scale
             (VF_add (VlastS t)
                (VF_neg
                   (Vfold_left (VF_add (n:=sig.n)) (VF_zero sig.n)
                      (Vmap2 (VF_scale (n:=sig.n))
                         (Vtail (Vremove_last t))
                         (Vconst (FmulInv (sval e.1)) M.N)))))
             (FmulInv (VlastS (Vtail (VandermondeCol m (sval e.1))))))).
    exists (Vadd
          (VF_mult (Vremove_last v)
             (Vtail (VandermondeCol m (FmulInv (sval e.1)))))
          ((VlastS v -
            Vfold_left Fadd 0
              (Vmap2 Fmul (Vtail (Vremove_last v))
                 (Vconst (FmulInv (sval e.1)) M.N))) /
           VlastS (Vtail (VandermondeCol m (sval e.1))))).
    exists (Vcons (Vhead v / sval e.1)
          (Vremove_last v0)).
    split. trivial. split. trivial. split.
    ++++ trivial. symmetry. rewrite Vtail_cons. rewrite Vremove_last_add. clear H3.
    rewrite Vtail_Vadd. rewrite <- Vtail_map2. apply VF_beq_true in H4.
    rewrite VF_scale_map2. replace (VF_mult (Vtail (VandermondeCol m (FmulInv (sval e.1))))
           (Vtail (VandermondeCol m (sval e.1)))) with (VF_one (S M.N)).
    rewrite VF_scale_1_map. rewrite (VSn_addS (Vmap2 (VF_mult (n:=n)) t0 t)) in H4.
    rewrite Vfold_left_Vadd_VFadd in H4. rewrite <- Vmap2_remove_last.
    apply VF_add_move in H4. symmetry in H4. rewrite H4. rewrite VF_comm.
    rewrite VF_add_zero. rewrite VlastS_map2.
    rewrite (VSn_addS (Vtail (VandermondeCol m (sval e.1)))). rewrite Vadd_map2.
    rewrite Vfold_left_Vadd_VFadd. rewrite VlastS_add. rewrite VF_scale_scale.
    rewrite VF_scale_1_gen.  rewrite VF_scale_map2.
    unfold VF_mult. rewrite VandermondeColDiv2.
    rewrite VF_add_neg3. apply VF_beq_true in H5. rewrite H5.
    rewrite VF_neg_mul. rewrite VF_neg_neg. rewrite VF_comm_mult. rewrite VF_mult_one.
    trivial.  apply (proj2_sig e.1).
    field; auto. rewrite VlastS_tail. rewrite VlastS_build.
    apply VF_prod_const_Nzero. apply (proj2_sig e.1).
    (* Need to clean up the replace form before *)
    apply Veq_nth. intros. rewrite Vnth_const. rewrite Vnth_map2. do 2 rewrite Vnth_tail.
    do 2 rewrite Vbuild_nth. rewrite <- FmulInv_VF_prod_Vconst. field; auto.
    apply VF_prod_const_Nzero. apply (proj2_sig e.1).  apply (proj2_sig e.1).
    ++++ unfold not.  intros. apply not_true_iff_false in H6. apply H6.
    apply VF_beq_true_forall. trivial.
     (* What if the commitments failed *)
    +++ right. left. exists (EPC s.1.1.1 s.1.1.2 (VF_neg (VF_one n)) 0).
    exists (VlastS t0). exists (VF_neg (VF_one n)).
    exists (VlastS v0). exists 0. unfold relComEPC. split.
    apply VF_beq_false in H5. trivial. split. apply Vadd_eq_elim_gen in H.
    destruct H. rewrite H. rewrite VlastS_map2. trivial. trivial.
    (* What if SW failed 2 *)
    +++ right. unfold argument. right. left. exists t0. exists t.
    exists v0. exists v. split. apply H.
    split. apply H1. split. apply H0. apply VF_beq_false in H4. trivial.
  Qed.

  Lemma e_abgrp : AbeGroup E add zero bool_eq disjoint inv.
  Proof.
    pose G2.module_abegrp.
    intros. constructor; intros. constructor; intros. constructor; intros.
    apply injective_projections; simpl. apply dot_assoc. field; auto.
    apply injective_projections; unfold add, zero. rewrite Prod_left_replace.
    apply one_left. do 2 rewrite Prod_right_replace. field; auto.
    apply injective_projections; simpl. apply one_right. field; auto.
    split; intros. apply andb_true_iff in H. destruct H.
    apply bool_eq_corr in H. apply F_bool_eq_corr in H0.
    apply injective_projections; auto.
    apply andb_true_iff. split. apply bool_eq_corr; rewrite H; auto.
    apply F_bool_eq_corr; rewrite H; auto.
    unfold bool_eq. rewrite bool_eq_sym. apply f_equal. apply F_bool_eq_sym.
    split; intros. apply andb_false_iff in H. destruct H. apply bool_neq_corr in H.
    unfold not. intros.  apply H. rewrite H0. auto. apply F_bool_neq_corr in H.
    unfold not. intros.  apply H. rewrite H0. auto. apply andb_false_iff.
    case_eq (G2.Gbool_eq a0.1 b.1); intros. right. apply F_bool_neq_corr.
    unfold not. intros. apply H. apply injective_projections. apply bool_eq_corr.
    trivial. trivial. left. trivial.
    unfold disjoint. rewrite bool_eq_sym. apply f_equal. rewrite F_bool_eq_sym.
    trivial.
    apply andb_true_iff in H. destruct H. apply negb_true_iff in H.
    apply bool_neq_corr in H. unfold not. intros. apply H. rewrite H1. trivial.
    apply injective_projections; simpl. apply inv_left. field; auto.
    apply injective_projections; simpl. apply inv_right. field; auto.
    apply injective_projections; simpl. apply comm. field; auto.
  Qed.

  Definition X := sig.X.

  Definition simulator (s : St)(t : TE)(e : E) : C :=
    let h   := s.1.1.1 in
    let hs  := s.1.1.2 in
    let CA  := s.1.2 in
    let cB  := s.2 in

     (Vmap (fun x => EPC h hs (VF_zero n) x) t).

  Definition simMap    (s : St)(w : W)(e : E)(x : X)(r : R) : TE :=
     VF_add r (Vbuild (fun i (ip : i < M.N) => VF_inProd x
     (Vfold_left (VF_mult (n:=n)) (VF_one n) (Vsub w.1.1.1 (IndexCB ip))))).
  Definition simMapInv (s : St)(w : W)(e : E)(x : X)(t : TE) : R :=
      (VF_sub t (Vbuild (fun i (ip : i < M.N) => VF_inProd x
     (Vfold_left (VF_mult (n:=n)) (VF_one n) (Vsub w.1.1.1 (IndexCB ip)))))).

  Definition simMapHelp (st: St)(x: X) : Prop :=
    let h   := st.1.1.1 in
    let hs  := st.1.1.2 in

    hs = Vmap (op h) x.

  Definition sigXcomp (s : St)(x : X) : sig.X := x.

  (* This may need more preconditions otherwise it might be too strong *)
  Lemma simMapHelpValid : forall (st : St)(x : X)(c : C)(e : E),
    simMapHelp st x ->
    sig.simMapHelp (ToSt (st,c,e)) (sigXcomp st x).
  Proof.
    intros. unfold sig.simMapHelp, ToSt, sigXcomp. simpl. apply H.
  Qed.

  Lemma simulatorZK1 : forall s w r e x,
     Rel s w ->
     simMapHelp s x ->
     (P0 s r w).2 = simulator s (simMap s w e x r) e.
  Proof.
    intros. unfold P0, simulator, simMap. rewrite Prod_right_replace. apply Veq_nth.
    intros. rewrite Vnth_map. rewrite Vnth_map2.
    rewrite Vbuild_nth. rewrite (trapdoorEPC s.1.1.1 x H0). rewrite Vnth_map2.
    rewrite Vbuild_nth. trivial.
  Qed.

  Lemma simMapInvValid : forall (st : St)(w : W)(x : X)
        (e : E)(r : R)(t : TE),
     Rel st w ->
     simMapHelp st x ->
    simMap st w e x (simMapInv st w e x t) = t /\
    simMapInv st w e x (simMap st w e x r) = r.
  Proof.
    intros. split.
    + unfold simMap, simMapInv. rewrite VF_add_neg2. trivial.
    + unfold simMap, simMapInv. rewrite VF_sub_corr. rewrite VF_add_neg. trivial.
  Qed.

End BGHadProdIns.
