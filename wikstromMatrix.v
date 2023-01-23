 Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
From Groups Require Import groups module vectorspace 
    dualvectorspaces matrices matricesF modulevectorspace.
Require Import sigmaprotocol.
Require Import basicSigmas.
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
Set Implicit Arguments.

(*This is a proof of the extended extractor of the Wikstrom mixnet in 
  the general case

  Outstanding issues:
    
     Need to actually add Matrix inverses 
        (At present we axiomist over it)
 *)


Module WikstromMixnet (G G1 G2 : GroupSig)(Ring : RingSig)(Field : FieldSig)
    (VS2 : VectorSpaceSig G2 Field)
    (VS1 : VectorSpaceSig G1 Field)
    (MVS : VectorSpaceModuleSameGroup G1 Ring Field VS1)
    (enc : Mixable G G1 Ring Field VS1 MVS)(Hack : Nat).

  Module BS := BasicSigmas G2 Field VS2.
  Import BS.

  Module WS := wikSigma G G1 G2 Ring Field VS2 VS1 MVS enc Hack.
  Import WS.


  Import Hack.
  Import Field.

  Module Mo := MatricesFIns Field.
  Import Mo.
  Module MoC := MatricesG G1 Field VS1 Mo.

    (* Make commitment scheme and matrix *)
  Module EPC := ExtendComScheme G2 Field VS2 Mo.
  Import EPC.
  Import MoM.
  Module PC := BasicComScheme G2 Field VS2 Mo.
  Import PC.
    

  Definition randomnessVector : nat -> Set := vector Ring.F.

  (* Addational vector lemma *)
  Module ALVS1 := VectorSpaceAddationalLemmas G1 Field VS1.
  Module ALVS2 := VectorSpaceAddationalLemmas G2 Field VS2.

  Module ALenc := MixablePropIns G G1 Ring Field VS1 MVS enc.
  Import ALenc.
  Module HardProb := HardProblems G2 Field VS2.
  Import HardProb.

  Module ALR := RingAddationalLemmas Ring.

  Import VS2.
  Import G2.

  (** We attempt to prove the correctness of Wikstrom's mix net latter step
      We take as a building block the DLog sigma from Helios
  *)

  (** 
    We will briefly describe the constrains

    wikS := M*M*M*(M^n)*(M^n)*(M^n)*(R^n)*(M^n)*(M^n)*(M^n)*(M^n)
           g pk h  h_i   c_i  ^c_i   u_i   a_i  b_i    a'_i  b'_i
    wikW := R*  R*      R*    R*   (R^n)     *(R^n)
           rBar rTilde rPrime rHat rHatPrime  u'

    where rBar = sum r_i where ^c_i = h^r_i h_pi_i
    where rTilde = cross product of u and r
    where rPrime = cross product of u and r
    where rHat = realted to ^c_n with r^

    wikC := M*M*M*M*(M^n)
    wikR :=   R    *R  *R * R  * R^N * R^N
             w_1 w_2 w_3 w_4     w'     w^
    wikE := E
    wikT := R*R*R*R*(R^n)*(R^n)

  *)

  Infix "+" := Fadd.
  Infix "*" := Fmul.
  Notation "x / y" := (Fmul x (FmulInv y)). 
  Notation "0" := Fzero.
  Notation "1" := Fone.
  Notation "- x" :=  (Finv x).
  Notation "x - y" := (x + (- y)).

  Infix "o" := Gdot (at level 50) .
  Notation "- x" := (Ginv x).

  Infix "^" := op.

  Notation " [ x ; .. ; y ] " := (Vcons x .. (Vcons y Vnil) ..).


  (* Relationships for the primary statments *)

  Definition relComEPC (h :G)(hs : VG (1+N))(c : G) (*Stament*)
                (m1 m2 : VF (1+N))(r1 r2 : F) :=  (*Witness *)
    m1 <> m2 /\
    c = (EPC h hs m1 r1) /\ c = (EPC h hs m2 r2). 

  Lemma PCbreaksEPC : (* We can use this to 
    simply the statment if anyone cares *)
    forall (h :G)(h1 : G)(hs : VG (1+N))(c : G) (*Stament*)
                (m1 m2 : F)(r1 r2 : F),
    Vhead hs = h1 ->
    relComPC h h1 c m1 m2 r1 r2 ->
    relComEPC h hs c (Vcons m1 (VF_zero N)) 
        (Vcons m2 (VF_zero N)) r1 r2.
  Proof.
    pose G2.module_abegrp.
    intros. unfold relComEPC. unfold relComPC in H0.
    destruct H0. destruct H1. split. unfold not.
    intros. apply Vcons_eq in H3. destruct H3. apply H0 in H3.
    apply H3. unfold EPC. unfold PC in *.
    simpl. rewrite VG_Zero_exp. do 2 rewrite VG_prod_Vcons.
    rewrite VG_Zero_prod. do 2 rewrite one_left.
    rewrite H. rewrite <- H1. rewrite <- H2.
    split. trivial. trivial.
  Qed.
    
  (* The commitment is to a permutation *)
  Definition relPi (h :G)(hs : VG (1+N))(c : VG (1+N)) (*Statment *)
    (m : MF (1+N))(r : VF (1+N)) :=       (*Witness*)
      MFisPermutation m
       /\ c = (com (1+N) h hs m r).

  Definition RF_inProd (N : nat)(a : VF N)(b : randomnessVector N) : Ring.F :=
    Vfold_left Ring.Fadd Ring.Fzero (Vmap2 MVS.op3 b a).

  Definition RF_CVmult (N : nat)(M : MF N)(v : randomnessVector N) : randomnessVector N :=
    Vmap (fun a => RF_inProd a v) M.

  (* Defination of shuffling *) (* e2_i = e1_p_i * r_p_i *)
  Definition relReEnc(pk : enc.PK)(e e' : vector G1.G (1+N))(m : MF (1+N))
    (r : randomnessVector (1+N)) :=
    let e'' := MoC.PexpMatrix e' m in
    let r'' := RF_CVmult m r in 
    let partial := Vmap2 (fun e e' => IsReEnc pk e e') e e'' in
    let partial2 := Vmap2 (fun x y => x y) partial r'' in
      Vforall (fun x => x ) partial2.

  Definition WikRel(pk : enc.PK)(e e' : vector G1.G (1+N))
    (g h :G)(hs : VG (1+N))(c : VG (1+N)) :=
    (exists (r : randomnessVector (1+N))(r' : VF (1+N))(m : MF (1+N)), 
      (relReEnc pk e e' m r /\ relPi g hs c m r'))  \/ 
    ((exists (c: G)(m1 m2 : VF (1+N))(r1 r2 : F),
       relComEPC g hs c m1 m2 r1 r2) \/ (
        exists (c: G)(m m' : F)(r1 r2 : F),
       relComPC g h c m m' r1 r2)).

  (* Relationships from the underlying sigma protocol *)
  (* the basic extractor pulls the following values:
    rBar (F) rDim (F) rTil (F) rStar (F) rHat (R*F) u' (R*F)
    which statisfy the following relations *)

  Definition SigStatment1 (c : VG (1+N))(h :G)(hs : VG (1+N))(rBar : F) :=
    VG_prod c = EPC (1+N) h hs (VF_one (1+N)) rBar.

  Definition SigStatment2 (c : VG (1+N))(h :G)(hs : VG (1+N))(u u' : VF (1+N))(rTil : F) :=
    VG_prod (VG_Pexp c u) = EPC (1+N) h hs u' rTil.

  Definition SigStatment3 (pk : enc.PK)(e e' : vector G1.G (1+N))(u u' : VF (1+N))
    (rStar : Ring.F) :=
    MoC.VG_prod (MoC.VG_Pexp e' u')  = 
      G1.Gdot (enc.enc pk enc.Mzero (Ring.Finv rStar)) (MoC.VG_prod (MoC.VG_Pexp e u)).

  Definition SigStatment4 (h h1 : G)(cHat : vector G (1+N))(u' rHat : VF (1+N)) :=
    (Vhead cHat) = PC h h1 (Vhead u') (Vhead rHat) /\ 
      (Vforall2 (@eq G) (Vtail cHat) (Vmap2 (fun x y => x y)
       (Vmap2 (fun h1 u r => PC h h1 u r) (Vremove_last cHat) (Vtail u')) (Vtail rHat))).

  Definition SigStatment5 (h h1 :G)(cHat : VG (1+N))(u : VF (1+N))(rDim : F) :=
    Vnth cHat (indexN) = PC h h1 (VF_prod u) rDim.

  Lemma Vfold_left_Fadd_v :
    forall (n : nat)(v v' : VF n),
    v = v' -> Vfold_left Fadd 0 v = Vfold_left Fadd 0 v'.
  Proof.
    intros. rewrite H. trivial.
  Qed.

  (* Stuff about EPC *)
  Lemma EPCProduct0 :
    forall(n : nat)(nM : nat)(h : G)(hs : VG nM),
    forall(g : forall i, Nat.lt i n  -> VF nM),
    forall(f : forall i, Nat.lt i n  -> F),
    let messages := Vbuild (fun j jp => (g j jp)) in 
    let randomness := Vbuild (fun j jp => (f j jp)) in 
    VG_prod (Vbuild (fun j jp => EPC nM h hs (g j jp) (f j jp))) =
    EPC nM h hs (Vfold_left_rev (VF_add (n:=nM)) (VF_zero nM) messages)
       (VF_sum randomness).
Proof.
   pose G1.module_abegrp. pose G2.module_abegrp. pose enc.M_abgrp.
  (*Base case is easy *)
  intros. induction n.
  cbn. unfold EPC. rewrite mod_ann. rewrite VG_Zero_exp. 
  rewrite VG_Zero_prod. rewrite one_right. trivial.
  (* now for the hard part *)
  rewrite VG_prod_induction. rewrite Vbuild_head.
  rewrite Vbuild_tail. rewrite IHn. rewrite <- EPC_add.
  replace (g 0%nat (Nat.lt_0_succ n)) with (Vhead messages).
  replace (Vbuild
           (fun (j : nat)
              (jp : (j < n)%nat) =>
            g (Datatypes.S j) (lt_n_S jp))) with (Vtail messages).
  replace (f 0%nat (Nat.lt_0_succ n)) with (Vhead randomness).
  replace (Vbuild
        (fun (j : nat) (jp : (j < n)%nat)
         => f (Datatypes.S j) (lt_n_S jp))) with (Vtail randomness).
  rewrite <- Vfold_left_add. rewrite VF_sum_induction. trivial.
  (*clean up *)
  unfold randomness. apply Vbuild_tail.
  unfold randomness. apply Vbuild_head.
  unfold messages. apply Vbuild_tail.
  unfold messages. apply Vbuild_head.
Qed. 

  Lemma EPCProduct_sub_lemma1 :
    forall (i n n' : nat)(v : vector (VF n) n')(ip : Nat.lt i n),
    Vnth (Vfold_left_rev (VF_add (n:=n)) (VF_zero n) v) ip
      = Vfold_left_rev Fadd Fzero 
      (Vmap (fun v => Vnth v ip) v).
Proof.
  intros. induction v. cbn. rewrite Vnth_const. trivial.
  (* part 2 *)
  cbn. rewrite Vnth_map2. rewrite IHv. trivial.
Qed.

  Theorem EPCProduct :
    forall(n : nat)(h : G)(hs : VG n),
    forall(U' A : MF n),
    forall(rTil : VF n)(i : nat)(ip : Nat.lt i n),
      EPC n h hs (MF_VCmult (Vnth A ip) U')
         (VF_inProd (Vnth A ip) rTil) = 
     VG_prod (Vbuild (fun j jp => EPC n h hs (VF_scale (Vnth U' jp) (Vnth (Vnth A ip) jp))
    ((Vnth rTil jp) * (Vnth (Vnth A ip) jp)))).
  Proof.
    pose G1.module_abegrp. pose G2.module_abegrp. pose enc.M_abgrp.
  intros. rewrite EPCProduct0. apply EPC_m_r_eq.
  (* part 1 *)
  apply Veq_nth. intros. unfold MF_VCmult. 
  unfold FMatrix.row_mat_to_vec, FMatrix.mat_mult, FMatrix.vec_to_row_mat, FMatrix.get_row.
  rewrite FMatrix.mat_build_nth. cbn. unfold FMatrix.VA.dot_product.
  rewrite EPCProduct_sub_lemma1. unfold FSemiRingT.Aplus, FSemiRingT.A0.
  apply Vfold_left_rev_eq. apply Veq_nth. intros.
  rewrite Vnth_map2. do 2 rewrite Vnth_map. rewrite Vbuild_nth.
  unfold VF_scale. rewrite Vnth_map. unfold FSemiRingT.Amult.
  destruct Field.vs_field. destruct F_R. apply Rmul_comm.
  (*part 2 *)
  unfold VF_inProd, FMatrix.VA.dot_product, VF_sum, FSemiRingT.Aplus.
  unfold FSemiRingT.A0, FSemiRingT.Amult. 
  rewrite Vfold_left_Fadd_eq. apply Vfold_left_Fadd_v.
  apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vbuild_nth. 
  destruct  Field.vs_field. destruct vs_field.
  destruct F_R. apply Rmul_comm.
  Qed.

  Lemma EPCExp :
    forall (n : nat)(h : G)(hs : VG n)(m : VF n)(r : F)(s :F),
    EPC n h hs (VF_scale m s) (r*s) = EPC n h hs m r ^ s.
  Proof.
    pose G1.module_abegrp. pose G2.module_abegrp. pose enc.M_abgrp.
    intros. unfold EPC. rewrite mod_dist_Gdot.
    rewrite <- mod_dist_FMul2. apply left_cancel.
    symmetry. apply VG_prod_VG_Pexp_scale.
  Qed.

  Theorem EPCExp_in_build :
   forall (n : nat)(h : G)(hs : VG n)(U' : MF n)(rTil v : VF n),
   Vbuild
       (fun (j : nat) (jp : (j < n)%nat) =>
        EPC n h hs
          (VF_scale (Vnth U' jp) (Vnth v jp))
          (Vnth rTil jp * Vnth v jp)) =
  Vbuild
       (fun (j : nat) (jp : (j < n)%nat) =>
        EPC n h hs (Vnth U' jp) (Vnth rTil jp) ^ (Vnth v jp)).
  Proof.
    intros. apply Veq_nth. intros. do 2 rewrite Vbuild_nth.
    apply EPCExp.
  Qed.

  Lemma logicLemma :
    forall a b: bool,
    a = false \/ b = false ->
    a = true ->
    b = false.
  Proof.
    intros. destruct H. congruence. apply H.
  Qed.

  Lemma prodLemma :
    forall (n : nat)(a b: VF n),
    VF_prod a <> VF_prod b -> a <> b.
  Proof.
    intros. unfold not in *. intros. rewrite H0 in H. apply H. trivial.
  Qed.

  Theorem Sigma1Helper :
    forall(g h : G)(hs : VG (1+N))(c : VG (1+N)), (*Commitment parameters and matrix commitmnets *)
    (* For primary challenges *)
    forall(U : MF (1+N)),
    forall(cHat : vector (VG (1+N)) (1+N)),
    forall(rBar rDim rTil : VF (1+N))(rStar : randomnessVector (1+N))(rHat U' : MF (1+N)),
    (* such that the secondary witnesses hold *)
    (* M2F_deter U <> 0 -> *)
    let f := (fun rBar U U' rTil rStar cHat rHat rDim => SigStatment1 c g hs rBar 
       /\ SigStatment2 c g hs U U' rTil /\
        SigStatment4 g h cHat U' rHat /\
        SigStatment5 g h cHat U rDim) in
   
    let res := Vmap2 (fun x y => x y)  (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y)
     (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) 
      (Vmap2 (fun x y => f x y) rBar U) U') rTil) rStar) cHat) rHat) rDim in 

    Vforall (fun x => x) res ->
    forall (i: nat)(ip : Nat.lt i (1+N)),
     SigStatment1 c g hs (Vnth rBar ip).
Proof.
  intros. apply (Vforall_nth ip) in H. unfold res in H. unfold f in H.
  do 7 rewrite Vnth_map2 in H. destruct H. apply H.
Qed.

  Theorem Sigma2Helper :
    forall(g h : G)(hs : VG (1+N))(c : VG (1+N)), (*Commitment parameters and matrix commitmnets *)
    (* For primary challenges *)
    forall(U : MF (1+N)),
    forall(cHat : vector (VG (1+N)) (1+N)),
    forall(rBar rDim rTil : VF (1+N))(rStar : randomnessVector (1+N))(rHat U' : MF (1+N)),
    (* such that the secondary witnesses hold *)
    (* M2F_deter U <> 0 -> *)
    let f := (fun rBar U U' rTil rStar cHat rHat rDim => SigStatment1 c g hs rBar 
       /\ SigStatment2 c g hs U U' rTil /\
        SigStatment4 g h cHat U' rHat /\
        SigStatment5 g h cHat U rDim) in
   
    let res := Vmap2 (fun x y => x y)  (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y)
     (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) 
      (Vmap2 (fun x y => f x y) rBar U) U') rTil) rStar) cHat) rHat) rDim in 

    Vforall (fun x => x) res ->
    forall (i: nat)(ip : Nat.lt i (1+N)),
     SigStatment2 c g hs (Vnth U ip) (Vnth U' ip) (Vnth rTil ip).
Proof.
  intros. apply (Vforall_nth ip) in H. unfold res in H. unfold f in H.
  do 7 rewrite Vnth_map2 in H. destruct H. destruct H0. apply H0.
Qed.

  Theorem Sigma4Helper :
    forall(g h : G)(hs : VG (1+N))(c : VG (1+N)), (*Commitment parameters and matrix commitmnets *)
    (* For primary challenges *)
    forall(U : MF (1+N)),
    forall(cHat : vector (VG (1+N)) (1+N)),
    forall(rBar rDim rTil : VF (1+N))(rStar : randomnessVector (1+N))(rHat U' : MF (1+N)),
    (* such that the secondary witnesses hold *)
    (* M2F_deter U <> 0 -> *)
    let f := (fun rBar U U' rTil rStar cHat rHat rDim => SigStatment1 c g hs rBar 
       /\ SigStatment2 c g hs U U' rTil /\
        SigStatment4 g h cHat U' rHat /\
        SigStatment5 g h cHat U rDim) in
   
    let res := Vmap2 (fun x y => x y)  (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y)
     (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) 
      (Vmap2 (fun x y => f x y) rBar U) U') rTil) rStar) cHat) rHat) rDim in 

    Vforall (fun x => x) res ->
    forall (i: nat)(ip : Nat.lt i (1+N)),
     SigStatment4 g h (Vnth cHat ip) (Vnth U' ip) (Vnth rHat ip).
Proof.
  intros. apply (Vforall_nth ip) in H. unfold res in H. unfold f in H.
  do 7 rewrite Vnth_map2 in H. destruct H. destruct H0. destruct H1.
  apply H1.
Qed.

  Theorem Sigma5Helper :
    forall(g h : G)(hs : VG (1+N))(c : VG (1+N)), (*Commitment parameters and matrix commitmnets *)
    (* For primary challenges *)
    forall(U : MF (1+N)),
    forall(cHat : vector (VG (1+N)) (1+N)),
    forall(rBar rDim rTil : VF (1+N))(rStar : randomnessVector (1+N))(rHat U' : MF (1+N)),
    (* such that the secondary witnesses hold *)
    (* M2F_deter U <> 0 -> *)
    let f := (fun rBar U U' rTil rStar cHat rHat rDim => SigStatment1 c g hs rBar 
       /\ SigStatment2 c g hs U U' rTil /\
        SigStatment4 g h cHat U' rHat /\
        SigStatment5 g h cHat U rDim) in
   
    let res := Vmap2 (fun x y => x y)  (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y)
     (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) 
      (Vmap2 (fun x y => f x y) rBar U) U') rTil) rStar) cHat) rHat) rDim in 

    Vforall (fun x => x) res ->
    forall (i: nat)(ip : Nat.lt i (1+N)),
     SigStatment5 g h (Vnth cHat ip) (Vnth U ip) (Vnth rDim ip).
Proof.
  intros. apply (Vforall_nth ip) in H. unfold res in H. unfold f in H.
  do 7 rewrite Vnth_map2 in H. destruct H. destruct H0. destruct H1.
  apply H2.
Qed.

  Lemma matrixCommitment_2to3_support :
    forall (n i : nat)(ip : Nat.lt i n)(g : forall i, Nat.lt i n  -> VG n),
    Vmap (fun v0 : vector G n => Vnth v0 ip) (Vbuild
     (fun (j : nat) (jp : (j < n)%nat) => g j jp)) = 
     Vbuild (fun (j : nat) (jp : (j < n)%nat) => Vnth (g j jp) ip).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. 
    do 2 rewrite Vbuild_nth. trivial.
  Qed.

  Lemma prod_of_exp_is_sum :
    forall (n : nat)(a : G)(g : forall i, Nat.lt i n  -> F),
     Vfold_left Gdot Gone (Vbuild (fun (j : nat) (jp : (j < n)%nat) =>
      a ^ (g j jp))) = a ^ VF_sum (Vbuild (fun (j : nat) (jp : (j < n)%nat) =>
    (g j jp))). 
  Proof.
  pose G1.module_abegrp. pose G2.module_abegrp. pose enc.M_abgrp.
  intros. induction n. cbn. rewrite mod_ann. trivial.
  rewrite (VSn_eq (Vbuild (fun (j : nat) (jp : (j < 1+n)%nat)
      => a2 ^ g j jp))). rewrite Vfold_left_Vcons. rewrite Vbuild_tail.
  rewrite IHn. rewrite Vhead_nth. rewrite Vbuild_nth.
  rewrite <- mod_dist_Fadd. rewrite <- Vbuild_tail.
  replace (g 0%nat (Nat.lt_0_succ n)) with (Vhead (Vbuild g)).
  rewrite <- VF_sum_induction. cbn. trivial.
  rewrite Vhead_nth. rewrite Vbuild_nth. trivial.
  Qed.

  Lemma matrixCommitment_2to3 :
    forall (n : nat)(c : VG n)(U : MF n)(v : VF n),
    Vfold_left (VG_mult (n:=n))(VG_id n)
       (Vbuild (fun (j : nat) (jp : (j < n)%nat) =>
       VG_Pexp c (VF_scale (Vnth U jp)(Vnth v jp)))) =
     VG_Pexp c (MF_VCmult v U) .
Proof.
  intros. apply Veq_nth. intros. rewrite Vfold_left_VG_mult.
  rewrite matrixCommitment_2to3_support. unfold VG_Pexp.
  rewrite Vnth_map2.
  (* this should probably be moved somewhere else *)
  pose G1.module_abegrp. pose G2.module_abegrp. pose enc.M_abgrp.
  assert (forall g : forall i, Nat.lt i n  -> VF n,
   Vbuild (fun (j : nat) (jp : (j < n)%nat) => Vnth (Vmap2 op c (g j jp)) ip) =
    Vbuild (fun (j : nat) (jp : (j < n)%nat) =>
    (Vnth c ip) ^ (Vnth (g j jp) ip))). intros. apply Veq_nth.
  intros. do 2 rewrite Vbuild_nth. rewrite Vnth_map2. trivial.
  (* end of strange *)
  rewrite H. rewrite prod_of_exp_is_sum.
  assert (forall a b c, b=c -> a^b = a^c).
  intros. rewrite H0. trivial.
  apply H0. unfold MF_VCmult.
  unfold FMatrix.row_mat_to_vec, FMatrix.mat_mult, FMatrix.vec_to_row_mat, FMatrix.get_row.
  rewrite FMatrix.mat_build_nth. unfold FMatrix.VA.dot_product.
  unfold VF_sum. rewrite Vfold_left_Fadd_eq. apply Vfold_left_Fadd_v.
  apply Veq_nth. intros. rewrite Vbuild_nth. rewrite Vnth_map2.
  cbn. rewrite Vnth_map. unfold FSemiRingT.Amult.
  rewrite FMatrix.get_elem_swap. 
  destruct Field.vs_field. destruct F_R. apply Rmul_comm.
Qed.

  Lemma prod_of_epc :
    forall (n m : nat)(h : G)(hs : VG m)(A : vector (VF m) n)(v : VF n),
    VG_prod (Vmap2 (EPC m h hs) A v) =  
        EPC m h hs (Vfold_left (VF_add (n:=m)) (VF_zero m) A) (VF_sum v).
Proof.
  pose G1.module_abegrp. pose G2.module_abegrp. pose enc.M_abgrp.
  intros. induction n. cbn. unfold EPC. rewrite (Vector_0_is_nil v).
  rewrite (Vector_0_is_nil A). cbn. rewrite mod_ann. rewrite VG_Zero_exp.
  rewrite VG_Zero_prod. symmetry. apply one_right.
  (* part 2 *)
  rewrite (VSn_eq A). rewrite (VSn_eq v). unfold VG_prod.
  assert ((Vmap2 (EPC m h hs)(Vcons (Vhead A)(Vtail A))(Vcons (Vhead v)
  (Vtail v))) = Vcons (EPC m h hs (Vhead A) (Vhead v))(Vmap2 (EPC m h hs)
   (Vtail A) (Vtail v))). cbn. auto.
  rewrite H. rewrite Vfold_left_Vcons. 
  unfold VG_prod in IHn. rewrite IHn.
  rewrite <- EPC_add. apply EPC_m_r_eq.
  cbn. rewrite Mo.Vfold_VFadd_const. trivial.
  unfold VF_sum. rewrite Vfold_left_Vcons_Fadd.
  trivial.
Qed.

  Lemma prod_of_com :
    forall (n : nat)(h : G)(hs : VG n)(A : MF n)(v : VF n),
    VG_prod (com n h hs A v) = 
       EPC n h hs (Vfold_left (VF_add (n:=n)) (VF_zero n) A) (VF_sum v).
Proof.
  intros. unfold com.
  rewrite prod_of_epc. apply EPC_m_r_eq. 
  (* m *)  
  + apply Veq_nth. intros. trivial.
  (* r *)
  + trivial.
Qed.

  Lemma sum_add_transpose :
    forall (n : nat)(B : MF (1+n)),
    Vfold_left (VF_add (n:=1 + n)) (VF_zero (1 + n)) B =
    Vmap (VF_sum (n:=1+n)) (FMatrix.mat_transpose B).
Proof.
  intros. unfold MF in *. apply Veq_nth. intros. rewrite Vfold_left_VF_add.
  rewrite Vnth_map. unfold VF_sum. pose (FMatrix.mat_transpose_col_row B).
  unfold FMatrix.get_row in e. rewrite e. apply Vfold_left_Fadd_v. apply Veq_nth.
  intros.  rewrite Vnth_map. trivial.
Qed.

  Lemma CVmult_all_ones :
    forall (n : nat)(B : MF n),
    Vmap (VF_sum (n:=n)) B =
    MF_CVmult B (VF_one n).
Proof.
 intros. unfold MF_CVmult, FMatrix.mat_vec_prod.
 unfold FMatrix.col_mat_to_vec, FMatrix.mat_mult.
 apply Veq_nth. intros. do 2 rewrite Vnth_map.
 rewrite FMatrix.mat_build_nth. rewrite FMatrix.get_col_col_mat.
 unfold FMatrix.VA.dot_product, FMatrix.get_row.
 unfold FSemiRingT.Aplus, FSemiRingT.A0, FSemiRingT.Amult.
 pose (VF_mult_one (Vnth B ip)). unfold VF_mult in e.
  rewrite e. unfold VF_sum. rewrite Vfold_left_Fadd_eq.
 trivial.
Qed.

  Lemma VCmult_all_ones :
    forall (n : nat)(B : MF n),
    Vmap (VF_sum (n:=n)) (FMatrix.mat_transpose B) =
    MF_VCmult (VF_one n) B.
Proof.
 intros. unfold MF_VCmult, FMatrix.mat_vec_prod.
 unfold FMatrix.row_mat_to_vec, FMatrix.mat_mult.
 apply Veq_nth. intros. unfold FMatrix.get_row. rewrite Vnth_map.
 rewrite FMatrix.mat_build_nth. unfold FMatrix.vec_to_row_mat. simpl.
 unfold FMatrix.VA.dot_product, FMatrix.get_row.
 unfold FSemiRingT.Aplus, FSemiRingT.A0, FSemiRingT.Amult.
 unfold VF_sum. rewrite Vfold_left_Fadd_eq. 
 assert (Vmap2 Fmul (VF_one n) (FMatrix.get_col B ip) = 
  (Vmap2 Fmul (FMatrix.get_col B ip) (VF_one n))). apply Veq_nth.
 intros. do 2 rewrite Vnth_map2. apply Field.vs_field.
  rewrite H. pose (VF_mult_one (FMatrix.get_col B ip)). unfold VF_mult in e.
  rewrite e. rewrite <- FMatrix.mat_transpose_col_row. unfold FMatrix.get_row.
 trivial.
Qed.

  Lemma succ_lt : forall(a b : nat),
    Nat.lt (1+a) (1+b) -> Nat.lt a b.
Proof.
  intros a b. intros. apply lt_S_n. apply H.
Qed.

  Lemma succ_lt2 : forall(a b : nat),
    Nat.lt (1+a) b -> Nat.lt a b.
Proof.
  intros. apply le_Sn_le. apply H.
Qed.

  Lemma less_then_zero : forall(j : nat),
    Nat.lt j 0 -> False. (* Or more general any contridication *)
  Proof.
    intros. apply lt_le_S in H. omega.
  Qed.

  Lemma a_minus_b_zero : forall (a b : nat),
    Nat.le b a -> 0%nat = Nat.sub a b -> a = b.
  Proof.
    intros. apply minus_Sn_m in H. induction a. omega.
    omega.
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
  intros. rewrite H. rewrite H0. trivial. apply H.
  rewrite <- (takeRemoveLast ip). trivial. rewrite Vnth_sub. apply Vnth_eq.
  omega. auto.
Qed. 


  (* end of take section *)

  Definition RandCon (n : nat)(v : vector (F*F) n) :=
    Vfold_left (fun ac x => x.2 + x.1 * ac) 0 v.

  Lemma RandConSucc : forall (n : nat)(v : vector (F*F) (1+n))(np : Nat.lt n (1+n)),
    RandCon v = (Vnth v np).2 + (Vnth v np).1 * (RandCon (Vremove_last v)).
Proof.
  intros. unfold RandCon. rewrite Vfold_left_remove_last. trivial.
Qed.

  Lemma Statment4_cruch :
    forall (h h1 : G)(cHat : VG (1+N))(u' rHat : VF (1+N)),
    let comb := Vmap2 (fun x y => (x,y)) u' rHat in
    SigStatment4 h h1 cHat u' rHat ->
    Vnth cHat indexN = PC h h1 (VF_prod u') 
     (RandCon comb).
Proof.
  destruct Field.vs_field. destruct F_R.
  intros. unfold SigStatment4 in H. destruct H.
  assert (forall (i :nat)(ip : Nat.le (0+(1+i)) (1+N))(ip' : Nat.lt i (1+N)),
      let u'sub := Vsub u' ip  in 
      let rHatSub := Vsub rHat ip in 
      let combSub := Vmap2 (fun x y => (x,y)) u'sub rHatSub in
      Vnth cHat ip' = PC h h1 (VF_prod u'sub) (RandCon combSub)).
  (* beginning induction *)
  intros. induction i. rewrite (VSn_eq u'sub). rewrite (VSn_eq combSub).
  rewrite (Vector_0_is_nil (Vtail u'sub)). rewrite (Vector_0_is_nil (Vtail combSub)).
  simpl. assert (Vnth cHat ip' = Vhead cHat). rewrite Vhead_nth.
  apply Vnth_eq. trivial. rewrite H1. rewrite H.
  apply PC_m_r_eq. unfold VF_prod. rewrite Vfold_left_Vcons_Fmul.
  simpl. rewrite Rmul_1_l. rewrite Vhead_nth. apply Vnth_eq.
  trivial. unfold RandCon. simpl. assert (forall a, a * 0 = 0). intros.
  rewrite Rmul_comm. apply FSRth.
  rewrite H2. rewrite Radd_comm. rewrite Radd_0_l. rewrite Vhead_nth. apply Vnth_eq. trivial. 
  (* induction part 2 *)
  assert (Nat.lt i N). apply succ_lt. apply ip. 
  apply (Vforall2_elim_nth H1) in H0. assert (Vnth cHat ip' = Vnth (Vtail cHat) H1).
  rewrite Vnth_tail. apply Vnth_eq. trivial.
  rewrite H2. rewrite H0. do 2 rewrite Vnth_map2.
  assert (Nat.lt i (1 + N)). apply succ_lt2. apply ip.
  pose (IHi H3). assert ((Vnth (Vremove_last cHat) H1) = 
  Vnth cHat H3). rewrite Vnth_remove_last_intro. trivial.
  rewrite H4. rewrite e. rewrite PC_up0. apply PC_m_r_eq.
  (* proving message equal *) 
  unfold VF_prod. 
  unfold u'sub. rewrite Vnth_tail. symmetry. rewrite takeMult. intros. 
  symmetry. assert (forall a b b', b =b' -> a*b = a*b').
  intros. rewrite H5. trivial. apply H5. apply Vnth_eq. trivial.
  (* proving randomness equal *)
  unfold combSub, u'sub, rHatSub. symmetry. rewrite RandConSucc. intros. 
  rewrite Vnth_map2. unfold fst. unfold snd. assert (forall a a' b b' c c', 
  a=a' -> b=b' -> c=c' -> a+b*c = a'+c'*b'). intros.  rewrite H5. rewrite H6.
  rewrite H7. rewrite Rmul_comm. trivial. apply H5. rewrite Vnth_tail.
  rewrite Vnth_sub. apply Vnth_eq. trivial. rewrite Vnth_tail. rewrite Vnth_sub. 
  apply Vnth_eq. trivial. assert (forall n (a b : vector (F*F) n),
   a=b -> RandCon a = RandCon b). intros. rewrite H6. trivial. apply H6. 
   rewrite Vremove_last_vmap2. apply Vmap2_eq. rewrite <- (takeRemoveLast H3).
  trivial. rewrite <- (takeRemoveLast H3). trivial. auto.
 (* Finsing up *)
  rewrite H1. intros. apply PC_m_r_eq. rewrite Vsub_id. trivial.
  do 2 rewrite Vsub_id. trivial. auto.
Qed.

  (* Now prove the sub theorem about matrix commitments
      we annotate with line numbers which correspond to 
      equation on page 11 of the paper *)
  Theorem matrixCommitment :
   (*for all statments *)
    forall(g h : G)(hs : VG (1+N))(c : VG (1+N)), (*Commitment parameters and matrix commitmnets *)
    (* For primary challenges *)
    forall(U A : MF (1+N)),
    forall(cHat : vector (VG (1+N)) (1+N)),
    (*for all secondary witnesses *)
    forall(rBar rDim rTil : VF (1+N))(rStar : randomnessVector (1+N))(rHat U' : MF (1+N)),
    (* such that the secondary witnesses hold *)
    (* M2F_deter U <> 0 -> *)
    let f := (fun rBar U U' rTil rStar cHat rHat rDim => SigStatment1 c g hs rBar 
       /\ SigStatment2 c g hs U U' rTil /\
        SigStatment4 g h cHat U' rHat /\
        SigStatment5 g h cHat U rDim) in
   
    let res := Vmap2 (fun x y => x y)  (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y)
     (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) 
      (Vmap2 (fun x y => f x y) rBar U) U') rTil) rStar) cHat) rHat) rDim in 

    Vforall (fun x => x) res ->
    (* Schwarz-Zippel *)
    let B := (MF_mult A U') in 
    let m := B in
    MF_mult U A = (MF_id (1+N)) ->
    MF_mult A U = (MF_id (1+N)) ->

    (*Things we assume which would preferably wouldn't *)
    (MFisPermutation B = false -> (
    VF_beq (MF_VCmult (VF_one (1+N)) B) (VF_one (1+N)) &&
    Fbool_eq (VF_prod (MF_VCmult (Vnth U index0) B) -
     VF_prod (Vnth U index0)) 
    0) = false) ->

      relPi g hs c B (MF_CVmult A rTil)  \/ 
    ((exists (c: G)(m1 m2 : VF (1+N))(r1 r2 : F),
       relComEPC g hs c m1 m2 r1 r2) \/ (
        exists (c: G)(m m' : F)(r1 r2 : F),
       relComPC g h c m m' r1 r2)).  
Proof.
  destruct Field.vs_field.
  intros g h hs c U A cHat rBar rDim rTil rStar rHat U' f res sigmaGood B m inv inv2.
  (* We show that the (rTil A) opens the commitment to b, this is
  the proof on the top part of page 11 of the write up *)
    case_eq (Fbool_eq (VF_prod (Vnth U' index0)) (VF_prod (Vnth U index0))).
  assert (c = com (1+N) g hs B (MF_CVmult A rTil)).
  unfold com. unfold B. apply Veq_nth. intros.
  (* prepare support *)
  assert (forall (i:nat)(ip: Nat.lt i (1+N)),
   SigStatment2 c g hs (Vnth U ip) (Vnth U' ip) (Vnth rTil ip)). intros.
  eapply (Sigma2Helper sigmaGood ip0). 
  rewrite Vnth_map2. unfold SigStatment2 in H. rewrite MF_getRow_prod. (* line 8 *)
  rewrite MF_getRow_VCmul. (* line 7 *) 
  rewrite EPCProduct. (* line 6 *)
  rewrite EPCExp_in_build. (* line 5 *)
  assert ((Vbuild (fun (j : nat) (jp : (j < 1 + N)%nat) =>
   EPC (1 + N) g hs (Vnth U' jp) (Vnth rTil jp) ^ Vnth (Vnth A ip) jp)) 
  = (Vbuild (fun (j : nat) (jp : (j < 1 + N)%nat) => VG_prod 
  (VG_Pexp c (Vnth U jp)) ^ Vnth (Vnth A ip) jp))). apply Veq_nth.
  intros. do 2 rewrite Vbuild_nth. rewrite <- H. trivial. 
  rewrite H0. (* line 4 *)
  assert ((Vbuild (fun (j : nat) (jp : (j < 1 + N)%nat) =>
      VG_prod (VG_Pexp c (Vnth U jp)) ^ Vnth (Vnth A ip) jp)) =
 (Vbuild (fun (j : nat) (jp : (j < 1 + N)%nat) =>
   VG_prod (VG_Pexp c (VF_scale (Vnth U jp) (Vnth (Vnth A ip) jp)))))).
  apply Veq_nth. intros. do 2 rewrite Vbuild_nth. apply VG_prod_VG_Pexp_scale.
  rewrite H1.
  (*line 3 *)
  rewrite VGprod_rearrange.
  (* line 2 *)
  rewrite matrixCommitment_2to3.
  (* line 1 *)
  rewrite <- MF_getRow_VCmul. rewrite <- invComm; auto. rewrite inv.
  rewrite MF_Vnth_id. rewrite VG_n_exp. trivial. 
  (* We show that everything works is a permutation *)
  intros. case_eq (MFisPermutation B).
  intros. left. unfold relPi. split. apply H2. apply H.  
  (* Finished proof for when B is a permutation *)
  intros. right. left. 
  case_eq (VF_beq (MF_VCmult (VF_one (1+N)) B) (VF_one (1+N))).
  (* Opening when M1 eq 1 *)
  intros. apply H1 in H2.
  apply andb_false_iff in H2. apply logicLemma in H2.
  remember (MF_VCmult (Vnth U index0) B) as u''.
  exists (VG_prod (VG_Pexp c (Vnth U index0))).
  exists (Vnth U' index0). exists u''. exists (Vnth rTil index0).
  exists (Vnth rTil index0).
  unfold relComEPC. split.
  (* U'1 <> u'' *)
  apply prodLemma. unfold not. intro. apply F_bool_eq_corr in H0.
  rewrite H0 in H4. rewrite Hequ'' in H4. apply F_bool_neq_corr in H2.
  unfold not in H2. apply H2. rewrite H4. rewrite Hequ''. apply F_R.
  (* opens to 1 *)
  split. assert (SigStatment2 c g hs (Vnth U index0) 
    (Vnth U' index0) (Vnth rTil index0)).
  intros. eapply (Sigma2Helper sigmaGood).
  unfold SigStatment2 in H4. apply H4.
  (* opens to 2 *)
  assert (SigStatment2 c g hs (Vnth U index0) 
    (Vnth U' index0) (Vnth rTil index0)).
  eapply (Sigma2Helper sigmaGood).
  unfold SigStatment2 in H4. rewrite H4.
  rewrite Hequ''. apply EPC_m_r_eq. rewrite <- MF_getRow_VCmul.
  unfold B. rewrite <- MF_assoc. rewrite inv.
  rewrite <- Id_comm. rewrite MF_one. trivial.
  (* part 2  of opens to 2 *)
  trivial. apply H3.
  (* Opening when M1 neq 1 *)
  intros. pose (MF_VCmult (VF_one (1+N)) B) as u''.
  exists (VG_prod c). exists (VF_one (1+N)). exists u''.
  exists (Vnth rBar index0). exists (VF_sum (MF_CVmult A rTil)).
  unfold relComEPC.
  (*  u'' neq 1 *)
  split.  unfold u''. apply VF_beq_false in H3.
  unfold not.  intros. symmetry in H4. unfold not in H3.
  apply H3 in H4. apply H4.
  (* opens to 1 *)
  split. 
  assert (SigStatment1 c g hs (Vnth rBar index0)).
  eapply (Sigma1Helper sigmaGood).
  unfold SigStatment1 in H4. apply H4.
  (* opens to 2 *)
  unfold u''. rewrite H. rewrite prod_of_com. apply EPC_m_eq.
  rewrite sum_add_transpose. rewrite <- VCmult_all_ones. trivial.
  (* Finish it up *)
  intros. right. right. exists (Vnth (Vnth cHat index0) indexN).
  exists (VF_prod (Vnth U' index0)). exists (VF_prod (Vnth U index0)).
  exists (RandCon (Vmap2 (fun x y => (x,y)) (Vnth U' index0) (Vnth rHat index0))).
  exists (Vnth rDim index0). unfold relComPC.
  split. apply F_bool_neq_corr. apply H. split.
  (* opening 1 *)
  assert (SigStatment4 g h (Vnth cHat index0) (Vnth U' index0) (Vnth rHat index0)).
  eapply (Sigma4Helper sigmaGood).
  rewrite (VSn_eq (Vnth cHat index0)). rewrite (VSn_eq (Vnth cHat index0)) in H1.
  rewrite (VSn_eq (Vnth U' index0)). rewrite (VSn_eq (Vnth rHat index0)).
  apply Statment4_cruch. rewrite (VSn_eq (Vnth U' index0)) in H1.
  rewrite (VSn_eq (Vnth rHat index0)) in H1. apply H1.
  (* opening 2 *)
  assert (SigStatment5 g h (Vnth cHat index0) (Vnth U index0) (Vnth rDim index0)).
  eapply (Sigma5Helper sigmaGood).
  unfold SigStatment5 in H1. apply H1.
Qed. 

Lemma Vfold_Fadd_const :  forall (n : nat)(v : randomnessVector n)(a : Ring.F),
    forall (h : Ring.F),
    Ring.Fadd (Vfold_left Ring.Fadd h v) a = 
      Vfold_left Ring.Fadd (Ring.Fadd h a) v.
  Proof.
    intros n v0 a. induction v0. cbn. intros. trivial. cbn. 
    intros. assert (Ring.Fadd (Vfold_left Ring.Fadd (Ring.Fadd h0 h) v0) a =
         Vfold_left Ring.Fadd (Ring.Fadd (Ring.Fadd h0 h) a) v0). apply IHv0.
    replace (Ring.Fadd (Ring.Fadd h0 a) h) with (Ring.Fadd (Ring.Fadd h0 h) a). apply H.
    pose Ring.module_ring. destruct r. rewrite <- Radd_assoc. 
    replace (Ring.Fadd h a) with (Ring.Fadd a h). rewrite Radd_assoc. trivial.
    apply Radd_comm.
  Qed.

Lemma VF_sum_induction :
    forall(N : nat)(v : randomnessVector (1+N)),
    Vfold_left Ring.Fadd Ring.Fzero v = 
      Ring.Fadd (Vfold_left Ring.Fadd Ring.Fzero (Vtail v)) (Vhead v).
Proof.
    intros. remember (Ring.Fadd (Vfold_left Ring.Fadd Ring.Fzero (Vtail v))
       (Vhead v)) as b.
    rewrite (VSn_eq v). rewrite Heqb. cbn. rewrite Vfold_Fadd_const.
    trivial.
Qed.

Lemma RF_inProd_zero :
  forall n (c : randomnessVector n),
   RF_inProd (VF_zero n) c = Ring.Fzero.
Proof.
  intros. induction n. cbn. trivial.
  unfold RF_inProd. rewrite VF_sum_induction.
  rewrite Vhead_nth. rewrite Vnth_map2. rewrite Vnth_const.
  rewrite MVS.RopFZero. pose Ring.module_ring. destruct r.
  rewrite Radd_comm. rewrite Radd_0_l. rewrite <- Vtail_map2.
  apply IHn.
Qed.

Lemma op3_dist_VF_sum :
  forall (n : nat)(a : randomnessVector n)(b : F),
  MVS.op3 (Vfold_left Ring.Fadd Ring.Fzero a) b = 
    Vfold_left Ring.Fadd Ring.Fzero (Vmap (fun x => MVS.op3 x b) a).
Proof.
  intros. induction n. rewrite (Vector_0_is_nil a). cbn.
  apply MVS.RopRZero. symmetry. rewrite VF_sum_induction.
  rewrite Vtail_map. rewrite <- IHn. rewrite Vhead_nth. 
  rewrite Vnth_map. rewrite <- MVS.RopDistRadd.
  rewrite <- Vhead_nth. rewrite <- VF_sum_induction. trivial.
Qed.

Lemma VF_sum_add : forall (N : nat)(a b : randomnessVector N),
    Ring.Fadd (Vfold_left Ring.Fadd Ring.Fzero a) 
    (Vfold_left Ring.Fadd Ring.Fzero b) = 
    Vfold_left Ring.Fadd Ring.Fzero (Vmap2 Ring.Fadd a b).
  Proof.
    pose Ring.module_ring. destruct r.
    intros. induction N0. rewrite (Vector_0_is_nil a). 
    rewrite (Vector_0_is_nil b).  cbn. 
    rewrite Radd_0_l. trivial. do 3 rewrite VF_sum_induction. 
    do 3 rewrite Vhead_nth. rewrite Vnth_map2. rewrite <- Vtail_map2. 
    rewrite <- IHN0. do 2 rewrite Radd_assoc.  trivial.
    apply ALR.F_right_cancel. do 2 rewrite <- Radd_assoc.
    apply ALR.F_left_cancel. rewrite Radd_comm. trivial.
 Qed.

Lemma RF_inProd_RF_CVmult_dist_sub :
  forall n n'  (a : VF n)(B : FMatrix.matrix n n') c, 
  RF_inProd a (Vmap ((RF_inProd (N:=n'))^~ c) B) =
    RF_inProd (FMatrix.row_mat_to_vec
     (FMatrix.mat_mult (FMatrix.vec_to_row_mat a) B)) c.
Proof.
  intros. induction n. cbn. replace (FMatrix.row_mat_to_vec
     (FMatrix.mat_mult (FMatrix.vec_to_row_mat a) B)) with (VF_zero n').
  symmetry. apply RF_inProd_zero. apply Veq_nth. intros. rewrite Vnth_const.
  rewrite FMatrix.Vnth_row_mat. rewrite FMatrix.mat_mult_spec. cbn. trivial.
  unfold RF_inProd. rewrite VF_sum_induction. rewrite <- Vtail_map2.
  rewrite Vtail_map. unfold RF_inProd in IHn. rewrite IHn.
  (* Inductive Hypo applied *)
  rewrite Vhead_nth. rewrite Vnth_map2. rewrite Vnth_map. 
  rewrite op3_dist_VF_sum. rewrite VF_sum_add.
  assert (forall a b : randomnessVector n', a = b -> Vfold_left Ring.Fadd Ring.Fzero
   a = Vfold_left Ring.Fadd Ring.Fzero b).
  intros. rewrite H. trivial. apply H. apply Veq_nth. intros. 
  do 3 rewrite Vnth_map2. rewrite Vnth_map. rewrite Vnth_map2.
  do 2 rewrite FMatrix.Vnth_row_mat. do 2 rewrite FMatrix.mat_mult_spec.
  rewrite MVS.RopDistFmul. rewrite <- MVS.RopDistFadd.
  assert (forall a b b',b=b' -> MVS.op3 a b = MVS.op3 a b').
  intros. rewrite H0. trivial. apply H0. pose Field.vs_field. 
  destruct f. destruct F_R.
  rewrite Radd_comm. rewrite FMatrix.VA.dot_product_comm. rewrite <- FMatrix.VA.dot_product_cons.
  assert (forall N (a a' b b': VF N), a=a' -> b=b' -> FMatrix.VA.dot_product a b =
  FMatrix.VA.dot_product a' b'). intros. rewrite H1. rewrite H2.
  trivial. rewrite FMatrix.VA.dot_product_comm. apply H1. cbn.
  rewrite <- Vhead_nth. rewrite <- VSn_eq. trivial.
  apply Veq_nth. intros. destruct i0. intros. 
  subst. cbn. rewrite FMatrix.get_elem_swap. apply Vnth_eq. trivial.
  cbn. do 2 rewrite <- FMatrix.get_elem_swap. unfold FMatrix.get_row.
  rewrite Vnth_tail. replace (Vnth B (lt_n_S (lt_S_n ip0))) with
  (Vnth B ip0). trivial. apply Vnth_eq. trivial.
Qed. 

Lemma RF_inProd_RF_CVmult_dist :
  forall n (a : VF n)(B : MF n) c, 
    RF_inProd a (RF_CVmult B c) = RF_inProd (MF_VCmult a B) c.
Proof.
  intros. unfold RF_CVmult, MF_VCmult. apply RF_inProd_RF_CVmult_dist_sub.
Qed.

Lemma temp2_support :  (*This lemma could be cleaned *)
    forall (n' n  : nat)(e' : vector G1.G n)(U : FMatrix.matrix n' n)(A : VF n')
    (i : nat)(ip : Nat.lt i n'),
     MoC.VG_prod (Vbuild 
        (fun (j : nat) (jp : (j < n')%nat) => MoC.VG_prod (MoC.VG_Pexp e'
                (VF_scale (Vnth U jp) (Vnth A jp))))) = 
        MoC.VG_prod (Vbuild (fun (j : nat) (jp : (j < n)%nat)
           => VS1.op (Vnth e' jp)
        (VF_inProd (FMatrix.get_col U jp) A))).
Proof.
  destruct Field.vs_field.
  intros. induction n. cbn. pose (VG_Zero_prod n'). unfold VG_id in e.
  rewrite MoC.VG_Zero_prod_build. trivial. rewrite (VSn_eq (Vbuild
     (fun (j : nat) (jp : (j < 1+n)%nat) =>
      VS1.op (Vnth e' jp) (VF_inProd (FMatrix.get_col U jp) A)))).
  rewrite MoC.VG_prod_Vcons. rewrite Vbuild_tail. rewrite Vbuild_head.
  (* Now I need use the Inductive hypotsis *)
  pose (IHn (Vtail e') 
    (FMatrix.mat_transpose (Vtail (FMatrix.mat_transpose U)))).
 assert (MoC.VG_prod (Vbuild (fun (j : nat) (jp : (j < n)%nat) =>
  VS1.op (Vnth (Vtail e') jp) (VF_inProd (FMatrix.get_col
      (FMatrix.mat_transpose (Vtail (FMatrix.mat_transpose U))) jp) A))) = 
 MoC.VG_prod (Vbuild (fun (i1 : nat) (ip1 : (i1 < n)%nat) =>
     VS1.op (Vnth e' (lt_n_S ip1)) (VF_inProd (FMatrix.get_col U (lt_n_S ip1)) A)))).
  apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vbuild_nth.
  rewrite Vnth_tail. assert(forall a a' b b', a=a' -> b=b' -> VS1.op a b = VS1.op a' b').
  intros. rewrite H. rewrite H0. trivial. apply H. trivial.
  assert(forall n (a a' b b': VF n), a=a' -> b=b' -> VF_inProd a b = VF_inProd a' b').
  intros.  rewrite H0. rewrite H1. trivial. apply H0. apply Veq_nth. intros.
  rewrite Vnth_map. pose FMatrix.mat_transpose_col_row. unfold FMatrix.get_row in e0.
  rewrite e0. symmetry. rewrite <- FMatrix.mat_transpose_col_row. rewrite Vnth_map.
  unfold FMatrix.get_row. apply Veq_nth2. rewrite Vnth_tail. trivial. trivial.
  symmetry in H. rewrite  H. symmetry in e. rewrite  e. rewrite MoC.VG_prod_vbuild.
  (* final clean up *)
  rewrite MoC.Vfold_Gdot_dob. rewrite MoC.Vmap2_Gdot_vbuild. 
  apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vbuild_nth.
  rewrite MoC.VG_prod_induction. assert (forall a b c d, a = b -> c = d -> 
    G1.Gdot a c = G1.Gdot b d). intros. rewrite H0. rewrite H1. trivial. apply H0.
  apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_tail.
  do 2 rewrite Vnth_map2.  assert (forall a b c d, a = b -> c = d -> 
    VS1.op a c = VS1.op b d). intros. rewrite H1. rewrite H2. trivial.
  apply H1. rewrite Vnth_tail. trivial.
  do 2 rewrite Vnth_map. pose FMatrix.mat_transpose_col_row. unfold FMatrix.get_row in e0.
  rewrite e0. rewrite Vnth_map. rewrite Vnth_tail. rewrite e0.
  rewrite Vnth_map. trivial. rewrite Vhead_nth. rewrite Vnth_map2.
  rewrite Vnth_map. assert (forall a b c d, a = b -> c = d -> 
    VS1.op a c = VS1.op b d). intros. rewrite H1. rewrite H2. trivial.
  apply H1. trivial. rewrite <- FMatrix.get_elem_swap. unfold FMatrix.get_row. trivial.
Qed.

  (* We need to construct a buch of vectors and sum them togeter *)
  Lemma temp2 :
    forall (n : nat)(e' : (vector G1.G (1+n)))(U A : (MF (1+n)))(i:nat)(ip:Nat.lt i (1+n)),
    MoC.VG_prod (MoC.VG_Pexp e' (MF_VCmult (Vnth A ip) U)) = 
     MoC.VG_prod (Vbuild (fun j jp => 
      VS1.op (MoC.VG_prod (MoC.VG_Pexp e' (Vnth U jp)))(Vnth (Vnth A ip) jp))).
Proof.
  intros. assert (Vbuild (fun (j : nat) (jp : (j < 1 + n)%nat) => 
        VS1.op (MoC.VG_prod  (MoC.VG_Pexp e' (Vnth U jp))) (Vnth (Vnth A ip) jp)) =
    (Vbuild (fun (j : nat) (jp : (j < 1 + n)%nat) => 
        (MoC.VG_prod  (MoC.VG_Pexp e' (VF_scale (Vnth U jp) (Vnth (Vnth A ip) jp))))))). 
  intros.  apply Veq_nth. intros. do 2 rewrite Vbuild_nth. 
  rewrite MoC.VG_prod_VG_Pexp_scale. trivial.  rewrite H. 
  (*Finished first move *)
  rewrite (temp2_support e' U (Vnth A ip) ip).
  (* clean it up *)
  apply Vfold_left_eq. apply Veq_nth. intros.  rewrite Vnth_map2. 
  rewrite MF_getCol_prod. unfold VF_inProd. 
  rewrite FMatrix.VA.dot_product_comm. rewrite Vbuild_nth.  trivial.
 Qed.

  Lemma temp4 : forall (n : nat),
    forall(g f : forall i, Nat.lt i (1+n)  -> G1.G),
    MoC.VG_prod
     (Vbuild
       (fun (j : nat) (jp : (j < (1+n))%nat) =>
        G1.Gdot (g j jp) (f j jp))) = 
    G1.Gdot (MoC.VG_prod (Vbuild
       (fun (j : nat) (jp : (j < (1+n))%nat) =>
       (g j jp)))) (MoC.VG_prod (Vbuild
       (fun (j : nat) (jp : (j < (1+n))%nat) =>
       (f j jp)))).
Proof.
  intros. rewrite <- MoC.Vmap2_Gdot_vbuild. rewrite MoC.VG_Prod_mult_dist. trivial.
Qed.


  Lemma temp5 :
    forall (n :nat)(e : vector G1.G n)(i :nat)(ip : Nat.lt i n),
    MoC.VG_prod (MoC.VG_Pexp e (Vnth (MF_id n) ip)) =
    Vnth e ip.
Proof.
  intros. rewrite MF_Vnth_id.
  rewrite MoC.VG_n_exp. trivial.
Qed.

  Lemma temp6 :
    forall (n : nat)(pk : enc.PK)(U : VF (1+n))(rStar : randomnessVector (1+n)),
    MoC.VG_prod
    (Vbuild
       (fun (j : nat) (jp : (j < (1+n))%nat) =>
        VS1.op (enc.enc pk enc.Mzero (Ring.Finv (Vnth rStar jp)))
         (Vnth U jp))) =
    enc.enc pk enc.Mzero (Vfold_left Ring.Fadd Ring.Fzero (Vmap2 MVS.op3 (Vmap Ring.Finv rStar) U)).
Proof.
  destruct Ring.module_ring. pose enc.M_abgrp.
  (* Base case *)
  intros. induction n. rewrite MoC.VG_prod_one_vec. rewrite Vbuild_head.
   rewrite enc.encOfOnePrec.
  apply EncEq. trivial. cbn. unfold FSemiRingT.Aplus, FSemiRingT.A0, FSemiRingT.Amult.
  rewrite Radd_0_l. assert (forall a b c d, a=b -> c=d -> 
  MVS.op3 a c= MVS.op3 b d). intros. rewrite H0. rewrite H. 
  trivial. apply H. rewrite Vhead_nth. rewrite Vnth_map.
  assert (forall a b, a=b -> Ring.Finv a = Ring.Finv b).
  intros. rewrite H0. trivial. apply H0. apply Vnth_eq. trivial.
  rewrite Vhead_nth. apply Vnth_eq. trivial. auto.
  (* Main case *)
  rewrite MoC.VG_prod_induction. rewrite Vbuild_tail. 
  assert ((Vbuild (fun (i : nat) (ip : i < Datatypes.S n) =>
    VS1.op (enc.enc pk enc.Mzero (Ring.Finv (Vnth rStar (lt_n_S ip)))) (Vnth U (lt_n_S ip)))) = 
    (Vbuild (fun (j : nat) (jp : j < 1 + n) => VS1.op (enc.enc pk enc.Mzero 
      (Ring.Finv (Vnth (Vtail rStar) jp)))(Vnth (Vtail U) jp)))). apply Veq_nth. intros. 
  do 2 rewrite Vbuild_nth. do 2 rewrite Vnth_tail. trivial. rewrite H.
  rewrite (IHn (Vtail U)(Vtail rStar)). rewrite Vhead_nth. rewrite Vbuild_nth.
  rewrite enc.encOfOnePrec. rewrite enc.homomorphism. apply EncEq.
  apply one_right. do 2 rewrite <- Vhead_nth. 
  symmetry. rewrite VF_sum_induction. rewrite Radd_comm.
  assert (forall a b c d, a=b -> c=d -> Ring.Fadd a c =
  Ring.Fadd b d). intros. rewrite H0. rewrite H1. trivial.
  apply H0. do 3 rewrite Vhead_nth. rewrite Vnth_map2. rewrite Vnth_map. trivial.
  assert (forall N (a b : randomnessVector N), a=b -> 
  Vfold_left Ring.Fadd Ring.Fzero a = Vfold_left Ring.Fadd Ring.Fzero b).
  intros. rewrite H1. trivial. apply H1. apply Veq_nth.
  intros. do 2 rewrite Vnth_map2. do 2 rewrite Vnth_tail. 
  do 2 rewrite Vnth_map. rewrite Vnth_tail. trivial.
Qed.

  Theorem Sigma3Helper :
    forall(pk : enc.PK)(e e' : (vector G1.G (1+N))), (* Forall keys and ciphertexts *)
    forall(g h : G)(hs : VG (1+N))(c : VG (1+N)), (*Commitment parameters and matrix commitmnets *)
    (* For primary challenges *)
    forall(U : MF (1+N)),
    forall(cHat : vector (VG (1+N)) (1+N)),
    forall(rBar rDim rTil : VF (1+N))(rStar : randomnessVector (1+N))(rHat U' : MF (1+N)),
    (* such that the secondary witnesses hold *)
    (* M2F_deter U <> 0 -> *)
    let f := (fun rBar U U' rTil rStar cHat rHat rDim => SigStatment1 c g hs rBar 
       /\ SigStatment2 c g hs U U' rTil /\ SigStatment3 pk e e' U U' rStar /\
        SigStatment4 g h cHat U' rHat /\
        SigStatment5 g h cHat U rDim) in
   
    let res := Vmap2 (fun x y => x y)  (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y)
     (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) 
      (Vmap2 (fun x y => f x y) rBar U) U') rTil) rStar) cHat) rHat) rDim in 

    Vforall (fun x => x) res ->
    forall (i : nat)(ip : Nat.lt i (1+N)),
     SigStatment3 pk e e' (Vnth U ip) 
        (Vnth U' ip) (Vnth rStar ip).
Proof.
  intros. apply (Vforall_nth ip) in H. unfold res in H. unfold f in H.
  do 7 rewrite Vnth_map2 in H. destruct H. destruct H0. destruct H1.
  apply H1.
Qed.

  Theorem extendedExtractor :
    (*for all statments *)
    forall(pk : enc.PK)(e e' : (vector G1.G (1+N))), (* Forall keys and ciphertexts *)
    forall(g h : G)(hs : VG (1+N))(c : VG (1+N)), (*Commitment parameters and matrix commitmnets *)
    (* For primary challenges *)
    forall(U A C : MF (1+N)),
    forall(cHat : vector (VG (1+N)) (1+N)),
    (*for all secondary witnesses *)
    forall(rBar rDim rTil : VF (1+N))(rStar : randomnessVector (1+N))(rHat U' : MF (1+N)),
    (* such that the secondary witnesses hold *)
    (* M2F_deter U <> 0 -> *)
    let f := (fun rBar U U' rTil rStar cHat rHat rDim => SigStatment1 c g hs rBar 
       /\ SigStatment2 c g hs U U' rTil /\ SigStatment3 pk e e' U U' rStar /\
        SigStatment4 g h cHat U' rHat /\
        SigStatment5 g h cHat U rDim) in
   
    let res := Vmap2 (fun x y => x y)  (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y)
     (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) 
      (Vmap2 (fun x y => f x y) rBar U) U') rTil) rStar) cHat) rHat) rDim in 

    Vforall (fun x => x) res ->
    (* Schwarz-Zippel *)
    let B := (MF_mult A U') in 
    let m := B in
    MF_mult U' C = (MF_id (1+N)) ->
    MF_mult C U' = (MF_id (1+N)) ->
    MF_mult U A = (MF_id (1+N)) ->
    MF_mult A U = (MF_id (1+N)) ->

    (*Things we assume which would preferably wouldn't *)
    (MFisPermutation B = false -> (
    VF_beq (MF_VCmult (VF_one (1+N)) B) (VF_one (1+N)) &&
    Fbool_eq (VF_prod (MF_VCmult (Vnth U index0) B) -
     VF_prod (Vnth U index0)) 
    0) = false) ->

    (* either the commitments are broken or we are happy *)
    (exists (r : randomnessVector (1+N))(r' : VF (1+N))(m : MF (1+N)), 
      (relReEnc pk e e' m r /\ relPi g hs c m r'))  \/ 
    ((exists (c: G)(m1 m2 : VF (1+N))(r1 r2 : F),
       relComEPC g hs c m1 m2 r1 r2) \/ (
        exists (c: G)(m m' : F)(r1 r2 : F),
       relComPC g h c m m' r1 r2)).
Proof.
  pose G1.module_abegrp.
  intros pk e e' g h hs c U A C cHat rBar rDim rTil rStar rHat U' f res.
  intros H B m inv inv2.  intros.
   assert (relPi g hs c (MF_mult A U') (MF_CVmult A rTil) 
     \/ ((exists (c: G)(m1 m2 : VF (1+N))(r1 r2 : F),
     relComEPC g hs c m1 m2 r1 r2) \/ (
      exists (c: G)(m m' : F)(r1 r2 : F), 
     relComPC g h c m m' r1 r2))).
    unfold f in res. unfold res in H.
    pose (matrixCommitment (U:=U)(c:=c)(hs:=hs)
     (g:=g)(h:=h)) as q. apply (q A cHat rBar rDim rTil rStar rHat); auto.
    apply Vforall_nth_intro. intros. apply (Vforall_nth ip) in H.
    do 7 rewrite Vnth_map2. do 7 rewrite Vnth_map2 in H. unfold f in H.
    destruct H. destruct H3. destruct H4. destruct H5. 
    split. apply H. split. apply H3. split. apply H5. apply H6.
    (* Case where the commitment is to a matrix *)
    assert (MF_eq U' (MF_mult U B)). unfold B. 
    rewrite <- MF_assoc. rewrite H0.
    rewrite <- Id_comm. rewrite MF_one. apply MFeq. trivial.
    destruct H3. 
    (* and U' = B U *)(*Proving ciphertexts are eual *)
    left. apply MFeq in H4. rewrite H4 in H3.
    rewrite <- MF_assoc in H3. assert (MF_mult U A = MF_mult A U).
    apply invComm; auto. rewrite H5 in H0.
    rewrite H0 in H3. rewrite <- Id_comm in H3. rewrite MF_one in H3.
    exists (RF_CVmult C (Vmap Ring.Finv rStar)). exists (MF_CVmult A rTil).
    exists B.  split.
    + unfold relReEnc. unfold IsReEnc. unfold reenc.
    apply Vforall_nth_intro. intros. do 2 rewrite Vnth_map2. unfold MoC.PexpMatrix.
    rewrite Vnth_map. (*
    remember (V2G_mult (Vnth e ip) (Enc g pk (Vnth (MF_CVmult B (MF_CVmult (MF_inv U') rStar)) ip) Gone)) as d.
    symmetry in Heqd. rewrite Heqd.*) (* success *) 
    rewrite Vnth_map.  assert (forall j (jp : Nat.lt j (1+N)), SigStatment3 pk e e' (Vnth U jp) 
      (Vnth U' jp) (Vnth rStar jp)). intros. eapply (Sigma3Helper 
    (pk:=pk)(e:=e)(e':=e')(g:=g)(h:=h)(hs:=hs)(c:=c)(U:=U)(cHat:=cHat)
    (rBar:=rBar)(rDim:=rDim)(rTil:=rTil)(rStar:=rStar)(rHat:=rHat)(U':=U')). 
    apply H. unfold SigStatment3 in H4. 
    rewrite <- (MF_one B). rewrite Id_comm.
    replace (MF_id (1+N)) with (MF_mult A U). (*line 9*)
    rewrite MF_assoc. rewrite <- H4. rewrite MF_getRow_VCmul. (* line 8  *)
    rewrite temp2. (* line 6 *)
    assert ((Vbuild (fun (j : nat)  (jp : (j < 1 + N)%nat) =>
      VS1.op (MoC.VG_prod (MoC.VG_Pexp e' (Vnth U' jp))) (Vnth (Vnth A ip) jp))) 
    = (Vbuild (fun (j : nat) (jp : (j < 1 + N)%nat) => VS1.op
        (G1.Gdot (enc.enc pk enc.Mzero (Ring.Finv (Vnth rStar jp))) (MoC.VG_prod
          (MoC.VG_Pexp e (Vnth U jp))))(Vnth (Vnth A ip) jp)))).
    apply Veq_nth. intros. do 2 rewrite Vbuild_nth. rewrite (H6 i0 ip0).
    intuition. rewrite H7. (* line 5 *) 
    assert ((Vbuild
     (fun (j : nat) (jp : (j < 1 + N)%nat) =>
      VS1.op
        (G1.Gdot (enc.enc pk enc.Mzero (Ring.Finv (Vnth rStar jp)))
           (MoC.VG_prod (MoC.VG_Pexp e (Vnth U jp))))
        (Vnth (Vnth A ip) jp))) = (Vbuild
     (fun (j : nat) (jp : (j < 1 + N)%nat) =>
      G1.Gdot (VS1.op (enc.enc pk enc.Mzero (Ring.Finv (Vnth rStar jp)))
        (Vnth (Vnth A ip) jp))
      (VS1.op (MoC.VG_prod (MoC.VG_Pexp e (Vnth U jp)))
        (Vnth (Vnth A ip) jp))))). apply Veq_nth. intros.
    do 2 rewrite Vbuild_nth. apply VS1.mod_dist_Gdot.
    rewrite H8. (*need to pull randomness out *)
   rewrite temp4. rewrite <- temp2. rewrite <- MF_getRow_VCmul.
  rewrite H0. rewrite temp5. rewrite comm. 
  assert (forall a a' b b', a =a' -> b = b' -> G1.Gdot a b = G1.Gdot a' b').
  intros.  rewrite H9. rewrite H10. trivial. symmetry. rewrite comm. apply H9.
  trivial. rewrite temp6. apply EncEq. trivial. 
  assert (forall N (a : VF N) B c, RF_inProd a (RF_CVmult B c) = RF_inProd 
    (MF_VCmult a B) c). intros.
  (* Need to prove this *)
  unfold RF_inProd. unfold RF_CVmult. 
  apply RF_inProd_RF_CVmult_dist_sub.
  rewrite H10. rewrite <- MF_getRow_VCmul.
  rewrite <- MF_getRow_VCmul. rewrite MF_assoc. rewrite inv.
  rewrite MF_one. trivial.
    + apply H3.
    (* trivial case where commitment isn't to a matrix *)
    + right. apply H3. 
Qed. 


  (*Having given the proof for the extended extractor we now crate
    the sigma protocol for the base statments. *) 
  Definition WikstromSigma :=
    genAndSigmaProtocol (genAndSigmaProtocol dLogForm dLogForm) (u'Form).

  Definition WikstromStatment (pk : enc.PK)(g h : G)(hs c cHat : VG (1+N))(u : VF (1+N))
    (e e' : (vector G1.G (1+N))) : Sigma.S WikstromSigma :=
    ((g, VG_prod c o - (VG_prod hs)),(g, (Vnth cHat indexN) o - h ^ (VF_prod u)),
      ((pk,g,h,hs,e'),(VG_prod (VG_Pexp c u),MoC.VG_prod (MoC.VG_Pexp e u),cHat))).

  Lemma WikstromExtractor :
    forall (pk : enc.PK)(g h : G)(hs c cHat : VG (1+N))(u : VF (1+N))(e e' : vector G1.G (1+N))
      (w : (F*F*((VF (1+N))*F*Ring.F*(VF (1+N))))),
    let Sig := WikstromSigma in
    let s := (WikstromStatment pk g h hs c cHat u e e') in 
    Sigma.Rel Sig s w ->
     VG_prod c o - VG_prod hs = g ^ w.1.1 /\
      (Vnth cHat indexN) o - h ^ (VF_prod u) = g ^ w.1.2 /\
    VG_prod (VG_Pexp c u) = EPC (1+N) g hs w.2.1.1.1 w.2.1.1.2  /\
    MoC.VG_prod (MoC.VG_Pexp e u) = G1.Gdot (MoC.VG_prod 
      (MoC.VG_Pexp e' w.2.1.1.1)) (enc.enc pk enc.Mzero (Ring.Finv w.2.1.2)) /\
    Vhead cHat = PC g h (Vhead w.2.1.1.1) (Vhead w.2.2) /\
    Vforall2 Gbool_eq (Vtail cHat) (Vmap2 (fun x y => x y)
       (Vmap2 (fun h1 u r => PC g h1 u r) (Vremove_last cHat) (Vtail w.2.1.1.1)) 
        (Vtail w.2.2)).
Proof.
  pose G1.module_abegrp.  pose G2.module_abegrp.
  intros. unfold Sig in *. unfold WikstromSigma in *.
  unfold parSigmaProtocol in *. simpl in *. unfold BS.HardProb.dLog in *.
  simpl in *. apply andb_true_iff in H. destruct H. 
  apply andb_true_iff in H. destruct H. 
  apply bool_eq_corr in H.  apply bool_eq_corr in H1.
  split. apply H. split. apply H1. unfold u'_Rel in H0.
  simpl in H0. apply andb_true_iff in H0. destruct H0. 
  apply andb_true_iff in H0. destruct H0. 
  apply andb_true_iff in H0. destruct H0. 
  apply bool_eq_corr in H0. split. apply H0.
  apply bool_eq_corr in H4. split. apply H4. split.
  apply bool_eq_corr in H3. do 3 rewrite Vhead_nth. do 3 rewrite index0eq. 
  apply H3. apply VGeq in H2. rewrite H2. apply Vforall2_intro_nth. intros.
  apply bool_eq_corr. trivial.
Qed.

  Lemma WikstromSigmaCorr :
    SigmaProtocol WikstromSigma.
Proof.
  intros. unfold WikstromSigma. apply andGenCorr. apply andGenCorr.
  apply dLogSigma. apply dLogSigma. trivial. apply u'Sigma.
  trivial.
Qed.
   
  Theorem SigmaImpliesAllGood :
    (*for all statments *)
    forall (pk : enc.PK)(e e' : (vector G1.G (1+N))), (* Forall keys and ciphertexts *)
    forall(g h : G)(hs : VG (1+N))(c : VG (1+N)), (*Commitment parameters and matrix commitmnets *)
    (* For primary challenges *)
    forall(U : MF (1+N)),
    (* M2F_deter U <> 0 -> *)
    forall(cHat : vector (VG (1+N)) (1+N)),
    let Sig := WikstromSigma in
    let s := Vmap2 (fun cHat col => WikstromStatment pk g h hs c cHat col e e') 
        cHat U  in
    (* Sigma protocols accept *)
    forall (com : vector (Sigma.C Sig) (1+N))(chal: vector (F*F) (1+N))
    (t : vector ((Sigma.T Sig)*(Sigma.T Sig)) (1+N)),

    let transcript := Vmap2 ( fun x y => (x,y)) (Vmap2 ( fun x y => (x,y)) (Vmap2 ( fun x y => (x,y)) s com) chal) t in

    Vforall (fun t => Sigma.V1 Sig (t.1.1.1,t.1.1.2,t.1.2.1,t.2.1) = true /\ 
      Sigma.V1 Sig (t.1.1.1,t.1.1.2,t.1.2.2,t.2.2) = true) transcript ->

    Vforall (fun e => Sigma.disjoint Sig e.1 e.2 = true) chal ->

    let w := Vmap (fun t => Sigma.extractor Sig t.2.1 t.2.2 t.1.2.1 t.1.2.2) transcript in
    let U' := Vmap (fun w => w.2.1.1.1) w in

    exists (rBar rDim rTil : VF (1+N))(rStar : randomnessVector (1+N))(rHat : MF (1+N)),

    let f := (fun rBar U U' rTil rStar cHat rHat rDim => SigStatment1 c g hs rBar 
       /\ SigStatment2 c g hs U U' rTil /\ SigStatment3 pk e e' U U' rStar /\
        SigStatment4 g h cHat U' rHat /\
        SigStatment5 g h cHat U rDim) in
   
    let res := Vmap2 (fun x y => x y)  (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y)
     (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) 
      (Vmap2 (fun x y => f x y) rBar U) U') rTil) rStar) cHat) rHat) rDim in 

    Vforall (fun x => x) res.
Proof.
    pose G1.module_abegrp.  pose G2.module_abegrp. pose enc.M_abgrp.
  intros. assert (forall i (ip : Nat.lt i (Nat.add 1%nat N)), Sigma.Rel Sig (Vnth s ip) 
    (Sigma.extractor Sig (Vnth t ip).1 (Vnth t ip).2 (Vnth chal ip).1 (Vnth chal ip).2)).
  intros. eapply special_soundness with (c:=(Vnth com0 ip)); auto. 
  apply WikstromSigmaCorr. apply (Vforall_nth ip) in H0. apply H0. apply (Vforall_nth ip) in H.
  destruct H. unfold transcript in H. do 3 rewrite Vnth_map2 in H. simpl in H.  apply H.
  apply (Vforall_nth ip) in H. destruct H. unfold transcript in H1. do 3 rewrite Vnth_map2 in H1.
  simpl in H1. apply H1.
  (* Setup complete beginning part 1 *)
  exists (Vmap (fun x => x.1.1) w). exists (Vmap (fun x => x.1.2) w).
  exists (Vmap (fun x => x.2.1.1.2) w). exists (Vmap (fun x => Ring.Finv x.2.1.2) w).
  exists (Vmap (fun x => x.2.2) w).
  unfold SigStatment1. unfold SigStatment2. unfold SigStatment3.
  unfold SigStatment4. unfold SigStatment5. apply Vforall_nth_intro.
  intros. do 7 rewrite Vnth_map2. do 9 rewrite Vnth_map. 
  assert (Sigma.Rel Sig (Vnth s ip) (Sigma.extractor Sig (Vnth t ip).1 
          (Vnth t ip).2 (Vnth chal ip).1 (Vnth chal ip).2)). apply H1.
  remember ((Sigma.extractor Sig (Vnth t ip).1 (Vnth t ip).2 (Vnth chal ip).1 
   (Vnth chal ip).2)) as wit. rewrite Vnth_map2 in H2. apply WikstromExtractor in H2.
  destruct H2. destruct H3. destruct H4. destruct H5. destruct H6.
  (* part 1.1 *)
  split. apply b_equal in H2. rewrite H2. unfold EPC.  rewrite VG_One_exp. 
  apply right_cancel. do 3 rewrite Vnth_map2. rewrite Heqwit. auto.
  (* part 1.2 *)
  split. rewrite H4. rewrite Heqwit. unfold transcript.
  do 3 rewrite Vnth_map2. apply EPC_m_r_eq. simpl. auto. simpl. auto.
  (* part 1.3 *)
  split. rewrite comm. rewrite H5. rewrite <- dot_assoc. rewrite enc.homomorphism.
  assert (forall (a b : F), a= b -> Fadd (Finv a) b = 0). intros. destruct Field.vs_field.
  destruct F_R. rewrite Radd_comm. rewrite H8. rewrite Ropp_def. auto.
  assert (forall (a b : Ring.F), a= b -> Ring.Fadd (Ring.Finv a) b = Ring.Fzero).
  intros. rewrite H9. destruct (Ring.module_ring). rewrite Radd_comm.
  apply Ropp_def. rewrite H9. rewrite Heqwit. unfold transcript. 
  do 3 rewrite Vnth_map2. auto. rewrite one_right. rewrite EncZeroZeroIsOne. 
  rewrite one_right. rewrite Heqwit. unfold transcript. do 3 rewrite Vnth_map2. auto.
  auto.
  (* part 1.4 (Part 1.4 and 1.5 are two parts of the same statment) *)
  split. split. rewrite H6. unfold transcript. rewrite Heqwit. do 3 rewrite Vnth_map2. 
  cbn. intuition.
  (* part 1.5 *)
  apply Vforall2_intro_nth. intros. do 2 rewrite Vnth_map2.  apply (Vforall2_elim_nth ip0) in H7.
  simpl in H7. apply bool_eq_corr in H7. rewrite H7. do 2 rewrite Vnth_map2. 
  rewrite Heqwit. unfold transcript. do 3 rewrite Vnth_map2. intuition.
  (* part 1.6 *)
  symmetry in H3. apply b_equal in H3. symmetry in H3. rewrite H3.
  assert (forall a, - - a = a). intros. symmetry. apply dob_neg. rewrite H8.
  unfold PC. rewrite Heqwit. rewrite Vnth_map. unfold transcript. 
  assert (forall a b c d, a =c -> b=d -> a o b = c o d). intros. rewrite H9. rewrite H10.
  trivial. apply H9. assert (forall a b, a=b -> g^a = g^b). intros. rewrite H10.
  trivial. apply H10.  unfold transcript. do 3 rewrite Vnth_map2. trivial. trivial.
Qed.

  Theorem TheMixnetIsSecure :
    (*for all statments *)
    forall(pk : enc.PK)(e e' : (vector G1.G (1+N))), (* Forall keys and ciphertexts *)
    forall(g h : G)(hs : VG (1+N))(c : VG (1+N)), (*Commitment parameters and matrix commitmnets *)
    (* For primary challenges *)
    forall(U A C : MF (1+N)),
    (* M2F_deter U <> 0 -> *)
    forall(cHat : vector (VG (1+N)) (1+N)),
    let Sig := WikstromSigma in
    let s := Vmap2 (fun cHat col => WikstromStatment pk g h hs c cHat col e e') 
        cHat U  in
    (* Sigma protocols accept *)
    forall (com : vector (Sigma.C Sig) (1+N))(chal: vector (F*F) (1+N))
    (t : vector ((Sigma.T Sig)*(Sigma.T Sig)) (1+N)),

    let transcript := Vmap2 ( fun x y => (x,y)) (Vmap2 ( fun x y => (x,y)) (Vmap2 ( fun x y => (x,y)) s com) chal) t in

    Vforall (fun t => Sigma.V1 Sig (t.1.1.1,t.1.1.2,t.1.2.1,t.2.1) = true /\ 
      Sigma.V1 Sig (t.1.1.1,t.1.1.2,t.1.2.2,t.2.2) = true) transcript ->

    Vforall (fun e => Sigma.disjoint Sig e.1 e.2 = true) chal ->

    let w := Vmap (fun t => Sigma.extractor Sig t.2.1 t.2.2 t.1.2.1 t.1.2.2) transcript in
    let U' := Vmap (fun w => w.2.1.1.1) w in

    let B := (MF_mult A U') in 
    let m := B in

    MF_mult U' C = (MF_id (1+N)) ->
    MF_mult C U' = (MF_id (1+N)) ->
    MF_mult U A = (MF_id (1+N)) ->
    MF_mult A U = (MF_id (1+N)) ->

    (MFisPermutation B = false -> (
    VF_beq (MF_VCmult (VF_one (1+N)) B) (VF_one (1+N)) &&
    Fbool_eq (VF_prod (MF_VCmult (Vnth U index0) B) -
     VF_prod (Vnth U index0)) 
    0) = false) ->
     WikRel pk e e' g h hs c.

Proof.
  intros. assert (exists (rBar rDim rTil : VF (1+N))(rStar : randomnessVector (1+N))(rHat : MF (1+N)),
  let f := (fun rBar U U' rTil rStar cHat rHat rDim => SigStatment1 c g hs rBar 
     /\ SigStatment2 c g hs U U' rTil /\ SigStatment3 pk e e' U U' rStar /\
      SigStatment4 g h cHat U' rHat /\
      SigStatment5 g h cHat U rDim) in
  let res := Vmap2 (fun x y => x y)  (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y)
   (Vmap2 (fun x y => x y) (Vmap2 (fun x y => x y) 
    (Vmap2 (fun x y => f x y) rBar U) U') rTil) rStar) cHat) rHat) rDim in
  Vforall (fun x => x) res).
  eapply (SigmaImpliesAllGood); auto. 
  pose (extendedExtractor (g:=g)(h:=h)(hs:=hs)(U:=U)(c:=c)(e':=e')(e:=e)
  (pk:=pk)) as q. do 5 destruct H6.  apply (q A C0 cHat x x0 x1 x2 x3 U');
  auto.
  Qed.

End WikstromMixnet.


