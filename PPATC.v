Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Ring.
Require Import Field. 
Require Import Field_theory.
From Groups Require Import groups module vectorspace dualvectorspaces
    nthvectorspaces modulevectorspace genprodvectorspaces groupfromring.
Require Import cryptoprim.
Require Import CoLoR.Util.Vector.VecUtil.

Module Type Ciphertext (G1 G2 : GroupSig) <: GroupSig.
  Definition G := prod (prod (prod (prod G1.G G1.G) G1.G) G2.G) G1.G.
  Definition Gdot (a b : G) : G := (G1.Gdot a.1.1.1.1 b.1.1.1.1, 
    G1.Gdot a.1.1.1.2 b.1.1.1.2, G1.Gdot a.1.1.2 b.1.1.2, G2.Gdot a.1.2 b.1.2,
    G1.Gdot a.2 b.2).
  Definition Gone := (G1.Gone,G1.Gone,G1.Gone,G2.Gone,G1.Gone).
  Definition Gbool_eq (a b : G) : bool := G1.Gbool_eq a.1.1.1.1 b.1.1.1.1 && 
    G1.Gbool_eq a.1.1.1.2 b.1.1.1.2 && G1.Gbool_eq a.1.1.2 b.1.1.2 && 
    G2.Gbool_eq a.1.2 b.1.2 && G1.Gbool_eq a.2 b.2.
  Definition Ginv (a : G) : G := (G1.Ginv a.1.1.1.1, 
    G1.Ginv a.1.1.1.2, G1.Ginv a.1.1.2, G2.Ginv a.1.2,
    G1.Ginv a.2).

  Lemma module_abegrp : AbeGroup G Gdot Gone Gbool_eq Ginv.
  Proof.
    pose G1.module_abegrp. pose G2.module_abegrp. destruct a. destruct a0.
    destruct abegrp_grp. destruct abegrp_grp0. destruct grp_mon. 
    destruct grp_mon0.
    (* dot assoc *)
    constructor. constructor. constructor. intros. unfold Gdot. 
    do 4 rewrite dot_assoc. rewrite dot_assoc0. trivial.
    (* id left *)
    intros. unfold Gdot. do 4 rewrite one_left. rewrite one_left0. destruct x.
    destruct p. destruct p. destruct p. simpl. trivial.
    (* id right *)
    intros. unfold Gdot. do 4 rewrite one_right. rewrite one_right0. destruct x.
    destruct p. destruct p. destruct p. simpl. trivial.
    (* bool_eq *)
    intros. unfold Gbool_eq. refine (conj _ _). intros. destruct a. destruct b. 
    destruct p. destruct p0. destruct p. destruct p0. destruct p. destruct p0. 
    simpl in *. intros. apply andb_true_iff in H. destruct H.
    apply andb_true_iff in H. destruct H. apply andb_true_iff in H. destruct H.
    apply andb_true_iff in H. destruct H. apply bool_eq_corr in H.
    apply bool_eq_corr in H0. apply bool_eq_corr in H2. apply bool_eq_corr in H3.
    apply bool_eq_corr0 in H1. rewrite H. rewrite H1. rewrite H2. rewrite H3.
    rewrite H0. trivial. intros. apply andb_true_iff. split.
    apply andb_true_iff. split.  apply andb_true_iff. split. 
    apply andb_true_iff. split.  apply bool_eq_corr. rewrite H. trivial.
    apply bool_eq_corr. rewrite H. trivial. apply bool_eq_corr. rewrite H. trivial.
    apply bool_eq_corr0. rewrite H. trivial. apply bool_eq_corr. rewrite H. trivial.
    (* bool_eq_not *)
    intros. unfold Gbool_eq. refine (conj _ _). intros.
    case_eq (G1.Gbool_eq a.1.1.1.1 b.1.1.1.1). intros.
    case_eq (G1.Gbool_eq a.1.1.1.2 b.1.1.1.2). intros. 
    case_eq (G1.Gbool_eq a.1.1.2 b.1.1.2). intros. 
    case_eq (G2.Gbool_eq a.1.2 b.1.2). intros.
    rewrite H0 in H. rewrite H1 in H. rewrite H2 in H. 
    rewrite H3 in H. simpl in H. apply bool_neq_corr in H.
    unfold not. intros. rewrite H4 in H. apply H. trivial.
    (* 1.2 *)
    intros. apply bool_neq_corr0 in H3. unfold not. intros.
    rewrite H4 in H3. apply H3. trivial.
    (* 1.3 *)
    intros. apply bool_neq_corr in H2. unfold not. intros.
    rewrite H3 in H2. apply H2. trivial.
    (* 1.4 *)
    intros. apply bool_neq_corr in H1. unfold not. intros.
    rewrite H2 in H1. apply H1. trivial.
    (* 1.5 *)
    intros. apply bool_neq_corr in H0. unfold not. intros.
    rewrite H1 in H0. apply H0. trivial.
    (* Fist part bool_neq_corr complete *)
    intros. unfold not in H. case_eq (G1.Gbool_eq a.1.1.1.1 b.1.1.1.1 &&
    G1.Gbool_eq a.1.1.1.2 b.1.1.1.2 &&
    G1.Gbool_eq a.1.1.2 b.1.1.2 &&
    G2.Gbool_eq a.1.2 b.1.2 && G1.Gbool_eq a.2 b.2).
    intros. assert False. apply H. apply andb_prop in H0.
    destruct H0. apply andb_prop in H0. destruct H0.
    apply andb_prop in H0. destruct H0. apply andb_prop in H0. destruct H0.
    apply bool_eq_corr in H0. apply bool_eq_corr in H1. 
    apply bool_eq_corr in H3. apply bool_eq_corr in H4.
    apply bool_eq_corr0 in H2. destruct a. destruct b.
    simpl in *. destruct p. destruct p0. simpl in *. destruct p.
    destruct p0. simpl in *. destruct p. destruct p0. simpl in *.
    rewrite H0. rewrite H1. rewrite H2. rewrite H3. rewrite H4.
    trivial. contradiction.
    intros. trivial.
    (* inv_left *)
    intros. unfold Gdot. simpl. do 4 rewrite <- inv_left.
    rewrite <- inv_left0. trivial.
    (* inv_right *)
    intros. unfold Gdot. simpl. do 4 rewrite <- inv_right.
    rewrite <- inv_right0. trivial.
    (* comm *)
    intros. unfold Gdot. simpl. apply injective_projections.
    simpl. apply injective_projections.
    simpl. apply injective_projections.
    simpl. apply injective_projections.
    simpl. apply comm. simpl. apply comm. simpl. apply comm.
    simpl. apply comm0. simpl. apply comm.
  Qed.
  

  Infix "o" := Gdot (at level 50) .
  Notation "- x" := (Ginv x).
End Ciphertext.

Module Type Nat.
  Parameter N : nat.
End Nat.

Module RN. (* The number of elements in the randomness tuple for PPATC *)
  Definition N := 3.
End RN.

Module Type VSofC (G1 G2 : GroupSig)(Field : FieldSig)
  (VS1 : VectorSpaceSig G1 Field)(VS2 : VectorSpaceSig G2 Field)
  (C : Ciphertext G1 G2) <: VectorSpaceSig C Field.

  Import C.
  Import Field.

  Definition op (a : G)(b : F) : G := 
    (VS1.op a.1.1.1.1 b, VS1.op a.1.1.1.2 b, VS1.op a.1.1.2 b, VS2.op a.1.2 b,
        VS1.op a.2 b).

  Lemma mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
  Proof.
    intros. unfold op. do 4 rewrite VS1.mod_dist_Gdot. rewrite VS2.mod_dist_Gdot.
    trivial.
  Qed.

  Lemma mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
  Proof.
    intros. unfold op. do 4 rewrite VS1.mod_dist_Fadd. rewrite VS2.mod_dist_Fadd.
    trivial.
  Qed.

  Lemma mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
  Proof.
    intros. unfold op. do 4 rewrite VS1.mod_dist_Fmul. rewrite VS2.mod_dist_Fmul.
    trivial.
  Qed.

  Lemma mod_id : forall (x : G), op x Fone = x.
  Proof.
    intros. unfold op. do 4 rewrite VS1.mod_id. rewrite VS2.mod_id.
    destruct x. do 3 destruct p. simpl. trivial.
  Qed.

  Lemma mod_ann : forall (x : G), op x Fzero = Gone.
  Proof.
    intros. unfold op. do 4 rewrite VS1.mod_ann. rewrite VS2.mod_ann.
    trivial.
  Qed.
  
End VSofC.

Module Type MVSoverC (G1 G2 : GroupSig)(Field : FieldSig)(C : Ciphertext G1 G2)
      (VS1 : VectorSpaceSig G1 Field)(VS2 : VectorSpaceSig G2 Field)    
      (Ring : NthRingSig RN Field)(VS : VSofC G1 G2 Field VS1 VS2 C) 
  <: VectorSpaceModuleSameGroup C Ring Field VS.

  Import Field.

  Definition op3 (a : Ring.F)(b : Field.F) : Ring.F :=
    Vmap (fun x => Field.Fmul x b) a.

  Lemma RopInv : forall a, op3 a (Field.Finv Field.Fone) = Ring.Finv a.
  Proof.
    intros. unfold op3. apply Veq_nth. intros. 
    do 2 rewrite Vnth_map. field; auto.
   Qed.
  Lemma RopInvDis : forall a b, op3 (Ring.Finv a) b = Ring.Finv (op3 a b).
  Proof.
    intros. unfold op3. apply Veq_nth. intros. 
    do 4 rewrite Vnth_map. field; auto.
   Qed.
  Lemma RopFZero : forall x, op3 x Field.Fzero = Ring.Fzero.
  Proof.
    intros. unfold op3. apply Veq_nth. intros. 
    rewrite Vnth_map. rewrite Vnth_const. field; auto.
   Qed.
  Lemma RopRZero : forall x, op3 Ring.Fzero x = Ring.Fzero.
  Proof.
    intros. unfold op3. apply Veq_nth. intros. 
    rewrite Vnth_map. rewrite Vnth_const. field; auto.
   Qed.
  Lemma RopDistRadd : forall x y z, op3 (Ring.Fadd x y) z = 
      Ring.Fadd (op3 x z) (op3 y z).
  Proof.
    intros. unfold op3. apply Veq_nth. intros. 
    rewrite Vnth_map. do 2 rewrite Vnth_map2.
    do 2 rewrite Vnth_map. field; auto.
   Qed.
  Lemma RopDistFadd : forall (r s : Field.F) (x : Ring.F), 
      op3 x (Field.Fadd r s) = Ring.Fadd (op3 x r) (op3 x s).
  Proof.
    intros. unfold op3. apply Veq_nth. intros. 
    rewrite Vnth_map. rewrite Vnth_map2.
    do 2 rewrite Vnth_map. field; auto.
   Qed.
  Lemma RopDistFmul : forall x y z, op3 (op3 x y) z = 
      op3 x (Field.Fmul y z).
  Proof.
    intros. unfold op3. apply Veq_nth. intros. 
    do 3 rewrite Vnth_map. field; auto.
   Qed.
  Lemma RaddInv : forall (a : Ring.F)(b : Field.F),
     (Ring.Fadd (op3 a b) (op3 a (Field.Finv b))) = Ring.Fzero.
  Proof.
    intros. unfold op3. apply Veq_nth. intros. 
    rewrite Vnth_map2. do 2 rewrite Vnth_map. 
    rewrite Vnth_const. field; auto.
   Qed.

End MVSoverC.

Module PPATC (G1 G2 : GroupSig)(Field : FieldSig)
  (VS1 : VectorSpaceSig G1 Field)(VS2 : VectorSpaceSig G2 Field)
  (C : Ciphertext G1 G2)(Ring : NthRingSig RN Field)
  (VS : VSofC G1 G2 Field VS1 VS2 C) 
  (MVS : MVSoverC G1 G2 Field C VS1 VS2 Ring VS)
    <: EncryptionScheme G1 C Ring Field VS MVS.

  Import MVS.
  Import Field.

  Module AVSL1 := VectorSpaceAddationalLemmas G1 Field VS1.
  Import AVSL1.
  Module AVSL2 := VectorSpaceAddationalLemmas G2 Field VS2.

  (* randomness for keygen *) (*g, h, h1, x1, x2 *)
  Definition KGR := prod (prod (prod (prod G1.G G2.G) G2.G) F) F.         
  (* public key space *)(* pk: g h h1, g1 = g^x1, g2 = g^x2. *)  
  Definition PK := prod (prod (prod (prod G1.G G2.G) G2.G) G1.G) G1.G.  
  (* secret key space *)(* sk: x1 x2 *)   
  Definition SK := prod F F.                  
  Definition M := G1.G.    (* message space    *)
  Definition Mop := G1.Gdot.  (* message space is an ablelian group *)
  Definition Mzero := G1.Gone.      
  Definition Minv := G1.Ginv.
  Definition Mbool_eq := G1.Gbool_eq.
  
  Definition keygen (kgr : KGR) : (PK*SK) := 
    let g := kgr.1.1.1.1 in
    let h := kgr.1.1.1.2 in
    let h1 := kgr.1.1.2 in 
    let x1 := kgr.1.2 in
    let x2 := kgr.2 in

    let pk := (g, h, h1, VS1.op g x1, VS1.op g x2) in
    let sk := (x1, x2) in

    (pk,sk).
  Definition keygenMix kgr := (keygen kgr).1. 

  Definition enc (pk : PK)(m : G1.G)(r : Ring.F) : C.G :=   
  (* g^r1, g^r2, g1^r o g2^r2, h^r o h1^r1, m o g1^r1 *)
    let g := pk.1.1.1.1 in
    let h := pk.1.1.1.2 in
    let h1 := pk.1.1.2 in 
    let g1 := pk.1.2 in
    let g2 := pk.2 in

    let r0 := Vhead r in
    let r1 := Vhead (Vtail r) in
    let r2 := Vhead (Vtail (Vtail r)) in 
    (VS1.op g r1, VS1.op g r2, G1.Gdot (VS1.op g1 r0)
     (VS1.op g2 r2), G2.Gdot (VS2.op h r0) (VS2.op h1 r1),
      G1.Gdot m (VS1.op g1 r1)).

  Definition dec (sk : SK)(c : C.G) : M :=
      G1.Gdot c.2 (G1.Ginv (VS1.op c.1.1.1.1 sk.1)).

  Definition keymatch (pk : PK)(sk : SK) : bool :=
      G1.Gbool_eq (VS1.op pk.1.1.1.1 sk.1) pk.1.2
        && G1.Gbool_eq (VS1.op pk.1.1.1.1 sk.2) pk.2.

  Lemma M_abgrp : AbeGroup M Mop Mzero Mbool_eq Minv.
    Proof.
      apply G1.module_abegrp.
    Qed.

  Lemma correct : forall (kgr : KGR)(m : M)(r : Ring.F),
                let (pk,sk) := keygen kgr in
                dec sk (enc pk m r) = m.
    Proof.
      pose M_abgrp. intros. cbn. 
      unfold dec, enc. simpl. 
      rewrite <- dot_assoc. pose VS1.mod_dist_Fmul. do 2 rewrite <- e.
      replace (kgr.1.2 * (Vhead (Vtail r))) with ((Vhead (Vtail r)) * kgr.1.2).
       rewrite <- inv_right.
      rewrite one_right. trivial. field; auto.
    Qed.

  Lemma homomorphism : forall (pk : PK)(m m' : M)(r r' : Ring.F),
                C.Gdot (enc pk m' r')(enc pk m r) = 
                  enc pk (Mop m m') (Ring.Fadd r r').
    Proof.
      pose M_abgrp. pose G2.module_abegrp. intros. unfold C.Gdot, enc. simpl.
      apply injective_projections. simpl.
      apply injective_projections. simpl.
      apply injective_projections. simpl.
      apply injective_projections. simpl.
      (* Number 1 *)  
      rewrite VS1.mod_dist_Fadd. rewrite comm. trivial.
      (* Number 2 *)
      simpl. rewrite VS1.mod_dist_Fadd. rewrite comm. trivial.
      (* Number 3 *)
      simpl. symmetry. do 2 rewrite VS1.mod_dist_Fadd.
      symmetry. rewrite comm. apply (commHack (A:=G1.G)).
      (* Number 4 *)
      simpl. symmetry. do 2 rewrite VS2.mod_dist_Fadd.
      symmetry. rewrite comm. apply (commHack (A:=G2.G)).
      (* Number 5 *)
      simpl. symmetry. rewrite VS1.mod_dist_Fadd.
      symmetry. rewrite comm. apply (commHack (A:=G1.G)).
    Qed.

  Lemma encOfOnePrec : forall (pk : PK)(a : Ring.F)(b: F),
          (VS.op (enc pk Mzero a) b) = enc pk Mzero (MVS.op3 a b).
    Proof.
      pose G1.module_abegrp.
      intros. unfold enc. unfold VS.op. unfold op3.
      apply injective_projections. simpl.
      apply injective_projections. simpl.
      apply injective_projections. simpl.
      apply injective_projections. simpl.
      (* Number 1 *)
      do 2 rewrite Vhead_nth. do 2 rewrite Vnth_tail.
      rewrite Vnth_map. rewrite mod_dist_FMul2. trivial.
      (* Number 2 *)
      simpl. do 2 rewrite Vhead_nth. do 4 rewrite Vnth_tail.
      rewrite Vnth_map. rewrite mod_dist_FMul2. trivial.
      (* Number 3 *)
      simpl. do 4 rewrite Vhead_nth. do 4 rewrite Vnth_tail.
      do 2 rewrite Vnth_map. do 2 rewrite mod_dist_FMul2.
      rewrite VS1.mod_dist_Gdot. trivial.
      (* Number 4 *)
      simpl. do 4 rewrite Vhead_nth. do 2 rewrite Vnth_tail.
      do 2 rewrite Vnth_map. rewrite VS2.mod_dist_Gdot.
      do 2 rewrite <- AVSL2.mod_dist_FMul2. trivial.
      (* Number 5 *)
      simpl. do 2 rewrite Vhead_nth. do 2 rewrite Vnth_tail.
      rewrite Vnth_map. do 2 rewrite one_left.
      rewrite mod_dist_FMul2. trivial.
    Qed.

End PPATC.

