Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Datatypes.
From Groups Require Import groups module vectorspace dualvectorspaces
    nthvectorspaces modulevectorspace groupfromring.

Module Type ProdGroupSig (M1M M2M : GroupSig) <: GroupSig.
  Definition G := prod M1M.G M2M.G.
  Definition Gdot (a b : G) := (M1M.Gdot a.1 b.1, M2M.Gdot a.2 b.2).
  Definition Gone := (M1M.Gone, M2M.Gone).
  Definition Ggen := (M1M.Ggen, M2M.Ggen).
  Definition Gbool_eq (a b : G) := M1M.Gbool_eq a.1 b.1 &&
                                    M2M.Gbool_eq a.2 b.2. 
  Definition Gdisjoint (a b : G) := M1M.Gdisjoint a.1 b.1 &&
                                    M2M.Gdisjoint a.2 b.2. 
  Definition Ginv (a : G) := (M1M.Ginv a.1, M2M.Ginv a.2).

  Lemma module_abegrp : AbeGroup G Gdot Gone Gbool_eq Gdisjoint Ginv.
  Proof.
    (** We need to prove the correctnes of the extended group*)
    pose M1M.module_abegrp. pose M2M.module_abegrp. constructor. 
    constructor. constructor. intros.
    unfold Gdot. rewrite dot_assoc. rewrite dot_assoc. trivial.
    intros. unfold Gdot. rewrite one_left. rewrite one_left.
    rewrite <- surjective_pairing. trivial.
    intros. unfold Gdot. rewrite one_right. rewrite one_right.
    rewrite <- surjective_pairing. trivial.
    (*bool_eq_corr*)
    intros. refine (conj _ _). destruct a. destruct b. 
    simpl in *. intros. apply andb_true_iff in H. destruct H. 
    assert (a1.1 = g). apply bool_eq_corr. apply H.
    assert (a1.2 = g0). apply bool_eq_corr. apply H0.
    destruct a1. simpl in *. rewrite H1. rewrite H2. trivial.
    intro. apply andb_true_iff. split. apply bool_eq_corr.
    rewrite H. trivial. apply bool_eq_corr. rewrite H. 
    trivial.
    (*bool_eq_sym*)
    intros. unfold Gbool_eq. rewrite bool_eq_sym. rewrite (bool_eq_sym a1.2).
    trivial.
    (*bool_neq_corr*)
    intros.  refine (conj _ _).  intros. 
    apply andb_false_iff in H.
    case_eq (M1M.Gbool_eq a1.1 b.1). 
    intros. rewrite H0 in H. destruct H. auto.
    apply bool_neq_corr in H. unfold not. intro.
    rewrite H1 in H. apply H. trivial.
    intros.
    apply bool_neq_corr in H0. unfold not. intros.
    rewrite H1 in H0. apply H0. trivial.
    (*Fist part bool_neq_corr complete *)
    intro. unfold not in H. unfold negb. 
    case_eq (M1M.Gbool_eq a1.1 b.1 && M2M.Gbool_eq a1.2 b.2). 
    intro. apply andb_true_iff in H0.
    destruct H0. assert (a1.2 = b.2).
    apply bool_eq_corr. apply H1. 
    assert (a1.1 = b.1). apply bool_eq_corr. apply H0.
    destruct a0. destruct b. simpl in *. destruct a1.
    simpl in *. rewrite H3 in H. rewrite H2 in H. assert False. 
    apply H. trivial. contradiction.
    intro. trivial.

    (* Disjoint sim *)
    intros. unfold Gdisjoint. rewrite disjoint_sym. rewrite (disjoint_sym a1.2).
    trivial.
    (* Disjoint corr *)
    intros. unfold Gdisjoint in H. apply andb_true_iff in H.
    destruct H. apply disjoint_corr in H. unfold not in *. intros. 
    apply H. rewrite H1. trivial.

    (* inv_left *)
    intros. unfold Gdot. simpl. rewrite <- inv_left. rewrite <- inv_left.
    trivial. intros. unfold Gdot. simpl.  rewrite <- inv_right.
    rewrite <- inv_right. trivial.

    (* comm *)
    intros. unfold Gdot. simpl. rewrite comm. remember (M1M.Gdot b.1 a1.1) as one.
    rewrite comm. trivial.
  Qed.

  Infix "o" := Gdot (at level 50) .
  Notation "- x" := (Ginv x).
End ProdGroupSig.


Module ProdGroupSigIns (M1M M2M : GroupSig) <: GroupSig.
  Definition G := prod M1M.G M2M.G.
  Definition Gdot (a b : G) := (M1M.Gdot a.1 b.1, M2M.Gdot a.2 b.2).
  Definition Gone := (M1M.Gone, M2M.Gone).
  Definition Ggen := (M1M.Ggen, M2M.Ggen).
  Definition Gbool_eq (a b : G) := M1M.Gbool_eq a.1 b.1 &&
                                    M2M.Gbool_eq a.2 b.2. 
  Definition Gdisjoint (a b : G) := M1M.Gdisjoint a.1 b.1 &&
                                    M2M.Gdisjoint a.2 b.2. 
  Definition Ginv (a : G) := (M1M.Ginv a.1, M2M.Ginv a.2).

  Lemma module_abegrp : AbeGroup G Gdot Gone Gbool_eq Gdisjoint Ginv.
  Proof.
    (** We need to prove the correctnes of the extended group*)
    pose M1M.module_abegrp. pose M2M.module_abegrp. constructor. 
    constructor. constructor. intros.
    unfold Gdot. rewrite dot_assoc. rewrite dot_assoc. trivial.
    intros. unfold Gdot. rewrite one_left. rewrite one_left.
    rewrite <- surjective_pairing. trivial.
    intros. unfold Gdot. rewrite one_right. rewrite one_right.
    rewrite <- surjective_pairing. trivial.
    (*bool_eq_corr*)
    intros. refine (conj _ _). destruct a. destruct b. 
    simpl in *. intros. apply andb_true_iff in H. destruct H. 
    assert (a1.1 = g). apply bool_eq_corr. apply H.
    assert (a1.2 = g0). apply bool_eq_corr. apply H0.
    destruct a1. simpl in *. rewrite H1. rewrite H2. trivial.
    intro. apply andb_true_iff. split. apply bool_eq_corr.
    rewrite H. trivial. apply bool_eq_corr. rewrite H. 
    trivial.
    (*bool_eq_sym*)
    intros. unfold Gbool_eq. rewrite bool_eq_sym. rewrite (bool_eq_sym a1.2).
    trivial.
    (*bool_neq_corr*)
    intros.  refine (conj _ _).  intros. 
    apply andb_false_iff in H.
    case_eq (M1M.Gbool_eq a1.1 b.1). 
    intros. rewrite H0 in H. destruct H. auto.
    apply bool_neq_corr in H. unfold not. intro.
    rewrite H1 in H. apply H. trivial.
    intros.
    apply bool_neq_corr in H0. unfold not. intros.
    rewrite H1 in H0. apply H0. trivial.
    (*Fist part bool_neq_corr complete *)
    intro. unfold not in H. unfold negb. 
    case_eq (M1M.Gbool_eq a1.1 b.1 && M2M.Gbool_eq a1.2 b.2). 
    intro. apply andb_true_iff in H0.
    destruct H0. assert (a1.2 = b.2).
    apply bool_eq_corr. apply H1. 
    assert (a1.1 = b.1). apply bool_eq_corr. apply H0.
    destruct a0. destruct b. simpl in *. destruct a1.
    simpl in *. rewrite H3 in H. rewrite H2 in H. assert False. 
    apply H. trivial. contradiction.
    intro. trivial.

    (* Disjoint sim *)
    intros. unfold Gdisjoint. rewrite disjoint_sym. rewrite (disjoint_sym a1.2).
    trivial.
    (* Disjoint corr *)
    intros. unfold Gdisjoint in H. apply andb_true_iff in H.
    destruct H. apply disjoint_corr in H. unfold not in *. intros. 
    apply H. rewrite H1. trivial.

    (* inv_left *)
    intros. unfold Gdot. simpl. rewrite <- inv_left. rewrite <- inv_left.
    trivial. intros. unfold Gdot. simpl.  rewrite <- inv_right.
    rewrite <- inv_right. trivial.

    (* comm *)
    intros. unfold Gdot. simpl. rewrite comm. remember (M1M.Gdot b.1 a1.1) as one.
    rewrite comm. trivial.
  Qed.

  Infix "o" := Gdot (at level 50) .
  Notation "- x" := (Ginv x).
End ProdGroupSigIns.

Module Type ProdRingSig (M1Ring M2Ring : RingSig) <: RingSig.

  Definition F := prod M1Ring.F M2Ring.F.
  Definition Fadd (a b : F) := (M1Ring.Fadd a.1 b.1, M2Ring.Fadd a.2 b.2). 
  Definition Fzero := (M1Ring.Fzero, M2Ring.Fzero).
  Definition Fbool_eq (a b : F) := M1Ring.Fbool_eq a.1 b.1 && M2Ring.Fbool_eq a.2 b.2.
  Definition Fsub (a b : F) := (M1Ring.Fsub a.1 b.1, M2Ring.Fsub a.2 b.2).
  Definition Finv (a : F) := (M1Ring.Finv a.1, M2Ring.Finv a.2).
  Definition Fmul (a b : F) := (M1Ring.Fmul a.1 b.1, M2Ring.Fmul a.2 b.2).
  Definition Fone := (M1Ring.Fone, M2Ring.Fone).

  Lemma module_ring : ring_theory Fzero Fone Fadd Fmul Fsub Finv (@eq F).
  Proof.
    destruct M1Ring.module_ring. destruct M2Ring.module_ring.
    constructor. intros. unfold Fadd. rewrite Radd_0_l.
    rewrite Radd_0_l0. trivial. rewrite (surjective_pairing x).
    auto. intros. unfold Fadd. rewrite Radd_comm. rewrite Radd_comm0.
    trivial. intros. unfold Fadd. rewrite Radd_assoc. rewrite Radd_assoc0.
    trivial. intros. unfold Fmul. rewrite Rmul_1_l. rewrite Rmul_1_l0.
    rewrite (surjective_pairing x). auto. intros. unfold Fmul.
    rewrite Rmul_comm. rewrite Rmul_comm0. trivial. intros.
    unfold Fmul. rewrite Rmul_assoc. rewrite Rmul_assoc0. trivial. 
    intros. unfold Fmul. unfold Fadd. rewrite Rdistr_l.
    rewrite Rdistr_l0. trivial. intros. unfold Fsub. rewrite Rsub_def. 
    rewrite Rsub_def0. trivial. intros. unfold Fadd. rewrite Ropp_def. 
    rewrite Ropp_def0. trivial.
  Qed. 

  Lemma F_bool_eq_corr: forall a b : F, Fbool_eq a b = true <-> a=b.
  Proof.
    intros. unfold Fbool_eq. destruct a. destruct b. simpl.
    refine (conj _ _). intros. apply andb_true_iff in H. destruct H.
    apply M1Ring.F_bool_eq_corr in H. apply M2Ring.F_bool_eq_corr in H0.
    rewrite H. rewrite H0. trivial.
    intros. apply andb_true_iff. assert (f = (f,f0).1). auto. 
    assert (f0 = (f,f0).2). auto. split. apply M1Ring.F_bool_eq_corr. 
    rewrite H0. rewrite H. auto. apply M2Ring.F_bool_eq_corr.
    rewrite H1. rewrite H. auto. 
  Qed.

  Lemma F_bool_eq_sym : forall a b : F, Fbool_eq a b = Fbool_eq b a.
  Proof.
    intros. unfold Fbool_eq. rewrite M1Ring.F_bool_eq_sym.
    rewrite M2Ring.F_bool_eq_sym. trivial.
  Qed.

  Lemma  F_bool_neq_corr: forall a b : F, Fbool_eq a b = false <-> a <> b.
  Proof.
    intros.  unfold Fbool_eq. destruct a. destruct b. simpl.
    assert (f = (f,f0).1). auto. assert (f0 = (f,f0).2). auto.
    refine (conj _ _). intros. apply andb_false_iff in H1. destruct H1.
    apply M1Ring.F_bool_neq_corr in H1. unfold not in *.
    intros. apply H1. rewrite H. rewrite H2. auto.
    apply M2Ring.F_bool_neq_corr in H1. unfold not in *. 
    intros. apply H1. rewrite H0. rewrite H2. auto.
    (* Second half *)
    intros. apply not_true_iff_false. unfold not in *.
    intros. apply H1. pose (F_bool_eq_corr (f,f0) (f1,f2)).
    unfold Fbool_eq in i. simpl in i. apply i in H2. apply H2.
  Qed.

  Infix "+" := Fadd.
  Infix "*" := Fmul.
  Notation "0" := Fzero.
  Notation "1" := Fone.
  Notation "- x" :=  (Finv x).
  Notation "x - y" := (x + (- y)).

  Add Ring module_ring : module_ring.
End ProdRingSig.

Module Type ProdVectorSpaceSig (M1C M2C : GroupSig) 
  (Ciphertext : ProdGroupSig M1C M2C) (Field : FieldSig) 
  (VS1 : VectorSpaceSig M1C Field)(VS2 : VectorSpaceSig M2C Field) 
  <: VectorSpaceSig Ciphertext Field.

  Import Ciphertext.
  Export Ciphertext.
  Import Field.
  Export Field.

  Definition op a b:= (VS1.op a.1 b, VS2.op a.2 b).

  Lemma mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
  Proof.
    intros. unfold op. rewrite VS1.mod_dist_Gdot. rewrite VS2.mod_dist_Gdot. trivial.
  Qed.

  Lemma mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
  Proof.
    intros. unfold op. rewrite VS1.mod_dist_Fadd. rewrite VS2.mod_dist_Fadd. trivial.
  Qed.

  Lemma mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
  Proof.
    intros. unfold op. rewrite VS1.mod_dist_Fmul. rewrite VS2.mod_dist_Fmul. trivial.
  Qed.

  Lemma mod_id : forall (x : G), op x Fone = x.
  Proof.
    intros. unfold op. rewrite VS1.mod_id. rewrite VS2.mod_id. destruct x. trivial.
  Qed.

  Lemma mod_ann : forall (x : G), op x Fzero = Gone.
  Proof.
    intros. unfold op. rewrite VS1.mod_ann. rewrite VS2.mod_ann. trivial.
  Qed.

  Infix "o" := Gdot (at level 50) .
  Notation "- x" := (Ginv x).

  Infix "^" := op.

End ProdVectorSpaceSig.

Module Type ProdVectorSpaceModuleSameGroup (M1C M2C : GroupSig) 
  (M1Ring M2Ring : RingSig)(Field : FieldSig)(VS1 : VectorSpaceSig M1C Field)
  (VS2 : VectorSpaceSig M2C Field)
  (MVS1 : VectorSpaceModuleSameGroup M1C M1Ring Field VS1)
  (MVS2 : VectorSpaceModuleSameGroup M2C M2Ring Field VS2)
  (Ciphertext : ProdGroupSig M1C M2C)(Ring : ProdRingSig M1Ring M2Ring)
  (VS : ProdVectorSpaceSig M1C M2C Ciphertext Field VS1 VS2)
  <: VectorSpaceModuleSameGroup Ciphertext Ring Field VS.

  Export Ciphertext.
  Export VS.

  Definition op3 a b := (MVS1.op3 a.1 b, MVS2.op3 a.2 b).

  Lemma RopInv : forall a, op3 a (Field.Finv Fone) = Ring.Finv a.
  Proof.
    intros. unfold op3. rewrite MVS1.RopInv. rewrite MVS2.RopInv. trivial.
  Qed.

  Lemma RopInvDis : forall a b, op3 (Ring.Finv a) b = Ring.Finv (op3 a b).
  Proof.
    intros. unfold op3. rewrite MVS1.RopInvDis. rewrite MVS2.RopInvDis. trivial.
  Qed.

  Lemma RopFZero : forall x, op3 x Fzero = Ring.Fzero.
  Proof.
    intros. unfold op3. rewrite MVS1.RopFZero. rewrite MVS2.RopFZero. trivial.
  Qed.
  
  Lemma RopFOne : forall x, op3 x Fone = x.
    Proof. 
      intros. unfold op3. rewrite MVS1.RopFOne. rewrite MVS2.RopFOne. 
      rewrite <- surjective_pairing. trivial.
    Qed.

  Lemma RopRZero : forall x, op3 Ring.Fzero x = Ring.Fzero.
  Proof.
    intros. unfold op3. rewrite MVS1.RopRZero. rewrite MVS2.RopRZero. trivial.
  Qed.

  Lemma RopDistRadd : forall x y z, op3 (Ring.Fadd x y) z = 
      Ring.Fadd (op3 x z) (op3 y z).
  Proof.
    intros. unfold op3. rewrite MVS1.RopDistRadd. rewrite MVS2.RopDistRadd. trivial.
  Qed.

  Lemma RopDistFadd : forall (r s : F) (x : Ring.F), 
      op3 x (Fadd r s) = Ring.Fadd (op3 x r) (op3 x s).
  Proof.
    intros. unfold op3. rewrite MVS1.RopDistFadd. rewrite MVS2.RopDistFadd. trivial.
  Qed.

  Lemma RopDistFmul : forall x y z, op3 (op3 x y) z = 
      op3 x (Fmul y z).
  Proof.
    intros. unfold op3. rewrite MVS1.RopDistFmul. rewrite MVS2.RopDistFmul. trivial.
  Qed.

  Lemma RaddInv : forall (a : Ring.F)(b : F),
     (Ring.Fadd (op3 a b) (op3 a (Finv b))) = Ring.Fzero.
  Proof.
    intros. unfold op3, Ring.Fadd. rewrite MVS1.RaddInv. rewrite MVS2.RaddInv. trivial.
  Qed.
End ProdVectorSpaceModuleSameGroup.
