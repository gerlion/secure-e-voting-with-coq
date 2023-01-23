Require Import Bool.
Require Import Setoid.
Require Import Ring.
Require Import Field.
Require Coq.Program.Tactics.
Require Import Coq.Init.Datatypes.
Require Import ssreflect ssrfun ssrbool.
Require Import groups.
Require Import vectorspace.

Module Type DualGroupSig (Group : GroupSig) <: GroupSig.
  Import Group.

  Definition G := prod G G.
  Definition Gdot (a b : G) : G := (Gdot a.1 b.1, Gdot a.2 b.2).
  Definition Gone := (Gone, Gone).
  Definition Ggen := (Ggen, Ggen).
  Definition Gbool_eq (a b : G) := Gbool_eq a.1 b.1 && Gbool_eq a.2 b.2.
  Definition Gdisjoint (a b : G) := Gdisjoint a.1 b.1 && Gdisjoint a.2 b.2.
  Definition Ginv a := (Ginv a.1, Ginv a.2).

  Lemma module_abegrp : AbeGroup G Gdot Gone Gbool_eq Gdisjoint Ginv.
  Proof.
    (** We need to prove the correctnes of the extended group*)
    pose module_abegrp. constructor. constructor. constructor. intros.
    unfold Gdot. rewrite dot_assoc. rewrite dot_assoc. trivial.
    intros. unfold Gdot. rewrite one_left. rewrite one_left.
    rewrite <- surjective_pairing. trivial.
    intros. unfold Gdot. rewrite one_right. rewrite one_right.
    rewrite <- surjective_pairing. trivial.
    (*bool_eq_corr*)
    intros. refine (conj _ _). destruct a. destruct b. 
    simpl in *. intros. apply andb_true_iff in H. destruct H. 
    assert (a0.1 = g). apply bool_eq_corr. apply H.
    assert (a0.2 = g0). apply bool_eq_corr. apply H0.
    destruct a0. simpl in *. rewrite H1. rewrite H2. trivial.
    intro. apply andb_true_iff. split. apply bool_eq_corr.
    rewrite H. trivial. apply bool_eq_corr. rewrite H. 
    trivial.
    (* bool_eq_sym *)
    intros. unfold Gbool_eq. rewrite bool_eq_sym. rewrite (bool_eq_sym a0.2).
    trivial.
    (*bool_neq_corr*)
    intros.  refine (conj _ _).  intros. 
    apply andb_false_iff in H.
    case_eq (Group.Gbool_eq a0.1 b.1). 
    intros. rewrite H0 in H. destruct H. auto.
    apply bool_neq_corr in H. unfold not. intro.
    rewrite H1 in H. apply H. trivial.
    intros.
    apply bool_neq_corr in H0. unfold not. intros.
    rewrite H1 in H0. apply H0. trivial.
    (*Fist part bool_neq_corr complete *)
    intro. unfold not in H. unfold negb. 
    case_eq (Group.Gbool_eq a0.1 b.1 && Group.Gbool_eq a0.2 b.2). 
    intro. apply andb_true_iff in H0.
    destruct H0. assert (a0.2 = b.2).
    apply bool_eq_corr. apply H1. 
    assert (a0.1 = b.1). apply bool_eq_corr. apply H0.
    destruct a0. destruct b. simpl in *. rewrite H3 in H. 
    rewrite H2 in H. assert False. apply H. trivial. contradiction.
    intro. trivial.
    (* Disjoint sim *)
    intros. unfold Gdisjoint. rewrite disjoint_sym. rewrite (disjoint_sym a0.2).
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
    intros. unfold Gdot. simpl. rewrite comm. remember (b.1 o a0.1) as one.
    rewrite comm. trivial.
  Qed.
End DualGroupSig.

Module DualGroupIns (Group : GroupSig) <: DualGroupSig Group.
  Import Group.

  Definition G := prod G G.
  Definition Gdot (a b : G) : G := (Gdot a.1 b.1, Gdot a.2 b.2).
  Definition Gone := (Gone, Gone).
  Definition Ggen := (Ggen, Ggen).
  Definition Gbool_eq (a b : G) := Gbool_eq a.1 b.1 && Gbool_eq a.2 b.2.
  Definition Gdisjoint (a b : G) := Gdisjoint a.1 b.1 && Gdisjoint a.2 b.2.
  Definition Ginv a := (Ginv a.1, Ginv a.2).

  Lemma module_abegrp : AbeGroup G Gdot Gone Gbool_eq Gdisjoint Ginv.
  Proof.
    (** We need to prove the correctnes of the extended group*)
    pose module_abegrp. constructor. constructor. constructor. intros.
    unfold Gdot. rewrite dot_assoc. rewrite dot_assoc. trivial.
    intros. unfold Gdot. rewrite one_left. rewrite one_left.
    rewrite <- surjective_pairing. trivial.
    intros. unfold Gdot. rewrite one_right. rewrite one_right.
    rewrite <- surjective_pairing. trivial.
    (*bool_eq_corr*)
    intros. refine (conj _ _). destruct a. destruct b. 
    simpl in *. intros. apply andb_true_iff in H. destruct H. 
    assert (a0.1 = g). apply bool_eq_corr. apply H.
    assert (a0.2 = g0). apply bool_eq_corr. apply H0.
    destruct a0. simpl in *. rewrite H1. rewrite H2. trivial.
    intro. apply andb_true_iff. split. apply bool_eq_corr.
    rewrite H. trivial. apply bool_eq_corr. rewrite H. 
    trivial.
    (* bool_eq_sym *)
    intros. intros. unfold Gbool_eq. rewrite bool_eq_sym. rewrite (bool_eq_sym a0.2).
    trivial.
    (*bool_neq_corr*)
    intros.  refine (conj _ _).  intros. 
    apply andb_false_iff in H.
    case_eq (Group.Gbool_eq a0.1 b.1). 
    intros. rewrite H0 in H. destruct H. auto.
    apply bool_neq_corr in H. unfold not. intro.
    rewrite H1 in H. apply H. trivial.
    intros.
    apply bool_neq_corr in H0. unfold not. intros.
    rewrite H1 in H0. apply H0. trivial.
    (*Fist part bool_neq_corr complete *)
    intro. unfold not in H. unfold negb. 
    case_eq (Group.Gbool_eq a0.1 b.1 && Group.Gbool_eq a0.2 b.2). 
    intro. apply andb_true_iff in H0.
    destruct H0. assert (a0.2 = b.2).
    apply bool_eq_corr. apply H1. 
    assert (a0.1 = b.1). apply bool_eq_corr. apply H0.
    destruct a0. destruct b. simpl in *. rewrite H3 in H. 
    rewrite H2 in H. assert False. apply H. trivial. contradiction.
    intro. trivial.
    (* Disjoint sim *)
    intros. unfold Gdisjoint. rewrite disjoint_sym. rewrite (disjoint_sym a0.2).
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
    intros. unfold Gdot. simpl. rewrite comm. remember (b.1 o a0.1) as one.
    rewrite comm. trivial.
  Qed.
End DualGroupIns.

(* A vector space constructed from another by taking the prod of the group,
    then performing all the elements pairwise *)
Module Type DualVectorSpaceSig (Group : GroupSig)(DualGroup : DualGroupSig Group)
     (Field : FieldSig)(VS : VectorSpaceSig Group Field) <: VectorSpaceSig DualGroup Field.
  Import VS.  
  Import DualGroup.
  
  Definition op (a :G)(b :F) := (op a.1 b, op a.2 b).

  Lemma vs_field : field_theory Fzero Fone Fadd Fmul Fsub Finv Fdiv FmulInv (@eq F).
  Proof.
    apply vs_field.
  Qed. 

  Lemma module_ring : ring_theory Fzero Fone Fadd Fmul Fsub Finv (@eq F).
  Proof.
    apply module_ring.
  Qed.

  Lemma mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
  Proof.
      intros. unfold Gdot. simpl. do 2 rewrite <- mod_dist_Gdot. trivial.
  Qed.

  Lemma mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
  Proof.
      intros. unfold Gdot. simpl. do 2 rewrite <- mod_dist_Fadd. trivial.
  Qed.

  Lemma mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
  Proof.
      intros. unfold op. simpl. do 2 rewrite <- mod_dist_Fmul. trivial.
  Qed.

  Lemma mod_id : forall (x : G), op x Fone = x.
  Proof.
      intros. unfold op. simpl. apply injective_projections. 
      rewrite <- mod_id. trivial. rewrite <- mod_id. trivial.
  Qed.
    
  Lemma mod_ann : forall (x : G), op x Fzero = Gone.
  Proof.
     intros. unfold op. simpl. apply injective_projections. 
      rewrite mod_ann. trivial. do 2 rewrite mod_ann. trivial.
  Qed.

  Infix "^" := op.

  Add Field vs_field : vs_field.
  Add Ring module_ring : module_ring.
End DualVectorSpaceSig.

Module DualVectorSpaceIns (Group : GroupSig)(DualGroup : DualGroupSig Group)
     (Field : FieldSig)(VS : VectorSpaceSig Group Field) <: VectorSpaceSig DualGroup Field.
  Import VS.  
  Import DualGroup.
  
  Definition op (a :G)(b :F) := (op a.1 b, op a.2 b).

  Lemma vs_field : field_theory Fzero Fone Fadd Fmul Fsub Finv Fdiv FmulInv (@eq F).
  Proof.
    apply vs_field.
  Qed. 

  Lemma module_ring : ring_theory Fzero Fone Fadd Fmul Fsub Finv (@eq F).
  Proof.
    apply module_ring.
  Qed.

  Lemma mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
  Proof.
      intros. unfold Gdot. simpl. do 2 rewrite <- mod_dist_Gdot. trivial.
  Qed.

  Lemma mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
  Proof.
      intros. unfold Gdot. simpl. do 2 rewrite <- mod_dist_Fadd. trivial.
  Qed.

  Lemma mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
  Proof.
      intros. unfold op. simpl. do 2 rewrite <- mod_dist_Fmul. trivial.
  Qed.

  Lemma mod_id : forall (x : G), op x Fone = x.
  Proof.
      intros. unfold op. simpl. apply injective_projections. 
      rewrite <- mod_id. trivial. rewrite <- mod_id. trivial.
  Qed.
    
  Lemma mod_ann : forall (x : G), op x Fzero = Gone.
  Proof.
     intros. unfold op. simpl. apply injective_projections. 
      rewrite mod_ann. trivial. do 2 rewrite mod_ann. trivial.
  Qed.

  Infix "^" := op.

  Add Field vs_field : vs_field.
  Add Ring module_ring : module_ring.
End DualVectorSpaceIns.
