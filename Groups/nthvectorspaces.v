Require Import Bool.
Require Import Setoid.
Require Import Ring.
Require Import Field.
Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import groups.
Require Import vectorspace.
Require Import matrices.
Require Import matricesF.
Require Import module.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import modulevectorspace.
Require Import VectorUtil.

(* Dirty hack to paramtise the next module *)
Module Type Nat.
  Parameter N : nat.
End Nat.

Module Type GroupNthSig (Group : GroupSig)(Hack : Nat) <: GroupSig.
  Import Group.
  Import Hack.

  Definition G := vector G (S N).
  Definition Gdot (a b : G) : G := Vmap2 Gdot a b.
  Definition Gone := Vconst Gone (S N).
  Definition Ggen := Vconst Ggen (S N).
  Definition Gbool_eq (a b : G) := bVforall2 Gbool_eq a b.
  Definition Gdisjoint (a b : G) := bVforall2 Gdisjoint a b.
  Definition Ginv (a : G) := Vmap Ginv a.

  Lemma module_abegrp : AbeGroup G Gdot Gone Gbool_eq Gdisjoint Ginv.
  Proof.
    (** We need to prove the correctnes of the extended group*)
    pose module_abegrp. destruct a. destruct abegrp_grp. destruct grp_mon.
    assert (forall a b : G, Gbool_eq a b = true <-> a = b).
    (*bool_eq_corr*)   
    intros. intros. unfold iff. refine (conj _ _).  intros. 
    assert (Vforall2 eq a b). rewrite <- (bVforall2_ok (@eq Group.G) Group.Gbool_eq).
    apply H. intros. apply bool_eq_corr. apply Veq_nth. intros. 
    apply (Vforall2_elim_nth ip) in H0. apply H0.
    (* part 2 *)
    intros. rewrite H. unfold Gbool_eq. rewrite (bVforall2_ok (@eq Group.G)).
    intros. apply bool_eq_corr. apply Vforall2_intro_nth. intros. trivial.
    (* Starting *)
    constructor. constructor. constructor. intros. unfold Gdot. symmetry. 
    apply Veq_nth. intros. do 4 rewrite Vnth_map2. rewrite dot_assoc. trivial.
    intro. unfold Gdot. apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vnth_const. apply one_left. 
    intro. unfold Gdot. apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vnth_const. apply one_right.
    apply H.
    (* bool_eq_sym*)
    intros. unfold Gbool_eq. unfold G in *. clear H. induction N.
    rewrite (VSn_eq a). rewrite (VSn_eq b).  
    rewrite (Vector_0_is_nil (Vtail a)). rewrite (Vector_0_is_nil (Vtail b)). cbn.
    rewrite bool_eq_sym. trivial. rewrite (VSn_eq a). rewrite (VSn_eq b). cbn.
    unfold bVforall2 in IHn. rewrite (IHn (Vtail a) (Vtail b)).
    rewrite bool_eq_sym. trivial.
    (*bool_neq_corr*)
    intros. refine (conj _ _). intros. apply not_true_iff_false in H0.
    unfold not in *. intros. apply H0. apply H. apply H1.
    intros. apply not_true_iff_false. unfold not in *.
    intros. apply H0. apply H. apply H1.

    (* Sym *)
    intros. unfold G, Gdisjoint in *. clear H. induction N. 
    rewrite (VSn_eq a). rewrite (VSn_eq b).
    rewrite (Vector_0_is_nil (Vtail a)). rewrite (Vector_0_is_nil (Vtail b)). 
    cbn. rewrite disjoint_sym. trivial.
    rewrite (VSn_eq a). rewrite (VSn_eq b). cbn.    
    unfold bVforall2 in IHn. rewrite (IHn (Vtail a) (Vtail b)).
    rewrite disjoint_sym. trivial.
    (* Corr *)
    intros. unfold Gdisjoint, G in *. 
    apply bVforall2_elim_head in H0. apply disjoint_corr in H0.
    unfold not in *. intros. apply H0. rewrite H1. trivial.

    (* inv_left *)
    intros. apply Veq_nth. intros. unfold Gdot. rewrite Vnth_const.
    rewrite Vnth_map2. rewrite Vnth_map. apply inv_left.
    (* inv_righ *)
    intros. apply Veq_nth. intros. unfold Gdot. rewrite Vnth_const.
    rewrite Vnth_map2. rewrite Vnth_map. apply inv_right.

    (* comm *)
    intros. apply Veq_nth. intros. do 2 rewrite Vnth_map2. apply comm.
  Qed.
End GroupNthSig.

Module GroupNthIns (Group : GroupSig)(Hack : Nat) <: GroupSig.
  Import Group.
  Import Hack.

  Definition G := vector G (S N).
  Definition Gdot (a b : G) : G := Vmap2 Gdot a b.
  Definition Gone := Vconst Gone (S N).
  Definition Ggen := Vconst Ggen (S N).
  Definition Gbool_eq (a b : G) := bVforall2 Gbool_eq a b.
  Definition Gdisjoint (a b : G) := bVforall2 Gdisjoint a b.
  Definition Ginv (a : G) := Vmap Ginv a.

  Lemma module_abegrp : AbeGroup G Gdot Gone Gbool_eq Gdisjoint Ginv.
  Proof.
    (** We need to prove the correctnes of the extended group*)
    pose module_abegrp. destruct a. destruct abegrp_grp. destruct grp_mon.
    assert (forall a b : G, Gbool_eq a b = true <-> a = b).
    (*bool_eq_corr*)   
    intros. intros. unfold iff. refine (conj _ _).  intros. 
    assert (Vforall2 eq a b). rewrite <- (bVforall2_ok (@eq Group.G) Group.Gbool_eq).
    apply H. intros. apply bool_eq_corr. apply Veq_nth. intros. 
    apply (Vforall2_elim_nth ip) in H0. apply H0.
    (* part 2 *)
    intros. rewrite H. unfold Gbool_eq. rewrite (bVforall2_ok (@eq Group.G)).
    intros. apply bool_eq_corr. apply Vforall2_intro_nth. intros. trivial. 
    (* Starting *)
    constructor. constructor. constructor. intros. unfold Gdot. symmetry. 
    apply Veq_nth. intros. do 4 rewrite Vnth_map2. rewrite dot_assoc. trivial.
    intro. unfold Gdot. apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vnth_const. apply one_left. 
    intro. unfold Gdot. apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vnth_const. apply one_right.
    apply H.
    (* bool_eq_sym*)
    intros. unfold Gbool_eq. unfold G in *. clear H. induction N.
    rewrite (VSn_eq a). rewrite (VSn_eq b).  
    rewrite (Vector_0_is_nil (Vtail a)). rewrite (Vector_0_is_nil (Vtail b)). cbn.
    rewrite bool_eq_sym. trivial. rewrite (VSn_eq a). rewrite (VSn_eq b). cbn.
    unfold bVforall2 in IHn. rewrite (IHn (Vtail a) (Vtail b)).
    rewrite bool_eq_sym. trivial.
    (*bool_neq_corr*)
    intros. refine (conj _ _). intros. apply not_true_iff_false in H0.
    unfold not in *. intros. apply H0. apply H. apply H1.
    intros. apply not_true_iff_false. unfold not in *.
    intros. apply H0. apply H. apply H1.

    (* Sym *)
    intros. unfold G, Gdisjoint in *. clear H. induction N. 
    rewrite (VSn_eq a). rewrite (VSn_eq b).
    rewrite (Vector_0_is_nil (Vtail a)). rewrite (Vector_0_is_nil (Vtail b)). 
    cbn. rewrite disjoint_sym. trivial.
    rewrite (VSn_eq a). rewrite (VSn_eq b). cbn.    
    unfold bVforall2 in IHn. rewrite (IHn (Vtail a) (Vtail b)).
    rewrite disjoint_sym. trivial.
    (* Corr *)
    intros. unfold Gdisjoint, G in *. 
    apply bVforall2_elim_head in H0. apply disjoint_corr in H0.
    unfold not in *. intros. apply H0. rewrite H1. trivial.

    (* inv_left *)
    intros. apply Veq_nth. intros. unfold Gdot. rewrite Vnth_const.
    rewrite Vnth_map2. rewrite Vnth_map. apply inv_left.
    (* inv_righ *)
    intros. apply Veq_nth. intros. unfold Gdot. rewrite Vnth_const.
    rewrite Vnth_map2. rewrite Vnth_map. apply inv_right.

    (* comm *)
    intros. apply Veq_nth. intros. do 2 rewrite Vnth_map2. apply comm.
  Qed.
End GroupNthIns.

(* Nth rings *)
Module Type NthRingSig (Hack : Nat)(Ring : RingSig) <: RingSig.
  Import Hack.
  Import Ring.

  Definition F := vector F (S N).
  Definition Fadd (a b : F) := Vmap2 Fadd a b.
  Definition Fzero := Vconst Fzero (S N).
  Definition Fbool_eq (a b : F) := bVforall2 Fbool_eq a b.
  Definition Fsub (a b : F) := Vmap2 Fsub a b.
  Definition Finv (a : F) := Vmap Finv a.
  Definition Fmul (a b : F) := Vmap2 Fmul a b.
  Definition Fone := Vconst Fone (S N). 

  Lemma module_ring : ring_theory Fzero Fone Fadd Fmul Fsub Finv (@eq F).
  Proof.
    constructor. intros. apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vnth_const. ring; auto.
    intros. apply Veq_nth. intros. do 2 rewrite Vnth_map2. ring; auto.
    intros. apply Veq_nth. intros. do 4 rewrite Vnth_map2. ring; auto.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_const.
    ring; auto. intros. apply Veq_nth. intros. do 2 rewrite Vnth_map2. 
    ring; auto. intros. apply Veq_nth. intros. do 4 rewrite Vnth_map2.
    ring; auto. intros. apply Veq_nth. intros. do 5 rewrite Vnth_map2.
    ring; auto. intros. apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    rewrite Vnth_map. ring; auto. intros. apply Veq_nth. intros. 
    rewrite Vnth_map2. rewrite Vnth_map. rewrite Vnth_const. ring; auto.
  Qed.

  Lemma F_bool_eq_corr: forall a b : F, Fbool_eq a b = true <-> a=b.
  Proof.
    intros. unfold iff. refine (conj _ _).  intros. 
    assert (Vforall2 eq a b). rewrite <- (bVforall2_ok (@eq Ring.F) Ring.Fbool_eq).
    apply H. intros. apply Ring.F_bool_eq_corr. apply Veq_nth. intros. 
    apply (Vforall2_elim_nth ip) in H0. apply H0.
    (* part 2 *)
    intros. rewrite H. unfold Fbool_eq. rewrite (bVforall2_ok (@eq Ring.F)).
    intros. apply Ring.F_bool_eq_corr. apply Vforall2_intro_nth. intros. trivial. 
  Qed.
  Lemma F_bool_eq_sym : forall a b :F, Fbool_eq a b = Fbool_eq b a.
  Proof.
    intros. unfold Fbool_eq. unfold F in *. induction N. 
    rewrite (VSn_eq a). rewrite (VSn_eq b). 
    rewrite (Vector_0_is_nil (Vtail a)). rewrite (Vector_0_is_nil (Vtail b)). cbn.
    rewrite F_bool_eq_sym. trivial. rewrite (VSn_eq a). rewrite (VSn_eq b). cbn.
    unfold bVforall2 in IHn. rewrite (IHn (Vtail a) (Vtail b)).
    rewrite F_bool_eq_sym. trivial.
  Qed.
 
  Lemma  F_bool_neq_corr: forall a b : F, Fbool_eq a b = false <-> a <> b.
  Proof.
    intros. refine (conj _ _). intros. apply not_true_iff_false in H.
    unfold not in *. intros. apply H. apply F_bool_eq_corr. apply H0.
    intros. apply not_true_iff_false. unfold not in *.
    intros. apply H. apply F_bool_eq_corr. apply H0.
  Qed.

  Add Ring module_ring : module_ring.
End NthRingSig.

(* Nth rings *)
Module NthRingIns (Hack : Nat)(Ring : RingSig) <: RingSig.
  Import Hack.
  Import Ring.

  Definition F := vector F (S N).
  Definition Fadd (a b : F) := Vmap2 Fadd a b.
  Definition Fzero := Vconst Fzero (S N).
  Definition Fbool_eq (a b : F) := bVforall2 Fbool_eq a b.
  Definition Fsub (a b : F) := Vmap2 Fsub a b.
  Definition Finv (a : F) := Vmap Finv a.
  Definition Fmul (a b : F) := Vmap2 Fmul a b.
  Definition Fone := Vconst Fone (S N). 

  Lemma module_ring : ring_theory Fzero Fone Fadd Fmul Fsub Finv (@eq F).
  Proof.
    constructor. intros. apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vnth_const. ring; auto.
    intros. apply Veq_nth. intros. do 2 rewrite Vnth_map2. ring; auto.
    intros. apply Veq_nth. intros. do 4 rewrite Vnth_map2. ring; auto.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_const.
    ring; auto. intros. apply Veq_nth. intros. do 2 rewrite Vnth_map2. 
    ring; auto. intros. apply Veq_nth. intros. do 4 rewrite Vnth_map2.
    ring; auto. intros. apply Veq_nth. intros. do 5 rewrite Vnth_map2.
    ring; auto. intros. apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    rewrite Vnth_map. ring; auto. intros. apply Veq_nth. intros. 
    rewrite Vnth_map2. rewrite Vnth_map. rewrite Vnth_const. ring; auto.
  Qed.

  Lemma F_bool_eq_corr: forall a b : F, Fbool_eq a b = true <-> a=b.
  Proof.
    intros. unfold iff. refine (conj _ _).  intros. 
    assert (Vforall2 eq a b). rewrite <- (bVforall2_ok (@eq Ring.F) Ring.Fbool_eq).
    apply H. intros. apply Ring.F_bool_eq_corr. apply Veq_nth. intros. 
    apply (Vforall2_elim_nth ip) in H0. apply H0.
    (* part 2 *)
    intros. rewrite H. unfold Fbool_eq. rewrite (bVforall2_ok (@eq Ring.F)).
    intros. apply Ring.F_bool_eq_corr. apply Vforall2_intro_nth. intros. trivial.
  Qed.
  Lemma F_bool_eq_sym : forall a b :F, Fbool_eq a b = Fbool_eq b a.
  Proof.
    intros. unfold Fbool_eq. unfold F in *. induction N. 
    rewrite (VSn_eq a). rewrite (VSn_eq b). 
    rewrite (Vector_0_is_nil (Vtail a)). rewrite (Vector_0_is_nil (Vtail b)). cbn.
    rewrite F_bool_eq_sym. trivial. rewrite (VSn_eq a). rewrite (VSn_eq b). cbn.
    unfold bVforall2 in IHn. rewrite (IHn (Vtail a) (Vtail b)).
    rewrite F_bool_eq_sym. trivial.
  Qed.
  Lemma  F_bool_neq_corr: forall a b : F, Fbool_eq a b = false <-> a <> b.
  Proof.
    intros. refine (conj _ _). intros. apply not_true_iff_false in H.
    unfold not in *. intros. apply H. apply F_bool_eq_corr. apply H0.
    intros. apply not_true_iff_false. unfold not in *.
    intros. apply H. apply F_bool_eq_corr. apply H0.
  Qed.

  Add Ring module_ring : module_ring.
End NthRingIns.

(* A vector space constructed from another by taking the prod of the group,
    then performing all the elements pairwise *)
Module Type NthVectorSpaceSig (Hack : Nat)(Group : GroupSig)(Field : FieldSig)
    (NthGroup : GroupNthSig Group Hack)(VS : VectorSpaceSig Group Field) <: VectorSpaceSig NthGroup Field.
  Import VS.  

  Import NthGroup.
  Export NthGroup.
  Import Field.
  Export Field.

  Module MatF := MatricesFIns Field.
  Module Mat := MatricesG Group Field VS MatF.
  Import Mat.
  Import MatF.
  
  Definition op (a :G)(b : F) := VG_Sexp a b.

  Lemma mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
  Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
      rewrite mod_dist_Gdot. do 2 rewrite Vnth_map. trivial.
  Qed.

  Lemma mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
  Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_map2.
      rewrite mod_dist_Fadd. do 2 rewrite Vnth_map. trivial. 
  Qed.

  Lemma mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
  Proof.
      intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. 
      rewrite mod_dist_Fmul. trivial. 
  Qed.

  Lemma mod_id : forall (x : G), op x Fone = x.
  Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. 
      rewrite <- mod_id. trivial. 
  Qed.
    
  Lemma mod_ann : forall (x : G), op x Fzero = Gone.
  Proof.
     intros. apply Veq_nth. intros. rewrite Vnth_map.  
      rewrite mod_ann. rewrite Vnth_const. trivial. 
  Qed.

  Infix "^" := op.

  Add Field vs_field : vs_field.
  Add Ring module_ring : module_ring. 
End NthVectorSpaceSig.

(* This seems like a really hackish way to get around Type issues with modules *)
Module NthVectorSpaceIns (Hack : Nat)(Group : GroupSig)(Field : FieldSig)
    (NthGroup : GroupNthSig Group Hack)(VS : VectorSpaceSig Group Field) <: VectorSpaceSig NthGroup Field.
  Import VS.  

  Import NthGroup.
  Export NthGroup.
  Import Field.
  Export Field.

  Module MatF := MatricesFIns Field.
  Module Mat := MatricesG Group Field VS MatF.
  Import Mat.
  Import MatF.
  
  
  Definition op (a :G)(b : F) := VG_Sexp a b.

  Lemma mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
  Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
      rewrite mod_dist_Gdot. do 2 rewrite Vnth_map. trivial.
  Qed.

  Lemma mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
  Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_map2.
      rewrite mod_dist_Fadd. do 2 rewrite Vnth_map. trivial. 
  Qed.

  Lemma mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
  Proof.
      intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. 
      rewrite mod_dist_Fmul. trivial. 
  Qed.

  Lemma mod_id : forall (x : G), op x Fone = x.
  Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. 
      rewrite <- mod_id. trivial. 
  Qed.
    
  Lemma mod_ann : forall (x : G), op x Fzero = Gone.
  Proof.
     intros. apply Veq_nth. intros. rewrite Vnth_map.  
      rewrite mod_ann. rewrite Vnth_const. trivial. 
  Qed.

  Infix "^" := op.

  Add Field vs_field : vs_field.
  Add Ring module_ring : module_ring. 
End NthVectorSpaceIns.

(* A module space constructed from another by taking the prod of the group *)
Module Type NthModuleSig (Hack : Nat)(Group : GroupSig)(Ring : RingSig)
    (NthGroup : GroupNthSig Group Hack)(NthRing : NthRingSig Hack Ring)
    (M : ModuleSig Group Ring) <: ModuleSig NthGroup NthRing.
  
  Import M.
  Import NthGroup.
  Import NthRing.

  Definition op (a :G)(b : F) := Vmap2 op a b.

  Lemma mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
  Proof.
      intros. apply Veq_nth. intros. do 5 rewrite Vnth_map2.
      rewrite mod_dist_Gdot. trivial.
  Qed.

  Lemma mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
  Proof.
      intros. apply Veq_nth. intros. do 5 rewrite Vnth_map2.
      rewrite mod_dist_Fadd. trivial. 
  Qed.

  Lemma mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
  Proof.
      intros. apply Veq_nth. intros. do 4 rewrite Vnth_map2. 
      rewrite mod_dist_Fmul. trivial. 
  Qed.

  Lemma mod_id : forall (x : G), op x Fone = x.
  Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map2. 
      rewrite <- mod_id. rewrite Vnth_const. trivial. 
  Qed.
    
  Lemma mod_ann : forall (x : G), op x Fzero = Gone.
  Proof.
     intros. apply Veq_nth. intros. rewrite Vnth_map2.  
     do 2 rewrite Vnth_const. rewrite mod_ann. trivial. 
  Qed.

  Infix "^" := op.
End NthModuleSig.

Module NthModuleIns (Hack : Nat)(Group : GroupSig)(Ring : RingSig)
    (NthGroup : GroupNthSig Group Hack)(NthRing : NthRingSig Hack Ring)
    (M : ModuleSig Group Ring) <: ModuleSig NthGroup NthRing.
  
  Import M.
  Import NthGroup.
  Import NthRing.

  Definition op (a :G)(b : F) := Vmap2 op a b.

  Lemma mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
  Proof.
      intros. apply Veq_nth. intros. do 5 rewrite Vnth_map2.
      rewrite mod_dist_Gdot. trivial.
  Qed.

  Lemma mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
  Proof.
      intros. apply Veq_nth. intros. do 5 rewrite Vnth_map2.
      rewrite mod_dist_Fadd. trivial. 
  Qed.

  Lemma mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
  Proof.
      intros. apply Veq_nth. intros. do 4 rewrite Vnth_map2. 
      rewrite mod_dist_Fmul. trivial. 
  Qed.

  Lemma mod_id : forall (x : G), op x Fone = x.
  Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map2. 
      rewrite <- mod_id. rewrite Vnth_const. trivial. 
  Qed.
    
  Lemma mod_ann : forall (x : G), op x Fzero = Gone.
  Proof.
     intros. apply Veq_nth. intros. rewrite Vnth_map2.  
     do 2 rewrite Vnth_const. rewrite mod_ann. trivial. 
  Qed.

  Infix "^" := op.
End NthModuleIns.

Module Type VectorSpaceModuleSameGroupNthSig (Hack : Nat)(Group : GroupSig)(Field : FieldSig)
  (Ring : RingSig)(VS : VectorSpaceSig Group Field)(NthGroup : GroupNthSig Group Hack)(NthRing : NthRingSig Hack Field) 
  (NthVectorSpace : NthVectorSpaceSig Hack Group Field NthGroup VS)
   <: VectorSpaceModuleSameGroup NthGroup NthRing Field NthVectorSpace.
  
  Import Field.

  Definition op3 (a : NthRing.F)(b : Field.F) := 
    Vmap (fun x => Field.Fmul x b) a.
  Lemma RopInv : forall a, op3 a (Finv Fone) = NthRing.Finv a.
    Proof.
     intros. apply Veq_nth. intros. do 2 rewrite Vnth_map. field; auto.
    Qed.
  Lemma RopInvDis : forall a b, op3 (NthRing.Finv a) b = NthRing.Finv (op3 a b).
  Proof.
    intros. apply Veq_nth. intros. do 4 rewrite Vnth_map. field; auto. 
  Qed.
    Lemma RopFZero : forall x, op3 x Fzero = NthRing.Fzero.
    Proof.
      intros. unfold op3. apply Veq_nth. intros.
      rewrite Vnth_map. rewrite Vnth_const. field; auto.
    Qed.
    Lemma RopFOne : forall x, op3 x Fone = x.
    Proof. 
      intros. unfold op3. apply Veq_nth. intros.
      rewrite Vnth_map. field; auto.
    Qed.
    Lemma RopRZero : forall x, op3 NthRing.Fzero x = NthRing.Fzero.
    Proof.
      intros. unfold op3. apply Veq_nth. intros.
      rewrite Vnth_map. rewrite Vnth_const. field; auto.
    Qed.
    Lemma RopDistRadd : forall x y z, op3 (NthRing.Fadd x y) z = 
      NthRing.Fadd (op3 x z) (op3 y z).
    Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
      do 2 rewrite Vnth_map. field; auto. 
    Qed.
    Lemma RopDistFadd : forall (r s : F) (x : NthRing.F), 
      op3 x (Fadd r s) = NthRing.Fadd (op3 x r) (op3 x s).
    Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_map2.
      do 2 rewrite Vnth_map. field; auto.
    Qed.
    Lemma RopDistFmul : forall x y z, op3 (op3 x y) z = 
      op3 x (Fmul y z).
    Proof.
      intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. field; auto.
    Qed.
    Lemma RaddInv : forall (a : NthRing.F)(b : F),
     (NthRing.Fadd (op3 a b) (op3 a (Finv b))) = NthRing.Fzero.
    Proof.
      intros. unfold op3. apply Veq_nth. intros. rewrite Vnth_map2.
      do 2 rewrite Vnth_map. rewrite Vnth_const. field; auto.
    Qed.
End VectorSpaceModuleSameGroupNthSig.

Module VectorSpaceModuleSameGroupNthIns(Hack : Nat)(Group : GroupSig)(Field : FieldSig)
  (VS : VectorSpaceSig Group Field)(NthGroup : GroupNthSig Group Hack)(NthRing : NthRingSig Hack Field) 
  (NthVectorSpace : NthVectorSpaceSig Hack Group Field NthGroup VS)
   <: VectorSpaceModuleSameGroup NthGroup NthRing Field NthVectorSpace.
  
  Definition op3 (a : NthRing.F)(b : Field.F) := 
    Vmap (fun x => Field.Fmul x b) a.

  Import Field.

  Lemma RopInv : forall a, op3 a (Finv Fone) = NthRing.Finv a.
    Proof.
     intros. apply Veq_nth. intros. do 2 rewrite Vnth_map. field; auto.
    Qed.
  Lemma RopInvDis : forall a b, op3 (NthRing.Finv a) b = NthRing.Finv (op3 a b).
  Proof.
    intros. apply Veq_nth. intros. do 4 rewrite Vnth_map. field; auto. 
  Qed.
    Lemma RopFZero : forall x, op3 x Fzero = NthRing.Fzero.
    Proof.
      intros. unfold op3. apply Veq_nth. intros.
      rewrite Vnth_map. rewrite Vnth_const. field; auto.
    Qed.    
    Lemma RopFOne : forall x, op3 x Fone = x.
    Proof. 
      intros. unfold op3. apply Veq_nth. intros.
      rewrite Vnth_map. field; auto.
    Qed.
    Lemma RopRZero : forall x, op3 NthRing.Fzero x = NthRing.Fzero.
    Proof.
      intros. unfold op3. apply Veq_nth. intros.
      rewrite Vnth_map. rewrite Vnth_const. field; auto.
    Qed.
    Lemma RopDistRadd : forall x y z, op3 (NthRing.Fadd x y) z = 
      NthRing.Fadd (op3 x z) (op3 y z).
    Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
      do 2 rewrite Vnth_map. field; auto. 
    Qed.
    Lemma RopDistFadd : forall (r s : F) (x : NthRing.F), 
      op3 x (Fadd r s) = NthRing.Fadd (op3 x r) (op3 x s).
    Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_map2.
      do 2 rewrite Vnth_map. field; auto.
    Qed.
    Lemma RopDistFmul : forall x y z, op3 (op3 x y) z = 
      op3 x (Fmul y z).
    Proof.
      intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. field; auto.
    Qed.
    Lemma RaddInv : forall (a : NthRing.F)(b : F),
     (NthRing.Fadd (op3 a b) (op3 a (Finv b))) = NthRing.Fzero.
    Proof.
      intros. unfold op3. apply Veq_nth. intros. rewrite Vnth_map2.
      do 2 rewrite Vnth_map. rewrite Vnth_const. field; auto.
    Qed.
End VectorSpaceModuleSameGroupNthIns.


Module Type VectorSpaceModuleSameGroupNthStack(Hack : Nat)(Group : GroupSig)(Field : FieldSig)(Ring : RingSig)
  (VS : VectorSpaceSig Group Field)(NthGroup : GroupNthSig Group Hack)(NthRing : NthRingSig Hack Ring) 
  (NthVectorSpace : NthVectorSpaceSig Hack Group Field NthGroup VS)(MVS : VectorSpaceModuleSameGroup
  Group Ring Field VS) <: VectorSpaceModuleSameGroup NthGroup NthRing Field NthVectorSpace.
  
  Definition op3 (a : NthRing.F)(b : Field.F) := 
    Vmap (fun x => MVS.op3 x b) a.

  Import Field.

  Lemma RopInv : forall a, op3 a (Finv Fone) = NthRing.Finv a.
    Proof.
     intros. apply Veq_nth. intros. do 2 rewrite Vnth_map. rewrite MVS.RopInv. trivial.
    Qed.
  Lemma RopInvDis : forall a b, op3 (NthRing.Finv a) b = NthRing.Finv (op3 a b).
  Proof.
    intros. apply Veq_nth. intros. do 4 rewrite Vnth_map. rewrite MVS.RopInvDis. trivial.
  Qed.
    Lemma RopFZero : forall x, op3 x Fzero = NthRing.Fzero.
    Proof.
      intros. unfold op3. apply Veq_nth. intros.
      rewrite Vnth_map. rewrite Vnth_const. rewrite MVS.RopFZero. trivial.
    Qed.
    Lemma RopFOne : forall x, op3 x Fone = x.
    Proof. 
      intros. unfold op3. apply Veq_nth. intros.
      rewrite Vnth_map. apply MVS.RopFOne. 
    Qed.
    Lemma RopRZero : forall x, op3 NthRing.Fzero x = NthRing.Fzero.
    Proof.
      intros. unfold op3. apply Veq_nth. intros.
      rewrite Vnth_map. rewrite Vnth_const. rewrite MVS.RopRZero. trivial.
    Qed.
    Lemma RopDistRadd : forall x y z, op3 (NthRing.Fadd x y) z = 
      NthRing.Fadd (op3 x z) (op3 y z).
    Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
      do 2 rewrite Vnth_map. rewrite MVS.RopDistRadd.  trivial.
    Qed.
    Lemma RopDistFadd : forall (r s : F) (x : NthRing.F), 
      op3 x (Fadd r s) = NthRing.Fadd (op3 x r) (op3 x s).
    Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_map2.
      do 2 rewrite Vnth_map. rewrite MVS.RopDistFadd. trivial.
    Qed.
    Lemma RopDistFmul : forall x y z, op3 (op3 x y) z = 
      op3 x (Fmul y z).
    Proof.
      intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. rewrite MVS.RopDistFmul. trivial.
    Qed.
    Lemma RaddInv : forall (a : NthRing.F)(b : F),
     (NthRing.Fadd (op3 a b) (op3 a (Finv b))) = NthRing.Fzero.
    Proof.
      intros. unfold op3. apply Veq_nth. intros. rewrite Vnth_map2.
      do 2 rewrite Vnth_map. rewrite Vnth_const. rewrite MVS.RaddInv. trivial.
    Qed.
End VectorSpaceModuleSameGroupNthStack.

Module VectorSpaceModuleSameGroupNthStackIns(Hack : Nat)(Group : GroupSig)(Field : FieldSig)(Ring : RingSig)
  (VS : VectorSpaceSig Group Field)(NthGroup : GroupNthSig Group Hack)(NthRing : NthRingSig Hack Ring) 
  (NthVectorSpace : NthVectorSpaceSig Hack Group Field NthGroup VS)(MVS : VectorSpaceModuleSameGroup
  Group Ring Field VS) <: VectorSpaceModuleSameGroup NthGroup NthRing Field NthVectorSpace.
  
  Definition op3 (a : NthRing.F)(b : Field.F) := 
    Vmap (fun x => MVS.op3 x b) a.

  Import Field.

  Lemma RopInv : forall a, op3 a (Finv Fone) = NthRing.Finv a.
    Proof.
     intros. apply Veq_nth. intros. do 2 rewrite Vnth_map. rewrite MVS.RopInv. trivial.
    Qed.
  Lemma RopInvDis : forall a b, op3 (NthRing.Finv a) b = NthRing.Finv (op3 a b).
  Proof.
    intros. apply Veq_nth. intros. do 4 rewrite Vnth_map. rewrite MVS.RopInvDis. trivial.
  Qed.
    Lemma RopFZero : forall x, op3 x Fzero = NthRing.Fzero.
    Proof.
      intros. unfold op3. apply Veq_nth. intros.
      rewrite Vnth_map. rewrite Vnth_const. rewrite MVS.RopFZero. trivial.
    Qed.
    Lemma RopFOne : forall x, op3 x Fone = x.
    Proof. 
      intros. unfold op3. apply Veq_nth. intros.
      rewrite Vnth_map. apply MVS.RopFOne.
    Qed.
    Lemma RopRZero : forall x, op3 NthRing.Fzero x = NthRing.Fzero.
    Proof.
      intros. unfold op3. apply Veq_nth. intros.
      rewrite Vnth_map. rewrite Vnth_const. rewrite MVS.RopRZero. trivial.
    Qed.
    Lemma RopDistRadd : forall x y z, op3 (NthRing.Fadd x y) z = 
      NthRing.Fadd (op3 x z) (op3 y z).
    Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
      do 2 rewrite Vnth_map. rewrite MVS.RopDistRadd.  trivial.
    Qed.
    Lemma RopDistFadd : forall (r s : F) (x : NthRing.F), 
      op3 x (Fadd r s) = NthRing.Fadd (op3 x r) (op3 x s).
    Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_map2.
      do 2 rewrite Vnth_map. rewrite MVS.RopDistFadd. trivial.
    Qed.
    Lemma RopDistFmul : forall x y z, op3 (op3 x y) z = 
      op3 x (Fmul y z).
    Proof.
      intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. rewrite MVS.RopDistFmul. trivial.
    Qed.
    Lemma RaddInv : forall (a : NthRing.F)(b : F),
     (NthRing.Fadd (op3 a b) (op3 a (Finv b))) = NthRing.Fzero.
    Proof.
      intros. unfold op3. apply Veq_nth. intros. rewrite Vnth_map2.
      do 2 rewrite Vnth_map. rewrite Vnth_const. rewrite MVS.RaddInv. trivial.
    Qed.
End VectorSpaceModuleSameGroupNthStackIns.
