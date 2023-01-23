Require Import Bool.
Require Import Setoid.
Require Import Ring.
Require Import Field.
Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import groups.
Require Import module.

Module Type FieldSig <: RingSig.
  Parameter F : Set.
  Parameter Fadd : F -> F -> F. 
  Parameter Fzero : F.
  Parameter Fbool_eq : F-> F-> bool.
  Parameter Fsub : F -> F -> F.
  Parameter Finv : F -> F.
  Parameter Fmul : F -> F -> F.
  Parameter Fone : F.
  Parameter FmulInv : F -> F.
  Parameter Fdiv : F-> F-> F.

  Axiom vs_field : field_theory Fzero Fone Fadd Fmul Fsub Finv Fdiv FmulInv (@eq F).
  Axiom module_ring : ring_theory Fzero Fone Fadd Fmul Fsub Finv (@eq F).

  Axiom F_bool_eq_corr: forall a b : F, Fbool_eq a b = true <-> a=b.
   Axiom F_bool_eq_sym : forall a b: F, Fbool_eq a b= Fbool_eq b a.
  Axiom  F_bool_neq_corr: forall a b : F, Fbool_eq a b = false <-> a <> b.

  Infix "+" := Fadd.
  Infix "*" := Fmul.
  Notation "x / y" := (Fmul x (FmulInv y)). 
  Notation "0" := Fzero.
  Notation "1" := Fone.
  Notation "- x" :=  (Finv x).
  Notation "x - y" := (x + (- y)).
  
  Add Field vs_field : vs_field.
  Add Ring module_ring : module_ring.
End FieldSig.


(** We now define vector space *)

Module Type VectorSpaceSig (Group : GroupSig)(Field : FieldSig)
                     <: ModuleSig Group Field.
  Import Group.
  Export Group.
  Import Field.
  Export Field.

  Parameter op : G -> F -> G.

  Axiom mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
  Axiom mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
  Axiom mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
  Axiom mod_id : forall (x : G), op x Fone = x.
  Axiom mod_ann : forall (x : G), op x Fzero = Gone.

  Infix "o" := Gdot (at level 50) .
  Notation "- x" := (Ginv x).

  Infix "^" := op.
End VectorSpaceSig.

(* We now prove some general results about vector spaces *)



Module FieldAddationalLemmas (Field : FieldSig).

  Import Field.
    Module AL := RingAddationalLemmas Field.

  Lemma F_mul_zero : forall (a b : F),
    a * b = 0 -> a = 0 \/ b = 0.
  Proof.
    destruct vs_field. destruct F_R. intros. case_eq (Fbool_eq a 0). intros. 
    apply F_bool_eq_corr in H0. left. trivial. right. apply F_bool_neq_corr in H0. 
    apply (AL.Fmul_left_cancel (FmulInv a)) in H. rewrite Rmul_assoc in H.
    rewrite Finv_l in H; auto. ring_simplify in H. trivial.
  Qed. 

  Lemma F_mul_nzero : forall (a b : F),
    a * b <> 0 <-> a <> 0 /\ b <> 0.
  Proof.
    destruct vs_field. destruct F_R. split; intros. 
    + split. unfold not. intros. apply H. rewrite H0. field.
    unfold not. intros. apply H. rewrite H0. field.
    + unfold not. intros. destruct H. apply F_mul_zero in H0. destruct H0.
    contradiction. contradiction.
  Qed. 
  
End FieldAddationalLemmas.

Module VectorSpaceAddationalLemmas (Group : GroupSig)(Field : FieldSig)
  (VS: VectorSpaceSig Group Field).


  Import VS.
  Module AL := RingAddationalLemmas Field.

  Lemma F_mul_zero : forall (a b : F),
    a * b = 0 -> a = 0 \/ b = 0.
  Proof.
    destruct vs_field. destruct F_R. intros. case_eq (Fbool_eq a 0). intros. 
    apply F_bool_eq_corr in H0. left. trivial. right. apply F_bool_neq_corr in H0. 
    apply (AL.Fmul_left_cancel (FmulInv a)) in H. rewrite Rmul_assoc in H.
    rewrite Finv_l in H; auto. ring_simplify in H. trivial.
  Qed. 

  Lemma F_mul_split : forall (x y z w : F),
    x = y -> z = w -> x * z = y * w.
  Proof.
    intros. rewrite H. rewrite H0. trivial.
  Qed.

  Lemma F_left_cancel : forall (x y z : F),
    x + y = x + z <-> y = z.
  Proof.
    intros. unfold iff. refine (conj _ _). intros.
    assert ((x + y)-x=  (x +z)-x). rewrite H.
    trivial. assert (x+y-x=y). destruct vs_field.
    destruct F_R. rewrite <- Radd_assoc. replace (y-x) with (Finv x+y).
    rewrite Radd_assoc. rewrite Ropp_def. rewrite Radd_0_l. trivial.
    apply Radd_comm.
    assert (x+z-x=z).  destruct vs_field.
    destruct F_R. rewrite <- Radd_assoc. replace (z-x) with (Finv x+z).
    rewrite Radd_assoc. rewrite Ropp_def. rewrite Radd_0_l. trivial.
    apply Radd_comm. rewrite <- H1. rewrite <- H2. apply H0. intros. 
    rewrite H. trivial.
  Qed.

  (* This lemma is only for when things go bad *)
  Lemma move_neg : forall (a b : F),
    Finv (a * b) = a * (Finv b).
  Proof.
    intros. field; auto. 
  Qed.
    
  Lemma shift :
    forall (a b : F),
     a = b <-> a - b = 0.
  Proof.
    destruct vs_field. destruct F_R.
    intros. unfold iff. refine (conj _ _). intros.
    rewrite H. apply vs_field. intros. replace b with (b + 0).
    rewrite <- H.  replace (a-b) with (Finv b+a).
    rewrite Radd_assoc. rewrite Ropp_def. rewrite Radd_0_l. trivial.
    apply Radd_comm. rewrite Radd_comm. apply Radd_0_l.
  Qed.

  Lemma inverse :
    forall (a b : F),
    a - b = 0 <-> b - a = 0.
  Proof.
    intros. intros. unfold iff. refine (conj _ _).   
    intros. apply shift in H. rewrite H. apply vs_field.
    intros. apply shift in H. rewrite H. apply vs_field.
  Qed.
  Lemma mod_dist_FMul2 :
   forall (r s: F) (x : G), op x (Fmul s r) = op (op x s) r.
  Proof.
    intros. destruct vs_field. destruct F_R. rewrite Rmul_comm. 
    rewrite mod_dist_Fmul. trivial.
  Qed.

  Lemma neg_eq :
  forall (a : F)(b : G), -(b^a) = (b^(Finv a)).
  Proof. 
    intros. pose (right_cancel (H:= module_abegrp)(b ^ a)(- b ^ a)(b ^ (Finv a))).
    apply i.
    replace (abegop (- b ^ a) (b ^ a)) with Gone. rewrite <- mod_dist_Fadd. 
    replace (Finv a + a) with Fzero.
    rewrite mod_ann. trivial. destruct vs_field. destruct F_R.
    rewrite Radd_comm. rewrite Ropp_def. trivial. remember (b ^ a) as c. 
    pose (inv_left (Group:= (abegrp_grp (AbeGroup:= module_abegrp)))).  
    apply e.
  Qed.

  (*Lemma Gen_to_Gen : forall (g : G)(x : F),
    g <> Gone ->
    Gone = g ^ (x ) ->
    x = 0.
  Proof.
    intros. a
  Admitted.

  Lemma F_G_isomorphic : forall (g : G)(x y : F),
    g <> Gone ->
    g^x = g^y ->
    x = y.
  Proof.
    intros. apply shift. pose module_abegrp.
    assert (Gone o g^x  = Gone o g^y). 
    rewrite (left_cancel Gone). apply H0.
    symmetry in H1.
    apply commHackEq in H1. rewrite neg_eq in H1.
    rewrite <- mod_dist_Fadd in H1.
    rewrite <- inv_right in H1. apply (Gen_to_Gen g).
    apply H. apply H1.
  Qed. *)

  
  Lemma op_cancel : forall (x : F)(y z : G),
   x <> 0 -> y ^ x = z ^ x -> y = z.
  Proof.
    intros. assert ((y ^ x) ^ FmulInv x  = (z ^ x) ^ FmulInv x).
    rewrite H0. trivial. do 2 rewrite <- mod_dist_Fmul in H1. 
    replace (FmulInv x * x) with (Fone) in H1.
    do 2 rewrite mod_id in H1. apply H1. destruct vs_field. destruct F_R.
    symmetry. apply Finv_l. apply H.
  Qed.

  Lemma mod_mone : forall (x : F),
    Gone ^ x = Gone.
  Proof.
    intros. replace (Gone) with (Gone ^ 0). rewrite <- mod_dist_Fmul.
    replace (x * 0) with 0. trivial.  destruct vs_field. destruct F_R.
    rewrite Rmul_comm. assert (semi_ring_theory Fzero Fone Fadd Fmul 
    (@eq F)). constructor; auto. intros. field; auto. symmetry. apply H.
    apply mod_ann.
  Qed.

  Lemma neg_eq2 :
    forall (a : F)(b : G), ((-b)^a) = (b^(Finv a)).
  Proof. 
    intros.  pose module_abegrp. 
    pose (right_cancel (H:= module_abegrp)(b ^ a)((- b) ^ a)(b ^ (Finv a))).
    apply i. rewrite <- mod_dist_Fadd. rewrite <- mod_dist_Gdot.
    rewrite <- inv_left. replace (Finv a + a) with 0. rewrite mod_ann.
    rewrite mod_mone. trivial. ring; auto.
  Qed.
  
  Lemma ExtractorHelper :
    forall(a b :G)(e1 e2 : F),
    e1 - e2 <> 0 ->
    b = ((a o b^e1) o - (a o b^e2))^(FmulInv (e1 - e2)).
  Proof.
    pose vs_field. pose module_abegrp.
    intros. remember (b ^ e1) as c. remember (b ^ e2) as d.
    replace (a0 o c) with (c o a0). rewrite <- dot_assoc. 
    replace (- (a0 o d)) with (-a0 o -d). replace (a0 o ((- a0) o (- d)))
    with (-d). rewrite Heqc. rewrite Heqd. rewrite neg_eq.
    rewrite <- mod_dist_Fadd. rewrite <- mod_dist_Fmul.
    replace (FmulInv (e1 - e2) * (e1 - e2)) with 1. symmetry. apply mod_id.
    field; auto. rewrite dot_assoc. rewrite <- inv_right.
    rewrite one_left. trivial. apply inv_dist. apply comm.
  Qed.


  Lemma ExtractorHelper2 :
    forall(a b :G)(e1 e2 : F),
    e1 - e2 <> 0 ->
    b = ((b^e1 o a) o - (b^e2 o a))^(FmulInv (e1 - e2)).
  Proof.
    pose vs_field. pose module_abegrp. intros. replace (b^e1 o a0) with (a0 o b^e1).
    replace (b ^ e2 o a0) with (a0 o b^e2). apply ExtractorHelper.
    apply H. apply comm. apply comm. 
  Qed.

  Lemma whenAutoFails1 :
    forall (a b : F),
      a = a + b - b.
  Proof.
    intros. field; auto.
  Qed.
  
  Lemma whenAutoFails2 : 
    forall (a b : F),
      a = a - b + b.
  Proof.
    intros. field; auto.
  Qed.

  Lemma whenAutoFail3 :
    forall (a : F),
    a * (Finv 1) = Finv a.
  Proof.
    intros. field; auto.
  Qed.

  Lemma whenAutoFail4 :
    forall (a : F),
    a * 0 = 0.
  Proof.
    intros. field; auto.
  Qed.

  Lemma scaleEqFull :
    forall (g h : G)(a b :F),
    g = h -> a = b -> g^a = h^b.
  Proof.
    intros. rewrite H. rewrite H0. trivial.
  Qed.

  Lemma scaleEq :
    forall (g : G)(a b :F),
    a = b -> g^a = g^b.
  Proof.
    intros. rewrite H. trivial.
  Qed.

  Lemma mod_dist_Gdot_eq  : forall (r r' : F) (x y : G), 
    r = r' ->
    op (Gdot x y) r = Gdot (op x r) (op y r').
  Proof.
    intros. subst. apply mod_dist_Gdot.
  Qed.

  Lemma FmulInv_dist : forall a b,
     a <> 0 ->
     b <> 0 ->
     FmulInv (a * b) = FmulInv a * FmulInv b.
  Proof. 
    intros. field; auto.  
  Qed. 

  Lemma FsubZero : forall a,
    a - 0 = a.
  Proof.
    intros. field; auto.
  Qed.

End VectorSpaceAddationalLemmas.
