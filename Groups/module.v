Require Import Bool.
Require Import Setoid.
Require Import Ring.
Require Import Field.
Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import groups.

Module Type RingSig.
  Parameter F : Set.
  Parameter Fadd : F -> F -> F. 
  Parameter Fzero : F.
  Parameter Fbool_eq : F-> F-> bool.
  Parameter Fsub : F -> F -> F.
  Parameter Finv : F -> F.
  Parameter Fmul : F -> F -> F.
  Parameter Fone : F.
  Axiom module_ring : ring_theory Fzero Fone Fadd Fmul Fsub Finv (@eq F).

  Axiom F_bool_eq_corr: forall a b : F, Fbool_eq a b = true <-> a=b.
  Axiom F_bool_eq_sym : forall a b: F, Fbool_eq a b= Fbool_eq b a.
  Axiom  F_bool_neq_corr: forall a b : F, Fbool_eq a b = false <-> a <> b.

  Infix "+" := Fadd.
  Infix "*" := Fmul.
  Notation "0" := Fzero.
  Notation "1" := Fone.
  Notation "- x" :=  (Finv x).
  Notation "x - y" := (x + (- y)).

  Add Ring module_ring : module_ring.
End RingSig.

Module RingAddationalLemmas (Ring : RingSig).
  Import Ring.

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
    trivial. assert (x+y-x=y). destruct module_ring.
    rewrite <- Radd_assoc. replace (y-x) with (Finv x+y).
    rewrite Radd_assoc. rewrite Ropp_def. rewrite Radd_0_l. trivial.
    apply Radd_comm.
    assert (x+z-x=z).  destruct module_ring.
    rewrite <- Radd_assoc. replace (z-x) with (Finv x+z).
    rewrite Radd_assoc. rewrite Ropp_def. rewrite Radd_0_l. trivial.
    apply Radd_comm. rewrite <- H1. rewrite <- H2. apply H0. intros. 
    rewrite H. trivial.
  Qed.

  Lemma Fmul_left_cancel : forall (x y z : F),
    y = z -> x * y = x * z.
  Proof.
    intros. rewrite H. trivial.
  Qed.

   Lemma F_right_cancel : forall (x y z : F),
    y + x = z + x <-> y = z.
  Proof.
    destruct module_ring.
    intros. unfold iff. refine (conj _ _). intros.
    apply (F_left_cancel x y z). rewrite Radd_comm.
    rewrite H. ring; auto.
    (* part 2 *)
    intros. rewrite H. trivial.
  Qed.

  (* This lemma is only for when things go bad *)
  Lemma move_neg : forall (a b : F),
    Finv (a * b) = a * (Finv b).
  Proof.
    intros. ring; auto. 
  Qed.

  Lemma move_neg2 : forall (a b : F),
    Finv (a * b) = (Finv a) * b.
  Proof.
    intros. ring; auto. 
  Qed.
    
  Lemma shift :
    forall (a b : F),
     a = b <-> a - b = 0.
  Proof.
    destruct module_ring. 
    intros. unfold iff. refine (conj _ _). intros.
    rewrite H. apply module_ring. intros. replace b with (b + 0).
    rewrite <- H.  replace (a-b) with (Finv b+a).
    rewrite Radd_assoc. rewrite Ropp_def. rewrite Radd_0_l. trivial.
    apply Radd_comm. rewrite Radd_comm. apply Radd_0_l.
  Qed.

  Lemma inverse :
    forall (a b : F),
    a - b = 0 <-> b - a = 0.
  Proof.
    intros. intros. unfold iff. refine (conj _ _).   
    intros. apply shift in H. rewrite H. apply module_ring.
    intros. apply shift in H. rewrite H. apply module_ring.
  Qed.

  Lemma inv_dis : forall (x y : F),
    Finv (x + y) = (Finv x) + (Finv y).
  Proof.
    intros. ring; auto.
  Qed.

  Lemma Finv_inv : forall (x : F),
    Finv (Finv x) = x.
  Proof.
      intros. ring.
  Qed.

  Lemma whenAutoFails1 :
    forall (a b : F),
      a = a + b - b.
  Proof.
    intros. ring; auto.
  Qed.
  
  Lemma whenAutoFails2 : 
    forall (a b : F),
      a = a - b + b.
  Proof.
    intros. ring; auto.
  Qed.

  Lemma whenAutoFail3 :
    forall (a : F),
    a * (Finv 1) = Finv a.
  Proof.
    intros. ring; auto.
  Qed.

  Lemma whenAutoFail4 :
    forall (a : F),
    a * 0 = 0.
  Proof.
    intros. ring; auto.
  Qed.

  Lemma bi_exp : forall (a b c d : F),
    (a + b) * (c + d) = a*c+a*d+b*c+b*d.
  Proof.
    intros. ring; auto.
  Qed.
  
  (* The following is a suite of cancel lemmas for terms of length 4 *)
  Lemma cancel_1_1 : forall (a b c d e f g h : F),
    a=e ->
    b+c+d = f+g+h -> a+b+c+d=e+f+g+h.
  Proof.
    destruct module_ring.
    intros. rewrite H. do 4 rewrite <- Radd_assoc. apply f_equal.
    do 2 rewrite Radd_assoc. trivial.
  Qed. 

  Lemma cancel_1_2 : forall (a b c d e f g h : F),
    a=f ->
    b+c+d = e+g+h -> a+b+c+d=e+f+g+h.
  Proof.
    destruct module_ring.
    intros. rewrite H. do 2 rewrite <- Radd_assoc. rewrite <- Radd_assoc in H0.
    rewrite H0. ring; auto.
  Qed. 

  Lemma cancel_1_3 : forall (a b c d e f g h : F),
    a=g ->
    b+c+d = e+f+h -> a+b+c+d=e+f+g+h.
  Proof.
    destruct module_ring.
    intros. rewrite H. do 2 rewrite <- Radd_assoc. rewrite <- Radd_assoc in H0.
    rewrite H0. ring; auto.
  Qed. 

  (* 
  Lemma cancel_1_4 :
  
  Lemma cancel_2_1 :
  
  Lemma cancel_2_2 : *)

  Lemma cancel_2_3 : forall (a b c d e f g h : F),
    b=g ->
    a+c+d = e+f+h -> a+b+c+d=e+f+g+h.
  Proof.
    destruct module_ring.
    intros. rewrite H. replace (a + g + c + d) with (a + c + d + g).
    rewrite H0. ring. ring.
  Qed. 

  (* 
  Lemma cancel_2_4 :

  Lemma cancel_3_1 :

  Lemma cancel_3_2 : *)

  Lemma cancel_3_3 : forall (a b c d e f g h : F),
    c=g ->
    a+b+d = e+f+h -> a+b+c+d=e+f+g+h.
  Proof.
    destruct module_ring.
    intros. rewrite H. replace (a + b + g + d) with (a + b + d + g).
    rewrite H0. ring. ring.
  Qed. 

  (*

  Lemma cancel_3_4 :

  Lemma cancel_4_1 :

  Lemma cancel_4_2 :

  Lemma cancel_4_3 :

  Lemma cancel_4_4 :
  *)

End RingAddationalLemmas.

(** We first define a module *)
Module Type ModuleSig (Group : GroupSig)(Ring : RingSig).
  Import Group.
  Export Group.
  Import Ring.
  Export Ring.

  Parameter op : G -> F -> G.

  Axiom mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
  Axiom mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
  Axiom mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
  Axiom mod_id : forall (x : G), op x Fone = x.
  Axiom mod_ann : forall (x : G), op x Fzero = Gone.

  Infix "o" := Gdot (at level 50) .
  Notation "- x" := (Ginv x).

  Infix "^" := op.
End ModuleSig.


Module ModuleAddationalLemmas (Group : GroupSig)(Ring : RingSig)
                                  (M : ModuleSig Group Ring).
  Import M.

  Lemma F_left_cancel : forall (x y z : F),
    x + y = x + z <-> y = z.
  Proof.
    intros. unfold iff. refine (conj _ _). intros.
    assert ((x + y)-x=  (x +z)-x). rewrite H.
    trivial. assert (x+y-x=y). destruct module_ring.
    rewrite <- Radd_assoc. replace (y-x) with (Finv x+y).
    rewrite Radd_assoc. rewrite Ropp_def. rewrite Radd_0_l. trivial.
    apply Radd_comm.
    assert (x+z-x=z).  destruct module_ring.
    rewrite <- Radd_assoc. replace (z-x) with (Finv x+z).
    rewrite Radd_assoc. rewrite Ropp_def. rewrite Radd_0_l. trivial.
    apply Radd_comm. rewrite <- H1. rewrite <- H2. apply H0. intros. 
    rewrite H. trivial.
  Qed.

   Lemma F_right_cancel : forall (x y z : F),
    y + x = z + x <-> y = z.
  Proof.
    destruct module_ring.
    intros. unfold iff. refine (conj _ _). intros.
    apply (F_left_cancel x y z). rewrite Radd_comm.
    rewrite H. ring; auto.
    (* part 2 *)
    intros. rewrite H. trivial.
  Qed.

  Lemma F_mul_left_cancel : forall (x y z : F),
    y = z -> x * y = x * z.
  Proof.
    intros. rewrite H. trivial.
  Qed.

  Lemma F_mul_right_cancel : forall (x y z : F),
    y = z -> y * x = z * x.
  Proof.
    intros. rewrite H. trivial.
  Qed.

  (* This lemma is only for when things go bad *)
  Lemma move_neg : forall (a b : F),
    Finv (a * b) = a * (Finv b).
  Proof.
    intros. ring; auto. 
  Qed.
    
  Lemma shift :
    forall (a b : F),
     a = b <-> a - b = 0.
  Proof.
    destruct module_ring. 
    intros. unfold iff. refine (conj _ _). intros.
    rewrite H. apply module_ring. intros. replace b with (b + 0).
    rewrite <- H.  replace (a-b) with (Finv b+a).
    rewrite Radd_assoc. rewrite Ropp_def. rewrite Radd_0_l. trivial.
    apply Radd_comm. rewrite Radd_comm. apply Radd_0_l.
  Qed.

  Lemma inverse :
    forall (a b : F),
    a - b = 0 <-> b - a = 0.
  Proof.
    intros. intros. unfold iff. refine (conj _ _).   
    intros. apply shift in H. rewrite H. apply module_ring.
    intros. apply shift in H. rewrite H. apply module_ring.
  Qed.
  Lemma mod_dist_FMul2 :
   forall (r s: F) (x : G), op x (Fmul s r) = op (op x s) r.
  Proof.
    intros. destruct module_ring. rewrite Rmul_comm. 
    rewrite mod_dist_Fmul. trivial.
  Qed.

  Lemma neg_eq :
  forall (a : F)(b : G), -(b^a) = (b^(Finv a)).
  Proof. 
    intros. pose (right_cancel (H:= module_abegrp)(b ^ a)(- b ^ a)(b ^ (Finv a))).
    apply i.
    replace (abegop (- b ^ a) (b ^ a)) with Gone. rewrite <- mod_dist_Fadd. 
    replace (Finv a + a) with Fzero.
    rewrite mod_ann. trivial. destruct module_ring.
    rewrite Radd_comm. rewrite Ropp_def. trivial. remember (b ^ a) as c. 
    pose (inv_left (Group:= (abegrp_grp (AbeGroup:= module_abegrp)))).  
    apply e.
  Qed.

  Lemma mod_mone : forall (x : F),
    Gone ^ x = Gone.
  Proof.
    intros. replace (Gone) with (Gone ^ 0). rewrite <- mod_dist_Fmul.
    replace (x * 0) with 0. trivial.  destruct module_ring.
    rewrite Rmul_comm. assert (semi_ring_theory Fzero Fone Fadd Fmul 
    (@eq F)). constructor; auto. intros. ring; auto. symmetry. apply H.
    apply mod_ann.
  Qed.

  Lemma mak : forall (x y : F),
    Finv (x + y) = (Finv x) + (Finv y).
  Proof.
    intros. ring; auto.
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

  
End ModuleAddationalLemmas.
