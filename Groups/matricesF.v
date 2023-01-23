Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.Bool.Bool.
Require Import groups.
Require Import Coq.Lists.List.
Require Import Ring.
Require Import Field.
From Coq Require Import Basics Morphisms Setoid.
From CoLoR Require Import RelDec OrdSemiRing LogicUtil RelExtras EqUtil NatUtil ZUtil SemiRing.
Require Import Coq.Vectors.Vector.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import CoLoR.Util.Vector.VecArith.
Require Import CoLoRmatrix.
Require Import module.
Require Import VectorUtil.
Require Import Coq.Logic.ConstructiveEpsilon.

Notation vector := Vector.t.
Notation Vconst := Vector.const.

Set Implicit Arguments.

Module Type MatricesF (Ring: RingSig).

  Import Ring.

  Lemma TrivialOrNot : (forall (x y : F), x = y) \/ 0 <> 1.
  Proof.
    intros. case_eq (Fbool_eq 0 1); intros. apply F_bool_eq_corr in H.
    left. intros. pose module_ring. destruct r. rewrite <- (Rmul_1_l x).
    rewrite <- (Rmul_1_l y). rewrite <- H. ring; auto. 
    apply F_bool_neq_corr in H. right. trivial.
  Qed.

  Module F <: SetA.
    Definition A := F.
  End F.

  Module F_Eqset := Eqset_def F.

  Module F_Eqset_dec <: Eqset_dec.
    Module Export Eq := F_Eqset.
    Definition eqA_dec := dec_beq F_bool_eq_corr.
  End F_Eqset_dec.

  Lemma FSRth : semi_ring_theory Fzero Fone Fadd Fmul (@eq F).
  Proof.
    constructor. apply module_ring. apply module_ring. apply module_ring. 
    apply module_ring. intros. ring; auto. apply module_ring. apply module_ring. 
    apply module_ring. 
  Qed.

  Module FSemiRingT <: SemiRingType.

    Module Export ES := F_Eqset_dec.

    Definition A0 := Fzero.
    Definition A1 := Fone.

    Definition Aplus := Fadd.

    Instance Aplus_mor : Proper (eqA ==> eqA ==> eqA) Aplus.
    Proof. intros a b ab c d cd. rewrite ab. rewrite cd. refl. Qed.


    Definition Amult := Fmul.

    Instance Amult_mor : Proper (eqA ==> eqA ==> eqA) Amult.
      Proof. intros a b ab c d cd. rewrite ab. rewrite cd. refl. Qed.

    Definition A_semi_ring := FSRth.

  End FSemiRingT.

  Module FMatrix := Matrix FSemiRingT.

  Module ALR := RingAddationalLemmas Ring.

  (* This file contains the definitions and lemmas about matrices *)
  (* This needs to be generalised, so that we can do the
   extraction of the mixnet properly *)

  Infix "+" := Fadd.
  Infix "*" := Fmul.
  Notation "0" := Fzero.
  Notation "1" := Fone.
  Notation "- x" :=  (Finv x).
  Notation "x - y" := (x + (- y)).

  Notation " [ x ; .. ; y ] " := (Vcons x .. (Vcons y Vnil) ..).

  (*We use P* to denote the pairwise use of the operation *)
  (*We use S* to denote the scaler use of the operation *)

  Lemma Vcons_Vapp : forall (N :nat)(A :Type)(a : A)(b : vector A N),
    Vapp [a] b = Vcons a b.
  Proof.
    intros. cbn. trivial.
  Qed.

  Definition VF : nat -> Set := vector F.
  Definition VF_zero := Vconst Fzero.
  Definition VF_one := Vconst Fone. 
  Definition VF_n_id (n N : nat)(np : n < N) := FMatrix.VA.id_vec np.
  Definition VF_prod n (v : VF n) : F :=
    Vfold_left Fmul Fone v.
  Definition VF_sum n (v : VF n) : F :=
    Vfold_left Fadd Fzero v.
  Definition VF_add n (v1 v2 : VF n) : VF n :=
    FMatrix.VA.vector_plus v1 v2.
  Definition VF_neg n (v1 : VF n) : VF n :=
    Vmap Finv v1.
  Definition VF_sub n (v1 v2 : VF n) : VF n :=
    VF_add v1 (VF_neg v2).
  Definition VF_mult n (v1 v2 : VF n) : VF n :=
    Vmap2 Fmul v1 v2.
  Definition VF_scale n (v : VF n)(s : F) : VF n :=
    Vmap (fun x => Fmul x s) v.
  Definition VF_inProd n (v v' : VF n) : F :=
    FMatrix.VA.dot_product v v'.
  Definition VF_eq n (r r' : VF n) : Prop :=
    Vforall2 (@eq F) r r'.
  Definition VF_beq n (r r' : VF n) : bool :=
    bVforall2 Fbool_eq r r'.
  Definition VF_an_id n (v : VF n) : bool :=
     bVexists (VF_beq v) (Vbuild (fun i ip =>  (FMatrix.VA.id_vec ip))).

  Definition Vector_0_is_nil (T : Type) (v : Vector.t T 0) : v = Vector.nil :=
  match v with Vector.nil => eq_refl end.


  Lemma Veq_nth3 : forall (n : nat)(A : Type)(v v' : vector A n),
    (forall i j (ip : i < n)(jp : j < n),
    i = j -> v = v' -> Vnth v ip = Vnth v' jp).
  Proof.
    intros. subst. apply Vnth_eq. trivial.
  Qed.

  Lemma Veq_nth2 : forall (n : nat)(A : Type)(v v' : vector A n),
    v = v' -> (forall i (ip : i < n), Vnth v ip = Vnth v' ip).
  Proof.
   intros. rewrite H. trivial.
  Qed.

  Lemma Vfold_left_eq : forall (n : nat)(A B : Type) (f : A->B->A)
    (v v' : vector B n)(a : A),
    v = v' -> Vfold_left f a v = Vfold_left f a v'.
  Proof.
    intros. rewrite H. trivial.
  Qed.

  Lemma Vfold_left_eq_cast : forall (n n' : nat)(H : n = n')
    (A B : Type)(f : A->B->A)(v : vector B n)
    (v' : vector B n')(a : A),
    Vcast v H = v' -> Vfold_left f a v = Vfold_left f a v'.
  Proof.
    intros. subst. trivial.
  Qed.

  Lemma Vfold_left_cast : forall (n n' : nat)(H : n = n')
    (A B : Type)(f : A->B->A)(v : vector B n)(a : A),
    Vfold_left f a v = Vfold_left f a (Vcast v H).
  Proof.
    intros. subst. trivial.
  Qed.


  Lemma Vtail_remove_last : forall (n : nat)(A : Type)(v : vector A (S (S n))),
    Vtail (Vremove_last v) = Vremove_last (Vtail v).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_tail.
    do 2 rewrite Vnth_remove_last. rewrite Vnth_tail.
    apply Vnth_eq. trivial.
  Qed.

  Lemma Vfold_left_remove_last : forall (A B : Type)(N : nat)
    (f : A->B->A)(v : vector B (S N))(np : Nat.lt N (S N))(a : A),
    Vfold_left f a v = f (Vfold_left f a (Vremove_last v)) (Vnth v np).
  Proof.
    intros A B N f v np. induction N. intros. cbn. rewrite (VSn_eq v). 
    simpl. rewrite (Vector_0_is_nil (Vtail v)). simpl. trivial. 
    intros. remember (Vremove_last v) as c. rewrite (VSn_eq c). 
    rewrite (VSn_eq v). simpl. rewrite IHN. intros. rewrite Heqc.
    assert (forall a a' b b', a=a' -> b=b' -> f a b = f a' b').
    intros. rewrite H. rewrite H0. trivial. apply H.
    assert ((f a (Vhead v)) = (f a (Vhead (Vremove_last v)))).
    do 2 rewrite Vhead_nth. apply H; auto. rewrite Vnth_remove_last.
    apply Vnth_eq. trivial. rewrite H0. apply Vfold_left_eq.
    rewrite Vtail_remove_last. trivial. apply Vnth_eq. trivial.
    auto.
  Qed. 

  Lemma Vfold_left_rev_eq : forall (n : nat)(A B : Type) (f : A->B->A)
    (v v' : vector B n)(a : A),
    v = v' -> Vfold_left_rev f a v = Vfold_left_rev f a v'.
  Proof.
    intros. rewrite H. trivial.
  Qed.

  Lemma Vmap2_eq : forall (n : nat)(A B C : Type) (f : A->B->C)
    (a a' : vector A n)(b b'  : vector B n),
    a = a' -> b = b' -> Vmap2 f a b = Vmap2 f a' b'.
  Proof.
    intros. rewrite H. rewrite H0. trivial.
  Qed.


  Lemma Vtail_map:  forall (N : nat)(A B : Type) (f : A->B)(v : vector A (1+N)),
    Vtail (Vmap f v) = Vmap f (Vtail v).
  Proof.
   intros. apply Veq_nth. intros. rewrite Vnth_tail. do 2 rewrite Vnth_map.
   rewrite Vnth_tail. trivial.
  Qed.

  Lemma Vtail_map2 : forall (A B C : Type) (f: A->B->C) (n :nat)
          (v : vector A (S n)) (v' : vector B (S n)),
      Vmap2 f (Vtail v) (Vtail v') = Vtail (Vmap2 f v v').
  Proof. 
    intros. VSntac v. refl. 
  Qed.

  Lemma Vremove_last_vmap2 :  forall (A B C : Type)(f : A->B->C)(N : nat)
    (v : vector A (S N))(v' : vector B (S N)),
    Vremove_last (Vmap2 f v v') = 
      Vmap2 f (Vremove_last v) (Vremove_last v').
  Proof.
    intros. assert (forall a a' b b', a=a' -> b=b' -> f a b = f a' b').
    intros. rewrite H. rewrite H0. trivial. induction N. cbn. trivial.
    rewrite (VSn_eq (Vremove_last (Vmap2 f v v'))).
    rewrite (VSn_eq (Vmap2 f (Vremove_last v) (Vremove_last v'))).
     apply Vcons_eq_intro. cbn. apply H. rewrite Vhead_nth. apply Vnth_eq.
    trivial. rewrite Vhead_nth. apply Vnth_eq. trivial.
    rewrite <- Vtail_map2. do 3 rewrite Vtail_remove_last. apply IHN. 
  Qed.

  Lemma Vapp_map : forall (N : nat)(A B : Type) (f : A->B)(v : vector A (1+N)),
    (Vapp [Vhead (Vmap f v)](Vtail (Vmap f v))) = 
    Vmap f (Vapp [Vhead v] (Vtail v)).
  Proof.
    intros. apply Veq_nth. intros. induction i.
    cbn. rewrite Vhead_nth. rewrite Vnth_map. rewrite <- Vhead_nth.
    trivial. cbn. rewrite Vnth_tail. do 2 rewrite Vnth_map.
    rewrite Vnth_tail. trivial.
  Qed.

  Lemma Vfold_Fadd_const :  forall (n : nat)(v : vector F n)(a : F),
    forall (h : F),
    (Vfold_left Fadd h v) + a = Vfold_left Fadd (h + a) v.
  Proof.
    intros n v0 a. induction v0. cbn. intros. trivial. cbn. 
    intros. assert (Vfold_left Fadd (h0 + h) v0 + a =
         Vfold_left Fadd ((h0 + h) + a) v0). apply IHv0.
    replace ((h0 + a) + h) with ((h0 + h) + a). apply H.
    ring; auto.
  Qed.

  Lemma Vfold_Fmul_const :  forall (n : nat)(v : vector F n)(a : F),
    forall (h : F),
    (Vfold_left Fmul h v) * a = Vfold_left Fmul (h * a) v.
  Proof.
    intros n v0 a. induction v0. cbn. intros. trivial. cbn. 
    intros. assert (Vfold_left Fmul (h0 * h) v0 * a =
         Vfold_left Fmul ((h0 * h) * a) v0). apply IHv0.
    replace ((h0 * a) * h) with ((h0 * h) * a). apply H.
    ring; auto.
  Qed.

  (* Square matrices of order 2 over Field F *)
  Definition index1 : 0%nat < 2%nat.
  Proof.
    auto.
  Defined.

  Lemma index1eq : forall (A : Type)(v : vector A 2%nat), 
    (Vnth v (Nat.lt_0_succ 1)) = Vnth v index1.
  Proof.
    intros. apply Vnth_eq. trivial.
  Qed.

  Definition index2 : 1%nat < 2%nat.
  Proof.
   auto.
  Defined. 

  Lemma index2eq : forall (A : Type)(v : vector A 2%nat), 
    (Vnth v (lt_n_S (Nat.lt_0_succ 0))) = Vnth v index2.
  Proof.
    intros. apply Vnth_eq. trivial.
  Qed.

  Lemma Vfold_left_Vcons_Fadd :
    forall (a : F)(n : nat)(b : VF n),
    Vfold_left Fadd Fzero (Vcons a b) = Vfold_left Fadd Fzero b + a.
  Proof. 
    intros. induction b. cbn. trivial.
    cbn. rewrite Vfold_Fadd_const.
    assert (((Fzero + a) + h) = ((Fzero + h) + a)).
    ring; auto. rewrite H. trivial.
  Qed.

  Lemma Vfold_left_Vadd_Fadd :
    forall (a : F)(n : nat)(b : VF n),
    Vfold_left Fadd Fzero (Vadd b a) = Vfold_left Fadd Fzero b + a.
  Proof. 
    intros. induction b. cbn. trivial.
    cbn. do 2 rewrite <- Vfold_Fadd_const. rewrite IHb.
    ring; auto.
  Qed.

  Lemma Vfold_left_Vadd_Fmul :
    forall (a : F)(n : nat)(b : VF n),
    Vfold_left Fmul Fone (Vadd b a) = Vfold_left Fmul Fone b * a.
  Proof. 
    intros. induction b. cbn. trivial.
    cbn. do 2 rewrite <- Vfold_Fmul_const. rewrite IHb.
    ring; auto.
  Qed.

  Lemma Vfold_left_Vapp_Fadd :
    forall (n n' : nat)(a : VF n')(b : VF n),
    Vfold_left Fadd Fzero (Vapp a b) = 
      Vfold_left Fadd Fzero a + Vfold_left Fadd Fzero b.
  Proof. 
    intros. induction a. cbn. ring; auto.
    simpl. do 2 rewrite <- Vfold_Fadd_const. rewrite IHa. ring; auto.
  Qed.


  Lemma Vfold_left_Vcons_Fmul :
    forall (a : F)(n : nat)(b : VF n),
    Vfold_left Fmul Fone (Vcons a b) = Vfold_left Fmul Fone b * a.
  Proof.
    intros. induction b. cbn. trivial.
    cbn. rewrite Vfold_Fmul_const.
    assert (((Fone * a) * h) = ((Fone * h) * a)).
    ring; auto.
    rewrite H. intuition. 
  Qed.

  Lemma VF_sum_VF_zero : forall n,
   VF_sum (VF_zero n) = 0.
  Proof.
    intros. induction n. cbn. trivial.
    simpl. unfold VF_sum in *. rewrite Vfold_left_Vcons_Fadd. 
    rewrite IHn. ring; auto.
  Qed.

  Lemma VF_prod_const : forall (c : F)(i j : nat),
      VF_prod (Vconst c i) * VF_prod (Vconst c j) = 
        VF_prod (Vconst c (i+j)).
  Proof.
    intros. induction i. cbn. unfold VF_prod. ring; auto.
    simpl. unfold VF_prod in *. do 2 rewrite Vfold_left_Vcons_Fmul.
    rewrite <- IHi. ring; auto.
  Qed.

  Lemma VG_prod_const_index : forall (c : F)(i j : nat),
    i = j -> VF_prod (Vconst c i) = VF_prod (Vconst c j).
  Proof.
    intros. rewrite H. trivial.
  Qed.

  Lemma VF_add_move : forall n (a b c : VF n),
    a = VF_add b c <-> VF_add a (VF_neg c) = b.
  Proof.
    intros. pose module_ring. destruct r. 
    split; intros. rewrite H. apply Veq_nth; intros. 
    do 2 rewrite Vnth_map2. rewrite Vnth_map. rewrite <- Radd_assoc.
    rewrite Ropp_def. rewrite Radd_comm. rewrite Radd_0_l.  trivial.
    rewrite <- H. apply Veq_nth; intros. do 2 rewrite Vnth_map2. 
    rewrite Vnth_map. rewrite <- Radd_assoc. rewrite <- (Radd_comm (Vnth c ip)).
    rewrite Ropp_def. rewrite Radd_comm. rewrite Radd_0_l.  trivial.
  Qed.

  Definition MF : nat -> Type := (fun x => FMatrix.matrix x x).                     
  Definition MF_id n : MF n := FMatrix.id_matrix n.
  Definition MF_col n (m : MF n) i (ip :i < n) : VF n :=
    FMatrix.get_col m ip.
  Definition MF_row n (m : MF n) i (ip :i < n) : VF n :=
    FMatrix.get_row m ip.
  Definition MF_mult n (m m':MF n) : MF n :=
    FMatrix.mat_mult m m'.
  Definition MF_trans n (m : MF n) : MF n :=
    FMatrix.mat_transpose m.
  Definition MF_CVmult n (m : MF n)(v : VF n) : VF n :=
    FMatrix.mat_vec_prod m v.
  Definition MF_VCmult n (v : VF n)(m : MF n) : VF n :=
   FMatrix.row_mat_to_vec (FMatrix.mat_mult (FMatrix.vec_to_row_mat v) m).
  Definition MF_eq n (m m' : MF n) : Prop :=
   FMatrix.mat_eqA m m'.
  Definition MF_Fscal n (m : MF n)(v : VF n) : MF n :=
    FMatrix.mat_build (fun i j ip jp => 
      Vnth (VF_mult (FMatrix.get_row m ip) v) jp).
  Definition MF_scal n (m : MF n)(a : F) : MF n :=
    FMatrix.mat_build (fun i j ip jp => 
     FMatrix.get_elem m ip jp * a).
  Definition MFisPermutation n (m : MF n) : bool :=
     bVforall (VF_an_id (n:=n)) m && bVforall (VF_an_id (n:=n)) (FMatrix.mat_transpose m).

  Lemma Vnth_MF_build : forall n (gen : forall i j, i < n -> j < n -> F) i
       (ip : i < n),
    Vnth (FMatrix.mat_build gen) ip = Vbuild (fun j (jp : j < n) => gen i j ip jp).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth. rewrite FMatrix.mat_build_nth.
    trivial.
  Qed.

  Lemma transpose_eq : forall n (a b : MF n),
      a = b <-> FMatrix.mat_transpose a = FMatrix.mat_transpose b.
  Proof.
    intros. split; intros.
    + apply Veq_nth. intros. apply Veq_nth. intros. do 2 rewrite FMatrix.mat_build_nth.
      unfold FMatrix.get_elem. apply (Veq_nth4 ip0) in H. apply (Veq_nth4 ip) in H.
      trivial.
    + apply Veq_nth. intros. apply Veq_nth. intros.  apply (Veq_nth4 ip0) in H.
      apply (Veq_nth4 ip) in H. do 2 rewrite FMatrix.mat_build_nth in H.
      unfold FMatrix.get_elem in H.
      trivial.
  Qed.

  Lemma transpose_move :
    forall (n : nat)(a b : MF n),
    FMatrix.mat_transpose (MF_mult a b) = 
    MF_mult (FMatrix.mat_transpose b) (FMatrix.mat_transpose a).
  Proof.
   intros. apply Veq_nth. intros. apply Veq_nth. intros.
   rewrite FMatrix.get_elem_swap. rewrite FMatrix.mat_transpose_row_col.
   unfold FMatrix.get_row. do 2 rewrite FMatrix.mat_build_nth.
   rewrite FMatrix.mat_transpose_row_col. rewrite <- (FMatrix.mat_transpose_idem b).
   rewrite FMatrix.mat_transpose_row_col. rewrite FMatrix.mat_transpose_idem.
    rewrite FMatrix.VA.dot_product_comm. trivial.
  Qed.

  Lemma transpose_move_gen :
    forall (n m l: nat)(a : FMatrix.matrix n m)
      (b : FMatrix.matrix m l),
    FMatrix.mat_transpose (FMatrix.mat_mult a b) = 
    FMatrix.mat_mult (FMatrix.mat_transpose b) (FMatrix.mat_transpose a).
  Proof.
   intros. apply Veq_nth. intros. apply Veq_nth. intros.
   rewrite FMatrix.get_elem_swap. rewrite FMatrix.mat_transpose_row_col.
   unfold FMatrix.get_row. do 2 rewrite FMatrix.mat_build_nth.
   rewrite FMatrix.mat_transpose_row_col. rewrite <- (FMatrix.mat_transpose_idem b).
   rewrite FMatrix.mat_transpose_row_col. rewrite FMatrix.mat_transpose_idem.
    rewrite FMatrix.VA.dot_product_comm. trivial.
  Qed.

  (*Addational definitions thaat only make sense for the crypto we are doing*)
  Lemma reasoningAboutIndexs : forall i : nat,
     (i < 2) -> (i = 0%nat \/ i = 1%nat).
  Proof.
    intros. induction i. left. trivial. right. lia.
  Qed.

  Infix "+" := Fadd.
  Infix "*" := Fmul.
  Notation "0" := Fzero.
  Notation "1" := Fone.
  Notation "- x" :=  (Finv x).
  Notation "x - y" := (x + (- y)).
  Notation " [ x ; .. ; y ] " := (Vcons x .. (Vcons y Vnil) ..).

  Lemma InProd_Vcons :
    forall (N : nat)(a b :F)(c d : VF N),
      VF_inProd (Vcons a c) (Vcons b d) = VF_inProd c d + a*b.
  Proof.
    intros. unfold VF_inProd. unfold FMatrix.VA.dot_product. simpl.
    trivial.
  Qed.

  Lemma InProd_Vcons2 :
    forall (N : nat)(a b :F)(c d : VF N),
      VF_inProd (Vcons a c) (Vcons b d) = a*b + VF_inProd c d.
  Proof.
    intros. unfold VF_inProd. unfold FMatrix.VA.dot_product. simpl.
    destruct module_ring. apply Radd_comm.
  Qed.

  Lemma InProd_Induction :
    forall (N : nat)(a b : VF (S N)),
      VF_inProd a b = VF_inProd (Vtail a) (Vtail b) + 
        (Vhead a)*(Vhead b).
  Proof.
    intros. unfold VF_inProd. unfold FMatrix.VA.dot_product. simpl.
    trivial.
  Qed.

  Lemma InProd_Induction2 :
    forall (N : nat)(a b : VF (S N)),
      VF_inProd a b = (Vhead a)*(Vhead b) + 
        VF_inProd (Vtail a) (Vtail b).
  Proof.
    intros. unfold VF_inProd. unfold FMatrix.VA.dot_product. simpl.
    destruct module_ring. apply Radd_comm.
  Qed.

  Lemma VF_add_vcons :
    forall (N : nat)(a b : VF (1+N)),
    VF_add a b = Vcons (Vhead a + Vhead b)
        (VF_add (Vtail a) (Vtail b)).
  Proof.
    intros. cbn. trivial. 
  Qed.

  Lemma VF_scale_0 : forall (N:nat)(r : VF N),
    VF_scale r 0 = VF_zero N.
  Proof.
    intros. apply Veq_nth. intros.
    rewrite Vnth_map. rewrite Vnth_const.
    ring; auto.
  Qed.

  Lemma VF_scale_1 : forall (N:nat)(r : VF N),
    VF_scale r 1 = r.
  Proof.
    intros. apply Veq_nth. intros.
    rewrite Vnth_map.
    ring; auto.
  Qed.

  Lemma VF_scale_1_map : forall n m (A : vector (VF m) n),
    Vmap2 (VF_scale (n:=m)) A (VF_one n) = A.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_const. 
    apply VF_scale_1.
  Qed.

  Lemma VF_scale_1_gen : forall (N:nat)(r : VF N) a,
    a = 1 ->
    VF_scale r a = r.
  Proof.
    intros. subst. apply VF_scale_1.
  Qed.

  Lemma VF_scale_map2 : forall n m (A : vector (VF m) n) (B C : VF n),
     Vmap2 (VF_scale (n:=m)) (Vmap2 (VF_scale (n:=m)) A B) C =
     Vmap2 (VF_scale (n:=m)) A (VF_mult B C).
  Proof.
    intros. apply Veq_nth. intros. do 4 rewrite Vnth_map2. apply Veq_nth.
    intros. do 3 rewrite Vnth_map. ring; auto.
  Qed.

  Lemma VF_scale_scale : forall n (v : VF n) a b,
    VF_scale (VF_scale v a) b = VF_scale v (a*b).
  Proof.
    intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. ring; auto.
  Qed.
 
 Lemma VF_scale_map_com : forall n m (A : vector (VF m) n) (B: VF n) a,
    Vmap (fun x => VF_scale x a) (Vmap2 (VF_scale (n:=m)) A B) = 
    Vmap2 (VF_scale (n:=m)) A (VF_scale B a).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
    rewrite Vnth_map. apply Veq_nth. intros. do 3 rewrite Vnth_map. ring; auto. 
  Qed. 

  Lemma VF_scale_map : forall n m (A : vector (VF m) n) b c,
    Vmap (fun x => VF_scale x b) (Vmap (fun x => VF_scale x c) A) =
    Vmap (fun x => VF_scale x (b*c)) A.
  Proof.
    intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. apply Veq_nth. intros.
    do 3 rewrite Vnth_map. ring; auto.
  Qed.

  Lemma VF_scale_vcons :  forall (N :nat)(r w c : F)(r' w' : VF N),
    Vcons (r + w * c) (VF_add r' (VF_scale w' c)) = 
      VF_add (Vapp [r] r') (VF_scale (Vapp [w] w') c).
  Proof.
    intros. cbn. apply Veq_nth. intros.
    induction i. cbn. unfold FSemiRingT.Aplus. trivial.
    cbn.  rewrite Vnth_map2. unfold FSemiRingT.Aplus. auto.
  Qed.

  Lemma VF_scale_vcons2 :  forall (N :nat)(r w c : F)(r' w' : VF N),
    Vcons ((r + w) * c) (VF_scale (VF_add r' w') c) =
    VF_scale (VF_add (Vapp [r] r') (Vapp [w] w')) c.
  Proof.
    intros. cbn. apply Veq_nth. intros.
    induction i. cbn. unfold FSemiRingT.Aplus. trivial.
    cbn.  rewrite Vnth_map. unfold FSemiRingT.Aplus. auto.
  Qed.

  Lemma VF_scale_imp : forall (N :nat)(a b : VF N) c,
    a = b -> VF_scale a c = VF_scale b c.
  Proof.
    intros. rewrite H. trivial.
  Qed.

  Lemma VF_sum_induction :
    forall(N : nat)(v : VF (1+N)),
    VF_sum v = VF_sum (Vtail v) + (Vhead v).
  Proof.
    intros. remember (VF_sum (Vtail v) + Vhead v) as b.
    rewrite (VSn_eq v). rewrite Heqb. cbn. rewrite Vfold_Fadd_const.
    trivial.
  Qed.

  Lemma VF_prod_induction :
    forall (n : nat)(a : VF (S n)),
    VF_prod a = VF_prod (Vtail a) * (Vhead a).
  Proof.
    intros. rewrite (VSn_eq a). apply Vfold_left_Vcons_Fmul.
  Qed.

  Lemma VF_sum_induction2 :
    forall(N : nat)(v : VF (1+N)),
    VF_sum v = (Vhead v) + VF_sum (Vtail v).
  Proof.
    intros. remember (Vhead v + VF_sum (Vtail v)) as b.
    rewrite (VSn_eq v). rewrite Heqb. cbn. destruct module_ring.
    symmetry. rewrite Radd_comm. rewrite Vfold_Fadd_const.
    trivial.
  Qed.

   Lemma VF_sum_vcons : forall (N : nat)(a: F)(v : VF N),
    VF_sum (Vcons a v) = VF_sum v + a.
  Proof.
    intros. rewrite VF_sum_induction. simpl. trivial.
  Qed.

  Lemma Vnth_MF :
    forall (N: nat)(m m' : MF N),
    forall i (ip : i < N) j (jp : j < N), 
    Vnth (Vnth (MF_mult m m') ip) jp = 
      VF_inProd (MF_row m ip) (MF_col m' jp).
  Proof.
    intros. rewrite FMatrix.mat_mult_elem.
    unfold VF_inProd, MF_row, MF_col. 
    unfold FMatrix.VA.dot_product, FMatrix.VA.dot_product.
     trivial.
  Qed.

  Lemma VF_scale_Vtail :
  forall N, forall (u :VF (S N))(a : F),
    VF_scale (Vtail u) a = Vtail (VF_scale u a).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. 
    do 2 rewrite Vnth_tail. rewrite Vnth_map. trivial.
  Qed.

  Lemma MF_Vnth_id :
    forall (n : nat)(i : nat)(ip : i < n),
    Vnth (MF_id n) ip = FMatrix.VA.id_vec ip.
  Proof.
    intros. unfold MF_id, FMatrix.id_matrix. 
    rewrite Vbuild_nth. trivial.
  Qed.

  Lemma MF_Col_id :
    forall (n : nat)(i : nat)(ip : i < n),
    MF_col (MF_id n) ip = FMatrix.VA.id_vec ip.
  Proof.
    intros. unfold MF_id, FMatrix.id_matrix. 
    apply Veq_nth. intros.  rewrite Vnth_map.
    rewrite Vbuild_nth. case_eq (i0 =? i).
    (* part 1 *)  
    intros. apply beq_nat_true in H. subst. 
    do 2 rewrite Vnth_replace. trivial.
    (* part 2 *)
    intros. apply beq_nat_false in H.
    rewrite Vnth_replace_neq. apply H.
    rewrite Vnth_replace_neq. unfold not in *.
    intros. symmetry in H0. apply H. apply H0.
    do 2 rewrite Vnth_const. trivial.
  Qed.


  Lemma Vnth_vcast : 
    forall (A : Type)(n n' j : nat)(v1 : vector A n)
    (v2 : vector A n')(hi : j <n)(hi' : j < n + n'),
    Vnth v1 hi = Vnth (Vapp v1 v2) hi'.
  Proof.
    intros. rewrite Vnth_app. destruct (le_gt_dec n j).
    lia. apply Vnth_eq. trivial.
  Qed.

  Lemma MFeq :
    forall (N : nat)(m m' : MF N),
    MF_eq m m' <-> m = m'.
  Proof.
    intros. unfold iff. refine (conj _ _).  intros. unfold MF_eq in *. 
    unfold FMatrix.mat_eqA in H. unfold FMatrix.get_elem in H. 
    apply Veq_nth. intros. unfold FMatrix.get_row in H. 
    unfold FSemiRingT.ES.Eq.eqA in H. apply Veq_nth. intros. apply H.
    (* part 2 *)
    intros. rewrite H. unfold MF_eq. unfold FMatrix.mat_eqA.
    unfold FSemiRingT.ES.Eq.eqA. intros. trivial. 
  Qed.

  Lemma MF_getRow_prod :
    forall (N :nat)(A: MF N)(rTil : VF N)(i :nat)(ip: i <N),
    Vnth (MF_CVmult A rTil) ip = 
      VF_inProd (Vnth A ip) rTil.
  Proof.
    intros. unfold MF_CVmult, FMatrix.mat_mult.
    unfold FMatrix.mat_vec_prod. unfold FMatrix.col_mat_to_vec, FMatrix.mat_mult, FMatrix.vec_to_col_mat.
    unfold FMatrix.get_col. rewrite Vnth_map.  
    rewrite FMatrix.mat_build_nth. unfold VF_inProd. 
    unfold FMatrix.VA.dot_product, FMatrix.VA.dot_product.
    apply Vfold_left_rev_eq. apply Veq_nth. intros.
    do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map. cbn.
    unfold FMatrix.get_row, FSemiRingT.Amult.
    trivial.
  Qed.

  Lemma MF_getRow_prod_gen :
    forall (n n' :nat)(A: vector (VF n) n')(rTil : VF n)(i :nat)(ip: i < n'),
    Vhead (Vnth (FMatrix.mat_mult A (FMatrix.mat_transpose [rTil])) ip) = 
      VF_inProd (Vnth A ip) rTil.
  Proof.
    intros. rewrite Vhead_nth. rewrite FMatrix.mat_build_nth. unfold VF_inProd.
    unfold FMatrix.get_row. apply f_equal2; auto. rewrite FMatrix.mat_transpose_row_col.
    cbn. trivial.
  Qed.

  Lemma MF_getCol_prod :
    forall (N :nat)(A: MF N)(rTil : VF N)(i :nat)(ip: i <N),
    Vnth (MF_VCmult rTil A) ip = 
      VF_inProd rTil (MF_col A ip).
  Proof.
    intros. unfold MF_VCmult, FMatrix.mat_mult, FMatrix.row_mat_to_vec, FMatrix.get_row.
    rewrite FMatrix.mat_build_nth. unfold VF_inProd. cbn.
    unfold MF_col. trivial.
  Qed.

  Lemma MF_getCol_prod_gen :
    forall (n n' :nat)(A: vector (VF n') n)(rTil : VF n)(i :nat)(ip: i < n'),
    Vnth (Vhead (FMatrix.mat_mult [rTil] A)) ip = 
      VF_inProd rTil (FMatrix.get_col A ip).
  Proof.
    intros. rewrite Vhead_nth. rewrite FMatrix.mat_build_nth. unfold VF_inProd.
    simpl. trivial.
  Qed.

  Lemma MF_getRow_VCmul :
    forall (N :nat)(A B : MF N)(i :nat)(ip: i <N),
    Vnth (MF_mult A B) ip = MF_VCmult (Vnth A ip) B.
  Proof.
    intros. apply Veq_nth. intros. unfold MF_mult, MF_VCmult.
    unfold FMatrix.mat_mult, FMatrix.row_mat_to_vec, FMatrix.mat_mult.
    unfold FMatrix.get_row, FMatrix.vec_to_row_mat.
    do 2 rewrite FMatrix.mat_build_nth. cbn. trivial.
  Qed.

  Lemma dot_product_v :
    forall (N : nat)(a v v' : VF N),
    v = v' -> FMatrix.VA.dot_product a v = FMatrix.VA.dot_product a v'.
  Proof.
    intros. rewrite H. trivial.
  Qed.

  Lemma MF_getRow_CVmul :
    forall (N :nat)(A B : MF N)(i :nat)(ip: i <N),
    MF_col (MF_mult B A) ip = MF_CVmult B (MF_col A ip).
  Proof.
    intros. apply Veq_nth. intros. unfold MF_mult, MF_CVmult, MF_col.
    unfold FMatrix.mat_mult, FMatrix.mat_vec_prod, FMatrix.mat_mult.
    unfold FMatrix.col_mat_to_vec, FMatrix.get_col. do 2 rewrite Vnth_map.
    do 2 rewrite FMatrix.mat_build_nth. apply dot_product_v.
    unfold FMatrix.vec_to_col_mat. apply Veq_nth. intros. 
    do 4 rewrite Vnth_map. cbn. trivial.
  Qed.

  Lemma Id_transpose :
    forall (N :nat),
    MF_id N = FMatrix.mat_transpose (MF_id N).
  Proof.
    intros. apply MFeq. unfold MF_eq, FMatrix.mat_eqA. intros.
    unfold FSemiRingT.ES.Eq.eqA. unfold MF_id. unfold FMatrix.id_matrix.
    unfold FMatrix.mat_transpose, FMatrix.get_row. rewrite FMatrix.mat_build_elem.
    unfold FMatrix.get_elem, FMatrix.get_row. do 2 rewrite Vbuild_nth.
    unfold FMatrix.VA.id_vec. case_eq (i =? j).
    (* part 1 *)  
    intros. apply beq_nat_true in H.
    apply Veq_nth3. symmetry. apply H. apply Vreplace_pi. apply H.
    (* part 2 *)
    intros. apply beq_nat_false in H. rewrite Vnth_replace_neq. apply H.
    rewrite Vnth_replace_neq. unfold not in *. intros. symmetry in H0. 
    apply H in H0. apply H0. do 2 rewrite Vnth_const. trivial.
  Qed.

  Lemma Id_select1 :
    forall (N :nat)(m:MF N),
    forall (i j :nat)(ip : i< N)(jp : j < N),
   FMatrix.VA.dot_product (FMatrix.get_row (MF_id N) jp) 
    (FMatrix.get_col m ip) = FMatrix.get_elem m jp ip.
  Proof.
    intros. unfold MF_id.
    unfold FMatrix.get_row. unfold FMatrix.id_matrix. rewrite Vbuild_nth.
    rewrite FMatrix.VA.dot_product_id. unfold FMatrix.get_elem. rewrite FMatrix.get_elem_swap.
    trivial.
  Qed.

  Lemma Id_select2 :
    forall (N :nat)(m:MF N),
    forall (i j :nat)(ip : i< N)(jp : j < N),
   FMatrix.VA.dot_product (FMatrix.get_row m ip)
    (FMatrix.get_col (MF_id N) jp) = FMatrix.get_elem m ip jp.
  Proof.
    intros. rewrite FMatrix.VA.dot_product_comm. rewrite Id_transpose.
    rewrite FMatrix.mat_transpose_row_col. unfold MF_id.
    unfold FMatrix.get_row. unfold FMatrix.id_matrix. rewrite Vbuild_nth.
    rewrite FMatrix.VA.dot_product_id. unfold FMatrix.get_elem. rewrite FMatrix.get_elem_swap.
    trivial.
  Qed.

  Lemma Id_comm :
    forall (N :nat)(m:MF N),
    MF_mult m (MF_id N) = MF_mult (MF_id N) m.
  Proof.
    intros. rewrite <- MFeq. unfold MF_eq, FMatrix.mat_eqA, MF_mult, FMatrix.mat_mult.
    intros. do 2 rewrite FMatrix.mat_build_elem. unfold FSemiRingT.ES.Eq.eqA.
    (* Definitally happy with the proof to here. *)
    rewrite Id_select2. rewrite Id_select1. trivial.
  Qed.

  Lemma MF_one : 
    forall (N : nat)(m :MF N),
    MF_mult m (MF_id N) = m.
  Proof.
    intros. rewrite Id_comm. rewrite <- MFeq. apply FMatrix.mat_mult_id_l.
    auto.
  Qed.

  Lemma MF_assoc :
    forall (N : nat)(a b c : MF N),
    MF_mult (MF_mult a b) c = MF_mult a (MF_mult b c).
  Proof.
    intros. unfold MF_mult. symmetry. apply Veq_nth. intros. apply Veq_nth. intros.
    apply FMatrix.mat_mult_assoc.
  Qed.

  Lemma VF_add_one :
    forall (a : F),
    Vfold_left_rev Fadd 0 [a] = a.
  Proof.
    intros. cbn. ring; auto.
  Qed.

  Lemma Vnth_Vbuild_VF :
    forall (n N : nat),  forall(g : forall i, Nat.lt i (1+n)  -> (VF N)),
    forall(i : nat)(ip : i< N),
       Vmap (fun x : VF N => Vnth x ip) (Vbuild g) = 
    Vbuild (fun j jp => Vnth (g j jp) ip).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. 
    do 2 rewrite Vbuild_nth. trivial.
  Qed.

  Lemma VF_eq_corr :
    forall (n : nat)(a b : VF n),
    VF_eq a b <-> a = b.
  Proof.
    intros. unfold VF_eq. 
    refine (conj _ _). intros. apply Veq_nth.
    intros. apply (Vforall2_elim_nth ip) in H. apply H.
    intro. rewrite H. pose (Vforall2_intro_nth eq b b).
    apply v. intros. trivial.
  Qed.

  Lemma VF_beq_true : 
    forall (n : nat)(a b : VF n),
    VF_beq a b = true <-> a = b.
  Proof.
    intros. unfold VF_beq. pose (bVforall2_ok (@eq F) Fbool_eq).
    rewrite i. intros. apply F_bool_eq_corr.  apply VF_eq_corr.
  Qed.

  Lemma VF_beq_false : 
    forall (n : nat)(a b : VF n),
    VF_beq a b = false <-> a <> b.
  Proof.
    intros. unfold VF_beq. refine (conj _ _). intros.
    unfold not. intros. rewrite H0 in H.
    assert (bVforall2 Fbool_eq b b = true). apply VF_beq_true.
    trivial. eapply (eq_true_false_abs (bVforall2 Fbool_eq b b));
    auto. intros. unfold not in *. apply not_true_is_false. unfold not.
    intros.  apply H. apply VF_beq_true in H0. apply H0.
  Qed.

  Lemma VF_eq_dec : forall n (a : VF n),
    forall y : VF n, {VF_eq a y} + {~ (VF_eq a) y}.
  Proof.
    intros. case_eq (VF_beq a y); intros. left. apply VF_eq_corr. 
    apply VF_beq_true in H. trivial. right. apply VF_beq_false in H.
     unfold not. intros. apply H. apply VF_eq_corr in H0. trivial.
  Qed.
  
  Lemma VF_dist :
    forall N : nat, forall (x y z : VF N),
      VF_mult (VF_add x y) z = VF_add (VF_mult x z)(VF_mult y z).
  Proof.
    intros. apply Veq_nth. intros. do 5 rewrite Vnth_map2.
    unfold FSemiRingT.Aplus. destruct (module_ring). apply Rdistr_l.
  Qed.

  Lemma VF_add_zero :
    forall N, forall a : VF N,
    VF_add a (VF_zero N) = a.
  Proof.
    pose (module_ring). intros. unfold VF_zero. unfold VF_add. unfold FMatrix.VA.zero_vec.
    unfold FMatrix.VA.vector_plus. apply Veq_nth. intros.
    rewrite Vnth_map2. unfold FSemiRingT.A0. rewrite Vnth_const.
    unfold FSemiRingT.Aplus. rewrite Radd_comm. apply r. rewrite Radd_0_l.
    apply r. trivial.  
  Qed.

  Lemma VF_mult_one :
    forall N, forall a : VF N,
    VF_mult a (VF_one N) = a.
  Proof. 
    pose (module_ring). intros. apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vnth_const. destruct r. destruct module_ring.
    rewrite Rmul_comm. apply Rmul_1_l.
  Qed.

  Lemma VF_neg_corr :
    forall N, forall a : VF N,
    VF_add a (VF_neg a) = VF_zero N.
  Proof.
    pose (module_ring). intros. unfold VF_zero. unfold VF_add. unfold VF_neg.
    unfold FMatrix.VA.zero_vec.
    unfold FMatrix.VA.vector_plus. apply Veq_nth. intros.
    rewrite Vnth_map2. unfold FSemiRingT.A0. rewrite Vnth_const.
    unfold FSemiRingT.Aplus. rewrite Vnth_map. rewrite Ropp_def.
    apply r. trivial.
  Qed.

  Lemma VF_neg_neg : forall N (v : VF N),
    VF_neg (VF_neg v) = v.
  Proof.
    intros. apply Veq_nth. intros. do 2 rewrite Vnth_map. ring; auto.
  Qed.

  Lemma VF_neg_zero : forall N,
    VF_neg (VF_zero N) = VF_zero N.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_const.
    ring; auto.
  Qed.

  Lemma VF_sub_corr :
        forall N, forall a b : VF N,
    VF_sub a b = VF_add a (VF_neg b).
  Proof.
    intros. unfold VF_sub. trivial.
  Qed.

  Lemma VF_comm :
    forall N, forall a b : VF N,
    VF_add a b = VF_add b a.
  Proof.
    pose (module_ring). intros. unfold VF_add. apply Veq_nth. intros. 
    unfold FMatrix.VA.vector_plus. do 2 rewrite Vnth_map2.
    rewrite Radd_comm. apply r. trivial.
  Qed.

  Lemma VF_mult_ass :
    forall N, forall a b c : VF N,
    VF_mult (VF_mult a b) c = VF_mult a (VF_mult b c).
  Proof.
    pose (module_ring). intros. unfold VF_mult. apply Veq_nth. intros.
    do 4 rewrite Vnth_map2. destruct r. rewrite <- Rmul_assoc. trivial.
  Qed.

  Lemma VF_comm_mult :
    forall N, forall a b : VF N,
    VF_mult a b = VF_mult b a.
  Proof.
    pose (module_ring). intros. unfold VF_mult. apply Veq_nth. intros.
    do 2 rewrite Vnth_map2. destruct r. destruct module_ring.
   apply Rmul_comm.
  Qed.

  Lemma VF_add_ass :
    forall N, forall a b c : VF N,
    VF_add (VF_add a b) c = VF_add a (VF_add b c).
  Proof.
    pose (module_ring). intros. unfold VF_add. unfold FMatrix.VA.vector_plus.
    unfold FSemiRingT.Aplus. apply Veq_nth. intros.
    do 4 rewrite Vnth_map2. rewrite Radd_assoc. 
    apply r. trivial.
  Qed.

  Lemma VF_comm_hack : forall N, forall a b c d : VF N,
    VF_add (VF_add a b) (VF_add c d) = VF_add (VF_add a c) (VF_add b d).
  Proof.
    intros. do 2 rewrite VF_add_ass. apply f_equal. do 2 rewrite <- VF_add_ass.
    apply f_equal2. apply VF_comm. trivial.
  Qed.

  Lemma Vfold_VFadd_const :  forall (n m : nat)
    (v : vector (VF m) n)(a : (VF m)), forall (h : (VF m)),
    VF_add (Vfold_left (VF_add (n:=m)) h v) a = Vfold_left (VF_add (n:=m)) (VF_add h a) v.
  Proof.
    intros n m v0 a. induction v0. cbn. intros. trivial. cbn. 
    intros. assert (VF_add (Vfold_left (VF_add (n:=m)) (VF_add h0 h) v0) a =
         Vfold_left (VF_add (n:=m)) (VF_add (VF_add h0 h) a) v0). apply IHv0.
    replace (VF_add (VF_add h0 a) h) with (VF_add (VF_add h0 h) a). apply H.
    rewrite VF_add_ass. replace (VF_add h a) with (VF_add a h) by apply VF_comm.
    rewrite <- VF_add_ass. trivial.
  Qed.

  Lemma Vfold_VFmul_const :  forall (n m : nat)
    (v : vector (VF m) n)(a : (VF m)), forall (h : (VF m)),
    VF_mult (Vfold_left (VF_mult (n:=m)) h v) a = 
      Vfold_left (VF_mult (n:=m)) (VF_mult h a) v.
  Proof.
    intros n m v0 a. induction v0. cbn. intros. trivial. cbn. 
    intros. assert (VF_mult (Vfold_left (VF_mult (n:=m)) (VF_mult h0 h) v0) a =
         Vfold_left (VF_mult (n:=m)) (VF_mult (VF_mult h0 h) a) v0). apply IHv0.
    replace (VF_mult (VF_mult h0 a) h) with (VF_mult (VF_mult h0 h) a). apply H.
    rewrite VF_mult_ass. replace (VF_mult h a) with (VF_mult a h) by apply VF_comm_mult.
    rewrite <- VF_mult_ass. trivial.
  Qed.

  Lemma Vfold_left_VFadd_eq :
    forall (n m : nat)(v: vector (VF n) m),
    Vfold_left_rev (VF_add (n:=n)) (VF_zero n) v = 
      Vfold_left (VF_add (n:=n)) (VF_zero n) v.
  Proof.
   intros. induction v. cbn. trivial.
   cbn. rewrite <- Vfold_VFadd_const.
   rewrite IHv. trivial.
  Qed. 

  Lemma Vfold_left_Vcons_VFadd :
    forall (n n' : nat)(a : (VF n))(b : vector (VF n) n'),
    Vfold_left (VF_add (n:=n)) (VF_zero n) (Vcons a b) =
    VF_add (Vfold_left (VF_add (n:=n)) (VF_zero n) b) a.
  Proof.
    intros. induction b. cbn. trivial.
    cbn. rewrite Vfold_VFadd_const.
    assert ((VF_add (VF_add (VF_zero n) a) h) =
     (VF_add (VF_add (VF_zero n) h) a)).
    do 2 rewrite VF_add_ass. replace (VF_add a h) with
    (VF_add h a) by apply VF_comm. trivial. rewrite H. trivial.
  Qed.

  Lemma Vfold_left_Vcons_VFmult :
    forall (n n' : nat)(a : (VF n))(b : vector (VF n) n'),
    Vfold_left (VF_mult (n:=n)) (VF_one n) (Vcons a b) =
    VF_mult (Vfold_left (VF_mult (n:=n)) (VF_one n) b) a.
  Proof.
    intros. induction b. cbn. trivial.
    cbn. rewrite Vfold_VFmul_const.
    assert ((VF_mult (VF_mult (VF_one n) a) h) =
     (VF_mult (VF_mult (VF_one n) h) a)).
    do 2 rewrite VF_mult_ass. replace (VF_mult a h) with
    (VF_mult h a) by apply VF_comm_mult. trivial. rewrite H. trivial.
  Qed.

  Lemma Vfold_left_Vadd_VFadd :
    forall (n n' : nat)(a : (VF n))(b : vector (VF n) n'),
    Vfold_left (VF_add (n:=n)) (VF_zero n) (Vadd b a) =
    VF_add (Vfold_left (VF_add (n:=n)) (VF_zero n) b) a.
  Proof.
    intros. induction b. cbn. trivial. 
    cbn. do 2 rewrite <- Vfold_VFadd_const. symmetry. rewrite VF_comm.
    rewrite <- VF_add_ass. apply f_equal2; auto. rewrite IHb. apply VF_comm.
  Qed.

  Lemma Vfold_left_Vadd_VFmul :
    forall (n n' : nat)(a : (VF n))(b : vector (VF n) n'),
    Vfold_left (VF_mult (n:=n)) (VF_one n) (Vadd b a) =
    VF_mult (Vfold_left (VF_mult (n:=n)) (VF_one n) b) a.
  Proof.
    intros. induction b. cbn. trivial. 
    cbn. do 2 rewrite <- Vfold_VFmul_const. symmetry. rewrite VF_comm_mult.
    rewrite <- VF_mult_ass. apply f_equal2; auto. rewrite IHb. apply VF_comm_mult.
  Qed.

  Lemma VF_neg_move : forall N, forall a b : VF N,
    VF_neg (VF_add a b) = VF_add (VF_neg a) (VF_neg b).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
    do 2 rewrite Vnth_map.  apply ALR.inv_dis. 
  Qed.

  Lemma VF_add_neg :
    forall N, forall a b : VF N,
    VF_add (VF_add a b) (VF_neg b) = a.
  Proof.
    intros. rewrite VF_add_ass. rewrite VF_neg_corr.
    rewrite VF_add_zero. trivial.
  Qed.

  Lemma VF_add_neg2 :
    forall N, forall a b : VF N,
    VF_add (VF_add a (VF_neg b)) b = a.
  Proof.
    intros. rewrite VF_add_ass. replace (VF_add (VF_neg b) b) with
    (VF_add b (VF_neg b)). rewrite VF_neg_corr. rewrite VF_add_zero.
    trivial. apply VF_comm.
  Qed.

  Lemma VF_add_neg3 :
    forall N, forall a b : VF N,
    VF_add b (VF_add a (VF_neg b))  = a.
  Proof.
    intros. rewrite VF_comm. apply VF_add_neg2.
  Qed.

  Lemma VF_neg_eq : forall N (a : VF N) e,
    VF_scale a (Finv e) = VF_neg (VF_scale a e).
  Proof.
    intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. cbn in *. 
    assert (forall a b : F, a * (Finv b) = Finv(a*b)). intros. ring; auto.
    apply H.
  Qed.

  Lemma VF_neg_scale : forall N (a : VF N) b,
    VF_scale (VF_neg a) b = VF_neg (VF_scale a b).
  Proof.
    intros. apply Veq_nth. intros. do 4 rewrite Vnth_map. ring; auto.
  Qed.

  Lemma VF_neg_mul : forall N (a : VF N) (b : VF N),
    VF_neg (VF_mult a b) = VF_mult (VF_neg a) b.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
    rewrite Vnth_map. ring; auto.
  Qed.

  Lemma VF_neg_sum : forall N (a : VF N),
    - VF_sum a = VF_sum (VF_neg a).
  Proof.
    intros. induction N. rewrite (Vector_0_is_nil a). cbn. ring; auto.
    rewrite (VSn_eq a). unfold VF_sum. rewrite Vfold_left_Vcons_Fadd.
    unfold VF_neg. rewrite Vcons_map. rewrite Vfold_left_Vcons_Fadd.
    unfold VF_sum in IHN. unfold VF_neg in IHN. rewrite <- IHN. ring; auto.
  Qed.

  Lemma Vnth_Vfold_left_cons_Fadd :
    forall (i n n' : nat)(v : vector (VF n) n')(h : (VF n))(ip : Nat.lt i n),
    Vnth
    (Vfold_left (VF_add (n:=n))
       (VF_add (VF_zero n) h) v) ip =
    Vnth
      (Vfold_left (VF_add (n:=n))
       (VF_zero n) v) ip + 
    Vnth h ip.
  Proof.
    intros. induction v. cbn. apply Vnth_map2. cbn.
    rewrite <- Vfold_VFadd_const. rewrite Vnth_map2.
    rewrite IHv. rewrite <- Vfold_VFadd_const. 
    rewrite Vnth_map2. destruct module_ring. 
    do 2 rewrite <- Radd_assoc.
    assert (forall a b c d, a=b -> c=d -> a + c = b + d).
    intros. rewrite H. rewrite H0. trivial. apply H.
    trivial. apply Radd_comm.
  Qed.

  Lemma Vfold_left_VF_add :
    forall (i n n' : nat)(v : vector (VF n) n')(ip : Nat.lt i n),
    Vnth (Vfold_left (VF_add (n:=n)) (VF_zero n) v) ip
      = Vfold_left Fadd Fzero 
      (Vmap (fun v => Vnth v ip) v).
  Proof.
    intros. 
    intros. induction v. cbn. rewrite Vnth_const. trivial.
    (* part 2 *)
    cbn. rewrite <- Vfold_Fadd_const. rewrite <-  IHv. 
    apply Vnth_Vfold_left_cons_Fadd.
  Qed.

  Lemma Vnth_Vfold_left_cons_Fmul :
    forall (i n n' : nat)(v : vector (VF n) n')(h : (VF n))(ip : Nat.lt i n),
    Vnth
    (Vfold_left (VF_mult (n:=n))
       (VF_mult (VF_one n) h) v) ip =
    Vnth
      (Vfold_left (VF_mult (n:=n))
       (VF_one n) v) ip *
    Vnth h ip.
  Proof.
    intros. induction v. cbn. apply Vnth_map2. cbn.
    rewrite <- Vfold_VFmul_const. rewrite Vnth_map2.
    rewrite IHv. rewrite <- Vfold_VFmul_const. 
    rewrite Vnth_map2. destruct module_ring. 
    do 2 rewrite <- Rmul_assoc. apply f_equal2; trivial.
  Qed.

  Lemma Vfold_left_VF_mult :
    forall (i n n' : nat)(v : vector (VF n) n')(ip : Nat.lt i n),
    Vnth (Vfold_left (VF_mult (n:=n)) (VF_one n) v) ip
      = Vfold_left Fmul Fone
      (Vmap (fun v => Vnth v ip) v).
  Proof.
    intros. 
    intros. induction v. cbn. rewrite Vnth_const. trivial.
    (* part 2 *)
    cbn. rewrite <- Vfold_Fmul_const. rewrite <-  IHv. 
    apply Vnth_Vfold_left_cons_Fmul.
  Qed.

  Lemma Vfold_left_Fadd_eq :
    forall (n : nat)(v : VF n),
    Vfold_left_rev Fadd 0 v = Vfold_left Fadd 0 v.
  Proof.
   intros. induction v. cbn. trivial.
   cbn. rewrite <- Vfold_Fadd_const.
   rewrite IHv. trivial.
  Qed. 

  Lemma InProd_Sum :
    forall (N: nat)(c d : VF N),
    VF_inProd c d = VF_sum (Vmap2 Fmul c d).
  Proof.
    intros. unfold VF_inProd, FMatrix.VA.dot_product,
    FSemiRingT.Amult, VF_sum, FSemiRingT.Aplus,
    FSemiRingT.A0. rewrite Vfold_left_Fadd_eq. trivial.
  Qed.

  Lemma VF_inProd_VF_one :
    forall (N : nat)(a : VF N),
    VF_inProd a (VF_one N) = VF_sum a.
  Proof.
    intros. rewrite InProd_Sum. apply f_equal. apply Veq_nth. intros.
    rewrite Vnth_map2. rewrite Vnth_const. ring; auto.
  Qed.

  Lemma MF_CVmult_breakdown :
    forall (N : nat)(A : MF N)(B : VF N),
    MF_CVmult A B = Vfold_left (VF_add (n:=N)) (VF_zero N) 
     (Vbuild (fun j jp => (VF_scale (MF_col A jp)  (Vnth B jp)))).
  Proof.
    intros. unfold MF_CVmult. unfold FMatrix.mat_vec_prod. 
    apply Veq_nth. intros. unfold VF_scale. rewrite Vfold_left_VF_add.
    rewrite FMatrix.Vnth_col_mat. rewrite FMatrix.mat_mult_spec.
    rewrite FMatrix.get_col_col_mat. unfold FMatrix.VA.dot_product.
    rewrite Vfold_left_Fadd_eq. apply Vfold_left_eq. apply Veq_nth.
    intros.  rewrite Vnth_map2. rewrite Vnth_map. rewrite Vbuild_nth.
    rewrite Vnth_map. rewrite FMatrix.get_elem_swap. trivial.
  Qed.
  
  Lemma VF_sum_add : forall (N : nat)(a b : VF N),
    Fadd (VF_sum a) (VF_sum b) = VF_sum (Vmap2 Fadd a b).
  Proof.
    intros. induction N. rewrite (Vector_0_is_nil a). 
    rewrite (Vector_0_is_nil b).  cbn. ring; auto.
    do 3 rewrite VF_sum_induction. do 3 rewrite Vhead_nth.
    rewrite Vnth_map2. rewrite <- Vtail_map2. rewrite <- IHN.
    ring_simplify. trivial.
  Qed.

  Lemma VF_prod_mult : forall (N : nat)(a b : VF N),
    Fmul (VF_prod a) (VF_prod b) = VF_prod (Vmap2 Fmul a b).
  Proof.
    intros. induction N. rewrite (Vector_0_is_nil a). 
    rewrite (Vector_0_is_nil b).  cbn. ring; auto.
    do 3 rewrite VF_prod_induction. do 3 rewrite Vhead_nth.
    rewrite Vnth_map2. rewrite <- Vtail_map2. rewrite <- IHN.
    ring_simplify. trivial.
  Qed.

  Lemma VF_sum_zero : forall (N : nat)(a : VF N),
    a = VF_zero N -> 0 = VF_sum a.
  Proof.
    intros. subst. induction N. cbn. trivial. cbn. 
    destruct module_ring. rewrite Radd_0_l. apply IHN.
  Qed.

  Lemma VF_sum_scale : forall (N : nat)(A : VF N)(a : F),
    VF_sum A * a = VF_sum (VF_scale A a).
  Proof.
    intros. induction N. rewrite (Vector_0_is_nil A). cbn. ring; auto.
    rewrite (VSn_eq A). simpl. unfold VF_sum. do 2 rewrite Vfold_left_Vcons_Fadd.
    destruct module_ring. destruct module_ring.
    rewrite Rdistr_l. rewrite IHN. trivial.  
  Qed.

  Lemma VF_scale_add : forall (n : nat)(a : F)(b c : VF n),
    VF_add (VF_scale b a) (VF_scale c a) = VF_scale (VF_add b c) a.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_map.
    rewrite Vnth_map2. unfold FSemiRingT.Aplus. destruct module_ring.
    symmetry. apply Rdistr_l.
  Qed.

  Lemma VF_scale_VF_add : forall (n m : nat)(a : F)(b : vector (VF n) m),
    VF_scale (Vfold_left (VF_add (n:=n)) (VF_zero n) b) a =
    Vfold_left (VF_add (n:=n)) (VF_zero n) (Vmap (fun x => VF_scale x a) b).
  Proof.
    intros. induction m. rewrite (Vector_0_is_nil b). cbn. apply Veq_nth.
    intros. rewrite Vnth_map. rewrite Vnth_const. ring; auto.
    (* main  *)
    rewrite (VSn_eq (Vmap ((VF_scale (n:=n))^~ a) b)).  rewrite Vfold_left_Vcons_VFadd.
    rewrite <-  Vmap_tail. rewrite <- IHm. rewrite Vhead_map.
    rewrite VF_scale_add. rewrite <- Vfold_left_Vcons_VFadd. rewrite <- VSn_eq.
    trivial. 
  Qed. 

  Lemma MF_CVmult_MF_CVmult_test
     : forall (N : nat)(B U' : MF N)(rStar : VF N),
    MF_CVmult B (MF_CVmult U' rStar) = MF_CVmult (MF_mult B U') rStar.
  Proof.
    intros. unfold MF_CVmult. unfold FMatrix.mat_vec_prod.
    rewrite FMatrix.vec_to_col_mat_idem. 
    assert(forall( A C : FMatrix.col_mat N), A = C -> FMatrix.col_mat_to_vec A =
    FMatrix.col_mat_to_vec C). intros.  rewrite H. trivial.
    apply H. symmetry. apply FMatrix.mat_eq. intros. unfold MF_mult.
    rewrite <- FMatrix.mat_mult_assoc. trivial.
  Qed.

  Lemma MF_VCmult_MF_VCmult_test
     : forall (N : nat)(B U' : MF N)(rStar : VF N),
    MF_VCmult (MF_VCmult rStar U') B = MF_VCmult rStar (MF_mult U' B).
  Proof.
    intros. unfold MF_VCmult. rewrite FMatrix.vec_to_row_mat_idem. apply f_equal. 
    apply FMatrix.mat_eq. intros. unfold MF_mult.
    rewrite <- FMatrix.mat_mult_assoc. trivial.
  Qed.

  Lemma VF_scale_mult : forall (n : nat)(a : F)(b c : VF  n),
    VF_scale (VF_mult b c) a =  VF_mult (VF_scale b a) c.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
    rewrite Vnth_map. ring; auto.  
  Qed.

  Lemma invEq : forall (n : nat)(X Y Y' : MF n),
  MF_mult X Y = MF_id n ->
  MF_mult Y' X = MF_id n ->
  Y = Y'.
  Proof. 
    intros. rewrite <- MF_one. rewrite <- H. rewrite <- MF_assoc.
    rewrite H0. rewrite <- Id_comm. rewrite MF_one. trivial.
  Qed.

   Lemma Vfold_left_add :
    forall (n nM : nat)(messages : vector (VF nM) (1+n)),
    (Vfold_left_rev (VF_add (n:=nM))
       (VF_zero (nM)) messages) = VF_add (Vfold_left_rev (VF_add (n:=nM))
       (VF_zero (nM)) (Vtail messages)) (Vhead messages).
  Proof.
    intros. do 2 rewrite Vfold_left_VFadd_eq. induction n.
    rewrite (VSn_eq messages). rewrite (Vector_0_is_nil (Vtail messages)). 
    cbn. trivial. (* part 1 complete yay *)
     rewrite (VSn_eq messages). cbn.
    rewrite <- Vfold_VFadd_const. rewrite IHn. trivial.
  Qed.

  Lemma VF_prod_1  :
    forall (v : F),
      VF_prod [v] = v.
  Proof.
    intros. cbn. ring; auto.
  Qed.

  Lemma VF_prod_1_head  :
    forall (v : VF 1),
      VF_prod v = Vhead v.
  Proof.
    intros. rewrite (VSn_eq v).
    rewrite (Vector_0_is_nil (Vtail v)).
    rewrite VF_prod_1. symmetry. 
    rewrite Vhead_nth. cbn. trivial.
  Qed.

  Lemma VF_prod_2_head  :
    forall (v : VF 2),
      VF_prod v = Vhead v * Vhead (Vtail v).
  Proof.
    intros. rewrite (VSn_eq v). rewrite (VSn_eq (Vtail v)).
    rewrite (Vector_0_is_nil (Vtail (Vtail v))). cbn.
    ring; auto.
  Qed.

  Lemma VF_prod_1_head_gen  :
    forall n (v : VF (S n)),
      n = 0%nat ->
      VF_prod v = Vhead v.
  Proof.
    intros. subst. apply VF_prod_1_head.
  Qed.

  Lemma Vmap_prod_1 :
    forall n (v : vector (VF 1) n),
    Vmap (VF_prod (n:=1)) v = 
      Vhead (FMatrix.mat_transpose v).
  Proof.
    intros. apply Veq_nth. intros. 
    rewrite Vnth_map. rewrite Vhead_nth.
    pose FMatrix.mat_transpose_col_row.
    unfold FMatrix.get_row in e. rewrite e.
    rewrite <- FMatrix.get_elem_swap.
    unfold FMatrix.get_row. 
    rewrite VF_prod_1_head. rewrite Vhead_nth.
    trivial.
  Qed.

    Lemma VF_sum_1  :
    forall (v : F),
      VF_sum [v] = v.
  Proof.
    intros. cbn. ring; auto.
  Qed.

  Lemma VF_sum_1_head  :
    forall (v : VF 1),
      VF_sum v = Vhead v.
  Proof.
    intros. rewrite (VSn_eq v).
    rewrite (Vector_0_is_nil (Vtail v)).
    rewrite VF_sum_1. symmetry. 
    rewrite Vhead_nth. cbn. trivial.
  Qed.

  Lemma VF_sum_vadd_1_head  :
    forall (n : nat)(v : vector (VF n) 1),
      Vfold_left (VF_add (n:=n)) (VF_zero n) v = Vhead v.
  Proof.
    intros. rewrite (VSn_eq v).
    rewrite (Vector_0_is_nil (Vtail v)).
    cbn. rewrite VF_comm. rewrite VF_add_zero. trivial. 
  Qed.

  Lemma VF_prod_vmult_1_head  :
    forall (n : nat)(v : vector (VF n) 1),
      Vfold_left (VF_mult (n:=n)) (VF_one n) v = Vhead v.
  Proof.
    intros. rewrite (VSn_eq v).
    rewrite (Vector_0_is_nil (Vtail v)).
    cbn. rewrite VF_comm_mult. rewrite VF_mult_one. trivial. 
  Qed.

  Lemma VF_Fadd_dist : forall n m (a: VF n)(B : vector (VF n) m),
    VF_mult a (Vfold_left (VF_add (n:=n)) (VF_zero n) B) =
      Vfold_left (VF_add (n:=n)) (VF_zero n) (Vmap (VF_mult a) B).
  Proof.
    intros. induction m. rewrite (Vector_0_is_nil B). cbn.
    apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_const. ring; auto.
    rewrite (VSn_eq B). rewrite Vcons_map. do 2 rewrite Vfold_left_Vcons_VFadd.
    rewrite <- IHm. rewrite VF_comm_mult. rewrite VF_dist. apply f_equal2.
    apply VF_comm_mult. apply VF_comm_mult.
  Qed.

  Lemma VF_sum_sum : forall n m (B : vector (VF n) m),
    VF_sum (Vfold_left (VF_add (n:=n)) (VF_zero n) B) =
    VF_sum (Vmap (VF_sum (n:=n)) B).
  Proof.
    intros. induction m. rewrite (Vector_0_is_nil B). cbn. pose VF_sum_VF_zero.
    unfold VF_sum in e. apply e. unfold VF_sum in *. rewrite (VSn_eq B). 
    rewrite Vcons_map. rewrite Vfold_left_Vcons_Fadd. rewrite <- IHm. 
    rewrite Vfold_left_Vcons_VFadd. rewrite VF_sum_add. unfold VF_sum. trivial.
  Qed.

  Lemma VF_prod_one : forall n,
    VF_prod (VF_one n) = 1.
  Proof.
    intros. induction n. cbn. trivial. cbn. replace (1*1) with 1. apply IHn.
    ring; auto.
  Qed.

  Lemma VF_prod_prod : forall n m (B : vector (VF n) m),
    VF_prod (Vfold_left (VF_mult (n:=n)) (VF_one n) B) =
    VF_prod (Vmap (VF_prod (n:=n)) B).
  Proof.
    intros. induction m. rewrite (Vector_0_is_nil B). cbn. apply VF_prod_one.
    unfold VF_prod in *. rewrite (VSn_eq B). 
    rewrite Vcons_map. rewrite Vfold_left_Vcons_Fmul. rewrite <- IHm. 
    rewrite Vfold_left_Vcons_VFmult. rewrite VF_prod_mult. trivial.
  Qed.

  Lemma Vmap_sum_1 :
    forall n (v : vector (VF 1) n),
    Vmap (VF_sum (n:=1)) v = 
      Vhead (FMatrix.mat_transpose v).
  Proof.
    intros. apply Veq_nth. intros. 
    rewrite Vnth_map. rewrite Vhead_nth.
    pose FMatrix.mat_transpose_col_row.
    unfold FMatrix.get_row in e. rewrite e.
    rewrite <- FMatrix.get_elem_swap.
    unfold FMatrix.get_row. 
    rewrite VF_sum_1_head. rewrite Vhead_nth.
    trivial.
  Qed.

  Lemma Vmap2_VF_add_assoc : forall n j (a b c : vector (VF n) j),
    Vmap2 (VF_add (n:=n)) (Vmap2 (VF_add (n:=n)) a b) c =
    Vmap2 (VF_add (n:=n)) a (Vmap2 (VF_add (n:=n)) b c).
  Proof.
    intros. apply Veq_nth. intros. do 4 rewrite Vnth_map2. apply VF_add_ass.
  Qed.

  Lemma Vmap2_VF_add_comm : forall n j (a b : vector (VF n) j),
    Vmap2 (VF_add (n:=n)) a b = Vmap2 (VF_add (n:=n)) b a.
  Proof.
    intros. apply Veq_nth. intros. do 2 rewrite Vnth_map2. apply VF_comm.
  Qed.
  
  Lemma Vfold_VFadd_vector_const :
    forall n j i (c : vector (vector (VF n) j) i)
      (a b : vector (VF n) j),
    Vfold_left (fun x y : vector (VF n) j =>
   Vmap2 (VF_add (n:=n)) x y)
   (Vmap2 (VF_add (n:=n)) a b) c =
  Vmap2 (VF_add (n:=n)) (Vfold_left
     (fun x : vector (VF n) j =>
      [eta Vmap2 (VF_add (n:=n)) x]) a c) b.
  Proof.
    induction c. simpl. trivial. simpl. intros. 
    assert (Vmap2 (VF_add (n:=n))
     (Vmap2 (VF_add (n:=n)) a b) h = Vmap2 (VF_add (n:=n))
     (Vmap2 (VF_add (n:=n)) a h) b). rewrite (Vmap2_VF_add_comm a b). 
    rewrite Vmap2_VF_add_assoc. rewrite Vmap2_VF_add_comm. trivial. 
    rewrite H. rewrite IHc. trivial.
  Qed.

  Lemma mat_mult_assoc_gen :
    forall n n' n'' n''' (m : FMatrix.matrix n n')
    (m' : FMatrix.matrix n' n'')(m'' : FMatrix.matrix n'' n'''),
      FMatrix.mat_mult (FMatrix.mat_mult m m') m'' =
      FMatrix.mat_mult m (FMatrix.mat_mult m' m'').
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. 
    pose FMatrix.mat_mult_assoc. unfold FMatrix.mat_eqA in m0.
    unfold FMatrix.get_elem, FMatrix.get_row in m0. rewrite m0.
    trivial.
  Qed.

  Lemma mat_mult_id_l :
     forall n n' (m : FMatrix.matrix n n'),
     FMatrix.mat_mult (FMatrix.id_matrix n) m =
     m.
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. 
    unfold FMatrix.id_matrix. rewrite FMatrix.mat_mult_elem.
    unfold FMatrix.get_row. rewrite Vbuild_nth.
    rewrite (FMatrix.VA.dot_product_id ip).
    rewrite FMatrix.get_elem_swap. trivial.
  Qed.

  Lemma mat_mult_id_r :
     forall n n' (m : FMatrix.matrix n n'),
     FMatrix.mat_mult m (FMatrix.id_matrix n') =
     m.
  Proof.
    intros. symmetry. rewrite <- FMatrix.mat_transpose_idem. 
    rewrite transpose_move_gen. pose Id_transpose. unfold MF_id in *.
    rewrite <- e. rewrite mat_mult_id_l. rewrite FMatrix.mat_transpose_idem.
    trivial.
  Qed.

  Lemma scale_mult : forall n n' (a : VF n')(b : vector (VF n) n'),
    Vmap2 (VF_scale (n:=n)) b a = 
      FMatrix.mat_transpose (Vmap (VF_mult a) (FMatrix.mat_transpose b)).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. rewrite FMatrix.mat_build_nth.
    rewrite Vnth_map2. rewrite Vnth_map. unfold FMatrix.get_elem. unfold FMatrix.get_row.
    rewrite Vnth_map. rewrite Vnth_map2. rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_elem. unfold FMatrix.get_row. destruct module_ring.
    apply Rmul_comm.
  Qed.



  Lemma Fmatrix_mult_vnth : forall n n' n'' (a : vector (VF n) n')
      (b : vector (VF n'') n) i (ip : i < n') ,
    Vnth (FMatrix.mat_mult a b) ip = Vhead (FMatrix.mat_mult [(Vnth a ip)] b).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vhead_nth. rewrite FMatrix.mat_build_nth.
    rewrite FMatrix.mat_build_nth. simpl. unfold FMatrix.get_row. trivial.
  Qed.

  Lemma mat_mult_rev : forall n n' n'' (a : vector (VF n) n')(b : vector (VF n'') n),
  FMatrix.mat_mult (rev a) b = rev (FMatrix.mat_mult a b).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros.
    rewrite Vbuild_nth. do 2 rewrite FMatrix.mat_mult_elem. unfold FMatrix.get_row.
    rewrite Vbuild_nth. trivial.
  Qed.

  Lemma mat_mult_rev2 : forall n n' n'' (a : vector (VF n) n')(b : vector (VF n'') n),
  FMatrix.mat_mult a (Vmap (fun x => rev x) b)  = Vmap (fun x => rev x)
     (FMatrix.mat_mult a b).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. rewrite Vnth_map.
    rewrite Vbuild_nth. do 2 rewrite FMatrix.mat_mult_elem. apply f_equal; auto.
   unfold FMatrix.get_row. apply Veq_nth. intros. do 3 rewrite Vnth_map.
    rewrite Vbuild_nth. trivial. 
  Qed.

  Lemma VF_add_transpose : forall n n' (a : vector (VF n) n'),
     Vfold_left (VF_add (n:=n')) (VF_zero n') (FMatrix.mat_transpose a) =
     Vmap (VF_sum (n:=n)) a.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. rewrite Vfold_left_VF_add.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_map. rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_elem. trivial.
  Qed.

  Lemma Vhead_mat_mult : forall n n' n'' (a : vector (VF n) (S n'))(b: vector (VF n'') n),
    [Vhead (FMatrix.mat_mult a b)] = FMatrix.mat_mult [Vhead a] b.
  Proof.
    intros. assert (forall j (a : VF j)(b : vector (VF j) 1),
       a = Vhead b -> [a] = b). intros. rewrite H. apply Veq_nth. intros.
    assert (i = 0%nat). lia. subst. simpl. rewrite Vhead_nth. apply Vnth_eq.
    trivial. apply H. do 2 rewrite Vhead_nth. apply Veq_nth. intros. 
    do 2 rewrite FMatrix.mat_build_nth. cbn. rewrite Vhead_nth. unfold FMatrix.get_row. trivial.
  Qed.

  Lemma rev_col : forall n n' (a : vector (VF n) (S n')) i (ip : i < n),
    FMatrix.get_col (rev a) ip = rev (FMatrix.get_col a ip).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth. do 2 rewrite Vnth_map.
    rewrite Vbuild_nth. trivial.
  Qed.
 
  Lemma VF_mult_zero : forall n (a : VF n),
    VF_mult (VF_zero n) a = VF_zero n.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_const.
    ring; auto.
  Qed.

  Lemma VF_sum_dist : forall n n' n'' (a : vector (VF n) n')(b : vector (VF n) n''),
  Vfold_left (VF_add (n:=n)) (VF_zero n)
  (Vmap [eta Vfold_left (VF_add (n:=n)) (VF_zero n)]
     (Vbuild  (fun (i : nat) (ip : i < n') =>
  Vbuild (fun (j : nat) (jp : j < n'') => VF_mult (Vnth a ip) (Vnth b jp))))) =
  VF_mult (Vfold_left (VF_add (n:=n)) (VF_zero n) a)
  (Vfold_left (VF_add (n:=n)) (VF_zero n) b).
  Proof.
    intros. induction n'. rewrite (Vector_0_is_nil a). simpl.
    rewrite VF_mult_zero. trivial.
    (* Inductive case *)
    intros. rewrite (VSn_eq a). rewrite Vfold_left_Vcons_VFadd. rewrite VF_dist.
    rewrite <- IHn'. rewrite <- Vfold_left_Vcons_VFadd. apply f_equal.
    rewrite VF_Fadd_dist. rewrite <- Vcons_map. apply Veq_nth. intros.
    do 2 rewrite Vnth_map. apply f_equal. rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    do 2 rewrite Vbuild_nth. rewrite Vnth_cons. destruct (lt_ge_dec 0 i). apply Veq_nth.
    intros. do 2 rewrite Vbuild_nth. apply f_equal2; auto. apply Vnth_eq. trivial.
    assert (False). lia. contradiction. rewrite Vbuild_nth. apply Veq_nth. intros.
    rewrite Vbuild_nth. rewrite Vnth_map. rewrite <- VSn_eq. rewrite Vhead_nth.
    apply f_equal2; auto. apply Vnth_eq. lia.
  Qed. 

  Lemma  Vfold_left_vcons_cancel : forall n n' (a : VF n)(b : vector (VF n) n')
    (c : VF (S n')),
  Vhead c = 1 -> VF_sub 
  (Vfold_left (VF_add (n:=n)) (VF_zero n)
     (Vmap2 (VF_scale (n:=n)) (Vcons a b) c))
  (Vfold_left (VF_add (n:=n)) (VF_zero n)
     (Vmap2 (VF_scale (n:=n)) b (Vtail c))) = a.
  Proof.
    intros. rewrite (VSn_eq c). rewrite Vcons_map2. rewrite Vfold_left_Vcons_VFadd. 
    rewrite <- VSn_eq. unfold VF_sub. assert (forall n (a b c :  VF n), VF_add (VF_add a b) c =
    VF_add b (VF_add a c)). intros. rewrite <- VF_add_ass. apply f_equal2; auto.
    apply VF_comm. rewrite H0. rewrite VF_neg_corr. rewrite VF_add_zero.
    rewrite H. rewrite VF_scale_1. trivial.
  Qed.

  Lemma  Vfold_left_vadd_cancel : forall n n' (a : VF n)(b : vector (VF n) n')
    (c : VF (S n')),
  Vhead c = 1 -> VF_sub 
  (Vfold_left (VF_add (n:=n)) (VF_zero n)
     (Vmap2 (VF_scale (n:=n)) (Vadd b a) (rev c)))
  (Vfold_left (VF_add (n:=n)) (VF_zero n)
     (Vmap2 (VF_scale (n:=n)) b (rev (Vtail c)))) = a.
  Proof.
    intros. pose VF_comm. pose VF_add_ass. rewrite Vfold_left_eq_rev; auto.
    rewrite rev_vmap2. rewrite <- Vcons_rev. rewrite rev_rev. remember (Vfold_left (VF_add (n:=n)) (VF_zero n)
     (Vmap2 (VF_scale (n:=n)) (Vcons a (rev b)) c)) as d.
    rewrite Vfold_left_eq_rev; auto. rewrite rev_vmap2. rewrite rev_rev.
    rewrite Heqd. apply Vfold_left_vcons_cancel; auto.
  Qed.

  Lemma VF_sum_vcons_cancel : forall n (a : F)(b : VF n)(c : VF (S n)),
    Vhead c = 1 -> 
    VF_sum (VF_mult c (Vcons a b)) -
    VF_sum (VF_mult (Vtail c) b) = a.
  Proof.
    intros. rewrite (VSn_eq c). unfold VF_mult. rewrite Vcons_map2.
    rewrite VF_sum_vcons. rewrite <- VSn_eq. rewrite H. ring; auto.
  Qed.

  Lemma VF_sum_vcons_cancel_gen : forall n (a c1 : VF (S n))(b c2: VF n),
    Vhead c1 = 1 ->
    Vtail c1 = c2 ->
    Vtail a = b ->
    Vfold_left Fadd 0 (Vmap2 Fmul a c1) - Vfold_left Fadd 0 (Vmap2 Fmul b c2) = 
      (Vhead a). 
  Proof.
    intros. rewrite (VSn_eq a). pose VF_sum_vcons_cancel. pose VF_comm_mult.
    unfold VF_sum, VF_mult in *. rewrite H1. rewrite e0. rewrite (e0 n b).
    rewrite <- H0. rewrite e; auto. 
  Qed.

  Lemma VF_sum_vadd_cancel : forall n (a : F)(b : VF n)(c : VF (S n)),
    Vhead c = 1 -> 
    VF_sum (VF_mult (rev c) (Vadd b a)) -
      VF_sum (VF_mult (rev (Vtail c)) b) = a.
  Proof.
    intros. unfold VF_sum. rewrite Vfold_left_eq_rev; intros. ring; auto.
    ring; auto. rewrite rev_vmap2. rewrite <- Vcons_rev. rewrite rev_rev.
    remember (Vfold_left Fadd 0 (Vmap2 Fmul c (Vcons a (rev b)))) as d.
    rewrite Vfold_left_eq_rev; intros. ring; auto. ring; auto.
    rewrite rev_vmap2. rewrite rev_rev. rewrite Heqd. apply VF_sum_vcons_cancel; auto.
  Qed.

  Lemma Vfold_left_vsub_cancel : forall n n' (a : VF n)(b : vector (VF n) n')(c : VF (S n')),
    Vhead c = 1 ->    
    Vfold_left (VF_add (n:=n)) (VF_zero n) (Vmap2 (VF_scale (n:=n)) 
      (Vcons  (VF_sub a (Vfold_left (VF_add (n:=n)) (VF_zero n)
      (Vmap2 (VF_scale (n:=n)) b (Vtail c)))) b) 
    c) = a.
  Proof.
    intros. rewrite (VSn_eq c). rewrite Vcons_map2. rewrite <- VSn_eq. rewrite H.
    rewrite VF_scale_1. rewrite Vfold_left_Vcons_VFadd. rewrite VF_sub_corr. rewrite VF_comm.
    rewrite VF_add_ass. assert (forall c, VF_add (VF_neg c) c  = VF_zero n). intros.
    rewrite VF_comm. apply VF_neg_corr. rewrite H0. apply VF_add_zero. 
  Qed.

  Lemma VF_sum_vsub_cancel : forall n' (a : F)(b : VF n')(c : VF (S n')),
     Vhead c = 1 ->    
     VF_sum (VF_mult c
      (Vcons (a - (VF_sum (VF_mult (Vtail c) b))) b)) = a.
  Proof.
    intros. rewrite (VSn_eq c). unfold VF_mult. rewrite Vcons_map2. rewrite <- VSn_eq. rewrite H.
    assert (forall d, 1 * d = d). intros. ring; auto. rewrite H0.
    rewrite VF_sum_vcons. ring; auto.
  Qed. 

  Lemma VF_sum_vsub_cancel_gen : forall n' (a : F)(b b' : VF n')(c : VF (S n')),
     Vhead c = 1 ->    
     b = b' ->
     VF_sum (VF_mult c
      (Vcons (a - (VF_sum (VF_mult (Vtail c) b))) b')) = a.
  Proof.
    intros. rewrite H0. rewrite (VSn_eq c). unfold VF_mult. rewrite Vcons_map2. 
    rewrite <- VSn_eq. rewrite H. assert (forall d, 1 * d = d). intros. ring; auto.
    rewrite H1. rewrite VF_sum_vcons. ring; auto.
  Qed. 

    
  Lemma Vfold_left_vsub_add_cancel : forall n n' (a : VF n)(b : vector (VF n) n')(c : VF (S n')),
    Vhead c = 1 ->    
    Vfold_left (VF_add (n:=n)) (VF_zero n) (Vmap2 (VF_scale (n:=n)) 
      (Vadd b (VF_sub a (Vfold_left (VF_add (n:=n)) (VF_zero n)
      (Vmap2 (VF_scale (n:=n)) b (rev (Vtail c)))))) 
    (rev c)) = a.
  Proof.
    intros. pose VF_comm. pose VF_add_ass. rewrite Vfold_left_eq_rev; auto.
    rewrite rev_vmap2.  rewrite <- Vcons_rev.  rewrite rev_rev. 
    remember (Vfold_left (VF_add (n:=n)) (VF_zero n)) as d.
    rewrite Vfold_left_eq_rev; auto. rewrite rev_vmap2. rewrite rev_rev. 
    rewrite  Heqd. apply Vfold_left_vsub_cancel; auto.
  Qed.

  Lemma VF_sum_vsub_add_cancel : forall n' (a : F)(b : VF n')(c : VF (S n')),
     Vhead c = 1 ->    
     VF_sum (VF_mult (rev c)
      (Vadd b (a - (VF_sum (VF_mult (rev (Vtail c)) b))))) = a.
  Proof.
    intros. unfold VF_sum. rewrite Vfold_left_eq_rev; intros. ring; auto.
    ring; auto. rewrite rev_vmap2. rewrite <- Vcons_rev. rewrite rev_rev.
    remember (Vfold_left Fadd 0) as d.
    rewrite Vfold_left_eq_rev; intros. ring; auto. ring; auto.
    rewrite rev_vmap2. rewrite rev_rev. rewrite Heqd. apply VF_sum_vsub_cancel; auto.
  Qed. 
    
  Lemma VF_mat_cancel : forall n n' (a : VF (S n))(b : VF n')(c : vector (VF n') n),
    Vhead a = 1 ->
      VF_add (Vhead (FMatrix.mat_mult [a] (Vcons b c)))
    (VF_neg (Vhead (FMatrix.mat_mult [Vtail (a)] c))) = b.
  Proof.
    intros. apply Veq_nth. intros. 
    rewrite Vnth_map2. rewrite Vnth_map. do 2 rewrite MF_getCol_prod_gen.
    unfold FSemiRingT.Aplus. do 2 rewrite InProd_Sum. pose VF_comm_mult.
    unfold VF_mult in e. rewrite e. rewrite (e n (Vtail a)).
   rewrite VF_sum_vcons_cancel_gen; auto.
  Qed.

  Lemma VF_mat_cancel_rev : forall n n' (a : VF (S n))(b : VF n')(c : vector (VF n') n),
    Vhead a = 1 ->
    Vhead (FMatrix.mat_mult [a] (Vcons (VF_sub b
     (Vhead (FMatrix.mat_mult [Vtail (a)] c))) c)) = b.
  Proof.
    intros. apply Veq_nth. intros. rewrite MF_getCol_prod_gen.
    assert (FMatrix.get_col (Vcons (VF_sub b (Vhead (FMatrix.mat_mult [Vtail a] c))) c) ip
    = Vcons (Vnth b ip - VF_inProd (Vtail a) (FMatrix.get_col c ip)) (FMatrix.get_col c ip)).
    apply Veq_nth. intros. rewrite Vnth_map. do 2  rewrite Vnth_cons. 
    destruct (lt_ge_dec 0 i0). rewrite Vnth_map. trivial. unfold VF_sub. 
    rewrite Vnth_map2. rewrite Vnth_map. rewrite MF_getCol_prod_gen. trivial.
    rewrite H0. do 2 rewrite InProd_Sum. rewrite VF_sum_vsub_cancel; auto.
  Qed.

  Lemma VF_sum_id : forall n i (ip : i < n),
    Vfold_left Fadd Fzero (FMatrix.VA.id_vec ip) = 1.
  Proof.
    induction n. lia. destruct i; intros. rewrite Vfold_left_Vcons_Fadd.
    pose VF_sum_VF_zero. unfold VF_sum in e. rewrite e. unfold FSemiRingT.A1.
    ring; auto. unfold FMatrix.VA.id_vec. rewrite Vreplace_tail. 
    rewrite Vfold_left_Vcons_Fadd. unfold FMatrix.VA.zero_vec. rewrite Vtail_const.
    rewrite IHn. rewrite Vhead_const. unfold FSemiRingT.A0. ring; auto.
  Qed.

  Lemma permutationSum : forall n (m : MF n),
    MFisPermutation m ->
    Vfold_left (VF_add (n:=n)) (VF_zero (n)) m = VF_one (n).
  Proof.
    intros. unfold MFisPermutation in H. apply andb_true_iff in H.
    destruct H. apply Veq_nth. intros. rewrite Vfold_left_VF_add.
    apply (bVforall_elim_nth ip) in H0. unfold VF_an_id  in H0.
    apply bVexists_eq in H0. elim H0. intros. elim H1. intros.
    (* We know the id *)
    apply VF_beq_true in H2. rewrite Vnth_MF_build in H2. 
     assert (Vmap (fun v : vector F n => Vnth v ip) m =
    Vbuild (fun j : nat => (FMatrix.get_elem m (j:=i))^~ ip)). intros.
    apply Veq_nth. intros. rewrite Vnth_map. rewrite Vbuild_nth. trivial.
    rewrite H3. rewrite H2. rewrite Vbuild_nth. rewrite VF_sum_id.
    rewrite Vnth_const. trivial.
  Qed.

  Lemma MF_CVmult_MF_VCmult_perm : forall n (m : MF n)(a : VF n), 
    MF_CVmult m a = MF_VCmult a (MF_trans m).
  Proof.
    intros. apply Veq_nth. intros. unfold MF_CVmult, MF_VCmult, MF_trans.
    rewrite Vnth_map. do 2 rewrite FMatrix.mat_mult_elem. 
    rewrite FMatrix.get_col_col_mat. rewrite FMatrix.mat_transpose_row_col.
    cbn. apply FMatrix.VA.dot_product_comm.
  Qed. 

  Lemma MF_trans_sub : forall n (m: MF (S n)),
    MF_trans (Vmap [eta Vremove_last (n:=n)] (Vtail m)) =
    Vmap [eta Vtail (n:=n)] (Vremove_last (MF_trans m)).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. rewrite Vnth_map.
    rewrite Vnth_remove_last. rewrite Vnth_tail. do 2 rewrite FMatrix.mat_build_nth. 
    unfold FMatrix.get_elem, FMatrix.get_row. rewrite Vnth_map.
    rewrite Vnth_remove_last. rewrite Vnth_tail. trivial.
  Qed.

   Lemma MF_trans_sub2 : forall n (m: MF (S n)),
    Vmap [eta Vremove_last (n:=n)] (Vtail (MF_trans m)) =
    MF_trans (Vmap [eta Vtail (n:=n)] (Vremove_last m)).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. rewrite Vnth_map.
    rewrite Vnth_remove_last. rewrite Vnth_tail. do 2 rewrite FMatrix.mat_build_nth. 
    unfold FMatrix.get_elem, FMatrix.get_row. rewrite Vnth_map.
    rewrite Vnth_remove_last. rewrite Vnth_tail. trivial.
  Qed.

  Lemma MF_trans_sub4 : forall n n' (m: FMatrix.matrix n (S n')),
    FMatrix.mat_transpose (Vmap [eta Vremove_last (n:=n')] m) = 
    Vremove_last (FMatrix.mat_transpose m).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. rewrite Vnth_remove_last.
    do 2 rewrite FMatrix.mat_build_nth. unfold FMatrix.get_elem, FMatrix.get_row.
    rewrite Vnth_map. rewrite Vnth_remove_last. trivial.
  Qed.

  Lemma MF_perm_inv : forall n (m : MF n),
    MFisPermutation m ->
    MFisPermutation (MF_trans m).
  Proof.
    intros. unfold MFisPermutation in *. rewrite FMatrix.mat_transpose_idem.
    apply andb_true_iff in H. apply andb_true_iff. destruct H. split; trivial.
  Qed.

  Lemma MF_not_perm_inv : forall n (m : MF n),
    MFisPermutation m = false ->
    MFisPermutation (MF_trans m) = false.
  Proof.
    intros. apply not_true_iff_false in H. apply not_true_iff_false.
    unfold not; intros. apply H. rewrite <- (FMatrix.mat_transpose_idem m).
    apply MF_perm_inv. apply H0.
  Qed.

  Lemma Vreplace_pi_id : forall n x x0 (xp : x < n)(xp0 : x0 < n),
    0 <> 1 ->
    FMatrix.VA.id_vec xp = FMatrix.VA.id_vec xp0 -> x = x0.
  Proof.
    intros. destruct (Nat.eq_dec x x0). trivial. apply (Veq_nth4 xp0) in H0. 
    rewrite Vnth_replace in H0. rewrite Vnth_replace_neq in H0. trivial.
    rewrite Vnth_const in H0. assert False. apply H.
    unfold FSemiRingT.A0 in H0. rewrite H0. trivial. contradiction.
  Qed.

  Lemma MF_perm_row_uniq_sub : forall n (m : MF n),
    bVforall (VF_an_id (n:=n)) (FMatrix.mat_transpose m) = true ->
        0 <> 1 ->
    forall  i i0 (ip : i < n)(ip0 : i0 < n) x x0 (xp : x < n)(xp0 : x0 < n),
    i <> i0 ->
    Vnth m ip  = FMatrix.VA.id_vec xp  ->
    Vnth m ip0 = FMatrix.VA.id_vec xp0 ->
    x <> x0.
  Proof.
    intros n m H neq i i0 ip ip0 x x0 xp xp0. intros. unfold not in *. intros. subst. 
    assert (xp = xp0). apply le_unique. rewrite H3 in H1. 
    apply (bVforall_elim_nth xp0) in H.  unfold VF_an_id in H. 
    apply bVexists_eq in H. elim H. intros. elim H4. intros. clear H4. 
    apply VF_beq_true in H5. rewrite Vbuild_nth in H5.
    pose FMatrix.mat_transpose_col_row. unfold FMatrix.get_row in e.
    rewrite e in H5. apply (Veq_nth4 xp0) in H2. apply (Veq_nth4 xp0) in H1.
    assert (FMatrix.get_col m xp0 = FMatrix.VA.id_vec x1). trivial.
    apply (Veq_nth4 ip) in H4. apply (Veq_nth4 ip0) in H5. rewrite Vnth_map in H4.
    rewrite Vnth_map in H5. rewrite H2 in H5. rewrite H1 in H4.
    rewrite Vnth_replace in H5. rewrite Vnth_replace in H4.
    rewrite H5 in H4. destruct (Nat.eq_dec i x).
    + subst. rewrite Vnth_replace in H4. rewrite Vnth_replace_neq in H4. 
    unfold not. intros. apply H0. trivial. rewrite Vnth_const in H4. 
    apply neq. unfold FSemiRingT.A0 in H4.
    rewrite H4. trivial.
    + symmetry in H4. rewrite Vnth_replace_neq in H4. unfold not in *.
    intros. apply n0. rewrite H4. trivial. rewrite Vnth_const in H4.
    rewrite <- H4 in H5. apply neq.
    unfold FSemiRingT.A0 in H5. rewrite <- H5. trivial.
  Qed.

  Lemma MF_perm_row_uniq : forall n (m : MF n),
    MFisPermutation m ->
        0 <> 1 ->
    forall  i i0 (ip : i < n)(ip0 : i0 < n) x x0 (xp : x < n)(xp0 : x0 < n),
    i <> i0 ->
    Vnth m ip  = FMatrix.VA.id_vec xp  ->
    Vnth m ip0 = FMatrix.VA.id_vec xp0 ->
    x <> x0.
  Proof.
    intros.  unfold MFisPermutation in H. apply andb_true_iff in H. destruct H.
    apply (MF_perm_row_uniq_sub m H4 H0 ip ip0 xp xp0); trivial.
  Qed.

  Lemma MF_perm_col_uniq : forall n (m : MF n),
    MFisPermutation m ->
    0 <> 1 ->
    forall  i i0 (ip : i < n)(ip0 : i0 < n) x x0 (xp : x < n)(xp0 : x0 < n),
    i <> i0 ->
    Vnth (MF_trans m) ip  = FMatrix.VA.id_vec xp  ->
    Vnth (MF_trans m) ip0 = FMatrix.VA.id_vec xp0 ->
    x <> x0.
  Proof.
    intros.  unfold MFisPermutation in H. apply andb_true_iff in H. destruct H.
    rewrite <- (FMatrix.mat_transpose_idem m) in H. 
    apply (MF_perm_row_uniq_sub (MF_trans m) H H0 ip ip0 xp xp0); trivial.
  Qed.

  Lemma MF_perm_mix_eq_sub : forall n (m : MF n) i (ip : i< n) x (xp : x < n),
    bVforall (VF_an_id (n:=n)) (FMatrix.mat_transpose m) = true ->
    Vnth m ip  = FMatrix.VA.id_vec xp ->
    Vnth (MF_trans m) xp = FMatrix.VA.id_vec ip.
  Proof.
    intros. destruct TrivialOrNot. apply Veq_nth. intros. apply H1. 
    apply (bVforall_elim_nth xp) in H.  unfold VF_an_id in H. 
    apply bVexists_eq in H. elim H. intros. elim H2. intros. clear H2. 
    apply VF_beq_true in H3. rewrite Vbuild_nth in H3. destruct (Nat.eq_dec x0 i).
    subst. rewrite H3. apply f_equal. apply le_unique.
    apply (Veq_nth4 ip) in H3. rewrite Vnth_replace_neq in H3. trivial.
    rewrite Vnth_const in H3. rewrite FMatrix.mat_build_nth in H3.
    unfold FMatrix.get_elem, FMatrix.get_row in H3. apply (Veq_nth4 xp) in H0.
    rewrite Vnth_replace in H0. rewrite H0 in H3.
    assert False. apply H1. unfold FSemiRingT.A1 in H3. rewrite H3.
    trivial. contradiction.
  Qed.

  Lemma MF_perm_mix_eq : forall n (m : MF n) i (ip : i< n) x (xp : x < n),
    MFisPermutation m ->
    Vnth m ip  = FMatrix.VA.id_vec xp <->
    Vnth (MF_trans m) xp = FMatrix.VA.id_vec ip.
  Proof. 
    intros. apply andb_true_iff in H. destruct H. split; intros. 
    apply MF_perm_mix_eq_sub; trivial. rewrite <- (FMatrix.mat_transpose_idem m). 
    apply MF_perm_mix_eq_sub. rewrite FMatrix.mat_transpose_idem. trivial. trivial.
  Qed.
    
   Lemma MF_perm_row_imp : forall n (m :MF n) j (jp : j < n) x (xp : x < n),
    MFisPermutation m ->
    (forall i (ip : i < n),
    i <> j ->
    Vnth m ip <> FMatrix.VA.id_vec xp) ->
    Vnth m jp = FMatrix.VA.id_vec xp.
  Proof.
    intros. destruct TrivialOrNot. apply Veq_nth. intros. apply H1. 
    assert (MFisPermutation m) as b. trivial.
    case_eq (VF_beq (Vnth m jp) (FMatrix.VA.id_vec xp)).
    intros. apply VF_beq_true in H2. trivial. intros. apply andb_true_iff in H.
    destruct H. apply (bVforall_elim_nth jp) in H.  unfold VF_an_id in H. 
    apply bVexists_eq in H. elim H. intros. elim H4. intros. clear H4. 
    apply VF_beq_true in H5. rewrite Vbuild_nth in H5. assert (x <> x0).
    unfold not. intros. apply VF_beq_false in H2. apply H2.
    rewrite H5. apply Vreplace_pi. auto.  
    (* At this point we know there are know 1s in the xth colomn. *)
    apply (bVforall_elim_nth xp) in H3.  unfold VF_an_id in H3. 
    apply bVexists_eq in H3. elim H3. intros. elim H6. intros. clear H6. 
    apply VF_beq_true in H7. rewrite Vbuild_nth in H7. 
    (* Now apprently there is a one at x3 *)
    apply MF_perm_mix_eq in H7. destruct (Nat.eq_dec x2 j). subst.
    subst. assert (Vnth m jp = Vnth m x3). apply Vnth_eq. trivial.
    rewrite H6 in H5. rewrite H5 in H7. apply Vreplace_pi_id in H7.
    assert False. unfold not in *. apply H4. rewrite H7. trivial. contradiction.
    trivial.
    apply (H0 x2 x3) in n0. contradiction. trivial.
  Qed.
  
  Lemma permTranInv :  forall n (m : MF n),
    MFisPermutation m ->
    MF_mult m (MF_trans m) = MF_id n.
  Proof. 
    intros. apply Veq_nth. intros. apply Veq_nth. intros. unfold MF_id, MF_mult.
    assert (MFisPermutation m). trivial.
    unfold MFisPermutation in H. apply andb_true_iff in H. destruct H.
    apply (bVforall_elim_nth ip) in H. unfold VF_an_id in H. apply bVexists_eq in H.
    elim H. intros. elim H2. intros. clear H2. apply VF_beq_true in H3.
    rewrite Vbuild_nth in H3. rewrite FMatrix.mat_build_nth. rewrite Vbuild_nth. 
    unfold FMatrix.VA.id_vec. destruct (Nat.eq_dec i0 i).
    + subst. rewrite Vnth_replace. rewrite FMatrix.mat_transpose_row_col.
    unfold FMatrix.get_row. rewrite H3. assert (Vnth m ip = Vnth m ip0).
    apply f_equal. apply le_unique. rewrite <- H2. rewrite H3.
    rewrite FMatrix.VA.dot_product_id. rewrite Vnth_replace. trivial.
    + assert (i <> i0). unfold not in *. intros. apply n0. rewrite H2. trivial. 
    rewrite Vnth_replace_neq; trivial. rewrite Vnth_const. 
    rewrite FMatrix.mat_transpose_row_col. unfold FMatrix.get_row.
    rewrite H3. rewrite FMatrix.VA.dot_product_id. assert (MFisPermutation m). 
    trivial. unfold MFisPermutation in H0. apply andb_true_iff in H0. destruct H0.
    apply (bVforall_elim_nth ip0) in H0. unfold VF_an_id in H0. 
    apply bVexists_eq in H0. elim H0. intros. elim H6. intros. clear H6.
    apply VF_beq_true in H7. rewrite Vbuild_nth in H7. rewrite H7.
    destruct TrivialOrNot. apply H6.
    pose (MF_perm_row_uniq m H4 H6 ip0 ip x2 x0 n0 H7 H3). rewrite Vnth_replace_neq.
    trivial. rewrite Vnth_const. trivial.
  Qed.

  Lemma vecIdVtail : forall x n (xp : S x < S n),
    Vtail (FMatrix.VA.id_vec xp) = FMatrix.VA.id_vec (lt_S_n xp).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_tail. trivial.
  Qed. 

  Lemma vecIdVremove_last : forall n ,
    Vremove_last (FMatrix.VA.id_vec (lt_0_Sn (S n))) = 
      FMatrix.VA.id_vec (lt_0_Sn n).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_remove_last. 
    unfold FMatrix.VA.id_vec. destruct i. do 2 rewrite Vnth_replace. trivial.
    rewrite Vnth_replace_neq. lia. rewrite Vnth_replace_neq. lia. 
    do 2 rewrite Vnth_const. trivial. 
  Qed.

  Lemma vecIdVremove_last2 : forall n x (xp : x < S n)(xp' : x < n),
    Vremove_last (FMatrix.VA.id_vec xp) = 
      FMatrix.VA.id_vec xp'.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_remove_last. 
    unfold FMatrix.VA.id_vec. destruct (Nat.eq_dec x i).
    + subst. do 2 rewrite Vnth_replace. trivial.
    + rewrite Vnth_replace_neq. lia. rewrite Vnth_replace_neq. lia. 
    do 2 rewrite Vnth_const. trivial. 
  Qed.

  Fixpoint MF_perm_last n : MF (S n) -> (Index (S n)) :=
    match n with
      | 0 => fun _ => MakeIndex (lt_0_Sn 0)
      | S a => fun m => match VF_beq (Vhead m) (FMatrix.VA.id_vec (lt_n_Sn (S a))) with
        | true => MakeIndex (lt_0_Sn (S a))
        | false => MakeIndexSucc (MF_perm_last (Vmap (fun a => Vtail a) (Vtail m)))
      end
    end.  

  Definition IdSub n (v : VF n) := VatMostOne (fun a => negb (Fbool_eq a 0)) v.

  Lemma IdSub_Vforall : forall n n' (v : vector (VF (S n)) n'),
    Vforall (IdSub (n:=S n)) v ->
    Vforall (IdSub (n:=n)) (Vmap (fun a => Vremove_last a) v).
  Proof.
    intros. induction v. simpl. trivial. simpl in *. destruct H. split.
    apply VatMostOne_remove. trivial. apply IHv. trivial.
  Qed.

  Lemma IdSub_Vforall2 : forall n n' (v : vector (VF (S n)) n'),
    Vforall (IdSub (n:=S n)) v ->
    Vforall (IdSub (n:=n)) (Vmap (fun a => Vtail a) v).
  Proof.
    intros. induction v. simpl. trivial. simpl in *. destruct H. split.
    apply VatMostOne_tail. trivial. apply IHv. trivial.
  Qed.

  Lemma IdFoldSub : forall n x (xp : x < n),
    0 <> 1 ->
    Vfold_left Nat.add 0%nat (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat 
      else 0%nat)  (FMatrix.VA.id_vec xp)) = 1%nat.
  Proof.
    induction n; intros. lia. rewrite (VSn_eq (FMatrix.VA.id_vec xp)). 
    rewrite Vcons_map. rewrite Vfold_left_Vcons;  intros. lia. lia.
     destruct x. replace (~~ Fbool_eq (Vhead (FMatrix.VA.id_vec xp)) 0) with true.
   replace (Vfold_left Nat.add 0%nat (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat)
     (Vtail (FMatrix.VA.id_vec xp)))) with 0%nat. lia. clear IHn. simpl.
   replace (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat) (FMatrix.VA.zero_vec n))
    with (Vconst 0%nat n). induction n. cbn. trivial. cbn. rewrite <- IHn. lia. lia.
    apply Veq_nth. intros. rewrite Vnth_const. rewrite Vnth_map. rewrite Vnth_const.
    replace (~~ Fbool_eq FSemiRingT.A0 0) with false. trivial.  symmetry. 
    apply negb_false_iff. apply F_bool_eq_corr. trivial. symmetry.
    apply negb_true_iff. apply F_bool_neq_corr. rewrite Vhead_nth. rewrite Vnth_replace.
    unfold not. intros. apply H. rewrite <- H0. trivial.
   rewrite IHn. replace (~~ Fbool_eq (Vhead (FMatrix.VA.id_vec xp)) 0) with
    false. trivial. symmetry. apply negb_false_iff. apply F_bool_eq_corr.
    rewrite Vhead_nth. rewrite Vnth_replace_neq. lia. rewrite Vnth_const. trivial.
    cbn. assert (Fbool_eq FSemiRingT.A0 0 = true). apply F_bool_eq_corr. trivial.
    rewrite H0. cbn. trivial.
  Qed.

  Lemma IdSubImp : forall n (v : VF (S n)) i (ip : i < n),
    IdSub v ->
    Vnth v (le_S ip) <> 0 ->
    VlastS v = 0.
  Proof.
    induction n; intros. lia. destruct i. unfold VlastS. rewrite Vlast_nth.
    case_eq (Fbool_eq (Vnth v (Nat.lt_succ_diag_r (S n))) 0); intros.
    apply F_bool_eq_corr in H1. trivial. apply F_bool_neq_corr in H1.
    unfold IdSub, VatMostOne in H. assert (2 <= Vfold_left Nat.add 0%nat 
    (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat) v)). 
    clear H. clear IHn. rewrite (VSn_eq v). rewrite (VSn_addS (Vtail v)).
    rewrite Vcons_map. rewrite Vadd_map. rewrite Vfold_left_Vcons;  intros. lia. lia.
    rewrite Vfold_add;  intros. lia. lia. replace (~~ Fbool_eq (Vhead v) 0) with true.
    replace (~~ Fbool_eq (VlastS (Vtail v)) 0) with true. lia. 
    symmetry. apply negb_true_iff. apply F_bool_neq_corr. unfold VlastS.
    rewrite Vlast_nth. unfold not in *. intros. apply H1. rewrite <- H.
    rewrite Vnth_tail. apply Vnth_eq. trivial. symmetry. apply negb_true_iff. 
    apply F_bool_neq_corr. rewrite Vhead_nth. unfold not in *. intros. apply H0.
    rewrite <- H. apply Vnth_eq. trivial. lia.
    rewrite <- VlastS_tail. apply (IHn (Vtail v) i (lt_S_n ip)). 
    apply VatMostOne_tail. trivial. rewrite Vnth_tail. unfold not in *.
    intros. apply H0.  rewrite <- H1. apply Vnth_eq. trivial.  
  Qed.

  Lemma IdSubImp2 : forall n (v : VF (S n)) i (ip : i < n),
    IdSub v ->
    Vnth v (lt_n_S ip) <> 0 ->
    Vhead v = 0.
  Proof.
    destruct n; intros. lia. rewrite Vhead_nth.
    case_eq (Fbool_eq (Vnth v (Nat.lt_0_succ (S n))) 0); intros.
    apply F_bool_eq_corr in H1. trivial. apply F_bool_neq_corr in H1.
    unfold IdSub, VatMostOne in H. assert (2 <= Vfold_left Nat.add 0%nat 
    (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat) v)). 
    clear H. rewrite (VSn_eq v). rewrite Vcons_map. rewrite Vfold_left_Vcons; intros. 
    lia. lia. rewrite (Vfold_left_Vremove Nat.add (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat)
    (Vtail v)) 0%nat ip); intros; trivial. lia. lia. rewrite Vnth_map.
    replace (~~ Fbool_eq (Vhead v) 0) with true.
    replace (~~ Fbool_eq (Vnth (Vtail v) ip) 0) with true. lia. 
    symmetry. apply negb_true_iff. apply F_bool_neq_corr. 
    rewrite Vnth_tail. unfold not in *. intros. apply H0. rewrite <- H. trivial.
    symmetry. apply negb_true_iff. 
    apply F_bool_neq_corr. rewrite Vhead_nth. unfold not in *. intros. apply H1.
    trivial. lia.
  Qed.

  Lemma IdSubImp3 : forall n (v : VF (S n)) i (ip : i < S n) j (jp : j < S n),
    IdSub v ->
    i <> j ->
    Vnth v ip <> 0 ->
    Vnth v jp = 0.
  Proof.
    destruct n; intros. lia.
    case_eq (Fbool_eq (Vnth v jp) 0); intros.
    apply F_bool_eq_corr in H2. trivial. apply F_bool_neq_corr in H1.
    unfold IdSub, VatMostOne in H. assert (2 <= Vfold_left Nat.add 0%nat 
    (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat) v)). 
    clear H. rewrite (Vfold_left_Vremove Nat.add (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat)
    v) 0%nat ip); intros; trivial. lia. lia. rewrite Vnth_map. destruct j.
    + destruct i. lia. rewrite (VSn_eq (Vremove (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat) v) ip)).
    rewrite Vfold_left_Vcons; intros. lia. lia. rewrite Vremove_head.
    rewrite Vhead_map. replace (~~ Fbool_eq (Vnth v ip) 0) with true.
    replace (~~ Fbool_eq (Vhead v) 0) with true. lia. symmetry. apply negb_true_iff.
    apply F_bool_neq_corr. apply F_bool_neq_corr in H1. rewrite <- Vnth0Head in H2.
    apply F_bool_neq_corr. trivial. symmetry. apply negb_true_iff.
    apply F_bool_neq_corr. apply F_bool_neq_corr in H1. trivial.
    + destruct (le_lt_dec i j). 
    ++ rewrite (Vfold_left_Vremove Nat.add (Vremove (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat) v)
    ip) 0%nat (lt_S_n jp)); intros; trivial. lia. lia. rewrite Vremove_correct_right. trivial. rewrite Vnth_map. 
    replace (~~ Fbool_eq (Vnth v ip) 0) with true.
    replace (~~ Fbool_eq (Vnth v (lt_n_S (lt_S_n jp))) 0) with true. lia. 
    symmetry. apply negb_true_iff. apply F_bool_neq_corr. apply F_bool_neq_corr in H2. 
    unfold not in *. intros. apply H2. rewrite <- H. apply Vnth_eq. trivial.
    symmetry. apply negb_true_iff. trivial.
    ++ assert (S j < S n). lia. rewrite (Vfold_left_Vremove Nat.add (Vremove (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat) v)
    ip) 0%nat H); intros; trivial. lia. lia. rewrite Vremove_correct_left.
     trivial. lia. rewrite Vnth_map.
    replace (~~ Fbool_eq (Vnth v ip) 0) with true.
    replace (~~ Fbool_eq (Vnth v (le_S H)) 0) with true. lia. 
    symmetry. apply negb_true_iff. apply F_bool_neq_corr. apply F_bool_neq_corr in H2. 
    unfold not in *. intros. apply H2. rewrite <- H3. apply Vnth_eq. trivial.
    symmetry. apply negb_true_iff. trivial.
    + lia.
  Qed.
     
  Lemma id_vec_to_IdSub : forall n (v : VF n),
    bVexists (VF_beq v) (Vbuild (fun i ip =>  (FMatrix.VA.id_vec ip))) ->
    IdSub v.
  Proof.
    intros. unfold IdSub, VatMostOne. apply bVexists_eq in H. elim H. intros.
    elim H0. intros. clear H0. apply VF_beq_true in H1. rewrite Vbuild_nth in H1. 
    rewrite H1. destruct TrivialOrNot. assert (Vmap (fun b : F => if ~~ Fbool_eq b 0 
    then 1%nat else 0%nat) (FMatrix.VA.id_vec x0) = Vconst 0%nat n). apply Veq_nth.
    intros. rewrite Vnth_map. rewrite Vnth_const. rewrite (H0 
    (Vnth (FMatrix.VA.id_vec x0) ip) 0). replace (~~ Fbool_eq 0 0) with false.
    trivial. symmetry. apply negb_false_iff. apply F_bool_eq_corr. trivial. 
    rewrite H2. clear H. clear H1. clear H2. clear H0. clear x0. clear x. clear v.
    induction n. cbn. lia. cbn. apply IHn. rewrite IdFoldSub. trivial. lia.
  Qed.

  Lemma Permutaion_to_IdSub : forall n (m : MF n),
    MFisPermutation m -> 
    Vforall (IdSub (n:=n)) m /\ Vforall (IdSub (n:=n)) (MF_trans m).
  Proof.
    intros. apply andb_true_iff in H. destruct H. split.
    + apply Vforall_nth_intro. intros. apply (bVforall_elim_nth ip) in H.
    apply id_vec_to_IdSub. trivial.
    + apply Vforall_nth_intro. intros. apply (bVforall_elim_nth ip) in H0.
    apply id_vec_to_IdSub. trivial.
  Qed.

  Lemma vecIdVremove_last3 : forall n (v : VF (S n)) x (xp : x < n),
    IdSub v ->
    Vremove_last v = FMatrix.VA.id_vec xp <-> v = FMatrix.VA.id_vec (le_S xp).
  Proof.
    split; intros. 
    + rewrite (VSn_addS v). rewrite H0. apply Veq_nth. intros. rewrite Vnth_add. destruct (Nat.eq_dec i n).
    unfold VlastS.  destruct (Nat.eq_dec x i).
    ++ subst. lia.
    ++ subst. rewrite Vnth_replace_neq. trivial. rewrite Vnth_const. 
    destruct TrivialOrNot. apply H1.
    apply (IdSubImp xp).
    trivial. apply (Veq_nth4 xp) in H0. rewrite Vnth_remove_last in H0. 
    assert (Nat.lt_lt_succ_r xp = le_S xp). apply le_unique. rewrite H2 in H0.
    rewrite H0. rewrite Vnth_replace. unfold not. intros. apply H1. rewrite <- H3.
    trivial.
    ++ destruct (Nat.eq_dec x i). 
    +++ subst. do 2 rewrite Vnth_replace. trivial.
    +++ rewrite Vnth_replace_neq. trivial. rewrite Vnth_replace_neq. trivial. do 2 rewrite Vnth_const.
    trivial.
    + rewrite H0. apply Veq_nth. intros. rewrite Vnth_remove_last. destruct (Nat.eq_dec x i).
    subst. rewrite Vnth_replace. rewrite Vnth_replace. trivial. rewrite Vnth_replace_neq. 
    trivial. rewrite Vnth_replace_neq. trivial. do 2 rewrite Vnth_const. trivial.
  Qed.

  Lemma MF_perm_last_valid_sub_sub : forall n (m : MF (S n)),
    Vforall (IdSub (n:=S n)) m ->
    sval (MF_perm_last m) < n ->
    Vnth m (proj2_sig (MF_perm_last m)) = FMatrix.VA.id_vec (lt_n_Sn n).
  Proof.
    intros. induction n. lia. simpl. case_eq (VF_beq (Vhead m) 
    (FMatrix.VA.id_vec (lt_n_Sn (S n))));
    intros. rewrite <- Vnth0Head. apply VF_beq_true in H1. trivial.
    rewrite (VSn_eq (FMatrix.VA.id_vec (lt_n_Sn (S n)))).
    rewrite vecIdVtail. assert (Vnth (Vmap (fun a => Vtail a) (Vtail m)) 
    (proj2_sig (MF_perm_last (Vmap (fun a => Vtail a) (Vtail m)))) = 
    FMatrix.VA.id_vec (Nat.lt_succ_diag_r n)). apply IHn.
    + simpl. apply IdSub_Vforall2. rewrite (VSn_eq m) in H. simpl in H. destruct H.
    trivial.
    + simpl in H0. rewrite H1 in H0. rewrite MakeIndexSuccProj in H0. 
    apply lt_S_n in H0. trivial.
    + rewrite Vnth_map in H2. replace (lt_S_n (Nat.lt_succ_diag_r (S n))) with
    (Nat.lt_succ_diag_r n). rewrite <- H2. 
    apply Veq_nth. intros. rewrite Vnth_cons. destruct (NatUtil.lt_ge_dec 0 i).
    ++ subst. do 2 rewrite Vnth_tail. apply Veq_nth3. lia. apply Vnth_eq. 
    rewrite MakeIndexSuccProj. lia.
    ++ replace (Vhead (FMatrix.VA.id_vec (Nat.lt_succ_diag_r (S n))))
    with 0. assert (i = 0%nat). lia. subst. rewrite <- Vnth0Head.
    destruct TrivialOrNot. apply H3.
    apply (IdSubImp2 (lt_n_Sn n)). apply (Vforall_nth (proj2_sig
        (MakeIndexSucc (MF_perm_last (Vmap (fun a => Vtail a) (Vtail m)))))) in  H.
    trivial. apply (Veq_nth4 (lt_n_Sn n)) in H2. rewrite Vnth_tail in H2.
    rewrite Vnth_tail in H2. assert (Vnth (Vnth m  (proj2_sig
    (MakeIndexSucc (MF_perm_last (Vmap (fun a => Vtail a) (Vtail m))))))
  (lt_n_S (lt_n_Sn n)) = Vnth (Vnth m (lt_n_S
             (proj2_sig (MF_perm_last (Vmap (fun a => Vtail a) (Vtail m))))))
       (lt_n_S (lt_n_Sn n))). apply Veq_nth3. trivial.
    apply Vnth_eq. rewrite MakeIndexSuccProj. lia. rewrite H4. rewrite H2.
    rewrite Vnth_replace. unfold not. intros. apply H3. rewrite <- H5. trivial.
    rewrite Vhead_nth. rewrite Vnth_replace_neq. lia. rewrite Vnth_const. trivial.
    ++ apply le_unique.
  Qed.

  Lemma MF_perm_last_clear : forall n (m : MF (S n)) i (ip : i < S n),
    i < proj1_sig (MF_perm_last m) ->
    VF_beq (Vnth m ip) (FMatrix.VA.id_vec (lt_n_Sn n)) = false.
  Proof.
    induction n. intros. 
    + (* base case *) cbn in *. lia.
    + intros. simpl in *. case_eq (VF_beq (Vhead m) 
    (FMatrix.VA.id_vec (lt_n_Sn (S n)))); intros. 
    ++ rewrite H0 in H. simpl in *. lia. 
    ++ destruct i. rewrite <- Vnth0Head. trivial. rewrite H0 in H. simpl.
    pose (IHn (Vmap [fun x=> Vtail x] (Vtail m)) i (lt_S_n ip)).
    assert (i < sval (MF_perm_last (Vmap [eta Vtail (n:=S n)] (Vtail m)))).
    simpl in H. rewrite MakeIndexSuccProj in H. lia. apply e in H1.
    apply VF_beq_false in H1. apply VF_beq_false. unfold not in *.
    intros. apply H1. rewrite Vnth_map. rewrite Vnth_tail. simpl. 
    replace (lt_n_S (lt_S_n ip)) with ip. rewrite H2. rewrite vecIdVtail.
    apply f_equal. apply le_unique. apply le_unique.
  Qed.  

  Lemma MF_perm_last_bound : forall n (m : MF (S n)),
    sval (MF_perm_last m) <= n.
  Proof.
    intros. induction n. cbn. trivial. simpl. destruct (VF_beq (Vhead m) 
    (FMatrix.VA.id_vec (Nat.lt_succ_diag_r (S n)))).
    destruct ((exist (Nat.lt_0_succ (S n)))). cbn. lia.
    pose (IHn (Vmap [eta Vremove_last (n:=S n)] (Vtail m))).
    rewrite MakeIndexSuccProj. apply le_n_S. trivial.
  Qed.

  Lemma MF_perm_last_valid_sub : forall n (m : MF (S n)),
    bVforall (VF_an_id (n:=S n)) m = true ->
    Vnth m (proj2_sig (MF_perm_last m)) = FMatrix.VA.id_vec (lt_n_Sn n) \/
    bVforall (fun a => negb (VF_beq a (FMatrix.VA.id_vec (lt_n_Sn n)))) m.
  Proof.
    intros. case_eq (le_lt_dec n (sval (MF_perm_last m))). 
    + intros. destruct n.
    ++ cbn. left.
    apply (bVforall_elim_nth (Nat.lt_0_succ 0)) in H. unfold VF_an_id in H. 
    apply bVexists_eq in H. elim H. intros. elim H1.
    intros. clear H1. apply VF_beq_true in H2. rewrite Vbuild_nth in H2.
    rewrite H2. assert (x = 0%nat). lia. subst. trivial.
    ++ assert (n < proj1_sig (MF_perm_last m)). lia. case_eq (VF_beq (Vnth m (proj2_sig (MF_perm_last m))) 
    (FMatrix.VA.id_vec ((lt_n_Sn (S n))))); intros.
    +++ left. apply VF_beq_true in H2. trivial.
    +++ right. apply bVforall_nth_intro. intros. case_eq (Nat.eq_dec i (S n)); intros.
    subst. apply VF_beq_false in H2. apply negb_true_iff. apply VF_beq_false.
    unfold not in *. intros. apply H2. rewrite <- H4. apply Vnth_eq.
    pose (MF_perm_last_bound m). lia. assert (i < S n). lia.
    apply negb_true_iff. apply MF_perm_last_clear. lia.
    + left. apply MF_perm_last_valid_sub_sub; trivial. apply Vforall_nth_intro. intros.
    apply id_vec_to_IdSub. apply (bVforall_elim_nth ip) in H. trivial. 
  Qed.

  Lemma MF_perm_clear : forall n (m : MF (S n)) i (ip : i < S n),
    MFisPermutation m -> 
    0 <> 1 ->
    i <> proj1_sig (MF_perm_last m) ->
    VF_beq (Vnth m ip) (FMatrix.VA.id_vec (lt_n_Sn n)) = false.
  Proof.
    intros. apply andb_true_iff in H. destruct H. 
    pose (MF_perm_last_valid_sub m H). destruct o.
    + apply VF_beq_false. unfold not. intros. 
    pose (MF_perm_row_uniq_sub m H2 H0 ip (proj2_sig (MF_perm_last m)) (Nat.lt_succ_diag_r n) 
    (Nat.lt_succ_diag_r n) H1 H4 H3). apply n0. trivial.
    + apply (bVforall_elim_nth ip) in H3. apply negb_true_iff in H3. trivial.
  Qed.  

  Lemma MF_perm_clear_nth : forall n (m : MF (S n)) i (ip : i < S n),
    MFisPermutation m -> 
    i <> proj1_sig (MF_perm_last m) ->
    Vnth (Vnth m ip) (Nat.lt_succ_diag_r n) = 0.
  Proof.
    intros. destruct TrivialOrNot. apply H1.
    pose (MF_perm_clear m ip H H1 H0). apply VF_beq_false in e.
    unfold MFisPermutation in H.  apply andb_true_iff in H.  destruct H.
    apply (bVforall_elim_nth ip) in H.
    apply bVexists_eq in H. elim H. intros. elim H3.
    intros. clear H3. apply VF_beq_true in H4. rewrite Vbuild_nth in H4.
    rewrite H4. destruct (Nat.eq_dec x n). assert (False). apply e. 
    rewrite H4. subst. apply f_equal. apply le_unique. contradiction.
    rewrite Vnth_replace_neq. trivial. rewrite Vnth_const. trivial.
  Qed. 

  Lemma MF_perm_last_corr : forall n (m : MF (S n)),
    MFisPermutation m -> 
    Vnth m (proj2_sig (MF_perm_last m)) = FMatrix.VA.id_vec (lt_n_Sn n).
  Proof.
    intros. destruct (le_lt_dec n (sval (MF_perm_last m))).
    assert (sval (MF_perm_last m) = n). pose (MF_perm_last_bound m). lia.
    apply MF_perm_row_imp. trivial. intros. apply VF_beq_false.
    apply MF_perm_last_clear. lia. 
    apply (MF_perm_last_valid_sub_sub m). apply Permutaion_to_IdSub. trivial. lia.
  Qed.

  (* Remove by row *)
  Definition MF_perm_sub n (m : MF (S n)) : MF n :=
    Vmap (fun a => Vremove_last a) (Vremove m (proj2_sig (MF_perm_last m))). 

  Lemma MF_perm_sub_id : forall n (m : MF (S n)),
    m = Vmap2 (fun a b => Vadd a (VlastS b))
      (Vinsert (Vremove_last (Vnth m (proj2_sig (MF_perm_last m)))) (MF_perm_sub m)
        (proj2_sig (MF_perm_last m))) m.
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. rewrite Vnth_map2. 
    apply Veq_nth2. rewrite (VSn_addS (Vnth m ip)). apply f_equal2.
    + unfold MF_perm_sub. rewrite Vnth_cast. rewrite Vnth_app.
    destruct (le_gt_dec (sval (MF_perm_last m)) i). rewrite Vnth_cons.
    destruct (NatUtil.lt_ge_dec 0 (i - sval (MF_perm_last m))).
    rewrite Vnth_sub. rewrite Vnth_map.  rewrite Vremove_correct_right. lia.
    apply f_equal. apply Vnth_eq. lia. apply f_equal. apply Vnth_eq. lia.
    rewrite Vnth_sub. rewrite Vnth_map. rewrite Vremove_correct_left.
    lia. apply f_equal. apply Vnth_eq. lia.
    + rewrite VlastS_add. trivial.
  Qed.

   Lemma MF_perm_last_tran : forall n (m : MF (S n)),
    MFisPermutation m -> 
    Vnth m (proj2_sig (MF_perm_last m)) = 
      Vnth (MF_trans m) (proj2_sig (MF_perm_last (MF_trans m))).
  Proof.
    intros. rewrite MF_perm_last_corr. trivial. rewrite MF_perm_last_corr.
    apply MF_perm_inv. trivial. trivial.
  Qed.

  Lemma permTranInd_sub :  forall n (m : MF (S n)),
    MFisPermutation m -> MFisPermutation (MF_perm_sub m).
  Proof.
    intros. assert (MFisPermutation m) as b. trivial. unfold MFisPermutation in *. 
    apply andb_true_iff in H.  destruct H. unfold MFisPermutation.
    apply andb_true_iff. split.
    + apply bVforall_nth_intro. intros. rewrite Vnth_map.
    destruct TrivialOrNot. unfold VF_an_id. apply bVexists_eq. exists i. 
    exists ip. apply VF_beq_true. apply Veq_nth. intros. apply H1.
    destruct (le_lt_dec (sval (MF_perm_last m)) i).
    ++ rewrite Vremove_correct_right. trivial. 
    apply (bVforall_elim_nth (lt_n_S ip)) in H.
    apply bVexists_eq in H. elim H. intros. elim H2.
    intros. clear H2. apply VF_beq_true in H3. rewrite Vbuild_nth in H3.
    apply bVexists_eq. exists x.  destruct (Nat.eq_dec x n).
    subst. assert False. assert (S i <> sval (MF_perm_last m)). lia.
    pose (MF_perm_clear m (lt_n_S ip) b H1). apply VF_beq_false in e.
    unfold not in *. apply e. rewrite H3. apply f_equal. apply le_unique. trivial.
    contradiction. assert (x < n). lia. exists H2. apply VF_beq_true. 
    rewrite Vbuild_nth. rewrite H3. apply vecIdVremove_last2.
    ++ rewrite Vremove_correct_left. trivial. 
    apply (bVforall_elim_nth (le_S ip)) in H.
    apply bVexists_eq in H. elim H. intros. elim H2.
    intros. clear H2. apply VF_beq_true in H3. rewrite Vbuild_nth in H3.
    apply bVexists_eq. exists x. destruct (Nat.eq_dec x n). assert False. 
    assert (i <> sval (MF_perm_last m)). lia. pose (MF_perm_clear m (le_S ip) b H1). 
    apply VF_beq_false in e0. unfold not in *. apply e0. rewrite H3. subst. 
    apply f_equal. apply le_unique. trivial. contradiction.
    assert (x < n). lia. exists H2. apply VF_beq_true. rewrite Vbuild_nth. 
    rewrite H3. apply vecIdVremove_last2.
    + apply bVforall_nth_intro. intros. unfold MF_perm_sub.
    assert (bVforall (VF_an_id (n:=S n)) (FMatrix.mat_transpose m) = true) as bac. 
    trivial.
    apply (bVforall_elim_nth (le_S ip)) in H0. apply bVexists_eq in H0. elim H0. 
    intros. elim H1. intros. clear H1. apply VF_beq_true in H2.
    rewrite Vbuild_nth in H2. apply bVexists_eq.
    destruct TrivialOrNot. unfold VF_an_id.  exists i. 
    exists ip. apply VF_beq_true. apply Veq_nth. intros. apply H1.
    destruct (le_lt_dec x (sval (MF_perm_last m))). 
    ++ assert (x <> sval (MF_perm_last m)). (* First we show what it can't be *)
    assert (Vnth m (proj2_sig (MF_perm_last m)) = 
    FMatrix.VA.id_vec (lt_n_Sn n)). apply MF_perm_last_corr. trivial.
    unfold not. intros. apply MF_perm_mix_eq  in H2. trivial. 
    subst. assert ((proj2_sig (MF_perm_last m)) = x0). apply le_unique.
    rewrite H4 in H3. rewrite H2 in H3. apply H1. apply (Veq_nth4 (le_S ip)) in H3.
    rewrite Vnth_replace in H3. rewrite Vnth_replace_neq in H3. lia.
    rewrite Vnth_const in H3. unfold FSemiRingT.A1 in H3. rewrite H3. trivial. trivial.
    (* The we resume *)
    assert (x < n). pose (MF_perm_last_bound m). lia. 
    assert (x < sval (MF_perm_last m)). lia. exists x. exists H4.
    apply VF_beq_true. rewrite Vbuild_nth. apply Veq_nth. intros. 
    rewrite FMatrix.mat_build_nth. unfold FMatrix.get_elem, FMatrix.get_row. 
    rewrite Vnth_map. destruct (le_lt_dec (sval (MF_perm_last m)) i0). 
    (* Ready to split *)
    apply (Veq_nth4 (lt_n_S ip0)) in H2. assert (x <> i0). lia.
    rewrite Vnth_replace_neq. trivial. rewrite Vnth_replace_neq in H2. trivial. lia.
    rewrite Vnth_const. rewrite Vnth_const in H2. rewrite <- H2. rewrite FMatrix.mat_build_nth. 
    unfold FMatrix.get_elem, FMatrix.get_row. rewrite Vnth_remove_last.
    apply Veq_nth3. trivial. rewrite Vremove_correct_right. lia. trivial.
    (* First split complete *) rewrite Vremove_correct_left. lia.
    rewrite Vnth_remove_last. apply (Veq_nth4 (le_S ip0)) in H2. 
    rewrite FMatrix.mat_build_nth in H2. unfold FMatrix.get_elem, FMatrix.get_row in H2.
    assert ((Nat.lt_lt_succ_r ip) = le_S ip). apply le_unique. rewrite H6.
    rewrite H2. destruct (Nat.eq_dec x i0). subst. do 2 rewrite Vnth_replace.
    trivial. rewrite Vnth_replace_neq. trivial. rewrite Vnth_replace_neq. trivial.
    do 2 rewrite Vnth_const. trivial.
    ++ destruct x. lia. apply (Vremove_intro (proj2_sig (MF_perm_last m))) in H2.
    rewrite Vremove_replace_const2 in H2. lia. exists x. exists (lt_S_n x0). 
    apply VF_beq_true. rewrite Vbuild_nth. unfold FMatrix.VA.id_vec, 
    FMatrix.VA.zero_vec. symmetry in H2. rewrite H2. 
    apply Veq_nth. intros. destruct (le_lt_dec (sval (MF_perm_last m)) i0).
    rewrite Vremove_correct_right. trivial. do 2  rewrite FMatrix.mat_build_nth. 
    unfold FMatrix.get_elem, FMatrix.get_row. rewrite Vnth_map.
    rewrite Vnth_remove_last. rewrite Vremove_correct_right. lia. apply Vnth_eq.
    trivial. rewrite Vremove_correct_left. trivial. do 2  rewrite FMatrix.mat_build_nth. 
    unfold FMatrix.get_elem, FMatrix.get_row. rewrite Vnth_map.
    rewrite Vnth_remove_last. rewrite Vremove_correct_left. lia. apply Vnth_eq.
    trivial.
  Qed.

  Lemma permSubRow : forall n (m : MF (S n)) i (ip : i < n) x (xp : x < n),
    sval (MF_perm_last m) <= i ->
    Vnth m (lt_n_S ip) = FMatrix.VA.id_vec (le_S xp) ->
    Vnth (MF_perm_sub m) ip = FMatrix.VA.id_vec xp.
  Proof.
    intros. rewrite Vnth_map. rewrite Vremove_correct_right. trivial.
    rewrite H0. rewrite vecIdVremove_last3. trivial. apply id_vec_to_IdSub.
    apply bVexists_eq. exists x. exists (le_S xp). apply VF_beq_true. 
    rewrite Vbuild_nth. trivial. trivial.
  Qed.

  Lemma permSubRow2 : forall n (m : MF (S n)) i (ip : i < n) x (xp : x < n),
    i < sval (MF_perm_last m) ->
    Vnth m (le_S ip) = FMatrix.VA.id_vec (le_S xp) ->
    Vnth (MF_perm_sub m) ip = FMatrix.VA.id_vec xp.
  Proof.
    intros. rewrite Vnth_map. rewrite Vremove_correct_left. trivial.
    rewrite H0. rewrite vecIdVremove_last3. trivial. apply id_vec_to_IdSub.
    apply bVexists_eq. exists x. exists (le_S xp). apply VF_beq_true.
    rewrite Vbuild_nth. trivial. trivial.
  Qed.

  Lemma permutationInnerProd : forall n (m : MF n)(a : VF n), 
    MFisPermutation m ->
    VF_prod (Vbuild (fun (j : nat) (jp : j < n) =>
      Vnth (MF_CVmult m a) jp)) =
    VF_prod a.
  Proof.
    intros. assert (MFisPermutation m) as b. trivial.
    induction n. cbn. rewrite (Vector_0_is_nil a). cbn. trivial.
    rewrite (MF_perm_sub_id m). unfold VF_prod. rewrite (VSn_addS a).
    rewrite Vfold_add. intros. ring; auto. intros. ring; auto. rewrite <- VSn_addS.
    rewrite (Vfold_left_Vremove Fmul (Vbuild
     (fun j : nat =>
      [eta Vnth
             (MF_CVmult
                (Vmap2
                   (fun (a0 : FMatrix.vec n) (b : FMatrix.vec (S n)) =>
                    Vadd a0 (VlastS b))
                   (Vinsert (Vremove_last (Vnth m (proj2_sig (MF_perm_last m))))
                      (MF_perm_sub m) (proj2_sig (MF_perm_last m))) m) a) (i:=j)])) Fone (proj2_sig (MF_perm_last m))).
     intros. ring; auto. intros. ring; auto. destruct module_ring.
     rewrite Rmul_comm. apply f_equal2.
    + unfold VF_prod in IHn. assert (MFisPermutation (MF_perm_sub m)). 
    apply permTranInd_sub. trivial. apply (IHn (MF_perm_sub m) (Vremove_last a)) in H0.
    rewrite <- MF_perm_sub_id. rewrite <- H0. apply f_equal. apply Veq_nth.
    intros. destruct (le_lt_dec (sval (MF_perm_last m)) i). rewrite Vremove_correct_right.
    trivial. do 2 rewrite Vbuild_nth. unfold VF_inProd. do 2 rewrite MF_getRow_prod.
     unfold VF_inProd.   apply andb_true_iff in H.  destruct H. 
    apply (bVforall_elim_nth (lt_n_S ip)) in H.
    apply bVexists_eq in H. elim H. intros. elim H2.
    intros. clear H2. apply VF_beq_true in H3. rewrite Vbuild_nth in H3.
    rewrite H3. destruct (Nat.eq_dec x n).
    destruct TrivialOrNot. rewrite (VSn_eq a). rewrite (VSn_eq (FMatrix.VA.id_vec x0)).
    pose InProd_Vcons. unfold VF_inProd in e0. rewrite e0. replace (Vhead a) with 0.
    replace (FMatrix.VA.dot_product (Vtail (FMatrix.VA.id_vec x0)) (Vtail a)) with 
    (FMatrix.VA.dot_product (Vnth (MF_perm_sub m) ip) (Vremove_last (Vcons 0 (Vtail a)))).
    ring; auto. apply f_equal2. apply Veq_nth. intros.  apply H2. apply Veq_nth. intros.
    apply H2. apply H2.
     assert (S i <> sval (MF_perm_last m)). lia.
    apply (MF_perm_clear m (lt_n_S ip) b) in H2. apply VF_beq_false in H2.
    assert False. apply H2. rewrite H3. subst. apply f_equal. apply le_unique.
    contradiction. trivial. assert (x < n). lia.
    apply (permSubRow m ip H2) in l. rewrite l. 
    do 2 rewrite FMatrix.VA.dot_product_id. rewrite Vnth_remove_last. apply Vnth_eq.
    trivial. rewrite H3. apply f_equal. apply le_unique. rewrite Vremove_correct_left.
    trivial. do 2 rewrite Vbuild_nth. unfold VF_inProd. do 2 rewrite MF_getRow_prod.
     unfold VF_inProd.  apply andb_true_iff in H.  destruct H. 
    apply (bVforall_elim_nth (le_S ip)) in H.
    apply bVexists_eq in H. elim H. intros. elim H2.
    intros. clear H2. apply VF_beq_true in H3. rewrite Vbuild_nth in H3.
    rewrite H3. destruct (Nat.eq_dec x n). assert (i <> sval (MF_perm_last m)). lia.
    destruct TrivialOrNot. rewrite (VSn_eq a). rewrite (VSn_eq (FMatrix.VA.id_vec x0)).
    pose InProd_Vcons. unfold VF_inProd in e0. rewrite e0. replace (Vhead a) with 0.
    replace (FMatrix.VA.dot_product (Vtail (FMatrix.VA.id_vec x0)) (Vtail a)) with 
    (FMatrix.VA.dot_product (Vnth (MF_perm_sub m) ip) (Vremove_last (Vcons 0 (Vtail a)))).
    ring; auto. apply f_equal2. apply Veq_nth. intros.  apply H4. apply Veq_nth. intros.
    apply H4. apply H4.
    apply (MF_perm_clear m (le_S ip) b) in H2. apply VF_beq_false in H2.
    assert False. apply H2. rewrite H3. subst. apply f_equal. apply le_unique.
    contradiction. trivial.  assert (x < n). lia.
    apply (permSubRow2 m ip H2) in l. rewrite l. 
    do 2 rewrite FMatrix.VA.dot_product_id. rewrite Vnth_remove_last. apply Vnth_eq.
    trivial. rewrite H3. apply f_equal. apply le_unique. trivial.
    + rewrite Vbuild_nth. rewrite <- MF_perm_sub_id. rewrite MF_getRow_prod.
    rewrite MF_perm_last_corr; trivial. unfold VF_inProd. 
    rewrite FMatrix.VA.dot_product_id. unfold VlastS. rewrite Vlast_nth. trivial.
  Qed.
  
  Lemma permutationInnerProd_sub : forall n (m : MF n)(a : VF n), 
    MFisPermutation m ->
    VF_prod (MF_CVmult m a) =
    VF_prod a.
  Proof.
    intros. rewrite (Vbuild_Vnth (MF_CVmult m a)). rewrite permutationInnerProd.
    trivial. trivial.
  Qed. 

  Lemma VF_inProd_zero : forall n (a : VF n),
    VF_inProd (VF_zero n) a = 0.
  Proof.
    intros. rewrite InProd_Sum. symmetry. apply VF_sum_zero. apply Veq_nth.
    intros. rewrite Vnth_map2. rewrite Vnth_const. ring; auto.
  Qed.

  Lemma MF_CVmult_Vcons : forall n (m a : VF (S n))(M : vector (VF (S n)) n),
      MF_CVmult (Vcons m M) a = Vcons (VF_inProd m a) 
        (Vbuild (fun i ip => VF_inProd (Vnth M ip) a)).
  Proof.
    intros. apply Veq_nth. intros. rewrite MF_getRow_prod. do 2 rewrite Vnth_cons. 
    destruct (lt_ge_dec 0 i). rewrite Vbuild_nth. trivial.
    trivial.
  Qed.

  Lemma VF_prod_zero : forall n (v : VF n) i (ip : i < n),
    Vnth v ip = 0 ->
    VF_prod v = 0.
  Proof.
    induction n. lia. destruct i.
    + intros. rewrite (VSn_eq v). unfold VF_prod. rewrite Vfold_left_Vcons; intros. 
    ring; auto. ring; auto. rewrite (Vnth0Head v ip). rewrite H. ring; auto.
    + intros. rewrite (VSn_eq v). unfold VF_prod. rewrite Vfold_left_Vcons; intros. 
    ring; auto. ring; auto. unfold VF_prod in IHn. rewrite <- Vnth_tail_lt_S_n in H.
    rewrite (IHn (Vtail v) i (lt_S_n ip)). trivial. ring; auto.
  Qed.

  Lemma VF_prod_MF_CVmult_zero : forall n (m : MF n)(a : VF n) i (ip : i < n),
    VF_zero n = Vnth m ip ->
    VF_prod (MF_CVmult m a) = 0.
  Proof.
    induction n; intros. lia. apply (VF_prod_zero (MF_CVmult m a) ip).
    rewrite MF_getRow_prod. rewrite <- H. rewrite VF_inProd_zero. trivial.
  Qed.

  Fixpoint matRecover_sub m f : nat :=
    match m with
      | 0 => 0%nat 
      | S a => if (Fbool_eq f (VF_sum (Vconst 1 a))) then a else
      matRecover_sub a f
    end.  

  Lemma matRecover_sub_ind : forall m f, 
     matRecover_sub (S m) f = if (Fbool_eq f (VF_sum (Vconst 1 m))) then m else
      matRecover_sub m f.
  Proof.
    intros. cbn. trivial.
  Qed. 

  Lemma matRecover_sub_corr_sub : forall x n,
    VF_sum (Vconst 1 x) <> VF_sum (Vconst 1 n) ->
    x <> n.
  Proof.
    intros. unfold not in *. intros. apply H. rewrite H0. trivial.
  Qed. 

  Lemma matRecover_sub_corr : forall n x,
    x < S n ->
    (forall i j (ip: i < S n)(ij : j < S n), 
    VF_sum (Vconst 1 i) = VF_sum (Vconst 1 j) -> i = j) ->
    matRecover_sub (S n) (VF_sum (Vconst 1 x)) = x.
  Proof.
    intros. induction n.
    + cbn. assert (x = 0%nat). lia. subst. 
    destruct (Fbool_eq (VF_sum (Vconst 1 0)) 0); trivial.
    + rewrite matRecover_sub_ind. 
    case_eq (Fbool_eq (VF_sum (Vconst 1 x)) (VF_sum (Vconst 1 (S n)))); intros.
    apply F_bool_eq_corr in H1. apply H0. lia. lia.  rewrite H1. trivial.
    apply IHn. apply F_bool_neq_corr in H1. apply matRecover_sub_corr_sub in H1.
    lia. intros. apply H0. lia. lia. trivial. 
  Qed.

  Lemma matRecover_sub_less : forall m f, 
    matRecover_sub (S m) f < (S m).
  Proof.
    intros. induction m. cbn. destruct (Fbool_eq f 0). lia. lia.
    rewrite matRecover_sub_ind. destruct (Fbool_eq f (VF_sum (Vconst 1 (S m)))).
    lia. lia.
  Qed.

  Definition matRecover n (a : VF (S n)) : MF (S n) :=  
    Vmap (fun a => FMatrix.VA.id_vec (matRecover_sub_less n a)) a.

  Lemma matRecoverCorrect : forall n (mat : MF (S n)),
    MFisPermutation mat ->
    (forall i j (ip: i < S n)(ij : j < S n), 
    VF_sum (Vconst 1 i) = VF_sum (Vconst 1 j) -> i = j) ->

    let aVec := MF_CVmult mat (Vbuild (fun i (ip : i < S n) => VF_sum (Vconst 1 i))) in

    matRecover aVec = mat.
  Proof.
    intros. apply Veq_nth. intros.
    rewrite Vnth_map. rewrite MF_getRow_prod. unfold MFisPermutation  in H.
    apply andb_true_iff in H. destruct H. apply (bVforall_elim_nth ip) in H.
    apply bVexists_eq in H. elim H. intros. elim H2. intros. apply VF_beq_true in H3.
    rewrite H3. rewrite Vbuild_nth. unfold VF_inProd. 
    rewrite (FMatrix.VA.dot_product_id). rewrite Vbuild_nth. apply gen_equal.
    apply matRecover_sub_corr. lia. trivial. 
  Qed.
  
End MatricesF.

Module MatricesFIns (Ring: RingSig) <: MatricesF Ring.

  Import Ring.

  Lemma TrivialOrNot : (forall (x y : F), x = y) \/ 0 <> 1.
  Proof.
    intros. case_eq (Fbool_eq 0 1); intros. apply F_bool_eq_corr in H.
    left. intros. pose module_ring. destruct r. rewrite <- (Rmul_1_l x).
    rewrite <- (Rmul_1_l y). rewrite <- H. ring; auto. 
    apply F_bool_neq_corr in H. right. trivial.
  Qed.

  Module F <: SetA.
    Definition A := F.
  End F.

  Module F_Eqset := Eqset_def F.

  Module F_Eqset_dec <: Eqset_dec.
    Module Export Eq := F_Eqset.
    Definition eqA_dec := dec_beq F_bool_eq_corr.
  End F_Eqset_dec.

  Lemma FSRth : semi_ring_theory Fzero Fone Fadd Fmul (@eq F).
  Proof.
    constructor. apply module_ring. apply module_ring. apply module_ring. 
    apply module_ring. intros. ring; auto. apply module_ring. apply module_ring. 
    apply module_ring. 
  Qed.

  Module FSemiRingT <: SemiRingType.

    Module Export ES := F_Eqset_dec.

    Definition A0 := Fzero.
    Definition A1 := Fone.

    Definition Aplus := Fadd.

    Instance Aplus_mor : Proper (eqA ==> eqA ==> eqA) Aplus.
    Proof. intros a b ab c d cd. rewrite ab. rewrite cd. refl. Qed.


    Definition Amult := Fmul.

    Instance Amult_mor : Proper (eqA ==> eqA ==> eqA) Amult.
      Proof. intros a b ab c d cd. rewrite ab. rewrite cd. refl. Qed.

    Definition A_semi_ring := FSRth.

  End FSemiRingT.

  Module FMatrix := Matrix FSemiRingT.

  Module ALR := RingAddationalLemmas Ring.

  (* This file contains the definitions and lemmas about matrices *)
  (* This needs to be generalised, so that we can do the
   extraction of the mixnet properly *)

  Infix "+" := Fadd.
  Infix "*" := Fmul.
  Notation "0" := Fzero.
  Notation "1" := Fone.
  Notation "- x" :=  (Finv x).
  Notation "x - y" := (x + (- y)).

  Notation " [ x ; .. ; y ] " := (Vcons x .. (Vcons y Vnil) ..).

  (*We use P* to denote the pairwise use of the operation *)
  (*We use S* to denote the scaler use of the operation *)

  Lemma Vcons_Vapp : forall (N :nat)(A :Type)(a : A)(b : vector A N),
    Vapp [a] b = Vcons a b.
  Proof.
    intros. cbn. trivial.
  Qed.

  Definition VF : nat -> Set := vector F.
  Definition VF_zero := Vconst Fzero.
  Definition VF_one := Vconst Fone. 
  Definition VF_n_id (n N : nat)(np : n < N) := FMatrix.VA.id_vec np.
  Definition VF_prod n (v : VF n) : F :=
    Vfold_left Fmul Fone v.
  Definition VF_sum n (v : VF n) : F :=
    Vfold_left Fadd Fzero v.
  Definition VF_add n (v1 v2 : VF n) : VF n :=
    FMatrix.VA.vector_plus v1 v2.
  Definition VF_neg n (v1 : VF n) : VF n :=
    Vmap Finv v1.
  Definition VF_sub n (v1 v2 : VF n) : VF n :=
    VF_add v1 (VF_neg v2).
  Definition VF_mult n (v1 v2 : VF n) : VF n :=
    Vmap2 Fmul v1 v2.
  Definition VF_scale n (v : VF n)(s : F) : VF n :=
    Vmap (fun x => Fmul x s) v.
  Definition VF_inProd n (v v' : VF n) : F :=
    FMatrix.VA.dot_product v v'.
  Definition VF_eq n (r r' : VF n) : Prop :=
    Vforall2 (@eq F) r r'.
  Definition VF_beq n (r r' : VF n) : bool :=
    bVforall2 Fbool_eq r r'.
  Definition VF_an_id n (v : VF n) : bool :=
    bVexists (VF_beq v) (Vbuild (fun i ip =>  (FMatrix.VA.id_vec ip))).

  Definition Vector_0_is_nil (T : Type) (v : Vector.t T 0) : v = Vector.nil :=
  match v with Vector.nil => eq_refl end.

  Lemma Veq_nth3 : forall (n : nat)(A : Type)(v v' : vector A n),
    (forall i j (ip : i < n)(jp : j < n),
    i = j -> v = v' -> Vnth v ip = Vnth v' jp).
  Proof.
    intros. subst. apply Vnth_eq. trivial.
  Qed.

  Lemma Veq_nth2 : forall (n : nat)(A : Type)(v v' : vector A n),
    v = v' -> (forall i (ip : i < n), Vnth v ip = Vnth v' ip).
  Proof.
   intros. rewrite H. trivial.
  Qed.

  Lemma Vfold_left_eq : forall (n : nat)(A B : Type) (f : A->B->A)
    (v v' : vector B n)(a : A),
    v = v' -> Vfold_left f a v = Vfold_left f a v'.
  Proof.
    intros. rewrite H. trivial.
  Qed.

  Lemma Vfold_left_eq_cast : forall (n n' : nat)(H : n = n')
    (A B : Type)(f : A->B->A)(v : vector B n)
    (v' : vector B n')(a : A),
    Vcast v H = v' -> Vfold_left f a v = Vfold_left f a v'.
  Proof.
    intros. subst. trivial.
  Qed.

  Lemma Vfold_left_cast : forall (n n' : nat)(H : n = n')
    (A B : Type)(f : A->B->A)(v : vector B n)(a : A),
    Vfold_left f a v = Vfold_left f a (Vcast v H).
  Proof.
    intros. subst. trivial.
  Qed.

  Lemma Vtail_remove_last : forall (n : nat)(A : Type)(v : vector A (S (S n))),
    Vtail (Vremove_last v) = Vremove_last (Vtail v).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_tail.
    do 2 rewrite Vnth_remove_last. rewrite Vnth_tail.
    apply Vnth_eq. trivial.
  Qed.

  Lemma Vfold_left_remove_last : forall (A B : Type)(N : nat)
    (f : A->B->A)(v : vector B (S N))(np : Nat.lt N (S N))(a : A),
    Vfold_left f a v = f (Vfold_left f a (Vremove_last v)) (Vnth v np).
  Proof.
    intros A B N f v np. induction N. intros. cbn. rewrite (VSn_eq v). 
    simpl. rewrite (Vector_0_is_nil (Vtail v)). simpl. trivial. 
    intros. remember (Vremove_last v) as c. rewrite (VSn_eq c). 
    rewrite (VSn_eq v). simpl. rewrite IHN. intros. rewrite Heqc.
    assert (forall a a' b b', a=a' -> b=b' -> f a b = f a' b').
    intros. rewrite H. rewrite H0. trivial. apply H.
    assert ((f a (Vhead v)) = (f a (Vhead (Vremove_last v)))).
    do 2 rewrite Vhead_nth. apply H; auto. rewrite Vnth_remove_last.
    apply Vnth_eq. trivial. rewrite H0. apply Vfold_left_eq.
    rewrite Vtail_remove_last. trivial. apply Vnth_eq. trivial.
    auto.
  Qed. 

  Lemma Vfold_left_rev_eq : forall (n : nat)(A B : Type) (f : A->B->A)
    (v v' : vector B n)(a : A),
    v = v' -> Vfold_left_rev f a v = Vfold_left_rev f a v'.
  Proof.
    intros. rewrite H. trivial.
  Qed.

  Lemma Vmap2_eq : forall (n : nat)(A B C : Type) (f : A->B->C)
    (a a' : vector A n)(b b'  : vector B n),
    a = a' -> b = b' -> Vmap2 f a b = Vmap2 f a' b'.
  Proof.
    intros. rewrite H. rewrite H0. trivial.
  Qed.


  Lemma Vtail_map:  forall (N : nat)(A B : Type) (f : A->B)(v : vector A (1+N)),
    Vtail (Vmap f v) = Vmap f (Vtail v).
  Proof.
   intros. apply Veq_nth. intros. rewrite Vnth_tail. do 2 rewrite Vnth_map.
   rewrite Vnth_tail. trivial.
  Qed.

  Lemma Vtail_map2 : forall (A B C : Type) (f: A->B->C) (n :nat)
          (v : vector A (S n)) (v' : vector B (S n)),
      Vmap2 f (Vtail v) (Vtail v') = Vtail (Vmap2 f v v').
  Proof. 
    intros. VSntac v. refl. 
  Qed.

  Lemma Vremove_last_vmap2 :  forall (A B C : Type)(f : A->B->C)(N : nat)
    (v : vector A (S N))(v' : vector B (S N)),
    Vremove_last (Vmap2 f v v') = 
      Vmap2 f (Vremove_last v) (Vremove_last v').
  Proof.
    intros. assert (forall a a' b b', a=a' -> b=b' -> f a b = f a' b').
    intros. rewrite H. rewrite H0. trivial. induction N. cbn. trivial.
    rewrite (VSn_eq (Vremove_last (Vmap2 f v v'))).
    rewrite (VSn_eq (Vmap2 f (Vremove_last v) (Vremove_last v'))).
     apply Vcons_eq_intro. cbn. apply H. rewrite Vhead_nth. apply Vnth_eq.
    trivial. rewrite Vhead_nth. apply Vnth_eq. trivial.
    rewrite <- Vtail_map2. do 3 rewrite Vtail_remove_last. apply IHN. 
  Qed.

  Lemma Vapp_map : forall (N : nat)(A B : Type) (f : A->B)(v : vector A (1+N)),
    (Vapp [Vhead (Vmap f v)](Vtail (Vmap f v))) = 
    Vmap f (Vapp [Vhead v] (Vtail v)).
  Proof.
    intros. apply Veq_nth. intros. induction i.
    cbn. rewrite Vhead_nth. rewrite Vnth_map. rewrite <- Vhead_nth.
    trivial. cbn. rewrite Vnth_tail. do 2 rewrite Vnth_map.
    rewrite Vnth_tail. trivial.
  Qed.

  Lemma Vfold_Fadd_const :  forall (n : nat)(v : vector F n)(a : F),
    forall (h : F),
    (Vfold_left Fadd h v) + a = Vfold_left Fadd (h + a) v.
  Proof.
    intros n v0 a. induction v0. cbn. intros. trivial. cbn. 
    intros. assert (Vfold_left Fadd (h0 + h) v0 + a =
         Vfold_left Fadd ((h0 + h) + a) v0). apply IHv0.
    replace ((h0 + a) + h) with ((h0 + h) + a). apply H.
    ring; auto.
  Qed.

  Lemma Vfold_Fmul_const :  forall (n : nat)(v : vector F n)(a : F),
    forall (h : F),
    (Vfold_left Fmul h v) * a = Vfold_left Fmul (h * a) v.
  Proof.
    intros n v0 a. induction v0. cbn. intros. trivial. cbn. 
    intros. assert (Vfold_left Fmul (h0 * h) v0 * a =
         Vfold_left Fmul ((h0 * h) * a) v0). apply IHv0.
    replace ((h0 * a) * h) with ((h0 * h) * a). apply H.
    ring; auto.
  Qed.

  (* Square matrices of order 2 over Field F *)
  Definition index1 : 0%nat < 2%nat.
  Proof.
    auto.
  Defined.

  Lemma index1eq : forall (A : Type)(v : vector A 2%nat), 
    (Vnth v (Nat.lt_0_succ 1)) = Vnth v index1.
  Proof.
    intros. apply Vnth_eq. trivial.
  Qed.

  Definition index2 : 1%nat < 2%nat.
  Proof.
   auto.
  Defined. 

  Lemma index2eq : forall (A : Type)(v : vector A 2%nat), 
    (Vnth v (lt_n_S (Nat.lt_0_succ 0))) = Vnth v index2.
  Proof.
    intros. apply Vnth_eq. trivial.
  Qed.

  Lemma Vfold_left_Vcons_Fadd :
    forall (a : F)(n : nat)(b : VF n),
    Vfold_left Fadd Fzero (Vcons a b) = Vfold_left Fadd Fzero b + a.
  Proof. 
    intros. induction b. cbn. trivial.
    cbn. rewrite Vfold_Fadd_const.
    assert (((Fzero + a) + h) = ((Fzero + h) + a)).
    ring; auto. rewrite H. trivial.
  Qed.

  Lemma Vfold_left_Vadd_Fadd :
    forall (a : F)(n : nat)(b : VF n),
    Vfold_left Fadd Fzero (Vadd b a) = Vfold_left Fadd Fzero b + a.
  Proof. 
    intros. induction b. cbn. trivial.
    cbn. do 2 rewrite <- Vfold_Fadd_const. rewrite IHb.
    ring; auto.
  Qed.

  Lemma Vfold_left_Vadd_Fmul :
    forall (a : F)(n : nat)(b : VF n),
    Vfold_left Fmul Fone (Vadd b a) = Vfold_left Fmul Fone b * a.
  Proof. 
    intros. induction b. cbn. trivial.
    cbn. do 2 rewrite <- Vfold_Fmul_const. rewrite IHb.
    ring; auto.
  Qed.

  Lemma Vfold_left_Vapp_Fadd :
    forall (n n' : nat)(a : VF n')(b : VF n),
    Vfold_left Fadd Fzero (Vapp a b) = 
      Vfold_left Fadd Fzero a + Vfold_left Fadd Fzero b.
  Proof. 
    intros. induction a. cbn. ring; auto.
    simpl. do 2 rewrite <- Vfold_Fadd_const. rewrite IHa. ring; auto.
  Qed.
  

  Lemma Vfold_left_Vcons_Fmul :
    forall (a : F)(n : nat)(b : VF n),
    Vfold_left Fmul Fone (Vcons a b) = Vfold_left Fmul Fone b * a.
  Proof.
    intros. induction b. cbn. trivial.
    cbn. rewrite Vfold_Fmul_const.
    assert (((Fone * a) * h) = ((Fone * h) * a)).
    ring; auto.
    rewrite H. intuition. 
  Qed.

  Lemma VF_sum_VF_zero : forall n,
   VF_sum (VF_zero n) = 0.
  Proof.
    intros. induction n. cbn. trivial.
    simpl. unfold VF_sum in *. rewrite Vfold_left_Vcons_Fadd. 
    rewrite IHn. ring; auto.
  Qed.

  Lemma VF_prod_const : forall (c : F)(i j : nat),
      VF_prod (Vconst c i) * VF_prod (Vconst c j) = 
        VF_prod (Vconst c (i+j)).
  Proof.
    intros. induction i. cbn. unfold VF_prod. ring; auto.
    simpl. unfold VF_prod in *. do 2 rewrite Vfold_left_Vcons_Fmul.
    rewrite <- IHi. ring; auto.
  Qed.

  Lemma VG_prod_const_index : forall (c : F)(i j : nat),
    i = j -> VF_prod (Vconst c i) = VF_prod (Vconst c j).
  Proof.
    intros. rewrite H. trivial.
  Qed.

  Lemma VF_add_move : forall n (a b c : VF n),
    a = VF_add b c <-> VF_add a (VF_neg c) = b.
  Proof.
    intros. pose module_ring. destruct r. 
    split; intros. rewrite H. apply Veq_nth; intros. 
    do 2 rewrite Vnth_map2. rewrite Vnth_map. rewrite <- Radd_assoc.
    rewrite Ropp_def. rewrite Radd_comm. rewrite Radd_0_l.  trivial.
    rewrite <- H. apply Veq_nth; intros. do 2 rewrite Vnth_map2. 
    rewrite Vnth_map. rewrite <- Radd_assoc. rewrite <- (Radd_comm (Vnth c ip)).
    rewrite Ropp_def. rewrite Radd_comm. rewrite Radd_0_l.  trivial.
  Qed.

  Definition MF : nat -> Type := (fun x => FMatrix.matrix x x).                     
  Definition MF_id n : MF n := FMatrix.id_matrix n.
  Definition MF_col n (m : MF n) i (ip :i < n) : VF n :=
    FMatrix.get_col m ip.
  Definition MF_row n (m : MF n) i (ip :i < n) : VF n :=
    FMatrix.get_row m ip.
  Definition MF_mult n (m m':MF n) : MF n :=
    FMatrix.mat_mult m m'.
  Definition MF_trans n (m : MF n) : MF n :=
    FMatrix.mat_transpose m.
  Definition MF_CVmult n (m : MF n)(v : VF n) : VF n :=
    FMatrix.mat_vec_prod m v.
  Definition MF_VCmult n (v : VF n)(m : MF n) : VF n :=
   FMatrix.row_mat_to_vec (FMatrix.mat_mult (FMatrix.vec_to_row_mat v) m).
  Definition MF_eq n (m m' : MF n) : Prop :=
   FMatrix.mat_eqA m m'.
  Definition MF_Fscal n (m : MF n)(v : VF n) : MF n :=
    FMatrix.mat_build (fun i j ip jp => 
      Vnth (VF_mult (FMatrix.get_row m ip) v) jp).
  Definition MF_scal n (m : MF n)(a : F) : MF n :=
    FMatrix.mat_build (fun i j ip jp => 
     FMatrix.get_elem m ip jp * a).
  Definition MFisPermutation n (m : MF n) : bool :=
     bVforall (VF_an_id (n:=n)) m && bVforall (VF_an_id (n:=n)) (FMatrix.mat_transpose m).
  
  Lemma Vnth_MF_build : forall n (gen : forall i j, i < n -> j < n -> F) i
       (ip : i < n),
    Vnth (FMatrix.mat_build gen) ip = Vbuild (fun j (jp : j < n) => gen i j ip jp).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth. rewrite FMatrix.mat_build_nth.
    trivial.
  Qed.
 
  Lemma transpose_move :
    forall (n : nat)(a b : MF n),
    FMatrix.mat_transpose (MF_mult a b) = 
    MF_mult (FMatrix.mat_transpose b) (FMatrix.mat_transpose a).
  Proof.
   intros. apply Veq_nth. intros. apply Veq_nth. intros.
   rewrite FMatrix.get_elem_swap. rewrite FMatrix.mat_transpose_row_col.
   unfold FMatrix.get_row. do 2 rewrite FMatrix.mat_build_nth.
   rewrite FMatrix.mat_transpose_row_col. rewrite <- (FMatrix.mat_transpose_idem b).
   rewrite FMatrix.mat_transpose_row_col. rewrite FMatrix.mat_transpose_idem.
    rewrite FMatrix.VA.dot_product_comm. trivial.
  Qed.

  Lemma transpose_move_gen :
    forall (n m l: nat)(a : FMatrix.matrix n m)
      (b : FMatrix.matrix m l),
    FMatrix.mat_transpose (FMatrix.mat_mult a b) = 
    FMatrix.mat_mult (FMatrix.mat_transpose b) (FMatrix.mat_transpose a).
  Proof.
   intros. apply Veq_nth. intros. apply Veq_nth. intros.
   rewrite FMatrix.get_elem_swap. rewrite FMatrix.mat_transpose_row_col.
   unfold FMatrix.get_row. do 2 rewrite FMatrix.mat_build_nth.
   rewrite FMatrix.mat_transpose_row_col. rewrite <- (FMatrix.mat_transpose_idem b).
   rewrite FMatrix.mat_transpose_row_col. rewrite FMatrix.mat_transpose_idem.
    rewrite FMatrix.VA.dot_product_comm. trivial.
  Qed.
  
  (*Addational definitions thaat only make sense for the crypto we are doing*)
  Lemma reasoningAboutIndexs : forall i : nat,
     (i < 2) -> (i = 0%nat \/ i = 1%nat).
  Proof.
    intros. induction i. left. trivial. right. lia.
  Qed.

  Infix "+" := Fadd.
  Infix "*" := Fmul.
  Notation "0" := Fzero.
  Notation "1" := Fone.
  Notation "- x" :=  (Finv x).
  Notation "x - y" := (x + (- y)).
  Notation " [ x ; .. ; y ] " := (Vcons x .. (Vcons y Vnil) ..).

  Lemma InProd_Vcons :
    forall (N : nat)(a b :F)(c d : VF N),
      VF_inProd (Vcons a c) (Vcons b d) = VF_inProd c d + a*b.
  Proof.
    intros. unfold VF_inProd. unfold FMatrix.VA.dot_product. simpl.
    trivial.
  Qed.

  Lemma InProd_Vcons2 :
    forall (N : nat)(a b :F)(c d : VF N),
      VF_inProd (Vcons a c) (Vcons b d) = a*b + VF_inProd c d.
  Proof.
    intros. unfold VF_inProd. unfold FMatrix.VA.dot_product. simpl.
    destruct module_ring. apply Radd_comm.
  Qed.

  Lemma InProd_Induction :
    forall (N : nat)(a b : VF (S N)),
      VF_inProd a b = VF_inProd (Vtail a) (Vtail b) + 
        (Vhead a)*(Vhead b).
  Proof.
    intros. unfold VF_inProd. unfold FMatrix.VA.dot_product. simpl.
    trivial.
  Qed.

  Lemma InProd_Induction2 :
    forall (N : nat)(a b : VF (S N)),
      VF_inProd a b = (Vhead a)*(Vhead b) + 
        VF_inProd (Vtail a) (Vtail b).
  Proof.
    intros. unfold VF_inProd. unfold FMatrix.VA.dot_product. simpl.
    destruct module_ring. apply Radd_comm.
  Qed.

  Lemma VF_add_vcons :
    forall (N : nat)(a b : VF (1+N)),
    VF_add a b = Vcons (Vhead a + Vhead b)
        (VF_add (Vtail a) (Vtail b)).
  Proof.
    intros. cbn. trivial. 
  Qed.

  Lemma VF_scale_vcons :  forall (N :nat)(r w c : F)(r' w' : VF N),
    Vcons (r + w * c) (VF_add r' (VF_scale w' c)) = 
      VF_add (Vapp [r] r') (VF_scale (Vapp [w] w') c).
  Proof.
    intros. cbn. apply Veq_nth. intros.
    induction i. cbn. unfold FSemiRingT.Aplus. trivial.
    cbn.  rewrite Vnth_map2. unfold FSemiRingT.Aplus. auto.
  Qed.

  Lemma VF_scale_vcons2 :  forall (N :nat)(r w c : F)(r' w' : VF N),
    Vcons ((r + w) * c) (VF_scale (VF_add r' w') c) =
    VF_scale (VF_add (Vapp [r] r') (Vapp [w] w')) c.
  Proof.
    intros. cbn. apply Veq_nth. intros.
    induction i. cbn. unfold FSemiRingT.Aplus. trivial.
    cbn.  rewrite Vnth_map. unfold FSemiRingT.Aplus. auto.
  Qed.

  Lemma VF_scale_imp : forall (N :nat)(a b : VF N) c,
    a = b -> VF_scale a c = VF_scale b c.
  Proof.
    intros. rewrite H. trivial.
  Qed.

  Lemma VF_sum_induction :
    forall(N : nat)(v : VF (1+N)),
    VF_sum v = VF_sum (Vtail v) + (Vhead v).
  Proof.
    intros. remember (VF_sum (Vtail v) + Vhead v) as b.
    rewrite (VSn_eq v). rewrite Heqb. cbn. rewrite Vfold_Fadd_const.
    trivial.
  Qed.

  Lemma VF_prod_induction :
    forall (n : nat)(a : VF (S n)),
    VF_prod a = VF_prod (Vtail a) * (Vhead a).
  Proof.
    intros. rewrite (VSn_eq a). apply Vfold_left_Vcons_Fmul.
  Qed.

  Lemma VF_sum_induction2 :
    forall(N : nat)(v : VF (1+N)),
    VF_sum v = (Vhead v) + VF_sum (Vtail v).
  Proof.
    intros. remember (Vhead v + VF_sum (Vtail v)) as b.
    rewrite (VSn_eq v). rewrite Heqb. cbn. destruct module_ring.
    symmetry. rewrite Radd_comm. rewrite Vfold_Fadd_const.
    trivial.
  Qed.

   Lemma VF_sum_vcons : forall (N : nat)(a: F)(v : VF N),
    VF_sum (Vcons a v) = VF_sum v + a.
  Proof.
    intros. rewrite VF_sum_induction. simpl. trivial.
  Qed.

  Lemma Vnth_MF :
    forall (N: nat)(m m' : MF N),
    forall i (ip : i < N) j (jp : j < N), 
    Vnth (Vnth (MF_mult m m') ip) jp = 
      VF_inProd (MF_row m ip) (MF_col m' jp).
  Proof.
    intros. rewrite FMatrix.mat_mult_elem.
    unfold VF_inProd, MF_row, MF_col. 
     trivial.
  Qed.

  Lemma VF_scale_Vtail :
  forall N, forall (u :VF (S N))(a : F),
    VF_scale (Vtail u) a = Vtail (VF_scale u a).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. 
    do 2 rewrite Vnth_tail. rewrite Vnth_map. trivial.
  Qed.

  Lemma MF_Vnth_id :
    forall (n : nat)(i : nat)(ip : i < n),
    Vnth (MF_id n) ip = FMatrix.VA.id_vec ip.
  Proof.
    intros. unfold MF_id, FMatrix.id_matrix. 
    rewrite Vbuild_nth. trivial.
  Qed.

  Lemma MF_Col_id :
    forall (n : nat)(i : nat)(ip : i < n),
    MF_col (MF_id n) ip = FMatrix.VA.id_vec ip.
  Proof.
    intros. unfold MF_id, FMatrix.id_matrix. 
    apply Veq_nth. intros.  rewrite Vnth_map.
    rewrite Vbuild_nth. case_eq (i0 =? i).
    (* part 1 *)  
    intros. apply beq_nat_true in H. subst. 
    do 2 rewrite Vnth_replace. trivial.
    (* part 2 *)
    intros. apply beq_nat_false in H.
    rewrite Vnth_replace_neq. apply H.
    rewrite Vnth_replace_neq. unfold not in *.
    intros. symmetry in H0. apply H. apply H0.
    do 2 rewrite Vnth_const. trivial.
  Qed.


  Lemma Vnth_vcast : 
    forall (A : Type)(n n' j : nat)(v1 : vector A n)
    (v2 : vector A n')(hi : j <n)(hi' : j < n + n'),
    Vnth v1 hi = Vnth (Vapp v1 v2) hi'.
  Proof.
    intros. rewrite Vnth_app. destruct (le_gt_dec n j).
    lia. apply Vnth_eq. trivial.
  Qed.

  Lemma MFeq :
    forall (N : nat)(m m' : MF N),
    MF_eq m m' <-> m = m'.
  Proof.
    intros. unfold iff. refine (conj _ _).  intros. unfold MF_eq in *. 
    unfold FMatrix.mat_eqA in H. unfold FMatrix.get_elem in H. 
    apply Veq_nth. intros. unfold FMatrix.get_row in H. 
    unfold FSemiRingT.ES.Eq.eqA in H. apply Veq_nth. intros. apply H.
    (* part 2 *)
    intros. rewrite H. unfold MF_eq. unfold FMatrix.mat_eqA.
    unfold FSemiRingT.ES.Eq.eqA. intros. trivial. 
  Qed.

  Lemma MF_getRow_prod :
    forall (N :nat)(A: MF N)(rTil : VF N)(i :nat)(ip: i <N),
    Vnth (MF_CVmult A rTil) ip = 
      VF_inProd (Vnth A ip) rTil.
  Proof.
    intros. unfold MF_CVmult, FMatrix.mat_mult.
    unfold FMatrix.mat_vec_prod. unfold FMatrix.col_mat_to_vec, FMatrix.mat_mult, FMatrix.vec_to_col_mat.
    unfold FMatrix.get_col. rewrite Vnth_map.  
    rewrite FMatrix.mat_build_nth. unfold VF_inProd. apply f_equal2.
    unfold FMatrix.get_row. trivial. apply Veq_nth. intros.
    do 2 rewrite Vnth_map.  cbn. trivial.
  Qed.

  Lemma MF_getRow_prod_gen :
    forall (n n' :nat)(A: vector (VF n) n')(rTil : VF n)(i :nat)(ip: i < n'),
    Vhead (Vnth (FMatrix.mat_mult A (FMatrix.mat_transpose [rTil])) ip) = 
      VF_inProd (Vnth A ip) rTil.
  Proof.
    intros. rewrite Vhead_nth. rewrite FMatrix.mat_build_nth. unfold VF_inProd.
    unfold FMatrix.get_row. apply f_equal2; auto. rewrite FMatrix.mat_transpose_row_col.
    cbn. trivial.
  Qed.

  Lemma MF_getCol_prod :
    forall (N :nat)(A: MF N)(rTil : VF N)(i :nat)(ip: i <N),
    Vnth (MF_VCmult rTil A) ip = 
      VF_inProd rTil (MF_col A ip).
  Proof.
    intros. unfold MF_VCmult, FMatrix.mat_mult, FMatrix.row_mat_to_vec, FMatrix.get_row.
    rewrite FMatrix.mat_build_nth. unfold VF_inProd. cbn.
    unfold MF_col. trivial.
  Qed.

  Lemma MF_getCol_prod_gen :
    forall (n n' :nat)(A: vector (VF n') n)(rTil : VF n)(i :nat)(ip: i < n'),
    Vnth (Vhead (FMatrix.mat_mult [rTil] A)) ip = 
      VF_inProd rTil (FMatrix.get_col A ip).
  Proof.
    intros. rewrite Vhead_nth. rewrite FMatrix.mat_build_nth. unfold VF_inProd.
    simpl. trivial.
  Qed.

  Lemma MF_getRow_VCmul :
    forall (N :nat)(A B : MF N)(i :nat)(ip: i <N),
    Vnth (MF_mult A B) ip = MF_VCmult (Vnth A ip) B.
  Proof.
    intros. apply Veq_nth. intros. unfold MF_mult, MF_VCmult.
    unfold FMatrix.mat_mult, FMatrix.row_mat_to_vec, FMatrix.mat_mult.
    unfold FMatrix.get_row, FMatrix.vec_to_row_mat.
    do 2 rewrite FMatrix.mat_build_nth. cbn. trivial.
  Qed.

  Lemma dot_product_v :
    forall (N : nat)(a v v' : VF N),
    v = v' -> FMatrix.VA.dot_product a v = FMatrix.VA.dot_product a v'.
  Proof.
    intros. rewrite H. trivial.
  Qed.

  Lemma MF_getRow_CVmul :
    forall (N :nat)(A B : MF N)(i :nat)(ip: i <N),
    MF_col (MF_mult B A) ip = MF_CVmult B (MF_col A ip).
  Proof.
    intros. apply Veq_nth. intros. unfold MF_mult, MF_CVmult, MF_col.
    unfold FMatrix.mat_mult, FMatrix.mat_vec_prod, FMatrix.mat_mult.
    unfold FMatrix.col_mat_to_vec, FMatrix.get_col. do 2 rewrite Vnth_map.
    do 2 rewrite FMatrix.mat_build_nth. apply dot_product_v.
    unfold FMatrix.vec_to_col_mat. apply Veq_nth. intros. 
    do 4 rewrite Vnth_map. cbn. trivial.
  Qed.

   Lemma Vhead_mat_build :  forall (n m : nat)
    (gen : forall i j, i < S m -> j < n -> F),
    Vhead (FMatrix.mat_build gen) = Vbuild (fun j jp => gen 0%nat j (lt_O_Sn m) jp).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vhead_nth. rewrite FMatrix.mat_build_nth.
    rewrite Vbuild_nth. trivial.
  Qed.

  Lemma MF_getCol_CVmul :
    forall (N :nat)(A B : MF N)(i :nat)(ip: i <N),
    MF_col (MF_mult B A) ip = MF_CVmult B (MF_col A ip).
  Proof.
    intros. apply Veq_nth. intros. unfold MF_mult, MF_CVmult, MF_col.
    unfold FMatrix.mat_mult, FMatrix.mat_vec_prod, FMatrix.mat_mult.
    unfold FMatrix.col_mat_to_vec, FMatrix.get_col. do 2 rewrite Vnth_map.
    do 2 rewrite FMatrix.mat_build_nth. apply dot_product_v.
    unfold FMatrix.vec_to_col_mat. apply Veq_nth. intros. 
    do 4 rewrite Vnth_map. cbn. trivial.
  Qed.

  Lemma Id_transpose :
    forall (N :nat),
    MF_id N = FMatrix.mat_transpose (MF_id N).
  Proof.
    intros. apply MFeq. unfold MF_eq, FMatrix.mat_eqA. intros.
    unfold FSemiRingT.ES.Eq.eqA. unfold MF_id. unfold FMatrix.id_matrix.
    unfold FMatrix.mat_transpose, FMatrix.get_row. rewrite FMatrix.mat_build_elem.
    unfold FMatrix.get_elem, FMatrix.get_row. do 2 rewrite Vbuild_nth.
    unfold FMatrix.VA.id_vec. case_eq (i =? j).
    (* part 1 *)  
    intros. apply beq_nat_true in H.
    apply Veq_nth3. symmetry. apply H. apply Vreplace_pi. apply H.
    (* part 2 *)
    intros. apply beq_nat_false in H. rewrite Vnth_replace_neq. apply H.
    rewrite Vnth_replace_neq. unfold not in *. intros. symmetry in H0. 
    apply H in H0. apply H0. do 2 rewrite Vnth_const. trivial.
  Qed.

  Lemma Id_select1 :
    forall (N :nat)(m:MF N),
    forall (i j :nat)(ip : i< N)(jp : j < N),
   FMatrix.VA.dot_product (FMatrix.get_row (MF_id N) jp) 
    (FMatrix.get_col m ip) = FMatrix.get_elem m jp ip.
  Proof.
    intros. unfold MF_id.
    unfold FMatrix.get_row. unfold FMatrix.id_matrix. rewrite Vbuild_nth.
    rewrite FMatrix.VA.dot_product_id. unfold FMatrix.get_elem. rewrite FMatrix.get_elem_swap.
    trivial.
  Qed.

  Lemma Id_select2 :
    forall (N :nat)(m:MF N),
    forall (i j :nat)(ip : i< N)(jp : j < N),
   FMatrix.VA.dot_product (FMatrix.get_row m ip)
    (FMatrix.get_col (MF_id N) jp) = FMatrix.get_elem m ip jp.
  Proof.
    intros. rewrite FMatrix.VA.dot_product_comm. rewrite Id_transpose.
    rewrite FMatrix.mat_transpose_row_col. unfold MF_id.
    unfold FMatrix.get_row. unfold FMatrix.id_matrix. rewrite Vbuild_nth.
    rewrite FMatrix.VA.dot_product_id. unfold FMatrix.get_elem. rewrite FMatrix.get_elem_swap.
    trivial.
  Qed.

  Lemma Id_comm :
    forall (N :nat)(m:MF N),
    MF_mult m (MF_id N) = MF_mult (MF_id N) m.
  Proof.
    intros. rewrite <- MFeq. unfold MF_eq, FMatrix.mat_eqA, MF_mult, FMatrix.mat_mult.
    intros. do 2 rewrite FMatrix.mat_build_elem. unfold FSemiRingT.ES.Eq.eqA.
    (* Definitally happy with the proof to here. *)
    rewrite Id_select2. rewrite Id_select1. trivial.
  Qed.

  Lemma MF_one : 
    forall (N : nat)(m :MF N),
    MF_mult m (MF_id N) = m.
  Proof.
    intros. rewrite Id_comm. rewrite <- MFeq. apply FMatrix.mat_mult_id_l.
    auto.
  Qed.

  Lemma MF_assoc :
    forall (N : nat)(a b c : MF N),
    MF_mult (MF_mult a b) c = MF_mult a (MF_mult b c).
  Proof.
    intros. unfold MF_mult. symmetry. apply Veq_nth. intros. apply Veq_nth. intros.
    apply FMatrix.mat_mult_assoc.
  Qed.

  Lemma VF_add_one :
    forall (a : F),
    Vfold_left_rev Fadd 0 [a] = a.
  Proof.
    intros. cbn. ring; auto.
  Qed.

  Lemma Vnth_Vbuild_VF :
    forall (n N : nat),  forall(g : forall i, Nat.lt i (1+n)  -> (VF N)),
    forall(i : nat)(ip : i< N),
       Vmap (fun x : VF N => Vnth x ip) (Vbuild g) = 
    Vbuild (fun j jp => Vnth (g j jp) ip).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. 
    do 2 rewrite Vbuild_nth. trivial.
  Qed.

  Lemma VF_eq_corr :
    forall (n : nat)(a b : VF n),
    VF_eq a b <-> a = b.
  Proof.
    intros. unfold VF_eq. 
    refine (conj _ _). intros. apply Veq_nth.
    intros. apply (Vforall2_elim_nth ip) in H. apply H.
    intro. rewrite H. pose (Vforall2_intro_nth eq b b).
    apply v. intros. trivial.
  Qed.

  Lemma VF_beq_true : 
    forall (n : nat)(a b : VF n),
    VF_beq a b = true <-> a = b.
  Proof.
    intros. unfold VF_beq. pose (bVforall2_ok (@eq F) Fbool_eq).
    rewrite i. intros. apply F_bool_eq_corr.  apply VF_eq_corr.
  Qed.

  Lemma VF_beq_true_forall : 
    forall (n m : nat)(a b : vector (VF n) m),
    bVforall2 (VF_beq (n:=n)) a b = true <-> a = b.
  Proof.
    split; intros. apply Veq_nth. intros. apply (bVforall2_elim_nth ip) in H.
    apply VF_beq_true in H. trivial. 
    apply bVforall2_nth_intro. intros. apply VF_beq_true. rewrite H. trivial.
  Qed.

  Lemma VF_beq_false : 
    forall (n : nat)(a b : VF n),
    VF_beq a b = false <-> a <> b.
  Proof.
    intros. unfold VF_beq. refine (conj _ _). intros.
    unfold not. intros. rewrite H0 in H.
    assert (bVforall2 Fbool_eq b b = true). apply VF_beq_true.
    trivial. eapply (eq_true_false_abs (bVforall2 Fbool_eq b b));
    auto. intros. unfold not in *. apply not_true_is_false. unfold not.
    intros.  apply H. apply VF_beq_true in H0. apply H0.
  Qed.
  
  Lemma VF_eq_dec : forall n (a : VF n),
    forall y : VF n, {VF_eq a y} + {~ (VF_eq a) y}.
  Proof.
    intros. case_eq (VF_beq a y); intros. left. apply VF_eq_corr. 
    apply VF_beq_true in H. trivial. right. apply VF_beq_false in H.
     unfold not. intros. apply H. apply VF_eq_corr in H0. trivial.
  Qed.
  
  Lemma VF_dist :
    forall N : nat, forall (x y z : VF N),
      VF_mult (VF_add x y) z = VF_add (VF_mult x z)(VF_mult y z).
  Proof.
    intros. apply Veq_nth. intros. do 5 rewrite Vnth_map2.
    unfold FSemiRingT.Aplus. destruct (module_ring). apply Rdistr_l.
  Qed.

  Lemma VF_add_zero :
    forall N, forall a : VF N,
    VF_add a (VF_zero N) = a.
  Proof.
    pose (module_ring). intros. unfold VF_zero. unfold VF_add. unfold FMatrix.VA.zero_vec.
    unfold FMatrix.VA.vector_plus. apply Veq_nth. intros.
    rewrite Vnth_map2. unfold FSemiRingT.A0. rewrite Vnth_const.
    unfold FSemiRingT.Aplus. rewrite Radd_comm.
    apply r. rewrite Radd_0_l. apply r. trivial.
  Qed.

  Lemma VF_mult_one :
    forall N, forall a : VF N,
    VF_mult a (VF_one N) = a.
  Proof. 
    pose (module_ring). intros. apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vnth_const. destruct r. destruct module_ring.
    rewrite Rmul_comm. apply Rmul_1_l.
  Qed.

  Lemma VF_neg_corr :
    forall N, forall a : VF N,
    VF_add a (VF_neg a) = VF_zero N.
  Proof.
    pose (module_ring). intros. unfold VF_zero. unfold VF_add. unfold VF_neg.
    unfold FMatrix.VA.zero_vec.
    unfold FMatrix.VA.vector_plus. apply Veq_nth. intros.
    rewrite Vnth_map2. unfold FSemiRingT.A0. rewrite Vnth_const.
    unfold FSemiRingT.Aplus. rewrite Vnth_map. rewrite Ropp_def.
    apply r. trivial.
  Qed.

  Lemma VF_neg_neg : forall N (v : VF N),
    VF_neg (VF_neg v) = v.
  Proof.
    intros. apply Veq_nth. intros. do 2 rewrite Vnth_map. ring; auto.
  Qed.

  Lemma VF_neg_zero : forall N,
    VF_neg (VF_zero N) = VF_zero N.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_const.
    ring; auto.
  Qed.

  Lemma VF_sub_corr :
        forall N, forall a b : VF N,
    VF_sub a b = VF_add a (VF_neg b).
  Proof.
    intros. unfold VF_sub. trivial.
  Qed.

  Lemma VF_comm :
    forall N, forall a b : VF N,
    VF_add a b = VF_add b a.
  Proof.
    pose (module_ring). intros. unfold VF_add. apply Veq_nth. intros. 
    unfold FMatrix.VA.vector_plus. do 2 rewrite Vnth_map2.
    rewrite Radd_comm. apply r. trivial.
  Qed.

  Lemma VF_mult_ass :
    forall N, forall a b c : VF N,
    VF_mult (VF_mult a b) c = VF_mult a (VF_mult b c).
  Proof.
    pose (module_ring). intros. unfold VF_mult. apply Veq_nth. intros.
    do 4 rewrite Vnth_map2. destruct r. rewrite <- Rmul_assoc. trivial.
  Qed.

  Lemma VF_comm_mult :
    forall N, forall a b : VF N,
    VF_mult a b = VF_mult b a.
  Proof.
    pose (module_ring). intros. unfold VF_mult. apply Veq_nth. intros.
    do 2 rewrite Vnth_map2. destruct r. destruct module_ring.
   apply Rmul_comm.
  Qed.

  Lemma VF_add_ass :
    forall N, forall a b c : VF N,
    VF_add (VF_add a b) c = VF_add a (VF_add b c).
  Proof.
    pose (module_ring). intros. unfold VF_add. unfold FMatrix.VA.vector_plus.
    unfold FSemiRingT.Aplus. apply Veq_nth. intros.
    do 4 rewrite Vnth_map2. rewrite Radd_assoc. apply r. trivial.
  Qed.

  Lemma VF_comm_hack : forall N, forall a b c d : VF N,
    VF_add (VF_add a b) (VF_add c d) = VF_add (VF_add a c) (VF_add b d).
  Proof.
    intros. do 2 rewrite VF_add_ass. apply f_equal. do 2 rewrite <- VF_add_ass.
    apply f_equal2. apply VF_comm. trivial.
  Qed.

  Lemma Vfold_VFadd_const :  forall (n m : nat)
    (v : vector (VF m) n)(a : (VF m)), forall (h : (VF m)),
    VF_add (Vfold_left (VF_add (n:=m)) h v) a = Vfold_left (VF_add (n:=m)) (VF_add h a) v.
  Proof.
    intros n m v0 a. induction v0. cbn. intros. trivial. cbn. 
    intros. assert (VF_add (Vfold_left (VF_add (n:=m)) (VF_add h0 h) v0) a =
         Vfold_left (VF_add (n:=m)) (VF_add (VF_add h0 h) a) v0). apply IHv0.
    replace (VF_add (VF_add h0 a) h) with (VF_add (VF_add h0 h) a). apply H.
    rewrite VF_add_ass. replace (VF_add h a) with (VF_add a h) by apply VF_comm.
    rewrite <- VF_add_ass. trivial.
  Qed.

  Lemma Vfold_VFmul_const :  forall (n m : nat)
    (v : vector (VF m) n)(a : (VF m)), forall (h : (VF m)),
    VF_mult (Vfold_left (VF_mult (n:=m)) h v) a = 
      Vfold_left (VF_mult (n:=m)) (VF_mult h a) v.
  Proof.
    intros n m v0 a. induction v0. cbn. intros. trivial. cbn. 
    intros. assert (VF_mult (Vfold_left (VF_mult (n:=m)) (VF_mult h0 h) v0) a =
         Vfold_left (VF_mult (n:=m)) (VF_mult (VF_mult h0 h) a) v0). apply IHv0.
    replace (VF_mult (VF_mult h0 a) h) with (VF_mult (VF_mult h0 h) a). apply H.
    rewrite VF_mult_ass. replace (VF_mult h a) with (VF_mult a h) by apply VF_comm_mult.
    rewrite <- VF_mult_ass. trivial.
  Qed.

  Lemma Vfold_left_VFadd_eq :
    forall (n m : nat)(v: vector (VF n) m),
    Vfold_left_rev (VF_add (n:=n)) (VF_zero n) v = 
      Vfold_left (VF_add (n:=n)) (VF_zero n) v.
  Proof.
   intros. induction v. cbn. trivial.
   cbn. rewrite <- Vfold_VFadd_const.
   rewrite IHv. trivial.
  Qed. 

  Lemma Vfold_left_Vcons_VFadd :
    forall (n n' : nat)(a : (VF n))(b : vector (VF n) n'),
    Vfold_left (VF_add (n:=n)) (VF_zero n) (Vcons a b) =
    VF_add (Vfold_left (VF_add (n:=n)) (VF_zero n) b) a.
  Proof.
    intros. induction b. cbn. trivial.
    cbn. rewrite Vfold_VFadd_const.
    assert ((VF_add (VF_add (VF_zero n) a) h) =
     (VF_add (VF_add (VF_zero n) h) a)).
    do 2 rewrite VF_add_ass. replace (VF_add a h) with
    (VF_add h a) by apply VF_comm. trivial. rewrite H. trivial.
  Qed.

  Lemma Vfold_left_Vcons_VFmult :
    forall (n n' : nat)(a : (VF n))(b : vector (VF n) n'),
    Vfold_left (VF_mult (n:=n)) (VF_one n) (Vcons a b) =
    VF_mult (Vfold_left (VF_mult (n:=n)) (VF_one n) b) a.
  Proof.
    intros. induction b. cbn. trivial.
    cbn. rewrite Vfold_VFmul_const.
    assert ((VF_mult (VF_mult (VF_one n) a) h) =
     (VF_mult (VF_mult (VF_one n) h) a)).
    do 2 rewrite VF_mult_ass. replace (VF_mult a h) with
    (VF_mult h a) by apply VF_comm_mult. trivial. rewrite H. trivial.
  Qed.

  Lemma Vfold_left_Vadd_VFadd :
    forall (n n' : nat)(a : (VF n))(b : vector (VF n) n'),
    Vfold_left (VF_add (n:=n)) (VF_zero n) (Vadd b a) =
    VF_add (Vfold_left (VF_add (n:=n)) (VF_zero n) b) a.
  Proof.
    intros. induction b. cbn. trivial. 
    cbn. do 2 rewrite <- Vfold_VFadd_const. symmetry. rewrite VF_comm.
    rewrite <- VF_add_ass. apply f_equal2; auto. rewrite IHb. apply VF_comm.
  Qed.

  Lemma Vfold_left_Vadd_VFmul :
    forall (n n' : nat)(a : (VF n))(b : vector (VF n) n'),
    Vfold_left (VF_mult (n:=n)) (VF_one n) (Vadd b a) =
    VF_mult (Vfold_left (VF_mult (n:=n)) (VF_one n) b) a.
  Proof.
    intros. induction b. cbn. trivial. 
    cbn. do 2 rewrite <- Vfold_VFmul_const. symmetry. rewrite VF_comm_mult.
    rewrite <- VF_mult_ass. apply f_equal2; auto. rewrite IHb. apply VF_comm_mult.
  Qed.

  Lemma VF_neg_move : forall N, forall a b : VF N,
    VF_neg (VF_add a b) = VF_add (VF_neg a) (VF_neg b).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
    do 2 rewrite Vnth_map.  apply ALR.inv_dis. 
  Qed.

  Lemma VF_add_neg :
    forall N, forall a b : VF N,
    VF_add (VF_add a b) (VF_neg b) = a.
  Proof.
    intros. rewrite VF_add_ass. rewrite VF_neg_corr.
    rewrite VF_add_zero. trivial.
  Qed.

  Lemma VF_add_neg2 :
    forall N, forall a b : VF N,
    VF_add (VF_add a (VF_neg b)) b = a.
  Proof.
    intros. rewrite VF_add_ass. replace (VF_add (VF_neg b) b) with
    (VF_add b (VF_neg b)). rewrite VF_neg_corr. rewrite VF_add_zero.
    trivial. apply VF_comm.
  Qed.

  Lemma VF_add_neg3 :
    forall N, forall a b : VF N,
    VF_add b (VF_add a (VF_neg b))  = a.
  Proof.
    intros. rewrite VF_comm. apply VF_add_neg2.
  Qed.

  Lemma VF_neg_eq : forall N (a : VF N) e,
    VF_scale a (Finv e) = VF_neg (VF_scale a e).
  Proof.
    intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. cbn in *. 
    assert (forall a b : F, a * (Finv b) = Finv(a*b)). intros. ring; auto.
    apply H.
  Qed.

  Lemma VF_neg_scale : forall N (a : VF N) b,
    VF_scale (VF_neg a) b = VF_neg (VF_scale a b).
  Proof.
    intros. apply Veq_nth. intros. do 4 rewrite Vnth_map. ring; auto.
  Qed.

  Lemma VF_scale_multi : forall N (a : MF N)(b : VF N) i (ip : i < N),
    Vmap (fun v => Vnth v ip) 
      (Vmap2 (VF_scale (n:= N)) a b) =
    VF_mult (FMatrix.get_col a ip) b.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
    do 2 rewrite Vnth_map. trivial.
  Qed.
    

  Lemma VF_neg_mul : forall N (a : VF N) (b : VF N),
    VF_neg (VF_mult a b) = VF_mult (VF_neg a) b.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
    rewrite Vnth_map. ring; auto.
  Qed.

  Lemma VF_neg_sum : forall N (a : VF N),
    - VF_sum a = VF_sum (VF_neg a).
  Proof.
    intros. induction N. rewrite (Vector_0_is_nil a). cbn. ring; auto.
    rewrite (VSn_eq a). unfold VF_sum. rewrite Vfold_left_Vcons_Fadd.
    unfold VF_neg. rewrite Vcons_map. rewrite Vfold_left_Vcons_Fadd.
    unfold VF_sum in IHN. unfold VF_neg in IHN. rewrite <- IHN. ring; auto.
  Qed.

  Lemma Vnth_Vfold_left_cons_Fadd :
    forall (i n n' : nat)(v : vector (VF n) n')(h : (VF n))(ip : Nat.lt i n),
    Vnth
    (Vfold_left (VF_add (n:=n))
       (VF_add (VF_zero n) h) v) ip =
    Vnth
      (Vfold_left (VF_add (n:=n))
       (VF_zero n) v) ip + 
    Vnth h ip.
  Proof.
    intros. induction v. cbn. apply Vnth_map2. cbn.
    rewrite <- Vfold_VFadd_const. rewrite Vnth_map2.
    rewrite IHv. rewrite <- Vfold_VFadd_const. 
    rewrite Vnth_map2. destruct module_ring. 
    do 2 rewrite <- Radd_assoc.
    assert (forall a b c d, a=b -> c=d -> a + c = b + d).
    intros. rewrite H. rewrite H0. trivial. apply H.
    trivial. apply Radd_comm.
  Qed.

  Lemma Vfold_left_VF_add :
    forall (i n n' : nat)(v : vector (VF n) n')(ip : Nat.lt i n),
    Vnth (Vfold_left (VF_add (n:=n)) (VF_zero n) v) ip
      = Vfold_left Fadd Fzero 
      (Vmap (fun v => Vnth v ip) v).
  Proof.
    intros. 
    intros. induction v. cbn. rewrite Vnth_const. trivial.
    (* part 2 *)
    cbn. rewrite <- Vfold_Fadd_const. rewrite <-  IHv. 
    apply Vnth_Vfold_left_cons_Fadd.
  Qed.

  Lemma Vnth_Vfold_left_cons_Fmul :
    forall (i n n' : nat)(v : vector (VF n) n')(h : (VF n))(ip : Nat.lt i n),
    Vnth
    (Vfold_left (VF_mult (n:=n))
       (VF_mult (VF_one n) h) v) ip =
    Vnth
      (Vfold_left (VF_mult (n:=n))
       (VF_one n) v) ip *
    Vnth h ip.
  Proof.
    intros. induction v. cbn. apply Vnth_map2. cbn.
    rewrite <- Vfold_VFmul_const. rewrite Vnth_map2.
    rewrite IHv. rewrite <- Vfold_VFmul_const. 
    rewrite Vnth_map2. destruct module_ring. 
    do 2 rewrite <- Rmul_assoc. apply f_equal2; trivial.
  Qed.

  Lemma Vfold_left_VF_mult :
    forall (i n n' : nat)(v : vector (VF n) n')(ip : Nat.lt i n),
    Vnth (Vfold_left (VF_mult (n:=n)) (VF_one n) v) ip
      = Vfold_left Fmul Fone
      (Vmap (fun v => Vnth v ip) v).
  Proof.
    intros. 
    intros. induction v. cbn. rewrite Vnth_const. trivial.
    (* part 2 *)
    cbn. rewrite <- Vfold_Fmul_const. rewrite <-  IHv. 
    apply Vnth_Vfold_left_cons_Fmul.
  Qed.


  Lemma Vfold_left_Fadd_eq :
    forall (n : nat)(v : VF n),
    Vfold_left_rev Fadd 0 v = Vfold_left Fadd 0 v.
  Proof.
   intros. induction v. cbn. trivial.
   cbn. rewrite <- Vfold_Fadd_const.
   rewrite IHv. trivial.
  Qed. 

  Lemma InProd_Sum :
    forall (N: nat)(c d : VF N),
    VF_inProd c d = VF_sum (Vmap2 Fmul c d).
  Proof.
    intros. unfold VF_inProd, FMatrix.VA.dot_product,
    FSemiRingT.Amult, VF_sum, FSemiRingT.Aplus,
    FSemiRingT.A0. rewrite Vfold_left_Fadd_eq. trivial.
  Qed.

  Lemma VF_inProd_VF_one :
    forall (N : nat)(a : VF N),
    VF_inProd a (VF_one N) = VF_sum a.
  Proof.
    intros. rewrite InProd_Sum. apply f_equal. apply Veq_nth. intros.
    rewrite Vnth_map2. rewrite Vnth_const. ring; auto.
  Qed.

  Lemma MF_CVmult_breakdown :
    forall (N : nat)(A : MF N)(B : VF N),
    MF_CVmult A B = Vfold_left (VF_add (n:=N)) (VF_zero N) 
     (Vbuild (fun j jp => (VF_scale (MF_col A jp)  (Vnth B jp)))).
  Proof.
    intros. unfold MF_CVmult. unfold FMatrix.mat_vec_prod. 
    apply Veq_nth. intros. unfold VF_scale. rewrite Vfold_left_VF_add.
    rewrite FMatrix.Vnth_col_mat. rewrite FMatrix.mat_mult_spec.
    rewrite FMatrix.get_col_col_mat. unfold FMatrix.VA.dot_product.
    rewrite Vfold_left_Fadd_eq. apply Vfold_left_eq. apply Veq_nth.
    intros.  rewrite Vnth_map2. rewrite Vnth_map. rewrite Vbuild_nth.
    rewrite Vnth_map. rewrite FMatrix.get_elem_swap. trivial.
  Qed.
  
  Lemma VF_sum_add : forall (N : nat)(a b : VF N),
    Fadd (VF_sum a) (VF_sum b) = VF_sum (Vmap2 Fadd a b).
  Proof.
    intros. induction N. rewrite (Vector_0_is_nil a). 
    rewrite (Vector_0_is_nil b).  cbn. ring; auto.
    do 3 rewrite VF_sum_induction. do 3 rewrite Vhead_nth.
    rewrite Vnth_map2. rewrite <- Vtail_map2. rewrite <- IHN.
    ring_simplify. trivial.
  Qed.

  Lemma VF_prod_mult : forall (N : nat)(a b : VF N),
    Fmul (VF_prod a) (VF_prod b) = VF_prod (Vmap2 Fmul a b).
  Proof.
    intros. induction N. rewrite (Vector_0_is_nil a). 
    rewrite (Vector_0_is_nil b).  cbn. ring; auto.
    do 3 rewrite VF_prod_induction. do 3 rewrite Vhead_nth.
    rewrite Vnth_map2. rewrite <- Vtail_map2. rewrite <- IHN.
    ring_simplify. trivial.
  Qed.

  Lemma VF_sum_zero : forall (N : nat)(a : VF N),
    a = VF_zero N -> 0 = VF_sum a.
  Proof.
    intros. subst. induction N. cbn. trivial. cbn. 
    destruct module_ring. rewrite Radd_0_l. apply IHN.
  Qed.

  Lemma VF_sum_scale : forall (N : nat)(A : VF N)(a : F),
    VF_sum A * a = VF_sum (VF_scale A a).
  Proof.
    intros. induction N. rewrite (Vector_0_is_nil A). cbn. ring; auto.
    rewrite (VSn_eq A). simpl. unfold VF_sum. do 2 rewrite Vfold_left_Vcons_Fadd.
    destruct module_ring. destruct module_ring.
    rewrite Rdistr_l. rewrite IHN. trivial.  
  Qed.

  Lemma VF_scale_add : forall (n : nat)(a : F)(b c : VF n),
    VF_add (VF_scale b a) (VF_scale c a) = VF_scale (VF_add b c) a.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_map.
    rewrite Vnth_map2. unfold FSemiRingT.Aplus. destruct module_ring.
    symmetry. apply Rdistr_l.
  Qed.

  Lemma VF_scale_VF_add : forall (n m : nat)(a : F)(b : vector (VF n) m),
    VF_scale (Vfold_left (VF_add (n:=n)) (VF_zero n) b) a =
    Vfold_left (VF_add (n:=n)) (VF_zero n) (Vmap (fun x => VF_scale x a) b).
  Proof.
    intros. induction m. rewrite (Vector_0_is_nil b). cbn. apply Veq_nth.
    intros. rewrite Vnth_map. rewrite Vnth_const. ring; auto.
    (* main  *)
    rewrite (VSn_eq (Vmap ((VF_scale (n:=n))^~ a) b)).  rewrite Vfold_left_Vcons_VFadd.
    rewrite <-  Vmap_tail. rewrite <- IHm. rewrite Vhead_map.
    rewrite VF_scale_add. rewrite <- Vfold_left_Vcons_VFadd. rewrite <- VSn_eq.
    trivial. 
  Qed. 

  Lemma MF_CVmult_MF_CVmult_test
     : forall (N : nat)(B U' : MF N)(rStar : VF N),
    MF_CVmult B (MF_CVmult U' rStar) = MF_CVmult (MF_mult B U') rStar.
  Proof.
    intros. unfold MF_CVmult. unfold FMatrix.mat_vec_prod.
    rewrite FMatrix.vec_to_col_mat_idem. 
    assert(forall( A C : FMatrix.col_mat N), A = C -> FMatrix.col_mat_to_vec A =
    FMatrix.col_mat_to_vec C). intros.  rewrite H. trivial.
    apply H. symmetry. apply FMatrix.mat_eq. intros. unfold MF_mult.
    rewrite <- FMatrix.mat_mult_assoc. trivial.
  Qed.

  Lemma MF_VCmult_MF_VCmult_test
     : forall (N : nat)(B U' : MF N)(rStar : VF N),
    MF_VCmult (MF_VCmult rStar U') B = MF_VCmult rStar (MF_mult U' B).
  Proof.
    intros. unfold MF_VCmult. rewrite FMatrix.vec_to_row_mat_idem. apply f_equal. 
    apply FMatrix.mat_eq. intros. unfold MF_mult.
    rewrite <- FMatrix.mat_mult_assoc. trivial.
  Qed.

  Lemma VF_scale_mult : forall (n : nat)(a : F)(b c : VF  n),
    VF_scale (VF_mult b c) a =  VF_mult (VF_scale b a) c.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
    rewrite Vnth_map. ring; auto.  
  Qed.

  Lemma invEq : forall (n : nat)(X Y Y' : MF n),
  MF_mult X Y = MF_id n ->
  MF_mult Y' X = MF_id n ->
  Y = Y'.
  Proof. 
    intros. rewrite <- MF_one. rewrite <- H. rewrite <- MF_assoc.
    rewrite H0. rewrite <- Id_comm. rewrite MF_one. trivial.
  Qed.

   Lemma Vfold_left_add :
    forall (n nM : nat)(messages : vector (VF nM) (1+n)),
    (Vfold_left_rev (VF_add (n:=nM))
       (VF_zero (nM)) messages) = VF_add (Vfold_left_rev (VF_add (n:=nM))
       (VF_zero (nM)) (Vtail messages)) (Vhead messages).
  Proof.
    intros. do 2 rewrite Vfold_left_VFadd_eq. induction n.
    rewrite (VSn_eq messages). rewrite (Vector_0_is_nil (Vtail messages)). 
    cbn. trivial. (* part 1 complete yay *)
     rewrite (VSn_eq messages). cbn.
    rewrite <- Vfold_VFadd_const. rewrite IHn. trivial.
  Qed.

  Lemma VF_scale_0 : forall (N:nat)(r : VF N),
    VF_scale r 0 = VF_zero N.
  Proof.
    intros. apply Veq_nth. intros.
    rewrite Vnth_map. rewrite Vnth_const.
    ring; auto.
  Qed.

  Lemma VF_scale_1 : forall (N:nat)(r : VF N),
    VF_scale r 1 = r.
  Proof.
    intros. apply Veq_nth. intros.
    rewrite Vnth_map.
    ring; auto.
  Qed.

  Lemma VF_scale_1_map : forall n m (A : vector (VF m) n),
    Vmap2 (VF_scale (n:=m)) A (VF_one n) = A.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_const. 
    apply VF_scale_1.
  Qed.

  Lemma VF_scale_1_gen : forall (N:nat)(r : VF N) a,
    a = 1 ->
    VF_scale r a = r.
  Proof.
    intros. subst. apply VF_scale_1.
  Qed.

  Lemma VF_scale_map2 : forall n m (A : vector (VF m) n) (B C : VF n),
     Vmap2 (VF_scale (n:=m)) (Vmap2 (VF_scale (n:=m)) A B) C =
     Vmap2 (VF_scale (n:=m)) A (VF_mult B C).
  Proof.
    intros. apply Veq_nth. intros. do 4 rewrite Vnth_map2. apply Veq_nth.
    intros. do 3 rewrite Vnth_map. ring; auto.
  Qed.

  Lemma VF_scale_scale : forall n (v : VF n) a b,
    VF_scale (VF_scale v a) b = VF_scale v (a*b).
  Proof.
    intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. ring; auto.
  Qed.

  Lemma VF_scale_map_com : forall n m (A : vector (VF m) n) (B: VF n) a,
    Vmap (fun x => VF_scale x a) (Vmap2 (VF_scale (n:=m)) A B) = 
    Vmap2 (VF_scale (n:=m)) A (VF_scale B a).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
    rewrite Vnth_map. apply Veq_nth. intros. do 3 rewrite Vnth_map. ring; auto. 
  Qed.  

  Lemma VF_scale_map : forall n m (A : vector (VF m) n) b c,
    Vmap (fun x => VF_scale x b) (Vmap (fun x => VF_scale x c) A) =
    Vmap (fun x => VF_scale x (b*c)) A.
  Proof.
    intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. apply Veq_nth. intros.
    do 3 rewrite Vnth_map. ring; auto.
  Qed.

  Lemma VF_prod_1  :
    forall (v : F),
      VF_prod [v] = v.
  Proof.
    intros. cbn. ring; auto.
  Qed.

  Lemma VF_prod_1_head  :
    forall (v : VF 1),
      VF_prod v = Vhead v.
  Proof.
    intros. rewrite (VSn_eq v).
    rewrite (Vector_0_is_nil (Vtail v)).
    rewrite VF_prod_1. symmetry. 
    rewrite Vhead_nth. cbn. trivial.
  Qed.

  Lemma VF_prod_2_head  :
    forall (v : VF 2),
      VF_prod v = Vhead v * Vhead (Vtail v).
  Proof.
    intros. rewrite (VSn_eq v). rewrite (VSn_eq (Vtail v)).
    rewrite (Vector_0_is_nil (Vtail (Vtail v))). cbn.
    ring; auto.
  Qed.

  Lemma VF_prod_1_head_gen  :
    forall n (v : VF (S n)),
      n = 0%nat ->
      VF_prod v = Vhead v.
  Proof.
    intros. subst. apply VF_prod_1_head.
  Qed.


  Lemma Vmap_prod_1 :
    forall n (v : vector (VF 1) n),
    Vmap (VF_prod (n:=1)) v = 
      Vhead (FMatrix.mat_transpose v).
  Proof.
    intros. apply Veq_nth. intros. 
    rewrite Vnth_map. rewrite Vhead_nth.
    pose FMatrix.mat_transpose_col_row.
    unfold FMatrix.get_row in e. rewrite e.
    rewrite <- FMatrix.get_elem_swap.
    unfold FMatrix.get_row. 
    rewrite VF_prod_1_head. rewrite Vhead_nth.
    trivial.
  Qed.

  Lemma VF_sum_1  :
    forall (v : F),
      VF_sum [v] = v.
  Proof.
    intros. cbn. ring; auto.
  Qed.

  Lemma VF_sum_1_head  :
    forall (v : VF 1),
      VF_sum v = Vhead v.
  Proof.
    intros. rewrite (VSn_eq v).
    rewrite (Vector_0_is_nil (Vtail v)).
    rewrite VF_sum_1. symmetry. 
    rewrite Vhead_nth. cbn. trivial.
  Qed.

  Lemma VF_sum_vadd_1_head  :
    forall (n : nat)(v : vector (VF n) 1),
      Vfold_left (VF_add (n:=n)) (VF_zero n) v = Vhead v.
  Proof.
    intros. rewrite (VSn_eq v).
    rewrite (Vector_0_is_nil (Vtail v)).
    cbn. rewrite VF_comm. rewrite VF_add_zero. trivial. 
  Qed.

  Lemma VF_Fadd_dist : forall n m (a: VF n)(B : vector (VF n) m),
    VF_mult a (Vfold_left (VF_add (n:=n)) (VF_zero n) B) =
      Vfold_left (VF_add (n:=n)) (VF_zero n) (Vmap (VF_mult a) B).
  Proof.
    intros. induction m. rewrite (Vector_0_is_nil B). cbn.
    apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_const. ring; auto.
    rewrite (VSn_eq B). rewrite Vcons_map. do 2 rewrite Vfold_left_Vcons_VFadd.
    rewrite <- IHm. rewrite VF_comm_mult. rewrite VF_dist. apply f_equal2.
    apply VF_comm_mult. apply VF_comm_mult.
  Qed.

  Lemma VF_prod_vmult_1_head  :
    forall (n : nat)(v : vector (VF n) 1),
      Vfold_left (VF_mult (n:=n)) (VF_one n) v = Vhead v.
  Proof.
    intros. rewrite (VSn_eq v).
    rewrite (Vector_0_is_nil (Vtail v)).
    cbn. rewrite VF_comm_mult. rewrite VF_mult_one. trivial. 
  Qed.

  Lemma VF_sum_sum : forall n m (B : vector (VF n) m),
    VF_sum (Vfold_left (VF_add (n:=n)) (VF_zero n) B) =
    VF_sum (Vmap (VF_sum (n:=n)) B).
  Proof.
    intros. induction m. rewrite (Vector_0_is_nil B). cbn. pose VF_sum_VF_zero.
    unfold VF_sum in e. apply e. unfold VF_sum in *. rewrite (VSn_eq B). 
    rewrite Vcons_map. rewrite Vfold_left_Vcons_Fadd. rewrite <- IHm. 
    rewrite Vfold_left_Vcons_VFadd. rewrite VF_sum_add. unfold VF_sum. trivial.
  Qed.

  Lemma Vmap_sum_1 :
    forall n (v : vector (VF 1) n),
    Vmap (VF_sum (n:=1)) v = 
      Vhead (FMatrix.mat_transpose v).
  Proof.
    intros. apply Veq_nth. intros. 
    rewrite Vnth_map. rewrite Vhead_nth.
    pose FMatrix.mat_transpose_col_row.
    unfold FMatrix.get_row in e. rewrite e.
    rewrite <- FMatrix.get_elem_swap.
    unfold FMatrix.get_row. 
    rewrite VF_sum_1_head. rewrite Vhead_nth.
    trivial.
  Qed.

  Lemma Vmap2_VF_add_assoc : forall n j (a b c : vector (VF n) j),
    Vmap2 (VF_add (n:=n)) (Vmap2 (VF_add (n:=n)) a b) c =
    Vmap2 (VF_add (n:=n)) a (Vmap2 (VF_add (n:=n)) b c).
  Proof.
    intros. apply Veq_nth. intros. do 4 rewrite Vnth_map2. apply VF_add_ass.
  Qed.

  Lemma Vmap2_VF_add_comm : forall n j (a b : vector (VF n) j),
    Vmap2 (VF_add (n:=n)) a b = Vmap2 (VF_add (n:=n)) b a.
  Proof.
    intros. apply Veq_nth. intros. do 2 rewrite Vnth_map2. apply VF_comm.
  Qed.
  
  Lemma Vfold_VFadd_vector_const :
    forall n j i (c : vector (vector (VF n) j) i)
      (a b : vector (VF n) j),
    Vfold_left (fun x y : vector (VF n) j =>
   Vmap2 (VF_add (n:=n)) x y)
   (Vmap2 (VF_add (n:=n)) a b) c =
  Vmap2 (VF_add (n:=n)) (Vfold_left
     (fun x : vector (VF n) j =>
      [eta Vmap2 (VF_add (n:=n)) x]) a c) b.
  Proof.
    induction c. simpl. trivial. simpl. intros. 
    assert (Vmap2 (VF_add (n:=n))
     (Vmap2 (VF_add (n:=n)) a b) h = Vmap2 (VF_add (n:=n))
     (Vmap2 (VF_add (n:=n)) a h) b). rewrite (Vmap2_VF_add_comm a b). 
    rewrite Vmap2_VF_add_assoc. rewrite Vmap2_VF_add_comm. trivial. 
    rewrite H. rewrite IHc. trivial.
  Qed.

  Lemma mat_mult_assoc_gen :
    forall n n' n'' n''' (m : FMatrix.matrix n n')
    (m' : FMatrix.matrix n' n'')(m'' : FMatrix.matrix n'' n'''),
      FMatrix.mat_mult (FMatrix.mat_mult m m') m'' =
      FMatrix.mat_mult m (FMatrix.mat_mult m' m'').
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. 
    pose FMatrix.mat_mult_assoc. unfold FMatrix.mat_eqA in m0.
    unfold FMatrix.get_elem, FMatrix.get_row in m0. rewrite m0.
    trivial.
  Qed.

  Lemma mat_mult_id_l :
     forall n n' (m : FMatrix.matrix n n'),
     FMatrix.mat_mult (FMatrix.id_matrix n) m =
     m.
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. 
    unfold FMatrix.id_matrix. rewrite FMatrix.mat_mult_elem.
    unfold FMatrix.get_row. rewrite Vbuild_nth.
    rewrite (FMatrix.VA.dot_product_id ip).
    rewrite FMatrix.get_elem_swap. trivial.
  Qed.

  Lemma mat_mult_id_r :
     forall n n' (m : FMatrix.matrix n n'),
     FMatrix.mat_mult m (FMatrix.id_matrix n') =
     m.
  Proof.
    intros. symmetry. rewrite <- FMatrix.mat_transpose_idem. 
    rewrite transpose_move_gen. pose Id_transpose. unfold MF_id in *.
    rewrite <- e. rewrite mat_mult_id_l. rewrite FMatrix.mat_transpose_idem.
    trivial.
  Qed.

  Lemma scale_mult : forall n n' (a : VF n')(b : vector (VF n) n'),
    Vmap2 (VF_scale (n:=n)) b a = 
      FMatrix.mat_transpose (Vmap (VF_mult a) (FMatrix.mat_transpose b)).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. rewrite FMatrix.mat_build_nth.
    rewrite Vnth_map2. rewrite Vnth_map. unfold FMatrix.get_elem. unfold FMatrix.get_row.
    rewrite Vnth_map. rewrite Vnth_map2. rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_elem. unfold FMatrix.get_row. destruct module_ring.
    apply Rmul_comm.
  Qed.

  Lemma Fmatrix_mult_vnth : forall n n' n'' (a : vector (VF n) n')
      (b : vector (VF n'') n) i (ip : i < n') ,
    Vnth (FMatrix.mat_mult a b) ip = Vhead (FMatrix.mat_mult [(Vnth a ip)] b).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vhead_nth. rewrite FMatrix.mat_build_nth.
    rewrite FMatrix.mat_build_nth. simpl. unfold FMatrix.get_row. trivial.
  Qed.

  Lemma mat_mult_rev : forall n n' n'' (a : vector (VF n) n')(b : vector (VF n'') n),
  FMatrix.mat_mult (rev a) b = rev (FMatrix.mat_mult a b).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros.
    rewrite Vbuild_nth. do 2 rewrite FMatrix.mat_mult_elem. unfold FMatrix.get_row.
    rewrite Vbuild_nth. trivial.
  Qed.

  Lemma VF_add_transpose : forall n n' (a : vector (VF n) n'),
     Vfold_left (VF_add (n:=n')) (VF_zero n') (FMatrix.mat_transpose a) =
     Vmap (VF_sum (n:=n)) a.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. rewrite Vfold_left_VF_add.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_map. rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_elem. trivial.
  Qed.

  Lemma Vhead_mat_mult : forall n n' n'' (a : vector (VF n) (S n'))(b: vector (VF n'') n),
    [Vhead (FMatrix.mat_mult a b)] = FMatrix.mat_mult [Vhead a] b.
  Proof.
    intros. assert (forall j (a : VF j)(b : vector (VF j) 1),
       a = Vhead b -> [a] = b). intros. rewrite H. apply Veq_nth. intros.
    assert (i = 0%nat). lia. subst. simpl. rewrite Vhead_nth. apply Vnth_eq.
    trivial. apply H. do 2 rewrite Vhead_nth. apply Veq_nth. intros. 
    do 2 rewrite FMatrix.mat_build_nth. cbn. rewrite Vhead_nth. unfold FMatrix.get_row. trivial.
  Qed.

  Lemma mat_mult_rev2 : forall n n' n'' (a : vector (VF n) n')(b : vector (VF n'') n),
  FMatrix.mat_mult a (Vmap (fun x => rev x) b)  = Vmap (fun x => rev x)
     (FMatrix.mat_mult a b).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. rewrite Vnth_map.
    rewrite Vbuild_nth. do 2 rewrite FMatrix.mat_mult_elem. apply f_equal; auto.
   unfold FMatrix.get_row. apply Veq_nth. intros. do 3 rewrite Vnth_map.
    rewrite Vbuild_nth. trivial. 
  Qed.

  Lemma rev_col : forall n n' (a : vector (VF n) (S n')) i (ip : i < n),
    FMatrix.get_col (rev a) ip = rev (FMatrix.get_col a ip).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth. do 2 rewrite Vnth_map.
    rewrite Vbuild_nth. trivial.
  Qed.

  Lemma VF_mult_zero : forall n (a : VF n),
    VF_mult (VF_zero n) a = VF_zero n.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_const.
    ring; auto.
  Qed.

  Lemma VF_sum_dist : forall n n' n'' (a : vector (VF n) n')(b : vector (VF n) n''),
  Vfold_left (VF_add (n:=n)) (VF_zero n)
  (Vmap [eta Vfold_left (VF_add (n:=n)) (VF_zero n)]
     (Vbuild  (fun (i : nat) (ip : i < n') =>
  Vbuild (fun (j : nat) (jp : j < n'') => VF_mult (Vnth a ip) (Vnth b jp))))) =
  VF_mult (Vfold_left (VF_add (n:=n)) (VF_zero n) a)
  (Vfold_left (VF_add (n:=n)) (VF_zero n) b).
  Proof.
    intros. induction n'. rewrite (Vector_0_is_nil a). simpl.
    rewrite VF_mult_zero. trivial.
    (* Inductive case *)
    intros. rewrite (VSn_eq a). rewrite Vfold_left_Vcons_VFadd. rewrite VF_dist.
    rewrite <- IHn'. rewrite <- Vfold_left_Vcons_VFadd. apply f_equal.
    rewrite VF_Fadd_dist. rewrite <- Vcons_map. apply Veq_nth. intros.
    do 2 rewrite Vnth_map. apply f_equal. rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    do 2 rewrite Vbuild_nth. rewrite Vnth_cons. destruct (lt_ge_dec 0 i). apply Veq_nth.
    intros. do 2 rewrite Vbuild_nth. apply f_equal2; auto. apply Vnth_eq. trivial.
    assert (False). lia. contradiction. rewrite Vbuild_nth. apply Veq_nth. intros.
    rewrite Vbuild_nth. rewrite Vnth_map. rewrite <- VSn_eq. rewrite Vhead_nth.
    apply f_equal2; auto. apply Vnth_eq. lia.
  Qed. 

  Lemma  Vfold_left_vcons_cancel : forall n n' (a : VF n)(b : vector (VF n) n')
    (c : VF (S n')),
  Vhead c = 1 -> VF_sub 
  (Vfold_left (VF_add (n:=n)) (VF_zero n)
     (Vmap2 (VF_scale (n:=n)) (Vcons a b) c))
  (Vfold_left (VF_add (n:=n)) (VF_zero n)
     (Vmap2 (VF_scale (n:=n)) b (Vtail c))) = a.
  Proof.
    intros. rewrite (VSn_eq c). rewrite Vcons_map2. rewrite Vfold_left_Vcons_VFadd. 
    rewrite <- VSn_eq. unfold VF_sub. assert (forall n (a b c :  VF n), VF_add (VF_add a b) c =
    VF_add b (VF_add a c)). intros. rewrite <- VF_add_ass. apply f_equal2; auto.
    apply VF_comm. rewrite H0. rewrite VF_neg_corr. rewrite VF_add_zero.
    rewrite H. rewrite VF_scale_1. trivial.
  Qed.

  Lemma  Vfold_left_vadd_cancel : forall n n' (a : VF n)(b : vector (VF n) n')
    (c : VF (S n')),
  Vhead c = 1 -> VF_sub 
  (Vfold_left (VF_add (n:=n)) (VF_zero n)
     (Vmap2 (VF_scale (n:=n)) (Vadd b a) (rev c)))
  (Vfold_left (VF_add (n:=n)) (VF_zero n)
     (Vmap2 (VF_scale (n:=n)) b (rev (Vtail c)))) = a.
  Proof.
    intros. pose VF_comm. pose VF_add_ass. rewrite Vfold_left_eq_rev; auto.
    rewrite rev_vmap2. rewrite <- Vcons_rev. rewrite rev_rev. remember (Vfold_left (VF_add (n:=n)) (VF_zero n)
     (Vmap2 (VF_scale (n:=n)) (Vcons a (rev b)) c)) as d.
    rewrite Vfold_left_eq_rev; auto. rewrite rev_vmap2. rewrite rev_rev.
    rewrite Heqd. apply Vfold_left_vcons_cancel; auto.
  Qed.

  Lemma VF_sum_vcons_cancel : forall n (a : F)(b : VF n)(c : VF (S n)),
    Vhead c = 1 -> 
    VF_sum (VF_mult c (Vcons a b)) -
    VF_sum (VF_mult (Vtail c) b) = a.
  Proof.
    intros. rewrite (VSn_eq c). unfold VF_mult. rewrite Vcons_map2.
    rewrite VF_sum_vcons. rewrite <- VSn_eq. rewrite H. ring; auto.
  Qed.

  Lemma VF_sum_vcons_cancel_gen : forall n (a c1 : VF (S n))(b c2: VF n),
    Vhead c1 = 1 ->
    Vtail c1 = c2 ->
    Vtail a = b ->
    Vfold_left Fadd 0 (Vmap2 Fmul a c1) - Vfold_left Fadd 0 (Vmap2 Fmul b c2) = 
      (Vhead a). 
  Proof.
    intros. rewrite (VSn_eq a). pose VF_sum_vcons_cancel. pose VF_comm_mult.
    unfold VF_sum, VF_mult in *. rewrite H1. rewrite e0. rewrite (e0 n b).
    rewrite <- H0. rewrite e; auto. 
  Qed.

  Lemma VF_sum_vadd_cancel : forall n (a : F)(b : VF n)(c : VF (S n)),
    Vhead c = 1 -> 
    VF_sum (VF_mult (rev c) (Vadd b a)) -
      VF_sum (VF_mult (rev (Vtail c)) b) = a.
  Proof.
    intros. unfold VF_sum. rewrite Vfold_left_eq_rev; intros. ring; auto.
    ring; auto. rewrite rev_vmap2. rewrite <- Vcons_rev. rewrite rev_rev.
    remember (Vfold_left Fadd 0 (Vmap2 Fmul c (Vcons a (rev b)))) as d.
    rewrite Vfold_left_eq_rev; intros. ring; auto. ring; auto.
    rewrite rev_vmap2. rewrite rev_rev. rewrite Heqd. apply VF_sum_vcons_cancel; auto.
  Qed.

  Lemma Vfold_left_vsub_cancel : forall n n' (a : VF n)(b : vector (VF n) n')(c : VF (S n')),
    Vhead c = 1 ->    
    Vfold_left (VF_add (n:=n)) (VF_zero n) (Vmap2 (VF_scale (n:=n)) 
      (Vcons  (VF_sub a (Vfold_left (VF_add (n:=n)) (VF_zero n)
      (Vmap2 (VF_scale (n:=n)) b (Vtail c)))) b) 
    c) = a.
  Proof.
    intros. rewrite (VSn_eq c). rewrite Vcons_map2. rewrite <- VSn_eq. rewrite H.
    rewrite VF_scale_1. rewrite Vfold_left_Vcons_VFadd. rewrite VF_sub_corr. rewrite VF_comm.
    rewrite VF_add_ass. assert (forall c, VF_add (VF_neg c) c  = VF_zero n). intros.
    rewrite VF_comm. apply VF_neg_corr. rewrite H0. apply VF_add_zero. 
  Qed.

  Lemma VF_sum_vsub_cancel : forall n' (a : F)(b : VF n')(c : VF (S n')),
     Vhead c = 1 ->    
     VF_sum (VF_mult c
      (Vcons (a - (VF_sum (VF_mult (Vtail c) b))) b)) = a.
  Proof.
    intros. rewrite (VSn_eq c). unfold VF_mult. rewrite Vcons_map2. rewrite <- VSn_eq. rewrite H.
    assert (forall d, 1 * d = d). intros. ring; auto. rewrite H0.
    rewrite VF_sum_vcons. ring; auto.
  Qed. 

  Lemma VF_sum_vsub_cancel_gen : forall n' (a : F)(b b' : VF n')(c : VF (S n')),
     Vhead c = 1 ->    
     b = b' ->
     VF_sum (VF_mult c
      (Vcons (a - (VF_sum (VF_mult (Vtail c) b))) b')) = a.
  Proof.
    intros. rewrite H0. rewrite (VSn_eq c). unfold VF_mult. rewrite Vcons_map2. 
    rewrite <- VSn_eq. rewrite H. assert (forall d, 1 * d = d). intros. ring; auto.
    rewrite H1. rewrite VF_sum_vcons. ring; auto.
  Qed. 
    
  Lemma Vfold_left_vsub_add_cancel : forall n n' (a : VF n)(b : vector (VF n) n')(c : VF (S n')),
    Vhead c = 1 ->    
    Vfold_left (VF_add (n:=n)) (VF_zero n) (Vmap2 (VF_scale (n:=n)) 
      (Vadd b (VF_sub a (Vfold_left (VF_add (n:=n)) (VF_zero n)
      (Vmap2 (VF_scale (n:=n)) b (rev (Vtail c)))))) 
    (rev c)) = a.
  Proof.
    intros. pose VF_comm. pose VF_add_ass. rewrite Vfold_left_eq_rev; auto.
    rewrite rev_vmap2.  rewrite <- Vcons_rev.  rewrite rev_rev. 
    remember (Vfold_left (VF_add (n:=n)) (VF_zero n)) as d.
    rewrite Vfold_left_eq_rev; auto. rewrite rev_vmap2. rewrite rev_rev. 
    rewrite  Heqd. apply Vfold_left_vsub_cancel; auto.
  Qed.

  Lemma VF_sum_vsub_add_cancel : forall n' (a : F)(b : VF n')(c : VF (S n')),
     Vhead c = 1 ->    
     VF_sum (VF_mult (rev c)
      (Vadd b (a - (VF_sum (VF_mult (rev (Vtail c)) b))))) = a.
  Proof.
    intros. unfold VF_sum. rewrite Vfold_left_eq_rev; intros. ring; auto.
    ring; auto. rewrite rev_vmap2. rewrite <- Vcons_rev. rewrite rev_rev.
    remember (Vfold_left Fadd 0) as d.
    rewrite Vfold_left_eq_rev; intros. ring; auto. ring; auto.
    rewrite rev_vmap2. rewrite rev_rev. rewrite Heqd. apply VF_sum_vsub_cancel; auto.
  Qed. 

  Lemma VF_mat_cancel : forall n n' (a : VF (S n))(b : VF n')(c : vector (VF n') n),
    Vhead a = 1 ->
      VF_add (Vhead (FMatrix.mat_mult [a] (Vcons b c)))
    (VF_neg (Vhead (FMatrix.mat_mult [Vtail (a)] c))) = b.
  Proof.
    intros. apply Veq_nth. intros. 
    rewrite Vnth_map2. rewrite Vnth_map. do 2 rewrite MF_getCol_prod_gen.
    unfold FSemiRingT.Aplus. do 2 rewrite InProd_Sum. pose VF_comm_mult.
    unfold VF_mult in e. rewrite e. rewrite (e n (Vtail a)).
   rewrite VF_sum_vcons_cancel_gen; auto.
  Qed.
  
  Lemma VF_mat_cancel_rev : forall n n' (a : VF (S n))(b : VF n')(c : vector (VF n') n),
    Vhead a = 1 ->
    Vhead (FMatrix.mat_mult [a] (Vcons (VF_sub b
     (Vhead (FMatrix.mat_mult [Vtail (a)] c))) c)) = b.
  Proof.
    intros. apply Veq_nth. intros. rewrite MF_getCol_prod_gen.
    assert (FMatrix.get_col (Vcons (VF_sub b (Vhead (FMatrix.mat_mult [Vtail a] c))) c) ip
    = Vcons (Vnth b ip - VF_inProd (Vtail a) (FMatrix.get_col c ip)) (FMatrix.get_col c ip)).
    apply Veq_nth. intros. rewrite Vnth_map. do 2  rewrite Vnth_cons. 
    destruct (lt_ge_dec 0 i0). rewrite Vnth_map. trivial. unfold VF_sub. 
    rewrite Vnth_map2. rewrite Vnth_map. rewrite MF_getCol_prod_gen. trivial.
    rewrite H0. do 2 rewrite InProd_Sum. rewrite VF_sum_vsub_cancel; auto.
  Qed. 

  Lemma VF_sum_id : forall n i (ip : i < n),
    Vfold_left Fadd Fzero (FMatrix.VA.id_vec ip) = 1.
  Proof.
    induction n. lia. destruct i; intros. rewrite Vfold_left_Vcons_Fadd.
    pose VF_sum_VF_zero. unfold VF_sum in e. rewrite e. unfold FSemiRingT.A1.
    ring; auto. unfold FMatrix.VA.id_vec. rewrite Vreplace_tail. 
    rewrite Vfold_left_Vcons_Fadd. unfold FMatrix.VA.zero_vec. rewrite Vtail_const.
    rewrite IHn. rewrite Vhead_const. unfold FSemiRingT.A0. ring; auto.
  Qed.

  Lemma permutationSum : forall n (m : MF n),
    MFisPermutation m ->
    Vfold_left (VF_add (n:=n)) (VF_zero (n)) m = VF_one (n).
  Proof.
    intros. unfold MFisPermutation in H. apply andb_true_iff in H.
    destruct H. apply Veq_nth. intros. rewrite Vfold_left_VF_add.
    apply (bVforall_elim_nth ip) in H0. unfold VF_an_id  in H0.
    apply bVexists_eq in H0. elim H0. intros. elim H1. intros.
    (* We know the id *)
    apply VF_beq_true in H2. rewrite Vnth_MF_build in H2. 
     assert (Vmap (fun v : vector F n => Vnth v ip) m =
    Vbuild (fun j : nat => (FMatrix.get_elem m (j:=i))^~ ip)). intros.
    apply Veq_nth. intros. rewrite Vnth_map. rewrite Vbuild_nth. trivial.
    rewrite H3. rewrite H2. rewrite Vbuild_nth. rewrite VF_sum_id.
    rewrite Vnth_const. trivial.
  Qed.

  Lemma MF_trans_sub : forall n (m: MF (S n)),
    MF_trans (Vmap [eta Vremove_last (n:=n)] (Vtail m)) =
    Vmap [eta Vtail (n:=n)] (Vremove_last (MF_trans m)).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. rewrite Vnth_map.
    rewrite Vnth_remove_last. rewrite Vnth_tail. do 2 rewrite FMatrix.mat_build_nth. 
    unfold FMatrix.get_elem, FMatrix.get_row. rewrite Vnth_map.
    rewrite Vnth_remove_last. rewrite Vnth_tail. trivial.
  Qed.

  Lemma MF_trans_sub2 : forall n (m: MF (S n)),
    Vmap [eta Vremove_last (n:=n)] (Vtail (MF_trans m)) =
    MF_trans (Vmap [eta Vtail (n:=n)] (Vremove_last m)).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. rewrite Vnth_map.
    rewrite Vnth_remove_last. rewrite Vnth_tail. do 2 rewrite FMatrix.mat_build_nth. 
    unfold FMatrix.get_elem, FMatrix.get_row. rewrite Vnth_map.
    rewrite Vnth_remove_last. rewrite Vnth_tail. trivial.
  Qed.

  Lemma MF_trans_sub3 : forall n (m: MF (S n)),
    MF_trans (Vmap [eta Vtail (n:=n)] (Vtail m)) =
    Vmap [eta Vtail (n:=n)] (Vtail (MF_trans m)).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. rewrite Vnth_map.
    do 2 rewrite Vnth_tail. do 2 rewrite FMatrix.mat_build_nth. 
    unfold FMatrix.get_elem, FMatrix.get_row. rewrite Vnth_map.
    rewrite Vnth_tail. rewrite Vnth_tail. trivial.
  Qed.

  Lemma MF_trans_sub4 : forall n n' (m: FMatrix.matrix n (S n')),
    FMatrix.mat_transpose (Vmap [eta Vremove_last (n:=n')] m) = 
    Vremove_last (FMatrix.mat_transpose m).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. rewrite Vnth_remove_last.
    do 2 rewrite FMatrix.mat_build_nth. unfold FMatrix.get_elem, FMatrix.get_row.
    rewrite Vnth_map. rewrite Vnth_remove_last. trivial.
  Qed.

  Lemma MF_perm_inv : forall n (m : MF n),
    MFisPermutation m ->
    MFisPermutation (MF_trans m).
  Proof.
    intros. unfold MFisPermutation in *. rewrite FMatrix.mat_transpose_idem.
    apply andb_true_iff in H. apply andb_true_iff. destruct H. split; trivial.
  Qed.

  Lemma MF_not_perm_inv : forall n (m : MF n),
    MFisPermutation m = false ->
    MFisPermutation (MF_trans m) = false.
  Proof.
    intros. apply not_true_iff_false in H. apply not_true_iff_false.
    unfold not; intros. apply H. rewrite <- (FMatrix.mat_transpose_idem m).
    apply MF_perm_inv. apply H0.
  Qed.

  Lemma Vreplace_pi_id : forall n x x0 (xp : x < n)(xp0 : x0 < n),
    0 <> 1 ->
    FMatrix.VA.id_vec xp = FMatrix.VA.id_vec xp0 -> x = x0.
  Proof.
    intros. destruct (Nat.eq_dec x x0). trivial. apply (Veq_nth4 xp0) in H0. 
    rewrite Vnth_replace in H0. rewrite Vnth_replace_neq in H0. trivial.
    rewrite Vnth_const in H0. assert False. apply H.
    unfold FSemiRingT.A0 in H0. rewrite H0. trivial. contradiction.
  Qed.

  Lemma MF_perm_row_uniq_sub : forall n (m : MF n),
    bVforall (VF_an_id (n:=n)) (FMatrix.mat_transpose m) = true ->
        0 <> 1 ->
    forall  i i0 (ip : i < n)(ip0 : i0 < n) x x0 (xp : x < n)(xp0 : x0 < n),
    i <> i0 ->
    Vnth m ip  = FMatrix.VA.id_vec xp  ->
    Vnth m ip0 = FMatrix.VA.id_vec xp0 ->
    x <> x0.
  Proof.
    intros n m H neq i i0 ip ip0 x x0 xp xp0. intros. unfold not in *. intros. subst. 
    assert (xp = xp0). apply le_unique. rewrite H3 in H1. 
    apply (bVforall_elim_nth xp0) in H.  unfold VF_an_id in H. 
    apply bVexists_eq in H. elim H. intros. elim H4. intros. clear H4. 
    apply VF_beq_true in H5. rewrite Vbuild_nth in H5.
    pose FMatrix.mat_transpose_col_row. unfold FMatrix.get_row in e.
    rewrite e in H5. apply (Veq_nth4 xp0) in H2. apply (Veq_nth4 xp0) in H1.
    assert (FMatrix.get_col m xp0 = FMatrix.VA.id_vec x1). trivial.
    apply (Veq_nth4 ip) in H4. apply (Veq_nth4 ip0) in H5. rewrite Vnth_map in H4.
    rewrite Vnth_map in H5. rewrite H2 in H5. rewrite H1 in H4.
    rewrite Vnth_replace in H5. rewrite Vnth_replace in H4.
    rewrite H5 in H4. destruct (Nat.eq_dec i x).
    + subst. rewrite Vnth_replace in H4. rewrite Vnth_replace_neq in H4. 
    unfold not. intros. apply H0. trivial. rewrite Vnth_const in H4. 
    apply neq. unfold FSemiRingT.A0 in H4.
    rewrite H4. trivial.
    + symmetry in H4. rewrite Vnth_replace_neq in H4. unfold not in *.
    intros. apply n0. rewrite H4. trivial. rewrite Vnth_const in H4.
    rewrite <- H4 in H5. apply neq.
    unfold FSemiRingT.A0 in H5. rewrite <- H5. trivial.
  Qed.

  Lemma MF_perm_row_uniq : forall n (m : MF n),
    MFisPermutation m ->
        0 <> 1 ->
    forall  i i0 (ip : i < n)(ip0 : i0 < n) x x0 (xp : x < n)(xp0 : x0 < n),
    i <> i0 ->
    Vnth m ip  = FMatrix.VA.id_vec xp  ->
    Vnth m ip0 = FMatrix.VA.id_vec xp0 ->
    x <> x0.
  Proof.
    intros.  unfold MFisPermutation in H. apply andb_true_iff in H. destruct H.
    apply (MF_perm_row_uniq_sub m H4 H0 ip ip0 xp xp0); trivial.
  Qed.

  Lemma MF_perm_col_uniq : forall n (m : MF n),
    MFisPermutation m ->
    0 <> 1 ->
    forall  i i0 (ip : i < n)(ip0 : i0 < n) x x0 (xp : x < n)(xp0 : x0 < n),
    i <> i0 ->
    Vnth (MF_trans m) ip  = FMatrix.VA.id_vec xp  ->
    Vnth (MF_trans m) ip0 = FMatrix.VA.id_vec xp0 ->
    x <> x0.
  Proof.
    intros.  unfold MFisPermutation in H. apply andb_true_iff in H. destruct H.
    rewrite <- (FMatrix.mat_transpose_idem m) in H. 
    apply (MF_perm_row_uniq_sub (MF_trans m) H H0 ip ip0 xp xp0); trivial.
  Qed.

  Lemma MF_perm_mix_eq_sub : forall n (m : MF n) i (ip : i< n) x (xp : x < n),
    bVforall (VF_an_id (n:=n)) (FMatrix.mat_transpose m) = true ->
    Vnth m ip  = FMatrix.VA.id_vec xp ->
    Vnth (MF_trans m) xp = FMatrix.VA.id_vec ip.
  Proof.
    intros. destruct TrivialOrNot. apply Veq_nth. intros. apply H1. 
    apply (bVforall_elim_nth xp) in H.  unfold VF_an_id in H. 
    apply bVexists_eq in H. elim H. intros. elim H2. intros. clear H2. 
    apply VF_beq_true in H3. rewrite Vbuild_nth in H3. destruct (Nat.eq_dec x0 i).
    subst. rewrite H3. apply f_equal. apply le_unique.
    apply (Veq_nth4 ip) in H3. rewrite Vnth_replace_neq in H3. trivial.
    rewrite Vnth_const in H3. rewrite FMatrix.mat_build_nth in H3.
    unfold FMatrix.get_elem, FMatrix.get_row in H3. apply (Veq_nth4 xp) in H0.
    rewrite Vnth_replace in H0. rewrite H0 in H3.
    assert False. apply H1. unfold FSemiRingT.A1 in H3. rewrite H3.
    trivial. contradiction.
  Qed.

  Lemma MF_perm_mix_eq : forall n (m : MF n) i (ip : i< n) x (xp : x < n),
    MFisPermutation m ->
    Vnth m ip  = FMatrix.VA.id_vec xp <->
    Vnth (MF_trans m) xp = FMatrix.VA.id_vec ip.
  Proof. 
    intros. apply andb_true_iff in H. destruct H. split; intros. 
    apply MF_perm_mix_eq_sub; trivial. rewrite <- (FMatrix.mat_transpose_idem m). 
    apply MF_perm_mix_eq_sub. rewrite FMatrix.mat_transpose_idem. trivial. trivial.
  Qed.
    
   Lemma MF_perm_row_imp : forall n (m :MF n) j (jp : j < n) x (xp : x < n),
    MFisPermutation m ->
    (forall i (ip : i < n),
    i <> j ->
    Vnth m ip <> FMatrix.VA.id_vec xp) ->
    Vnth m jp = FMatrix.VA.id_vec xp.
  Proof.
    intros. destruct TrivialOrNot. apply Veq_nth. intros. apply H1. 
    assert (MFisPermutation m) as b. trivial.
    case_eq (VF_beq (Vnth m jp) (FMatrix.VA.id_vec xp)).
    intros. apply VF_beq_true in H2. trivial. intros. apply andb_true_iff in H.
    destruct H. apply (bVforall_elim_nth jp) in H.  unfold VF_an_id in H. 
    apply bVexists_eq in H. elim H. intros. elim H4. intros. clear H4. 
    apply VF_beq_true in H5. rewrite Vbuild_nth in H5. assert (x <> x0).
    unfold not. intros. apply VF_beq_false in H2. apply H2.
    rewrite H5. apply Vreplace_pi. auto.  
    (* At this point we know there are know 1s in the xth colomn. *)
    apply (bVforall_elim_nth xp) in H3.  unfold VF_an_id in H3. 
    apply bVexists_eq in H3. elim H3. intros. elim H6. intros. clear H6. 
    apply VF_beq_true in H7. rewrite Vbuild_nth in H7. 
    (* Now apprently there is a one at x3 *)
    apply MF_perm_mix_eq in H7. destruct (Nat.eq_dec x2 j). subst.
    subst. assert (Vnth m jp = Vnth m x3). apply Vnth_eq. trivial.
    rewrite H6 in H5. rewrite H5 in H7. apply Vreplace_pi_id in H7.
    assert False. unfold not in *. apply H4. rewrite H7. trivial. contradiction.
    trivial.
    apply (H0 x2 x3) in n0. contradiction. trivial.
  Qed.
  
  Lemma permTranInv :  forall n (m : MF n),
    MFisPermutation m ->
    MF_mult m (MF_trans m) = MF_id n.
  Proof. 
    intros. apply Veq_nth. intros. apply Veq_nth. intros. unfold MF_id, MF_mult.
    assert (MFisPermutation m). trivial.
    unfold MFisPermutation in H. apply andb_true_iff in H. destruct H.
    apply (bVforall_elim_nth ip) in H. unfold VF_an_id in H. apply bVexists_eq in H.
    elim H. intros. elim H2. intros. clear H2. apply VF_beq_true in H3.
    rewrite Vbuild_nth in H3. rewrite FMatrix.mat_build_nth. rewrite Vbuild_nth. 
    unfold FMatrix.VA.id_vec. destruct (Nat.eq_dec i0 i).
    + subst. rewrite Vnth_replace. rewrite FMatrix.mat_transpose_row_col.
    unfold FMatrix.get_row. rewrite H3. assert (Vnth m ip = Vnth m ip0).
    apply f_equal. apply le_unique. rewrite <- H2. rewrite H3.
    rewrite FMatrix.VA.dot_product_id. rewrite Vnth_replace. trivial.
    + assert (i <> i0). unfold not in *. intros. apply n0. rewrite H2. trivial. 
    rewrite Vnth_replace_neq; trivial. rewrite Vnth_const. 
    rewrite FMatrix.mat_transpose_row_col. unfold FMatrix.get_row.
    rewrite H3. rewrite FMatrix.VA.dot_product_id. assert (MFisPermutation m). 
    trivial. unfold MFisPermutation in H0. apply andb_true_iff in H0. destruct H0.
    apply (bVforall_elim_nth ip0) in H0. unfold VF_an_id in H0. 
    apply bVexists_eq in H0. elim H0. intros. elim H6. intros. clear H6.
    apply VF_beq_true in H7. rewrite Vbuild_nth in H7. rewrite H7.
    destruct TrivialOrNot. apply H6.
    pose (MF_perm_row_uniq m H4 H6 ip0 ip x2 x0 n0 H7 H3). rewrite Vnth_replace_neq.
    trivial. rewrite Vnth_const. trivial.
  Qed.

  Lemma vecIdVtail : forall x n (xp : S x < S n),
    Vtail (FMatrix.VA.id_vec xp) = FMatrix.VA.id_vec (lt_S_n xp).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_tail. trivial.
  Qed. 

  Lemma vecIdVremove_last : forall n ,
    Vremove_last (FMatrix.VA.id_vec (lt_0_Sn (S n))) = 
      FMatrix.VA.id_vec (lt_0_Sn n).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_remove_last. 
    unfold FMatrix.VA.id_vec. destruct i. do 2 rewrite Vnth_replace. trivial.
    rewrite Vnth_replace_neq. lia. rewrite Vnth_replace_neq. lia. 
    do 2 rewrite Vnth_const. trivial. 
  Qed.

  Lemma vecIdVremove_last2 : forall n x (xp : x < S n)(xp' : x < n),
    Vremove_last (FMatrix.VA.id_vec xp) = 
      FMatrix.VA.id_vec xp'.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_remove_last. 
    unfold FMatrix.VA.id_vec. destruct (Nat.eq_dec x i).
    + subst. do 2 rewrite Vnth_replace. trivial.
    + rewrite Vnth_replace_neq. lia. rewrite Vnth_replace_neq. lia. 
    do 2 rewrite Vnth_const. trivial. 
  Qed.

  Fixpoint MF_perm_last n : MF (S n) -> (Index (S n)) :=
    match n with
      | 0 => fun _ => MakeIndex (lt_0_Sn 0)
      | S a => fun m => match VF_beq (Vhead m) (FMatrix.VA.id_vec (lt_n_Sn (S a))) with
        | true => MakeIndex (lt_0_Sn (S a))
        | false => MakeIndexSucc (MF_perm_last (Vmap (fun a => Vtail a) (Vtail m)))
      end
    end.  

  Definition IdSub n (v : VF n) := VatMostOne (fun a => negb (Fbool_eq a 0)) v.

  Lemma IdSub_Vforall : forall n n' (v : vector (VF (S n)) n'),
    Vforall (IdSub (n:=S n)) v ->
    Vforall (IdSub (n:=n)) (Vmap (fun a => Vremove_last a) v).
  Proof.
    intros. induction v. simpl. trivial. simpl in *. destruct H. split.
    apply VatMostOne_remove. trivial. apply IHv. trivial.
  Qed.

  Lemma IdSub_Vforall2 : forall n n' (v : vector (VF (S n)) n'),
    Vforall (IdSub (n:=S n)) v ->
    Vforall (IdSub (n:=n)) (Vmap (fun a => Vtail a) v).
  Proof.
    intros. induction v. simpl. trivial. simpl in *. destruct H. split.
    apply VatMostOne_tail. trivial. apply IHv. trivial.
  Qed.

  Lemma IdFoldSub : forall n x (xp : x < n),
    0 <> 1 ->
    Vfold_left Nat.add 0%nat (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat 
      else 0%nat)  (FMatrix.VA.id_vec xp)) = 1%nat.
  Proof.
    induction n; intros. lia. rewrite (VSn_eq (FMatrix.VA.id_vec xp)). 
    rewrite Vcons_map. rewrite Vfold_left_Vcons;  intros. lia. lia.
     destruct x. replace (~~ Fbool_eq (Vhead (FMatrix.VA.id_vec xp)) 0) with true.
   replace (Vfold_left Nat.add 0%nat (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat)
     (Vtail (FMatrix.VA.id_vec xp)))) with 0%nat. lia. clear IHn. simpl.
   replace (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat) (FMatrix.VA.zero_vec n))
    with (Vconst 0%nat n). induction n. cbn. trivial. cbn. rewrite <- IHn. lia. lia.
    apply Veq_nth. intros. rewrite Vnth_const. rewrite Vnth_map. rewrite Vnth_const.
    replace (~~ Fbool_eq FSemiRingT.A0 0) with false. trivial.  symmetry. 
    apply negb_false_iff. apply F_bool_eq_corr. trivial. symmetry.
    apply negb_true_iff. apply F_bool_neq_corr. rewrite Vhead_nth. rewrite Vnth_replace.
    unfold not. intros. apply H. rewrite <- H0. trivial.
   rewrite IHn. replace (~~ Fbool_eq (Vhead (FMatrix.VA.id_vec xp)) 0) with
    false. trivial. symmetry. apply negb_false_iff. apply F_bool_eq_corr.
    rewrite Vhead_nth. rewrite Vnth_replace_neq. lia. rewrite Vnth_const. trivial.
    cbn. assert (Fbool_eq FSemiRingT.A0 0 = true). apply F_bool_eq_corr. trivial.
    rewrite H0. cbn. trivial.
  Qed.

  Lemma IdSubImp : forall n (v : VF (S n)) i (ip : i < n),
    IdSub v ->
    Vnth v (le_S ip) <> 0 ->
    VlastS v = 0.
  Proof.
    induction n; intros. lia. destruct i. unfold VlastS. rewrite Vlast_nth.
    case_eq (Fbool_eq (Vnth v (Nat.lt_succ_diag_r (S n))) 0); intros.
    apply F_bool_eq_corr in H1. trivial. apply F_bool_neq_corr in H1.
    unfold IdSub, VatMostOne in H. assert (2 <= Vfold_left Nat.add 0%nat 
    (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat) v)). 
    clear H. clear IHn. rewrite (VSn_eq v). rewrite (VSn_addS (Vtail v)).
    rewrite Vcons_map. rewrite Vadd_map. rewrite Vfold_left_Vcons;  intros. lia. lia.
    rewrite Vfold_add;  intros. lia. lia. replace (~~ Fbool_eq (Vhead v) 0) with true.
    replace (~~ Fbool_eq (VlastS (Vtail v)) 0) with true. lia. 
    symmetry. apply negb_true_iff. apply F_bool_neq_corr. unfold VlastS.
    rewrite Vlast_nth. unfold not in *. intros. apply H1. rewrite <- H.
    rewrite Vnth_tail. apply Vnth_eq. trivial. symmetry. apply negb_true_iff. 
    apply F_bool_neq_corr. rewrite Vhead_nth. unfold not in *. intros. apply H0.
    rewrite <- H. apply Vnth_eq. trivial. lia.
    rewrite <- VlastS_tail. apply (IHn (Vtail v) i (lt_S_n ip)). 
    apply VatMostOne_tail. trivial. rewrite Vnth_tail. unfold not in *.
    intros. apply H0.  rewrite <- H1. apply Vnth_eq. trivial.  
  Qed.

  Lemma IdSubImp2 : forall n (v : VF (S n)) i (ip : i < n),
    IdSub v ->
    Vnth v (lt_n_S ip) <> 0 ->
    Vhead v = 0.
  Proof.
    destruct n; intros. lia. rewrite Vhead_nth.
    case_eq (Fbool_eq (Vnth v (Nat.lt_0_succ (S n))) 0); intros.
    apply F_bool_eq_corr in H1. trivial. apply F_bool_neq_corr in H1.
    unfold IdSub, VatMostOne in H. assert (2 <= Vfold_left Nat.add 0%nat 
    (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat) v)). 
    clear H. rewrite (VSn_eq v). rewrite Vcons_map. rewrite Vfold_left_Vcons; intros. 
    lia. lia. rewrite (Vfold_left_Vremove Nat.add (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat)
    (Vtail v)) 0%nat ip); intros; trivial. lia. lia. rewrite Vnth_map.
    replace (~~ Fbool_eq (Vhead v) 0) with true.
    replace (~~ Fbool_eq (Vnth (Vtail v) ip) 0) with true. lia. 
    symmetry. apply negb_true_iff. apply F_bool_neq_corr. 
    rewrite Vnth_tail. unfold not in *. intros. apply H0. rewrite <- H. trivial.
    symmetry. apply negb_true_iff. 
    apply F_bool_neq_corr. rewrite Vhead_nth. unfold not in *. intros. apply H1.
    trivial. lia.
  Qed.

  Lemma IdSubImp3 : forall n (v : VF (S n)) i (ip : i < S n) j (jp : j < S n),
    IdSub v ->
    i <> j ->
    Vnth v ip <> 0 ->
    Vnth v jp = 0.
  Proof.
    destruct n; intros. lia.
    case_eq (Fbool_eq (Vnth v jp) 0); intros.
    apply F_bool_eq_corr in H2. trivial. apply F_bool_neq_corr in H1.
    unfold IdSub, VatMostOne in H. assert (2 <= Vfold_left Nat.add 0%nat 
    (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat) v)). 
    clear H. rewrite (Vfold_left_Vremove Nat.add (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat)
    v) 0%nat ip); intros; trivial. lia. lia. rewrite Vnth_map. destruct j.
    + destruct i. lia. rewrite (VSn_eq (Vremove (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat) v) ip)).
    rewrite Vfold_left_Vcons; intros. lia. lia. rewrite Vremove_head.
    rewrite Vhead_map. replace (~~ Fbool_eq (Vnth v ip) 0) with true.
    replace (~~ Fbool_eq (Vhead v) 0) with true. lia. symmetry. apply negb_true_iff.
    apply F_bool_neq_corr. apply F_bool_neq_corr in H1. rewrite <- Vnth0Head in H2.
    apply F_bool_neq_corr. trivial. symmetry. apply negb_true_iff.
    apply F_bool_neq_corr. apply F_bool_neq_corr in H1. trivial.
    + destruct (le_lt_dec i j). 
    ++ rewrite (Vfold_left_Vremove Nat.add (Vremove (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat) v)
    ip) 0%nat (lt_S_n jp)); intros; trivial. lia. lia. rewrite Vremove_correct_right. trivial. rewrite Vnth_map. 
    replace (~~ Fbool_eq (Vnth v ip) 0) with true.
    replace (~~ Fbool_eq (Vnth v (lt_n_S (lt_S_n jp))) 0) with true. lia. 
    symmetry. apply negb_true_iff. apply F_bool_neq_corr. apply F_bool_neq_corr in H2. 
    unfold not in *. intros. apply H2. rewrite <- H. apply Vnth_eq. trivial.
    symmetry. apply negb_true_iff. trivial.
    ++ assert (S j < S n). lia. rewrite (Vfold_left_Vremove Nat.add (Vremove (Vmap (fun b : F => if ~~ Fbool_eq b 0 then 1%nat else 0%nat) v)
    ip) 0%nat H); intros; trivial. lia. lia. rewrite Vremove_correct_left.
     trivial. lia. rewrite Vnth_map.
    replace (~~ Fbool_eq (Vnth v ip) 0) with true.
    replace (~~ Fbool_eq (Vnth v (le_S H)) 0) with true. lia. 
    symmetry. apply negb_true_iff. apply F_bool_neq_corr. apply F_bool_neq_corr in H2. 
    unfold not in *. intros. apply H2. rewrite <- H3. apply Vnth_eq. trivial.
    symmetry. apply negb_true_iff. trivial.
    + lia.
  Qed.
     
  Lemma id_vec_to_IdSub : forall n (v : VF n),
    bVexists (VF_beq v) (Vbuild (fun i ip =>  (FMatrix.VA.id_vec ip))) ->
    IdSub v.
  Proof.
    intros. unfold IdSub, VatMostOne. apply bVexists_eq in H. elim H. intros.
    elim H0. intros. clear H0. apply VF_beq_true in H1. rewrite Vbuild_nth in H1. 
    rewrite H1. destruct TrivialOrNot. assert (Vmap (fun b : F => if ~~ Fbool_eq b 0 
    then 1%nat else 0%nat) (FMatrix.VA.id_vec x0) = Vconst 0%nat n). apply Veq_nth.
    intros. rewrite Vnth_map. rewrite Vnth_const. rewrite (H0 
    (Vnth (FMatrix.VA.id_vec x0) ip) 0). replace (~~ Fbool_eq 0 0) with false.
    trivial. symmetry. apply negb_false_iff. apply F_bool_eq_corr. trivial. 
    rewrite H2. clear H. clear H1. clear H2. clear H0. clear x0. clear x. clear v.
    induction n. cbn. lia. cbn. apply IHn. rewrite IdFoldSub. trivial. lia.
  Qed.

  Lemma Permutaion_to_IdSub : forall n (m : MF n),
    MFisPermutation m -> 
    Vforall (IdSub (n:=n)) m /\ Vforall (IdSub (n:=n)) (MF_trans m).
  Proof.
    intros. apply andb_true_iff in H. destruct H. split.
    + apply Vforall_nth_intro. intros. apply (bVforall_elim_nth ip) in H.
    apply id_vec_to_IdSub. trivial.
    + apply Vforall_nth_intro. intros. apply (bVforall_elim_nth ip) in H0.
    apply id_vec_to_IdSub. trivial.
  Qed.

  Lemma vecIdVremove_last3 : forall n (v : VF (S n)) x (xp : x < n),
    IdSub v ->
    Vremove_last v = FMatrix.VA.id_vec xp <-> v = FMatrix.VA.id_vec (le_S xp).
  Proof.
    split; intros. 
    + rewrite (VSn_addS v). rewrite H0. apply Veq_nth. intros. rewrite Vnth_add. destruct (Nat.eq_dec i n).
    unfold VlastS.  destruct (Nat.eq_dec x i).
    ++ subst. lia.
    ++ subst. rewrite Vnth_replace_neq. trivial. rewrite Vnth_const. 
    destruct TrivialOrNot. apply H1.
    apply (IdSubImp xp).
    trivial. apply (Veq_nth4 xp) in H0. rewrite Vnth_remove_last in H0. 
    assert (Nat.lt_lt_succ_r xp = le_S xp). apply le_unique. rewrite H2 in H0.
    rewrite H0. rewrite Vnth_replace. unfold not. intros. apply H1. rewrite <- H3.
    trivial.
    ++ destruct (Nat.eq_dec x i). 
    +++ subst. do 2 rewrite Vnth_replace. trivial.
    +++ rewrite Vnth_replace_neq. trivial. rewrite Vnth_replace_neq. trivial. do 2 rewrite Vnth_const.
    trivial.
    + rewrite H0. apply Veq_nth. intros. rewrite Vnth_remove_last. destruct (Nat.eq_dec x i).
    subst. rewrite Vnth_replace. rewrite Vnth_replace. trivial. rewrite Vnth_replace_neq. 
    trivial. rewrite Vnth_replace_neq. trivial. do 2 rewrite Vnth_const. trivial.
  Qed.

  Lemma MF_perm_last_valid_sub_sub : forall n (m : MF (S n)),
    Vforall (IdSub (n:=S n)) m ->
    sval (MF_perm_last m) < n ->
    Vnth m (proj2_sig (MF_perm_last m)) = FMatrix.VA.id_vec (lt_n_Sn n).
  Proof.
    intros. induction n. lia. simpl. case_eq (VF_beq (Vhead m) 
    (FMatrix.VA.id_vec (lt_n_Sn (S n))));
    intros. rewrite <- Vnth0Head. apply VF_beq_true in H1. trivial.
    rewrite (VSn_eq (FMatrix.VA.id_vec (lt_n_Sn (S n)))).
    rewrite vecIdVtail. assert (Vnth (Vmap (fun a => Vtail a) (Vtail m)) 
    (proj2_sig (MF_perm_last (Vmap (fun a => Vtail a) (Vtail m)))) = 
    FMatrix.VA.id_vec (Nat.lt_succ_diag_r n)). apply IHn.
    + simpl. apply IdSub_Vforall2. rewrite (VSn_eq m) in H. simpl in H. destruct H.
    trivial.
    + simpl in H0. rewrite H1 in H0. rewrite MakeIndexSuccProj in H0. 
    apply lt_S_n in H0. trivial.
    + rewrite Vnth_map in H2. replace (lt_S_n (Nat.lt_succ_diag_r (S n))) with
    (Nat.lt_succ_diag_r n). rewrite <- H2. 
    apply Veq_nth. intros. rewrite Vnth_cons. destruct (NatUtil.lt_ge_dec 0 i).
    ++ subst. do 2 rewrite Vnth_tail. apply Veq_nth3. lia. apply Vnth_eq. 
    rewrite MakeIndexSuccProj. lia.
    ++ replace (Vhead (FMatrix.VA.id_vec (Nat.lt_succ_diag_r (S n))))
    with 0. assert (i = 0%nat). lia. subst. rewrite <- Vnth0Head.
    destruct TrivialOrNot. apply H3.
    apply (IdSubImp2 (lt_n_Sn n)). apply (Vforall_nth (proj2_sig
        (MakeIndexSucc (MF_perm_last (Vmap (fun a => Vtail a) (Vtail m)))))) in  H.
    trivial. apply (Veq_nth4 (lt_n_Sn n)) in H2. rewrite Vnth_tail in H2.
    rewrite Vnth_tail in H2. assert (Vnth (Vnth m  (proj2_sig
    (MakeIndexSucc (MF_perm_last (Vmap (fun a => Vtail a) (Vtail m))))))
  (lt_n_S (lt_n_Sn n)) = Vnth (Vnth m (lt_n_S
             (proj2_sig (MF_perm_last (Vmap (fun a => Vtail a) (Vtail m))))))
       (lt_n_S (lt_n_Sn n))). apply Veq_nth3. trivial.
    apply Vnth_eq. rewrite MakeIndexSuccProj. lia. rewrite H4. rewrite H2.
    rewrite Vnth_replace. unfold not. intros. apply H3. rewrite <- H5. trivial.
    rewrite Vhead_nth. rewrite Vnth_replace_neq. lia. rewrite Vnth_const. trivial.
    ++ apply le_unique.
  Qed.

  Lemma MF_perm_last_clear : forall n (m : MF (S n)) i (ip : i < S n),
    i < proj1_sig (MF_perm_last m) ->
    VF_beq (Vnth m ip) (FMatrix.VA.id_vec (lt_n_Sn n)) = false.
  Proof.
    induction n. intros. 
    + (* base case *) cbn in *. lia.
    + intros. simpl in *. case_eq (VF_beq (Vhead m) 
    (FMatrix.VA.id_vec (lt_n_Sn (S n)))); intros. 
    ++ rewrite H0 in H. simpl in *. lia. 
    ++ destruct i. rewrite <- Vnth0Head. trivial. rewrite H0 in H. simpl.
    pose (IHn (Vmap [fun x=> Vtail x] (Vtail m)) i (lt_S_n ip)).
    assert (i < sval (MF_perm_last (Vmap [eta Vtail (n:=S n)] (Vtail m)))).
    simpl in H. rewrite MakeIndexSuccProj in H. lia. apply e in H1.
    apply VF_beq_false in H1. apply VF_beq_false. unfold not in *.
    intros. apply H1. rewrite Vnth_map. rewrite Vnth_tail. simpl. 
    replace (lt_n_S (lt_S_n ip)) with ip. rewrite H2. rewrite vecIdVtail.
    apply f_equal. apply le_unique. apply le_unique.
  Qed.  

  Lemma MF_perm_last_bound : forall n (m : MF (S n)),
    sval (MF_perm_last m) <= n.
  Proof.
    intros. induction n. cbn. trivial. simpl. destruct (VF_beq (Vhead m) 
    (FMatrix.VA.id_vec (Nat.lt_succ_diag_r (S n)))).
    destruct ((exist (Nat.lt_0_succ (S n)))). cbn. lia.
    pose (IHn (Vmap [eta Vremove_last (n:=S n)] (Vtail m))).
    rewrite MakeIndexSuccProj. apply le_n_S. trivial.
  Qed.

  Lemma MF_perm_last_valid_sub : forall n (m : MF (S n)),
    bVforall (VF_an_id (n:=S n)) m = true ->
    Vnth m (proj2_sig (MF_perm_last m)) = FMatrix.VA.id_vec (lt_n_Sn n) \/
    bVforall (fun a => negb (VF_beq a (FMatrix.VA.id_vec (lt_n_Sn n)))) m.
  Proof.
    intros. case_eq (le_lt_dec n (sval (MF_perm_last m))). 
    + intros. destruct n.
    ++ cbn. left.
    apply (bVforall_elim_nth (Nat.lt_0_succ 0)) in H. unfold VF_an_id in H. 
    apply bVexists_eq in H. elim H. intros. elim H1.
    intros. clear H1. apply VF_beq_true in H2. rewrite Vbuild_nth in H2.
    rewrite H2. assert (x = 0%nat). lia. subst. trivial.
    ++ assert (n < proj1_sig (MF_perm_last m)). lia. case_eq (VF_beq (Vnth m (proj2_sig (MF_perm_last m))) 
    (FMatrix.VA.id_vec ((lt_n_Sn (S n))))); intros.
    +++ left. apply VF_beq_true in H2. trivial.
    +++ right. apply bVforall_nth_intro. intros. case_eq (Nat.eq_dec i (S n)); intros.
    subst. apply VF_beq_false in H2. apply negb_true_iff. apply VF_beq_false.
    unfold not in *. intros. apply H2. rewrite <- H4. apply Vnth_eq.
    pose (MF_perm_last_bound m). lia. assert (i < S n). lia.
    apply negb_true_iff. apply MF_perm_last_clear. lia.
    + left. apply MF_perm_last_valid_sub_sub; trivial. apply Vforall_nth_intro. intros.
    apply id_vec_to_IdSub. apply (bVforall_elim_nth ip) in H. trivial. 
  Qed.

  Lemma MF_perm_clear : forall n (m : MF (S n)) i (ip : i < S n),
    MFisPermutation m -> 
    0 <> 1 ->
    i <> proj1_sig (MF_perm_last m) ->
    VF_beq (Vnth m ip) (FMatrix.VA.id_vec (lt_n_Sn n)) = false.
  Proof.
    intros. apply andb_true_iff in H. destruct H. 
    pose (MF_perm_last_valid_sub m H). destruct o.
    + apply VF_beq_false. unfold not. intros. 
    pose (MF_perm_row_uniq_sub m H2 H0 ip (proj2_sig (MF_perm_last m)) (Nat.lt_succ_diag_r n) 
    (Nat.lt_succ_diag_r n) H1 H4 H3). apply n0. trivial.
    + apply (bVforall_elim_nth ip) in H3. apply negb_true_iff in H3. trivial.
  Qed.  

  Lemma MF_perm_clear_nth : forall n (m : MF (S n)) i (ip : i < S n),
    MFisPermutation m -> 
    i <> proj1_sig (MF_perm_last m) ->
    Vnth (Vnth m ip) (Nat.lt_succ_diag_r n) = 0.
  Proof.
    intros. destruct TrivialOrNot. apply H1.
    pose (MF_perm_clear m ip H H1 H0). apply VF_beq_false in e.
    unfold MFisPermutation in H.  apply andb_true_iff in H.  destruct H.
    apply (bVforall_elim_nth ip) in H.
    apply bVexists_eq in H. elim H. intros. elim H3.
    intros. clear H3. apply VF_beq_true in H4. rewrite Vbuild_nth in H4.
    rewrite H4. destruct (Nat.eq_dec x n). assert (False). apply e. 
    rewrite H4. subst. apply f_equal. apply le_unique. contradiction.
    rewrite Vnth_replace_neq. trivial. rewrite Vnth_const. trivial.
  Qed. 


  Lemma MF_perm_last_corr : forall n (m : MF (S n)),
    MFisPermutation m -> 
    Vnth m (proj2_sig (MF_perm_last m)) = FMatrix.VA.id_vec (lt_n_Sn n).
  Proof.
    intros. destruct (le_lt_dec n (sval (MF_perm_last m))).
    assert (sval (MF_perm_last m) = n). pose (MF_perm_last_bound m). lia.
    apply MF_perm_row_imp. trivial. intros. apply VF_beq_false.
    apply MF_perm_last_clear. lia. 
    apply (MF_perm_last_valid_sub_sub m). apply Permutaion_to_IdSub. trivial. lia.
  Qed.

  (* Remove by row *)
  Definition MF_perm_sub n (m : MF (S n)) : MF n :=
    Vmap (fun a => Vremove_last a) (Vremove m (proj2_sig (MF_perm_last m))). 

  Lemma MF_perm_sub_id : forall n (m : MF (S n)),
    m = Vmap2 (fun a b => Vadd a (VlastS b))
      (Vinsert (Vremove_last (Vnth m (proj2_sig (MF_perm_last m)))) (MF_perm_sub m)
        (proj2_sig (MF_perm_last m))) m.
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. rewrite Vnth_map2. 
    apply Veq_nth2. rewrite (VSn_addS (Vnth m ip)). apply f_equal2.
    + unfold MF_perm_sub. rewrite Vnth_cast. rewrite Vnth_app.
    destruct (le_gt_dec (sval (MF_perm_last m)) i). rewrite Vnth_cons.
    destruct (NatUtil.lt_ge_dec 0 (i - sval (MF_perm_last m))).
    rewrite Vnth_sub. rewrite Vnth_map.  rewrite Vremove_correct_right. lia.
    apply f_equal. apply Vnth_eq. lia. apply f_equal. apply Vnth_eq. lia.
    rewrite Vnth_sub. rewrite Vnth_map. rewrite Vremove_correct_left.
    lia. apply f_equal. apply Vnth_eq. lia.
    + rewrite VlastS_add. trivial.
  Qed.

   Lemma MF_perm_last_tran : forall n (m : MF (S n)),
    MFisPermutation m -> 
    Vnth m (proj2_sig (MF_perm_last m)) = 
      Vnth (MF_trans m) (proj2_sig (MF_perm_last (MF_trans m))).
  Proof.
    intros. rewrite MF_perm_last_corr. trivial. rewrite MF_perm_last_corr.
    apply MF_perm_inv. trivial. trivial.
  Qed.

  Lemma permTranInd_sub :  forall n (m : MF (S n)),
    MFisPermutation m -> MFisPermutation (MF_perm_sub m).
  Proof.
    intros. assert (MFisPermutation m) as b. trivial. unfold MFisPermutation in *. 
    apply andb_true_iff in H.  destruct H. unfold MFisPermutation.
    apply andb_true_iff. split.
    + apply bVforall_nth_intro. intros. rewrite Vnth_map.
    destruct TrivialOrNot. unfold VF_an_id. apply bVexists_eq. exists i. 
    exists ip. apply VF_beq_true. apply Veq_nth. intros. apply H1.
    destruct (le_lt_dec (sval (MF_perm_last m)) i).
    ++ rewrite Vremove_correct_right. trivial. 
    apply (bVforall_elim_nth (lt_n_S ip)) in H.
    apply bVexists_eq in H. elim H. intros. elim H2.
    intros. clear H2. apply VF_beq_true in H3. rewrite Vbuild_nth in H3.
    apply bVexists_eq. exists x.  destruct (Nat.eq_dec x n).
    subst. assert False. assert (S i <> sval (MF_perm_last m)). lia.
    pose (MF_perm_clear m (lt_n_S ip) b H1). apply VF_beq_false in e.
    unfold not in *. apply e. rewrite H3. apply f_equal. apply le_unique. trivial.
    contradiction. assert (x < n). lia. exists H2. apply VF_beq_true. 
    rewrite Vbuild_nth. rewrite H3. apply vecIdVremove_last2.
    ++ rewrite Vremove_correct_left. trivial. 
    apply (bVforall_elim_nth (le_S ip)) in H.
    apply bVexists_eq in H. elim H. intros. elim H2.
    intros. clear H2. apply VF_beq_true in H3. rewrite Vbuild_nth in H3.
    apply bVexists_eq. exists x. destruct (Nat.eq_dec x n). assert False. 
    assert (i <> sval (MF_perm_last m)). lia. pose (MF_perm_clear m (le_S ip) b H1). 
    apply VF_beq_false in e0. unfold not in *. apply e0. rewrite H3. subst. 
    apply f_equal. apply le_unique. trivial. contradiction.
    assert (x < n). lia. exists H2. apply VF_beq_true. rewrite Vbuild_nth. 
    rewrite H3. apply vecIdVremove_last2.
    + apply bVforall_nth_intro. intros. unfold MF_perm_sub.
    assert (bVforall (VF_an_id (n:=S n)) (FMatrix.mat_transpose m) = true) as bac. 
    trivial.
    apply (bVforall_elim_nth (le_S ip)) in H0. apply bVexists_eq in H0. elim H0. 
    intros. elim H1. intros. clear H1. apply VF_beq_true in H2.
    rewrite Vbuild_nth in H2. apply bVexists_eq.
    destruct TrivialOrNot. unfold VF_an_id.  exists i. 
    exists ip. apply VF_beq_true. apply Veq_nth. intros. apply H1.
    destruct (le_lt_dec x (sval (MF_perm_last m))). 
    ++ assert (x <> sval (MF_perm_last m)). (* First we show what it can't be *)
    assert (Vnth m (proj2_sig (MF_perm_last m)) = 
    FMatrix.VA.id_vec (lt_n_Sn n)). apply MF_perm_last_corr. trivial.
    unfold not. intros. apply MF_perm_mix_eq  in H2. trivial. 
    subst. assert ((proj2_sig (MF_perm_last m)) = x0). apply le_unique.
    rewrite H4 in H3. rewrite H2 in H3. apply H1. apply (Veq_nth4 (le_S ip)) in H3.
    rewrite Vnth_replace in H3. rewrite Vnth_replace_neq in H3. lia.
    rewrite Vnth_const in H3. unfold FSemiRingT.A1 in H3. rewrite H3. trivial. trivial.
    (* The we resume *)
    assert (x < n). pose (MF_perm_last_bound m). lia. 
    assert (x < sval (MF_perm_last m)). lia. exists x. exists H4.
    apply VF_beq_true. rewrite Vbuild_nth. apply Veq_nth. intros. 
    rewrite FMatrix.mat_build_nth. unfold FMatrix.get_elem, FMatrix.get_row. 
    rewrite Vnth_map. destruct (le_lt_dec (sval (MF_perm_last m)) i0). 
    (* Ready to split *)
    apply (Veq_nth4 (lt_n_S ip0)) in H2. assert (x <> i0). lia.
    rewrite Vnth_replace_neq. trivial. rewrite Vnth_replace_neq in H2. trivial. lia.
    rewrite Vnth_const. rewrite Vnth_const in H2. rewrite <- H2. rewrite FMatrix.mat_build_nth. 
    unfold FMatrix.get_elem, FMatrix.get_row. rewrite Vnth_remove_last.
    apply Veq_nth3. trivial. rewrite Vremove_correct_right. lia. trivial.
    (* First split complete *) rewrite Vremove_correct_left. lia.
    rewrite Vnth_remove_last. apply (Veq_nth4 (le_S ip0)) in H2. 
    rewrite FMatrix.mat_build_nth in H2. unfold FMatrix.get_elem, FMatrix.get_row in H2.
    assert ((Nat.lt_lt_succ_r ip) = le_S ip). apply le_unique. rewrite H6.
    rewrite H2. destruct (Nat.eq_dec x i0). subst. do 2 rewrite Vnth_replace.
    trivial. rewrite Vnth_replace_neq. trivial. rewrite Vnth_replace_neq. trivial.
    do 2 rewrite Vnth_const. trivial.
    ++ destruct x. lia. apply (Vremove_intro (proj2_sig (MF_perm_last m))) in H2.
    rewrite Vremove_replace_const2 in H2. lia. exists x. exists (lt_S_n x0). 
    apply VF_beq_true. rewrite Vbuild_nth. unfold FMatrix.VA.id_vec, 
    FMatrix.VA.zero_vec. symmetry in H2. rewrite H2. 
    apply Veq_nth. intros. destruct (le_lt_dec (sval (MF_perm_last m)) i0).
    rewrite Vremove_correct_right. trivial. do 2  rewrite FMatrix.mat_build_nth. 
    unfold FMatrix.get_elem, FMatrix.get_row. rewrite Vnth_map.
    rewrite Vnth_remove_last. rewrite Vremove_correct_right. lia. apply Vnth_eq.
    trivial. rewrite Vremove_correct_left. trivial. do 2  rewrite FMatrix.mat_build_nth. 
    unfold FMatrix.get_elem, FMatrix.get_row. rewrite Vnth_map.
    rewrite Vnth_remove_last. rewrite Vremove_correct_left. lia. apply Vnth_eq.
    trivial.
  Qed.

  Lemma permSubRow : forall n (m : MF (S n)) i (ip : i < n) x (xp : x < n),
    sval (MF_perm_last m) <= i ->
    Vnth m (lt_n_S ip) = FMatrix.VA.id_vec (le_S xp) ->
    Vnth (MF_perm_sub m) ip = FMatrix.VA.id_vec xp.
  Proof.
    intros. rewrite Vnth_map. rewrite Vremove_correct_right. trivial.
    rewrite H0. rewrite vecIdVremove_last3. trivial. apply id_vec_to_IdSub.
    apply bVexists_eq. exists x. exists (le_S xp). apply VF_beq_true.
    rewrite Vbuild_nth. trivial. trivial.
  Qed.

  Lemma permSubRow2 : forall n (m : MF (S n)) i (ip : i < n) x (xp : x < n),
    i < sval (MF_perm_last m) ->
    Vnth m (le_S ip) = FMatrix.VA.id_vec (le_S xp) ->
    Vnth (MF_perm_sub m) ip = FMatrix.VA.id_vec xp.
  Proof.
    intros. rewrite Vnth_map. rewrite Vremove_correct_left. trivial.
    rewrite H0. rewrite vecIdVremove_last3. trivial. apply id_vec_to_IdSub.
    apply bVexists_eq. exists x. exists (le_S xp). apply VF_beq_true.
    rewrite Vbuild_nth. trivial. trivial.
  Qed.

  Lemma permutationInnerProd : forall n (m : MF n)(a : VF n), 
    MFisPermutation m ->
    VF_prod (Vbuild (fun (j : nat) (jp : j < n) =>
      Vnth (MF_CVmult m a) jp)) =
    VF_prod a.
  Proof.
    intros. assert (MFisPermutation m) as b. trivial.
    induction n. cbn. rewrite (Vector_0_is_nil a). cbn. trivial.
    rewrite (MF_perm_sub_id m). unfold VF_prod. rewrite (VSn_addS a).
    rewrite Vfold_add. intros. ring; auto. intros. ring; auto. rewrite <- VSn_addS.
    rewrite (Vfold_left_Vremove Fmul (Vbuild
     (fun j : nat =>
      [eta Vnth
             (MF_CVmult
                (Vmap2
                   (fun (a0 : FMatrix.vec n) (b : FMatrix.vec (S n)) =>
                    Vadd a0 (VlastS b))
                   (Vinsert (Vremove_last (Vnth m (proj2_sig (MF_perm_last m))))
                      (MF_perm_sub m) (proj2_sig (MF_perm_last m))) m) a) (i:=j)])) Fone (proj2_sig (MF_perm_last m))).
     intros. ring; auto. intros. ring; auto. destruct module_ring.
     rewrite Rmul_comm. apply f_equal2.
    + unfold VF_prod in IHn. assert (MFisPermutation (MF_perm_sub m)). 
    apply permTranInd_sub. trivial. apply (IHn (MF_perm_sub m) (Vremove_last a)) in H0.
    rewrite <- MF_perm_sub_id. rewrite <- H0. apply f_equal. apply Veq_nth.
    intros. destruct (le_lt_dec (sval (MF_perm_last m)) i). rewrite Vremove_correct_right.
    trivial. do 2 rewrite Vbuild_nth. unfold VF_inProd. do 2 rewrite MF_getRow_prod.
     unfold VF_inProd.   apply andb_true_iff in H.  destruct H. 
    apply (bVforall_elim_nth (lt_n_S ip)) in H.
    apply bVexists_eq in H. elim H. intros. elim H2.
    intros. clear H2. apply VF_beq_true in H3. rewrite Vbuild_nth in H3.
    rewrite H3. destruct (Nat.eq_dec x n).
    destruct TrivialOrNot. rewrite (VSn_eq a). rewrite (VSn_eq (FMatrix.VA.id_vec x0)).
    pose InProd_Vcons. unfold VF_inProd in e0. rewrite e0. replace (Vhead a) with 0.
    replace (FMatrix.VA.dot_product (Vtail (FMatrix.VA.id_vec x0)) (Vtail a)) with 
    (FMatrix.VA.dot_product (Vnth (MF_perm_sub m) ip) (Vremove_last (Vcons 0 (Vtail a)))).
    ring; auto. apply f_equal2. apply Veq_nth. intros.  apply H2. apply Veq_nth. intros.
    apply H2. apply H2.
     assert (S i <> sval (MF_perm_last m)). lia.
    apply (MF_perm_clear m (lt_n_S ip) b) in H2. apply VF_beq_false in H2.
    assert False. apply H2. rewrite H3. subst. apply f_equal. apply le_unique.
    contradiction. trivial. assert (x < n). lia.
    apply (permSubRow m ip H2) in l. rewrite l. 
    do 2 rewrite FMatrix.VA.dot_product_id. rewrite Vnth_remove_last. apply Vnth_eq.
    trivial. rewrite H3. apply f_equal. apply le_unique. rewrite Vremove_correct_left.
    trivial. do 2 rewrite Vbuild_nth. unfold VF_inProd. do 2 rewrite MF_getRow_prod.
     unfold VF_inProd.  apply andb_true_iff in H.  destruct H. 
    apply (bVforall_elim_nth (le_S ip)) in H.
    apply bVexists_eq in H. elim H. intros. elim H2.
    intros. clear H2. apply VF_beq_true in H3. rewrite Vbuild_nth in H3.
    rewrite H3. destruct (Nat.eq_dec x n). assert (i <> sval (MF_perm_last m)). lia.
    destruct TrivialOrNot. rewrite (VSn_eq a). rewrite (VSn_eq (FMatrix.VA.id_vec x0)).
    pose InProd_Vcons. unfold VF_inProd in e0. rewrite e0. replace (Vhead a) with 0.
    replace (FMatrix.VA.dot_product (Vtail (FMatrix.VA.id_vec x0)) (Vtail a)) with 
    (FMatrix.VA.dot_product (Vnth (MF_perm_sub m) ip) (Vremove_last (Vcons 0 (Vtail a)))).
    ring; auto. apply f_equal2. apply Veq_nth. intros.  apply H4. apply Veq_nth. intros.
    apply H4. apply H4.
    apply (MF_perm_clear m (le_S ip) b) in H2. apply VF_beq_false in H2.
    assert False. apply H2. rewrite H3. subst. apply f_equal. apply le_unique.
    contradiction. trivial.  assert (x < n). lia.
    apply (permSubRow2 m ip H2) in l. rewrite l. 
    do 2 rewrite FMatrix.VA.dot_product_id. rewrite Vnth_remove_last. apply Vnth_eq.
    trivial. rewrite H3. apply f_equal. apply le_unique. trivial.
    + rewrite Vbuild_nth. rewrite <- MF_perm_sub_id. rewrite MF_getRow_prod.
    rewrite MF_perm_last_corr; trivial. unfold VF_inProd. 
    rewrite FMatrix.VA.dot_product_id. unfold VlastS. rewrite Vlast_nth. trivial.
  Qed.

  Lemma permutationInnerProd_sub : forall n (m : MF n)(a : VF n), 
    MFisPermutation m ->
    VF_prod (MF_CVmult m a) =
    VF_prod a.
  Proof.
    intros. rewrite (Vbuild_Vnth (MF_CVmult m a)). rewrite permutationInnerProd.
    trivial. trivial.
  Qed.

  Lemma MF_CVmult_MF_VCmult_perm : forall n (m : MF n)(a : VF n), 
    MF_CVmult m a = MF_VCmult a (MF_trans m).
  Proof.
    intros. apply Veq_nth. intros. unfold MF_CVmult, MF_VCmult, MF_trans.
    rewrite Vnth_map. do 2 rewrite FMatrix.mat_mult_elem. 
    rewrite FMatrix.get_col_col_mat. rewrite FMatrix.mat_transpose_row_col.
    cbn. apply FMatrix.VA.dot_product_comm.
  Qed. 

  Lemma VF_inProd_zero : forall n (a : VF n),
    VF_inProd (VF_zero n) a = 0.
  Proof.
    intros. rewrite InProd_Sum. symmetry. apply VF_sum_zero. apply Veq_nth.
    intros. rewrite Vnth_map2. rewrite Vnth_const. ring; auto.
  Qed.

  Lemma MF_CVmult_Vcons : forall n (m a : VF (S n))(M : vector (VF (S n)) n),
      MF_CVmult (Vcons m M) a = Vcons (VF_inProd m a) 
        (Vbuild (fun i ip => VF_inProd (Vnth M ip) a)).
  Proof.
    intros. apply Veq_nth. intros. rewrite MF_getRow_prod. do 2 rewrite Vnth_cons. 
    destruct (lt_ge_dec 0 i). rewrite Vbuild_nth. trivial.
    trivial.
  Qed.

  Lemma VF_prod_zero : forall n (v : VF n) i (ip : i < n),
    Vnth v ip = 0 ->
    VF_prod v = 0.
  Proof.
    induction n. lia. destruct i.
    + intros. rewrite (VSn_eq v). unfold VF_prod. rewrite Vfold_left_Vcons; intros. 
    ring; auto. ring; auto. rewrite (Vnth0Head v ip). rewrite H. ring; auto.
    + intros. rewrite (VSn_eq v). unfold VF_prod. rewrite Vfold_left_Vcons; intros. 
    ring; auto. ring; auto. unfold VF_prod in IHn. rewrite <- Vnth_tail_lt_S_n in H.
    rewrite (IHn (Vtail v) i (lt_S_n ip)). trivial. ring; auto.
  Qed.

  Lemma VF_prod_MF_CVmult_zero : forall n (m : MF n)(a : VF n) i (ip : i < n),
    VF_zero n = Vnth m ip ->
    VF_prod (MF_CVmult m a) = 0.
  Proof.
    induction n; intros. lia. apply (VF_prod_zero (MF_CVmult m a) ip).
    rewrite MF_getRow_prod. rewrite <- H. rewrite VF_inProd_zero. trivial.
  Qed.

  Lemma VF_prod_one : forall n,
    VF_prod (VF_one n) = 1.
  Proof.
    intros. induction n. cbn. trivial. cbn. replace (1*1) with 1. apply IHn.
    ring; auto.
  Qed.

  Lemma VF_prod_prod : forall n m (B : vector (VF n) m),
    VF_prod (Vfold_left (VF_mult (n:=n)) (VF_one n) B) =
    VF_prod (Vmap (VF_prod (n:=n)) B).
  Proof.
    intros. induction m. rewrite (Vector_0_is_nil B). cbn. apply VF_prod_one.
    unfold VF_prod in *. rewrite (VSn_eq B). 
    rewrite Vcons_map. rewrite Vfold_left_Vcons_Fmul. rewrite <- IHm. 
    rewrite Vfold_left_Vcons_VFmult. rewrite VF_prod_mult. trivial.
  Qed.

  Fixpoint matRecover_sub m f : nat :=
    match m with
      | 0 => 0%nat 
      | S a => if (Fbool_eq f (VF_sum (Vconst 1 a))) then a else
      matRecover_sub a f
    end.  

  Lemma matRecover_sub_ind : forall m f, 
     matRecover_sub (S m) f = if (Fbool_eq f (VF_sum (Vconst 1 m))) then m else
      matRecover_sub m f.
  Proof.
    intros. cbn. trivial.
  Qed. 

  Lemma matRecover_sub_corr_sub : forall x n,
    VF_sum (Vconst 1 x) <> VF_sum (Vconst 1 n) ->
    x <> n.
  Proof.
    intros. unfold not in *. intros. apply H. rewrite H0. trivial.
  Qed. 

  Lemma matRecover_sub_corr : forall n x,
    x < S n ->
    (forall i j (ip: i < S n)(ij : j < S n), 
    VF_sum (Vconst 1 i) = VF_sum (Vconst 1 j) -> i = j) ->
    matRecover_sub (S n) (VF_sum (Vconst 1 x)) = x.
  Proof.
    intros. induction n.
    + cbn. assert (x = 0%nat). lia. subst. 
    destruct (Fbool_eq (VF_sum (Vconst 1 0)) 0); trivial.
    + rewrite matRecover_sub_ind. 
    case_eq (Fbool_eq (VF_sum (Vconst 1 x)) (VF_sum (Vconst 1 (S n)))); intros.
    apply F_bool_eq_corr in H1. apply H0. lia. lia.  rewrite H1. trivial.
    apply IHn. apply F_bool_neq_corr in H1. apply matRecover_sub_corr_sub in H1.
    lia. intros. apply H0. lia. lia. trivial. 
  Qed.

  Lemma matRecover_sub_less : forall m f, 
    matRecover_sub (S m) f < (S m).
  Proof.
    intros. induction m. cbn. destruct (Fbool_eq f 0). lia. lia.
    rewrite matRecover_sub_ind. destruct (Fbool_eq f (VF_sum (Vconst 1 (S m)))).
    lia. lia.
  Qed.

  Definition matRecover n (a : VF (S n)) : MF (S n) :=  
    Vmap (fun a => FMatrix.VA.id_vec (matRecover_sub_less n a)) a.

  Lemma matRecoverCorrect : forall n (mat : MF (S n)),
    MFisPermutation mat ->
    (forall i j (ip: i < S n)(ij : j < S n), 
    VF_sum (Vconst 1 i) = VF_sum (Vconst 1 j) -> i = j) ->

    let aVec := MF_CVmult mat (Vbuild (fun i (ip : i < S n) => VF_sum (Vconst 1 i))) in

    matRecover aVec = mat. intros. apply Veq_nth. intros.
    rewrite Vnth_map. rewrite MF_getRow_prod. unfold MFisPermutation  in H.
    apply andb_true_iff in H. destruct H. apply (bVforall_elim_nth ip) in H.
    apply bVexists_eq in H. elim H. intros. elim H2. intros. apply VF_beq_true in H3.
    rewrite H3. rewrite Vbuild_nth. unfold VF_inProd. 
    rewrite (FMatrix.VA.dot_product_id). rewrite Vbuild_nth. apply gen_equal.
    apply matRecover_sub_corr. lia. trivial. 
  Qed.

  Lemma transpose_eq : forall n (a b : MF n),
      a = b <-> FMatrix.mat_transpose a = FMatrix.mat_transpose b.
  Proof.
    intros. split; intros.
    + apply Veq_nth. intros. apply Veq_nth. intros. do 2 rewrite FMatrix.mat_build_nth.
      unfold FMatrix.get_elem. apply (Veq_nth4 ip0) in H. apply (Veq_nth4 ip) in H.
      trivial.
    + apply Veq_nth. intros. apply Veq_nth. intros.  apply (Veq_nth4 ip0) in H.
      apply (Veq_nth4 ip) in H. do 2 rewrite FMatrix.mat_build_nth in H.
      unfold FMatrix.get_elem in H.
      trivial.
  Qed.

End MatricesFIns.

