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

Notation vector := Vector.t.
Notation Vconst := Vector.const.

(*
    This contains The 
*)

Set Implicit Arguments.

Module Type MatricesF (Ring: RingSig).

  Import Ring.

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
    Vfold_left andb false (Vbuild (fun i ip => VF_beq v (FMatrix.VA.id_vec ip))).

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
    intros. induction i. left. trivial. right. omega.
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

  Lemma VF_sum_induction :
    forall(N : nat)(v : VF (1+N)),
    VF_sum v = VF_sum (Vtail v) + (Vhead v).
  Proof.
    intros. remember (VF_sum (Vtail v) + Vhead v) as b.
    rewrite (VSn_eq v). rewrite Heqb. cbn. rewrite Vfold_Fadd_const.
    trivial.
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
    omega. apply Vnth_eq. trivial.
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
    rewrite i. apply VF_eq_corr. intros. apply F_bool_eq_corr.
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
    unfold FSemiRingT.Aplus. rewrite Radd_comm. rewrite Radd_0_l.
    trivial. apply r. apply r.
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
    trivial. apply r.
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
    rewrite Radd_comm. trivial. apply r.
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
    do 4 rewrite Vnth_map2. rewrite Radd_assoc. trivial.
    apply r.
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

  Lemma Vfold_left_Vadd_VFadd :
    forall (n n' : nat)(a : (VF n))(b : vector (VF n) n'),
    Vfold_left (VF_add (n:=n)) (VF_zero n) (Vadd b a) =
    VF_add (Vfold_left (VF_add (n:=n)) (VF_zero n) b) a.
  Proof.
    intros. induction b. cbn. trivial. 
    cbn. do 2 rewrite <- Vfold_VFadd_const. symmetry. rewrite VF_comm.
    rewrite <- VF_add_ass. apply f_equal2; auto. rewrite IHb. apply VF_comm.
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

  Lemma VF_neg_eq : forall N (a : VF N) e,
    VF_scale a (Finv e) = VF_neg (VF_scale a e).
  Proof.
    intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. cbn in *. 
    assert (forall a b : F, a * (Finv b) = Finv(a*b)). intros. ring; auto.
    apply H.
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

  Lemma invComm : 
   forall (N : nat)(X Y : MF N),
   MF_mult X Y = MF_id N ->
   MF_mult Y X = MF_id N ->
   MF_mult X Y = MF_mult Y X.
  Proof.
    intros. rewrite H. rewrite H0. trivial.
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
    

End MatricesF.

Module MatricesFIns (Ring: RingSig) <: MatricesF Ring.

  Import Ring.

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
    Vfold_left andb false (Vbuild (fun i ip => VF_beq v (FMatrix.VA.id_vec ip))).

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
    intros. induction i. left. trivial. right. omega.
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

  Lemma VF_sum_induction :
    forall(N : nat)(v : VF (1+N)),
    VF_sum v = VF_sum (Vtail v) + (Vhead v).
  Proof.
    intros. remember (VF_sum (Vtail v) + Vhead v) as b.
    rewrite (VSn_eq v). rewrite Heqb. cbn. rewrite Vfold_Fadd_const.
    trivial.
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
    omega. apply Vnth_eq. trivial.
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
    rewrite i. apply VF_eq_corr. intros. apply F_bool_eq_corr.
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
    unfold FSemiRingT.Aplus. rewrite Radd_comm. rewrite Radd_0_l.
    trivial. apply r. apply r.
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
    trivial. apply r.
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
    rewrite Radd_comm. trivial. apply r.
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
    do 4 rewrite Vnth_map2. rewrite Radd_assoc. trivial.
    apply r.
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

  Lemma Vfold_left_Vadd_VFadd :
    forall (n n' : nat)(a : (VF n))(b : vector (VF n) n'),
    Vfold_left (VF_add (n:=n)) (VF_zero n) (Vadd b a) =
    VF_add (Vfold_left (VF_add (n:=n)) (VF_zero n) b) a.
  Proof.
    intros. induction b. cbn. trivial. 
    cbn. do 2 rewrite <- Vfold_VFadd_const. symmetry. rewrite VF_comm.
    rewrite <- VF_add_ass. apply f_equal2; auto. rewrite IHb. apply VF_comm.
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

  Lemma VF_neg_eq : forall N (a : VF N) e,
    VF_scale a (Finv e) = VF_neg (VF_scale a e).
  Proof.
    intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. cbn in *. 
    assert (forall a b : F, a * (Finv b) = Finv(a*b)). intros. ring; auto.
    apply H.
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

  Lemma invComm : 
   forall (N : nat)(X Y : MF N),
   MF_mult X Y = MF_id N ->
   MF_mult Y X = MF_id N ->
   MF_mult X Y = MF_mult Y X.
  Proof.
    intros. rewrite H. rewrite H0. trivial.
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

End MatricesFIns.
