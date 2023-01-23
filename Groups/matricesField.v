Require Import Bool.
Require Import Setoid.
Require Import Ring.
Require Import Field.
Require Import Coq.ZArith.ZArith.
Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Matrix Vandermonde Gaussian.
Require Import groups.
Require Import vectorspace.
Require Import module.
Require Import matricesF.
(* Require Import VectorUtil. *)
Require Import CoLoR.Util.Vector.VecUtil. 
Require Import CoLoR.Util.Nat.NatUtil.
Require Import Lia.
Require Import VectorUtil.
Require Import Coq.Logic.ConstructiveEpsilon.
From mathcomp Require Import
   fintype bigop finset prime fingroup
  algebra.matrix
  algebra.ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module MatricesFieldIns (Field : FieldSig).

  Import Field.
  Module mat := MatricesFIns Field.
  Import mat.

  Module AL := RingAddationalLemmas Field.
  Module FAL := FieldAddationalLemmas Field.

  Definition VandermondeCol (m : nat)(c : F) := 
    Vbuild (fun i (ip : i < m) => VF_prod (Vconst c i)).

  Lemma VandermondeColBreak : forall (a b : nat)(c : F),
    (Vbreak (VandermondeCol (a+b) c)).1 = VandermondeCol a c.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_vbreak_1. lia.
    intros. do 2 rewrite Vbuild_nth. trivial. 
  Qed.

  Lemma VandermondeCol_remove : forall m c,
    Vremove_last (VandermondeCol (S m) c) = VandermondeCol m c.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_remove_last.
    do 2 rewrite Vbuild_nth. trivial.
  Qed.

  Definition VandermondeColGen (m : nat)(c : F)(base : nat) := 
    Vbuild (fun i (ip : i < m) => VF_prod (Vconst c (i+base))).

  Lemma VandermondeColBreakGen : forall (a b : nat)(c : F)(l : nat),
    (Vbreak (VandermondeColGen (a+b) c l)).1 = VandermondeColGen a c l.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_vbreak_1. lia.
    intros. do 2 rewrite Vbuild_nth. trivial. 
  Qed.
   
  Lemma VandermondeColGe_eq : forall (m : nat)(c : F),
    VandermondeCol m c = VandermondeColGen m c 0.
  Proof.
    intros. apply Veq_nth. intros. do 2 rewrite Vbuild_nth.
    apply VG_prod_const_index. lia. 
  Qed.  

  Lemma VandermondeCol_tail_rev : forall b e,
    Vtail (rev (VandermondeCol (S b) e)) = rev (VandermondeCol b e).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_tail. do 4 rewrite Vbuild_nth. 
    apply VG_prod_const_index. lia.  
  Qed.

  Lemma VandermondeColGen_tail : forall b e c,
    Vtail (VandermondeColGen (S b) e c) =
    VandermondeColGen b e (S c).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_tail. do 2 rewrite Vbuild_nth.
    apply VG_prod_const_index. lia.
  Qed.

  Lemma VandermondeCol_induct : forall b e c,
    (double_induct (VandermondeColGen (S b + S b) e c)) =
    VandermondeColGen (b + b) e (c+1).
  Proof.
    intros. apply Veq_nth. intros. unfold double_induct. 
    rewrite Vnth_remove_last. rewrite Vnth_tail. rewrite Vnth_cast.
    do 2 rewrite Vbuild_nth. apply VG_prod_const_index. lia.
  Qed.

  Definition Vandermonde (m : nat)(c : VF m) :=
    Vmap (VandermondeCol m) c.

  Lemma VF_inProd_build_div : forall n (a : VF n) b 
      (gen : (forall i, i< n -> F)),  
  b <> 0 ->
  VF_inProd a
  (Vbuild (fun j jp => gen j jp / b)) = 
      VF_sum (VF_mult a (Vbuild (fun j jp => gen j jp))) / b.
  Proof.
    intros. rewrite InProd_Sum. induction n. cbn. field. trivial.
    (* Induction step *)
    unfold VF_sum in *. rewrite Vfold_left_induction. 
    rewrite <- Vtail_map2. rewrite Vbuild_tail. rewrite IHn. 
    rewrite Vfold_left_induction.  do 2 rewrite Vhead_map2.
    destruct vs_field. destruct F_R. rewrite Rdistr_l. do 2 rewrite Vbuild_head.
    apply f_equal2. apply Rmul_assoc. apply f_equal2. apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_tail. rewrite Vnth_map2. 
    trivial. trivial. intros; field. intros; field. intros; field. intros; field.
  Qed.

  Lemma Vfold_left_inv : forall i0 a b,
    a = b ->
    Vfold_left Fmul 1 (Vconst (Finv 1) (0 + i0)) * a +
    b * Vfold_left Fmul 1 (Vconst (Finv 1) (1 + i0)) = 0.
  Proof.
    intros. rewrite H. induction i0. cbn. field. cbn. rewrite <- IHi0.
    destruct vs_field. destruct F_R. rewrite Radd_comm. apply f_equal2.
    + rewrite Rmul_comm. apply f_equal2; trivial. rewrite Vfold_left_const.
    rewrite Vfold_left_const.  cbn. intros; field. 
    intros; field.  intros; field. intros; field. intros; field.

    +  rewrite Rmul_comm. apply f_equal2; trivial.
  Qed. 

  Lemma VF_prod_zero : forall n (v : VF (S n)),
    VF_prod v = 0 -> exists i (ip : i < S n), Vnth v ip = 0.
  Proof.
    intros. unfold VF_prod in H. induction n. exists 0%nat. exists (lt_O_Sn 0). 
    rewrite Vfold_left_head in H. rewrite Vhead_nth in H. trivial.   intros. field.
    rewrite Vfold_left_induction in H.
    apply FAL.F_mul_zero in H. destruct H. exists 0%nat. exists (lt_O_Sn (S n)).
    rewrite Vhead_nth in H. trivial. apply IHn in H. elim H; intros. elim H0; intros.
    exists (S x). exists (lt_n_S x0). rewrite Vnth_tail in H1. trivial.
     intros; field. intros; field.
  Qed.

  Module SSRfield := makeField Field.

  Import SSRfield.
  
  Definition VandermondeInv m (c : VF m) :  MF m :=
    @Matrix_inv R_field  m (Vandermonde c).


  (* We now need to prove some lemmas which we need to make use of
  the Matrix.v libary *)
  Lemma vector_nth_eq : forall i A n (e : vector A n) (ip : i < n),
       Vnth e ip = Vector.nth e (Fin.of_nat_lt ip).
  Proof.
    induction i. destruct e. lia. cbn. trivial. intros. destruct n. lia.
    assert (i < n). lia. assert (ip = lt_n_S H). apply lt_unique. rewrite H0.
    rewrite <- Vnth_tail. rewrite IHi. cbn. rewrite (VSn_eq e). cbn. apply f_equal.
    apply f_equal. apply lt_unique.
  Qed.

  Definition nat_to_ord i n (ip : i < n) : 'I_n.
  Proof. 
   intros. apply (Matrix.introT ssrnat.ltP) in ip.
    apply (Ordinal ip).
  Defined.
  
  Lemma ord_comp : forall i n (ip : i < n), 
      finite_to_ord (Fin.of_nat_lt ip) = nat_to_ord ip.
  Proof.
    intros *.
    unfold finite_to_ord,
    nat_to_ord.
    rewrite Fin.to_nat_of_nat.
    reflexivity.
  Qed.

  
  
  Lemma comp_ord : forall i n (ip : i < n),
      ord_to_finite (nat_to_ord ip) = Fin.of_nat_lt ip.
  Proof.
    intros *.
    unfold ord_to_finite,
      nat_to_ord.
    rewrite Fin.of_nat_ext.
    reflexivity.
  Qed.
    
    
    
  (* I'm assuming a lemma of this already exists but I couldn't get it to work *)
  Lemma nat_eq_eq : forall (n n' : nat),
      (ssrnat.eqn n n') = true -> n = n'.
  Proof.
    induction n. intros. destruct n'. trivial. cbn in H. lia.
    intros. destruct n'. cbn in H. lia. cbn in H. apply IHn in H. lia.
  Qed.
  
  Lemma matrixId : forall n,
      MF_id n = @matrix_to_Matrix R_field n n (1%:M).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros.
    rewrite Vbuild_nth. symmetry. do 2 rewrite vector_nth_eq. 
    rewrite <- matrix_to_Matrix_correctness. do 2 rewrite ord_comp. destruct
                                             (Nat.eq_dec i0 i); intros.
    + subst. rewrite Vnth_replace. unfold  FSemiRingT.A1.
      rewrite id_A. cbn. rewrite ssrnat.eqnE. rewrite eqtype.eq_refl. trivial.
    + rewrite Vnth_replace_neq. rewrite Vnth_const. rewrite id_A. cbn.
      case_eq (ssrnat.eqn i0 i); intros. apply nat_eq_eq in H. lia. trivial. lia.
  Qed.


  Lemma fold_right_map {n : nat} :
    forall (l : list 'I_n) (f : 'I_n -> F),
      List.fold_right
        (applybig \o (fun j : 'I_n => BigBody j Fadd true (f j))) 0
      l  =
      List.fold_right Fadd 0
        (List.map f l).
  Proof.
    induction l.
    + intros; simpl.
      reflexivity.
    + intros; simpl.
      rewrite IHl.
      reflexivity.
  Qed.
    
  
  Lemma bigop_to_list : forall n (f : ordinal n -> F),
      \big[Fadd/0]_(j <- Finite.enum (ordinal_finType n)) (f j)
      = List.fold_left Fadd (List.map f (Finite.enum (ordinal_finType n))) 0.
  Proof.
    intros *.
    rewrite unlock /=.
    unfold reducebig.
    change (@seq.foldr ?A ?B) with (@List.fold_right B A).
    rewrite List.fold_symmetric.
    rewrite fold_right_map.
    reflexivity.
    all: intros; field.
 Qed.
    
    
    
  
  Lemma dot_eq : forall n (m m' : FMatrix.matrix n n) i i0
                        (ip : i < n)(ip0 : i0 < n),
      FMatrix.VA.dot_product (FMatrix.get_row m ip) (FMatrix.get_col m' ip0) =
  \big[Fadd/0]_(j <- Finite.enum (ordinal_finType n))
    (Matrix_to_matrix m' (nat_to_ord ip0) j * Matrix_to_matrix m j (nat_to_ord ip)).
  Proof.
    intros. destruct n. lia.  rewrite bigop_to_list. pose InProd_Sum.
    unfold VF_inProd in e.
    rewrite e. assert (forall a b, List.fold_left Fadd a b =  Vfold_left Fadd b (vec_of_list a)). induction a. cbn. trivial. intros. cbn. rewrite IHa. trivial. rewrite H.
    unfold VF_sum. remember
    (fun j : ordinal_finType (S n) => Matrix_to_matrix m' (nat_to_ord ip0) j *
          Matrix_to_matrix m j (nat_to_ord ip)) as f.
    assert (S n = length (List.map f  (Finite.enum (ordinal_finType (S n))))).
    rewrite List.map_length. symmetry. rewrite <- CommonSSR.ordinal_enum_size.
    rewrite CommonSSR.size_length. trivial.
    apply (Vfold_left_eq_gen H0). apply Veq_nth. intros. rewrite Vnth_cast.
    rewrite Vnth_map2. rewrite Vnth_map.
    rewrite (@Vnth_vec_of_list _ _ (f (nat_to_ord (lt_0_Sn n)))).
    rewrite List.map_nth. rewrite <- CommonSSR.nth_nth.
    assert (i1 < S n). rewrite H0. trivial.
    pose (CommonSSR.ordinal_enum (nat_to_ord H1)). rewrite e0.
    replace (Vnth_cast_aux H0 ip1) with H1. rewrite Heqf. destruct vs_field.
    destruct F_R. rewrite Rmul_comm. apply f_equal2.
    + unfold Matrix_to_matrix. rewrite mxE. unfold matrix_to_finite_fun.
      do 2 rewrite <- vector_to_finite_fun_correctness. unfold FMatrix.get_row.
      do 2 rewrite comp_ord. do 2 rewrite <- vector_nth_eq. trivial.
    + unfold Matrix_to_matrix. rewrite mxE. unfold matrix_to_finite_fun.
      do 2 rewrite <- vector_to_finite_fun_correctness. unfold FMatrix.get_row.
      do 2 rewrite comp_ord. do 2 rewrite <- vector_nth_eq. trivial.
      apply lt_unique.
  Qed.
  
  Lemma MF_mult_mult : forall n (m m' : MF n),
       MF_mult m' m = @Matrix_mul R_field n n n m m'.
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros.
    rewrite FMatrix.mat_build_nth. do 2 rewrite vector_nth_eq. unfold Matrix_mul.
    rewrite <- matrix_to_Matrix_correctness.
    unfold mulmx. cbn. do 2 rewrite ord_comp. rewrite mxE. apply dot_eq.
  Qed.
  
  Lemma toListExtend : forall n h (e : vector R_field n),
      (Vector.to_list (Vcons h e)) = List.cons h (Vector.to_list e).
  Proof.
    intros. cbn. trivial.
  Qed.
  
  Lemma uniq_change : forall n (e : vector R_field n),
    PairwisePredicate (fun x y : F => ~~ Fbool_eq x y) e ->
    seq.uniq (Vector.to_list e).
  Proof.
    intros. unfold seq.uniq. induction e; intros.
    + cbn. trivial.
    + rewrite toListExtend. apply Bool.andb_true_iff. split.
    ++ apply Bool.andb_true_iff in H. destruct H. apply negb_true_iff.
       apply not_true_is_false. unfold not. intros. clear IHe H0.
       assert (exists i (ip : i < n), Vnth e ip = h). induction e. cbn in H1.
       rewrite seq.in_nil in H1. lia. rewrite seq.in_cons in H1.
       apply orb_true_iff in H1. destruct H1. exists 0%nat. exists (lt_0_Sn n).
       cbn. apply F_bool_eq_corr in H0. rewrite H0. trivial. apply IHe in H0. elim H0.
       intros. elim H1. intros. exists (S x).
       exists (lt_n_S x0). cbn. rewrite <- H2. apply Vnth_eq. trivial.
       cbn in H.  apply Bool.andb_true_iff in H. destruct H. trivial.
       elim H0; intros. elim H2; intros. apply (bVforall_elim_nth x0) in H.
       apply negb_true_iff in H. apply F_bool_neq_corr in H. apply H.
       rewrite H3. trivial.
    ++ apply IHe. cbn in H.  apply Bool.andb_true_iff in H. destruct H. trivial.
  Qed.
  
  Lemma Vnth_list_pos : forall n (e : vector R_field n) i (ip : i < n) y,
    seq.nth y (Vector.to_list e) (finite_to_ord (Fin.of_nat_lt ip)) = Vnth e ip.
  Proof.
    induction e. intros. rewrite ord_comp. lia. destruct i. cbn. trivial. intros.
    rewrite ord_comp. unfold seq.nth. rewrite toListExtend. cbn.
    pose (IHe i (lt_S_n ip) y). symmetry in e0. rewrite e0. apply f_equal.
    rewrite ord_comp. cbn. trivial.
  Qed.

  Lemma Vander_eq_sub : forall a i0,
      (fix loop (m : nat) : R :=
     match m with
     | 0%nat => 1
     | 1%nat => a
     | S (S _ as i1) => a * loop i1
     end) i0 = VF_prod (Vconst a i0).
  Proof.
    intros. induction i0. cbn. trivial. rewrite IHi0. destruct vs_field.
    destruct F_R. destruct i0. cbn. rewrite Rmul_1_l. trivial. simpl.
    unfold VF_prod. symmetry. rewrite Vfold_left_Vcons_Fmul. rewrite Rmul_comm.
    trivial.
  Qed.

  Lemma Vander_eq : forall n (e : vector R_field n),
      Vandermonde e = Matrix_vandermonde e.
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. rewrite Vnth_map.
    rewrite Vbuild_nth. symmetry. do 2 rewrite vector_nth_eq.
    unfold Matrix_vandermonde. rewrite <- matrix_to_Matrix_correctness.
    unfold vandermonde. rewrite mxE. rewrite Vnth_list_pos. rewrite ord_comp.
    cbn. apply Vander_eq_sub.
  Qed.
  
  (* Resuming main now the related proofs are done. *)
  
  Lemma invVandermondeRight : forall (n : nat)(e : VF n),
    PairwisePredicate (fun x y => negb (Fbool_eq x y)) e ->
    MF_mult (Vandermonde e) (VandermondeInv e) = MF_id n.
  Proof.
    intros. rewrite matrixId. rewrite MF_mult_mult. unfold VandermondeInv.
    apply (@vandermonde_left_inverse_Matrix R_field n e). apply uniq_change.
    trivial. apply Vander_eq.
  Qed.

  Lemma invVandermondeLeft : forall (n : nat)(e : VF n),
    PairwisePredicate (fun x y => negb (Fbool_eq x y)) e ->
    MF_mult  (VandermondeInv e) (Vandermonde e) = MF_id n.
  Proof.
    intros. rewrite matrixId. rewrite MF_mult_mult. unfold VandermondeInv.
    apply (@vandermonde_right_inverse_Matrix R_field n e). apply uniq_change.
    trivial. apply Vander_eq.
  Qed. 

  Lemma VandermondeHead : forall (m n : nat)(e : F)
      (a : vector (VF m) (S n)),
    Vhead (FMatrix.mat_mult [VandermondeCol (S n) e] a) =
    VF_add (Vhead a) (Vfold_left (VF_add (n:=m)) (VF_zero m)
        (Vmap2 (VF_scale (n:=m)) (Vtail a)
           (Vtail (VandermondeCol (S n) e)))).
  Proof.
    intros. rewrite Vhead_nth. apply Veq_nth. intros. 
    rewrite FMatrix.mat_mult_elem. unfold FMatrix.get_row. 
    rewrite <- Vhead_nth. rewrite Vnth_map2. rewrite Vfold_left_VF_add.
    unfold FSemiRingT.Aplus. destruct vs_field. destruct F_R.
    rewrite Radd_comm. rewrite <- Vfold_left_Vcons_Fadd.
    unfold FMatrix.VA.dot_product. remember VandermondeCol as x.
    rewrite Vfold_left_Fadd_eq. apply f_equal. simpl. apply Vcons_eq_intro.
    rewrite Heqx. rewrite Vhead_map. rewrite Vbuild_head. cbn. 
    unfold FSemiRingT.Amult. rewrite Rmul_1_l. trivial.
    apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
    rewrite Vnth_map. unfold FSemiRingT.Amult. do 3 rewrite Vnth_tail.
    rewrite Vnth_map. apply Rmul_comm.
  Qed.

  Lemma F_mul_zero : forall (a b : F),
    a * b = 0 -> a = 0 \/ b = 0.
  Proof.
    destruct vs_field. destruct F_R. intros. case_eq (Fbool_eq a 0). intros. 
    apply F_bool_eq_corr in H0. left. trivial. right. apply F_bool_neq_corr in H0. 
    apply (AL.Fmul_left_cancel (FmulInv a)) in H. rewrite Rmul_assoc in H.
    rewrite Finv_l in H; auto. ring_simplify in H. trivial.
  Qed. 
      

  Lemma VF_prod_const_Nzero : forall (c : F)(i : nat),
    c <> 0 ->
    VF_prod (Vconst c i) <> 0.
  Proof.
    intros. induction i. cbn. apply vs_field. simpl. unfold not. intros.
    apply IHi. unfold VF_prod in H0. rewrite Vfold_left_Vcons_Fmul in H0.
    apply F_mul_zero in H0. destruct H0. trivial. contradiction.
  Qed.

  Definition VF_inv n (v1 : VF n) : VF n :=
    Vmap FmulInv v1.
  
  Lemma VF_inv_corr : forall n (v1 : VF n),
    Vforall (fun x => x <> 0) v1 ->
    VF_mult v1 (VF_inv v1) = VF_one n.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_const.
    rewrite Vnth_map. field; auto. apply (Vforall_nth ip) in H. apply H.
  Qed.

  Lemma FmulInv_VF_prod_Vconst : forall i a,
    a <> 0 ->
    FmulInv (VF_prod (Vconst a i)) = VF_prod (Vconst (FmulInv a) i).
  Proof.
    intros. induction i. cbn. field; auto. apply vs_field.
    simpl. unfold VF_prod in *. do 2 rewrite Vfold_left_Vcons_Fmul. 
    rewrite <- IHi. field; auto. split. auto. apply VF_prod_const_Nzero. auto.
  Qed. 

  Lemma VandermondeColDiv : forall m a,
    a <> 0 ->
    Vmap2 Fmul (VF_inv (Vtail (Vtail (VandermondeCol (S (S m)) a))))
              (Vremove_last (Vtail (VandermondeCol (S (S m)) a))) = 
    Vconst (FmulInv a) m.
  Proof.
    intros. apply Veq_nth; intros. rewrite Vnth_map2. rewrite Vnth_map.
    rewrite Vnth_remove_last. do 3 rewrite Vnth_tail. do 2 rewrite Vbuild_nth.
    rewrite FmulInv_VF_prod_Vconst. trivial. rewrite Vnth_const.
    induction i.  cbn. field; auto. unfold VF_prod.
    assert (Vfold_left Fmul 1 (Vconst (FmulInv a) (S (S (S i)))) *
Vfold_left Fmul 1 (Vconst a (S (S i))) = Vfold_left Fmul 1 (Vconst (FmulInv a) (S (S i))) *
Vfold_left Fmul 1 (Vconst a  (S i))). do 5 rewrite Vconst_cons.
    do 5 rewrite Vfold_left_Vcons_Fmul. field; auto. rewrite H0.
    apply IHi. lia. trivial.
  Qed. 

  Lemma VandermondeColDiv2 : forall m a,
    a <> 0 ->
    Vmap2 Fmul ((Vtail (Vtail (VandermondeCol (S (S m)) (FmulInv a)))))
              (Vremove_last (Vtail (VandermondeCol (S (S m)) a))) = 
    Vconst (FmulInv a) m.
  Proof.
    intros. rewrite <- VandermondeColDiv; auto. apply Veq_nth; intros. 
    do 2 rewrite Vnth_map2. apply f_equal2; auto. rewrite Vnth_map.
    do 4 rewrite Vnth_tail. do 2 rewrite Vbuild_nth. rewrite FmulInv_VF_prod_Vconst.
    trivial. trivial.
  Qed. 


End MatricesFieldIns.

