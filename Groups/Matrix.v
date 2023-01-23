Require Import Field_theory
  Ring_theory List NArith
  Ring Field Utf8 Lia Vector
  Coq.Arith.PeanoNat Fin Lia LinIndep
  Gaussian CommonSSR Vandermonde
  Epsilon FunctionalExtensionality
  ProofIrrelevance.
From mathcomp Require Import
  all_ssreflect algebra.matrix
  algebra.ssralg.
Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import
  eqtype fingroup fintype ssrnat seq finalg ssralg.
From mathcomp Require Import
  bigop gproduct finset div.

Require Import vectorspace module.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module makeField (f : FieldSig).

  Import f.
  Module AL := RingAddationalLemmas f.

  Definition R := F.
  
  Definition eqr (r1 r2 : R) : bool := Fbool_eq r1 r2.
  
  Lemma eqrP : Equality.axiom eqr.
  Proof.
    unfold Equality.axiom. intros. rewrite /eqr. apply introP; intros.
    apply F_bool_eq_corr in H. trivial. apply Bool.negb_true_iff in H.
    apply F_bool_neq_corr in H. trivial.
  Qed.
  
  Canonical Structure R_eqMixin := EqMixin eqrP.
  Canonical Structure R_eqType := Eval hnf in EqType R R_eqMixin.

  Fact inhR : inhabited R.
  Proof. exact: (inhabits f.Fzero). Qed.

  Definition pickR (P : pred R) (n : nat) :=
  let x := epsilon inhR P in if P x then Some x else None.

  Fact pickR_some P n x : pickR P n = Some x -> P x.
  Proof. by rewrite /pickR; case: (boolP (P _)) => // Px [<-]. Qed.

  Fact pickR_ex (P : pred R) :
    (exists x : R, P x) -> exists n, pickR P n.
  Proof. by rewrite /pickR; move=> /(epsilon_spec inhR)->;
    exists 0%N.
  Qed.

  Fact pickR_ext (P Q : pred R) : P =1 Q -> pickR P =1 pickR Q.
  Proof.
  move=> PEQ n; rewrite /pickR; set u := epsilon _ _; set v := epsilon _ _.
  suff->: u = v by rewrite PEQ.
  by congr epsilon; apply: functional_extensionality=> x; rewrite PEQ.
  Qed.

  Definition R_choiceMixin : choiceMixin R :=
  Choice.Mixin pickR_some pickR_ex pickR_ext.

  Canonical R_choiceType := Eval hnf in ChoiceType R R_choiceMixin.

  Lemma radd_assoc : associative f.Fadd.
  Proof.
    move =>x y z. field.
  Qed.

  
  Lemma radd_comm : commutative f.Fadd.
  Proof.
    move =>x y. field.
  Qed.

  Lemma radd_left_id : left_id f.Fzero f.Fadd.
  Proof.
    move => x. field.
  Qed.
  
  Lemma radd_left_inv : left_inverse f.Fzero f.Finv f.Fadd.
  Proof.
    move =>x. field.
  Qed.

  Definition R_zmodmixin :=
      ZmodMixin radd_assoc radd_comm radd_left_id radd_left_inv.

 
  Canonical R_zmodtype := ZmodType R R_zmodmixin.
  

  Lemma rmul_assoc : @associative (GRing.Zmodule.sort R_zmodtype) f.Fmul.
  Proof.
    unfold associative. intros x y z. unfold R_zmodtype, ZmodType in *. destruct vs_field. destruct F_R. apply Rmul_assoc.
  Qed.
  
  Lemma rmul_comm : commutative f.Fmul.
  Proof.
    move =>x y. field.
  Qed.
  

  Lemma rmul_left_id : left_id Fone Fmul.
  Proof.
    move =>x. field.
  Qed.
  
  Lemma rmul_dist_l : left_distributive Fmul Fadd.
  Proof.
    move =>x y z. field.
  Qed.

  Lemma rO_neq_rI : is_true (negb (eqr Fone Fzero)).
  Proof.
    intros. apply Bool.negb_true_iff. apply F_bool_neq_corr. destruct vs_field.
    apply F_1_neq_0.
  Qed.
  
  
  Definition R_comringmixin :=
    ComRingMixin rmul_assoc rmul_comm
    rmul_left_id rmul_dist_l rO_neq_rI.


  Canonical R_ring := RingType R R_comringmixin.
  Canonical R_comring := ComRingType R rmul_comm.

  Import Monoid.

  Lemma radd_right_id : right_id Fzero Fadd.
  Proof.
    move => x. field.
  Qed.

  Lemma rmul_right_id : right_id Fone Fmul.
  Proof.
    intro. field.
  Qed.


  Canonical Radd_monoid :=
    Law radd_assoc radd_left_id radd_right_id.
  Canonical Radd_comoid :=
    ComLaw radd_comm.

  Canonical Rmul_monoid := Law rmul_assoc rmul_left_id rmul_right_id.
  Canonical Rmul_comoid := ComLaw rmul_comm.

 
  Lemma rmul_0_l : left_zero Fzero Fmul.
  Proof.
    move => x. field.
  Qed.

  Lemma rmul_0_r : right_zero Fzero Fmul.
  Proof.
    move => x. field.
  Qed.

  Lemma rmul_plus_dist_l : left_distributive Fmul Fadd.
  Proof.
    move => x y z. field.
  Qed.

  Lemma rmul_plus_dist_r : right_distributive Fmul Fadd.
  Proof.
    move => x y z. field.
  Qed.
  
  Canonical Rmul_mul_law := MulLaw rmul_0_l rmul_0_r.
  Canonical Radd_add_law :=
    AddLaw rmul_plus_dist_l rmul_plus_dist_r.

  Definition Rinvx r := if (negb (eqr r Fzero)) then FmulInv r else r.

  Definition unit_R r := negb (eqr r Fzero).

  Lemma RmultRinvx : {in unit_R, left_inverse Fone Rinvx Fmul}.
  Proof.
    move=>r; rewrite -topredE /unit_R /Rinvx => /= rNZ /=.
    rewrite rNZ. destruct vs_field. apply Finv_l. apply Bool.negb_true_iff in rNZ.
    apply F_bool_neq_corr in rNZ. trivial.
  Qed.
  
  Lemma Finv_r: ∀ p : R, negb (eqr p Fzero) → Fmul p (FmulInv p) = Fone.
  Proof.
    intros ? Hp. field.  apply Bool.negb_true_iff in Hp.
    apply F_bool_neq_corr in Hp. trivial.
  Qed.

  Lemma RinvxRmult : {in unit_R, right_inverse Fone Rinvx Fmul}.
  Proof.
    move=> r; rewrite -topredE /unit_R /Rinvx => /= rNZ /=.
    by rewrite rNZ Finv_r //; apply/eqP.
  Qed.

  Lemma intro_unit_R x y :
    Fmul y x = Fone /\ Fmul x y = Fone -> unit_R x.
  Proof.
    intros. destruct H. unfold unit_R. apply Bool.negb_true_iff.
    apply F_bool_neq_corr. unfold not. intros. destruct vs_field.
    apply F_1_neq_0. rewrite H1 in H. rewrite rmul_0_r in H. rewrite H. trivial.
  Qed.

  Lemma Rinvx_out : {in predC unit_R, Rinvx =1 id}.
  Proof. by move=> x; rewrite inE /= /Rinvx -if_neg => ->. Qed.

  Definition R_unitRingMixin :=
    UnitRingMixin RmultRinvx RinvxRmult intro_unit_R Rinvx_out.

  Canonical Structure R_unitRing :=
    Eval hnf in UnitRingType R R_unitRingMixin.

  Canonical Structure R_comUnitRingType :=
    Eval hnf in [comUnitRingType of R].

  Lemma R_idomainMixin (x y : R) : Fmul x y = Fzero -> (x == Fzero) || (y == Fzero).
  Proof.
    intros. apply Bool.orb_true_iff. case_eq (eqr x 0); intros.
    apply F_bool_eq_corr in H0. left. apply F_bool_eq_corr. trivial.
    right. apply F_bool_eq_corr. apply F_bool_neq_corr in H0.
    apply (AL.Fmul_left_cancel (FmulInv x)) in H. rewrite Rmul_assoc in H.
    destruct vs_field. rewrite Finv_l in H; auto. ring_simplify in H. trivial.
    apply vs_field.
  Qed.

  Canonical Structure R_idomainType :=
    Eval hnf in IdomainType R R_idomainMixin.
  
  Lemma R_fieldMixin : GRing.Field.mixin_of [unitRingType of R].
  Proof. done. Qed.

  Definition R_fieldIdomainMixin := FieldIdomainMixin R_fieldMixin.

  Canonical Structure R_field := FieldType R R_fieldMixin.
    
End makeField.


Section Mat.

  Variable (R : Type).

  Lemma vector_inv_0 (v : Vector.t R 0) :
    v = @Vector.nil R.
  Proof.
    refine (match v with
            | @Vector.nil _ => _
            end).
    reflexivity.
  Defined.

  Lemma vector_inv_S (n : nat) (v : Vector.t R (S n)) :
    {x & {v' | v = @Vector.cons _ x _ v'}}.
  Proof.
    refine (match v with
            | @Vector.cons _ x _ v' =>  _
            end).
    eauto.
  Defined.

  Lemma fin_inv_0 (i : Fin.t 0) : False.
  Proof. refine (match i with end). Defined.

  Lemma fin_inv_S (n : nat) (i : Fin.t (S n)) :
    (i = Fin.F1) + {i' | i = Fin.FS i'}.
  Proof.
    refine (match i with
            | Fin.F1 _ => _
            | Fin.FS _ _ => _
            end); eauto.
  Defined.


  Definition vector_to_finite_fun :
    forall n, Vector.t R n -> (Fin.t n -> R).
  Proof.
    induction n.
    + intros v f.
      apply fin_inv_0 in f.
      refine (match f with end).
    + intros v f.
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      destruct (fin_inv_S f) as [h | [t p]].
      exact vhd.
      exact (IHn vtl t).
  Defined.



  Definition finite_fun_to_vector :
    forall n,  (Fin.t n -> R) -> Vector.t R n.
  Proof.
    induction n.
    + intros f.
      apply Vector.nil.
    + intros f.
      apply Vector.cons.
      apply f, Fin.F1.
      apply IHn;
      intro m.
      apply f, Fin.FS, m.
  Defined.


  Lemma finite_fun_to_vector_correctness
    (m : nat) (f : Fin.t m -> R) (i : Fin.t m) :
    Vector.nth (finite_fun_to_vector f) i = f i.
  Proof.
    induction m.
    - inversion i.
    - pose proof fin_inv_S i as [-> | (i' & ->)].
      + reflexivity.
      + cbn.
        now rewrite IHm.
  Defined.


  Lemma vector_to_finite_fun_correctness
    (m : nat) (v : Vector.t R m) (i : Fin.t m) :
    Vector.nth v i = (vector_to_finite_fun v) i.
  Proof.
    induction m.
    - inversion i.
    - pose proof fin_inv_S i as [-> | (i' & ->)].
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      rewrite vp.
      reflexivity.
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      rewrite vp;
      simpl;
      now rewrite IHm.
  Defined.

  Lemma vector_finite_back_forth :
    forall (n : nat) (v : Vector.t R n),
    v = finite_fun_to_vector (vector_to_finite_fun v).
  Proof.
    induction n.
    + intros v.
      pose proof (vector_inv_0 v) as Hv.
      subst;
      reflexivity.
    + intros v.
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      subst; simpl; f_equal.
      apply IHn.
  Defined.
      


  
End Mat.

 
Section Reflection.

  (* These two are just need because it's
    opaque in library *)
  Lemma introT :
    forall (P : Prop) (b : bool),
    reflect P b -> P -> b.
  Proof.
    intros ? ? Hr Hp.
    case b eqn:Ht.
    constructor.
    inversion Hr as [_ | Hrt].
    unfold not in Hrt.
    specialize (Hrt Hp).
    exfalso.
    exact Hrt.
  Defined.

  Lemma elimT :
    forall (P : Prop) (b : bool),
    reflect P b -> b -> P.
  Proof.
    intros ? ? Hr H.
    case b eqn:Hb.
    inversion Hr as [Hrt | _].
    exact Hrt.
    refine (match H with end).
  Defined.



End Reflection.


Section Mx.

  Variable (R : Type).

  Definition F n m := Vector.t (Vector.t R n) m.

  (* Thomas: I see you have renamed/deleted it to F
     but it won't compile because all the functions
     uses Matrix. Feel to change it again.
     I brought it because I needed to compile the
     code base*)
  Definition Matrix n m := Vector.t (Vector.t R n) m.
  
  Definition finite_fun_to_matrix {n m}
    (f : Fin.t n -> Fin.t m -> R) : Matrix n m :=
    @finite_fun_to_vector _ m (fun (x : Fin.t m) =>
      @finite_fun_to_vector _ n (fun (y : Fin.t n) => f y x)).

  Definition matrix_to_finite_fun {n m}
    (mx : Matrix n m) : Fin.t n -> Fin.t m -> R :=
    fun (x : Fin.t n) (y : Fin.t m) =>
      @vector_to_finite_fun _ n
        ((@vector_to_finite_fun _ m mx) y) x.

  Lemma matrix_to_finite_back_forth :
    forall n m (mx : Matrix n m),
    mx = finite_fun_to_matrix (matrix_to_finite_fun mx).
  Proof.
    intros ? ?.
    revert n.
    induction m.
    + intros ? ?.
      unfold Matrix in mx.
      pose proof (vector_inv_0 mx) as Hn.
      subst; reflexivity.
    + intros ? ?.
      unfold Matrix in mx.
      destruct (vector_inv_S mx) as (vhd & vtl & vp).
      subst.
      unfold finite_fun_to_matrix,
      matrix_to_finite_fun.
      simpl; f_equal.
      apply vector_finite_back_forth.
      apply IHm.
  Defined.



  Definition finite_to_ord {n} (f : Fin.t n) : 'I_n.
    destruct (Fin.to_nat f) as [m Hm].
    apply (introT ltP) in Hm.
    apply (Ordinal Hm).
  Defined.

  

  Definition ord_to_finite {n} (x : 'I_n) : Fin.t n.
    have Hx: x < n by [].
    apply (elimT ltP) in Hx.
    apply (Fin.of_nat_lt Hx).
  Defined.



  Definition Matrix_to_matrix {n m}
    (mx : Matrix n m) : 'M[R]_(n, m) :=
    \matrix_(i < n, j < m)
      (matrix_to_finite_fun
        mx
        (ord_to_finite i)
        (ord_to_finite j)).

  Definition matrix_to_Matrix {n m}
    (mx : 'M[R]_(n, m)) : Matrix n m :=
    finite_fun_to_matrix (fun (i : Fin.t n)
      (j : Fin.t m) =>
      mx (finite_to_ord i) (finite_to_ord j)).


  Lemma matrix_to_Matrix_correctness :
    forall n m (i : Fin.t n) (j : Fin.t m)
    (mx : 'M[R]_(n, m)),
    mx (finite_to_ord i) (finite_to_ord j) =
    Vector.nth (Vector.nth (matrix_to_Matrix mx) j) i.
  Proof.
    intros *.
    unfold matrix_to_Matrix,
    finite_fun_to_matrix.
    rewrite finite_fun_to_vector_correctness.
    rewrite finite_fun_to_vector_correctness.
    reflexivity.
  Defined.
    

  
  Lemma finite_to_ord_correctness n (i : Fin.t n) :
    ord_to_finite (finite_to_ord i) = i.
  Proof.
    induction n.
    + inversion i.
    + pose proof fin_inv_S i as [-> | (i' & ->)].
      ++ cbn; reflexivity.
      ++  specialize (IHn i').
          unfold
          finite_to_ord,
          ord_to_finite
          in * |- *.
          cbn in * |- *.
          destruct (Fin.to_nat i') as [a Ha].
          cbn.
          f_equal.
          cbn in *.
          rewrite Fin.of_nat_ext.
          rewrite Fin.of_nat_ext in IHn.
          exact IHn.
  Qed.


  Lemma ord_to_finite_correctness n (i : 'I_n) :
    finite_to_ord (ord_to_finite i) = i.
  Proof.
    unfold finite_to_ord,
      ord_to_finite.
    rewrite Fin.to_nat_of_nat.
    destruct i; cbn.
    f_equal.
    apply bool_irrelevance.
  Qed.
  
   Lemma vector_to_finite_simp :
    forall n m (mx : Matrix n m) (i : Fin.t n)
    (j : Fin.t m),
    vector_to_finite_fun (vector_to_finite_fun mx j) i =
    (Matrix_to_matrix mx) (finite_to_ord i) (finite_to_ord j).
  Proof.
    intros *.
    rewrite matrix_to_Matrix_correctness.
    repeat rewrite vector_to_finite_fun_correctness.
    rewrite -!vector_to_finite_fun_correctness.
    rewrite -matrix_to_Matrix_correctness mxE.
    rewrite !finite_to_ord_correctness.
    unfold matrix_to_finite_fun.
    rewrite !vector_to_finite_fun_correctness.
    reflexivity.
  Defined.
    
 
 

  Lemma Matrix_back_and_forth_same :
    forall (n m : nat) (mx : 'M[R]_(n, m)),
    mx = Matrix_to_matrix (matrix_to_Matrix mx).
  Proof.
    move=> n m mx.
    apply/matrixP => i j.
    rewrite /Matrix_to_matrix mxE.
    rewrite /matrix_to_finite_fun /=.
    rewrite -!vector_to_finite_fun_correctness.
    rewrite -matrix_to_Matrix_correctness.
    by rewrite !ord_to_finite_correctness.
  Qed.


End Mx.

Section Minv.

  Variable (R : fieldType).

  Definition Matrix_inv {n : nat} (mx : Matrix R n n) :
    Matrix R n n :=
    matrix_to_Matrix (invmx (Matrix_to_matrix mx)).
    
  Definition Matrix_det {n : nat}
    (mx : Matrix R n n) : R :=
    determinant (Matrix_to_matrix mx).

  Definition Matrix_transpose {n m : nat}
    (v : Matrix R n m) : Matrix R m n :=
    finite_fun_to_vector (fun i : Fin.t n =>
      (finite_fun_to_vector (fun j : Fin.t m =>
        Vector.nth (Vector.nth v j) i))).

  Theorem transpose_inv (m n : nat) (M : Matrix R m n) :
    Matrix_transpose (Matrix_transpose M) = M.
  Proof.
    unfold Matrix_transpose.
    eapply eq_nth_iff.
    intros ? ? ->.
    rewrite finite_fun_to_vector_correctness.
    eapply eq_nth_iff.
    intros ? ? ->.
    rewrite !finite_fun_to_vector_correctness.
    reflexivity.
  Qed.
  
  Definition Matrix_mul {m n p : nat}
    (A : Matrix R m n) (B : Matrix R n p) :
    Matrix R m p :=
    matrix_to_Matrix
      (mulmx (Matrix_to_matrix A) (Matrix_to_matrix B)).


  (* Matrix_inv function is pointwise equal to invmx *)
  Lemma Matrix_inv_is_point_wise_equal_to_invmx_matrix :
    forall n (i : Fin.t n) (j : Fin.t n)
      (mx : Matrix R n n),
      Vector.nth (Vector.nth (@Matrix_inv n mx) j) i =
      invmx
        (Matrix_to_matrix mx)
        (finite_to_ord i)
        (finite_to_ord j).
  Proof.
    intros *; symmetry.
    rewrite matrix_to_Matrix_correctness.
    reflexivity.
  Defined.


  Lemma inverse_matrix_gen :
    forall (n:nat) (A: 'M[R]_(n, n)),
    (A \in unitmx ->
    mulmx A (invmx A) = 1%:M /\
    mulmx (invmx A) A = 1%:M)%R.
  Proof.
    intros; split.
    + by apply mulmxV.
    + by apply mulVmx.
  Defined.


  Lemma left_inverse_Matrix :
    forall (n : nat) (mx : Matrix R n n),
    (Matrix_to_matrix mx) \in unitmx ->
    Matrix_mul (Matrix_inv mx) mx =
    matrix_to_Matrix (1%:M).
  Proof.
    intros ? ? Hm.
    unfold Matrix_mul.
    f_equal.
    unfold Matrix_inv.
    remember ((invmx (Matrix_to_matrix mx))) as mxt.
    rewrite <-Matrix_back_and_forth_same.
    subst.
    destruct (inverse_matrix_gen Hm) as [Hl Hr].
    assumption.
  Qed.

  
  Lemma right_inverse_Matrix :
    forall (n : nat) (mx : Matrix R n n),
    (Matrix_to_matrix mx) \in unitmx ->
    Matrix_mul mx (Matrix_inv mx) =
    matrix_to_Matrix (1%:M).
  Proof.
    intros ? ? Hm.
    unfold Matrix_mul.
    f_equal.
    unfold Matrix_inv.
    remember ((invmx (Matrix_to_matrix mx))) as mxt.
    rewrite <-Matrix_back_and_forth_same.
    subst.
    destruct (inverse_matrix_gen Hm) as [Hl Hr].
    assumption.
  Qed.
  
End Minv.


Section Vander.
  
  Variable (R : fieldType).

  
  Definition Matrix_vandermonde {n : nat} (v : Vector.t R n) :
    Matrix R n n := matrix_to_Matrix
      (@Vandermonde.vandermonde R n n (Vector.to_list v)).

  
  Lemma vander_in_unitmx :
    forall (n : nat) (v : Vector.t R n),
    uniq (Vector.to_list v) ->
    (Matrix_to_matrix (@Matrix_vandermonde n v)) \in unitmx.
  Proof.
    intros ? ? H.
    unfold Matrix_vandermonde.
    rewrite <-Matrix_back_and_forth_same.
    apply vandermonde_unitmx.
    exact H.
    pose proof VectorSpec.length_to_list _ n v as Hl.
    auto.
  Qed.



  Lemma vandermonde_left_inverse_Matrix :
    forall (n : nat) (v : Vector.t R n) mx,
    uniq (Vector.to_list v) ->
    mx = Matrix_vandermonde v ->
    @Matrix_mul R n n n (@Matrix_inv R n mx) mx =
    matrix_to_Matrix (1%:M).
  Proof.
    intros * Hu Hmx.
    apply left_inverse_Matrix.
    subst;
    exact (vander_in_unitmx Hu).
  Qed.



  Lemma vandermonde_right_inverse_Matrix :
    forall (n : nat) (v : Vector.t R n) mx,
    uniq (Vector.to_list v) ->
    mx = Matrix_vandermonde v ->
    @Matrix_mul R n n n mx (@Matrix_inv R n mx) =
    matrix_to_Matrix (1%:M).
  Proof.
    intros * Hu Hmx.
    apply right_inverse_Matrix.
    subst;
    exact (vander_in_unitmx Hu).
  Qed.


End Vander.
