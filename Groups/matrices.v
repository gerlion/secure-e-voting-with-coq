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
Require Import matricesF.
Require Import VectorUtil.

Notation vector := Vector.t.
Notation Vconst := Vector.const.

(* This file has the following structure *)
(*
Linear algebrea
    1. First we define some dependencies 
    2. Then we define the vector and matrix spaces 
    
Linear algebra proofs
    1. Then we prove some properites over the linear alegbra
*)

Set Implicit Arguments.

Module MatricesG (Group : GroupSig)(Ring: RingSig)
      (M : ModuleSig Group Ring)(MatF : MatricesF Ring).

  Import MatF.

  Import M.
  Module AddMLemmas := ModuleAddationalLemmas Group Ring M.
  Import AddMLemmas.
  Export AddMLemmas. 

  (* This file contains the definitions and lemmas about matrices *)
  (* This needs to be generalised, so that we can do the
   extraction of the mixnet properly *)

  Infix "+" := Fadd.
  Infix "*" := Fmul.
  Notation "0" := Fzero.
  Notation "1" := Fone.
  Notation "- x" :=  (Finv x).
  Notation "x - y" := (x + (- y)).

  Infix "o" := Gdot (at level 50) .
  Notation "- x" := (Ginv x).

  Infix "^" := op.
  Notation " [ x ; .. ; y ] " := (Vcons x .. (Vcons y Vnil) ..).

  (*We use P* to denote the pairwise use of the operation *)
  (*We use S* to denote the scaler use of the operation *)

 
  Definition VG : nat -> Set := vector G.
  Definition VG_id := Vconst Gone.
  Definition VG_mult n (v v' : VG n) : VG n := 
  Vmap2 Gdot v v'.
  Definition VG_inv n (v : VG n) : VG n :=
  Vmap Ginv v.
  Definition VG_prod n (v : VG n) : G :=
  Vfold_left Gdot Gone v.
  Definition VG_Pexp n (v : VG n)(v' : VF n) : VG n :=
   Vmap2 op v v'.
  Definition VG_Sexp n (v: VG n)(e : F) : VG n :=
   Vmap (fun x => x ^ e) v.
  Definition VG_eq n (m m' : VG n) : bool :=
    bVforall2 Gbool_eq m m'.

  Lemma VG_inv_corr : forall (n : nat)(v : vector G n),
    VG_id n = VG_mult (VG_inv v) v.
  Proof.
    pose module_abegrp.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. 
    rewrite Vnth_const. rewrite Vnth_map. rewrite <- inv_left.
    trivial.
  Qed.

  Lemma VG_shift : forall n (a b c : VG n),
    VG_mult a b = c <-> a = VG_mult c (VG_inv b).
  Proof.
    pose module_abegrp. intros; split; intros.
    + apply Veq_nth. intros. rewrite <- H. rewrite Vnth_map2. rewrite Vnth_map.
    rewrite Vnth_map2. rewrite <- dot_assoc. rewrite <- inv_right. 
    rewrite one_right. trivial.
    + apply Veq_nth. intros. rewrite H. do 2 rewrite Vnth_map2. rewrite Vnth_map.
    rewrite <- dot_assoc. rewrite <- inv_left. rewrite one_right. trivial.
  Qed.

  Lemma Vfold_Gdot_const :  forall (n : nat)(v : vector G n)(a : G),
    forall (h : G),
    (Vfold_left Gdot h v) o a = Vfold_left Gdot (h o a) v.
  Proof.
    pose module_abegrp. intros n v0 a0. induction v0. cbn. intros. trivial. cbn. 
    intros. assert (Vfold_left Gdot (h0 o h) v0 o a0 =
         Vfold_left Gdot ((h0 o h) o a0) v0). apply IHv0.
    replace ((h0 o a0) o h) with ((h0 o h) o a0). apply H.
    rewrite <- dot_assoc. replace (h o a0) with (a0 o h) by apply comm.
    rewrite dot_assoc. trivial.
  Qed.

  Definition VG_mult_VG_Pexp_Fadd : forall (n : nat)
      (a : VG n)(c d : VF n),
    VG_mult (VG_Pexp a c) (VG_Pexp a d) = 
      VG_Pexp a (VF_add c d).
  Proof.
    intros. apply Veq_nth. intros. do 5 rewrite Vnth_map2.
    rewrite mod_dist_Fadd. trivial.
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

  Lemma Vfold_left_Vcons :
    forall (a : G)(n : nat)(b : VG n),
    Vfold_left Gdot Gone (Vcons a b) = Vfold_left Gdot Gone b o a.
  Proof.
    pose module_abegrp. intros. induction b. cbn. trivial.
    cbn. rewrite Vfold_Gdot_const.
    assert (((Gone o a0) o h) = ((Gone o h) o a0)).
    cbn. do 2 rewrite <- dot_assoc.
    assert ((a0 o h) = (h o a0)). apply comm.
    rewrite H. intuition. rewrite H. trivial.
  Qed.

  Lemma Vfold_Gdot_dob : forall (n : nat)(v v' : vector G n),
    (Vfold_left Gdot Gone v) o (Vfold_left Gdot Gone v') = 
      Vfold_left Gdot Gone (Vmap2 Gdot v v').
  Proof.
    pose module_abegrp. intros. induction n. cbn. rewrite (Vector_0_is_nil v). 
    rewrite (Vector_0_is_nil v'). cbn. apply one_right.
    rewrite (VSn_eq v). rewrite (VSn_eq v'). cbn. 
    do 3 rewrite <- Vfold_Gdot_const.
    remember (Vfold_left Gdot Gone (Vtail v)) as b.
    remember (Vfold_left Gdot Gone (Vtail v')) as c.
    rewrite dot_assoc. replace (b o Vhead v) with (Vhead v o b) by apply comm.
    replace ((Vhead v o b) o c) with (Vhead v o (b o c)) by apply dot_assoc.
    rewrite Heqb. rewrite Heqc. rewrite IHn. rewrite dot_assoc. apply right_cancel.
    apply comm.
  Qed.

  Definition VG_MF_exp_coll (n : nat)(c : VG n)(B : MF n) : VG n :=
    Vbuild (fun i ip => VG_prod (VG_Pexp c (MF_col B ip))).

  Definition VG_MF_exp_row (n : nat)(c : VG n)(B : MF n) : VG n :=
    Vbuild (fun i ip => VG_prod (VG_Pexp c (Vnth B ip))).

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

  Infix "o" := Gdot (at level 50) .
  Notation "- x" := (Ginv x).

  Infix "^" := op.
  Notation " [ x ; .. ; y ] " := (Vcons x .. (Vcons y Vnil) ..).

  Lemma VG_mult_Vmap2 :
    forall n (A B : Type)(v : vector A n)(v' : vector B n)
      (f f' : A -> B -> G),
    Vmap2 (fun x y => f x y o f' x y) v v' =
    VG_mult (Vmap2 f v v') (Vmap2 f' v v').
  Proof.
    intros. apply Veq_nth. intros. do 4 rewrite Vnth_map2. trivial.
  Qed.

  Lemma VG_prod_induction :
    forall(N : nat)(v : VG (S N)),
    VG_prod v = VG_prod (Vtail v) o (Vhead v).
  Proof.
    intros. remember (VG_prod (Vtail v) o Vhead v) as b.
    rewrite (VSn_eq v). rewrite Heqb. cbn. rewrite Vfold_Gdot_const.
    trivial.
  Qed.

  Lemma VG_prod_induction_tail :
    forall(N : nat)(v : VG (S N)),
    - (Vhead v) o VG_prod v = VG_prod (Vtail v).
  Proof.
    pose (module_abegrp).
    intros. remember (VG_prod (Vtail v)) as b. remember (Vhead v) as c.
    rewrite (VSn_eq v). rewrite Heqb. cbn. rewrite Heqc. rewrite <- Vfold_Gdot_const.
    rewrite comm. rewrite <- dot_assoc. rewrite <- inv_right.
    rewrite one_right. 
    trivial.
  Qed.

  Lemma VG_prod_cancel : forall (N : nat)(v : VG (S N)),
    VG_prod v o - VG_prod (Vtail v) = Vhead v.
  Proof.
    pose (module_abegrp).
    intros. rewrite VG_prod_induction. rewrite comm.
    rewrite dot_assoc. rewrite <- inv_left. rewrite one_left. trivial.
  Qed.

  Lemma VG_prod_induction_double:
    forall(N : nat)(v : VG (S N + S N)),
    VG_prod v = VG_prod (Vtail v) o (Vhead v).
  Proof.
    intros. remember (VG_prod (Vtail v) o Vhead v) as b.
    rewrite (VSn_eq v). rewrite Heqb. cbn. rewrite Vfold_Gdot_const.
    trivial.
  Qed.

  Lemma VG_mod_dist :
    forall N, forall (v : VG N)(a : F)(b : G), 
      (Vfold_left Gdot b v) ^ a = Vfold_left Gdot (b^a) (Vmap (fun x => x ^ a) v).
  Proof.
    intros v0 a. induction a. cbn. trivial.  intros. cbn in *.
    assert (Vfold_left Gdot (b o h) a ^ a0 = Vfold_left Gdot ((b o h) ^  a0)(Vmap (op^~ a0) a)).
    apply IHa. rewrite <- mod_dist_Gdot. apply H.
  Qed.

  Lemma VG_Sexp_id : 
    forall N, forall (e : VG N), 
    VG_Sexp e 1 = e.
  Proof.
    intros.  unfold VG_Sexp. apply Vmap_eq_nth.
    intros. rewrite mod_id. trivial. 
  Qed.

  Lemma VG_Sexp_id_gen : 
    forall N, forall a (e : VG N), 
    a = 1 ->
    VG_Sexp e a = e.
  Proof.
    intros. rewrite H. apply VG_Sexp_id.
  Qed.


  Lemma VG_Sexp_dis_dot :
  forall N, forall (a b : VG N)(c : F),
    VG_Sexp (VG_mult a b) c = VG_mult (VG_Sexp a c) (VG_Sexp b c).
  Proof.
    intros. apply Vmap_eq_nth. intros. do 2 rewrite Vnth_map2.
    rewrite mod_dist_Gdot. do 2 rewrite Vnth_map. trivial.
  Qed.

  Lemma Sexp_dist :
  forall N, forall (e : VG N)(u : VF N)(a : F),
  op (VG_prod (VG_Pexp e u)) a = 
    VG_prod (VG_Pexp e (VF_scale u a)).
  Proof.
    intros. induction N. cbn. apply mod_mone.
    simpl. unfold VG_prod. do 2 rewrite Vfold_left_Vcons.
    rewrite mod_dist_Gdot. rewrite IHN. do 3 rewrite Vhead_nth.
    rewrite Vnth_map. rewrite mod_dist_FMul2. unfold VG_prod.
     rewrite VF_scale_Vtail. trivial.
  Qed.

  Lemma VG_Sexp_ann :
  forall N, forall (e : VG N), 
     VG_Sexp e 0 = VG_id N.
  Proof.
    intros. unfold VG_Sexp. apply Vmap_eq_nth.
    intros. rewrite mod_ann. unfold VG_id. rewrite Vnth_const.
    trivial.
  Qed.

  Lemma VG_Sexp_eq :
    forall N, forall(a : F)(e e' : VG N), 
     e = e' -> VG_Sexp e a  = VG_Sexp e' a.
  Proof.
    intros. rewrite H. trivial. 
  Qed.

  Lemma VG_Sexp_eq2 :
    forall N, forall(a a' : F)(e : VG N), 
     a = a' -> VG_Sexp e a  = VG_Sexp e a'.
  Proof.
    intros. rewrite H. trivial. 
  Qed.

  Lemma VG_Sexp_Sexp : forall N, forall a a' (e : VG N),
    VG_Sexp (VG_Sexp e a) a' = VG_Sexp e (a*a').
  Proof.
    intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. rewrite mod_dist_FMul2.
    trivial.
  Qed.

  Lemma Vbuild_op :
    forall (N :nat)(e : VG N)(X : MF N)(b : VF N),
    (Vbuild (fun (j : nat) (jp : j < N) =>
      op (VG_prod (VG_Pexp e (MF_col X jp)))
        (Vnth b jp))) = VG_Pexp (Vbuild (fun (j : nat) (jp : j < N) =>
      VG_prod (VG_Pexp e (MF_col X jp)))) b.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. 
    do 2 rewrite Vbuild_nth. trivial. 
  Qed.

  Lemma VG_One_exp :
  forall (N : nat)(e : VG N),
    VG_Pexp e (VF_one N) = e.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_const.
    rewrite mod_id. trivial.
  Qed.

  Lemma VG_prod_Vcons :
    forall (N : nat)(a : G)(b : VG N),
    VG_prod (Vcons a b) = VG_prod b o a.
  Proof.
    intros. cbn. rewrite Vfold_Gdot_const. trivial.
  Qed.

  Lemma VG_prod_Vcons_Gone : forall (N : nat)(b : VG N),
    VG_prod (Vcons Gone b) = VG_prod b.
  Proof.
    intros. rewrite VG_prod_Vcons. pose (module_abegrp).
    rewrite one_right. trivial.
  Qed.
  
  Lemma Sexp_dist0 :
    forall N, forall (e : VG N)(a : F),
  op (VG_prod e) a = 
    VG_prod (VG_Sexp e a).
  Proof.
    intros. induction N. cbn. rewrite (Vector_0_is_nil e).
    cbn. apply mod_mone.
    rewrite (VSn_eq e). simpl. do 2 rewrite VG_prod_Vcons.
    rewrite mod_dist_Gdot. rewrite IHN.
    trivial.
  Qed.


  Lemma VG_Pexp_Vcons : forall (N : nat)(c : F)(d : VF N)(a : G)(b: VG N),
    VG_Pexp (Vcons a b) (Vcons c d) = Vcons (a^c) (VG_Pexp b d).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. trivial.
  Qed.

  Lemma VG_prod_break :
   forall (N N' : nat)(e : VG (N+N')),
      VG_prod e = (VG_prod (Vbreak e).1) o (VG_prod (Vbreak e).2).
  Proof.
    pose (module_abegrp). intros. rewrite (Vbreak_eq_app e). induction (Vbreak e).1.
    cbn. rewrite one_left. trivial.
    (* part 1 *) 
    rewrite Vbreak_app. simpl in *. do 2 rewrite VG_prod_Vcons.
    rewrite IHt. rewrite Vbreak_app. simpl. 
    do 2 rewrite <- dot_assoc. apply left_cancel. apply comm.
  Qed.

  Lemma VG_Zero_exp :
  forall (N : nat)(e : VG N),
    VG_Pexp e (VF_zero N) = VG_id N.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vnth_const.
    unfold FSemiRingT.A0. rewrite mod_ann. trivial.
  Qed.

  Lemma VG_Zero_prod :
   forall (N : nat),
    VG_prod (VG_id N) = Gone.
  Proof.
    pose (module_abegrp). intros. induction N. cbn. trivial.
    cbn. rewrite <- Vfold_Gdot_const.
    unfold VG_prod, VG_id in IHN. rewrite IHN.
    rewrite one_right. trivial.
  Qed.
  
  Lemma VG_Zero_prod_gen : forall N (a : VG N),
    a = VG_id N ->
    VG_prod a = Gone.
  Proof.
    intros. rewrite H. apply VG_Zero_prod.
  Qed.

  Lemma VG_Zero_prod_build :
    forall (N : nat),
      VG_prod (Vbuild (fun (j : nat) (_ : (j < N)%nat) => Gone)) = Gone.
  Proof.
    pose (module_abegrp). intros. induction N. cbn. trivial. 
    rewrite (VSn_eq (Vbuild (fun (j : nat) (_ : (j < S N)%nat) => Gone))).
    simpl. rewrite VG_prod_Vcons. rewrite IHN.  
    rewrite one_left. trivial.
  Qed.

  Lemma Vfold_left_one :
    forall (v : VG 1)(ip : 0 < 1),
    VG_prod v = Vnth v ip.
  Proof.
    pose (module_abegrp). intros. unfold VG_prod. rewrite (VSn_eq v).
    cbn. rewrite (Vector_0_is_nil (Vtail v)). cbn. 
    rewrite one_left. trivial.
  Qed.

  Lemma VG_prod_replace :
    forall (n N : nat)(np: n < N)(a : G),
    VG_prod (Vreplace (VG_id N) np a) = a.
  Proof.
    pose (module_abegrp). induction n. intros. destruct N. lia.

      (* induction base *)
      simpl. rewrite VG_prod_Vcons. rewrite VG_Zero_prod. apply one_left.

      (* induction step *)
      intros. destruct N. lia. simpl. rewrite VG_prod_Vcons.
      rewrite one_right. rewrite (IHn N (lt_S_n np) a0). trivial.
  Qed.


  (*ugly proof of a simple statment*)
  Lemma VG_n_exp :
  forall (N : nat)(e : VG N)(n : nat)(np : n < N),
    VG_prod (VG_Pexp e (VF_n_id np)) =
       Vnth e np.
  Proof.
    intros.
    (* Replace vector with simple replace *)
    assert (VG_Pexp e (VF_n_id np) = 
      (Vreplace (VG_id N) np (Vnth e np))).
    apply Veq_nth. intros.  rewrite Vnth_map2.  case (Nat.eq_dec n i).
    intros. subst. do 2 rewrite Vnth_replace.  rewrite mod_id. apply Vnth_eq.
    trivial. intros. rewrite Vnth_replace_neq; auto. rewrite Vnth_const.
    rewrite Vnth_replace_neq; auto. rewrite Vnth_const. rewrite mod_ann. 
    trivial. rewrite H.
    (* yey part 1 complete *)
    apply VG_prod_replace. 
  Qed. 

  Lemma VG_n_exp_id :
  forall (N : nat)(e : VG N),
    VG_prod (VG_Pexp e (VF_one N)) =
       VG_prod e.
  Proof.
    intros. apply f_equal. apply Veq_nth. intros. rewrite Vnth_map2. 
    rewrite Vnth_const. rewrite mod_id. trivial.
  Qed. 

  Lemma MF_CVmult_one : 
    forall (N : nat)(m : MF N),
    Vmap (VF_sum (n:= N)) m =
    MF_CVmult m (VF_one N).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map.   
    pose FMatrix.mat_mult_row. unfold FMatrix.get_row in e. unfold MF_CVmult.
    unfold FMatrix.mat_vec_prod. rewrite FMatrix.Vnth_col_mat. 
    rewrite FMatrix.mat_mult_spec. rewrite FMatrix.get_col_col_mat.
    pose VF_inProd_VF_one. unfold VF_inProd in e0. rewrite e0. trivial.
  Qed.

  Lemma VGeq :
    forall (N : nat)(m m' : VG N),
    VG_eq m m' = true <-> m = m'.
  Proof.
    pose (module_abegrp). intros. unfold iff. refine (conj _ _).  intros. 
    assert (Vforall2 eq m m'). rewrite <- (bVforall2_ok (@eq G) Gbool_eq).
    apply H. intros. apply bool_eq_corr. apply Veq_nth. intros. 
    apply (Vforall2_elim_nth ip) in H0. apply H0.
    (* part 2 *)
    intros. rewrite H. unfold VG_eq. rewrite (bVforall2_ok (@eq G)). 
     intros. apply bool_eq_corr. apply Vforall2_intro_nth. intros. trivial.
  Qed.

  Lemma VG_assoc :
    forall (N : nat)(a b c : VG (N)),
    VG_mult (VG_mult a b) c = VG_mult a (VG_mult b c).
  Proof.
    pose (module_abegrp). intros. induction N. cbn. trivial.
    (* part 2 *)
    simpl in *. rewrite IHN. apply Vcons_eq_intro.
    rewrite dot_assoc. trivial. trivial.
  Qed.

  Lemma VG_comm :
    forall (N : nat)(a b : VG (N)),
    VG_mult a b = VG_mult b a.
  Proof. 
    pose (module_abegrp). intros. induction N. cbn. trivial.
    cbn in *. apply Vcons_eq_intro. apply comm. apply IHN.
  Qed.

  Lemma Vfold_VG_mult_const :  forall (n n' : nat)
    (v : vector (VG n') n)(a : (VG n')),
    forall (h : (VG n')),
    VG_mult (Vfold_left (VG_mult (n:=n')) h v) a =
       Vfold_left (VG_mult (n:=n')) (VG_mult h a) v.
  Proof.
    intros n n' v0 a. induction v0. intros.  cbn in *. trivial.
    (* part 1 complete *) 
    intros. cbn. rewrite IHv0.
    assert (forall a a' : VG n', a = a' -> 
    Vfold_left (VG_mult (n:=n')) a v0 = Vfold_left (VG_mult (n:=n')) a' v0).
    intros. rewrite H. trivial. apply H. rewrite VG_assoc.
    replace (VG_mult h a) with (VG_mult a h) by apply VG_comm. 
    rewrite VG_assoc. trivial.
  Qed.

  Lemma Vfold_VG_mult_const_inside_Vfold_Gdot :
    forall (n n' : nat)(v : vector (VG n) (S n')),
  Vfold_left Gdot Gone
    (Vcons (Vfold_left Gdot Gone (Vhead v))
       (Vfold_left (VG_mult (n:=n)) 
          (VG_id n) (Vtail v))) =
  Vfold_left Gdot Gone
    (Vfold_left (VG_mult (n:=n)) 
       (VG_id n) v).
  Proof.
    pose (module_abegrp).
    (* Setup *)
     assert (forall (n : nat) (v v' : vector G n),
      Vfold_left Gdot Gone (Vmap2 Gdot v v') = 
     Vfold_left Gdot Gone v o Vfold_left Gdot Gone v').
    intros. symmetry. pose Vfold_Gdot_dob.   apply e.
    (* phase 1 *)
    intros. induction n'. rewrite (VSn_eq v).
    rewrite (Vector_0_is_nil (Vtail v)).
     cbn. unfold VG_mult. 
    rewrite H. rewrite Vfold_Gdot_const. intuition. 
    (* phase 2 *)
    rewrite (VSn_eq v). simpl in *. unfold VG_mult in IHn'.
    rewrite <- Vfold_VG_mult_const.
    unfold VG_mult. rewrite H. pose (IHn' (Vtail v)).
    symmetry in e. rewrite e. rewrite <- Vfold_Gdot_const.
    apply right_cancel. rewrite <- Vfold_Gdot_const.
    remember (Vhead (Vtail v)) as a0. 
    remember (Vtail (Vtail v)) as b. rewrite (VSn_eq (Vtail v)).
    simpl. rewrite <- Vfold_VG_mult_const. unfold VG_mult. rewrite H.
    rewrite Heqa0. rewrite Heqb. intuition.
  Qed.

  Lemma VG_one :
    forall (N : nat)(a : VG (N)),
    VG_mult a (VG_id (N)) = a.
  Proof.
    pose (module_abegrp). intros. induction N. cbn. unfold VG in *. 
    rewrite (Vector_0_is_nil a0). trivial.
    (* part 2 *)
    simpl in *. rewrite one_right. rewrite IHN.
    symmetry. apply VSn_eq.
  Qed.

  Lemma VG_prod_one :
    forall (a : G),
    VG_prod [a] = a.
  Proof. 
    pose (module_abegrp). intros. cbn. rewrite one_left. trivial.
  Qed.

  Lemma VG_prod_one_vec :
    forall (a : VG 1),
    VG_prod a = Vhead a.
  Proof. 
    pose (module_abegrp). intros. rewrite (VSn_eq a0).
    rewrite (Vector_0_is_nil (Vtail a0)). cbn. rewrite one_left. trivial.
  Qed.

  Lemma VG_prod_one_vec_gen :
    forall n (a : VG (S n)),
    n = 0%nat ->
    VG_prod a = Vhead a.
  Proof. 
    intros. subst. apply VG_prod_one_vec.
  Qed.

  Lemma VG_prod_zero :
    VG_prod [] = Gone.
  Proof. 
    pose (module_abegrp). intros. cbn. trivial.
  Qed.

  Lemma VG_Prod_mult_dist :
  forall (n : nat)(a b: vector G n),
  VG_prod (Vmap2 Gdot a b) = Gdot (VG_prod a) (VG_prod b).
  Proof.
    pose module_abegrp.
    intros. induction n. simpl. rewrite (Vector_0_is_nil a0).
    rewrite (Vector_0_is_nil b). cbn. symmetry. apply one_right.
    rewrite VG_prod_induction. rewrite <- Vtail_map2. rewrite IHn.
    rewrite Vhead_nth. rewrite Vnth_map2. pose commHack.
    unfold abegop in *. rewrite e. do 2 rewrite <- Vhead_nth.
    do 2 rewrite <- VG_prod_induction. trivial.
  Qed.

  Lemma Vnth_Vfold_left_cons_Gdot :
    forall (i n n' : nat)(v : vector (VG n) n')(h : (VG n))(ip : Nat.lt i n),
    Vnth
    (Vfold_left (VG_mult (n:=n))
       (VG_mult (VG_id n) h) v) ip =
    Vnth
      (Vfold_left (VG_mult (n:=n))
       (VG_id n) v) ip o 
    Vnth h ip.
  Proof.
    pose (module_abegrp). intros. induction v. cbn. apply Vnth_map2. cbn.
    rewrite <- Vfold_VG_mult_const. rewrite Vnth_map2.
    rewrite IHv. rewrite <- Vfold_VG_mult_const. 
    rewrite Vnth_map2. do 2 rewrite <- dot_assoc.
    apply left_cancel. apply comm.
  Qed.

  Lemma VG_Sexp_VG_Pexp : forall n (v : VG n)(a : VF n)(b : F),
    VG_Sexp (VG_Pexp v a) b = VG_Pexp v (VF_scale a b).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map.
    do 2 rewrite Vnth_map2. rewrite Vnth_map.
    rewrite mod_dist_FMul2. trivial. 
  Qed.

  Lemma Vfold_left_VG_mult :
    forall (i n n' : nat)(v : vector (VG n) n')(ip : Nat.lt i n),
    Vnth (Vfold_left (VG_mult (n:=n)) (VG_id n) v) ip
      = Vfold_left Gdot Gone 
      (Vmap (fun v => Vnth v ip) v).
  Proof.
    intros. 
    intros. induction v. cbn. rewrite Vnth_const. trivial.
    (* part 2 *)
    cbn. rewrite <- Vfold_Gdot_const. rewrite <-  IHv. 
    apply Vnth_Vfold_left_cons_Gdot.
  Qed.

  Lemma Vmap2_Gdot_vbuild :
    forall (n : nat)(g g' : forall i, Nat.lt i n  -> G),
      Vmap2 Gdot (Vbuild (fun j jp => g j jp)) (Vbuild (fun j jp => g' j jp))
      = (Vbuild (fun j jp => g j jp o g' j jp)).
  Proof.
    intros. induction n. cbn. trivial. rewrite (VSn_eq
    (Vbuild (fun (j : nat) (jp : j < S n) => g j jp o g' j jp))).
    rewrite Vbuild_head. rewrite (VSn_eq (Vbuild (fun j : nat => [eta g j]))).
    rewrite (VSn_eq (Vbuild (fun j : nat => [eta g' j]))). rewrite Vcons_map2.
    do 2 rewrite Vbuild_head. do 3 rewrite Vbuild_tail. rewrite IHn. trivial.
  Qed.

  Lemma VF_sum_op : forall (a : G) n (v : VF n),
    a ^ VF_sum v = VG_prod (Vmap (op a) v).
  Proof.
    intros. induction n. rewrite (Vector_0_is_nil v). cbn. rewrite mod_ann. trivial.
    rewrite VG_prod_induction. rewrite Vtail_map. rewrite <- IHn. rewrite Vhead_map.
    rewrite <- mod_dist_Fadd. rewrite <- VF_sum_induction. trivial.
  Qed.

  Lemma VG_prod_vbuild : 
    forall (a : G)(n' : nat)(U A : VF n'),
    a ^ VF_inProd U A = 
      VG_prod (Vbuild (fun (j : nat) (jp : (j < n')%nat) => 
        a ^ (Vnth U jp * (Vnth A jp)))).
  Proof.
    intros. induction n'. cbn. rewrite mod_ann.
    trivial. rewrite (VSn_eq (Vbuild
       (fun (j : nat) (jp : j < S n') =>
        a ^ (Vnth U jp * Vnth A jp)))).
    rewrite VG_prod_Vcons. rewrite Vbuild_tail. 
    assert ((Vbuild
       (fun (i : nat) (ip : i < n') =>
        a ^ (Vnth U (lt_n_S ip) * Vnth A (lt_n_S ip)))) =
    (Vbuild
       (fun (i : nat) (ip : i < n') =>
        a ^ (Vnth (Vtail U)  ip * Vnth (Vtail A) ip)))).
    apply Veq_nth. intros. do 2 rewrite Vbuild_nth. do 2 rewrite <- Vnth_tail.
    trivial. rewrite H.  rewrite <- IHn'. rewrite (VSn_eq U). rewrite (VSn_eq A).
    simpl. rewrite InProd_Vcons. rewrite mod_dist_Fadd. trivial.
  Qed.

  Definition PexpMatrix (N : nat)(c : VG N)(e : MF N) : VG N :=
    Vmap (fun row => VG_prod (VG_Pexp c row)) (e).
      
   Theorem VG_prod_VG_Pexp_scale :
    forall (n : nat)(c : VG n)(U : VF n)(s : F),
    VG_prod (VG_Pexp c U) ^ s = 
    VG_prod (VG_Pexp c (VF_scale U s)).
  Proof.
    intros. unfold VG_prod, VG_Pexp, VF_scale. rewrite VG_mod_dist.
    rewrite mod_mone. apply Vfold_left_eq. apply Veq_nth.
    intros. rewrite Vnth_map2. do 2 rewrite Vnth_map. rewrite Vnth_map2.
    rewrite mod_dist_FMul2. trivial.
  Qed.

  Lemma VG_MF_exp_coll_id : forall (n : nat)(c : VG n),
    VG_MF_exp_coll c (MF_id n) = c.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth.
    rewrite MF_Col_id. rewrite VG_n_exp. trivial.
  Qed.

  Lemma VG_MF_exp_row_id : forall (n : nat)(c : VG n),
    VG_MF_exp_row c (MF_id n) = c.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth.
    rewrite MF_Vnth_id. rewrite VG_n_exp. trivial.
  Qed.
  
  Lemma VGprod_rearrange : 
    forall(n nM : nat),
      forall(g : forall i, Nat.lt i n  -> VG (1+nM)),
    VG_prod (Vbuild (fun (j : nat) (jp : (j < n)%nat) =>
     VG_prod (g j jp))) = VG_prod (Vfold_left (VG_mult (n:=1+nM))
    (VG_id (1+nM)) (Vbuild (fun (j : nat)(jp : (j < n)%nat) => (g j jp)))).
  Proof.
    pose Group.module_abegrp.
    (* part 1 *)
    intros. induction n. cbn. rewrite one_right.
    assert (Vfold_left Gdot Gone (Vconst Gone nM) = VG_prod (VG_id nM)).
    unfold VG_prod, VG_id. trivial.  rewrite H. rewrite VG_Zero_prod.
    trivial.
    (* part 2 *)
    rewrite (VSn_eq (Vbuild (fun (j : nat) (jp : (j < 1+n)%nat)
      => VG_prod (g j jp)))). unfold VG_prod in *. rewrite Vfold_left_Vcons.
    rewrite Vbuild_tail. rewrite IHn. rewrite <- Vbuild_tail.
    rewrite <- Vfold_left_Vcons.
    assert ((Vhead (Vbuild (fun (j : nat) (jp : (j < 1+n)
    %nat) => Vfold_left Gdot Gone (g j jp)))) = 
    Vfold_left Gdot Gone (Vhead (Vbuild g))).
    do 2 rewrite Vhead_nth. do 2 rewrite Vbuild_nth. trivial.
    rewrite H. rewrite Vfold_VG_mult_const_inside_Vfold_Gdot.
    intuition.
  Qed.

  Lemma VF_neg_inv :
    forall N : nat, forall (hs : VG N)(m : VF N),
    VG_prod(VG_Pexp hs (VF_neg m)) = 
      - VG_prod (VG_Pexp hs m).
  Proof. 
    pose (module_abegrp). intros. unfold VF_neg. unfold VG_Pexp. unfold VG_prod. induction m.
    cbn. auto. rewrite <- one_right. rewrite <- inv_left. trivial.
    cbn. do 2 rewrite <- Vfold_Gdot_const. rewrite IHm. rewrite <- neg_eq.
    apply inv_dist.
  Qed.

  Lemma VG_Pexp_mult :
    forall N (v v' : VG N)(v'' : VF N),
      VG_Pexp (VG_mult v v') v'' =
      VG_mult (VG_Pexp v v'') (VG_Pexp v' v'').
  Proof.
    intros. apply Veq_nth. intros. do 5 rewrite Vnth_map2.
    rewrite mod_dist_Gdot. trivial.
  Qed.

  Lemma VF_add_product :
    forall N, forall (hs : VG N)(m1 m2 : VF N), 
    VG_prod (VG_Pexp hs m2)
    o VG_prod (VG_Pexp hs m1) =
    VG_prod
    (VG_Pexp hs
       (VF_add m1 m2)).
  Proof.
    pose (module_abegrp). intros. unfold VG_prod. unfold VF_add. 
    unfold VG_Pexp. cbn.
    unfold FMatrix.VA.vector_plus. unfold FSemiRingT.Aplus.
    rewrite Vfold_Gdot_dob. apply Vfold_left_eq. apply Veq_nth.
    intros. do 5 rewrite Vnth_map2. rewrite mod_dist_Fadd. apply comm.
  Qed.

 
  Lemma VG_prod_VG_prod_VF_scale_VF_inProd :  (*This lemma could be cleaned *)
    forall (n' n  : nat)(e' : VG n)(U : FMatrix.matrix n n')(A : VF n'),
     VG_prod (Vbuild 
        (fun (j : nat) (jp : (j < n')%nat) => VG_prod (VG_Pexp e'
                (VF_scale (FMatrix.get_col U jp) (Vnth A jp))))) = 
        VG_prod (Vbuild (fun (j : nat) (jp : (j < n)%nat)
           => op (Vnth e' jp)
        (VF_inProd (Vnth U jp) A))).
  Proof.
      intros. induction n. cbn. rewrite VG_Zero_prod_build.
     trivial. rewrite (VSn_eq (Vbuild
       (fun (j : nat) (jp : (j < 1+ n)%nat) =>
        op (Vnth e' jp) (VF_inProd (Vnth U jp) A)))).
    rewrite VG_prod_Vcons. rewrite Vbuild_tail. rewrite Vbuild_head.
    (* Now I need use the Inductive hypotsis *)
    pose (IHn (Vtail e') 
      (Vtail U)).
   assert (VG_prod (Vbuild (fun (j : nat) (jp : (j < n)%nat) =>
      op (Vnth (Vtail e') jp) (VF_inProd (Vnth
        (Vtail U) jp) A))) = 
    VG_prod (Vbuild (fun (i1 : nat) (ip1 : (i1 < n)%nat) =>
       op (Vnth e' (lt_n_S ip1)) (VF_inProd (Vnth U (lt_n_S ip1)) A)))).
    apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vbuild_nth.
    rewrite Vnth_tail. assert(forall a a' b b', a=a' -> b=b' -> op a b = op a' b').
    intros. rewrite H. rewrite H0. trivial. apply H. trivial.
    assert(forall n (a a' b b': VF n), a=a' -> b=b' -> VF_inProd a b = VF_inProd a' b').
    intros.  rewrite H0. rewrite H1. trivial. apply H0. apply Veq_nth. intros.
    rewrite Vnth_tail. trivial. trivial.
    symmetry in H. rewrite  H. symmetry in e. rewrite  e. rewrite VG_prod_vbuild.
    (* final clean up *)
    rewrite Vfold_Gdot_dob. rewrite Vmap2_Gdot_vbuild. 
    apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vbuild_nth.
    rewrite VG_prod_induction. assert (forall a b c d, a = b -> c = d -> 
      Gdot a c = Gdot b d). intros. rewrite H0. rewrite H1. trivial. apply H0.
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_tail.
    do 2 rewrite Vnth_map2.  assert (forall a b c d, a = b -> c = d -> 
      op a c = op b d). intros. rewrite H1. rewrite H2. trivial.
    apply H1. rewrite Vnth_tail. trivial.
    do 2 rewrite Vnth_map. do 2 rewrite Vnth_map. rewrite Vnth_tail.
    trivial. rewrite Vhead_nth. rewrite Vnth_map2.
    rewrite Vnth_map. assert (forall a b c d, a = b -> c = d -> 
      op a c = op b d). intros. rewrite H1. rewrite H2. trivial.
    apply H1. trivial. rewrite <- FMatrix.get_elem_swap. unfold FMatrix.get_row. trivial.
  Qed. 

  Lemma VG_prod_VG_prod_VF_scale_VF_inProd_2 :  (*This lemma could be cleaned *)
    forall (n' n  : nat)(e' : VG n)(U : FMatrix.matrix n' n)(A : VF n'),
     VG_prod (Vbuild 
        (fun (j : nat) (jp : (j < n')%nat) => VG_prod (VG_Pexp e'
                (VF_scale (Vnth U jp) (Vnth A jp))))) = 
        VG_prod (Vbuild (fun (j : nat) (jp : (j < n)%nat)
           => op (Vnth e' jp)
        (VF_inProd (FMatrix.get_col U jp) A))).
  Proof.
      intros. induction n. cbn. rewrite VG_Zero_prod_build.
     trivial. rewrite (VSn_eq (Vbuild
       (fun (j : nat) (jp : (j < 1+ n)%nat) =>
        op (Vnth e' jp) (VF_inProd (FMatrix.get_col U jp) A)))).
    rewrite VG_prod_Vcons. rewrite Vbuild_tail. rewrite Vbuild_head.
    pose (IHn (Vtail e')(Vmap (fun a => Vtail a) U)).
    (* Now I need use the Inductive hypotsis *)
   assert (VG_prod (Vbuild (fun (j : nat) (jp : (j < n)%nat) =>
      op (Vnth (Vtail e') jp) (VF_inProd (FMatrix.get_col
                (Vmap [eta 
                   Vtail (n:=n)] U) jp) A))) = 
    VG_prod (Vbuild (fun (i1 : nat) (ip1 : (i1 < n)%nat) =>
       op (Vnth e' (lt_n_S ip1)) (VF_inProd (FMatrix.get_col U (lt_n_S ip1)) A)))).
    apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vbuild_nth.
    rewrite Vnth_tail. apply scaleEq.
    apply f_equal2; auto.  apply Veq_nth. intros.
    do 3 rewrite Vnth_map. rewrite Vnth_tail. trivial.
    symmetry in H. rewrite  H. symmetry in e. rewrite  e. 
    rewrite VG_prod_vbuild.
    (* final clean up *)
    rewrite Vfold_Gdot_dob. rewrite Vmap2_Gdot_vbuild. 
    apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vbuild_nth.
    rewrite VG_prod_induction. apply f_equal2. 
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_tail.
    do 2 rewrite Vnth_map2. apply f_equal2.
    rewrite Vnth_tail. trivial.
    do 2 rewrite Vnth_map. rewrite Vnth_map. rewrite Vnth_tail.
    trivial. rewrite Vhead_nth. rewrite Vnth_map2. apply f_equal2; auto.
    do 2 rewrite Vnth_map. trivial.
  Qed. 
  
  Lemma VG_prod_VG_Pexp_MF_CVmult :  (* Prod d^{A Ui} = Prod (Prod d^Uij Ai) *)
    forall (n : nat)(e' : VG n)(U A : MF n)(i:nat)(ip:Nat.lt i n),
    VG_prod (VG_Pexp e' (MF_CVmult A (MF_col U ip))) = 
     VG_prod (Vbuild (fun j jp => 
      op (VG_prod (VG_Pexp e' (MF_col A jp)))(Vnth (MF_col U ip) jp))). 
  Proof.
    intros. assert (Vbuild (fun (j : nat) (jp : (j < n)%nat) => 
          op (VG_prod  (VG_Pexp e' (MF_col A jp))) (Vnth (MF_col U ip) jp)) =
      (Vbuild (fun (j : nat) (jp : (j < n)%nat) => 
          (VG_prod  (VG_Pexp e' (VF_scale (MF_col A jp) (Vnth (MF_col U ip) jp))))))). 
    intros.  apply Veq_nth. intros. do 2 rewrite Vbuild_nth. 
    rewrite VG_prod_VG_Pexp_scale. trivial.  rewrite H. 
    (*Finished first move *)
    rewrite (VG_prod_VG_prod_VF_scale_VF_inProd e' A (MF_col U ip)).
    (* clean it up *)
    apply Vfold_left_eq. apply Veq_nth. intros.  rewrite Vnth_map2. 
    rewrite MF_getRow_prod. unfold VF_inProd. 
    rewrite Vbuild_nth. trivial. 
  Qed. 

  Lemma VG_prod_VG_Pexp_MF_CVmult_row :  (* Prod d^{A Ui} = Prod (Prod d^Uij Ai) *)
    forall (n : nat)(e' : VG n)(U A : MF n)(i:nat)(ip:Nat.lt i n),
    VG_prod (VG_Pexp e' (MF_CVmult A (Vnth U ip))) = 
     VG_prod (Vbuild (fun j jp => 
      op (VG_prod (VG_Pexp e' (MF_col A jp)))(Vnth (Vnth U ip) jp))). 
  Proof.
    intros. assert (Vbuild (fun (j : nat) (jp : (j < n)%nat) => 
          op (VG_prod  (VG_Pexp e' (MF_col A jp))) (Vnth (Vnth U ip) jp)) =
      (Vbuild (fun (j : nat) (jp : (j < n)%nat) => 
          (VG_prod  (VG_Pexp e' (VF_scale (MF_col A jp) (Vnth (Vnth U ip) jp))))))). 
    intros.  apply Veq_nth. intros. do 2 rewrite Vbuild_nth. 
    rewrite VG_prod_VG_Pexp_scale. trivial.  rewrite H. 
    (*Finished first move *)
    rewrite (VG_prod_VG_prod_VF_scale_VF_inProd e' A (Vnth U ip)).
    (* clean it up *)
    apply Vfold_left_eq. apply Veq_nth. intros.  rewrite Vnth_map2. 
    rewrite MF_getRow_prod. unfold VF_inProd. 
    rewrite Vbuild_nth. trivial. 
  Qed. 

  Lemma VG_prod_VG_Pexp_MF_VCmult :  (* Prod d^{A Ui} = Prod (Prod d^Uij Ai) *)
    forall (n : nat)(e' : VG n)(U A : MF n)(i:nat)(ip:Nat.lt i n),
    VG_prod (VG_Pexp e' (MF_VCmult (Vnth U ip) A)) = 
     VG_prod (Vbuild (fun j jp => 
      op (VG_prod (VG_Pexp e' (Vnth A jp)))(Vnth (Vnth U ip) jp))). 
  Proof.
    intros. assert (Vbuild (fun (j : nat) (jp : (j < n)%nat) => 
          op (VG_prod  (VG_Pexp e' (Vnth A jp))) (Vnth (Vnth U ip) jp)) =
      (Vbuild (fun (j : nat) (jp : (j < n)%nat) => 
          (VG_prod  (VG_Pexp e' (VF_scale (Vnth A jp) (Vnth (Vnth U ip) jp))))))). 
    intros.  apply Veq_nth. intros. do 2 rewrite Vbuild_nth. 
    rewrite VG_prod_VG_Pexp_scale. trivial.  rewrite H.
    rewrite (VG_prod_VG_prod_VF_scale_VF_inProd_2 e' A (Vnth U ip)). 
    (* clean it up *)
    apply Vfold_left_eq. apply Veq_nth. intros.  rewrite Vnth_map2. 
    rewrite MF_getCol_prod. unfold VF_inProd. 
    rewrite Vbuild_nth. apply f_equal2; auto.
    apply FMatrix.VA.dot_product_comm.
  Qed. 

  Lemma VG_MF_exp_coll_dist : forall (n : nat)(c : VG n)(A B : MF n),
    VG_MF_exp_coll (VG_MF_exp_coll c A) B = VG_MF_exp_coll c (MF_mult A B).
  Proof.
    intros. apply Veq_nth. intros. do 2 rewrite Vbuild_nth.
    rewrite MF_getRow_CVmul. rewrite VG_prod_VG_Pexp_MF_CVmult.
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_map2.
    do 2 rewrite Vbuild_nth. trivial.
  Qed.

  Lemma VG_MF_exp_row_dist : forall (n : nat)(c : VG n)(A B : MF n),
    VG_MF_exp_row (VG_MF_exp_row c A) B = VG_MF_exp_row c (MF_mult B A).
  Proof.
    intros. apply Veq_nth. intros. do 2 rewrite Vbuild_nth.
    rewrite MF_getRow_VCmul. rewrite VG_prod_VG_Pexp_MF_VCmult.
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vbuild_nth.
    rewrite Vnth_map2. rewrite Vbuild_nth. trivial.
  Qed.

  Lemma Vmap_prod_pexp_scale : forall (n m : nat)
    (g : vector (VF n) (1+m))(a : VG n)(x : F),
    VG_prod (Vmap (fun y : VF n => VG_prod 
    (VG_Pexp a (VF_scale y x))) g) =
    VG_prod (VG_Pexp a (VF_scale (Vmap (VF_sum (n:=(1+m))) 
      (FMatrix.mat_transpose g)) x)).
  Proof.
   intros. induction m. cbn. rewrite Vmap_sum_1.
    rewrite FMatrix.mat_transpose_idem.
   remember (Vmap (fun y : VF n =>
    VG_prod (VG_Pexp a (VF_scale y x))) g) as b. 
   symmetry in Heqb. rewrite Heqb.
   rewrite (VSn_eq b). rewrite (Vector_0_is_nil (Vtail b)).
   rewrite VG_prod_one. rewrite Vhead_nth. 
   rewrite <- Heqb. rewrite Vnth_map. rewrite Vhead_nth. 
   trivial. (* General case *)
   rewrite VG_prod_induction. rewrite Vtail_map.
   rewrite IHm. rewrite Vhead_nth. rewrite Vnth_map.
   rewrite Vfold_Gdot_dob. apply Vfold_left_eq.
   apply Veq_nth. intros. do 4 rewrite Vnth_map2.
   do 5 rewrite Vnth_map. rewrite <- mod_dist_Fadd.
   apply scaleEq. rewrite (VSn_eq (Vnth (FMatrix.mat_transpose g)
     ip)). unfold VF_sum. rewrite Vfold_left_Vcons_Fadd.
  rewrite Vhead_nth. pose FMatrix.mat_transpose_col_row.
    unfold FMatrix.get_row in e. rewrite e.
    rewrite <- FMatrix.get_elem_swap. unfold FMatrix.get_row.
   assert (forall a b c, (a + b) * c = a*c+b*c). intros. ring; auto.
   rewrite H. apply F_right_cancel.
   apply F_mul_right_cancel. apply Vfold_left_eq.
   apply Veq_nth. intros. rewrite e. rewrite Vnth_tail.
   do 2 rewrite Vnth_map.  rewrite Vnth_tail. trivial.
  Qed.

  Lemma VG_prod_scale_base : forall n m 
      (cBar : vector (VG n) m)(e : VF m)(y : VF n),
    VG_prod (Vmap2 (fun (Ci : VG n) (xi : F) => 
    VG_prod (VG_Pexp Ci (VF_scale y xi))) cBar e) =
    VG_prod (Vmap2 (fun (Ci : VG n) (xi : VF n) =>
    VG_prod (VG_Pexp Ci xi)) cBar (Vmap (fun xi => 
    VF_scale y xi) e)).
  Proof.
    intros. apply Vfold_left_eq. apply Veq_nth. intros.
    do 2 rewrite Vnth_map2. rewrite Vnth_map. trivial.
  Qed.

  Lemma Vapp_VG_prod : forall (n m : nat)
    (a : VG n)(b : VG m),
    VG_prod (Vapp a b) = VG_prod a o VG_prod b.
  Proof.
    pose (module_abegrp).
    intros. induction n. rewrite (Vector_0_is_nil a0).
    cbn. rewrite one_left. trivial.
    (* Base 1 complete *)
    rewrite (VSn_eq a0). rewrite Vapp_cons. 
    do 2 rewrite VG_prod_Vcons. rewrite IHn. 
    do 2 rewrite <- dot_assoc. apply left_cancel. apply comm.
  Qed.

  Lemma VG_prod_VG_Pexp_app :
    forall (n m : nat)(a : VG n)(b : VG m)(c : VF (n+m)),
    VG_prod (VG_Pexp (Vapp a b) c) = 
      VG_prod (VG_Pexp a (Vbreak c).1) o
      VG_prod (VG_Pexp b (Vbreak c).2).
  Proof.
    intros. rewrite (Vbreak_eq_app c). unfold VG_Pexp.
    rewrite Vapp_Vmap2. rewrite Vapp_VG_prod. 
    rewrite Vbreak_app. simpl. auto.
  Qed.

  Lemma VG_prod_add : forall (l : nat)(a :  VG l)(b : G),
    VG_prod (Vadd a b) = VG_prod a o b.
  Proof.
    pose (module_abegrp).
    intros. induction l. rewrite (Vector_0_is_nil a0).
    cbn. trivial. symmetry. rewrite VG_prod_induction.
    rewrite <- dot_assoc. replace (Vhead a0 o b) with 
    (b o Vhead a0). rewrite dot_assoc. rewrite <- IHl.
    rewrite <- VG_prod_Vcons. rewrite Vadd_cons. trivial.
    apply comm.
  Qed.

  Lemma VG_prod_rev : forall (l : nat)(a : VG l),
    VG_prod a = VG_prod (rev a).
  Proof.
    intros. induction l. rewrite (Vector_0_is_nil a).
    cbn. trivial. rewrite VG_prod_induction.
    rewrite IHl. rewrite (VSn_eq a). rewrite rev_Vcons.
    simpl. rewrite VG_prod_add. trivial.
  Qed.

  Lemma VG_prod_VG_Pexp_rev : forall (l : nat)(a : VG l)
    (b :VF l),
    VG_prod (VG_Pexp (rev a) b) = VG_prod (VG_Pexp a (rev b)).
  Proof.
    intros. rewrite VG_prod_rev. apply Vfold_left_eq.
    apply Veq_nth. intros. rewrite Vbuild_nth. do 2 rewrite 
    Vnth_map2. do 2 rewrite Vbuild_nth. rewrite invertPosCancel. 
    trivial.
  Qed.

  Lemma VG_prod_VG_Pexp : forall (n m : nat)(x : VG n)
      (ys: vector (VF n) m)(ss : VF m),
    VG_prod (Vmap2 (fun y s =>
      VG_prod (VG_Pexp x (VF_scale y s)))
         ys ss) = 
    VG_prod (VG_Pexp x
      (Vfold_left (VF_add (n:=n)) (VF_zero n) 
        (Vmap2 (VF_scale (n:=n)) ys ss))
    ).
  Proof.
    intros. induction m. cbn. rewrite VG_Zero_exp.
    symmetry. apply VG_Zero_prod. rewrite VG_prod_induction. 
    rewrite <- Vtail_map2. rewrite IHm. rewrite Vhead_nth.
    rewrite Vnth_map2. rewrite <- VG_Prod_mult_dist.
    apply Vfold_left_eq. pose VG_mult_VG_Pexp_Fadd.
    unfold VG_mult in e. rewrite e. rewrite <- Vfold_left_Vcons_VFadd.
    do 2 rewrite <- Vhead_nth. rewrite <- Vcons_map2.
    do 2 rewrite <- VSn_eq. trivial.
  Qed.

  Definition VG_scale_sum (n j m : nat)(b : vector (vector 
      (VF n) j) m) :=
     Vfold_left (fun x y => 
      Vmap2 (VF_add (n:=n)) x y) (Vconst (VF_zero n) j) b.

  Lemma VG_scale_sum_induction : forall (n j m : nat)
    (b : vector (vector (VF n) j) (S m)),
    VG_scale_sum b = Vmap2 (VF_add (n:=n)) (VG_scale_sum (Vtail b))
    (Vhead b).
  Proof.
    intros. unfold VG_scale_sum. rewrite (VSn_eq b). cbn.
    rewrite Vfold_VFadd_vector_const. trivial.
  Qed.

  Lemma VG_Zero_exp_vec : forall n j (C : vector (VG n) j),
    Vmap2 (fun Ci Xi => VG_prod (VG_Pexp Ci Xi)) C 
      (Vconst (VF_zero n) j) = VG_id j.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vnth_const. rewrite VG_Zero_exp. rewrite VG_Zero_prod.
    rewrite Vnth_const. trivial.
  Qed.

  Lemma VG_Pexp_Pexp : forall n (a : VG n)(b c : VF n),
    VG_Pexp (VG_Pexp a b) c = VG_Pexp a (VF_mult b c).
  Proof.
    intros. apply Veq_nth. intros. do 4 rewrite Vnth_map2. 
    rewrite <- mod_dist_FMul2. trivial.
  Qed.

  Lemma VG_prod_pexp : forall n m (C : vector (VG n) m)(a b : vector (VF n) m),
  VG_prod (Vmap2 (fun Ci xi => VG_prod (VG_Pexp Ci xi)) C (Vmap2 (VF_add (n:=n))
    a b)) = Gdot (VG_prod (Vmap2 (fun Ci xi => VG_prod (VG_Pexp Ci xi)) 
    C a)) (VG_prod (Vmap2 (fun (Ci : VG n) (xi : VF n) =>
      VG_prod (VG_Pexp Ci xi)) C b)).
  Proof.
    pose module_abegrp.
    intros. induction m. cbn. symmetry. apply one_right. rewrite (VSn_eq a0).
    rewrite (VSn_eq b). rewrite Vcons_map2. rewrite (VSn_eq C).
    do 3 rewrite Vcons_map2. do 3 rewrite VG_prod_Vcons. rewrite IHm.
    do 2 rewrite <- dot_assoc. apply left_cancel. rewrite comm.
    rewrite <- VG_mult_VG_Pexp_Fadd. rewrite VG_Prod_mult_dist.
    rewrite <- dot_assoc. apply left_cancel. apply comm.
  Qed.
    
  Lemma VG_prod_VG_Pexp_2 :  forall (n m j : nat)
    (a : VF m)(b : vector (VF n) m)(C : vector (VG n) j)
    (f : F -> VF j),
    let b2 := Vmap2 (fun x y => (Vmap (fun xi => 
         VF_scale y xi) (f x))) a b in
    VG_prod (Vmap2 
      (fun (x : F) (y : VF n) => VG_prod (Vmap2 
        (fun (Ci : VG n) (xi : F) => 
            VG_prod (VG_Pexp Ci (VF_scale y xi)))
           C (f x))) a b) = 
    VG_prod (Vmap2 (fun (Ci : VG n) (xi : VF n) => 
          VG_prod (VG_Pexp Ci xi)) C (VG_scale_sum b2)).
  Proof.
    pose module_abegrp.
    intros. induction m. cbn. rewrite VG_Zero_exp_vec. rewrite VG_Zero_prod. 
    trivial. rewrite (VSn_eq a0). rewrite (VSn_eq b). simpl. rewrite VG_prod_Vcons.
    rewrite IHm. rewrite VG_scale_sum_induction. rewrite VG_prod_pexp.
    apply f_equal2. trivial. unfold b2.
    apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    apply f_equal. simpl. rewrite Vnth_map. trivial.
  Qed.
      
  Lemma VG_prod_cast : forall (n m : nat)(nm : n=m)(c : VG n),
    VG_prod c = VG_prod (Vcast c nm).
  Proof.
    intros. induction n. rewrite (Vector_0_is_nil c).
    subst. cbn. trivial. subst. rewrite VG_prod_induction. 
    trivial.
  Qed.

  Lemma VG_prod_induction_2 :
    forall(N : nat)(v : VG (S (N+N))),
    VG_prod v = VG_prod (Vremove_last v) o (Vlast (Vhead v) v).
  Proof.
    intros. rewrite (VSn_add_default (Vhead v) v).
    rewrite VG_prod_add. rewrite <- VSn_add_default. trivial.
  Qed.

  Lemma VG_prod_induction_dob :
    forall(N : nat)(v : VG (S N + S N)),
    VG_prod v = VG_prod (double_induct v) o (Vhead v) o (Vlast (Vhead v) v).
  Proof.
    pose module_abegrp.
    intros. unfold double_induct. rewrite (VG_prod_cast (casting_double_induct N)).
    rewrite VG_prod_induction. rewrite VG_prod_induction_2.
    do 2 rewrite <- dot_assoc. apply f_equal. rewrite comm.
    rewrite Vhead_cast. apply f_equal. do 2 rewrite Vlast_nth.
    rewrite Vnth_tail. rewrite Vnth_cast. apply Vnth_eq. auto.
  Qed.

  Lemma double_exp_over_fixed_base :
    forall m n (b : VG m)(e : vector (VF m) n)(e' : VF n),
    VG_Pexp (Vmap (fun x : VF m => 
      VG_prod (VG_Pexp b x)) e) e' = 
    Vmap (fun x : VF m => 
      VG_prod (VG_Pexp b x)) (Vmap2 (VF_scale (n:=m)) e e').
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2.
    do 2 rewrite Vnth_map. rewrite Vnth_map2.
    apply Sexp_dist.
  Qed.

  Lemma mat_build_nill : forall m 
    (gen : forall i j, i < m -> j < 0 -> F),
    FMatrix.mat_build gen = Vconst Vnil m.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_const.
    apply Veq_nth. intros. rewrite FMatrix.mat_build_nth.
    assert False. lia. contradiction.
  Qed. 

  Lemma VG_prod_const_one : forall m,
    VG_prod (Vconst Gone m) = Gone.
  Proof.
    pose module_abegrp.
    intros. induction m. cbn. trivial. rewrite VG_prod_induction.
    rewrite Vtail_const. rewrite IHm. rewrite Vhead_nth.
    rewrite Vnth_const. rewrite one_left. trivial.
  Qed.

  Lemma Vmap_prod_pexp : forall m n (b : VG m)
    (e : vector (VF m) n),
    VG_prod (Vmap (fun x : VF m => VG_prod (VG_Pexp b x)) e) =
    VG_prod (VG_Pexp b (Vmap (VF_sum (n:=n)) (FMatrix.mat_transpose e))).
  Proof.
    intros. induction n. rewrite (Vector_0_is_nil e). cbn.
    unfold FMatrix.mat_transpose. rewrite mat_build_nill.
    assert (VG_Pexp b (Vmap (VF_sum (n:=0)) (Vconst [ ] m)) =
    Vconst Gone m). apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vnth_map. do 2 rewrite Vnth_const. cbn.
    rewrite mod_ann. trivial. rewrite H. rewrite VG_prod_const_one.
    trivial. (* Inductive case *)
    rewrite VG_prod_induction. rewrite <- Vmap_tail.
    rewrite IHn. unfold VG_prod. rewrite Vhead_nth. 
    rewrite Vnth_map. rewrite VF_add_product.
    apply Vfold_left_eq. apply Veq_nth. intros. 
    do 3 rewrite Vnth_map2. apply f_equal2; auto.
    do 2 rewrite Vnth_map. destruct module_ring. unfold FSemiRingT.Aplus.
    rewrite Radd_comm.
    (* May need to move this *)
     rewrite <- VF_sum_vcons.
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_cons.
    destruct (lt_ge_dec 0 i0). do 2 rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_elem, FMatrix.get_row. rewrite Vnth_tail.
    apply Veq_nth3; auto. apply Vnth_eq. lia. rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_elem, FMatrix.get_row. apply Veq_nth3; auto. 
    assert (i0 = 0%nat). lia. subst. apply Vnth_eq. lia.
  Qed.
   

  Lemma VG_prod_pexp_fixed_base :
    forall m n n' (H : n = n')(H' : n' = n)
      (b : VG m)(e : vector (VF m) n)(e' : VF n'),
    VG_prod (VG_Pexp (Vcast (Vmap (fun x : VF m => 
      VG_prod (VG_Pexp b x)) e) H) e') =
      VG_prod (VG_Pexp b (Vhead (FMatrix.mat_mult [Vcast e' H'] e))). 
  Proof.
    intros. subst. simpl. rewrite double_exp_over_fixed_base.
    rewrite Vmap_prod_pexp. apply f_equal. apply f_equal2; auto.
    apply Veq_nth. intros. rewrite Vnth_map. rewrite Vbuild_nth.
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq. apply Vfold_left_eq.
    apply Veq_nth. intros. rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_elem, FMatrix.get_row. do 2 rewrite Vnth_map2.
    rewrite Vnth_map. destruct module_ring. rewrite Rmul_comm.
    apply f_equal2. apply Veq_nth3; auto. cbn. rewrite Vcast_refl.
    trivial. rewrite Vnth_map. trivial.
  Qed.

  Lemma PexpMatrix_nth : forall (N : nat)(c : VG N)(e : MF N) i (ip : i < N) x 
      (xp : x < N),
    Vnth e ip = FMatrix.VA.id_vec xp ->
    Vnth (PexpMatrix c e) ip = Vnth c xp.
  Proof.  
    pose module_abegrp. intros. rewrite Vnth_map. rewrite H. 
    rewrite (Veq_app (VG_Pexp c (FMatrix.VA.id_vec xp)) xp). 
    rewrite <- VG_prod_cast. rewrite Vapp_VG_prod.
    replace (VG_prod (Vsub (VG_Pexp c (FMatrix.VA.id_vec xp)) (Veq_app_aux2 xp))) with Gone.
    rewrite one_right. rewrite (VSn_addS (Vsub (VG_Pexp c (FMatrix.VA.id_vec xp)) (Veq_app_aux1 xp))).
    unfold VG_prod. rewrite Vfold_add. intros. rewrite dot_assoc. trivial.
    intros. apply comm. replace (Vfold_left Gdot Gone
  (Vremove_last (Vsub (VG_Pexp c (FMatrix.VA.id_vec xp)) (Veq_app_aux1 xp)))) with
    Gone. rewrite one_left. rewrite VlastS_nth. rewrite Vnth_sub. rewrite Vnth_map2.
    rewrite Vnth_replace. rewrite mod_id. apply f_equal. apply le_unique. 
    (* Clean up *)
    symmetry. apply VG_Zero_prod_gen. apply Veq_nth. intros. rewrite Vnth_remove_last.
    rewrite Vnth_sub. rewrite Vnth_map2. rewrite Vnth_replace_neq. lia. do 2 rewrite Vnth_const.
    rewrite mod_ann. trivial.
    symmetry. apply VG_Zero_prod_gen. apply Veq_nth. intros. rewrite Vnth_sub. 
    rewrite Vnth_map2. rewrite Vnth_replace_neq. lia. do 2 rewrite Vnth_const.
    rewrite mod_ann. trivial.
  Qed.

  Lemma PexpMatrixId : forall N (c : VG N),
    PexpMatrix c (MF_id N) = c.
  Proof.
    intros. apply Veq_nth. intros. apply PexpMatrix_nth. rewrite Vbuild_nth. trivial.
  Qed.

  (* This should be in a library but at the moment not apprioate library exist *)
  Lemma PexpMatrix_Prod : forall (N : nat)(c : VG N)(e : MF N),
    MFisPermutation e ->
    VG_prod (PexpMatrix c e) = VG_prod c.
  Proof.
    pose module_abegrp. intros. induction N. rewrite (Vector_0_is_nil c). 
    rewrite (Vector_0_is_nil e). cbn. trivial. 
    (* Base case complete *)
    rewrite (VSn_addS c). unfold VG_prod. rewrite Vfold_add. intros. 
    rewrite dot_assoc. trivial. intros. rewrite comm. trivial. unfold VG_prod in IHN.
    rewrite <- (IHN (Vremove_last c) (MF_perm_sub e)). rewrite <- VSn_addS.
    (* We need to break the vector into parts *)
    pose (proj2_sig (MF_perm_last e)).
    rewrite (Veq_app (PexpMatrix c e) l). pose VG_prod_cast. unfold VG_prod in e0.
    rewrite <- e0. pose Vapp_VG_prod. unfold VG_prod in e1. rewrite e1.
    assert (0+(sval (MF_perm_last e))<= N). assert (sval (MF_perm_last e) < S N). apply l.
    lia. rewrite (Veq_app (PexpMatrix (Vremove_last c) (MF_perm_sub e)) H0). 
    rewrite <- e0. rewrite e1. symmetry. rewrite comm. rewrite dot_assoc. apply f_equal2.
    (* part 1 *)
    rewrite comm. rewrite <- Vfold_add. apply f_equal. apply Veq_nth. intros.
    rewrite Vnth_add. destruct (Nat.eq_dec i (0 + sval (MF_perm_last e))).
    rewrite VlastS_nth. rewrite Vnth_sub. rewrite PexpMatrix_nth; trivial.
    pose (MF_perm_last_corr e H). rewrite <- e3. apply Veq_nth3. lia. trivial.
    do 2 rewrite Vnth_sub. do 3 rewrite Vnth_map. rewrite (VSn_addS (VG_Pexp c 
    (Vnth e (Vnth_sub_aux 0 (Veq_app_aux1 l) ip)))). unfold VG_prod. rewrite Vfold_add.
    intros. rewrite dot_assoc. trivial. intros. apply comm. rewrite VlastS_nth.
    rewrite Vnth_map2. rewrite MF_perm_clear_nth; trivial. rewrite mod_ann.
    rewrite one_right. apply f_equal. apply Veq_nth. intros. rewrite Vnth_remove_last.
    do 2 rewrite Vnth_map2. do 2 rewrite Vnth_remove_last. apply f_equal.
    rewrite Vremove_correct_left. lia. apply Veq_nth3. trivial. apply Vnth_eq. trivial.
    (* clean up for part 1 *)
    intros. rewrite dot_assoc. trivial. intros. apply comm.
    (* part 2 *)
    apply f_equal. apply Veq_nth. intros. do 2 rewrite Vnth_sub. do 3 rewrite Vnth_map.
    rewrite (VSn_addS ((VG_Pexp c (Vnth e (Vnth_sub_aux (S (sval (MF_perm_last e))) (Veq_app_aux2 l) ip))))).
    rewrite VG_prod_add. rewrite VlastS_nth. rewrite Vnth_map2.
    pose ((Vnth_sub_aux (S (sval (MF_perm_last e))) (Veq_app_aux2 l) ip)).
    rewrite MF_perm_clear_nth; auto. lia. rewrite mod_ann. rewrite one_right.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_remove_last. do 2 rewrite Vnth_map2.
    do 2 rewrite Vnth_remove_last. apply f_equal. rewrite Vremove_correct_right. lia.
    apply Veq_nth3. trivial. apply Vnth_eq. lia. 
    (* clean up *)
    apply permTranInd_sub; trivial.
  Qed.

  Lemma PexpMatrix_Pexp : forall (N : nat)(c : VG N)(e : MF N)(a : VF N),
    MFisPermutation e ->
    VG_Pexp (PexpMatrix c e) a = PexpMatrix (VG_Pexp c (MF_CVmult (MF_trans e) a)) e.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. assert (MFisPermutation e).
    trivial. unfold MFisPermutation in H.  apply andb_true_iff in H.  destruct H.
    apply (bVforall_elim_nth ip) in H.
    apply bVexists_eq in H. elim H. intros. elim H2.
    intros. clear H2. apply VF_beq_true in H3. rewrite Vbuild_nth in H3.
    rewrite (PexpMatrix_nth c e ip x0 H3). rewrite (PexpMatrix_nth 
    (VG_Pexp c (MF_CVmult (MF_trans e) a)) e ip x0 H3). rewrite Vnth_map2. rewrite Vnth_map. 
    rewrite FMatrix.mat_build_nth. rewrite FMatrix.get_col_col_mat.
    pose (MF_perm_mix_eq e ip x0 H0). apply i0 in H3. unfold FMatrix.get_row.
    rewrite H3. rewrite FMatrix.VA.dot_product_id. trivial.
  Qed.

  Lemma PexpMatrix_MF_mult : forall (N : nat)(c : VG N)(e0 e1 : MF N) i (ip : i < N),
    Vnth (PexpMatrix c (MF_mult e0 e1)) ip = VG_prod (Vbuild
     (fun (j : nat) (jp : j < N) => VG_prod (VG_Pexp c (Vnth e1 jp)) ^ Vnth (Vnth e0 ip) jp)).
  Proof.
    intros. rewrite Vnth_map. rewrite MF_getRow_VCmul. rewrite VG_prod_VG_Pexp_MF_VCmult. trivial. 
  Qed.

  Lemma PexpMatrix_MF_mult_base : forall (N : nat)(s : VG N)(a b : MF N),  
    PexpMatrix (PexpMatrix s a) b = PexpMatrix s (MF_mult b a).
  Proof.
    intros. apply Veq_nth. intros. rewrite PexpMatrix_MF_mult. rewrite Vnth_map. apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vbuild_nth. rewrite Vnth_map. trivial.
  Qed.

  Lemma PexpMatrix_mult  : forall (N : nat)(a b : VG N)(c : MF N),  
     PexpMatrix (VG_mult a b) c = VG_mult (PexpMatrix a c) (PexpMatrix b c).
  Proof.
    intros. unfold PexpMatrix. apply Veq_nth. intros. rewrite Vnth_map2.
    do 3 rewrite Vnth_map. rewrite VG_Pexp_mult. unfold VF_prod. 
    rewrite VG_Prod_mult_dist. trivial.
  Qed.

  Lemma VG_Pexp_build : forall n (gen : forall i, i < n -> G) (a : VF n),
    Vbuild (fun (j : nat) (jp : j < n) => gen j jp ^ Vnth a jp) = VG_Pexp (Vbuild (fun (j : nat) 
      (jp : j <n) => gen j jp)) a.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vbuild_nth.  trivial.
  Qed.

  Lemma VG_mult_build : forall n (gen1 gen2 : forall i, i < n -> G),
    Vbuild (fun (j : nat) (jp : j < n) => gen1 j jp o gen2 j jp) = VG_mult (Vbuild (fun (j : nat) 
      (jp : j <n) => gen1 j jp)) (Vbuild (fun (j : nat) (jp : j <n) => gen2 j jp)).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vbuild_nth.  trivial.
  Qed.

  Lemma VG_Pexp_inProd : forall n h (m x : VF n),
    VG_Pexp (Vmap (op h) m) x = Vmap (op h) (VF_mult m x).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vnth_map.
    rewrite VF_comm_mult. rewrite Vnth_map2. rewrite mod_dist_Fmul. trivial.
  Qed.

  Lemma VG_prod_pexp_VecToMat : forall n m (t : VG (n*m))(y : VF (n*m)),
    VG_prod (Vmap2 (fun x y => VG_prod (VG_Pexp x y))
        (VecToMat n m t)(VecToMat n m y)) = VG_prod (VG_Pexp t y).
  Proof.
    pose Group.module_abegrp. intros. induction m. 
    + cbn. assert (Nat.mul n 0%nat = 0%nat). lia. 
    unfold VG_prod. rewrite Vfold_left_nil_gen. lia. trivial.
    + rewrite VG_prod_induction. rewrite <- Vtail_map2. 
    do 2 rewrite VecToMatTail. rewrite IHm. unfold VG_prod.
    rewrite <- Vfold_left_Vcons. rewrite Vhead_map2. rewrite Vfold_left_Vcons.
    rewrite comm. pose Vapp_VG_prod. unfold VG_prod in *. rewrite <- e.
    assert (Nat.mul n (S m) = Nat.add n (Nat.mul n m)). clear IHm. clear e. 
    clear t. clear y. induction n. lia. lia. rewrite (Vfold_left_cast_irr H). 
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_app. destruct (le_gt_dec n i).
    ++ rewrite Vnth_cast. do 2 rewrite Vnth_map2. do 2 rewrite Vnth_sub.
    apply f_equal2; apply Vnth_eq; lia.
    ++ do 2 rewrite Vbuild_head. rewrite Vnth_cast. do 2 rewrite Vnth_map2.
    do 2 rewrite Vnth_sub. apply f_equal2; apply Vnth_eq; lia.
  Qed.

  
 

End MatricesG.
