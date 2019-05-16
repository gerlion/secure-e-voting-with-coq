Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import groups.
Require Import Coq.Lists.List.
Require Import Ring.
Require Import Field.
Require Import HeliosIACR2018.

Section Matrices.
Delimit Scope Matrices with F.
Open Scope Matrices.

(* This file contains the definitons and lemmas about matrices *)
(* This needs to be generalised, so that we can do the
 extraction of the mixnet properly *)

Infix "+" := Fadd.
Infix "*" := Fmul.
Notation "x / y" := (Fmul x (FmulInv y)). 
Notation "0" := Fzero.
Notation "1" := Fone.
Notation "- x" :=  (Finv x).
Notation "x - y" := (x + (- y)).

Infix "o" := Gdot (at level 50) .
Notation "- x" := (Ginv x).

Infix "^" := op.

(*We use P* to denote the pairwise use of the operation *)
(*We use S* to denote the scaler use of the operation *)


(* Vectors of length 2 over Field F *)

Structure V2F : Type := {r1 : F; r2: F}.
Definition V2F_zero : V2F := Build_V2F 0 0.
Definition V2F_one : V2F := Build_V2F 1 1.
Definition V2F_prod (v : V2F) : F :=
(r1 v) * (r2 v).
Definition V2F_sum (v : V2F) : F :=
(r1 v) + (r2 v).
Definition V2F_add (v1 v2 : V2F) : V2F :=
Build_V2F ((r1 v1) + (r1 v2)) ((r2 v1) + (r2 v2)).
Definition V2F_neg (v1 : V2F) : V2F :=
Build_V2F (Finv (r1 v1))(Finv (r2 v1)).
Definition V2F_sub (v1 v2 : V2F) : V2F :=
Build_V2F ((r1 v1) - (r1 v2)) ((r2 v1) - (r2 v2)).
Definition V2F_mult (v1 v2 : V2F) : V2F :=
Build_V2F ((r1 v1) * (r1 v2)) ((r2 v1) * (r2 v2)).
Definition V2F_scale (v : V2F)(s : F) : V2F :=
Build_V2F((r1 v) * s)((r2 v) * s).
Definition V2F_inProd (v v' : V2F) : F :=
r1 v * r1 v' + r2 v * r2 v'.
Definition V2F_eq (r r' : V2F) : bool :=
  Fbool_eq (r1 r) (r1 r') && Fbool_eq (r2 r) (r2 r').

(* Vectors of length 2 over Abelien Group G *)

Structure V2G : Type := {m1 : G; m2: G}.        
Definition V2G_id : V2G := Build_V2G Gone Gone.
Definition V2G_mult (v v' : V2G) : V2G := 
Build_V2G (m1 v o m1 v')(m2 v o m2 v').
Definition V2G_inv (v : V2G) : V2G :=
Build_V2G (Ginv (m1 v))(Ginv (m2 v)).
Definition V2G_prod (v : V2G) : G :=
m1 v o m2 v.
Definition V2G_Pexp (v : V2G)(v' : V2F) : V2G :=
 Build_V2G (m1 v ^ r1 v')(m2 v ^ r2 v').
Definition V2G_Sexp (v: V2G)(e : F) : V2G :=
 Build_V2G (m1 v ^ e)(m2 v ^ e).
Definition V2G_cons (m : (G*G)) : V2G:= Build_V2G m.1 m.2.
Definition V2G_eq (m m' : V2G) : bool :=
  Gbool_eq (m1 m) (m1 m') && Gbool_eq (m2 m) (m2 m').

(* Square matrices of order 2 over Field F *)

Structure M2F : Type := {r00 : F; r01 : F;   (* r00 r01 *)
r10 : F; r11 : F}.                           (* r10 r11 *)
Definition M2F_id : M2F := Build_M2F 1 0 0 1.
Definition M2F_col1 (m : M2F) : V2F :=
  Build_V2F(r00 m)(r10 m).
Definition M2F_col2 (m : M2F) : V2F :=
  Build_V2F(r01 m)(r11 m).
Definition M2F_row1 (m : M2F) : V2F :=
  Build_V2F(r00 m)(r01 m).
Definition M2F_row2 (m : M2F) : V2F :=
  Build_V2F(r10 m)(r11 m).
Definition M2F_mult (m m':M2F) : M2F :=
Build_M2F (r00 m * r00 m' + r01 m * r10 m')
(r00 m * r01 m' + r01 m * r11 m')
(r10 m * r00 m' + r11 m * r10 m')
(r10 m * r01 m' + r11 m * r11 m').
Definition M2F_CVmult (m : M2F)(v : V2F) : V2F :=
  Build_V2F (V2F_inProd (M2F_row1 m) v) (V2F_inProd (M2F_row2 m) v).
Definition M2F_VCmult (v : V2F)(m : M2F) : V2F :=
  Build_V2F (V2F_inProd (M2F_col1 m) v) (V2F_inProd (M2F_col2 m) v).
Definition M2F_eq (m m' : M2F) : bool :=
  Fbool_eq (r00 m) (r00 m') && Fbool_eq (r01 m) (r01 m') &&
  Fbool_eq (r10 m) (r10 m') && Fbool_eq (r11 m) (r11 m').
Definition M2F_Fscal (m : M2F)(v : V2F) : M2F :=
  Build_M2F (r00 m * r1 v)(r01 m * r2 v)
(r10 m * r1 v)(r11 m * r2 v).
Definition M2F_isPermutation (m : M2F) :=
   M2F_eq m (Build_M2F 1 0 0 1) || M2F_eq m (Build_M2F 0 1 1 0).
Definition M2F_deter (m : M2F) : F :=
 (r00 m * r11 m)-(r01 m *r10 m).
Definition M2F_inv (m : M2F) : M2F :=
 let det := M2F_deter m in
 Build_M2F (r11 m /det)
           (Finv (r01 m)/det)
           (Finv (r10 m)/det)
           (r00 m /det).
Definition M2F_col_con (m m' : V2F) : M2F :=
  Build_M2F (r1 m) (r1 m') (r2 m) (r2 m').


(*Addational definitions thaat only make sense for the crypto we are doing*)

Definition ciphExp (c : (V2G*V2G))(e : V2F) : (V2G*V2G) :=
  (V2G_Sexp c.1 (r1 e), V2G_Sexp c.2 (r2 e)).

Definition V2G_Tprod (c : (V2G*V2G)) : V2G :=
  V2G_mult c.1 c.2.


Definition ciphMatrix (c : (V2G*V2G))(e : M2F) : (V2G*V2G) :=
  (V2G_Tprod (ciphExp c (M2F_col1 e)),V2G_Tprod (ciphExp c (M2F_col2 e))).

Lemma V2G_eqBreakDown :
  forall m m' : V2G,
  m = m' <-> (m1 m = m1 m' /\ m2 m = m2 m').
Proof.  
  pose HeliosIACR2018.
  intros. unfold iff. refine (conj _ _).
  intros. rewrite H. split. trivial. split. trivial.
  intros. destruct H.
  destruct m. destruct m'. simpl in *. rewrite H.
  rewrite H0. trivial.
Qed.

Lemma V2F_eqBreakDown :
  forall m m' : V2F,
  m = m' <-> (r1 m = r1 m' /\ r2 m = r2 m').
Proof.  
  pose HeliosIACR2018.
  intros. unfold iff. refine (conj _ _).
  intros. rewrite H. split. trivial. split. trivial.
  intros. destruct H.
  destruct m. destruct m'. simpl in *. rewrite H.
  rewrite H0. trivial.
Qed.
 
Lemma M2F_eqBreakDown :
  forall m m' : M2F,
  m = m' <-> (r00 m = r00 m' /\ r01 m = r01 m' /\ 
      r10 m = r10 m' /\ r11 m = r11 m').
Proof.  
pose HeliosIACR2018.

  intros. unfold iff. refine (conj _ _).
  intros. rewrite H. split. trivial. split. trivial.
  split. trivial. split. trivial.
  intros. destruct H. destruct H0. destruct H1.
  destruct m. destruct m'. simpl in *. rewrite H.
  rewrite H0. rewrite H1. rewrite H2. trivial.
Qed.

(*Lemmas on Vectors of length 2 over Abelien Group G *)
Lemma V2G_Sexp_id : 
  forall (e : V2G), 
  V2G_Sexp e 1 = e.
Proof.
  pose HeliosIACR2018.
  intros.  unfold V2G_Sexp. destruct e. simpl. do 2 rewrite mod_id. trivial.
Qed.

Lemma V2G_Sexp_ann :
forall (e : V2G), 
   V2G_Sexp e 0 = V2G_id.
Proof.
  pose HeliosIACR2018.
  intros. unfold V2G_Sexp. destruct e. simpl. do 2 rewrite mod_ann. trivial.
Qed.

Lemma V2G_Sexp_dis_dot :
  forall (a b : V2G)(c : F),
  V2G_Sexp (V2G_mult a b) c = V2G_mult (V2G_Sexp a c) (V2G_Sexp b c).
Proof.
  pose HeliosIACR2018.
  intros. unfold V2F_mult. unfold V2G_Sexp. simpl.
   apply V2G_eqBreakDown. simpl.  split. apply mod_dist_Gdot.
  apply mod_dist_Gdot.
Qed.

Lemma V2G_Sexp_dis_add :
  forall (a: V2G)(b c : F),
  V2G_Sexp a (b+c) = V2G_mult (V2G_Sexp a b) (V2G_Sexp a c).
Proof.
  pose HeliosIACR2018.
  intros. unfold V2F_mult. unfold V2G_Sexp. simpl.
   apply V2G_eqBreakDown. simpl.  split. apply mod_dist_Fadd.
  apply mod_dist_Fadd.
Qed.

Lemma V2G_Sexp_dis_mul :
  forall (a: V2G)(b c : F),
  V2G_Sexp a (b*c) = V2G_Sexp (V2G_Sexp a b) c.
Proof.
  pose HeliosIACR2018.
  intros. unfold V2F_mult. unfold V2G_Sexp. simpl.
   apply V2G_eqBreakDown. simpl.  split. apply mod_dist_FMul2.
  apply mod_dist_FMul2.
Qed.


Lemma V2G_Sexp_inv :
  forall (a : V2G)(c : F),
  V2G_inv (V2G_Sexp a c) = V2G_Sexp a (Finv c).
Proof.
  pose HeliosIACR2018.
  intros. unfold V2G_inv. unfold V2G_Sexp. simpl.
   apply V2G_eqBreakDown. simpl.  split. apply neg_eq. apply neg_eq.
Qed.

Lemma V2G_InvCorr :
  forall (e : V2G),
  V2G_mult e (V2G_inv e) = V2G_id.
Proof.
    pose HeliosIACR2018.
  intros. unfold V2G_mult. unfold V2G_inv. unfold V2G_id. 
  apply V2G_eqBreakDown. simpl.  split. rewrite <- inv_right. trivial.
  rewrite <- inv_right. trivial.
Qed.

Lemma V2G_Comm :
forall (e e' : V2G),
  V2G_mult e e' = V2G_mult e' e.
Proof.
  pose HeliosIACR2018.
 intros. destruct e. destruct e'. unfold V2G_mult. simpl.
 rewrite comm. replace (m4 o m6) with (m6 o m4) by apply comm. trivial.
Qed.

Lemma V2G_InvCorr2 :
  forall (e : V2G),
  V2G_mult (V2G_inv e) e = V2G_id.
Proof.
  intros. rewrite V2G_Comm. apply V2G_InvCorr.
Qed.

Lemma V2G_Assoc :
forall (x y z : V2G),
  V2G_mult (V2G_mult x y) z = V2G_mult x (V2G_mult  y z).
Proof.
  pose HeliosIACR2018.
  intros. apply V2G_eqBreakDown. unfold V2G_mult. simpl. split.
  rewrite dot_assoc. trivial. rewrite dot_assoc. trivial.
Qed.

Lemma V2G_right_cancel :  forall x y z: V2G,
 (V2G_mult y x) = (V2G_mult z x) <-> (y = z).
Proof.
  pose HeliosIACR2018.
  intros. unfold V2G_mult. destruct x. destruct y. destruct z.
  simpl in *. unfold iff. refine (conj _ _).  intros.
  apply V2G_eqBreakDown. apply V2G_eqBreakDown in H. destruct H.
  simpl in *. split. apply right_cancel in H. apply H.
  apply right_cancel in H0. apply H0. intros.
  apply V2G_eqBreakDown. apply V2G_eqBreakDown in H. destruct H.
  simpl in *. split. rewrite H. trivial. rewrite H0. trivial.
Qed.

Lemma V2G_commHack :
  forall a b c d : V2G,
  V2G_mult (V2G_mult a b) (V2G_mult c d) = 
    V2G_mult (V2G_mult a c) (V2G_mult b d).
Proof.
  intros. do 2 rewrite <- V2G_Assoc. apply V2G_right_cancel.
  rewrite V2G_Assoc. replace (V2G_mult b c) with (V2G_mult c b).
  rewrite V2G_Assoc. trivial. apply V2G_Comm.
Qed.

Lemma V2G_One :
forall (e : V2G),
  V2G_mult e V2G_id = e.
Proof.
  pose HeliosIACR2018.
  intros. destruct e. unfold V2G_id. unfold V2G_mult. simpl.
  do 2 rewrite one_right. trivial.
Qed.

Lemma V2G_inv_dist :
forall (a b : V2G),
  V2G_mult (V2G_inv a) (V2G_inv b) = V2G_inv (V2G_mult a b).
Proof.
  pose HeliosIACR2018.
  intros. unfold V2G_inv. unfold V2G_mult. simpl.
  apply V2G_eqBreakDown. simpl. destruct a. destruct b. simpl. split.
  apply (@inv_dist G Gdot Gone Gbool_eq Ginv module_abegrp m3 m5).
  apply (@inv_dist G Gdot Gone Gbool_eq Ginv module_abegrp m4 m6).
Qed.

Lemma V2G_inv_dist2 :
forall (a b : V2G),
  V2G_inv (V2G_mult a b) = V2G_mult (V2G_inv a) (V2G_inv b).
Proof.
  symmetry. apply V2G_inv_dist.
Qed.


Lemma V2G_One_exp :
forall (e : V2G),
  V2G_Pexp e V2F_one = e.
Proof.
    pose HeliosIACR2018.
  intros. unfold V2G_Pexp. unfold V2F_one. simpl. rewrite mod_id.
  rewrite mod_id. destruct e. simpl. trivial.
Qed.

Lemma V2G_Mul :
  forall (a b c d : V2G),
     a = c /\ b = d -> V2G_mult a b = V2G_mult c d.
Proof.
  pose HeliosIACR2018. intros.
  destruct H. rewrite H. rewrite H0. intuition.
Qed.

Lemma invCorrect :
  forall m : M2F,
  M2F_deter m <> 0 ->
  M2F_mult m (M2F_inv m) = M2F_id.
Proof.
  Add Field vs_field : Ffield.
  intros.  unfold M2F_inv. unfold M2F_mult. unfold M2F_deter in *.
  simpl. apply M2F_eqBreakDown. split. simpl. field; auto.
  split. simpl. field; auto. split. simpl. field; auto.
  simpl. field; auto.
Qed.

Lemma V2Geq :
  forall m m' : V2G,
  V2G_eq m m' = true <-> m = m'.
Proof.
  pose HeliosIACR2018.
  intros. unfold iff. refine (conj _ _).  intros. unfold V2G_eq in *.
  destruct m' in *. destruct m in *. simpl in *. apply andb_true_iff in H.
  destruct H. apply bool_eq_corr in H. apply bool_eq_corr in H0.
  rewrite H. rewrite H0. trivial. intros. rewrite H. unfold V2G_eq.
  apply andb_true_iff. split. apply bool_eq_corr. trivial.
  apply bool_eq_corr. trivial.
Qed.

Lemma Meq :
  forall m m' : M2F,
  M2F_eq m m' = true <-> m = m'.
Proof.
  pose HeliosIACR2018.
  intros. unfold iff. refine (conj _ _).  intros. unfold M2F_eq in *. destruct m' in *.
  destruct m in *. simpl in *. apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H. destruct H. apply andb_true_iff in H. destruct H.
  apply F_bool_eq_corr in H. apply F_bool_eq_corr in H0. apply F_bool_eq_corr in H1.
  apply F_bool_eq_corr in H2. rewrite H. rewrite H0. rewrite H1. rewrite H2. trivial.
  (*case 2*)
  intros. unfold M2F_eq. do 3 rewrite andb_true_iff. split. split. split.
  apply F_bool_eq_corr. rewrite H. trivial. apply F_bool_eq_corr. rewrite H. trivial.
  apply F_bool_eq_corr. rewrite H. trivial. apply F_bool_eq_corr. rewrite H. trivial.
Qed.

Lemma Mneq :
  forall m m' : M2F,
  M2F_eq m m' = false -> m <> m'.
Proof.
  pose HeliosIACR2018. intros. intros. unfold not.
  intros. rewrite <- Meq in H0. apply (eq_true_false_abs (M2F_eq m m')).
  apply H0. apply H. 
Qed.

Lemma deterPrem :
  forall m b : M2F,
  M2F_deter m <> 0 ->
  M2F_isPermutation b ->
  M2F_deter (M2F_mult b m) <> 0.
Proof.
  pose HeliosIACR2018.
  intros. unfold M2F_isPermutation in H0.
  apply orb_true_iff in H0. destruct H0.
  (* case 1 *)  
  apply Meq in H0. rewrite H0.
  unfold M2F_mult. unfold M2F_deter in *. simpl. replace ((1 * r00 m + 0 * r10 m) * (0 * r01 m + 1 * r11 m) -
(1 * r01 m + 0 * r11 m) * (0 * r00 m + 1 * r10 m)) with (r00 m * r11 m - r01 m * r10 m).
  apply H. field; auto.
  (* case 2 *)
  apply Meq in H0. rewrite H0.
  unfold M2F_mult. unfold M2F_deter in *. simpl. replace ((0 * r00 m + 1 * r10 m) * (1 * r01 m + 0 * r11 m) -
  (0 * r01 m + 1 * r11 m) * (1 * r00 m + 0 * r10 m)) with 
  (r01 m * r10 m - r00 m * r11 m). unfold not in *. intros. 
  apply H. remember (r00 m * r11 m ) as a. remember (r01 m * r10 m) as c.
  apply (shift) in H1. rewrite H1. field; auto. field; auto.
Qed.

Lemma M2F_one1 : 
  forall m :M2F,
  M2F_mult m M2F_id = m.
Proof.
  intros. unfold M2F_id. destruct m. unfold M2F_mult. simpl.
  apply M2F_eqBreakDown. split. simpl. field; auto.
  split. simpl. field; auto. split. simpl. field; auto.
  simpl. field; auto.
Qed.

Lemma M2F_one2 : 
  forall m :M2F,
  M2F_mult M2F_id m = m.
Proof.
  intros. unfold M2F_id. destruct m. unfold M2F_mult. simpl.
  apply M2F_eqBreakDown. split. simpl. field; auto.
  split. simpl. field; auto. split. simpl. field; auto.
  simpl. field; auto.
Qed.

Lemma sub_M2F_assoc :
  forall a b c d : F,
  a + b + c + d = 
  a + c + b + d.
Proof.
  intros. field; auto.
Qed.

Lemma M2F_assoc :
  forall a b c :M2F,
  M2F_mult (M2F_mult a b) c = M2F_mult a (M2F_mult b c).
Proof.
  intros. unfold M2F_mult. destruct a. destruct b. destruct c.
  simpl. apply M2F_eqBreakDown. split. simpl. field; auto.
  split. simpl. field; auto. split. simpl. field; auto.
  simpl. field; auto.
Qed.

Lemma M2F_col_con1 :
  forall (a b : V2F),
  M2F_col1 (M2F_col_con a b) = a.
Proof.
  intros. unfold M2F_col_con. unfold M2F_col1. simpl.
  destruct a. simpl. trivial.
Qed.

Lemma M2F_col_con2 :
  forall (a b : V2F),
  M2F_col2 (M2F_col_con a b) = b.
Proof.
  intros. unfold M2F_col_con. unfold M2F_col2. simpl.
  destruct b. simpl. trivial.
Qed.
  
(* Lemmas on addational crypto stuff *)
Lemma permExp :
  forall m : M2F,
  forall e : (V2G*V2G),
  M2F_isPermutation m ->
  if M2F_eq m M2F_id then 
    e = (V2G_Tprod (ciphExp e (M2F_col1 m)),V2G_Tprod (ciphExp e (M2F_col2 m))) else
   (e.2, e.1) = (V2G_Tprod (ciphExp e (M2F_col1 m)),V2G_Tprod (ciphExp e (M2F_col2 m))).
Proof.
  pose HeliosIACR2018.
  intros. case_eq (M2F_eq m M2F_id). intros. unfold M2F_col1. unfold ciphExp. simpl.
  apply Meq in H0. rewrite H0. unfold M2F_id. simpl. do 2 rewrite V2G_Sexp_id. 
  do 2 rewrite V2G_Sexp_ann. unfold V2G_Tprod. simpl. rewrite V2G_One. rewrite V2G_Comm.
  rewrite V2G_One. destruct e. trivial.
  (*Case 2 *)
  intros. unfold M2F_isPermutation in H. unfold M2F_id in H0. rewrite H0 in H.
  simpl in *. apply Meq in H. rewrite H. unfold M2F_col1. unfold M2F_col2.
  unfold ciphExp. simpl. do 2 rewrite V2G_Sexp_id. do 2 rewrite V2G_Sexp_ann.
  unfold V2G_Tprod. simpl. rewrite V2G_One. rewrite V2G_Comm. rewrite V2G_One. trivial.
Qed.

Lemma permPresId :
  forall m : M2F,
  M2F_isPermutation m ->
  V2F_eq (M2F_CVmult m V2F_one) V2F_one.
Proof.
  intros. unfold M2F_isPermutation in H. apply orb_true_iff in H.
  destruct H. apply Meq in H. rewrite H. unfold M2F_CVmult.
  unfold V2F_inProd. simpl. auto.
  apply Meq in H. rewrite H. unfold M2F_CVmult.
  unfold V2F_inProd. simpl. auto.
Qed.

Lemma prodPres1 :
  forall B : M2F,
  forall U : V2F,
 V2F_inProd (M2F_col1 B) U * V2F_inProd (M2F_col2 B) U =
   V2F_prod (M2F_VCmult U B).
Proof.
  intros. unfold V2F_inProd. unfold V2F_prod. unfold M2F_VCmult.
  unfold V2F_inProd. simpl. field; auto.
Qed.

Lemma prodPres2 :
  forall B : M2F,
  forall U : V2F,
 V2F_inProd (M2F_row1 B) U * V2F_inProd (M2F_row2 B) U =
   V2F_prod (M2F_CVmult B U).
Proof.
  intros. unfold V2F_inProd. unfold V2F_prod. unfold M2F_CVmult.
  unfold V2F_inProd. simpl. field; auto.
Qed.

Lemma permPresProd : 
  forall m : M2F,
  forall u : V2F,
  M2F_isPermutation m ->
  V2F_inProd (M2F_col1 m) u * V2F_inProd (M2F_col2 m) u = V2F_prod u.
Proof.
  intros. unfold M2F_isPermutation in H. apply orb_true_iff in H.
  destruct H. apply Meq in H. rewrite H. unfold V2F_inProd.
  unfold V2F_prod. simpl. field; auto. 
  apply Meq in H. rewrite H. unfold V2F_inProd.
  unfold V2F_prod. simpl. field; auto. 
Qed. 

Lemma V2F_eq_true :
  forall a b : V2F,
  V2F_eq a b = true <-> a = b.
Proof.
  pose HeliosIACR2018.
  intros. unfold V2F_eq. rewrite andb_true_iff. 
  do 2 rewrite F_bool_eq_corr. unfold iff.
  refine (conj _ _). intros. destruct H. destruct a.
  destruct b. simpl in *. rewrite H. rewrite H0.
  trivial. intros. split. rewrite H. trivial.
  rewrite H. trivial.
Qed.

Lemma V2F_eq_false :
  forall a b : V2F,
  V2F_eq a b = false -> a <> b.
Proof.
  pose HeliosIACR2018.
  intros. unfold V2F_eq in H. apply andb_false_iff in H. 
  destruct H. apply F_bool_neq_corr in H. unfold not in *. 
  intros.  rewrite H0 in H. apply H. trivial.
  apply F_bool_neq_corr in H. unfold not in *.
  intros. rewrite H0 in H. apply H. trivial.
Qed.

Lemma V2F_add_product :
  forall (hs : V2G)(m1 m2 : V2F), 
  V2G_prod (V2G_Pexp hs m2)
  o V2G_prod (V2G_Pexp hs m1) =
  V2G_prod
  (V2G_Pexp hs
     (V2F_add m1 m2)).
Proof.
  pose HeliosIACR2018.
  intros. unfold V2G_prod. unfold V2F_add. 
  unfold V2G_Pexp. simpl. symmetry. 
  replace (r1 m3 + r1 m4) with (r1 m4 + r1 m3).
  replace (r2 m3 + r2 m4) with (r2 m4 + r2 m3).
  do 2 rewrite mod_dist_Fadd. do 2 rewrite <- dot_assoc.
  apply left_cancel. do 2 rewrite dot_assoc.
  apply right_cancel. apply comm. field; auto.
  field; auto.
Qed.

Lemma V2F_neg_inv :
  forall (hs : V2G)(m : V2F),
  V2G_prod(V2G_Pexp hs (V2F_neg m)) = 
    - V2G_prod (V2G_Pexp hs m).
Proof.
  pose HeliosIACR2018.
  intros. unfold V2F_neg. unfold V2G_Pexp.
  unfold V2G_prod. simpl. rewrite <- neg_eq.
  rewrite <- neg_eq. apply inv_dist.
Qed.

Lemma V2F_add_zero :
  forall a : V2F,
  V2F_add a V2F_zero = a.
Proof.
  intros. unfold V2F_zero. unfold V2F_add. 
  apply V2F_eqBreakDown. simpl. split. field; auto. field; auto.
Qed.

Lemma V2F_neg_corr :
  forall a : V2F,
  V2F_add a (V2F_neg a) = V2F_zero.
Proof.
  intros. unfold V2F_neg. unfold V2F_add. apply V2F_eqBreakDown.
  simpl. split. field; auto. field; auto.
Qed.

Lemma V2F_comm :
  forall a b : V2F,
  V2F_add a b = V2F_add b a.
Proof.
  intros. unfold V2F_add. apply V2F_eqBreakDown. simpl. split.
  field; auto. field; auto.
Qed.

Lemma V2F_add_ass :
  forall a b c : V2F,
  V2F_add (V2F_add a b) c = V2F_add a (V2F_add b c).
Proof.
  intros. unfold V2F_neg. unfold V2F_add.  apply V2F_eqBreakDown.
  simpl. split. field; auto. field; auto.
Qed.

Lemma V2F_add_neg :
  forall a b : V2F,
  V2F_add (V2F_add a b) (V2F_neg b) = a.
Proof.
  intros. rewrite V2F_add_ass. rewrite V2F_neg_corr.
  rewrite V2F_add_zero. trivial.
Qed.

Lemma V2F_add_neg2 :
  forall a b : V2F,
  V2F_add (V2F_add a (V2F_neg b)) b = a.
Proof.
  intros. rewrite V2F_add_ass. replace (V2F_add (V2F_neg b) b) with
  (V2F_add b (V2F_neg b)). rewrite V2F_neg_corr. rewrite V2F_add_zero.
  trivial. apply V2F_comm.
Qed.

Lemma column_eq_1 :
  forall A B : M2F,
  M2F_col1 (M2F_mult B A) = M2F_CVmult B (M2F_col1 A).
Proof.
  intros. unfold M2F_mult. unfold M2F_CVmult. unfold M2F_col1.
  unfold V2F_inProd. unfold M2F_row1. simpl. trivial.
Qed. 

Lemma column_eq_2 :
  forall A B : M2F,
  M2F_col2 (M2F_mult B A) = M2F_CVmult B (M2F_col2 A).
Proof.
  intros. unfold M2F_mult. unfold M2F_CVmult. unfold M2F_col1.
  unfold V2F_inProd. unfold M2F_row1. simpl. trivial.
Qed. 

Lemma row_eq_1 :
  forall A : M2F,
  forall rTil : V2F,
  r1 (M2F_VCmult rTil A) = V2F_inProd rTil (M2F_col1 A).
Proof.
  intros. unfold M2F_VCmult. unfold V2F_inProd. simpl.
  field; auto.
Qed.

Lemma row_eq_2 :
  forall A : M2F,
  forall rTil : V2F,
  r2 (M2F_VCmult rTil A) = V2F_inProd rTil (M2F_col2 A).
Proof.
  intros. unfold M2F_VCmult. unfold V2F_inProd. simpl.
  field; auto.
Qed.

Lemma M2F_CVmult_breakdown :
  forall A : M2F,
  forall B : V2F,
  M2F_CVmult A B = V2F_add (V2F_scale (M2F_col1 A) (r1 B))
     (V2F_scale (M2F_col2 A) (r2 B)).
Proof.
  intros. unfold M2F_CVmult. unfold V2F_scale. unfold V2F_inProd. unfold V2F_add.
  simpl. trivial. 
Qed.


Lemma ColumnCommute1 :
  forall U A : M2F,
  (M2F_CVmult U (M2F_col1 A)) = M2F_col1 (M2F_mult U A).
Proof.
  intros. unfold M2F_CVmult. unfold M2F_mult. 
  unfold V2F_inProd. unfold M2F_col1. simpl. trivial.
Qed.

Lemma ColumnCommute2 :
  forall U A : M2F,
  (M2F_CVmult U (M2F_col2 A)) = M2F_col2 (M2F_mult U A).
Proof.
  intros. unfold M2F_CVmult. unfold M2F_mult. 
  unfold V2F_inProd. unfold M2F_col1. simpl. trivial.
Qed.

Lemma inProdPres :
  forall A : M2F,  
  forall rTil : V2F,
  V2F_inProd (M2F_col1 A) rTil +
   V2F_inProd (M2F_col2 A) rTil =
  V2F_inProd (M2F_VCmult rTil A) V2F_one.
Proof.
  intros. unfold M2F_VCmult. unfold V2F_inProd. simpl.
  field; auto.
Qed. 

Lemma scalInProd :
  forall A : M2F,  
  forall U rTil : V2F,
  V2F_inProd (M2F_VCmult rTil (M2F_Fscal A U)) V2F_one =
  V2F_inProd (M2F_VCmult rTil A) U.
Proof.
  intros. unfold M2F_Fscal. unfold M2F_VCmult. unfold V2F_inProd.
  simpl. field; auto.
Qed.

Lemma inProdComb :
  forall A : M2F,  
  forall U rTil : V2F,
  V2F_inProd (M2F_col1 (M2F_Fscal A U)) rTil +
   V2F_inProd (M2F_col2 (M2F_Fscal A U)) rTil =
  V2F_inProd (M2F_VCmult rTil A) U.
Proof.
  intros. rewrite inProdPres. apply scalInProd.
Qed.

Lemma invComm :
 forall U : M2F,
 M2F_deter U <> 0 ->
 M2F_mult (M2F_inv U) U = M2F_mult U (M2F_inv U).
Proof.
  intros. rewrite invCorrect. apply H. unfold M2F_inv. unfold M2F_mult.
  simpl. unfold M2F_deter. apply M2F_eqBreakDown. simpl. split.
  field; auto. split. field; auto. split. field; auto. field; auto.
Qed.

End Matrices.
