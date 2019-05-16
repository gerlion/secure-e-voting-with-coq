Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import groups.
Require Import matrices.
Require Import HeliosIACR2018.
Require Import sigmaprotocol.
Require Import basicSigmas.
Require Import List.
Require Import Field.
Require Import cryptoprim.
Require Coq.Classes.RelationClasses.

Section Wikstrom.
Delimit Scope Wikstrom with F.
Open Scope Wikstrom.

(** We attempt to prove the correctness of Wikstrom's mix net latter step
    We take as a building block the DLog sigma from Helios
*)

(** 
  We will briefly describe the constrains

  wikS := M*M*M*(M^n)*(M^n)*(M^n)*(R^n)*(M^n)*(M^n)*(M^n)*(M^n)
         g pk h  h_i   c_i  ^c_i   u_i   a_i  b_i    a'_i  b'_i
  wikW := R*  R*      R*    R*   (R^n)     *(R^n)
         rBar rTilde rPrime rHat rHatPrime  u'

  where rBar = sum r_i where ^c_i = h^r_i h_pi_i
  where rTilde = cross product of u and r
  where rPrime = cross product of u and r
  where rHat = realted to ^c_n with r^

  wikC := M*M*M*M*(M^n)
  wikR :=   R    *R  *R * R  * R^N * R^N
           w_1 w_2 w_3 w_4     w'     w^
  wikE := E
  wikT := R*R*R*R*(R^n)*(R^n)

*)

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

(* We begin by creating short hand for notation *)
(* We denote vectors as Q*Q and matricies as (Q*Q)*(Q*Q), for some Q *)
(*  were Q.i.j is the value of matrix in the ith row and jth coloumn *)


(* Relationships for the primary statments *)

Definition relComEPC (h :G)(hs : V2G)(c : G) (*Stament*)
              (m1 m2 : V2F)(r1 r2 : F) :=  (*Witness *)
  m1 <> m2 /\
  c = (EPC h hs m1 r1) /\ c = (EPC h hs m2 r2). 

Definition relComPC (h :G)(h1 : G)(c : G) (*Stament*)
              (m1 m2 : F)(r1 r2 : F) :=  (*Witness *)
  m1 <> m2 /\
  c = (PC h h1 m1 r1) /\ c = (PC h h1 m2 r2). 
  
(* The commitment is to a permutation *)
Definition relPi (h :G)(hs : V2G)(c : V2G) (*Statment *)
  (m : M2F)(r : V2F) :=       (*Witness*)
    M2F_isPermutation m
     /\ c = (com h hs m r).


(* Defination of shuffling *) (* e2_i = e1_p_i * r_p_i *)
Definition relReEnc(g pk : G)(e e' : (V2G*V2G))(m : M2F)
  (r : V2F) :=
  let e'' := ciphMatrix e' m in
  let r'' := M2F_CVmult m r in 
    IsReEnc g pk e.1 e''.1 (r1 r'')  /\ IsReEnc g pk e.2 e''.2 (r2 r'').

(* Relationships from the underlying sigma protocol *)
(* the basic extractor pulls the following values:
  rBar (F) rDim (F) rTil (F) rStar (F) rHat (R*F) u' (R*F)
  which statisfy the following relations *)

Definition SigStatment1 (c : V2G)(h :G)(hs : V2G)(rBar : F) :=
  V2G_prod c = EPC h hs V2F_one rBar.

Definition SigStatment2 (c : V2G)(h :G)(hs : V2G)(u u' : V2F)(rTil : F) :=
  V2G_prod (V2G_Pexp c u) = EPC h hs u' rTil.

Definition SigStatment3 (g pk : G)(e e' : (V2G*V2G))(u u' : V2F)(rStar : F) :=
  V2G_Tprod (ciphExp e' u')  = 
    V2G_mult (Enc g pk rStar Gone) (V2G_Tprod (ciphExp e u)).

Definition SigStatment4 (h h1 : G)(cHat : V2G)(u' rHat : V2F) :=
  (m1 cHat) = PC h h1 (r1 u') (r1 rHat) /\ (m2 cHat) = PC h (m1 cHat) (r2 u') (r2 rHat).

Definition SigStatment5 (h h1 :G)(cHat : V2G)(u : V2F)(rDim : F) :=
  m2 cHat = PC h h1 (V2F_prod u) rDim.

Lemma temp :
 forall (a : V2F)(B : M2F),
 M2F_CVmult (M2F_Fscal B a) V2F_one =
 (M2F_CVmult B a).
Proof.
  pose HeliosIACR2018. Add Field vs_field : Ffield.
 intros. unfold V2F_one. unfold M2F_Fscal. unfold M2F_CVmult.
 unfold V2F_inProd. simpl. apply V2F_eqBreakDown. simpl. split.
  field; auto. field; auto.
Qed.

(* Stuff about EPC *)
Lemma EPCProduct0 :
  forall(h : G)(hs : V2G),
  forall(B : M2F),
  forall(r r' : F),
  EPC h hs (M2F_col1 B) r o EPC h hs (M2F_col2 B) r' =
  EPC h hs (M2F_CVmult B V2F_one)(r + r').
Proof.
  pose HeliosIACR2018. 
  intros. unfold EPC. unfold M2F_CVmult. unfold V2F_inProd.
  unfold V2G_Pexp. unfold V2G_prod. simpl. 
  rewrite <- dot_assoc. do 3 rewrite mod_dist_Fadd.
  do 2 rewrite <- dot_assoc. apply left_cancel. 
  rewrite comm. do 2 rewrite <- dot_assoc. rewrite comm.
  rewrite <- dot_assoc. apply left_cancel. 
  rewrite <- dot_assoc. rewrite comm. do 2 rewrite <- dot_assoc.
  replace (r00 B * 1) with (r00 B). apply left_cancel.
  rewrite comm. rewrite <- dot_assoc.
  replace (r01 B * 1) with (r01 B). apply left_cancel.
  replace (r10 B * 1) with (r10 B). rewrite comm.
  replace (r11 B * 1) with (r11 B). trivial.
  field; auto. field; auto. field; auto. field; auto.
Qed.


Theorem EPCProduct1 :
  forall(h : G)(hs : V2G),
  forall(U' A : M2F),
  forall(rTil : V2F),
    EPC h hs
        (V2F_add
           (V2F_scale (M2F_col1 U')
              (r1 (M2F_col1 A)))
           (V2F_scale (M2F_col2 U')
              (r2 (M2F_col1 A))))
        (V2F_inProd rTil (M2F_col1 A)) = 
   (EPC h hs (V2F_scale (M2F_col1 U')(r1 (M2F_col1 A))) ((r1 rTil) * (r1 (M2F_col1 A)))) o
   (EPC h hs (V2F_scale (M2F_col2 U')(r2 (M2F_col1 A))) ((r2 rTil) * (r2 (M2F_col1 A)))).
Proof.
  pose HeliosIACR2018.
  intros. cbn. unfold V2F_scale. unfold V2F_add. unfold EPC. simpl. 
  unfold V2F_inProd. rewrite mod_dist_Fadd. cbn.  
  do 2 rewrite <- dot_assoc. apply left_cancel. symmetry. rewrite comm. 
  rewrite <- dot_assoc. apply left_cancel. unfold V2G_prod.
  unfold V2G_Pexp. simpl. rewrite mod_dist_Fadd. rewrite mod_dist_Fadd.
  remember (m1 hs ^ (r01 U' * r10 A)) as a.
  remember (m2 hs ^ (r10 U' * r00 A)) as d. rewrite comm. 
  do 2 rewrite <- dot_assoc. apply left_cancel. rewrite comm.
  rewrite <- dot_assoc. apply left_cancel. 
  rewrite comm. trivial.
Qed.

Theorem EPCProduct2 :
  forall(h : G)(hs : V2G),
  forall(U' A : M2F),
  forall(rTil : V2F),
    EPC h hs
        (V2F_add
           (V2F_scale (M2F_col1 U')
              (r1 (M2F_col2 A)))
           (V2F_scale (M2F_col2 U')
              (r2 (M2F_col2 A))))
        (V2F_inProd rTil (M2F_col2 A)) = 
   (EPC h hs (V2F_scale (M2F_col1 U')(r1 (M2F_col2 A))) ((r1 rTil) * (r1 (M2F_col2 A)))) o
   (EPC h hs (V2F_scale (M2F_col2 U')(r2 (M2F_col2 A))) ((r2 rTil) * (r2 (M2F_col2 A)))).
Proof.
  pose HeliosIACR2018.
  intros. cbn. unfold V2F_scale. unfold V2F_add. unfold EPC. simpl. 
  unfold V2F_inProd. rewrite mod_dist_Fadd. cbn.  
  do 2 rewrite <- dot_assoc. apply left_cancel. symmetry. rewrite comm. 
  rewrite <- dot_assoc. apply left_cancel. unfold V2G_prod.
  unfold V2G_Pexp. simpl. do 2 rewrite mod_dist_Fadd. 
  remember (m1 hs ^ (r01 U' * r11 A)) as a.
  remember (m2 hs ^ (r10 U' * r01 A)) as d.  rewrite comm. 
  do 2 rewrite <- dot_assoc. apply left_cancel. rewrite comm.
  rewrite <- dot_assoc. apply left_cancel. rewrite comm. trivial.
Qed.

Theorem EPCSum :
  forall c : V2G,
  forall U : M2F,
  forall b : V2F,
  V2G_prod (V2G_Pexp c (M2F_col1 U)) ^ r1 b o 
  V2G_prod (V2G_Pexp c (M2F_col2 U)) ^ r2 b = 
    (m1 c)^(V2F_inProd (M2F_row1 U) b) o 
    (m2 c)^(V2F_inProd (M2F_row2 U) b) .
Proof.
  pose HeliosIACR2018. intros. unfold V2G_Pexp. 
  unfold V2G_prod. unfold V2F_inProd. simpl. 
  do 2 rewrite mod_dist_Gdot. symmetry. 
  do 2 rewrite mod_dist_Fadd. do 4 rewrite mod_dist_FMul2.
  remember ((m1 c ^ r00 U) ^ r1 b) as a.
  remember ((m2 c ^ r11 U) ^ r2 b) as d.
  remember ((m2 c ^ r10 U) ^ r1 b) as e.
  do 2 rewrite dot_assoc. 
  apply right_cancel. do 2 rewrite <- dot_assoc.
  apply left_cancel. apply comm. 
Qed.

Theorem EPCProd :
  forall c : V2G,
  forall U : M2F,
  forall b : V2F,
 m1 c ^ V2F_inProd (M2F_row1 U) b o
 m2 c ^ V2F_inProd (M2F_row2 U) b = 
 V2G_prod (V2G_Pexp c (M2F_CVmult U b)).
Proof.
  intros. unfold M2F_CVmult. unfold V2G_Pexp. 
  unfold V2F_inProd. unfold V2G_prod. simpl. trivial.
Qed. 

Lemma EPCExpPair :
  forall (h : G)(hs : V2G),
  forall (A : M2F)(b c : V2F),
 V2G_Pexp (com h hs A b) c = com h hs (M2F_Fscal A c) (V2F_mult b c).
Proof.
  pose HeliosIACR2018.
  intros. unfold M2F_Fscal. unfold V2F_mult. unfold V2G_Pexp. unfold com.
  unfold M2F_col1. unfold M2F_col2. unfold EPC. unfold V2G_prod. 
  unfold V2G_Pexp.  simpl. do 4 rewrite mod_dist_Gdot. 
  do 6 rewrite <- mod_dist_Fmul. apply V2G_eqBreakDown. simpl. split.
  replace (r1 c * r1 b) with (r1 b * r1 c). apply left_cancel.
  replace (r1 c * r00 A) with (r00 A * r1 c). apply left_cancel.
  replace (r1 c * r10 A) with (r10 A * r1 c). intuition.
  field; auto. field; auto. field; auto.
  replace (r2 c * r2 b) with (r2 b * r2 c). apply left_cancel.
  replace (r2 c * r01 A) with (r01 A * r2 c). apply left_cancel.
  replace (r2 c * r11 A) with (r11 A * r2 c). intuition.
  field; auto. field; auto. field; auto.
Qed.

Lemma prodComEqEPC :
  forall (h : G)(hs : V2G),
  forall (B A : M2F)(rTil : V2F),
  V2G_prod (com h hs B (M2F_VCmult rTil A)) =
  EPC h hs (M2F_CVmult B V2F_one)
  (V2F_inProd (M2F_col1 A) rTil +
   V2F_inProd (M2F_col2 A) rTil).
Proof.
  intros. unfold com. unfold V2G_prod. simpl. apply EPCProduct0.
Qed.

Lemma multVCmult :
  forall (A : M2F)(rTil U : V2F),
  V2F_mult (M2F_VCmult rTil A) U = 
    M2F_VCmult rTil (M2F_Fscal A U). 
Proof.
  intros. unfold M2F_col1. unfold M2F_VCmult. unfold V2F_mult. simpl.
  unfold V2F_inProd. unfold M2F_col1. unfold M2F_col2. simpl.
 apply V2F_eqBreakDown. simpl. split. field; auto. field; auto.
Qed.

Lemma Theorem1ProofOfRestrictedShuffle :
  forall m : M2F,
  forall v : V2F,
  r01 m * r2 v * r11 m * r2 v - r1 v * r2 v <> 0 ->
  r01 m * r2 v * r10 m * r1 v - r1 v * r2 v <> 0 ->
  r00 m * r1 v * r11 m * r2 v - r1 v * r2 v <> 0 ->
  r00 m * r1 v * r10 m * r1 v - r1 v * r2 v <> 0 ->
  ((r00 m <> 0) -> (r01 m <> 0) -> V2F_inProd (M2F_row1 m) v * V2F_inProd (M2F_row2 m) v - V2F_prod v <> 0) ->
  ((r10 m <> 0) -> (r11 m <> 0) -> V2F_inProd (M2F_row1 m) v * V2F_inProd (M2F_row2 m) v - V2F_prod v <> 0) ->  
  Finv (r2 v * r1 v)  <> 0 ->
  M2F_isPermutation m = false -> (
  V2F_eq (M2F_CVmult m V2F_one) V2F_one &&
  Fbool_eq (V2F_inProd (M2F_row1 m) v * V2F_inProd (M2F_row2 m) v - V2F_prod v) 
  0) = false.
Proof.
  pose HeliosIACR2018. destruct v. intros m v case_1 case_2 case_3 case_4 case_5 case_6. 
  intros. 
  destruct v. apply andb_false_iff.  case_eq (V2F_eq (M2F_CVmult m V2F_one) V2F_one). intros.
  right. intros. rewrite F_bool_neq_corr. unfold not. intros.
  apply V2F_eq_true in H1. unfold M2F_CVmult in H1. unfold V2F_inProd in H1.
  unfold V2F_one in H1. simpl in *. replace (r00 m * 1 + r01 m * 1) with
  (r00 m + r01 m) in H1 by field; auto. replace (r10 m * 1 + r11 m * 1) with 
  (r10 m + r11 m) in H1 by field; auto.  unfold M2F_isPermutation in H0. 
  apply orb_false_iff in H0. destruct H0. apply Mneq in H0. apply Mneq in H3.
   unfold not in *.
  (* If any row m_i were the zero vector, then f would be the zero
   polynomial. *)
  case_eq (V2F_eq (M2F_row1 m) V2F_zero || V2F_eq (M2F_row2 m) 
  V2F_zero). intros. apply orb_true_iff in H4. destruct H4.
  apply V2F_eq_true in H4. rewrite H4 in H2. unfold V2F_inProd in H2.
  simpl in *. replace ((0 * r1 + 0 * r2) *
   (r10 m * r1 + r11 m * r2)) with 0 in H2 by field; auto.
  unfold V2F_prod in H2. simpl in *. apply H.
  rewrite <- H2. field; auto.  apply V2F_eq_true in H4. 
  rewrite H4 in H2. unfold V2F_inProd in H2.
  simpl in *. replace ((0 * r1 + 0 * r2) *
   (r10 m * r1 + r11 m * r2)) with 0 in H2 by field; auto.
  unfold V2F_prod in H2. simpl in *. apply H.
  rewrite <- H2. field; auto. 
  (* no rows zero, . If all rows of M were non-zero, and not contains more then one
  none-zero element *) 
  intros. apply orb_false_iff in H4. destruct H4. case_eq ((Fbool_eq (r00 m) Fzero 
   || Fbool_eq (r01 m) Fzero) && (Fbool_eq (r10 m) Fzero || Fbool_eq (r11 m) Fzero)).
  unfold V2F_inProd in H2. unfold V2F_prod in H2. simpl in *. intros. apply andb_true_iff in H6. 
  destruct H6. apply orb_true_iff in H6. apply orb_true_iff in H7.  destruct H6. 
  destruct H7. (* case 1 *) apply F_bool_eq_corr in H6. apply F_bool_eq_corr in H7.
  rewrite H6 in H2. rewrite H7 in H2. replace ((0 * r1 + r01 m * r2) * 
  (0 * r1 + r11 m * r2)) with (r01 m * r2 * r11 m * r2) in H2. apply case_1. 
  rewrite <- H2. trivial. field; auto. (* case 2 *) apply F_bool_eq_corr in H6. 
  apply F_bool_eq_corr in H7. rewrite H6 in H2. rewrite H7 in H2. replace (
  (0 * r1 + r01 m * r2) * (r10 m * r1 + 0 * r2)) with (r01 m * r2 * r10 m * r1) in H2.
  apply case_2. rewrite <- H2. trivial. field; auto. (* case 3 *) apply F_bool_eq_corr 
  in H6. destruct H7. apply F_bool_eq_corr in H7. rewrite H6 in H2. rewrite H7 in H2.
  replace ((r00 m * r1 + 0 * r2) * (0 * r1 + r11 m * r2)) with (r00 m * r1 * r11 m * r2) in H2.
  apply case_3. rewrite <- H2. trivial. field; auto. (* case 4 *) 
  apply F_bool_eq_corr in H7. rewrite H6 in H2. rewrite H7 in H2.
  replace ((r00 m * r1 + 0 * r2) * (r10 m * r1 + 0 * r2)) with (r00 m * r1 * r10 m * r1) in H2.
  apply case_4. rewrite <- H2. trivial. field; auto.
 
  (* but some row m_i contained more than one non-zero element, then f would contain
   a factor of the form j\u2208J mi,jxj with |J| \u2265 2 and mi,j = 0 for j \u2208 J *)
  intros. apply andb_false_iff in H6. destruct H6. apply orb_false_iff in H6.
  destruct H6. assert (r00 m <> 0). unfold not.  rewrite <- F_bool_neq_corr.
  apply H6. assert (r01 m <> 0). unfold not. rewrite <- F_bool_neq_corr. apply H7.
  unfold V2F_inProd in H2. simpl in *. apply case_5; auto. apply orb_false_iff in H6.
  destruct H6. assert (r10 m <> 0). unfold not.  rewrite <- F_bool_neq_corr.
  apply H6. assert (r11 m <> 0). unfold not. rewrite <- F_bool_neq_corr. apply H7. 
  apply case_6; auto.
  
  (*Trivial case *)
  intros. left. trivial. 
Qed.

Lemma logicLemma :
  forall a b: bool,
  a = false \/ b = false ->
  a = true ->
  b = false.
Proof.
  intros. destruct H. congruence. apply H.
Qed.

Lemma prodLemma :
  forall a b: V2F,
  V2F_prod a <> V2F_prod b -> a <> b.
Proof.
  intros. unfold not in *. intros. rewrite H0 in H. apply H. trivial.
Qed.

(* Now prove the sub theorem about matrix commitments
    we annotate with line numbers which correspond to 
    equation on page 11 of the paper *)
Theorem matrixCommitment :
  (*Commitment parameters and matrix commitments *)
  forall(h : G)(hs : V2G)(c cHat : V2G),
  (*for all primary challenges *)  
  forall(U : M2F),
  (*for all secondary witnesses *)
  forall(rBar rDim rTil rStar : V2F)(rHat U' : M2F),
  let A := (M2F_inv U) in
  let B := (M2F_mult U' A) in
  let m := B in
  let v := (M2F_col1 U) in
  (*Schwartz Zippel Lemma assumpations *)
  r01 m * r2 v * r11 m * r2 v - r1 v * r2 v <> 0 ->
  r01 m * r2 v * r10 m * r1 v - r1 v * r2 v <> 0 ->
  r00 m * r1 v * r11 m * r2 v - r1 v * r2 v <> 0 ->
  r00 m * r1 v * r10 m * r1 v - r1 v * r2 v <> 0 ->
  ((r00 m <> 0) -> (r01 m <> 0) -> V2F_inProd (M2F_row1 m) v * V2F_inProd (M2F_row2 m) v - V2F_prod v <> 0) ->
  ((r10 m <> 0) -> (r11 m <> 0) -> V2F_inProd (M2F_row1 m) v * V2F_inProd (M2F_row2 m) v - V2F_prod v <> 0) ->  
  Finv (r2 v * r1 v)  <> 0 ->
  (* and back to normal *)  
  M2F_deter U <> 0 ->
  SigStatment1 c h hs (r1 rBar)  ->
  SigStatment1 c h hs (r2 rBar)  ->
  SigStatment2 c h hs (M2F_col1 U) (M2F_col1 U') (r1 rTil) ->
  SigStatment2 c h hs (M2F_col2 U) (M2F_col2 U') (r2 rTil) ->
  SigStatment4 h (m1 hs) cHat (M2F_col1 U') (M2F_col1 rHat) ->
  SigStatment5 h (m1 hs) cHat (M2F_col1 U) (r1 rDim) ->
    relPi h hs c B (M2F_VCmult rTil A)  \/ 
  ((exists (c: G)(m1 m2 : V2F)(r1 r2 : F),
     relComEPC h hs c m1 m2 r1 r2) \/ (
      exists (c: G)(m m' : F)(r1 r2 : F),
     relComPC h (m1 hs) c m m' r1 r2)).  
Proof.
  pose HeliosIACR2018. destruct v.
  intros h hs c cHat U rBar rDim rTil rStar rHat U' A B m v case_1 case_2 case_3 case_4 case_5 case_6 case_7. 
  intros.  
  case_eq (Fbool_eq (V2F_prod (M2F_col1 U)) (V2F_prod (M2F_col1 U'))). intros.
  (* We show that the (rTil A) opens the commitment to b *)
  assert (c = com h hs B (M2F_VCmult rTil A)).
  unfold com. unfold B. rewrite column_eq_1. rewrite column_eq_2.
  rewrite row_eq_1. rewrite row_eq_2. (* line 8 *)
  do 2 rewrite M2F_CVmult_breakdown. (* line 7 *)
  rewrite EPCProduct1. rewrite EPCProduct2. (* line 6 *)
  do 4 rewrite EPCExp. (* line 5 *)
  rewrite <- H2. rewrite <- H3. (* line 4 *)
  rewrite EPCSum. remember (m1 c ^ V2F_inProd (M2F_row1 U) (M2F_col1 A)
      o m2 c ^ V2F_inProd (M2F_row2 U) (M2F_col1 A)) as a. 
   rewrite EPCSum. rewrite EPCProd. rewrite Heqa. rewrite EPCProd.
  (* line 1 *)
  rewrite ColumnCommute1. rewrite ColumnCommute2.
  rewrite invCorrect. apply H. unfold M2F_id. 
  unfold V2G_Pexp. unfold V2G_prod. simpl. 
  do 2 rewrite mod_id. do 2 rewrite mod_ann. 
  rewrite one_right. rewrite one_left. destruct c. trivial.
  (* We show that everything works is a permutation *)
  intros. case_eq (M2F_isPermutation B).
  intros. left. unfold relPi. split. apply H8. apply H7.  
  (* Finished proof for when B is a permutation *)
  intros. right. left. case_eq (V2F_eq (M2F_CVmult B V2F_one) V2F_one).
  (* Opening when M1 eq 1 *)
  intros. apply (Theorem1ProofOfRestrictedShuffle(B)(M2F_col1 U)) in H8; auto.
  apply andb_false_iff in H8. apply logicLemma in H8.
  pose (M2F_CVmult B (M2F_col1 U)) as u''.
  exists (V2G_prod (V2G_Pexp c (M2F_col1 U))).
  exists (M2F_col1 U'). exists u''. exists (r1 rTil).
  exists (V2F_inProd (M2F_VCmult rTil A) (M2F_col1 U)).
  unfold relComEPC. split.
  (* U'1 <> u'' *)
  unfold u''.  apply prodLemma. apply F_bool_neq_corr in H8. unfold not in H8.
  unfold not. intros. apply H8. rewrite prodPres2. rewrite <- H10. 
  apply F_bool_eq_corr in H6. rewrite H6.
  remember (V2F_prod (M2F_col1 U')) as a. field; auto.
  (* opens to 1 *)
  split. unfold SigStatment2 in H2. rewrite H2. intuition.
  (* opens to 2 *)
  unfold u''. rewrite H7. rewrite EPCExpPair. rewrite multVCmult.
  rewrite prodComEqEPC. rewrite temp. rewrite inProdComb. intuition.
  apply H9.
  (* Opening when M1 neq 1 *)
  intros. pose (M2F_CVmult B V2F_one) as u''.
  exists (V2G_prod c). exists V2F_one. exists u''.
  exists (r1 rBar). exists (V2F_sum (M2F_VCmult rTil A)).
  unfold M2F_VCmult. unfold V2F_sum. unfold relComEPC. simpl. 
  (*  u'' neq 1 *)
  split.  unfold u''. apply V2F_eq_false in H9.
  unfold not.  intros. symmetry in H10. unfold not in H9.
  apply H9 in H10. apply H10.
  (* opens to 1 *)
  split. unfold SigStatment1 in H0. rewrite H0.
  unfold EPC. unfold V2G_Pexp. unfold V2G_prod. simpl.
  apply left_cancel. intuition.
  (* opens to 2 *)
  rewrite H7. rewrite prodComEqEPC. unfold u''.
  intuition.
  (* Case if prod U neq prod U' *)
  intros. right. right. exists (m2 cHat). exists (V2F_prod (M2F_col1 U)).
  exists (V2F_prod (M2F_col1 U')). exists (r1 rDim). 
  exists ((r2 (M2F_col1 rHat)) + ((r1 (M2F_col1 rHat))*(r2 (M2F_col1 U')))).
  unfold relComPC. split.
  (* prod u'' neq prod u *)
  apply F_bool_neq_corr in H6. apply H6.
  (* opens to 1 *)
  split. unfold SigStatment5 in H5. apply H5. 
  (* opens to 2 *)
  unfold SigStatment4 in H4. destruct H4.
  rewrite H7. rewrite H4. unfold PC. unfold V2F_prod. simpl.
  rewrite mod_dist_Fadd. rewrite <- dot_assoc. apply left_cancel.
  rewrite mod_dist_Gdot. do 2 rewrite <-  mod_dist_Fmul.
  replace (r10 U'* r00 rHat) with (r00 rHat * r10 U').
  replace (r10 U' * r00 U') with (r00 U' * r10 U'). intuition.
  field; auto. field; auto.
Qed.

Lemma temp2 :
  forall (e' : (V2G*V2G))(U' : M2F)(a : V2F),
  V2G_Tprod (ciphExp e' (M2F_CVmult U' a)) = 
   V2G_mult (V2G_Sexp (V2G_Tprod (ciphExp e' (M2F_col1 U'))) (r1 a))
    (V2G_Sexp (V2G_Tprod (ciphExp e' (M2F_col2 U'))) (r2 a)).
Proof.
  pose HeliosIACR2018.
  intros. unfold ciphExp. unfold V2G_Tprod.  simpl. unfold V2G_Sexp. 
  unfold V2G_mult.  simpl. unfold V2F_inProd. simpl. 
  apply V2G_eqBreakDown. simpl. split. 
  (* Case 1 *)
  do 2 rewrite mod_dist_Gdot.
  replace ((m1 e'.1 ^ r00 U') ^ r1 a) with (m1 e'.1 ^ (r00 U' * r1 a)).
  replace ((m1 e'.2 ^ r10 U') ^ r1 a) with (m1 e'.2 ^ (r10 U' * r1 a)).
  replace ((m1 e'.1 ^ r01 U') ^ r2 a) with (m1 e'.1 ^ (r01 U' * r2 a)).
  replace ((m1 e'.2 ^ r11 U') ^ r2 a) with (m1 e'.2 ^ (r11 U' * r2 a)).
  remember (r00 U' * r1 a) as b.
  remember (r10 U' * r1 a) as c.
  remember (r01 U' * r2 a) as d.
  remember (r11 U' * r2 a) as e. symmetry. rewrite dot_assoc.
  replace (m1 e'.2 ^ (c + e)) with (m1 e'.2 ^ c o m1 e'.2 ^ e).
  rewrite dot_assoc. apply right_cancel. rewrite comm. rewrite dot_assoc.
  apply right_cancel. rewrite mod_dist_Fadd. rewrite comm. trivial.
  rewrite mod_dist_Fadd. trivial. apply mod_dist_FMul2.
  apply mod_dist_FMul2. apply mod_dist_FMul2. apply mod_dist_FMul2.
  (* Case 2 *)
  do 2 rewrite mod_dist_Gdot.
  replace ((m2 e'.1 ^ r00 U') ^ r1 a) with (m2 e'.1 ^ (r00 U' * r1 a)).
  replace ((m2 e'.2 ^ r10 U') ^ r1 a) with (m2 e'.2 ^ (r10 U' * r1 a)).
  replace ((m2 e'.1 ^ r01 U') ^ r2 a) with (m2 e'.1 ^ (r01 U' * r2 a)).
  replace ((m2 e'.2 ^ r11 U') ^ r2 a) with (m2 e'.2 ^ (r11 U' * r2 a)).
  remember (r00 U' * r1 a) as b.
  remember (r10 U' * r1 a) as c.
  remember (r01 U' * r2 a) as d.
  remember (r11 U' * r2 a) as e. symmetry. rewrite dot_assoc.
  replace (m2 e'.2 ^ (c + e)) with (m2 e'.2 ^ c o m2 e'.2 ^ e).
  rewrite dot_assoc. apply right_cancel. rewrite comm. rewrite dot_assoc.
  apply right_cancel. rewrite mod_dist_Fadd. rewrite comm. trivial.
  rewrite mod_dist_Fadd. trivial. apply mod_dist_FMul2.
  apply mod_dist_FMul2. apply mod_dist_FMul2. apply mod_dist_FMul2.
Qed.

Lemma temp4 :
  forall (a b c d : V2G),
  V2G_mult (V2G_mult a b) (V2G_mult c d) = 
  V2G_mult (V2G_mult a c) (V2G_mult b d).
Proof.
  pose HeliosIACR2018.
  intros. unfold V2G_mult. apply V2G_eqBreakDown.  simpl. split.
  do 2 rewrite -> dot_assoc. apply right_cancel. rewrite comm.
  rewrite dot_assoc. apply right_cancel. apply comm.
  do 2 rewrite -> dot_assoc. apply right_cancel. rewrite comm.
  rewrite dot_assoc. apply right_cancel. apply comm.
Qed.

Lemma temp5_1 :
  forall (e : (V2G*V2G)),
  e.1 = V2G_Tprod (ciphExp e (M2F_col1 M2F_id)).
Proof.
  pose HeliosIACR2018.
  intros. unfold M2F_id. unfold ciphExp. unfold V2G_Tprod.
  unfold V2G_Sexp. unfold V2G_mult. apply V2G_eqBreakDown. simpl. split.
  rewrite mod_id. rewrite mod_ann. rewrite one_right. trivial.
  rewrite mod_id. rewrite mod_ann. rewrite one_right. trivial.
Qed.

Lemma temp5_2 :
  forall (e : (V2G*V2G)),
  e.2 = V2G_Tprod (ciphExp e (M2F_col2 M2F_id)).
Proof.
  pose HeliosIACR2018.
  intros. unfold M2F_id. unfold ciphExp. unfold V2G_Tprod.
  unfold V2G_Sexp. unfold V2G_mult. apply V2G_eqBreakDown. simpl. split.
  rewrite mod_id. rewrite mod_ann. rewrite one_left. trivial.
  rewrite mod_id. rewrite mod_ann. rewrite one_left. trivial.
Qed.

Lemma temp7_1 :
  forall (U U' B : M2F)(rStar : V2F),
  M2F_isPermutation B ->
  M2F_deter U <> 0 ->
  M2F_deter U' <> 0 ->
  U' = M2F_mult B U ->
  (V2F_inProd rStar (M2F_col1 (M2F_inv U))) = (V2F_inProd (M2F_row1 (M2F_mult U' (M2F_inv U)))
     (M2F_VCmult rStar (M2F_inv U'))).
Proof.
  intros. unfold M2F_inv. unfold M2F_mult. unfold V2F_inProd.
  simpl. unfold V2F_inProd. simpl. unfold M2F_isPermutation in H.
  apply orb_true_iff in H. destruct H.
  (* case 1 *)
  apply Meq in H. rewrite H in H2. rewrite H2. simpl. unfold M2F_mult.
  unfold M2F_deter. simpl. field; auto.
  (* case 2 *)
  apply Meq in H. rewrite H in H2. rewrite H2. simpl. unfold M2F_mult.
  unfold M2F_deter. simpl. field; auto.  split.  rewrite H2 in H1.
  unfold M2F_mult in H1. unfold M2F_deter in H1. simpl in *.
  replace (r10 U * r01 U - r11 U * r00 U) with ((0 * r00 U + 1 * r10 U) 
  * (1 * r01 U + 0 * r11 U) - (0 * r01 U + 1 * r11 U) * 
  (1 * r00 U + 0 * r10 U)). apply H1. field; auto.  apply H0.
Qed.

Lemma temp7_2 :
  forall (U U' B : M2F)(rStar : V2F),
  M2F_isPermutation B ->
  M2F_deter U <> 0 ->
  M2F_deter U' <> 0 ->
  U' = M2F_mult B U ->
  (V2F_inProd rStar (M2F_col2 (M2F_inv U))) = (V2F_inProd (M2F_row2 (M2F_mult U' (M2F_inv U)))
     (M2F_VCmult rStar (M2F_inv U'))).
Proof.
  intros. unfold M2F_inv. unfold M2F_mult. unfold V2F_inProd.
  simpl. unfold V2F_inProd. simpl. unfold M2F_isPermutation in H.
  apply orb_true_iff in H. destruct H.
  (* case 1 *)
  apply Meq in H. rewrite H in H2. rewrite H2. simpl. unfold M2F_mult.
  unfold M2F_deter. simpl. field; auto.
  (* case 2 *)
  apply Meq in H. rewrite H in H2. rewrite H2. simpl. unfold M2F_mult.
  unfold M2F_deter. simpl. field; auto.  split.  rewrite H2 in H1.
  unfold M2F_mult in H1. unfold M2F_deter in H1. simpl in *.
  replace (r10 U * r01 U - r11 U * r00 U) with ((0 * r00 U + 1 * r10 U) 
  * (1 * r01 U + 0 * r11 U) - (0 * r01 U + 1 * r11 U) * 
  (1 * r00 U + 0 * r10 U)). apply H1. field; auto.  apply H0.
Qed.

Lemma temp8 :
  forall (g pk m :G)(r r' : F),
  r = r' -> Enc g pk r m = Enc g pk r' m.
Proof.
  intros. rewrite H. trivial.
Qed.

Lemma temp9 :
  forall (B U : M2F)(A : V2F),
  M2F_CVmult (M2F_mult B U) A =
  M2F_CVmult B (M2F_CVmult U A).
Proof.
  intros. unfold M2F_CVmult. unfold M2F_mult. unfold V2F_inProd. simpl.
  apply V2F_eqBreakDown. simpl. split. field; auto.  field; auto.
Qed.

Theorem extendedExtractor :
  (*for all statments *)
  forall(g pk : G)(e e' : (V2G*V2G)), (* Forall keys and ciphertexts *)
  forall(h : G)(hs : V2G)(c cHat1 cHat2 : V2G), (*Commitment parameters and matrix commitmnets *)
  (*for all primary challenges *)  
  forall(U : M2F),
  (*for all secondary witnesses *)
  forall(rBar rDim rTil rStar : V2F)(rHat U' : M2F),
  (* such that the secondary witnesses hold *)
  M2F_deter U <> 0 ->
  SigStatment1 c h hs (r1 rBar)  ->
  SigStatment1 c h hs (r2 rBar)  ->
  SigStatment2 c h hs (M2F_col1 U) (M2F_col1 U') (r1 rTil) ->
  SigStatment2 c h hs (M2F_col2 U) (M2F_col2 U') (r2 rTil) ->
  SigStatment3 g pk e e' (M2F_col1 U) (M2F_col1 U') (r1 rStar) ->
  SigStatment3 g pk e e' (M2F_col2 U) (M2F_col2 U') (r2 rStar) ->
  SigStatment4 h (m1 hs) cHat1 (M2F_col1 U') (M2F_col1 rHat) ->
  SigStatment4 h (m1 hs) cHat2 (M2F_col2 U') (M2F_col2 rHat) ->
  SigStatment5 h (m1 hs) cHat1 (M2F_col1 U) (r1 rDim) ->
  SigStatment5 h (m1 hs) cHat2 (M2F_col2 U) (r2 rDim) ->
  (* Schwarz-Zippel *)
  let A := M2F_inv U in 
  let B := (M2F_mult U' A) in 
  let m := B in
  let v := (M2F_col1 U) in
  (*Schwartz Zippel Lemma assumpations *)
  r01 m * r2 v * r11 m * r2 v - r1 v * r2 v <> 0 ->
  r01 m * r2 v * r10 m * r1 v - r1 v * r2 v <> 0 ->
  r00 m * r1 v * r11 m * r2 v - r1 v * r2 v <> 0 ->
  r00 m * r1 v * r10 m * r1 v - r1 v * r2 v <> 0 ->
  ((r00 m <> 0) -> (r01 m <> 0) -> V2F_inProd (M2F_row1 m) v * V2F_inProd (M2F_row2 m) v - V2F_prod v <> 0) ->
  ((r10 m <> 0) -> (r11 m <> 0) -> V2F_inProd (M2F_row1 m) v * V2F_inProd (M2F_row2 m) v - V2F_prod v <> 0) ->  
  Finv (r2 v * r1 v)  <> 0 ->

  (* either the commitments are broken or we are happy *)
  (exists (r r' : V2F)(m : M2F), 
    (relReEnc g pk e e' m r /\ relPi h hs c m r'))  \/ 
  ((exists (c: G)(m1 m2 : V2F)(r1 r2 : F),
     relComEPC h hs c m1 m2 r1 r2) \/ (
      exists (c: G)(m m' : F)(r1 r2 : F),
     relComPC h (m1 hs) c m m' r1 r2)).
Proof.
  pose HeliosIACR2018.
  intros g pk e e' h hs c cHat1 cHat2 U rBar rDim rTil rStar rHat U'. intros. assert (relPi h hs c B (M2F_VCmult rTil A) 
     \/ ((exists (c: G)(m1 m2 : V2F)(r1 r2 : F),
     relComEPC h hs c m1 m2 r1 r2) \/ (
      exists (c: G)(m m' : F)(r1 r2 : F),
     relComPC h (m1 hs) c m m' r1 r2))).
    apply (matrixCommitment h hs c cHat1 U rBar rDim rTil rStar rHat U'); 
    auto. destruct H17. 
    (* Case where the commitment is to a matrix *)
    assert (M2F_eq U' (M2F_mult B U)). unfold B. unfold A.
    rewrite M2F_assoc. rewrite invComm. apply H. rewrite invCorrect.
    apply H. rewrite M2F_one1. apply Meq. trivial.
    (* and U' = B U *)
    unfold SigStatment3 in H4. unfold SigStatment3 in H5.
    intros. left. exists (M2F_VCmult rStar (M2F_inv U')). exists (M2F_VCmult rTil A).
    exists B.  split.
    + unfold relReEnc. unfold IsReEnc. unfold ReEnc. unfold ciphMatrix.
    simpl. split. 
    (*Proving ciphertext in position one equal *)
    replace (M2F_col1 B) with (M2F_CVmult B (M2F_col1 (M2F_id))).
    replace (M2F_col1 M2F_id) with (M2F_CVmult U (M2F_col1 A)). (*line 9*)
    rewrite <- temp9. apply Meq in H18. rewrite <- H18.
    rewrite temp2. rewrite H4. rewrite H5. rewrite V2G_Sexp_dis_dot.
    rewrite V2G_Sexp_dis_dot. rewrite temp4. rewrite <- temp2.
    rewrite ColumnCommute1. unfold A. rewrite invCorrect. apply H.
    fold A. rewrite <- temp5_1. rewrite V2G_Comm. apply V2G_Mul. split.
    trivial. do 2 rewrite EncOfOneRasiedToB. rewrite EncIsHomomorphic. 
    rewrite one_right. fold (V2F_inProd rStar (M2F_col1 A)).
    unfold B. unfold A. apply temp8. apply (temp7_1 U U' B rStar).
    apply H17. apply H. rewrite H18. apply deterPrem. apply H.
    apply H17. apply H18. unfold A. rewrite <- column_eq_1.
    rewrite invCorrect. apply H. trivial. rewrite <- column_eq_1.
    rewrite M2F_one1. trivial.
    (*Proving ciphertext in position two equal *)
    replace (M2F_col2 B) with (M2F_CVmult B (M2F_col2 (M2F_id))).
    replace (M2F_col2 M2F_id) with (M2F_CVmult U (M2F_col2 A)). (*line 9*)
    rewrite <- temp9. apply Meq in H18. rewrite <- H18.
    rewrite temp2. rewrite H4. rewrite H5. rewrite V2G_Sexp_dis_dot.
    rewrite V2G_Sexp_dis_dot. rewrite temp4. rewrite <- temp2.
    rewrite ColumnCommute2. unfold A. rewrite invCorrect. apply H.
    fold A. rewrite <- temp5_2. rewrite V2G_Comm. apply V2G_Mul. split.
    trivial. do 2 rewrite EncOfOneRasiedToB. rewrite EncIsHomomorphic. 
    rewrite one_right. fold (V2F_inProd rStar (M2F_col2 A)).
    unfold B. unfold A. apply temp8. apply (temp7_2 U U' B rStar).
    apply H17. apply H. rewrite H18. apply deterPrem. apply H.
    apply H17. apply H18. unfold A. rewrite <- column_eq_2.
    rewrite invCorrect. apply H. trivial. rewrite <- column_eq_2.
    rewrite M2F_one1. trivial.
    + apply H17.
    (* trivial case where commitment isn't to a matrix *)
    + right. apply H17.
Qed.


(*Having given the proof for the extended extractor we now crate
  the sigma protocol for the base statments. *)
Definition WikstromSigma :=
  genAndSigmaProtocol F (genAndSigmaProtocol F dLogForm dLogForm) (u'Form).

Definition WikstromStatment (g pk h : G)(hs c cHat : V2G)(u : V2F)(e e' : (V2G*V2G)) :=
  ((h, V2G_prod c o - (V2G_prod hs)),(h, (m2 cHat) o - (m1 hs) ^ (V2F_prod u)),
  ((g, pk, h, hs, e'),(V2G_prod (V2G_Pexp c u), (V2G_Tprod (ciphExp e u)),cHat))).

Lemma WikstromExtractor :
  forall (g pk h : G)(hs c cHat : V2G)(u : V2F)(e e' : (V2G*V2G))(w : (F*F*(V2F*F*F*V2F))),
  let Sig := WikstromSigma in
  let s := (WikstromStatment g pk h hs c cHat u e e') in 
  Sigma.Rel F Sig s w ->
   V2G_prod c o - V2G_prod hs = h ^ w.1.1 /\
    m2 cHat o - (m1 hs) ^ (V2F_prod u) = h ^ w.1.2 /\
  V2G_prod (V2G_Pexp c u) = EPC h hs w.2.1.1.1 w.2.1.1.2  /\
  V2G_Tprod (ciphExp e u) =  V2G_mult (V2G_Tprod 
    (ciphExp e' w.2.1.1.1)) (Enc g pk w.2.1.2 Gone) /\
  m1 cHat = PC h (m1 hs) (r1 w.2.1.1.1) (r1 w.2.2) /\
  m2 cHat = PC h (m1 cHat) (r2 w.2.1.1.1) (r2 w.2.2).
Proof.
  pose HeliosIACR2018.
  intros. unfold Sig in *. unfold WikstromSigma in *.
  unfold parSigmaProtocol in *. simpl in *. unfold dLog in *.
  simpl in *. apply andb_true_iff in H. destruct H. 
  apply andb_true_iff in H. destruct H. 
  apply bool_eq_corr in H.  apply bool_eq_corr in H1.
  split. apply H. split. apply H1. unfold u'_Rel in H0.
  simpl in H0. apply andb_true_iff in H0. destruct H0. 
  apply andb_true_iff in H0. destruct H0. 
  apply andb_true_iff in H0. destruct H0. 
  apply bool_eq_corr in H0. split. apply H0.
  apply V2Geq in H4. split. apply H4. split.
  apply bool_eq_corr in H3. apply H3.
  apply bool_eq_corr in H2. apply H2.
Qed.

Lemma WikstromSigmaCorr :
  SigmaProtocol F WikstromSigma.
Proof.
  intros. unfold WikstromSigma. apply andGenCorr. apply andGenCorr.
  apply dLogSigma. apply dLogSigma. trivial. apply u'Sigma.
  trivial.
Qed.
 
Theorem SigmaImpliesAllGood :
  (*for all statments *)
  forall(g pk : G)(e e' : (V2G*V2G)), (* Forall keys and ciphertexts *)
  forall(h : G)(hs : V2G)(c : V2G), (*Commitment parameters and matrix commitmnets *)
  (* For primary challenges *)
  forall(U : M2F),
  M2F_deter U <> 0 ->
  forall(cHat1 cHat2 : V2G),
  let Sig := WikstromSigma in
  let s1 := WikstromStatment g pk h hs c cHat1 (M2F_col1 U) e e' in
  let s2 := WikstromStatment g pk h hs c cHat2 (M2F_col2 U) e e' in
  (* Sigma protocols accept *)
  forall (c1 c2 : Sigma.C F Sig)(e1 e2 e3 e4 : F)
  (t1 t2 t3 t4 : Sigma.T F Sig),
  Sigma.V1 F Sig (s1,c1,e1,t1) = true ->
  Sigma.V1 F Sig (s1,c1,e2,t2) = true ->
  Sigma.V1 F Sig (s2,c2,e3,t3) = true ->
  Sigma.V1 F Sig (s2,c2,e4,t4) = true ->
  Sigma.disjoint F Sig e1 e2 ->
  Sigma.disjoint F Sig e3 e4 ->

  let w1 := (Sigma.extractor F Sig t1 t2 e1 e2) in
  let w2 := (Sigma.extractor F Sig t3 t4 e3 e4) in
  let U' := (M2F_col_con w1.2.1.1.1 w2.2.1.1.1) in

  exists (rBar rDim rTil rStar : V2F)(rHat : M2F),
  SigStatment1 c h hs (r1 rBar) /\
  SigStatment1 c h hs (r2 rBar) /\
  SigStatment2 c h hs (M2F_col1 U) (M2F_col1 U') (r1 rTil) /\
  SigStatment2 c h hs (M2F_col2 U) (M2F_col2 U') (r2 rTil) /\
  SigStatment3 g pk e e' (M2F_col1 U) (M2F_col1 U') (r1 rStar) /\
  SigStatment3 g pk e e' (M2F_col2 U) (M2F_col2 U') (r2 rStar) /\
  SigStatment4 h (m1 hs) cHat1 (M2F_col1 U') (M2F_col1 rHat) /\
  SigStatment4 h (m1 hs) cHat2 (M2F_col2 U') (M2F_col2 rHat) /\
  SigStatment5 h (m1 hs) cHat1 (M2F_col1 U) (r1 rDim) /\
  SigStatment5 h (m1 hs) cHat2 (M2F_col2 U) (r2 rDim).
Proof.
  pose HeliosIACR2018.
  intros. assert (Sigma.Rel F Sig s1 (Sigma.extractor F Sig t1 t2 e1 e2)).
  eapply special_soundness with (c:=c1); auto. 
  apply WikstromSigmaCorr. 
  assert (Sigma.Rel F Sig s2 (Sigma.extractor F Sig t3 t4 e3 e4)).
  eapply special_soundness with (c:=c2); auto. apply WikstromSigmaCorr.
  fold w1. fold w2. 
  exists (Build_V2F w1.1.1 w2.1.1). exists (Build_V2F w1.1.2 w2.1.2).
  exists (Build_V2F w1.2.1.1.2 w2.2.1.1.2).
  exists (Build_V2F (Finv w1.2.1.2) (Finv w2.2.1.2)).
  exists (M2F_col_con w1.2.2 w2.2.2).
  unfold SigStatment1. unfold SigStatment2. unfold SigStatment3.
  unfold SigStatment4. unfold SigStatment5.
  apply WikstromExtractor in H6. apply WikstromExtractor in H7.
  destruct H6. destruct H7. split. 
  unfold EPC. simpl. apply b_equal. rewrite V2G_One_exp. apply H6.
  split. unfold EPC. apply b_equal. rewrite V2G_One_exp. apply H7.
  unfold PC. destruct H8. destruct H9. destruct H10.
  destruct H12. destruct H11. destruct H14. destruct H15. destruct H13. 
  (*Proving cases form u' *)
  split. simpl. rewrite M2F_col_con1. apply H10. split. 
  rewrite M2F_col_con2. apply H11. split. rewrite M2F_col_con1.
  rewrite ciphEqual. symmetry. apply H12. split. 
  rewrite ciphEqual. symmetry. apply H14. split. split.
  rewrite H13. unfold PC. intuition. rewrite H17. unfold PC. intuition.
  split.  split.  rewrite H15. unfold PC. intuition.  rewrite H16. 
  unfold PC. intuition. split. simpl. cbn in H8. rewrite <- H8. rewrite comm.
  rewrite dot_assoc. symmetry. apply comm_inv_wac.  
  simpl. cbn in H9. rewrite <- H9. rewrite comm.
  rewrite dot_assoc. symmetry. apply comm_inv_wac. 
Qed.

Theorem TheMixnetIsSecure :
  (*for all statments *)
  forall(g pk : G)(e e' : (V2G*V2G)), (* Forall keys and ciphertexts *)
  forall(h : G)(hs : V2G)(c : V2G), (*Commitment parameters and matrix commitmnets *)
  (* For primary challenges *)
  forall(U : M2F),
  M2F_deter U <> 0 ->
  forall(cHat1 cHat2 : V2G),
  let Sig := WikstromSigma in
  let s1 := WikstromStatment g pk h hs c cHat1 (M2F_col1 U) e e' in
  let s2 := WikstromStatment g pk h hs c cHat2 (M2F_col2 U) e e' in
  (* Sigma protocols accept *)
  forall (c1 c2 : Sigma.C F Sig)(e1 e2 e3 e4 : F)
    (t1 t2 t3 t4 : Sigma.T F Sig),
  Sigma.V1 F Sig (s1,c1,e1,t1) = true ->
  Sigma.V1 F Sig (s1,c1,e2,t2) = true ->
  Sigma.V1 F Sig (s2,c2,e3,t3) = true ->
  Sigma.V1 F Sig (s2,c2,e4,t4) = true ->
  Sigma.disjoint F Sig e1 e2 ->
  Sigma.disjoint F Sig e3 e4 ->

  let w1 := (Sigma.extractor F Sig t1 t2 e1 e2) in
  let w2 := (Sigma.extractor F Sig t3 t4 e3 e4) in
  let U' := (M2F_col_con w1.2.1.1.1 w2.2.1.1.1) in
  let A := M2F_inv U in 
  let B := (M2F_mult U' A) in 
  let m := B in
  let v := (M2F_col1 U) in
  (*Schwartz Zippel Lemma assumpations *)
  r01 m * r2 v * r11 m * r2 v - r1 v * r2 v <> 0 ->
  r01 m * r2 v * r10 m * r1 v - r1 v * r2 v <> 0 ->
  r00 m * r1 v * r11 m * r2 v - r1 v * r2 v <> 0 ->
  r00 m * r1 v * r10 m * r1 v - r1 v * r2 v <> 0 ->
  ((r00 m <> 0) -> (r01 m <> 0) -> V2F_inProd (M2F_row1 m) v * V2F_inProd (M2F_row2 m) v - V2F_prod v <> 0) ->
  ((r10 m <> 0) -> (r11 m <> 0) -> V2F_inProd (M2F_row1 m) v * V2F_inProd (M2F_row2 m) v - V2F_prod v <> 0) ->  
  Finv (r2 v * r1 v)  <> 0 -> 

  (exists (r r' : V2F)(m : M2F), 
    (relReEnc g pk e e' m r /\ relPi h hs c m r'))  \/ 
  ((exists (c: G)(m1 m2 : V2F)(r1 r2 : F),
     relComEPC h hs c m1 m2 r1 r2) \/ (
      exists (c: G)(m m' : F)(r1 r2 : F),
     relComPC h (m1 hs) c m m' r1 r2)).
Proof.
  intros. assert (exists (rBar rDim rTil rStar : V2F)(rHat : M2F),
  SigStatment1 c h hs (r1 rBar) /\
  SigStatment1 c h hs (r2 rBar) /\
  SigStatment2 c h hs (M2F_col1 U) (M2F_col1 U') (r1 rTil) /\
  SigStatment2 c h hs (M2F_col2 U) (M2F_col2 U') (r2 rTil) /\
  SigStatment3 g pk e e' (M2F_col1 U) (M2F_col1 U') (r1 rStar) /\
  SigStatment3 g pk e e' (M2F_col2 U) (M2F_col2 U') (r2 rStar) /\
  SigStatment4 h (m1 hs) cHat1 (M2F_col1 U') (M2F_col1 rHat) /\
  SigStatment4 h (m1 hs) cHat2 (M2F_col2 U') (M2F_col2 rHat) /\
  SigStatment5 h (m1 hs) cHat1 (M2F_col1 U) (r1 rDim) /\
  SigStatment5 h (m1 hs) cHat2 (M2F_col2 U) (r2 rDim)).
  apply (SigmaImpliesAllGood g pk e e' h hs c U H cHat1 cHat2 
    c1 c2 e1 e2 e3 e4 t1 t2 t3 t4); auto. do 6 destruct H13.
  destruct H14. destruct H15. destruct H16. destruct H17. destruct H18.
  destruct H19. destruct H20. destruct H21.
  apply (extendedExtractor g pk e e' h hs c cHat1 cHat2 U
          x x0 x1 x2 x3 U'); auto.
Qed.

End Wikstrom.


