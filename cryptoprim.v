Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import groups.
Require Import Coq.Lists.List.
Require Import Quote.
Require Import Ring.
Require Import Field. 
Require Import Field_theory.
Require Import HeliosIACR2018.
Require Import matrices.

Section CryptoPrimatives.
Delimit Scope CryptoPrimatives with F.
Open Scope CryptoPrimatives.

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

Definition dLog (s :G*G)(w : F) := 
  let g     := s.1 in
  let gtox  := s.2 in 
  Gbool_eq gtox (g^w).

(** Given a generator g, public key h, randomness r, and message m,
   produce the ElGamal ciphertext *)
Definition enc (g h :G)(r : F)(m :G): (G*G):=
  (g^r,h^r o m).

(*Definition of matrix returning vector not product *)
Definition Enc (g h :G)(r : F)(m :G): V2G :=
  V2G_cons (g^r,h^r o m).

Definition dec (g pk : G)(c : (G*G))(privateKey :F) : G :=
  c.2 o Ginv (c.1^privateKey).

Definition mult (a b :(G))  :=  a o b.

Definition multCiph (a b :(G*G))  :=  (a.1 o b.1, a.2 o b.2).

(*We now prove that ElGamal is homomorphic *)
Lemma encIsHomomorphic : forall g h : G, forall r1 r2 : F, 
  forall m1 m2 : G,
  multCiph (enc g h r1 m1) (enc g h r2 m2) = enc g h (r1+r2) (m1 o m2).
Proof.
  pose HeliosIACR2018. intros. unfold multCiph. unfold enc. simpl.
  do 2 rewrite mod_dist_Fadd. do 2 rewrite dot_assoc. 
  apply injective_projections. simpl. trivial. simpl. apply right_cancel.
  remember (h ^ r1) as a. remember (h ^ r2) as b. rewrite <- dot_assoc.
  replace (m1 o b) with (b o m1) by apply comm. rewrite dot_assoc. trivial.
Qed.

Lemma EncIsHomomorphic : forall g h : G, forall r1 r2 : F,
  forall m1 m2 : G,
  V2G_mult (Enc g h r1 m1) (Enc g h r2 m2) = Enc g h (r1+r2) (m1 o m2).
Proof.
  pose HeliosIACR2018. intros. unfold V2G_mult. unfold Enc. 
  unfold V2G_cons. apply V2G_eqBreakDown. simpl.  split.
  rewrite mod_dist_Fadd. trivial.
  do 2 rewrite dot_assoc. apply right_cancel. rewrite comm. 
  rewrite dot_assoc. apply right_cancel. rewrite mod_dist_Fadd.
  rewrite comm. trivial.
Qed.

Lemma elGamalCorrect :
  forall (g y :G)(m : G)(r : F)(x :F),
    g^x = y ->
  dec g y (enc g y r m) x = m.
Proof.
  pose HeliosIACR2018.  Add Field vs_field : Ffield.
  intros. unfold dec. unfold enc. simpl. rewrite <- H. 
  rewrite neg_eq. 
  replace ((g ^ x) ^ r) with (g ^ (x*r)) by apply mod_dist_FMul2.
  replace ((g ^ r) ^ (Finv x)) with ( g ^ ( r *Finv x)) by apply mod_dist_FMul2.
  rewrite comm. rewrite dot_assoc. rewrite <- mod_dist_Fadd. replace (r * Finv x + x * r) with 0.
  rewrite mod_ann. apply one_left. field; auto.
Qed.

Definition EncVec (g pk : G)(m : V2G)(r : V2F) : V2G*V2G:=
  (V2G_cons (enc g pk (r1 r) (m1 m)), V2G_cons(enc g pk (r2 r) (m2 m))).

Definition ReEnc (g pk : G)(c1 : V2G)(r : F) : V2G :=
  V2G_mult c1 (Enc g pk r Gone). 

Definition ReEncVec (g pk : G)(c1 : (V2G*V2G))(r : V2F) : ((V2G)*(V2G)) :=
  (V2G_mult c1.1 (Enc g pk (r1 r) Gone),
   V2G_mult c1.2 (Enc g pk (r2 r) Gone)). 

(* definiation of c2 being a re-encryption of c1 *)
Definition IsReEnc (g pk : G)(c1 c2 : V2G)(r : F) : Prop :=
  c2 = ReEnc g pk c1 r.

(* Given a list of ciphertexts produce the product *)
Definition Prod (cs : list (G*G)) : (G*G) :=
  let zero := Gone in
  fold_left multCiph cs (zero,zero). 

(* Given a list of group element produce the product *)
Definition ProdSingle (cs : list (G)) : (G) :=
  let zero := Gone in
  fold_left mult cs zero. 

(* We admit evidence of knowledge of randomness or 
  secret key but in two different definitions *)

(* Given a generator g, public key h, ciphertext c,
  and message m *)
Definition decryptsTo (g h :G)(c : (G*G))(m : G) :=
  exists (r : F), enc g h r m = c.

(* Given a generator g, public key h, ciphertext c,
  and message m *)
Definition decryptsTo2 (g h :G)(c : (G*G))(m : G) :=
  exists (x : F), g^x = h /\ (c.2 o - m) = c.1^x.

(* Given a generator g, public key h, ciphertext c,
  c is an encryption of zero or one *)
Definition decryptsToOneOrZero (g h :G)(c : (G*G)) : Prop  :=
  let zero := Gone in
  let one := g in
  decryptsTo g h c zero \/ decryptsTo g h c one.

Definition PC (h: G)(h1 : G)(m : F)(r: F) : G :=
  h^r o h1^m.

Definition EPC (h :G)(hs : V2G)(m : V2F)(r : F) : G :=
  h^r o V2G_prod (V2G_Pexp hs m).

(*the definiation of a commitment commitment to a matrix *) 
Definition com (h :G)(hs : V2G)(m : M2F)(r : V2F) : V2G :=
  Build_V2G(EPC h hs (M2F_col1 m) (r1 r))(EPC h hs (M2F_col2 m) (r2 r)).

Lemma EncInv : 
  forall (g pk : G)(a : F),
    Enc g pk (Finv a) Gone = V2G_inv (Enc g pk a Gone).
Proof.
  pose HeliosIACR2018.
  intros. unfold Enc. do 2 rewrite one_right. unfold V2G_inv.
  unfold V2G_cons. simpl. do 2 rewrite <- neg_eq. trivial.
Qed.
  
Lemma EncOfOneRasiedToB :
  forall (g pk : G)(a b : F),
  (V2G_Sexp (Enc g pk a Gone) b) = Enc g pk (a*b) Gone.
Proof.
  pose HeliosIACR2018.
  intros. unfold Enc. unfold V2G_Sexp. unfold V2G_cons.
  apply V2G_eqBreakDown. simpl. split. rewrite mod_dist_FMul2.
  trivial. rewrite mod_dist_Gdot. rewrite mod_mone.
  apply right_cancel. rewrite mod_dist_FMul2. trivial.
Qed.

Lemma Sexp_dist :
  forall (e : (V2G*V2G))(u : V2F)(a : F),
  V2G_Sexp (V2G_Tprod (ciphExp e u)) a = 
    V2G_Tprod (ciphExp e (V2F_scale u a)).
Proof.
  pose HeliosIACR2018.
  intros.  unfold V2F_scale.  unfold ciphExp.  unfold V2G_Sexp. 
  unfold V2G_Tprod. unfold V2G_mult. simpl. apply V2G_eqBreakDown.
  simpl. split. do 2 rewrite mod_dist_FMul2. rewrite mod_dist_Gdot.
  trivial. do 2 rewrite mod_dist_FMul2. rewrite mod_dist_Gdot.
  trivial.
Qed.

Lemma V2F_scale_neg :
  forall (a : V2F)(e : F),
  V2F_scale a (Finv e) = V2F_neg (V2F_scale a e).
Proof.
  pose HeliosIACR2018.
  intros. unfold V2F_scale. unfold V2F_neg. apply V2F_eqBreakDown.
  simpl. split. field; auto. field; auto.
Qed.

Lemma V2G_mult_Tprod_ciphExp :
  forall (e : V2G*V2G)(a b : V2F),
  V2G_mult (V2G_Tprod (ciphExp e a))
  (V2G_Tprod (ciphExp e b)) = V2G_Tprod (ciphExp e (V2F_add a b)).
Proof.
    pose HeliosIACR2018.
  intros. unfold ciphExp. unfold V2G_Sexp. unfold V2G_Tprod. simpl.
  unfold V2G_mult. simpl. apply V2G_eqBreakDown. simpl. split.
  do 2 rewrite mod_dist_Fadd. do 2 rewrite dot_assoc. apply right_cancel.
  do 2 rewrite <- dot_assoc. apply left_cancel. apply comm.
  do 2 rewrite mod_dist_Fadd. do 2 rewrite dot_assoc. apply right_cancel.
  do 2 rewrite <- dot_assoc. apply left_cancel. apply comm.
Qed.

Lemma ciphExp_neg : 
  forall (e : V2G*V2G)(a : V2F),
  V2G_Tprod (ciphExp e (V2F_neg a)) = V2G_inv (V2G_Tprod (ciphExp e a)).
Proof.
  pose HeliosIACR2018.
  intros. unfold V2F_neg. unfold ciphExp. unfold V2G_Tprod. 
  unfold V2G_inv. unfold V2G_Sexp. unfold V2G_mult. destruct a. 
  destruct e. destruct v0. destruct v1. simpl. apply V2G_eqBreakDown.
  simpl. split. do 2 rewrite <- neg_eq. remember (m1 ^ r1) as a.
  remember (m0^r2) as b. apply (@inv_dist G Gdot Gone Gbool_eq Ginv module_abegrp a b).
  do 2 rewrite <- neg_eq. remember (m2 ^ r1) as a.
  remember (m3^r2) as b. apply (@inv_dist G Gdot Gone Gbool_eq Ginv module_abegrp a b).
Qed.

Lemma ciphEqual :
  forall (a b : V2G)(g pk : G)(r : F),
  a = V2G_mult (Enc g pk (Finv r) Gone) b <-> 
    V2G_mult a (Enc g pk r Gone) = b .
Proof.
  pose HeliosIACR2018.
  intros.  unfold iff. refine (conj _ _). intros. rewrite H.
  rewrite V2G_Comm. rewrite <- V2G_Assoc. rewrite EncIsHomomorphic.
  rewrite one_right. replace (r - r) with 0. unfold Enc. rewrite mod_ann.
  rewrite mod_ann. rewrite one_right. unfold V2G_cons. simpl. fold V2G_id.
  rewrite V2G_Comm. rewrite V2G_One. trivial. field; auto.
  intros. rewrite <- H.
  rewrite V2G_Comm. rewrite V2G_Assoc. rewrite EncIsHomomorphic.
  rewrite one_right. replace (r - r) with 0. unfold Enc. rewrite mod_ann.
  rewrite mod_ann. rewrite one_right. unfold V2G_cons. simpl. fold V2G_id.
  rewrite V2G_One. trivial. field; auto.
Qed.

End CryptoPrimatives.