(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import FunInd Recdef Lia CommonSSR.

Require Import CommonSSR.

Ltac eq_subst H := apply (elimT eqP) in H; subst.

Section Gauss.

Variable F : fieldType.

Local Open Scope ring_scope.

(*NOTE: nothing to do w gaussian elimination but I need a place to put this*)
Definition rev_cols {m n} (A: 'M[F]_(m, n)) : 'M_(m, n) :=
 \matrix_(i < m, j < n) A i (rev_ord j).

Definition rev_rows {m n} (A: 'M[F]_(m, n)) : 'M_(m, n) :=
  \matrix_(i < m, j < n) A (rev_ord i) j.

(*Can't rewrite directly due to dependent type issues*)
Lemma big_eq_ord {A: Type} (r1 r2 : nat) (Heq: r2 = r1) (op: A -> A -> A) idx (P : pred 'I_r1) F':
  \big[op/idx]_(i < r1 | P i) F' i = \big[op/idx]_(i < r2 | P (eq_ord Heq i)) F' (eq_ord Heq i).
Proof.
  subst. apply eq_big.
  - move => x. f_equal. by apply ord_inj.
  - move => x Hx. f_equal. by apply ord_inj.
Qed.

(*The key fact we need about these*)
Lemma rev_cols_row_mul: forall {m n k} (A : 'M[F]_(m, n)) (B: 'M[F]_(n, k)),
  A *m B = (rev_cols A) *m (rev_rows B).
Proof.
  move => m n k A B. rewrite -matrixP => i j. rewrite !mxE /=.
  have: 0 <= n by []. rewrite leq_eqVlt => /orP[/eqP Hn0 /= | Hnpos /=].
  - subst. rewrite big_seq_cond big_seq_cond. symmetry. 
    rewrite (big_seq_cond (r:=(index_enum (ordinal_finType 0)))) (big_seq_cond (r:=(index_enum (ordinal_finType 0)))).
    rewrite !big1 //; move => x; have: x < 0 by []; by [].
  - rewrite !(big_nth (Ordinal Hnpos)) big_nat_rev /= big_nat_cond. symmetry. rewrite big_nat_cond.
    apply eq_big => [// | x]. have->: size (index_enum (ordinal_finType n)) = n
      by rewrite /index_enum /= ordinal_enum_size.
    move => /andP[/andP[_ Hxn] _].
    have Hcase: (n - (nth (Ordinal Hnpos) (ord_enum n) x).+1)%N = nth (Ordinal Hnpos) (ord_enum n) (0 + n - x.+1). {
      have Hx: x = nat_of_ord (Ordinal Hxn) by []. rewrite {1}Hx nth_ord_enum /= add0n.
      have ->: (n - x.+1)%N = nat_of_ord (rev_ord (Ordinal Hxn)) by []. by rewrite nth_ord_enum. }
 rewrite !mxE /=. by f_equal; f_equal; apply ord_inj; rewrite /= !index_ord_enum.
Qed.

(*Preliminaries*)

(*get elements of identity matrix*)
Lemma id_A : forall {n} (x y : 'I_n),
  (1%:M) x y = if x == y then 1 else (GRing.zero F).
Proof.
move => n x y; rewrite /scalar_mx mxE; by case : (x == y). 
Qed.

(*Some closed form summations we will use*)
Lemma sum_if: forall {n} (x : 'I_n) (f1 : 'I_n -> F),
  \sum_(i < n) (if x == i then f1 i else 0) = f1 x.
Proof.
  move => n x f1. rewrite (big_nth x) /= /index_enum /=. rewrite ordinal_enum_size.
  have Hzero: forall i : nat, i < n -> i != x ->
  (if x == nth x (Finite.enum (ordinal_finType n)) i
    then f1 (nth x (Finite.enum (ordinal_finType n)) i)
    else 0) = 0. {  move => i Hin Hx. have: i == Ordinal Hin by []. move => /eqP Hi; rewrite Hi.
   rewrite ordinal_enum. have: (Ordinal Hin != x) by [].
   rewrite /negb. rewrite eq_sym. by case(x == Ordinal Hin). }
  rewrite (@big_cat_nat _ _ _ x) /= => [| // | ]. 2: by apply: ltnW.
  rewrite big_nat_cond big1.
  - rewrite big_ltn => [|//]. rewrite big_nat_cond big1.
    + by rewrite ordinal_enum eq_refl GRing.add0r GRing.addr0.
    + move => i /andP[/andP [Hxi Hin]]. move => H{H}. apply Hzero. by []. by rewrite gtn_eqF.
  - move => i /andP[/andP [Hxi Hin]]. move => H{H}. apply Hzero. have: x < n by []. move : Hin.
    apply ltn_trans. by rewrite ltn_eqF.
Qed.

Lemma sum_if_twice: forall {n} (r1 r2 : 'I_n) (f1 f2 : 'I_n -> F),
  r1 < r2 ->
  \sum_(i < n) (if i == r1 then f1 i else if i == r2 then f2 i else 0) = f1 r1 + f2 r2.
Proof.
move => n r1 r2 f1 f2 Hlt. rewrite (big_nth r1) /= /index_enum /= ordinal_enum_size.
  have Hzero: forall i : nat, i < n -> i != r1 -> i != r2 ->
  (if nth r1 (Finite.enum (ordinal_finType n)) i == r1
  then f1 (nth r1 (Finite.enum (ordinal_finType n)) i)
  else
  if nth r1 (Finite.enum (ordinal_finType n)) i == r2
  then f2 (nth r1 (Finite.enum (ordinal_finType n)) i)
  else 0) = 0. {
  move => i Hin Hir1 Hr2. have: i == Ordinal Hin by []. move => /eqP Hi. rewrite Hi. 
  rewrite ordinal_enum.
  have: (Ordinal Hin != r1) by []. have: (Ordinal Hin != r2) by []. rewrite /negb.  case(Ordinal Hin == r2).
  by []. by case (Ordinal Hin == r1). } 
  rewrite (@big_cat_nat _ _ _ r1) /=. 2 : by []. 2 : by [apply: ltnW].
  rewrite big_nat_cond big1. 
  - rewrite big_ltn. 2: by [].
    rewrite ordinal_enum eq_refl GRing.add0r (@big_cat_nat _ _ _ r2) /=. 2 : by []. 2 : by [apply: ltnW].
    rewrite big_nat_cond big1.
    + rewrite big_ltn. 2: by []. rewrite ordinal_enum.
      have: (r2 == r1 = false) by apply gtn_eqF. move => Hneq; rewrite Hneq {Hneq}.
      rewrite eq_refl GRing.add0r big_nat_cond big1. by rewrite GRing.addr0.
      move => i /andP[/andP [H0i Hix]]. move =>H {H}. 
      apply: Hzero. by []. rewrite gtn_eqF. by []. move : Hlt H0i. apply ltn_trans. by rewrite gtn_eqF.
    + move => i /andP[/andP [H0i Hix]]. move =>H {H}. apply: Hzero. have: r2 < n by []. move : Hix.
      apply ltn_trans. by rewrite gtn_eqF. by rewrite ltn_eqF.
  - move => i /andP[/andP [H0i Hix]]. move =>H {H}. apply: Hzero. have: r1 < n by []. move : Hix.
    apply ltn_trans. by rewrite ltn_eqF. rewrite ltn_eqF //. move : Hix Hlt. apply ltn_trans.
Qed.


(** Elementary Row Operations*)

(*Swapping rows is already defined by mathcomp - it is xrow. We just need the following*)
Lemma xrow_val: forall {m n} (A: 'M[F]_(m,n)) (r1 r2 : 'I_m) x y,
  (xrow r1 r2 A) x y = if x == r1 then A r2 y else if x == r2 then A r1 y else A x y.
Proof. 
  rewrite /xrow /row_perm //= => m n A r1 r2 x y. rewrite mxE.
  case : (x == r1) /eqP => [-> | Hxr1]. by rewrite perm.tpermL.
  case : (x == r2) /eqP => [ -> | Hxr2]. by rewrite perm.tpermR.
  rewrite perm.tpermD //. all: by rewrite eq_sym; apply /eqP.
Qed. 

Lemma xrow_rr : forall {m n } (A: 'M[F]_(m, n)) (r: 'I_m),
  xrow r r A = A.
Proof.
  move => m n A r. rewrite -matrixP => x y. rewrite xrow_val.
  case : (x == r) /eqP => [Hxr | Hxr//]. by rewrite Hxr.
Qed.

(*scalar multiply row r in matrix A by scalar c*)
Definition sc_mul {m n} (A : 'M[F]_(m, n)) (c: F) (r: 'I_m) : 'M[F]_(m, n) :=
  \matrix_(i < m, j < n) if i == r then c * (A i j) else A i j. 

(*elementary matrix for scalar multiplication*)
Definition sc_mul_mx (n: nat) (c: F) r : 'M[F]_(n, n) := @sc_mul n n (1%:M) c r.

(*scalar multiplication is same as mutliplying by sc_mul_mx on left*)
Lemma sc_mulE: forall {m n : nat} (A: 'M[F]_(m, n)) (c: F) (r: 'I_m),
  sc_mul A c r = (sc_mul_mx c r) *m A.
Proof.
move => m n A c r; rewrite /sc_mul_mx /sc_mul. rewrite -matrixP /eqrel => x y. rewrite !mxE /=. erewrite eq_big_seq.
2 : { move => z. rewrite mxE id_A //. }
rewrite /=. case : (eq_op x r). 
  - erewrite eq_big_seq. 2 : { move => z Inz. rewrite -GRing.mulrA //. }
    rewrite (@eq_big_seq _ _ _ _ _ _ (fun z => c * ((if x == z then A z y else 0)))).
    rewrite -big_distrr. by rewrite sum_if. rewrite //= /eqfun. move => x' Xin.
    case(x == x'). by rewrite GRing.mul1r. by rewrite GRing.mul0r.
  - rewrite (@eq_big_seq _ _ _ _ _ _ (fun z => ((if x == z then A z y else 0)))).
    by rewrite sum_if. rewrite /eqfun //= => x' Xin. case (x == x').
    by rewrite GRing.mul1r. by rewrite GRing.mul0r.
Qed.

(*inverse for scalar sc_mul_mx*)
Lemma sc_mul_mx_inv: forall {m : nat} (c: F) (r: 'I_m),
  c != 0 ->
  (sc_mul_mx c r) *m (sc_mul_mx c^-1 r) = 1%:M.
Proof.
  move => m c r Hc. rewrite -sc_mulE. rewrite !/sc_mul_mx /sc_mul.
  rewrite -matrixP /eqrel => x y. rewrite !mxE. case Heq: ( x == r). 
  rewrite GRing.mulrA. rewrite GRing.divff. by rewrite GRing.mul1r. by []. by [].
Qed.

(*sc_mul_mx is invertible*)
Lemma sc_mul_mx_unitmx: forall {m : nat} (c: F) (r: 'I_m),
  c != 0 ->
  (sc_mul_mx c r) \in unitmx.
Proof.
  move => m c r Hc. apply: (proj1 (mulmx1_unit (@sc_mul_mx_inv m c r  Hc))).
Qed. 

(*Add multiple of one row to another - r2 := r2 + c * r1*)
Definition add_mul {m n} (A : 'M[F]_(m, n)) (c: F) (r1 r2: 'I_m) : 'M[F]_(m, n) :=
  \matrix_(i < m, j < n) if i == r2 then (A r2 j) + (c * (A r1 j)) else A i j. 

(*elementary matrix for adding multiples*)
Definition add_mul_mx (n: nat) (c: F) r1 r2 : 'M[F]_(n,n) := 
  \matrix_(i < n, j < n) if i == r2 then 
                            if j == r1 then c else if j == r2 then 1 else 0
                         else if i == j then 1 else 0.


(*adding multiple is the same as multiplying by [add_mul_mx] matrix on left *)
Lemma add_mulE: forall {m n : nat} (A: 'M[F]_(m, n)) (c: F) (r1 r2: 'I_m),
  r1 != r2 ->
  add_mul A c r1 r2 = (add_mul_mx c r1 r2) *m A.
Proof.
move => m n A c r1 r2 Hr12; rewrite /add_mul_mx /add_mul. rewrite -matrixP /eqrel => x y. rewrite !mxE /=.
erewrite eq_big_seq. 2 : { move => z. rewrite mxE //. } rewrite //=.
case : (eq_op x r2). 
  - rewrite (@eq_big_seq _ _ _ _ _ _ (fun z => ((if z == r1 then c * A z y else if z == r2 then A z y else 0)))).
    case (orP (ltn_total r1 r2)) => [Hleq | Hgt].
    + case (orP Hleq) => [Hlt | Heq]. rewrite sum_if_twice //. by rewrite GRing.addrC.
      have: (nat_of_ord r1 != nat_of_ord r2) by [].
      rewrite /negb. by rewrite Heq.
    + rewrite (@eq_big_seq _ _ _ _ _ _ (fun z => ((if z == r2 then A z y else if z == r1 then c * A z y else 0)))).
      rewrite sum_if_twice //. move => z Hz. case : (z == r1) /eqP => [-> | //]. move: Hgt. 
      case : (r1 == r2) /eqP =>[ -> | //]. by rewrite ltnn.
    + move => z Hz. case Hzeq : (z == r1) => //=. case Hze: (z == r2) => //=.  by apply GRing.mul1r. by apply GRing.mul0r.
  - rewrite (@eq_big_seq _ _ _ _ _ _ (fun z => (if x == z then A z y else 0))). by rewrite sum_if.
    move => z Hz. case Heqz : (x == z). by apply GRing.mul1r. by apply GRing.mul0r.
Qed.

Lemma add_mul_mx_inv: forall {m : nat} (c: F) (r1 r2: 'I_m),
  r1 != r2 ->
  (add_mul_mx c r1 r2) *m (add_mul_mx (- c) r1 r2) = 1%:M.
Proof.
  move => m c r1 r2 Hr12. rewrite -add_mulE //. rewrite !/add_mul_mx /add_mul.
  rewrite -matrixP /eqrel => x y. rewrite !mxE eq_refl. rewrite (negbTE Hr12).
  case : (x == r2) /eqP => [-> |]. rewrite eq_sym. case : (r1 == y) /eqP => [<-|]. 
  rewrite GRing.mulr1 GRing.addNr eq_sym. by rewrite (negbTE Hr12).
  rewrite eq_sym GRing.mulr0 GRing.addr0. by case H : (r2 == y). by case H : (x == y).
Qed.

(*add_mul_mx is invertible*)
Lemma add_mul_mx_unitmx: forall {m : nat} (c: F) (r1 r2: 'I_m),
  r1 != r2 ->
  (add_mul_mx c r1 r2) \in unitmx.
Proof.
  move => m c r1 r2 Hr12. apply: (proj1 (mulmx1_unit (@add_mul_mx_inv m c r1 r2 Hr12))).
Qed.

(** Row equivalence *)

Inductive ero : forall (m n : nat), 'M[F]_(m, n) -> 'M[F]_(m, n) -> Prop :=
  | ero_swap: forall {m n} r1 r2 (A : 'M[F]_(m,n)),
      ero A (xrow r1 r2 A)
  | ero_sc_mul: forall {m n} r c (A : 'M[F]_(m,n)),
      c != 0 ->
      ero A (sc_mul A c r)
  | ero_add_mul: forall {m n} r1 r2 c (A : 'M[F]_(m,n)),
      r1 != r2 ->
      ero A (add_mul A c r1 r2).

Lemma ero_mul_unit: forall {m n} (A B : 'M[F]_(m, n)),
  ero A B ->
  exists E, (E \in unitmx) && (B == E *m A).
Proof.
  move => m n A B Hero. elim: Hero; move => m' n' r1.
  - move => r2 A'. exists (tperm_mx r1 r2). by rewrite {1}/tperm_mx unitmx_perm xrowE eq_refl.
  - move => c A' Hc. exists (sc_mul_mx c r1). by rewrite sc_mulE eq_refl sc_mul_mx_unitmx.
  - move => r2 c A' Hr. exists (add_mul_mx c r1 r2). rewrite add_mulE. by rewrite eq_refl add_mul_mx_unitmx. by [].
Qed.

Lemma ero_sym: forall {m n} (A B : 'M[F]_(m, n)),
  ero A B ->
  ero B A.
Proof.
  move => m n A B Hero. case: Hero.
  - move => m' n' r1 r2 A'. have HA': A' = xrow r1 r2 (xrow r1 r2 A'). { rewrite -matrixP => x y.
    rewrite !xrow_val !eq_refl.  case : (x == r1) /eqP => [-> |].
    + by case Hr12: (r2 == r1) /eqP => [-> |].
    + by case Hr12: (x == r2) /eqP => [-> |]. }
    rewrite {2}HA'. apply ero_swap.
  - move => m' n' r c A' Hc0. have HA': A' = sc_mul (sc_mul A' c r) c^-1 r. {
      rewrite !sc_mulE mulmxA mulmx1C. by rewrite mul1mx. by rewrite sc_mul_mx_inv. }
    rewrite {2}HA'. apply ero_sc_mul. by apply GRing.invr_neq0.
  - move => m' n' r1 r2 c A' Hr12. have HA': A' = add_mul (add_mul A' c r1 r2) (- c) r1 r2. {
      rewrite !add_mulE // mulmxA mulmx1C. by rewrite mul1mx. by rewrite add_mul_mx_inv. }
    rewrite {2}HA'. by apply ero_add_mul.
Qed. 

Inductive row_equivalent: forall m n, 'M[F]_(m, n) -> 'M[F]_(m, n) -> Prop :=
  | row_equiv_refl: forall {m n} (A: 'M[F]_(m,n)),
     row_equivalent A A
  | row_equiv_ero: forall {m n} (A B C: 'M[F]_(m,n)),
     ero A B ->
     row_equivalent B C ->
     row_equivalent A C.

Lemma ero_row_equiv: forall {m n} (A B : 'M[F]_(m,n)),
  ero A B ->
  row_equivalent A B.
Proof.
  move => m n A B Hero. apply (@row_equiv_ero _ _ _ B) => [//|]. apply row_equiv_refl.
Qed.

Lemma row_equivalent_trans: forall {m n} (A B C : 'M[F]_(m, n)),
  row_equivalent A B ->
  row_equivalent B C ->
  row_equivalent A C.
Proof.
  move => m n A B C Hre. move : C. elim: Hre; clear m n A B.
  - by [].
  - move => m n A B C Hero Hre IH D Hd. apply (@row_equiv_ero _ _ A B D). by []. by apply: IH.
Qed. 

Lemma row_equivalent_sym: forall {m n} (A B: 'M[F]_(m, n)),
  row_equivalent A B -> row_equivalent B A.
Proof.
  move => m n A B Hre. elim: Hre.
  - move => m' n' A'. apply row_equiv_refl.
  - move => m' n' A' B' C' Hero HBC HCB.
    apply ero_sym in Hero. apply (row_equivalent_trans HCB).
    by apply ero_row_equiv.
Qed.

(*If A and B are row equivalent, then A = EB for some invertible matrix E*) 
Lemma row_equivalent_mul_unit: forall {m n} (A B : 'M[F]_(m, n)),
  row_equivalent A B ->
  exists E, (E \in unitmx) && (B == E *m A).
Proof.
  move => m n A B Hre. elim: Hre; clear m n A B; move => m n A.
  - exists (1%:M). by rewrite unitmx1 mul1mx eq_refl.
  - move => B C Hero Hre IH. case : IH. move => E /andP[Heu /eqP Hc].
    apply ero_mul_unit in Hero. case: Hero. move => E' /andP[Heu' /eqP Hb]. subst. 
    exists (E *m E'). rewrite unitmx_mul.
    by rewrite mulmxA eq_refl Heu Heu'. 
Qed.

(*If A and B are row equivalent, then A is invertible iff B is*)
Lemma row_equivalent_unitmx_iff: forall {n} (A B : 'M[F]_(n, n)),
  row_equivalent A B ->
  (A \in unitmx) = (B \in unitmx).
Proof.
  move => n A B Hre. apply row_equivalent_mul_unit in Hre. case Hre => E /andP[Hunit /eqP Hb]. 
  by rewrite Hb unitmx_mul Hunit. 
Qed. 

(** Submatrix Preservation of Row Equivalence*)

Ltac case_eqb x y H :=
  case_view (x == y) (@eqP _ x y) H.

Ltac case_ltb x y H :=
  case_view (x < y) (@ltP _ x y) H.

(*If we do a scalar multiplication, any submatrix is row equivalent to the corresponding resulting submatrix*)
Lemma mxsub_sc_mul_row_equiv: forall {m n m' n'} (A : 'M[F]_(m, n)) (f : 'I_m' -> 'I_m) (g : 'I_n' -> 'I_n) (r: 'I_m) c,
  injective f ->
  c != 0 ->
  row_equivalent (mxsub f g A) (mxsub f g (sc_mul A c r)).
Proof.
  move => m n m' n' A f g r c Hinj Hc.
  have Href: reflect (exists x, f x == r) ([exists x, f x == r]). apply existsPP. 
  move => x. apply idP. case Hex : ([exists x, f x == r]).
  - have: exists x, f x == r. by apply (elimT Href). move {Hex} => [x Hfx].
    have->: (mxsub f g (sc_mul A c r)) = sc_mul (mxsub f g A) c x.
    rewrite /mxsub /sc_mul -matrixP /eqrel => i j. rewrite !mxE. 
    case : (i == x) /eqP => [-> | Heq]. by rewrite Hfx.
    have->: f i == r = false. case : (f i == r) /eqP => [Hf | //]. move : Hinj. rewrite /injective => /(_ x i).
    apply (elimT eqP) in Hfx. subst. move : Hf -> => H. by rewrite H in Heq. by [].
    apply ero_row_equiv. by constructor.
  - have : (~ exists x, f x == r) by rewrite (rwN Href) Hex. move {Hex} => Hex. 
    have: (mxsub f g (sc_mul A c r)) = mxsub f g A. rewrite /mxsub /sc_mul -matrixP /eqrel.
    move => i j; rewrite !mxE. case Fir : (f i == r). 
    have : (exists x, f x == r) by (exists i; rewrite Fir). by []. by []. move ->.
    constructor.
Qed.

(*We have a similar result for adding scalar multiples, but the row we are adding must be in the submatrix*)
Lemma mxsub_add_mul_row_equiv: forall {m n m' n'} (A : 'M[F]_(m, n)) (f : 'I_m' -> 'I_m) (g : 'I_n' -> 'I_n) 
  (r1 r2: 'I_m) c,
  injective f ->
  r1 != r2 ->
  (exists (i : 'I_m'), f i == r1) ->
  row_equivalent (mxsub f g A) (mxsub f g (add_mul A c r1 r2)).
Proof.
  move => m n m' n' A f g r1 r2 c Hinj Hr12 [i Hfi].
  have Href: reflect (exists x, f x == r2) ([exists x, f x == r2]). apply existsPP. 
  move => x. apply idP. case Hex : ([exists x, f x == r2]).
  - have: exists x, f x == r2. by apply (elimT Href). move {Hex} => [x Hfx].
    have->: (mxsub f g (add_mul A c r1 r2)) = add_mul (mxsub f g A) c i x. {
      rewrite /mxsub /add_mul -matrixP. move => i' j'. rewrite !mxE.
      case : (i' == x) /eqP => [-> | Hix].
      - rewrite Hfx. eq_subst Hfx. by eq_subst Hfi.
      - case Hfir2 : (f i' == r2) => [|//]. have : (i' = x). apply Hinj. eq_subst Hfx. 
        by eq_subst Hfir2. by []. }
    apply ero_row_equiv. constructor. case: (i == x) /eqP => [Hix |//]. subst. 
    move: Hr12. eq_subst Hfi. by rewrite Hfx.
  - have : (~ exists x, f x == r2) by rewrite (rwN Href) Hex. move {Hex} => Hex.
    have->:  (mxsub f g (add_mul A c r1 r2)) = mxsub f g A.
    rewrite /mxsub /add_mul -matrixP. move => i' j'. rewrite !mxE.
    case Hfir : (f i' == r2). have : (exists x, f x == r2) by (exists i'; by rewrite Hfir). by [].
    by []. by constructor.
Qed.

(*We need another similar result for swaps for the Vandermonde proofs (not needed for gaussian elimination directly)*)
Lemma mxsub_xrow_row_equiv: forall {m n m' n'} (A: 'M[F]_(m, n)) (f: 'I_m' -> 'I_m) (g: 'I_n' -> 'I_n)
  (r1 r2 : 'I_m),
  injective f ->
  (exists (i : 'I_m'), f i == r1) ->
  (exists (i: 'I_m'), f i == r2) ->
  row_equivalent (mxsub f g A) (mxsub f g (xrow r1 r2 A)).
Proof.
  move => m n m' n' A f g r1 r2 Hinj [i1 Hi1] [i2 Hi2].
  have->: (mxsub f g (xrow r1 r2 A)) = xrow i1 i2 (mxsub f g A). {
    rewrite -matrixP => x y. rewrite mxE !xrow_val !mxE.
    case_eqb x i1 Hxi1.
    - subst. rewrite Hi1. by eq_subst Hi2.
    - case_eqb (f x) r1 Hxr1.
      + subst. exfalso. apply Hxi1. apply Hinj. apply /eqP. by rewrite eq_sym Hi1.
      + case_eqb x i2 Hxi2.
        * subst. rewrite Hi2. by eq_subst Hi1.
        * case_eqb (f x) r2 Hxr2. 
          -- subst. exfalso. apply Hxi2. apply Hinj. apply /eqP. by rewrite eq_sym Hi2.
          -- by []. }
  apply ero_row_equiv. constructor.
Qed.

(*We can combine these - any submatrix of columns is preserved under row operations*)
Lemma colsub_row_equivalent: forall {m n n'} (A B: 'M[F]_(m, n)) (f: 'I_n' -> 'I_n),
  row_equivalent A B ->
  row_equivalent (colsub f A) (colsub f B).
Proof.
  move => m n n' A B f Hre. induction Hre.
  - constructor.
  - apply (@row_equivalent_trans _ _ _ (colsub f B)).
    + destruct H. (*case and elim dont work well here*)
      * apply mxsub_xrow_row_equiv. apply inj_id. exists r1. apply eq_refl. exists r2. apply eq_refl.
      * apply mxsub_sc_mul_row_equiv. apply inj_id. by [].
      * apply mxsub_add_mul_row_equiv. apply inj_id. by []. exists r1. apply eq_refl.
    + apply IHHre.
Qed.

(** Gaussian Elimination Intermediate Functions*)
(*Find the first nonzero entry in column col, starting from index r*)
(*Because we want to use the result to index into a matrix, we need an ordinal. So we have a function that
  returns the nat, then we wrap the type in an option. This makes the proofs a bit more complicated*)

Definition fst_nonzero_nat {m n} (A: 'M[F]_(m, n)) (col: 'I_n) (r: 'I_m) : nat :=
  (find (fun (x : 'I_m) => (r <= x) && (A x col != 0)) (ord_enum m)).

Definition fst_nonzero {m n} (A: 'M[F]_(m, n)) (col: 'I_n) (r: 'I_m) : option 'I_m :=
  insub (fst_nonzero_nat A col r).

Lemma fst_nonzero_nat_bound:  forall {m n} (A: 'M[F]_(m, n)) (col: 'I_n) (r: 'I_m),
  (fst_nonzero_nat A col r == m) || (fst_nonzero_nat A col r < m).
Proof.
  move => m n A col r. rewrite /fst_nonzero_nat.
  have Hleq := find_size(fun x : 'I_m => (r <= x) && (A x col != 0)) (ord_enum m). move : Hleq.
  by rewrite size_ord_enum leq_eqVlt.
Qed.  

(*Specification of some case of [find_nonzero]*)
Lemma fst_nonzero_some_iff: forall {m n} (A: 'M[F]_(m, n)) (col: 'I_n) (r: 'I_m) f,
  fst_nonzero A col r = Some f <-> (r <= f) /\ (A f col != 0) /\ (forall (x : 'I_m), r <= x < f -> A x col == 0).
Proof.
  move => m n A col r f.
  have: r <= f /\ A f col != 0 /\ (forall x : 'I_m, r <= x < f -> A x col == 0) <-> fst_nonzero_nat A col r = f.
  rewrite /fst_nonzero_nat. rewrite find_iff.
  - split. move => [Hrf [Hnonz Hbef]]. split. move => x. by rewrite nth_ord_enum Hrf Hnonz.
    move => x y Hyf. have Hym : y < m. have : f < m by []. move : Hyf. by apply ltn_trans.
    have: nth x (ord_enum m) y = nth x (ord_enum m) (Ordinal Hym) by [].
    move ->. rewrite nth_ord_enum. case Hr : (r <= Ordinal Hym).
    rewrite Hbef //=. rewrite Hyf.  have: (r <= y) by []. by move ->. by [].  
    move => [Ha Hprev]. move : Ha => /(_ f). rewrite nth_ord_enum => /andP[Hleq Ha].
    rewrite Hleq Ha. repeat(split; try by []). move => x /andP[Hxr Hxf]. move : Hprev => /(_ r x).
    rewrite Hxf nth_ord_enum. move => Hor. have : ~~ ((r <= x) && (A x col != 0)) by rewrite {1}/negb Hor.
    move : Hor => H{H}. rewrite Bool.negb_andb => /orP[Hrx | Hac]. move : Hxr Hrx. by move ->.
    move : Hac. rewrite /negb. by case: (A x col == 0).
  - apply r.
  - by rewrite size_ord_enum. 
  - move ->. rewrite /fst_nonzero. have Hbound := (fst_nonzero_nat_bound A col r).
    move : Hbound => /orP[/eqP Heq | Hlt].
    + rewrite insubF. split. by []. rewrite Heq => Hmf.
      have: (f < m) by []. by rewrite -Hmf ltnn. by rewrite Heq ltnn.  
    + rewrite insubT. split. move => Hs. case : Hs. move => Hf. rewrite -Hf. by [].
      move => Hfst. f_equal. have : (nat_of_ord (Sub (fst_nonzero_nat A col r) Hlt) == nat_of_ord f).
      by rewrite -Hfst. move => Hnatord. have : (Sub (fst_nonzero_nat A col r) Hlt  == f).
      by []. move => Hsub. by apply /eqP.
Qed. 

Lemma fst_nonzero_none: forall {m n} (A: 'M[F]_(m, n)) (col: 'I_n) (r: 'I_m),
  fst_nonzero A col r = None ->
  forall (x : 'I_m), r <= x -> A x col = 0.
Proof.
  move => m n A col r. rewrite /fst_nonzero.
  case : (orP (fst_nonzero_nat_bound A col r)) => [ Heq | Hlt].
  move => H{H}. move : Heq. rewrite /fst_nonzero_nat. have Hsz := size_ord_enum m. move => Hfind.
  have : (find (fun x : 'I_m => (r <= x) && (A x col != 0)) (ord_enum m) == size (ord_enum m)).
  by rewrite Hsz. move {Hfind} => /eqP Hfind. move => x Hrx. rewrite find_none_iff in Hfind.
  move : Hfind => /(_ x). have->/=: x \in ord_enum m by apply mem_ord_enum.
  move => Hfind. apply rem_impl in Hfind. move: Hfind.
  rewrite negb_and => /orP[Hnrx | Hxcol]. by move: Hrx Hnrx ->. apply (elimT eqP).
  move : Hxcol. by case : (A x col == 0).
  by rewrite insubT.
Qed. 

(*Now, we define the leading coefficient of a row (ie, the first nonzero element) - will be n if row is all zeroes*)
(*We also want an ordinal, so we do something similar to above*)
Definition lead_coef_nat {m n} (A: 'M[F]_(m, n)) (row: 'I_m) : nat :=
  find (fun x => A row x != 0) (ord_enum n).

Definition lead_coef {m n} (A: 'M[F]_(m, n)) (row: 'I_m) : option 'I_n := insub (lead_coef_nat A row).

Lemma lead_coef_nat_bound : forall {m n} (A: 'M[F]_(m, n)) (row: 'I_m),
  (lead_coef_nat A row == n) || (lead_coef_nat A row < n).
Proof.
  move => m n A row. rewrite /lead_coef_nat.
  have Hsz := find_size (fun (x : 'I_n) => A row x != 0) (ord_enum n). move : Hsz.
  by rewrite size_ord_enum leq_eqVlt.
Qed.

(*Specification for the some case*)
Lemma lead_coef_some_iff: forall {m n} (A: 'M[F]_(m, n)) (row: 'I_m) c,
  lead_coef A row = Some c <-> (A row c != 0) /\ (forall (x : 'I_n), x < c -> A row x = 0).
Proof.
  move => m n A row c. have: A row c != 0 /\ (forall x : 'I_n, x < c -> A row x = 0) <-> lead_coef_nat A row = c.
  rewrite /lead_coef_nat. rewrite find_iff. split.
  - move => [Harc Hprev]. split; move => x. by rewrite nth_ord_enum. move => y Hyc.
    rewrite Hprev. by rewrite eq_refl. have Hyn : y < n. have : c < n by [].
    move : Hyc. apply ltn_trans. have : nth x (ord_enum n) y == nth x (ord_enum n) (Ordinal Hyn) by [].
    move => /eqP Hnth. by rewrite Hnth nth_ord_enum.
  - move => [Harc Hprev]. move : Harc => /(_ c). rewrite nth_ord_enum. move : Hprev => /(_ c) Hprev Harc.
    split. by []. move => x Hxc. move : Hprev => /(_ x). rewrite Hxc nth_ord_enum.
    case : (A row x == 0) /eqP => [ Heq|//]. by rewrite Heq.
    move => Hcon Hf. by have: (~~false = false) by apply Hf. 
  - apply c.
  - by rewrite size_ord_enum.
  - move ->. rewrite /lead_coef. have Hbound := (lead_coef_nat_bound A row).
    move : Hbound => /orP[/eqP Heq | Hlt].
    + rewrite insubF. split => [//|]. rewrite Heq => Hnc.
      have: (c < n) by []. by rewrite -Hnc ltnn. by rewrite Heq ltnn.
    + rewrite insubT. split. move => Hs. case : Hs. move => Hf. rewrite -Hf. by [].
      move => Hfst. f_equal. have : (nat_of_ord (Sub (lead_coef_nat A row) Hlt) == nat_of_ord c)
      by rewrite -Hfst. move => Hnatord. 
      have : (Sub (lead_coef_nat A row) Hlt == c) by []. by move => /eqP Heq.
Qed. 

Lemma lead_coef_none_iff: forall {m n} (A: 'M[F]_(m, n)) (row: 'I_m),
  lead_coef A row = None <-> (forall (x : 'I_n),  A row x = 0).
Proof.
  move => m n A row. have: (forall x : 'I_n, A row x = 0) <-> lead_coef_nat A row = n.
  have : lead_coef_nat A row = n <-> lead_coef_nat A row = size (ord_enum n) by rewrite size_ord_enum.
  move ->. rewrite find_none_iff. split.
  move => Hc x Hin. rewrite negbK. apply (introT eqP). apply Hc.
  move => Hc x. apply (elimT eqP). move : Hc => /(_ x); rewrite negbK. move ->. by []. by apply mem_ord_enum.
  move ->. rewrite /lead_coef. case (orP(lead_coef_nat_bound A row)) => [/eqP Heq | Hlt].
  - rewrite insubF. by []. by rewrite Heq ltnn. 
  - rewrite insubT. split => [//| Heq /=]. have: n < n by rewrite -{1}Heq. by rewrite ltnn.
Qed. 

(*Fold a function over the rows of a matrix that are contained in a list.
  If this function only affects a single row and depends only on the entries in that row and possibly
  rows that are not in the list, then we can describe the (i, j)th component just with the function itself.
  This allows us to prove things about the multiple intermediate steps in gaussian elimination at once*)

(*Two helper lemmas*)
Lemma mx_row_transform_notin: forall {m n} (A: 'M[F]_(m,n)) (f: 'I_m -> 'M[F]_(m,n) -> 'M[F]_(m,n)) (l: seq 'I_m),
  (forall (A: 'M[F]_(m,n)) i j r, i != r ->  A i j = (f r A) i j) ->
  forall r j, r \notin l ->
  (foldr f A l) r j = A r j.
Proof.
  move => m n A f l Hfcond. elim: l => [//| h t IH].
  move => r j. rewrite in_cons negb_or => /andP[Hhr Hnotint] //=. rewrite -Hfcond. by apply: IH. by []. 
Qed. 

Lemma row_function_equiv: forall {m n} (A: 'M[F]_(m,n)) (l : seq 'I_m) (r : 'I_m) (f: 'I_m -> 'M[F]_(m,n) -> 'M[F]_(m,n)),
  (forall (A : 'M_(m, n)) (i : ordinal_eqType m) (j : 'I_n) r,
         i != r -> A i j = f r A i j) -> (*f only changes entries in r*)
  (forall (A B : 'M[F]_(m,n)), (forall j, A r j = B r j) -> (forall r' j, r' \notin l -> A r' j = B r' j) ->
    forall j, (f r A) r j = (f r B) r j) -> (*f depends only on values in row r and rows not in the list*) 
  r \notin l ->
  forall j, (f r (foldr f A l)) r j = (f r A) r j.
Proof.
  move => m n A l r f Hres Hinp Hinr' j. rewrite (Hinp _ A). by []. move => j'. apply: mx_row_transform_notin.
  by []. by []. apply: mx_row_transform_notin. by [].
Qed. 

(*How we can describe the entries of the resulting list (all other entries are handled by [mx_row_transform_notin]*)
Lemma mx_row_transform: forall {m n} (A: 'M[F]_(m,n)) (f: 'I_m -> 'M[F]_(m,n) -> 'M[F]_(m,n)) (l: seq 'I_m) r,
  (forall (A: 'M[F]_(m,n)) i j r, i != r ->  A i j = (f r A) i j) ->
  (forall (A B : 'M[F]_(m,n)) r, (forall j, A r j = B r j) -> (forall r' j, r' \notin l -> A r' j = B r' j) ->
    forall j, (f r A) r j = (f r B) r j) ->
  uniq l ->
  forall j, r \in l ->
  (foldr f A l) r j = (f r A) r j.
Proof.
  move => m n A f l r Hfout. elim: l => [//| h t IH]. rewrite //= => Hfin /andP[Hnotin Huniq] j.
  rewrite //= in_cons. move /orP => [/eqP Hhr | Hinr]. subst. apply (row_function_equiv).
  apply: Hfout. move => A' B H1 H2. apply: Hfin. apply: H1. move => r'' j'' Hnotin'. apply: H2.
  move : Hnotin'. by rewrite in_cons negb_or => /andP[Heq Hnin]. by [].
  rewrite -Hfout. apply: IH; rewrite //. move => A' B' H1 H2.
  move => Hcond j'. apply Hfin. by []. move => r' j'' Hnotin'. apply Hcond. move: Hnotin'.
  by rewrite in_cons negb_or => /andP[Heq Hnin].
  case Heq : (r == h). move : Heq => /eqP Heq. subst. move : Hinr Hnotin. move ->. by []. by [].
Qed.

(*We can use [foldl] instead, since these functions can be evaluated in any order*)
Lemma mx_row_transform_rev: forall {m n} (A: 'M[F]_(m,n)) (f: 'I_m -> 'M[F]_(m,n) -> 'M[F]_(m,n)) (l: seq 'I_m),
  (forall (A: 'M[F]_(m,n)) i j r, i != r ->  A i j = (f r A) i j) ->
  (forall (A B : 'M[F]_(m,n)) r, (forall j, A r j = B r j) -> (forall r' j, r' \notin l -> A r' j = B r' j) ->
    forall j, (f r A) r j = (f r B) r j) ->
  uniq l ->
  (foldr f A l) = foldr f A (rev l).
Proof.
  move => m n A f l Hfout Hfin Hun.
  rewrite -matrixP /eqrel => i j. case Hin: (i \in l).
  - rewrite !mx_row_transform; try by []. move => A' B' Heq1 Heq2 Hcond. apply Hfin. by [].
    move => r' j'. rewrite -mem_rev. apply Hcond. by rewrite rev_uniq. by rewrite mem_rev.
  - rewrite !mx_row_transform_notin; try by []. by rewrite mem_rev Hin. by rewrite Hin.
Qed.

(*This resulting matrix is row equivalent if f is*)
Lemma mx_row_transform_equiv: forall {m n} (A: 'M[F]_(m,n)) (f: 'I_m -> 'M[F]_(m,n) -> 'M[F]_(m,n)) (l: seq 'I_m),
  (forall (A: 'M[F]_(m, n)) (r : 'I_m), row_equivalent A (f r A)) ->
  row_equivalent A (foldr f A l).
Proof.
  move => m n A f l Hre. elim: l => [//=| h t IH].
  apply: row_equiv_refl. rewrite //=. apply (row_equivalent_trans IH). apply Hre.
Qed. 

(*Now we can define the gaussian elimination functions*)

(*make all entries in column c 1 or zero*)
Definition all_cols_one {m n} (A: 'M[F]_(m, n)) (c: 'I_n) :=
  foldr (fun x (acc : 'M[F]_(m, n)) => let f := acc x c in if f == 0 then acc else (sc_mul acc (f^-1) x)) A (ord_enum m).

Lemma all_cols_one_val: forall {m n} (A: 'M[F]_(m,n)) c i j,
  (all_cols_one A c) i j = let f := A i c in if f == 0 then A i j else A i j / f.
Proof.
  move => m n A c i j. rewrite mx_row_transform. 
  - rewrite //=. case Heq: (A i c == 0) => [//|].
    by rewrite /sc_mul mxE eq_refl GRing.mulrC.
  - move => A' i' j' r'. rewrite /=. case (A' r' c == 0) => [//|//=].
    rewrite /sc_mul mxE /negb. by case: (i' == r').
  - move => A' B' r Hin Hout j'. rewrite /=. case Harc: (A' r c == 0);
    rewrite Hin in Harc; rewrite Harc. by rewrite Hin.
    by rewrite /sc_mul !mxE eq_refl !Hin.
  - apply ord_enum_uniq.
  - apply mem_ord_enum.
Qed.

Lemma all_cols_one_row_equiv: forall {m n} (A: 'M[F]_(m,n)) c,
  row_equivalent A (all_cols_one A c).
Proof.
  move => m n A c. apply mx_row_transform_equiv.
  move => A' r. rewrite //=. case Hz: (A' r c == 0).
  - constructor.
  - apply ero_row_equiv. constructor. apply GRing.Theory.invr_neq0. by rewrite Hz.
Qed.

(*A version of [rem] that instead removes all matching elements. In our case, it is the same, but we
  can prove a more general lemma about foldr*)

Definition remAll  {A: eqType} (x : A) (l : seq A) := filter (predC1 x) l.

Lemma foldr_remAll: forall {A : eqType} {B} (l: seq A) (f: A -> B -> B) (base: B) (z: A),
  foldr (fun x acc => if (x == z) then acc else f x acc) base l =
  foldr f base (remAll z l).
Proof.
  move => A B l. elim: l => [//| h t IH f base z /=]. rewrite /negb. case : (h == z).
  by rewrite IH. by rewrite /= IH.
Qed.

Lemma foldl_remAll: forall {A : eqType} {B} (l: seq A) (f: B -> A -> B) (base: B) (z: A),
  foldl (fun acc x => if (x == z) then acc else f acc x) base l =
  foldl f base (remAll z l).
Proof.
  move => A B l. elim: l => [//| h t IH f base z /=]. rewrite /negb. case : (h == z).
  by rewrite IH. by rewrite /= IH.
Qed.

Lemma remAll_notin: forall {A: eqType} (x: A) (l: seq A),
  x \notin (remAll x l).
Proof.
  move => A x l. elim: l => [// | h t IH //=].
  rewrite {2}/negb. case Heq:  (h == x). exact IH. rewrite in_cons Bool.negb_orb.
  by rewrite {1}/negb eq_sym Heq IH.
Qed. 

Lemma remAll_in: forall {A: eqType} (x y : A) (l: seq A),
  x != y ->
  x \in l ->
  x \in (remAll y l).
Proof.
  move => A x y l. elim : l => [//| h t IH Hneq /=].
  rewrite in_cons; move /orP => [/eqP Hxh | Ht]. subst. by rewrite Hneq in_cons eq_refl.
  have: x \in remAll y t. by apply IH. case : (h != y) => [|//].
  rewrite in_cons. move ->. by rewrite orbT.
Qed. 

Lemma rem_remAll: forall {A: eqType} (x : A) (l: seq A),
  uniq l ->
  rem x l = remAll x l.
Proof.
  move => A x l Hu. by rewrite rem_filter.
Qed. 


(*Subtract row r from all rows except row r (if A r' c = 0)*) 
Definition sub_all_rows {m n} (A: 'M[F]_(m, n)) (r : 'I_m) (c : 'I_n) : 'M[F]_(m, n) :=
  foldr (fun x acc => if x == r then acc else let f := A x c in
                        if f == 0 then acc else add_mul acc (- 1) r x) A (ord_enum m). 

Lemma sub_all_rows_val: forall {m n} (A: 'M[F]_(m,n)) r c i j,
  (sub_all_rows A r c) i j = if i == r then A i j else
                            if A i c == 0 then A i j else A i j - A r j.
Proof.
  move => m n A r c i j. rewrite /sub_all_rows. rewrite foldr_remAll. case : (i == r) /eqP => [-> | Hir].
  rewrite mx_row_transform_notin. by []. move => A' i' j' r'.
  case : (A r' c == 0). by []. rewrite /add_mul mxE //= /negb. by case : (i' == r').
  apply remAll_notin. 
  rewrite mx_row_transform.
  - case (A i c == 0) => [// | ]. by rewrite /add_mul mxE eq_refl GRing.mulN1r.
  - move => A' i' j' r'. case : (A r' c == 0) => [//|].
    rewrite /add_mul mxE /negb. by case H : (i' == r').
  - move => A' B' r' Hin Hout j'. case : (A r' c == 0). apply Hin.
    rewrite !/add_mul !mxE !eq_refl !Hin.
    rewrite Hout => [//|]. apply remAll_notin.
  - rewrite -rem_remAll. apply rem_uniq. all: apply ord_enum_uniq.
  - apply remAll_in. by apply /eqP. by rewrite mem_ord_enum.
Qed.

Lemma sub_all_rows_row_equiv: forall {m n} (A: 'M[F]_(m,n)) r c,
  row_equivalent A (sub_all_rows A r c).
Proof.
  move => m n A r c. apply mx_row_transform_equiv.
  move => A' r'. rewrite //=. case Heq : (r' == r).
  constructor. case: (A r' c == 0). constructor.
  apply ero_row_equiv. constructor. by rewrite eq_sym Heq.
Qed.

(** One Step *)

(*The state of the matrix when we have computed gaussian elimination up to row r and column c*)
Definition gauss_invar {m n} (A: 'M[F]_(m, n)) (r : nat) (c: nat) :=
  (forall (r' : 'I_m), r' < r -> exists c', lead_coef A r' = Some c' /\ c' < c) /\ (*all rows up to r have leading coefficient before column c*) 
  (forall (r1 r2 : 'I_m) c1 c2, r1 < r2 -> r2 < r -> lead_coef A r1 = Some c1 -> lead_coef A r2 = Some c2 ->
    c1 < c2) /\ (*leading coefficients occur in strictly increasing columns*)
  (forall (r' : 'I_m) (c' : 'I_n), c' < c -> lead_coef A r' = Some c' -> 
     (forall (x: 'I_m), x != r' -> A x c' = 0)) /\ (*columns with leading coefficients have zeroes in all other entries*) 
  (forall (r' : 'I_m) (c' : 'I_n), r <= r' ->  c' < c -> A r' c' = 0). (*first c entries of rows >= r are all zero*)

(*One step of gaussian elimination*)
Definition gauss_one_step {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (c: 'I_n) : 'M[F]_(m, n) * (option 'I_m) :=
  match (fst_nonzero A c r) with
  | None => (A, Some r)
  | Some k =>
    let A1 := xrow k r A in
    let A2 := all_cols_one A1 c in
    let A3 := sub_all_rows A2 r c in
    (A3, insub (r.+1))
  end.

(*Results about the structure of the matrix after 1 step of gaussian elim. We use these lemmas to prove invariant
  preservation*)

(*First, in the first r rows and c columns, we did not change whether any entries are zero or not*)
Lemma gauss_one_step_beginning_submx: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (c: 'I_n) (k : 'I_m),
  (forall (r' : 'I_m) (c' : 'I_n), r <= r' ->  c' < c -> A r' c' = 0) ->
  r <= k ->
  forall (x : 'I_m) (y: 'I_n), x < r -> y < c -> 
    A x y == 0 = ((sub_all_rows (all_cols_one (xrow k r A) c) r c) x y == 0).
Proof.
  move => m n A r c k Hinv Hrk x y Hxr Hyc. rewrite sub_all_rows_val.
  case Heq : (x == r). move : Heq. have H := ltn_eqF Hxr. have : x == r = false by []. move ->. by [].
  have: (forall y, all_cols_one (xrow k r A) c x y = all_cols_one A c x y).
    move => z. rewrite !all_cols_one_val //=.
    have: (x == k) = false. apply ltn_eqF. move: Hxr Hrk. apply ltn_leq_trans.
    move => Hxkneq. have: forall j, (xrow k r A x j) = A x j.
    move => j. by rewrite xrow_val Hxkneq Heq. move => Hxrowj.
    rewrite !Hxrowj. by []. move => Hallcols.
 rewrite !Hallcols.
 have : (A x y == 0) = (all_cols_one A c x y == 0). rewrite all_cols_one_val /=. case Hac : (A x c == 0). by [].
   by rewrite GRing.mulf_eq0 GRing.invr_eq0 Hac orbF.
 case Hall : (all_cols_one A c x c == 0). 
  - by [].
  - have: all_cols_one (xrow k r A) c r y == 0. rewrite all_cols_one_val //=.
    have: forall z, xrow k r A r z = A k z. move => z. rewrite xrow_val.
    case H: (r==k). by eq_subst H. by rewrite eq_refl. move => Hxrow. rewrite !Hxrow.
    have: A k y == 0. by rewrite Hinv. move => H; eq_subst H. rewrite H.
    case: (A k c == 0) =>[//|]. by rewrite GRing.mul0r.
    move => /eqP Hallry. by rewrite Hallry GRing.subr0.
Qed.

(* Second (this holds in general for any matrix) - all entries in the resulting matrix column c are zero, except r is one*)
Lemma gauss_one_step_col_c: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (c: 'I_n) (k : 'I_m),
  A k c != 0 ->
  forall (x : 'I_m), (sub_all_rows (all_cols_one (xrow k r A) c) r c) x c = if x == r then 1 else 0.
Proof.
  move => m n A r c k Hkc x. rewrite sub_all_rows_val.
   have: xrow k r A r c = A k c. rewrite xrow_val.
    case : (r==k) /eqP => [-> //|]. by rewrite eq_refl.
  case : (x == r) /eqP => [-> //= | Hxr].
  - rewrite all_cols_one_val /=.
    move ->. by rewrite (negbTE Hkc) GRing.mulfV.
  - move => Hxrow. 
    have /eqP Hrc1: all_cols_one (xrow k r A) c r c == 1 
      by rewrite all_cols_one_val //= !Hxrow (negbTE Hkc) GRing.mulfV. 
    rewrite Hrc1. case : (all_cols_one (xrow k r A) c x c == 0) /eqP => [// |].
    move => /eqP Hneq; move: Hneq. rewrite all_cols_one_val /=.
    case Hxc : (xrow k r A x c == 0). by rewrite Hxc. move => _.
    rewrite GRing.mulfV. apply /eqP. by rewrite GRing.subr_eq0 eq_refl. apply (negbT Hxc).
Qed. 

(*Third - all entries with row >=r and col < c are still zero*)
Lemma gauss_one_step_bottom_rows: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (c: 'I_n) (k : 'I_m),
  (forall (r' : 'I_m) (c' : 'I_n), r <= r' ->  c' < c -> A r' c' = 0) ->
  fst_nonzero A c r = Some k ->
  forall (x : 'I_m) (y: 'I_n), r <= x -> y < c -> 
    (sub_all_rows (all_cols_one (xrow k r A) c) r c) x y = 0.
Proof.
  move => m n A r c k Hinv Hfst x y Hrx Hyc. move : Hfst. rewrite fst_nonzero_some_iff. move => [Hrk [Hakc Hprev]].
  rewrite sub_all_rows_val. move : Hrx.
  have: forall z, xrow k r A r z = A k z. move => z. rewrite xrow_val.
    case: (r == k) /eqP => [-> //|]. by rewrite eq_refl.
 move => Hxrow. rewrite leq_eqVlt eq_sym =>
  /orP[Hrx | Hrx]. 
  - have /eqP Hxr' : (x == r) => [//|]. subst. rewrite eq_refl all_cols_one_val /= !Hxrow.
    case (A k c == 0). by apply Hinv. by rewrite Hinv // GRing.mul0r.
  - have : x == r = false by apply gtn_eqF. move => Hxrneq. rewrite Hxrneq.
    have: all_cols_one (xrow k r A) c r y = 0. rewrite all_cols_one_val /=.
    rewrite ! Hxrow. have: A k y = 0 by apply Hinv. move ->.
    case (A k c == 0). by []. by rewrite GRing.mul0r. move ->. rewrite GRing.subr0.
    have->: all_cols_one (xrow k r A) c x y = 0. rewrite all_cols_one_val /=. move: Hrx.
    case : (x == k) /eqP => [-> // Hrx | /eqP Hxk Hrx]. 
    have->: forall z, xrow k r A k z = A r z. move => z. by rewrite xrow_val eq_refl.
    rewrite Hprev. rewrite xrow_val eq_refl. apply Hinv. by apply leqnn.
    by []. by rewrite Hrx leqnn.
    have: forall z, xrow k r A x z = A x z. move => z. rewrite xrow_val.
    by rewrite (negbTE Hxk) Hxrneq. move => Hx. rewrite !Hx.
    have->: A x y = 0. apply Hinv. by rewrite leq_eqVlt Hrx orbT. by [].
    case : (A x c == 0) => [//|]. by rewrite GRing.mul0r.
    by case (all_cols_one (xrow k r A) c x c == 0).
Qed.

(*Fourth - for all rows < r, the leading coefficient has not changed (this follows from the others)*)
Lemma gauss_one_step_prop_lead_coef: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (c: 'I_n) (k : 'I_m),
  (forall (r' : 'I_m) (c' : 'I_n), r <= r' ->  c' < c -> A r' c' = 0) ->
  (forall (r' : 'I_m), r' < r -> exists c', lead_coef A r' = Some c' /\ c' < c) ->
  fst_nonzero A c r = Some k ->
  forall (r' : 'I_m), r' < r -> 
    lead_coef A r' = lead_coef (sub_all_rows (all_cols_one (xrow k r A) c) r c) r'.
Proof.
  move => m n A r c k Hzero Hlead Hfz r' Hrr'. move : Hlead => /(_ r'). rewrite Hrr' => Hlc.
  have Hlcr' : (exists c' : 'I_n, lead_coef A r' = Some c' /\ c' < c) by apply Hlc.
  move : {Hlc} Hlcr' => [c' [Hlc Hcc']]. rewrite Hlc. have Hrk : r <= k. move : Hfz.
  rewrite fst_nonzero_some_iff. by move => [Hrk [Hakc Hprev]]. 
  have Hbeg := (gauss_one_step_beginning_submx Hzero Hrk).
  symmetry. move : Hlc. rewrite !lead_coef_some_iff. move => [Harc' Hprev].
  split. by rewrite -Hbeg. move => x Hxc'. 
  have: sub_all_rows (all_cols_one (xrow k r A) c) r c r' x == 0. rewrite -Hbeg. rewrite Hprev. all: try by [].
  move : Hxc' Hcc'. by apply ltn_trans. by move => /eqP Hs.
Qed.

(*Finally, leading coefficient of row r is c*)
Lemma gauss_one_step_r_lead: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (c: 'I_n) (k : 'I_m),
  (forall (r' : 'I_m) (c' : 'I_n), r <= r' ->  c' < c -> A r' c' = 0) ->
  fst_nonzero A c r = Some k ->
  lead_coef (sub_all_rows (all_cols_one (xrow k r A) c) r c) r = Some c.
Proof.
  move => m n A r c l Hz. rewrite lead_coef_some_iff. move => Hfst. split; move : Hfst.
  rewrite fst_nonzero_some_iff; move => [Hrl [Hlc H{H}]]. 
  have Hc := gauss_one_step_col_c r  Hlc r. by rewrite Hc eq_refl GRing.oner_neq0.
  move => Hfz x Hxc. by apply gauss_one_step_bottom_rows.
Qed.

Definition ord_bound_convert {n} (o: option 'I_n) : nat :=
  match o with
  | None => n
  | Some x => x
  end.

Lemma ord_bound_convert_plus: forall {n} (x : 'I_n),
  @ord_bound_convert n (insub (x.+1)) = (x.+1).
Proof.
  move => n x. have: x < n by []. rewrite leq_eqVlt => /orP[/eqP Heq | Hlt].
  rewrite insubF. by rewrite Heq. by rewrite Heq ltnn.
  by rewrite insubT.
Qed.

(*Note: this is a little awkward because r and c are bounded (and need to be for the functions called in
  [gauss_one_step]. However, in gaussian elimination, when we finish,
  r or c will achieve the bound. Instead of having to carry options around everywhere, we phrase the invariant
  in terms of nats, which forces us to unwrap the option with [ord_bound_convert]*)
Lemma gauss_one_step_invar: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (c: 'I_n),
  gauss_invar A r c ->
  match (gauss_one_step A r c) with
  | (A', or) => gauss_invar A' (ord_bound_convert or) (c.+1)
  end.
Proof.
  move => m n A r c Hinv. case G : (gauss_one_step A r c) => [A' or]. move : G.
  rewrite /gauss_one_step. case Fz : (fst_nonzero A c r) => [k |]; rewrite //=.
  - move => G. case : G => Ha' Hor. subst.
    move : Hinv. rewrite {1}/gauss_invar; move => [Hleadbefore [Hincr [Hzcol Hzero]]].
    rewrite /gauss_invar. rewrite !ord_bound_convert_plus. split; try split; try split.
    + move => r'. rewrite ltnS leq_eqVlt; move => /orP[Hrr' | Hrr'].
      * have : r' == r by []. rewrite {Hrr'} => /eqP Hrr'. subst. exists c.
        split. by apply gauss_one_step_r_lead. by [].
      * have Hlead2 := Hleadbefore. move : Hleadbefore => /(_ r' Hrr') [c' [Hlc Hcc']]. exists c'. split.
        by rewrite -gauss_one_step_prop_lead_coef. have : c < c.+1 by []. move : Hcc'; apply ltn_trans.
    + move => r1 r2 c1 c2 Hr12. rewrite ltnS leq_eqVlt; move => /orP[Hr2r | Hr2r].
      * have: (r2 == r) by []. move {Hr2r} => /eqP Hr2r. subst. rewrite gauss_one_step_r_lead =>[|//|//].
        rewrite -gauss_one_step_prop_lead_coef => [| //|//|//|//].
        move => Hl1 Hl2. case : Hl2 => Hl2. subst. move : Hleadbefore => /(_ r1 Hr12) [c'] . move => [Hlc Hcc'].
        rewrite Hlc in Hl1. case: Hl1. by move => H; subst.
      * have Hr1r : r1 < r. move : Hr12 Hr2r. by apply ltn_trans.
        rewrite -!gauss_one_step_prop_lead_coef; try by []. by apply Hincr. 
    + move => r' c'. rewrite ltnS leq_eqVlt; move => /orP[Hcc' | Hcc'].
      * have : (c' == c) by []. rewrite {Hcc'} => /eqP H; subst.
        (*need to show that if leading coefficient of r' is c, then r' = r*)
        case Hrr' : (r' == r).
        -- move => H{H} x Hxr. rewrite gauss_one_step_col_c.
           have ->: x == r = false. have Hreq : (r' == r) by []. eq_subst Hreq.
           by rewrite (negbTE Hxr). by []. move : Fz.
           rewrite fst_nonzero_some_iff. by move => [Hrk [Hakc H]].
        -- rewrite lead_coef_some_iff. move => [Hnonz Hbef]. move : Hnonz.
           rewrite gauss_one_step_col_c. by rewrite Hrr' eq_refl. move: Fz.
           rewrite fst_nonzero_some_iff. by move => [H1 [H2 H3]].
      * (*this time, need to show that r' < r. Cannot be greater because entry is 0*)
        case (orP (ltn_total r r')) => [/orP[Hltxr | Heqxr] | Hgtxr].
        -- rewrite lead_coef_some_iff. move => [Hnonzero  H{H}].
           move : Hnonzero. rewrite gauss_one_step_bottom_rows; try by [].
           by rewrite eq_refl. by rewrite leq_eqVlt Hltxr orbT.
        -- have H: (r == r') by []; eq_subst H.
           rewrite gauss_one_step_r_lead => [|//|//]. move => H; case : H. move => H; move : H Hcc' ->.
           by rewrite ltnn.
        -- rewrite -gauss_one_step_prop_lead_coef; try by []. move => Hl x Hxr.
           case (orP (ltn_total r x)) => [Hgeq | Hlt].
           ++ have Hrx : (r <= x). by rewrite leq_eqVlt orbC. move {Hgeq}. 
              by apply gauss_one_step_bottom_rows.
           ++ apply (elimT eqP). rewrite -gauss_one_step_beginning_submx; try by [].
              rewrite (Hzcol r'); try by []. move : Fz. rewrite fst_nonzero_some_iff. by move => [H H'].
    + move => r' c' Hrr'. rewrite ltnS leq_eqVlt; move => /orP[Hcc' | Hcc'].
      * have H: (c' == c) by []; eq_subst H. rewrite gauss_one_step_col_c.
        have: r' == r = false by apply gtn_eqF. by move ->. move: Fz. rewrite fst_nonzero_some_iff.
        by move => [H [H' H'']].
      * apply gauss_one_step_bottom_rows; try by []. by rewrite leq_eqVlt Hrr' orbT.
  - have: forall (x: 'I_m), r <= x -> A x c = 0 by apply fst_nonzero_none. move {Fz} => Fz.
    move => G. case : G => Ha' Hor. subst.
    move : Hinv. rewrite {1}/gauss_invar; move => [Hleadbefore [Hincr [Hzcol Hzero]]].
    rewrite /gauss_invar. split; try split; try split.
    + move => r' Hrr'.  move : Hleadbefore => /(_ r' Hrr') [c' [Hlc Hcc']]. exists c'. split. by [].
      have: (c < c.+1) by []. move : Hcc'. by apply ltn_trans.
    + by [].
    + move => r' c'. rewrite ltnS leq_eqVlt; move => /orP[Hcc' | Hcc'].
      have :(c' == c) by []. move => /eqP H; subst.
      case (orP (ltn_total r r')) => [Hgeq | Hlt]. 
      * have Hrx : (r <= r'). by rewrite leq_eqVlt orbC. move {Hgeq}. 
        rewrite lead_coef_some_iff Fz. rewrite eq_refl. by move => [H H']. by [].
      * move => Hlc. move : Hleadbefore => /(_ r' Hlt) [c' [Hlc' Hltcc']].
        rewrite Hlc in Hlc'. case: Hlc'. move => H; subst. move : Hltcc'. by rewrite ltnn.
      * by apply Hzcol.
    + move => r' c' Hrr'. rewrite ltnS leq_eqVlt; move => /orP[Hcc' | Hcc'].
      * have : (c' == c) by []. move => /eqP H; subst. by apply Fz.
      * by apply Hzero.
Qed.

Lemma gauss_one_step_row_equiv: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (c: 'I_n),
  row_equivalent A (gauss_one_step A r c).1.
Proof.
  move => m n A r c. case G : (gauss_one_step A r c) => [A' or]. move : G.
  rewrite /gauss_one_step. case Fz : (fst_nonzero A c r) => [k |]; rewrite //=;
  move => G; case : G => Ha' Hor; subst.
  - apply row_equivalent_trans with (B:= (all_cols_one (xrow k r A) c)).
    apply row_equivalent_trans with (B:= xrow k r A). apply ero_row_equiv. constructor.
    apply all_cols_one_row_equiv. apply sub_all_rows_row_equiv.
  - constructor.
Qed.

Import FunInd.
Import Recdef.
Import Lia.

(** Gaussian Elimination Full Algorithm*)
(*We have two versions: a fuel-based version that goes for s steps or finishes, whichever happens first, or
  a version that goes to the end. We prove equivalence when s is large enough. The second version is
  easier for proofs, but we need the first, generalized version, in GaussRestrict.v*)
Fixpoint gauss_multiple_steps {m n} (A: 'M[F]_(m, n)) (r: option 'I_m) (c: option 'I_n) s : 'M[F]_(m, n) :=
  match s with
  | 0 => A
  | s'.+1 => match r, c with
             | Some r', Some c' => match (gauss_one_step A r' c') with
                                   | (A', or) => gauss_multiple_steps A' or (insub (c'.+1)) s'
                                   end
             | _, _ => A
             end
  end.

Function gauss_all_steps {m n} (A: 'M[F]_(m, n)) (r : option 'I_m) (c : option 'I_n) 
  {measure (fun x => (n - ord_bound_convert x)%N) c} : 'M[F]_(m, n) :=
  match r, c with
  | Some r', Some c' => match (gauss_one_step A r' c') with
                        | (A', or) => gauss_all_steps A' or (insub (c'.+1))
                        end
  | _, _ => A
  end.
Proof.
move => m n A r c r' Hrr' c' Hcc' A' or. subst.
rewrite /gauss_one_step. case Fz : (fst_nonzero A c' r') => [k |]; rewrite //=;
move => G; case : G => Ha' Hor; subst; rewrite ord_bound_convert_plus;
rewrite subnS; apply Lt.lt_pred_n_n; apply (elimT ltP); by rewrite subn_gt0. 
Defined.

Lemma gauss_multiple_steps_row_none: forall {m n} (A: 'M[F]_(m, n)) oc s,
  gauss_multiple_steps A None oc s = A.
Proof.
  move => m n A or s. rewrite /gauss_multiple_steps. by case : s => [//|].
Qed.

Lemma gauss_multiple_steps_col_none: forall {m n} (A: 'M[F]_(m, n)) or s,
  gauss_multiple_steps A or None s = A.
Proof.
  move => m n A or s. rewrite /gauss_multiple_steps. case : s => [//|]. by case: or.
Qed.

(*If we give enough fuel, the result will be the same using either*)
Lemma gauss_multiple_steps_equiv: forall {m n} (A: 'M[F]_(m, n)) or (c: 'I_n) s,
  n <= s + c ->
  gauss_multiple_steps A or (Some c) s = gauss_all_steps A or (Some c).
Proof.
  move => m n A or c s. move: A or c. 
  elim : s => [A or c| s' IH/= A or c].
  - rewrite add0n/= leqNgt. have->//: c < n by [].
  - rewrite gauss_all_steps_equation. case : or =>[a Hsc|//].
    case Hg: (gauss_one_step A a c) => [A' or].
    case Hcn : (c.+1 < n).
    + rewrite insubT /=. apply IH. by rewrite /= -add1n addnA addn1.
    + rewrite insubF //= gauss_multiple_steps_col_none gauss_all_steps_equation /=.
      move: Hg. by case : or.
Qed.

(* One more needed result: [gauss_multiple_steps] is row equivalent (and therefore preserves colsub invertibility)*)
Lemma gauss_multiple_steps_row_equiv: forall {m n} (A: 'M[F]_(m, n)) or oc s,
  row_equivalent A (gauss_multiple_steps A or oc s).
Proof.
  move => m n A or oc s. move: A or oc. elim : s => [/= A or oc | s' IH /= A or oc].
  - constructor.
  - case : or; last first. constructor. move => or. case: oc; last first. constructor. move => oc.
    case Hg: (gauss_one_step A or oc) => [A' or'].
    have Hrow: row_equivalent A A'. have->: A' = (gauss_one_step A or oc).1 by rewrite Hg.
    apply gauss_one_step_row_equiv.
    apply (row_equivalent_trans Hrow). apply IH.
Qed.

Lemma gauss_multiple_steps_colsub_unitmx: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) or oc s,
  (colsub (widen_ord Hmn) A) \in unitmx =
  (colsub (widen_ord Hmn) (gauss_multiple_steps A or oc s) \in unitmx).
Proof.
  move => m n A Hmn or oc s. erewrite (row_equivalent_unitmx_iff); last first. apply colsub_row_equivalent.
  apply gauss_multiple_steps_row_equiv. by [].
Qed.

(*After we run this function, the gaussian invariant is satisfied for either m or n*)
(*We will handle the None case separately - (ie, if m = 0 or n = 0*)
Lemma gauss_all_steps_invar: forall {m n} (A: 'M[F]_(m, n)) (r : option 'I_m) (c : option 'I_n),
  gauss_invar A (ord_bound_convert r) (ord_bound_convert c) ->
  (exists r', r' <= m /\ gauss_invar (gauss_all_steps A r c) r' n) \/
  (exists c', c' <= n /\ gauss_invar (gauss_all_steps A r c) m c').
Proof.
  move => m n.
  apply (@gauss_all_steps_ind m n (fun (B : 'M[F]_(m, n)) (r' : option 'I_m) (c' : option 'I_n) (C : 'M_(m, n)) =>
    gauss_invar B (ord_bound_convert r') (ord_bound_convert c') ->
    (exists r'' : nat, r'' <= m /\ gauss_invar C r'' n) \/
    (exists c'' : nat, c'' <= n /\ gauss_invar C m c''))).
  - move => A r c r' Hrr' c' Hcc' A' or Hgo Hind; subst.
    rewrite /ord_bound_convert. move => Hinv.
    apply Hind. have H := gauss_one_step_invar Hinv. rewrite Hgo in H.
    by rewrite ord_bound_convert_plus.
  - move => A r c x Hrx x' Hcx'; subst. case : x => a. case : x' => b.
    by []. rewrite /ord_bound_convert. move => H. left. exists a. split.
    rewrite leq_eqVlt. have: a < m  by []. move ->. by rewrite orbT. by [].
    rewrite {1}/ord_bound_convert. move => Hg. right. exists (ord_bound_convert x').
    split; try by []. rewrite /ord_bound_convert. move : Hg. case : x'.
    move => b Hg. rewrite leq_eqVlt. have: b < n by []. move ->. by rewrite orbT.
    by rewrite leqnn.
Qed.

Lemma gauss_all_steps_row_equiv: forall {m n} (A: 'M[F]_(m, n)) (r : option 'I_m) (c : option 'I_n),
  row_equivalent A (gauss_all_steps A r c).
Proof.
  move => m n. apply (@gauss_all_steps_ind m n (fun B r' c' C => row_equivalent B C)).
  - move => A r c r' Hrr' c' Hcc' A' or Hg; subst.
    apply (@row_equivalent_trans _ _ _ A'). have Hrow := (gauss_one_step_row_equiv A r' c').
    rewrite Hg in Hrow. apply Hrow.
  - constructor.
Qed.

Ltac lt_zero := intros;
  match goal with
  | [H: is_true (?x < 0) |- _] => by rewrite ltn0 in H
  end.

(*At the beginning, the matrix satisfies the invariant*)
Lemma gauss_invar_init : forall {m n} (A: 'M[F]_(m, n)),
  gauss_invar A 0%N 0%N.
Proof.
  move => m n A. rewrite /gauss_invar. repeat(split; try lt_zero).
Qed.

(*Now, make all leading coefficients 1*)
Definition all_lc_1 {m n} (A: 'M[F]_(m, n)) :=
  foldr (fun x acc => match (lead_coef A x) with
                      | None => acc
                      | Some l => sc_mul acc (A x l)^-1 x
                      end) A (ord_enum m).

(*The following lemma is helpful*)
Lemma all_lc_1_val: forall {m n} (A: 'M[F]_(m,n)) i j,
  all_lc_1 A i j = match (lead_coef A i) with
                    | None => A i j
                    | Some l => (A i l)^-1 * (A i j)
                  end.
Proof.
  move => m n A i j. rewrite /all_lc_1. rewrite mx_row_transform.
  - case: (lead_coef A i) => [|//]. move => a. by rewrite /sc_mul mxE eq_refl.
  - move => A' i' j' r Hir'. case : (lead_coef A r) => [|//].
    move => a. rewrite /sc_mul mxE. have : i' == r = false by move : Hir';  case (i' == r).
    by move ->.
  - move => A' B' r' Hab H{H} j'. case : (lead_coef A ); last apply Hab. move => a.
    by rewrite !/sc_mul !mxE !eq_refl Hab.
  - apply ord_enum_uniq.
  - apply mem_ord_enum.
Qed.

(*[all_lc_1] does not change the zero entries of the matrix*)
Lemma all_lc_1_zeroes: forall {m n} (A: 'M[F]_(m, n)) x y,
  (A x y == 0) = ((all_lc_1 A) x y == 0).
Proof.
  move => m n A x y. rewrite all_lc_1_val. case Hlc : (lead_coef A x) => [k |].
  - move : Hlc. rewrite lead_coef_some_iff; move => [Haxk H{H}].
    rewrite GRing.mulf_eq0. have: ((A x k)^-1 == 0 = false). rewrite GRing.invr_eq0.
    move : Haxk. by case: (A x k == 0). by move ->.
  - by [].
Qed.

(*[all_lc_1] does not change leading coefficients*)
Lemma all_lc_1_lcs:  forall {m n} (A: 'M[F]_(m, n)) x,
  lead_coef A x = lead_coef (all_lc_1 A) x.
Proof.
  move => m n A x. case Hlorg : (lead_coef A x) => [c|]; symmetry; move : Hlorg.
  - rewrite !lead_coef_some_iff => [[Haxc Hbef]]. split. move: Haxc. by rewrite all_lc_1_zeroes.
    move => x' Hxc. apply (elimT eqP). rewrite -all_lc_1_zeroes. apply (introT eqP).
    by apply Hbef.
  - rewrite !lead_coef_none_iff. move => Hall x'. apply (elimT eqP). rewrite -all_lc_1_zeroes. by rewrite Hall.
Qed. 

(*Together, this implies that [gauss_invar] is preserved*)
Lemma all_lc_1_gauss_invar: forall {m n} (A: 'M[F]_(m, n)) r c,
  gauss_invar A r c ->
  gauss_invar (all_lc_1 A) r c.
Proof.
  move => m n A r c. rewrite /gauss_invar; move => [Hleadbefore [Hincr [Hzcol Hzero]]].
  repeat(try split).
  - move => r' Hrr'. rewrite -all_lc_1_lcs. by apply Hleadbefore.
  - move => r1 r2 c1 c2 Hr12 Hr2r. rewrite -!all_lc_1_lcs. by apply Hincr.
  - move => r' c' Hcc'. rewrite -all_lc_1_lcs. move => Hlc Hx Hxr. apply (elimT eqP). 
    rewrite -all_lc_1_zeroes. apply (introT eqP). by apply Hzcol with(r' := r').
  - move => r' c' Hrr' Hcc'. apply (elimT eqP). rewrite -all_lc_1_zeroes. apply (introT eqP).
    by apply Hzero.
Qed.

(*Finally, this in fact does set all leading coefficients to one*)
Lemma all_lc_1_sets_lc: forall {m n} (A: 'M[F]_(m, n)) x c,
  lead_coef A x = Some c ->
  (all_lc_1 A) x c = 1.
Proof.
  move => m n A x c Hlc. rewrite all_lc_1_val Hlc. move : Hlc; rewrite lead_coef_some_iff => [[Hnz H{H}]].
  by rewrite GRing.mulVf.
Qed.

(*Additionally, the resulting matrix is row equivalent*)
Lemma all_lc_1_row_equiv: forall {m n} (A: 'M[F]_(m, n)),
  row_equivalent A (all_lc_1 A).
Proof.
  move => m n A. apply mx_row_transform_equiv. move => A' r.
  case Hlc : (lead_coef A r) => [k |].
  - apply ero_row_equiv. constructor. move : Hlc. rewrite lead_coef_some_iff => [[Hnz H{H}]].
    by apply GRing.invr_neq0.
  - constructor.
Qed.

(*Putting it all together. First, we defined reduced row echelon form*)
Definition row_echelon {m n} (A: 'M[F]_(m, n)) :=
  (*all rows of zeroes are at the bottom*)
  (exists r, r <= m /\ forall (x: 'I_m), (lead_coef A x == None) = (r <= x)) /\
  (*all leading coefficients appear in strictly increasing order*)
  (forall (r1 r2 : 'I_m) c1 c2, r1 < r2 -> lead_coef A r1 = Some c1 -> lead_coef A r2 = Some c2 ->
    c1 < c2) /\
  (*each column with a leading coefficient has zeroes in all other columns*)
  (forall (r' : 'I_m) (c' : 'I_n), lead_coef A r' = Some c' -> 
     (forall (x: 'I_m), x != r' -> A x c' = 0)).

(*Reduced row echelon add the requirements that all leading coefficients are 1*)
Definition red_row_echelon {m n} (A: 'M[F]_(m, n)) :=
  row_echelon A /\ (forall (r: 'I_m) c, lead_coef A r = Some c -> A r c = 1).

(*We prove in a separate lemma that the result of [gauss_all_steps] is in row echelon form*)
Lemma end_invar_ref: forall {m n} (A: 'M[F]_(m, n)),
  (exists r', r' <= m /\ gauss_invar A r' n) \/
  (exists c', c' <= n /\ gauss_invar A m c') ->
  row_echelon A.
Proof.
  move => m n A. (*need to handle each case separately, maybe there is a way to make it nicer*)
  move => [ [r' [Hrm Hinv]] |[c' [Hcn Hinv]]]; move : Hinv; rewrite /gauss_invar; 
  move => [Hleadbefore [Hincr [Hzcol Hzero]]]; rewrite /row_echelon.
  - (*we use the first condition in multiple places, so we prove it separately*)
    have Hlc : (forall (x : 'I_m), (lead_coef A x == None) = (r' <= x)). 
    move => x. case Hlt : (r' <= x).  
    apply (introT eqP). rewrite lead_coef_none_iff. move => x'. by apply Hzero.
    have Hxr' : (x < r'). rewrite ltnNge. by rewrite Hlt. move {Hlt}.
    move : Hleadbefore => /(_ x Hxr') [c [Hlc Hcn]]. by rewrite Hlc.
    repeat(split).
    + exists r'. split. by []. apply Hlc.
    + move => r1 r2 c1 c2 Hr12 Hl1 Hl2. have Hr2r: (r2 < r').
      case Hr : (r2 < r'). by []. have : r' <= r2 by rewrite leqNgt Hr.
      move {Hr} => Hr. rewrite -Hlc in Hr. rewrite Hl2 in Hr. by [].
      by apply (Hincr r1 r2).
    + move => r1 c1 Hlr1. by apply Hzcol.
  - repeat(split).
    + exists m. split. apply leqnn. move => x. have Hx: x < m by [].
      move : Hleadbefore => /(_ x Hx) [c [Hlcx Hcc']]. rewrite Hlcx.
      have: m <= x = false. have : x < m by []. rewrite ltnNge. by case : (m <= x). by move ->.
    + move => r1 r2 c1 c2 Hr12. by apply Hincr.
    + move => r c Hlr. apply Hzcol => [|//]. have Hr : r < m by [].
      move : Hleadbefore => /(_ r Hr) [c1 [Hlr1 Hcc2]]. rewrite Hlr1 in Hlr. case: Hlr.
      by move => Hc1; subst.
Qed.

(*The full function*)
Definition gaussian_elim {m n} (A: 'M[F]_(m, n)) :=
  all_lc_1 (gauss_all_steps A (insub 0%N) (insub 0%N)).

Lemma insub_zero: forall n,
  @ord_bound_convert n (insub 0%N) = 0%N.
Proof.
  move => n. case Hn : (0 < n).
  by rewrite insubT. have: (n == 0%N) by rewrite eqn0Ngt Hn. move => /eqP H; subst.
  by rewrite insubF.
Qed.

Lemma gaussian_elim_rref: forall {m n} (A: 'M[F]_(m, n)),
  red_row_echelon (gaussian_elim A).
Proof.
  move => m n A. rewrite /red_row_echelon. rewrite /gaussian_elim. split.
  2 : { move => r c. rewrite -all_lc_1_lcs. by apply all_lc_1_sets_lc. }
  apply end_invar_ref. 
  have : (exists r' : nat, r' <= m /\ gauss_invar (gauss_all_steps A (insub 0%N) (insub 0%N)) r' n) \/
  (exists c' : nat, c' <= n /\ gauss_invar (gauss_all_steps A (insub 0%N) (insub 0%N)) m c').
  apply gauss_all_steps_invar. rewrite !insub_zero. by apply gauss_invar_init.
  move => [[r' [Hl1 Hl2]] |[c' [Hr1 Hr2]]]. left. exists r'. split. by [].
  by apply all_lc_1_gauss_invar. right. exists c'. split. by [].  by apply all_lc_1_gauss_invar.
Qed.

Lemma gaussian_elim_row_equiv: forall {m n} (A: 'M[F]_(m, n)),
  row_equivalent A (gaussian_elim A).
Proof.
  move => m n A. rewrite /gaussian_elim. 
  apply (@row_equivalent_trans _ _ _ (gauss_all_steps A (insub 0%N) (insub 0%N))).
  apply gauss_all_steps_row_equiv. apply all_lc_1_row_equiv.
Qed.

(** Some intermediate results about the structure of matrices during Gaussian Elimination*)


(*In order to prove the next two lemmas, we want to use induction on ordinals up to a fixed bound. This is
  complicated, since there are lots of proofs obligations to ensure that all ordinals are valid. Additionally,
  we want to reason both forward and backward, so we provide two versions of induction over ordinals*)

(*Enables us to construct an ordinal of type 'I_n with x.+1*)
Lemma ltn_succ: forall r n x, r < n -> x < r -> x.+1 < n.
Proof.
  move => r n x Hrn Hxr1. move : Hxr1 Hrn. apply leq_ltn_trans.
Qed.

Definition ord_widen_succ r n (Hrn : r < n) (x: 'I_r) : 'I_n :=
  Ordinal (ltn_succ Hrn (ltn_ord x)).

(*If P holds on r and whenever P holds on (n.+1), P holds on n, then P holds on all values of n <= r*)
Lemma ord_ind_bound_rev: forall (m: nat) (r: 'I_m) (P: 'I_m -> Prop),
  P r ->
  (forall (n: 'I_m) (Hnr : n < r), (P (Ordinal (ltn_succ (ltn_ord r) Hnr)) -> P n)) ->
  (forall (n: 'I_m), n <= r -> P n).
Proof.
  move => m r P Hpr Hind n. case : n. move => n.
  remember (r - n)%N as x. move : n Heqx. elim : x.
  - move => n Hrn Hmn Hr. have: r <= n by rewrite /leq -Hrn. move {Hrn} => Hrn.
    have : n <= r by []. move => Hnr.
    have : (nat_of_ord r == n)  by rewrite eqn_leq Hrn Hnr. move => Hnat.
    have: (r == Ordinal Hmn) by []. move => /eqP Hord. by rewrite -Hord.
  - move => n Hind' n' Hsub Hnm'. rewrite leq_eqVlt => /orP[Heq | Hlt].
    + have: (Ordinal Hnm' == r) by []. by move => /eqP H; subst.
    + apply (Hind _ Hlt). apply Hind'. by rewrite subnS -Hsub -pred_Sn.
      have : (nat_of_ord (Ordinal (ltn_succ (ltn_ord r) Hlt)) == n'.+1) by []. move => /eqP Hord.
      by rewrite Hord.
Qed.

(*Likewise, if P holds on 0 and whenever P holds on n < r, P holds on n.+1, then P holds on all values of n <= r*)
Lemma ord_ind_bound: forall (m: nat) (r: 'I_m) (P: 'I_m -> Prop),
  P (Ordinal (ord_nonzero r)) ->
  (forall (n: 'I_m) (Hnr: n < r), P n -> P (Ordinal (ltn_succ (ltn_ord r) Hnr))) ->
  (forall (n: 'I_m), n <= r -> P n).
Proof.
  move => m r P Hzero Hind n. case : n. move => n. elim : n.
  - move => Hm0 Hr. have : ((Ordinal Hm0) == (Ordinal (ord_nonzero r))) by []. move => /eqP Hord. 
    by rewrite Hord.
  - move => n Hind' Hn1 Hr.
    have Hnm : n < m by apply (ltn_trans (ltnSn n) Hn1).
    have Hnr : Ordinal Hnm <= r. have Hn1r: n.+1 <= r by []. have : n <= r by apply (ltnW Hn1r). by [].
    have Hpn: P (Ordinal Hnm) by apply (Hind' Hnm Hnr). have Hnr' : n < r by []. 
    have Hpsuc : P (Ordinal (ltn_succ (ltn_ord r) Hnr')) by apply (Hind (Ordinal Hnm) Hnr' Hpn).
    have Ho1: nat_of_ord (Ordinal (ltn_succ (ltn_ord r) Hnr')) == n.+1 by [].
    have Ho2: nat_of_ord (Ordinal Hn1) == n.+1 by []. 
    have: (Ordinal (ltn_succ (ltn_ord r) Hnr')) == (Ordinal Hn1) by []. move => /eqP Hord. by rewrite -Hord.
Qed.

(*Now we want to prove that, if [gauss_invar r r] holds, the upper left r x r submatrix is a diagonal matrix
  with nonzero entries along the diagonal. In order to do this, we first want to prove that, for each row r' < r,
  lead_coef A r' = r'. This relies on a piegonhole-type argument which is difficult to prove in Coq. So we work
  in two parts: first we use forward induction to prove that lead_coef A r' >= r', then we use backwards induction
  to prove that lead_coef A r' = r' (using the previous result)*)

(*If [gauss_invar r c] holds, then for all r' < r, r' <= lead_coef r'*)
Lemma gauss_invar_lead_coef_geq: forall {m n} (A: 'M[F]_(m, n)) r c,
  r <= m ->
  gauss_invar A r c ->
  (forall (r' : 'I_m), r' < r -> exists c', lead_coef A r' = Some c' /\ r' <= c').
Proof.
  move => m n A r c Hrm. rewrite /gauss_invar; move => [Hleadbefore [Hincr [Hzcol Hzero]]].
  case: (r == 0)%N /eqP => [-> //| /eqP Hr0] .
  have: 0 < r. case (orP (ltn_total r 0)) => [/orP[Hlt // | Heq] | Hgt //]. by rewrite Heq in Hr0. 
  move => {} Hr0. have Hr1m: r.-1 < m by rewrite prednK.
  have: (forall (r' : 'I_m), r' <= Ordinal Hr1m -> exists c' : 'I_n, lead_coef A r' = Some c' /\ r' <= c').
  apply ord_ind_bound.
  + move : Hleadbefore. move => /(_ (Ordinal (ord_nonzero (Ordinal Hr1m))) Hr0) [c' [Hlc Hbound]].
    exists c'. by [].
  + move => n' Hnr' [c' [Hlc Hcbound]].
    have Hb : (Ordinal (ltn_succ (ltn_ord (Ordinal Hr1m)) Hnr')) < r. 
    have Hnrsuc: n'.+1 < r. have Hnrpred: n' < r.-1 by []. by rewrite -ltn_predRL. by [].
    move : Hleadbefore. move => /(_ _ Hb) [c'' [Hlc' Hbound']].
    exists c''. split. by []. 
    have Hcc': c' < c''. eapply Hincr. 3: apply Hlc. 3: apply Hlc'. by []. by [].
    have Hnc': n' < c'' by apply (leq_ltn_trans Hcbound Hcc'). by [].
  + move => Halt r' Hrr'. apply Halt. by rewrite -ltn_pred.
Qed.

(*If [gauss_invar r r] holds, then for all r' < r, r' == lead_coef r'*)
Lemma gauss_invar_square_lc: forall {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (r: nat),
  r <= m ->
  gauss_invar A r r ->
  (forall (r': 'I_m), r' < r -> lead_coef A r' = Some (widen_ord Hmn r')).
Proof.
  move => m n A Hmn r Hrm Hinv.
  case: (r == 0)%N /eqP => [-> //| /eqP Hr0] .
  have: 0 < r. case (orP (ltn_total r 0)) => [/orP[Hlt // | Heq] | Hgt //]. by rewrite Heq in Hr0.
  move => {} Hr0. have Hr1m: r.-1 < m by rewrite prednK.
  have Halt: (forall (r' : 'I_m), r' <= Ordinal Hr1m -> lead_coef A r' = Some (widen_ord Hmn r')).
  + have Hrpred: (Ordinal Hr1m) < r by rewrite ltn_predL.  apply ord_ind_bound_rev.
    * have: (exists c', lead_coef A (Ordinal Hr1m) = Some c' /\ (Ordinal Hr1m) <= c'). 
      by apply (gauss_invar_lead_coef_geq Hrm Hinv).
      move => [c' [Hlc Hlb]]. rewrite Hlc. f_equal.  
      move : Hinv; rewrite /gauss_invar; move => [Hleadbefore [Hincr [Hzcol Hzero]]].
      move : Hleadbefore. move => /(_ _ Hrpred) [c'' [Hlc' Hcr]].
      have: (c' = c''). rewrite Hlc in Hlc'. by case: Hlc'. move => Hcc'; subst. move {Hlc'}.
      rewrite ltn_pred in Hcr => [| //]. apply (elimT eqP).
      have: (nat_of_ord c'') == r.-1. rewrite eqn_leq. have: r.-1 <= c'' by []. have: c'' <= r.-1 by [].
      move ->. by move ->. by [].
    * move => n' Hnr1 Hlc. remember (Ordinal (ltn_succ (ltn_ord (Ordinal Hr1m)) Hnr1)) as on1 eqn : Hon1.
      have Hnr' : n' < r by apply (ltn_trans Hnr1 Hrpred). 
      have: (exists c', lead_coef A n' = Some c' /\ n' <= c').
      by apply (gauss_invar_lead_coef_geq Hrm Hinv). move => [c' [Hlc' Hb]].
      move : Hinv; rewrite /gauss_invar; move => [Hleadbefore [Hincr [Hzcol Hzero]]].
      have: c' < widen_ord Hmn on1. apply (Hincr n' on1). by rewrite Hon1 ltnSn.
      rewrite Hon1. have: n'.+1 < r. have H: n' < r.-1 by []. by rewrite -ltn_predRL. by [].
      by []. by []. move => Hcub. have: c' < n'.+1 by rewrite Hon1 in Hcub. move => Hcn'.
      have: c' <= n' by []. move => {Hcn'} Hcub.
      have: nat_of_ord c' == n' by rewrite eqn_leq Hcub Hb. rewrite Hlc'. 
      move => Hcn. f_equal. have: c' == widen_ord Hmn n' by []. by move => /eqP H.
  + move => r' Hrr'. apply Halt. by rewrite -ltn_pred.
Qed.

(*What we really want to show: when we are at step r in Gaussian elimination, the first r x r matrix
  in the upper left corner is a diagonal matrix with nonzero entries along the diagonal*)
Lemma gauss_invar_square_id: forall {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (r: nat),
  r <= m ->
  gauss_invar A r r ->
  (forall (x: 'I_m) (y: 'I_n), x < r -> y < r -> (A x y == 0) = (nat_of_ord x != nat_of_ord y)).
Proof.
  move => m n A Hmn r Hrm Hinv x y Hxr Hyr. 
  have: lead_coef A x = Some (widen_ord Hmn x) by apply (gauss_invar_square_lc _ Hrm Hinv).
  move => Hlc. 
  case Hxy : (nat_of_ord x == nat_of_ord y).
  - move : Hlc. rewrite lead_coef_some_iff; move => [Ha H{H}].
    have: widen_ord Hmn x == y by []. move => /eqP Hw; subst.
    move : Ha. by case: (A x (widen_ord Hmn x) == 0).
  - have: lead_coef A (Ordinal (ltn_leq_trans Hyr Hrm)) = Some y.
    rewrite (gauss_invar_square_lc _ Hrm Hinv). f_equal. apply (elimT eqP).
    have: nat_of_ord (widen_ord Hmn (Ordinal (ltn_leq_trans Hyr Hrm))) == nat_of_ord y by []. by [].
    by []. move => {} Hlc.
    move : Hinv; rewrite /gauss_invar; move => [Hleadbefore [Hincr [Hzcol Hzero]]].
    have: A x y = 0. apply (Hzcol (Ordinal (ltn_leq_trans Hyr Hrm))); try by []. 
    case Hxyeq: (x == Ordinal (ltn_leq_trans Hyr Hrm)) => [|//].
    have: (nat_of_ord (Ordinal (ltn_leq_trans Hyr Hrm)) == nat_of_ord y) by [].
    move => /eqP Hyy. have: (nat_of_ord x == nat_of_ord y). rewrite -Hyy. by []. move => Hxy'.
    move : Hxy' Hxy. by move ->. move ->. by rewrite eq_refl.
Qed.

(*If a matrix has a row of zeroes, then it is not invertible*)
Lemma row_zero_not_unitmx: forall {m} (A: 'M[F]_(m, m)) (r: 'I_m),
  (forall (c: 'I_m), A r c = 0) ->
  A \notin unitmx.
Proof.
  move => m A r Hzero. case Hin : (A \in unitmx) => [|//]. 
  have: (A *m (invmx A) = 1%:M). apply mulmxV. apply Hin.
  move => Hinv {Hin}.
  have :  1%:M r r = GRing.one F by rewrite id_A eq_refl.
  rewrite -Hinv. have: (A *m invmx A) r r = 0. rewrite mxE big1 =>[//|].
  move => i H{H}. by rewrite Hzero GRing.mul0r. move ->.
  move => H. have: 1 != GRing.zero F by apply GRing.oner_neq0. by rewrite H eq_refl.
Qed.


(** Properties of Row Echelon Form*)

(*We want to show: if m <= n and if the first m x m submatrix is invertible, then the resulting matrix looks like
  I_m | W*)

Lemma lead_coef_colsub: forall {m n} (Hmn: m <= n) (A: 'M[F]_(m, n)) r c,
  lead_coef (colsub (widen_ord Hmn) A) r = Some c ->
  lead_coef A r = Some (widen_ord Hmn c).
Proof.
  move => m n Hmn A r c.  rewrite !lead_coef_some_iff /=; move => [Harc Hallz]. split. by rewrite mxE in Harc.
  move => x Hx. have Hcm: c < m by []. have Hxm: x < m by apply (ltn_trans Hx).
  have Hcond: (Ordinal Hxm) < c by []. apply Hallz in Hcond. rewrite mxE in Hcond.
  by have<-: (widen_ord Hmn (Ordinal Hxm)) = x by apply ord_inj.
Qed.

(*We can disreguard the trivial case of m = 0*)
Lemma matrix_zero_rows: forall {n} (A B: 'M[F]_(0, n)), A = B.
Proof.
  move => n A B. rewrite -matrixP /eqrel. move => x y. have: x < 0 by []. by rewrite ltn0.
Qed.

(*For any matrix in row reduced echelon form, either the first m x m submatrix is the identity
  or there is a row where the first m values are 0*)
Lemma rref_colsub_cases: forall {m n} (Hmn: m <= n) (A: 'M[F]_(m, n)),
  red_row_echelon A ->
  colsub (widen_ord Hmn) A = 1%:M \/ (exists (r: 'I_m), forall (c: 'I_n), c < m -> A r c = 0).
Proof.
  move => m n Hmn A [[[b [Hb Hzeroes]] [Hinc Hcols]] Hlc].
  have: 0 <= m by []. rewrite leq_eqVlt => /orP[/eqP Hm0 | Hmgt].
  - subst. left. apply matrix_zero_rows.
  - case Hlcm: (lead_coef A (pred_ord Hmgt)) =>[c|]. (*case on leading coefficient of last row*)
    + case : (orP (ltn_leq_total c m)) => [Hin | Hout]; last first.
      * right. exists (pred_ord Hmgt). move => c' Hc'. move: Hlcm. rewrite lead_coef_some_iff => [[Hc Hall]].
        apply Hall. apply (ltn_leq_trans Hc' Hout).
      * (*the hard case: WTS that the LHS is the identity matrix*)
        have Hinv: gauss_invar (colsub (widen_ord Hmn) A) m m. {
        rewrite /gauss_invar. repeat(split).
        - move => r' Hrn'. have : r' <= m.-1 by rewrite -ltn_pred.
          rewrite leq_eqVlt => /orP[/eqP Hrm | Hrm].
          + exists (Ordinal Hin). split. move: Hlcm. rewrite !lead_coef_some_iff => [[Hrc Hall]].
            have Hr': r' = (pred_ord Hmgt) by apply ord_inj.
            have Hc: (widen_ord Hmn (Ordinal Hin)) = c by apply ord_inj.
            split. by rewrite mxE Hr' Hc. move => x Hx. rewrite mxE Hr'. by apply Hall. by [].
          + case Hlc': (lead_coef A r') =>[col |].
            * have Hcol: col < m. have Hcol: col < c. have Hr' : (r' < pred_ord Hmgt) by [].
              apply (Hinc _ _ _ _ Hr' Hlc' Hlcm). by apply (ltn_trans Hcol).
              exists (Ordinal Hcol). split; try by [].
              move: Hlc'. rewrite !lead_coef_some_iff => [[Hrc Hall]]. split.
              rewrite mxE. by have->: (widen_ord Hmn (Ordinal Hcol)) = col by apply ord_inj.
              move => x Hx. rewrite mxE. by apply Hall.
            * have Hbr: b <= r'. rewrite -(Hzeroes r'). by apply /eqP.
              have Hrb1: b <= (pred_ord Hmgt). apply ltnW. by apply (leq_ltn_trans Hbr).
              rewrite -Hzeroes in Hrb1. by rewrite Hlcm in Hrb1.
        - move => r1 r2 c1 c2 Hr12 Hr2m Hlc1 Hlc2. apply lead_coef_colsub in Hlc1.
          apply lead_coef_colsub in Hlc2. apply (Hinc _ _ _ _ Hr12 Hlc1 Hlc2).
        - move => r' c' Hc' Hlcw x Hxr. rewrite mxE. apply (Hcols r'). by apply lead_coef_colsub.
          by [].
        - move => r' c' Hr'. rewrite leqNgt in Hr'. have Hr'': r' < m by []. by rewrite Hr'' in Hr'. }
        have Hlcs: (forall (r': 'I_m), lead_coef (colsub (widen_ord Hmn) A) r' = Some r').
          move => r'.  rewrite (gauss_invar_square_lc (leqnn m) (leqnn m) Hinv). f_equal.
          by apply ord_inj. by []. left.
        rewrite -matrixP => x y. rewrite mxE id_A.
        case : (x == y) /eqP => [-> // | Hxy].
        -- move : Hlcs => /(_ y) Hlcs. apply Hlc. by apply lead_coef_colsub.
        -- move: Hlcs => /(_ y) Hlcs. apply (Hcols y). by apply lead_coef_colsub. by apply /eqP.
    + right. move: Hlcm; rewrite lead_coef_none_iff => Hzero. exists (pred_ord Hmgt). move => c Hc. apply Hzero.
Qed.

(*A few corollaries of this, first, the first m columns of a rref matrix are the identity iff the first m
  columns are invertible*)
Lemma rref_colsub_id: forall {m n} (Hmn: m <= n) (A: 'M[F]_(m, n)),
  red_row_echelon A ->
  colsub (widen_ord Hmn) A \in unitmx = (colsub (widen_ord Hmn) A == 1%:M).
Proof.
  move => m n Hmn A Hred. apply (rref_colsub_cases Hmn) in Hred. case : Hred.
  - move ->. by rewrite unitmx1 eq_refl.
  - move => [r Hzero]. 
    have Hinv: (colsub (widen_ord Hmn) A \notin unitmx). { apply (row_zero_not_unitmx (r:=r)).
      move => c. rewrite mxE. apply Hzero. by have: c < m by []. }
    rewrite (negbTE Hinv). 
    case Hid: (colsub (widen_ord Hmn) A == 1%:M).
    + apply (elimT eqP) in Hid. have : colsub (widen_ord Hmn) A r r = 1%:M r r by rewrite Hid.
      rewrite id_A mxE eq_refl Hzero. move => /eqP H01. rewrite eq_sym in H01. by rewrite GRing.oner_eq0 in H01.
      by have : r < m by [].
    + by [].
Qed.

(*We can extend this to gaussian elimination*)
(*The first m x m submatrix is invertible exactly when the first m x m submatrix
  of the gaussian elimination result is the identity*)
Lemma gaussian_elim_identity: forall {m n} (Hmn: m <= n) (A: 'M[F]_(m, n)),
  (colsub (widen_ord Hmn) A) \in unitmx =
   (colsub (widen_ord Hmn) (gaussian_elim A) == 1%:M).
Proof.
  move => m n Hmn A.
  erewrite (row_equivalent_unitmx_iff); last first. apply colsub_row_equivalent. apply gaussian_elim_row_equiv.
  apply rref_colsub_id. apply gaussian_elim_rref.
Qed.

(*Another version that is easier to use for some things*)
Lemma gaussian_elim_identity_val: forall {m n} (Hmn: m <= n) (A: 'M[F]_(m, n)),
  (colsub (widen_ord Hmn) A) \in unitmx ->
  forall (r : 'I_m) (c : 'I_n), c < m -> gaussian_elim A r c = if nat_of_ord r == nat_of_ord c then 1 else 0.
Proof.
  move => m n Hmn A. rewrite gaussian_elim_identity. move => /eqP Hid r c Hcm.
  have: colsub (widen_ord Hmn) (gaussian_elim A) r (Ordinal Hcm) = if (nat_of_ord r == nat_of_ord c) then 1 else 0
  by rewrite Hid id_A. rewrite mxE /=. have->: (widen_ord Hmn (Ordinal Hcm)) = c by apply ord_inj.
  by [].
Qed. 

(*For the special case of n x n matrices, A \in unitmx exactly when gaussian_elim A = 1*)
Lemma colsub_square_mx: forall {m} (A: 'M[F]_m),
  colsub (widen_ord (leqnn m)) A = A.
Proof.
  move => m A. rewrite -matrixP => i j. rewrite mxE /=.
  f_equal. by apply ord_inj.
Qed.

Lemma unitmx_iff_gauss_id: forall {n} (A: 'M[F]_n),
  A \in unitmx = (gaussian_elim A == 1%:M).
Proof.
  move => n A. rewrite -{1}(colsub_square_mx A) -(colsub_square_mx (gaussian_elim A)).
  apply gaussian_elim_identity.
Qed.

(*We can use Gaussian elimination to find inverses: if we have the matrix [A | I] and A is invertible,
  if we row reduce it, we get [I | B], where B = A^-1*)

Definition find_invmx {n} (A: 'M[F]_n) :=
  rsubmx (gaussian_elim (row_mx A 1%:M)).

(*Convert between [colsub] and [lsubmx]*)
Lemma colsub_lsubmx: forall {n} (A: 'M[F]_(n, n + n)),
  colsub (widen_ord (leq_addr n n)) A = lsubmx A.
Proof.
  move => n A. rewrite lsubmxEsub /= -matrixP => x y.
  rewrite !mxE /=. f_equal. by apply ord_inj.
Qed. 

(*This is another way of stating [gaussian_elim_identity]*)
Lemma gaussian_id_structure: forall {n} (A B: 'M[F]_(n, n)),
  A \in unitmx ->
  exists C, gaussian_elim (row_mx A B) = row_mx 1%:M C.
Proof.
  move => n A B Hinv.
  exists (rsubmx (gaussian_elim (row_mx A B))).
  have->:1%:M = lsubmx (gaussian_elim (row_mx A B)).
  pose proof (gaussian_elim_identity (leq_addr n n) (row_mx A B)) as Hgaus.
    move: Hgaus. rewrite !colsub_lsubmx row_mxKl Hinv => Hid. apply /eqP.
    by rewrite eq_sym -Hid. 
  by rewrite hsubmxK.
Qed.

(*This may exist in mathcomp but I couldn't find it*)
Lemma invmx_uniq: forall {n} (A B: 'M[F]_n),
  B *m A = 1%:M ->
  B = invmx A.
Proof.
  move => n A B Hmul. have Ha: A \in unitmx by apply (mulmx1_unit Hmul).
  have: B *m A *m (invmx A) = invmx A by rewrite Hmul mul1mx.
  by rewrite -mulmxA mulmxV // mulmx1.
Qed.

Lemma gaussian_finds_invmx: forall {n} (A: 'M[F]_(n, n)),
  A \in unitmx ->
  find_invmx A = invmx A.
Proof.
  move => n A Hinv. rewrite /find_invmx.
  pose proof (@gaussian_id_structure n A 1%:M Hinv ) as [C Hrr]. rewrite Hrr row_mxKr.
  have Hre: row_equivalent (row_mx A 1%:M) (row_mx 1%:M C).
  rewrite -Hrr. apply gaussian_elim_row_equiv. apply row_equivalent_mul_unit in Hre.
  move: Hre => [E /andP[He /eqP Hmul]]. move: Hmul.
  rewrite mul_mx_row => Hrow. apply eq_row_mx in Hrow. case: Hrow => [Hea Hce].
  symmetry in Hea. apply invmx_uniq in Hea. rewrite mulmx1 in Hce. by subst.
Qed.

(** Casting Matrices*)

(*We need to "push" a cast through Gaussian elimination (ie, castmx (gauss_elim A) = gauss_elim (castmx A)).
  This requires a lot of work*)

Lemma cast_eq: forall m n m' n' (A: 'M[F]_(m, n)) (B: 'M[F]_(m', n')) (Heq: (m = m') * (n = n')),
  (forall (x: 'I_m) (y: 'I_n), A x y = B (cast_ord (fst Heq) x) (cast_ord (snd Heq) y)) ->
  castmx Heq A = B.
Proof.
  move => m n m' n' A B Heq Hab. rewrite -matrixP => x y.
  rewrite castmxE Hab /=. f_equal; by apply ord_inj.
Qed.

Definition cast_seq n n' (H: n = n') (s: seq 'I_n)  : seq 'I_n' :=
  map (cast_ord H) s.

Lemma foldr_castmx: forall m n m' n' (A: 'M[F]_(m, n)) (Heq: (m = m') * (n = n')) 
  (f: 'I_m -> 'M[F]_(m, n) -> 'M[F]_(m, n)) (g: 'I_m' -> 'M[F]_(m', n') -> 'M[F]_(m', n')) (l: seq 'I_m),
  (forall (x: 'I_m) (A: 'M[F]_(m, n)), castmx Heq (f x A) = g (cast_ord (fst Heq) x) (castmx Heq A)) ->
  castmx Heq (foldr f A l) = foldr g (castmx Heq A) (cast_seq (fst Heq) l).
Proof.
  move => m n m' n' A Heq f g l Hfg. elim : l => [//= | h t IH /=].
  by rewrite Hfg IH.
Qed.

(*Probably can abstract this as functor or monad or something*)
Definition cast_option n n' (H: n = n')  (o: option 'I_n) : option 'I_n' :=
  match o with
  | None => None
  | Some x => Some ((cast_ord H) x)
  end.

Lemma cast_option_none: forall n n' (H: n = n') (o: option 'I_n),
  (cast_option H o == None) = (o == None).
Proof.
  move => n n' H o. by case : o.
Qed.

Lemma cast_option_some: forall n n' (H: n = n') (o: option 'I_n) c,
  cast_option H o = Some c ->
  exists d, o = Some d /\ (cast_ord H) d = c.
Proof.
  move => n n' H o c. case : o =>[d //= Hsome | //=]. exists d. case: Hsome. by move ->.
Qed.

(*Working with casts is very annoying*)
Lemma lead_coef_cast: forall m n m' n' (H: (m = m') * (n = n')) (A: 'M[F]_(m, n)) (r: 'I_m),
  lead_coef A r = cast_option (esym (snd H)) (lead_coef (castmx H A) (cast_ord (fst H) r)).
Proof.
  move => m n m' n' H A r.
  case Hlc: (lead_coef A r) =>[c /= | //=].
  - move: Hlc. rewrite lead_coef_some_iff => [[Hrc Hbefore]].
    symmetry. case Hlc : (lead_coef (castmx H A) (cast_ord H.1 r)) => [d /= | //=].
    + move : Hlc. rewrite lead_coef_some_iff => [[Hrd Hbef]].
      move : Hrd; rewrite castmxE /= => Hrd.
      case (orP (ltn_total c  (cast_ord (esym (snd H)) d))).
      * move => /orP[Hlt | Heq].
        -- have: A r c == 0%R. apply /eqP.  move: Hbef => /(_ (cast_ord (snd H) c)).
           rewrite castmxE !cast_ordK => Hzero. by apply Hzero.
            move : Hrc; by case : (A r c == 0%R).
        -- apply (elimT eqP) in Heq. f_equal. by apply ord_inj.
      * move => Hdc. have:  A (cast_ord (esym H.1) (cast_ord H.1 r)) (cast_ord (esym H.2) d) == 0%R.
        apply /eqP. move : Hbefore => /(_ _ Hdc). by rewrite !cast_ordK.
        move: Hrd. by case : (A (cast_ord (esym H.1) (cast_ord H.1 r)) (cast_ord (esym H.2) d) == 0%R).
    + move: Hlc. rewrite lead_coef_none_iff => /(_ (cast_ord (snd H) c)). rewrite castmxE !cast_ordK => Hrc'. move: Hrc.
      by rewrite Hrc' eq_refl.
  - move: Hlc. rewrite lead_coef_none_iff => [Hall]. symmetry. apply /eqP. rewrite cast_option_none. apply /eqP.
    rewrite lead_coef_none_iff. move => x. rewrite castmxE !cast_ordK. apply Hall.
Qed.

Lemma cast_leq: forall m n m' n' (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N),
  (m' <= n')%N.
Proof.
  move => m n m' n' [Hm Hn]. by rewrite Hm Hn.
Qed.

Lemma cast_seq_pmap: forall n n' (H: n = n') (l: list nat),
  cast_seq H (pmap insub l) = pmap insub l.
Proof.
  move => n n' H l. elim : l => [//= | h t Ih /=].
  case Hh: (h < n)%N.
  - rewrite !insubT /=. by rewrite -H. move => Hn'. rewrite Ih /=. f_equal.
    by apply ord_inj.
  - by rewrite !insubF // -H.
Qed.  

Lemma cast_ord_enum: forall n n' (H: n = n'),
  cast_seq H (ord_enum n) = ord_enum n'.
Proof.
  move => n n' H. rewrite /ord_enum. by rewrite cast_seq_pmap H.
Qed.

Lemma cast_ord_switch: forall n n' (H: n = n') x y,
  (cast_ord (esym H) x == y) = (x == cast_ord H y).
Proof.
  move => n n' H x y.
  case : (x == cast_ord H y) /eqP => Hx.
  - rewrite Hx /=. by rewrite cast_ordK eq_refl.
  - apply /eqP. move => C. move: Hx. by rewrite -C cast_ordKV.
Qed.

(*Push the cast through each intermediate function*)

Lemma sc_mul_castmx: forall m n m' n' (Heq: (m = m') * (n = n')) (A: 'M[F]_(m, n)) c (r: 'I_m),
  castmx Heq (sc_mul A c r) = sc_mul (castmx Heq A) c (cast_ord (fst Heq) r).
Proof.
  move => m n m' n' Heq A c r. rewrite -matrixP => x y.
  by rewrite castmxE !mxE cast_ord_switch !castmxE.
Qed.

(*We need a few other general results to show that inverses do not change under casting*)

Lemma mulmx_castmx: forall n n' (H: n = n') (A B: 'M[F]_n),
  castmx (H, H) (A *m B)%R = ((castmx (H, H) A) *m (castmx (H, H) B))%R.
Proof.
  move => n n' H A B. rewrite -matrixP => x y.
  rewrite castmxE !mxE. have Hn: (n <= n')%N by rewrite H leqnn.
  rewrite (big_nth x) (big_nth (cast_ord (esym H) x)) /=.
  rewrite !index_ord_enum !size_ord_enum.
  rewrite (big_nat_widen _ _ _ _ _ Hn) big_nat_cond (big_nat_cond _ _ _ _ (fun x => true)).
  apply eq_big.
  - move => i. by rewrite /= H andbb andbT.
  - rewrite /=. move => i /andP[Hi' Hi].
    rewrite !castmxE /=. 
    have Hii: i = nat_of_ord (Ordinal Hi) by []. 
    have Hii': i = nat_of_ord (Ordinal Hi') by []. 
    have->: (nth x (ord_enum n') i) = (nth x (ord_enum n') (Ordinal Hi')) by f_equal.
    have->: (nth (cast_ord (esym H) x) (ord_enum n) i) = (nth (cast_ord (esym H) x) (ord_enum n) (Ordinal Hi)) by f_equal.
    rewrite !nth_ord_enum. by f_equal; f_equal; apply ord_inj.
Qed.

Lemma id_castmx: forall n n' (H: n = n'),
  castmx (R:=F) (H, H) (1%:M)%R = (1%:M)%R.
Proof.
  move => n n' H. rewrite -matrixP => x y.
  by rewrite castmxE !id_A cast_ord_switch cast_ordKV.
Qed.

Lemma unitmx_castmx: forall n n' (H: n = n') (A: 'M[F]_n),
  ((castmx (H, H) A) \in unitmx) = (A \in unitmx).
Proof.
  move => n n' H A. case Hun: (A \in unitmx).
  - have Hmul: (A *m (invmx A))%R = (1%:M)%R by apply mulmxV.
    have: castmx (H, H) (A *m invmx A)%R = castmx (H, H) (1%:M)%R by rewrite Hmul.
    rewrite mulmx_castmx id_castmx => Hcast. apply mulmx1_unit in Hcast. apply Hcast.
  - case Hcastun: (castmx (H, H) A \in unitmx) => [|//].
    have Hmul: ((castmx (H, H) A) *m (invmx (castmx (H, H) A)))%R = (1%:M)%R by apply mulmxV.
    have: castmx (esym H, esym H) (castmx (H, H) A *m invmx (castmx (H, H) A))%R =
          castmx (esym H, esym H) (1%:M)%R by rewrite Hmul.
    rewrite mulmx_castmx castmxK id_castmx => Ha.
    apply mulmx1_unit in Ha. case : Ha => [Ha  Hc]. by rewrite Ha in Hun.
Qed.

End Gauss.