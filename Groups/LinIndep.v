(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Require Import Gaussian.
Require Import CommonSSR.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Section LinIndep.

Variable F : fieldType.

Local Open Scope ring_scope.

(*We want to define the notion that the rows of a matrix are linearly independent*)
(*cannot make bool unless field is finite, which is true in this case*)
Definition rows_lin_indep {m n} (A: 'M[F]_(m, n)) : Prop :=
  forall (c: 'I_m -> F),
  (forall (j : 'I_n), (\sum_(i < m) (c(i) * A i j)) = 0) ->
  forall (x: 'I_m), c x = 0.

(*For some reason, this doesn't exist in library*)
Lemma sum_change_cond: forall {I: eqType} (r: seq I) p1 p2 (f: I -> F),
  (forall x, x \in r -> p1 x = p2 x) ->
  \sum_(i <- r | p1 i) f i = \sum_(i <- r | p2 i) f i.
Proof.
  move => I r p1 p2 f Hp12. rewrite big_seq_cond. rewrite (big_seq_cond (fun i => p2 i)).
  apply eq_big. 2: by []. move => x. case Hin: (x \in r) => [|//].
  by rewrite Hp12.
Qed. 

(*We can add up a summation by picking one element, adding everything else, then adding this element separately*)
Lemma sum_remove_one: forall {n} (p : pred 'I_n) (f : 'I_n -> F) (x: 'I_n),
  p x ->
  \sum_(i < n | p i) (f i) = \sum_(i < n | (p i && (i != x))) (f i) + (f x).
Proof.
  move => n p f x Hpx. rewrite (big_nth x). rewrite !(big_nth x) /= /index_enum /= ordinal_enum_size.
  have Hxn: x <= n by apply ltnW.
  rewrite (@big_cat_nat _ _ _ x) => [/=|//|//]. 
  rewrite (@big_cat_nat _ _ _ x 0 n) => [/= | // | //].
  rewrite -GRing.addrA. f_equal.
  - apply sum_change_cond. move => i Hin.
    have Hix: i < x by move: Hin; rewrite mem_iota add0n subn0.
    have Hinlt: i < n by apply (ltn_trans Hix).
    have ->: (nth x (Finite.enum (ordinal_finType n)) i =
           (nth x (Finite.enum (ordinal_finType n)) (Ordinal Hinlt))) by [].
    rewrite ordinal_enum. have ->: Ordinal Hinlt != x. 
    rewrite ltn_neqAle in Hix. by move : Hix => /andP[Hixneq H{H}].
    by rewrite andbT.
  - rewrite big_ltn_cond =>[|//].
    rewrite (@big_ltn_cond _ _ _ x) => [|//].
    rewrite !ordinal_enum Hpx eq_refl /= GRing.addrC. f_equal.
    apply sum_change_cond. move => i Hiin.
    have Hin: i < n. move: Hiin. rewrite mem_iota subnKC. by move => /andP[H1 H2]. by [].
    have ->: nth x (Finite.enum (ordinal_finType n)) i = nth x (Finite.enum (ordinal_finType n)) (Ordinal Hin) by [].
    rewrite ordinal_enum. have ->: Ordinal Hin != x. have: i != x. move : Hiin; rewrite mem_iota ltn_neqAle
    => /andP[/andP[Hnneq H{H}] H{H}]. by rewrite eq_sym. by []. by rewrite andbT.
Qed. 

 
(*Row operations preserve linear independence*)

(*Scalar multiplication preserves linear independence*)
(*Idea: multiple c_r by k to preserve sum, does not change 0*)
Lemma sc_mul_lin_indep: forall {m n} (A: 'M[F]_(m, n)) k r,
  k != 0 ->
  rows_lin_indep A <-> rows_lin_indep (sc_mul A k r).
Proof.
  move => m n A k r Hk. rewrite /rows_lin_indep /sc_mul !/mxE.
  have Hinner: (forall (j : 'I_n) (c : 'I_m -> F),
  \sum_(i < m) c i * (\matrix_(i0, j0) (if i0 == r then k * A i0 j0 else A i0 j0)) i j =
  \sum_(i < m) c i *  (if i == r then k * A i j else A i j)). {
  move => j c. apply congr_big => [//|//|]. move => i H{H}; by rewrite mxE. }
  have Hinner_simpl: (forall (j : 'I_n) (c : 'I_m -> F),
     \sum_(i < m) c i * (if i == r then k * A i j else A i j) =
     (\sum_(i < m | i != r) c i * A i j) + (c r) * (k * A r j)). {
  move => j c. rewrite (@sum_remove_one _ _ _ r) => [|//].
  rewrite eq_refl. f_equal. 
  apply eq_big. by []. move => i /andP[H{H} Hir]. by have->: i == r = false by move: Hir; case: (i == r). }
  split.
  - move => Hlin c Hprod x.
    move : Hlin => /(_ (fun x => if x == r then c x * k else c x)) Hlin.
    have Hcond: (forall j : 'I_n, \sum_(i < m) (if i == r then c i * k else c i) * A i j = 0). {
    move => j. rewrite -{2}(Hprod j) Hinner Hinner_simpl.
    rewrite (@sum_remove_one _ _ _ r) =>[|//]. rewrite eq_refl GRing.mulrA. f_equal. 
    apply eq_big => [//|//]. move => i /andP[H{H} Hir]. by have ->: (i==r = false) by move: Hir; by case (i==r). }
    move : Hlin => /(_ Hcond x).
    case Hxr: (x == r).
    + move => Hp. have: (c x * k == 0) by apply (introT eqP).
      rewrite GRing.mulf_eq0. have->: (k == 0 = false) by move : Hk; by case: (k==0).
      by rewrite orbF => /eqP Hc.
    + by [].
  - move => Hlin c Hprod x.
    move : Hlin => /(_ (fun x => if x == r then c x * k^-1 else c x)) Hlin.
    have Hcond: (forall j : 'I_n, \sum_(i < m)  (if i == r then c i / k else c i) *
           (\matrix_(i0, j0) (if i0 == r then k * A i0 j0 else A i0 j0)) i j = 0). {
    move => j. rewrite -{2}(Hprod j) Hinner Hinner_simpl. rewrite eq_refl.
    rewrite (@sum_remove_one _ (fun _ => true) _ r) =>[|//]. rewrite -!GRing.mulrA.  rewrite (GRing.mulrA (k^-1))
    GRing.mulVf =>[|//]. rewrite GRing.mul1r. f_equal.
    apply eq_big => [//|//]. move => i Hir. by have ->: (i==r = false) by move: Hir; by case (i==r). }
    move : Hlin => /(_ Hcond x).
    case Hxr: (x == r).
    + move => Hp. have: (c x / k == 0) by apply (introT eqP).
      rewrite GRing.mulf_eq0 GRing.invr_eq0. have->: (k == 0 = false) by move : Hk; by case: (k==0).
      by rewrite orbF => /eqP Hc.
    + by [].
Qed.

(*Swapping rows preserves linear independence*)
(*Idea: switch c_r1 and c_r2, preserves sum but does not change 0*)
Lemma xrow_lin_indep: forall {m n} (A: 'M[F]_(m, n)) r1 r2,
  rows_lin_indep A <-> rows_lin_indep (xrow r1 r2 A).
Proof.
  move => m n A r1 r2. rewrite /rows_lin_indep.
  have Hinner: (forall (c: 'I_m -> F) (j: 'I_n),
    \sum_(i < m) (c i * xrow r1 r2 A i j) =
    \sum_(i < m) (fun (j: 'I_m) => if j == r1 then c r2 else if j == r2 then c r1 else c j) i * A i j). {
  move => c j. rewrite (@sum_remove_one _ _ _ r1) => [|//]. rewrite xrow_val eq_refl.
  rewrite (@sum_remove_one _ (fun _ => true) _ r1) =>[|//]. rewrite eq_refl.
  case: (r1 == r2) /eqP => [ -> // | /eqP Hr12].
  - f_equal. apply eq_big. by []. move => i /andP[H{H} Hir2].
    rewrite xrow_val. move: Hir2; by case: (i == r2).
  - have Hr12': (r2 != r1) by rewrite eq_sym Hr12. rewrite (@sum_remove_one _ _ _ r2) =>[|//].
    rewrite (@sum_remove_one _ (fun x => true && (x != r1)) _ r2) => [|//]. 
    rewrite !eq_refl !xrow_val (negbTE Hr12') eq_refl -!GRing.addrA (GRing.addrC (c r2 * A r1 j)). f_equal.
    apply eq_big. by []. move => i /andP[/andP[H{H} Hir1] Hir2].
    move: Hir1 Hir2. rewrite xrow_val. by case (i == r1); case: (i == r2). }
  split.
  - move => Hlin c. move: Hlin => /(_ (fun (j: 'I_m) => if j == r1 then c r2 else if j == r2 then c r1 else c j)) 
    Hlin Hprod x. 
    have Hcond: (forall j : 'I_n,
        \sum_(i < m) (if i == r1 then c r2 else if i == r2 then c r1 else c i) * A i j = 0). move => j.
    by rewrite -Hinner Hprod. move: Hlin => /(_ Hcond).
    case: (x == r1) /eqP => [-> // | /eqP Hxr1].
    + move => /(_ r2). case: (r2 == r1) /eqP => [-> // | //]. by rewrite eq_refl.
    + case: (x == r2) /eqP => [-> // | /eqP Hxr2]. move => /(_ r1). by rewrite eq_refl.
      move /(_ x). by rewrite (negbTE Hxr1) (negbTE Hxr2).
  - move => Hlin c. move: Hlin => /(_ (fun (j: 'I_m) => if j == r1 then c r2 else if j == r2 then c r1 else c j)) 
    Hlin Hprod x. 
    have Hcond: (forall j : 'I_n,
        \sum_(i < m) (if i == r1 then c r2 else if i == r2 then c r1 else c i) * xrow r1 r2 A i j = 0). { move => j.
    rewrite Hinner -{2}(Hprod j). apply eq_big. by []. move => i H{H}. case: (i == r1) /eqP => [-> // | /eqP Hir1].
    - rewrite eq_refl. by case: (r2 == r1) /eqP =>[->|].
    - case: (i == r2) /eqP => [-> //|//]. by rewrite eq_refl. }
    move: Hlin => /(_ Hcond).
    case: (x == r1) /eqP => [-> //|/eqP Hxr1 ].
    + move => /(_ r2). case: (r2 == r1) /eqP => [-> // | //]. by rewrite eq_refl.
    + case: (x == r2) /eqP => [->//|/eqP Hxr2]. move => /(_ r1). by rewrite eq_refl.
      move /(_ x). by rewrite (negbTE Hxr1) (negbTE Hxr2).
Qed.

(*Adding multiple of one row to another preserves linear independence*)
Lemma add_mul_lin_indep: forall {m n} (A: 'M[F]_(m, n)) k r1 r2,
  r1 != r2 ->
  rows_lin_indep A <-> rows_lin_indep (add_mul A k r1 r2).
Proof.
  move =>m n A k r1 r2 Hr12. rewrite /rows_lin_indep.
  have Hinner: (forall (c: 'I_m -> F) (j: 'I_n),
    \sum_(i < m) (fun (j: 'I_m) => if j == r1 then c r1 - k * c r2 else c j)  i * add_mul A k r1 r2 i j =
    \sum_(i < m) c i * A i j). {
  move => c j. rewrite (@sum_remove_one _ _ _ r1) => [|//]. rewrite eq_refl /add_mul mxE.
  have Hr12f: r1 == r2 = false by move: Hr12; case (r1 == r2). rewrite Hr12f.
  rewrite (@sum_remove_one _ (fun _ => true) _ r1) =>[|//].
  rewrite (@sum_remove_one _ _ _ r2). 2: by rewrite eq_sym. rewrite eq_sym Hr12f mxE eq_refl -GRing.addrA.
  have ->: c r2 * (A r2 j + k * A r1 j) + (c r1 - k * c r2) * A r1 j = c r2 * A r2 j + c r1 * A r1 j. {
  rewrite GRing.mulrDl GRing.mulrDr -GRing.addrA. f_equal.
  by rewrite GRing.addrC (GRing.mulrC k) GRing.mulNr (GRing.mulrA _ k) -GRing.addrA GRing.addNr GRing.addr0. }
  rewrite (@sum_remove_one _ (fun i => true && (i != r1)) _ r2). 2: by rewrite eq_sym.
  rewrite -GRing.addrA. f_equal. apply eq_big =>[//|].
  move => i /andP[/andP[H{H} Hir1] Hir2]. rewrite mxE.
  have->: (i == r1 = false) by move: Hir1; case (i == r1).
  by have->: (i == r2 = false) by move: Hir2; case (i == r2). }
  split.
  - move => Hlin c. move: Hlin => /(_ (fun (j: 'I_m) => if j == r1 then c r1 + k * c r2 else c j)) 
    Hlin Hprod x. 
    have Hcond: (forall j : 'I_n, \sum_(i < m) (if i == r1 then c r1 + k * c r2 else c i) * A i j = 0). {
      move => j. rewrite -Hinner eq_refl -{2}(Hprod j). apply eq_big =>[//|]. move => i H{H}.
      case Hir1: (i == r1). rewrite /add_mul mxE. have Hr12f: r1 == r2 = false by move: Hr12; case (r1 == r2).
      rewrite eq_sym Hr12f. have ->: (i == r2 = false). case Hir2: (i == r2). eq_subst Hir1. eq_subst Hir2.
      by rewrite eq_refl in Hr12f. by []. rewrite -GRing.addrA (GRing.addrN (k * c r2)) GRing.addr0. by eq_subst Hir1.
      by rewrite /add_mul mxE. }
    move : Hlin => /(_ Hcond).
    case: (c r2 == 0) /eqP => [-> //| /eqP Hcr2].
    + move => /(_ x). rewrite GRing.mulr0 GRing.addr0. by case: (x == r1) /eqP => [->|].
    + move /(_ r2). rewrite eq_sym (negbTE Hr12).
      move => Hcr2'. move: Hcr2' Hcr2 ->. by rewrite eq_refl.
  - move => Hlin c. move: Hlin => /(_ (fun (j: 'I_m) => if j == r1 then c r1 - k * c r2 else c j)) 
    Hlin Hprod x.
    have Hcond:  (forall j : 'I_n,
        \sum_(i < m) (if i == r1 then c r1 - k * c r2 else c i) * add_mul A k r1 r2 i j = 0).
    move => j. by rewrite Hinner Hprod. move : Hlin => /(_ Hcond).
    case: (c r2 == 0) /eqP => [-> // | /eqP Hcr2].
    + move => /(_ x). rewrite GRing.mulr0 GRing.subr0.  by case: (x == r1) /eqP => [-> |].
    + move /(_ r2). rewrite eq_sym (negbTE Hr12). move => Hcr2'. move: Hcr2' Hcr2 ->. by rewrite eq_refl.
Qed.

(*We can put these together in the following results*)
Lemma ero_lin_indep: forall {m n} (A B : 'M[F]_(m, n)),
  (ero A B) ->
  rows_lin_indep A <-> rows_lin_indep B.
Proof.
  move => m n A B Hero. elim: Hero  => m' n' r1.
  - move => r2 A'. apply xrow_lin_indep.
  - move => k A' Hk. by apply sc_mul_lin_indep.
  - move => r2 k A' Hr12. by apply add_mul_lin_indep.
Qed.

Lemma row_equivalent_lin_indep: forall {m n} (A B : 'M[F]_(m, n)),
  row_equivalent A B ->
  rows_lin_indep A <-> rows_lin_indep B.
Proof.
  move => m n A B Hre. elim: Hre => m' n' A'.
  - by [].
  - move => B' C' Hero Hre IH. rewrite -IH. by apply ero_lin_indep.
Qed.

(*The crucial test (for our purposes). The rows of a matrix are linearly independent iff
  the rows of the row reduced matrix are linearly independent. For an n x n matrix, linear independence
  of a row reduced matrix occurs exactly when the matrix is the identity*)
Lemma gauss_elim_lin_indep: forall {m n} (A: 'M[F]_(m, n)),
  rows_lin_indep A <-> rows_lin_indep (gaussian_elim A).
Proof.
  move => m n A. apply row_equivalent_lin_indep. apply gaussian_elim_row_equiv.
Qed.

(*A matrix with a row of zeroes does not have linearly independent rows*)
Lemma row_zero_not_lin_indep: forall {m n} (A : 'M[F]_(m, n)) (r: 'I_m),
  (forall (c: 'I_n), A r c = 0) ->
  ~rows_lin_indep A.
Proof.
  move => m n A r Hzero. rewrite /rows_lin_indep => Hlin. move : Hlin => /(_ (fun x => if x == r then 1 else 0)).
  have Hcond: (forall j : 'I_n, \sum_(i < m) (if i == r then 1 else 0) * A i j = 0). {
   move => j. 
    have->: \sum_(i < m) (if i == r then 1 else 0) * A i j = \sum_(i < m) (if r == i then A i j else 0).
    apply eq_big =>[//|]. move => i H{H}. rewrite eq_sym. case : (r == i).
    by rewrite GRing.mul1r. by rewrite GRing.mul0r.
  rewrite sum_if. apply Hzero. }
  move => /(_ Hcond r). rewrite eq_refl. move => Honez. have: (GRing.one F) != 0 by rewrite GRing.oner_neq0.
  by rewrite Honez eq_refl.
Qed.

(*The identity matrix does have linearly independent rows*)
Lemma identity_lin_indep: forall n,
  @rows_lin_indep n n (1%:M).
Proof.
  move => n. rewrite /rows_lin_indep => c Hsum x.
  move : Hsum => /(_ x).
  have->: \sum_(i < n) c i * 1%:M i x = c x. {
  have->: \sum_(i < n) c i * 1%:M i x = \sum_(i < n) (if x == i then c i else 0).
  apply eq_big => [//|i H{H}]. rewrite id_A eq_sym. 
  case : (x == i). by rewrite GRing.mulr1. by rewrite GRing.mulr0.
  apply sum_if. } by [].
Qed.

(** Invertible Matrices (part 2) *)

(* We prove in [Gaussian.v] that invertibility is equivalent to [gaussian_elim A == I]. Here we give
  another equivalent condition - that the rows of A are linearly independent*)

Lemma unitmx_iff_lin_indep_rows: forall {n} (A: 'M[F]_n),
  A \in unitmx <-> rows_lin_indep A.
Proof.
  move => n A. rewrite gauss_elim_lin_indep unitmx_iff_gauss_id. split.
  - move /eqP ->. apply identity_lin_indep.
  - move => Hre. have Hred: red_row_echelon (gaussian_elim A) by apply gaussian_elim_rref.
    apply (rref_colsub_cases (leqnn n)) in Hred. case: Hred => [//= <- | [r Hzero]].
    apply /eqP. symmetry. apply colsub_square_mx. 
    have Hrenot: ~ (rows_lin_indep (gaussian_elim A)).
    apply (@row_zero_not_lin_indep _ _  _ r). move => c. by apply Hzero. by [].
Qed. 

End LinIndep.
