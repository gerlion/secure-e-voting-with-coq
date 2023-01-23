(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Require Import mathcomp.algebra.poly.
Require Import LinIndep.
Require Import CommonSSR.


Section GenericVandermonde.
Local Open Scope ring_scope.


  Variable (F : fieldType).

  Definition vandermonde (m n: nat) (l : list F) : 'M[F]_(m, n) :=
    \matrix_(i < m, j < n) (nth 0 l j) ^+ i.

  Lemma vandermonde_unitmx: forall n l,
    uniq l ->
    n = size l ->
    vandermonde n n l \in unitmx.
  Proof.
    move => n l Huniq Hlen.
    rewrite unitmx_iff_lin_indep_rows.
    rewrite /rows_lin_indep /vandermonde. 
    move => c Hzero.
    have: forall (j: 'I_n), \sum_(i < n) c i * (nth 0 l j) ^+ i = 0. {
    move => j. rewrite -{3}(Hzero j). 
    apply eq_big =>[//|]. 
    move => i H{H}. by rewrite mxE. }
    move => {}Hzero.
    (*Polys require functions from nat -> F, so we need the following*)
    remember (fun (n: nat) => match (insub n) with 
      |Some n' => c n' | None => 0 end) as c'. 
    remember (\poly_(i < n) c' i) as p.
    have Hroots: forall (j: 'I_n), p.[l`_j] = 0. { move => j.
      have Hsz: size p <= n by rewrite Heqp; apply size_poly. 
      rewrite (horner_coef_wide _ Hsz) -{4}(Hzero j) -(@big_mkord _ _ _ n (fun _ => true) (fun i => p`_i * l`_j ^+ i))
      (big_nth j) ordinal_enum_size 
        big_nat_cond (big_nat_cond _ _ 0 n (fun _ => true)).
      apply eq_big => [//| i /andP[/andP[H{H} Hin] H{H}]].
      have->: (nth j (index_enum (ordinal_finType n)) i) = 
      (nth j (index_enum (ordinal_finType n)) (Ordinal Hin))
      by apply (elimT eqP). rewrite !ordinal_enum. rewrite Heqp coef_poly Hin /=. 
      by have->: c' i = c (Ordinal Hin) by rewrite Heqc' insubT /=. }
    have Hallroot: all (root p) l. { rewrite all_in => x Hxin. 
      rewrite /root. apply (introT eqP).
      have <-: nth 0 l (index x l) = x by apply nth_index.
      have Hidx: (index x l) < n by rewrite Hlen index_mem.
      have ->: l`_(index x l) = l`_(Ordinal Hidx) by []. apply Hroots. }
    (*Therefore, p is the 0 polynomial*)
    have Hp: p = 0. apply (roots_geq_poly_eq0 Hallroot Huniq). by rewrite -Hlen Heqp size_poly.
    move => x. have: p`_x = 0 by rewrite Hp; apply coef0.
    rewrite Heqp coef_poly. have Hxn: x < n by []. rewrite Hxn Heqc' insubT /=.
    have->: Ordinal Hxn = x. (apply (elimT eqP)). by have: x == x by rewrite eq_refl. by [].
  Qed.


End GenericVandermonde.
