Require Import Bool.
Require Import Setoid.
Require Import Coq.Logic.Eqdep_dec.
Require Import ZArith Znumtheory.
Require Import Coqprime.Z.Zmod.
Require Import Coq.NArith.BinNat.
Require Import Ring.
Require Import Field.
Require Import Coqprime.elliptic.GZnZ.
Require Import Specif.
Require Import Coq.PArith.Pnat.
Require Import Coq.ZArith.Znat.
Require Import ArithRing.
Require Import Lia.
Require Import Recdef.
Require Import Div2.
Require Import Coq.Arith.Wf_nat.
Require Import primeP.
Require Import primeQ.
Require Import Coq.ZArith.Znat.
Require Import Groups.groups.
Require Import Groups.vectorspace.
Require Import Coq.PArith.Pnat.
Require Import Coq.Structures.Equalities.

Open Scope Z_scope.

Section HeliosIACR2018.

Definition P : Z := 16328632084933010002384055033805457329601614771185955389739167309086214800406465799038583634953752941675645562182498120750264980492381375579367675648771293800310370964745767014243638518442553823973482995267304044326777047662957480269391322789378384619428596446446984694306187644767462460965622580087564339212631775817895958409016676398975671266179637898557687317076177218843233150695157881061257053019133078545928983562221396313169622475509818442661047018436264806901023966236718367204710755935899013750306107738002364137917426595737403871114187750804346564731250609196846638183903982387884578266136503697493474682071.
Definition Q : Z := 61329566248342901292543872769978950870633559608669337131139375508370458778917.

Lemma P_prime : prime P.
Proof.
  apply mm.
Qed.

Lemma P_pos : 0 < P.
Proof.
  unfold P; lia.
Qed.

Lemma Q_prime : prime Q.
Proof.
  apply myPrime.
Qed.

Lemma Q_pos : 0 < Q.
Proof.
  unfold Q. lia.
Qed.

Lemma Q_nat_nonzero : Z.to_nat Q <> 0%nat.
Proof.
  unfold Q. cbn.
    lia.
Qed.

(* The base field *)

Theorem znz_bij: forall P : Z, forall a b : (znz P), a = b <-> val P a = val P b.
  split. intros; subst; auto.
   intros. destruct a, b. cbn in *.
    subst. f_equal. apply eq_proofs_unicity_on. apply Z.eq_decidable.
Qed.

Definition Fp : Set := (znz P).

Definition FpAdd : Fp -> Fp -> Fp  := (add _).

Definition FpZero : Fp := (zero _).

Definition FpBool_eq (a b :Fp) : bool := Z.eqb (val P a) (val P b).

Definition FpSub : Fp -> Fp -> Fp := (sub _).

Definition FpInv : Fp -> Fp := (opp _).

Definition FpMul : Fp -> Fp -> Fp := (mul _).

Definition FpOne : Fp := (one _).

Definition FpMulInv : Fp -> Fp := (inv _).

Definition FpDiv : Fp-> Fp-> Fp := (div _).

Lemma Fpfield : field_theory FpZero FpOne FpAdd FpMul FpSub FpInv FpDiv FpMulInv (@eq Fp).
Proof.
  apply FZpZ. apply P_prime.
Qed.

Add Field Fpfield : Fpfield.

Lemma inverse_Fp : forall x z : Fp,
    x <> FpZero ->
  FpMul (FpMulInv x) (FpMul x z) = z.
Proof.
 intros; field; auto.
Qed.

Lemma left_cancel_Fp : forall x y z: Fp,
  x <> FpZero ->
 (FpMul x y = FpMul x z) <-> (y = z).
Proof.
  intros. unfold iff. refine (conj _ _).
  (*Case 1 *)
  intros. assert (FpMul (FpMulInv x) (FpMul x y) = FpMul (FpMulInv x) (FpMul x z)). rewrite H0. trivial.
  do 2 rewrite inverse_Fp in H1. trivial. apply H. apply H. apply H.
  (*Case 2 *)
  intros.  rewrite H0. trivial.
Qed.

Lemma one_neq_zero :
  FpOne <> FpZero.
Proof.
  apply (F_1_neq_0
  (rmul:=FpMul)(radd:=FpAdd)(rO:=FpZero)(rI:=FpOne)(rsub:=FpSub)(ropp:=FpInv)
  (rdiv:=FpDiv)(rinv:=FpMulInv)(req:=(@eq Fp))). apply Fpfield.
Qed.

Lemma inverse_not_zero : forall x : Fp,
  x <> FpZero ->
  (FpMulInv x) <> FpZero.
Proof.
  intros. rewrite <- left_cancel_Fp with (x:=x).
  replace (FpMul x (FpMulInv x)) with FpOne by (field; auto).
  replace (FpMul x FpZero) with FpZero by (field; auto). apply one_neq_zero. apply H.
Qed.


(* The field ismorphic to the group *)

Definition F : Set := (znz Q).

Definition Fadd : F -> F -> F  := (add _).
  
Definition Fzero : F := (zero _).

Definition Fbool_eq_init (a b :F) : bool := Z.eqb (val Q a) (val Q b).

Definition Fsub : F -> F -> F := (sub _).

Definition Finv : F -> F := (opp _).

Definition Fmul : F -> F -> F := (mul _).

Definition Fone : F := (one _).

Definition FmulInv : F -> F := (inv _).

Definition Fdiv : F-> F-> F := (div _).

Lemma Ffield : field_theory Fzero Fone Fadd Fmul Fsub Finv Fdiv FmulInv (@eq F).
Proof.
  apply FZpZ. apply Q_prime.
Qed.

Add Field Ffield : Ffield.

Lemma zero_mod : forall n: nat,
  n <> 0%nat ->
  Nat.modulo 0%nat n = 0%nat.
Proof.
  intros. rewrite Nat.mod_0_l. trivial. apply H.
Qed.


Lemma mod_irr : forall a : Z,
  0 <= a ->
  Z.to_nat (a mod Q) =  Nat.modulo (Z.to_nat a) (Z.to_nat Q).
Proof.
  intros a Ha.
  assert (Ht : exists (k r : Z), k >= 0 /\ 0 <= r < Q /\ a = r + k * Q).
  assert (Q <> 0). unfold Q.  lia.
  pose proof (Z.div_mod a Q H).
  exists (a / Q), (a mod Q).
  split. unfold Q.
  apply Z_div_ge0. lia.  lia.
  split. apply Z.mod_pos_bound. unfold Q. lia.
  lia.
  destruct Ht as [k [r [Ht1 [Ht2 Ht3]]]].
  rewrite Ht3.
  rewrite Z_mod_plus_full.
  rewrite Z.mod_small; swap 1 2.
  assumption.
  rewrite Z2Nat.inj_add.
  rewrite Z2Nat.inj_mul.
  rewrite Nat.mod_add.
  rewrite Nat.mod_small. auto.
  apply Z2Nat.inj_lt; try lia.
  subst. cbn. lia.
  lia.  lia.  lia.  unfold Q. lia.
Qed.


Lemma greq_zero : forall a b :Z,
  0 <= a ->
  0 <= b ->
  0 <= a+b.
Proof.
  intros a b Ha Hb.
  lia.
Qed.


Lemma greq_zero2 : forall a b :Z,
  0 <= a ->
  0 <= b ->
  0 <= a*b.
Proof.
  intros a b Ha Hb.
  apply Z.mul_nonneg_nonneg; try assumption.
Qed.


Lemma Fadd_eq_Nadd_mod : forall r s : F,
  Z.to_nat (val Q (Fadd r s)) =
      Nat.modulo (Nat.add (Z.to_nat (val Q r)) (Z.to_nat (val Q s))) (Z.to_nat Q).
Proof.
  intros. rewrite <- Z2Nat.inj_add. apply mod_irr.
  rewrite inZnZ.
  apply greq_zero.
  rewrite inZnZ. apply Z.mod_pos_bound. apply Q_pos.
  rewrite inZnZ. apply Z.mod_pos_bound. apply Q_pos.
  rewrite inZnZ. apply Z.mod_pos_bound. apply Q_pos.
  rewrite inZnZ. apply Z.mod_pos_bound. apply Q_pos.
Qed.
  
Lemma Fmul_eq_Nmul : forall r s : F,
  (Z.to_nat (val Q (Fmul r s)) = Nat.modulo (Nat.mul (Z.to_nat (val Q s)) (Z.to_nat (val Q r))) (Z.to_nat Q)).
  intros. replace (Fmul r s) with (Fmul s r). unfold Fmul. rewrite <- Z2Nat.inj_mul.
   apply mod_irr. apply greq_zero2.
  rewrite inZnZ. apply Z.mod_pos_bound. apply Q_pos.
  rewrite inZnZ. apply Z.mod_pos_bound. apply Q_pos.
  rewrite inZnZ. apply Z.mod_pos_bound. apply Q_pos.
  rewrite inZnZ. apply Z.mod_pos_bound. apply Q_pos. field; auto.
Qed.

(*The schnorr group *)
Fixpoint naive_power (a:Fp)(n:nat) : Fp :=
  match n with 0%nat => FpOne
  | S p => FpMul a (naive_power a p)
  end.

Lemma dist_power_over_mult :
  forall a b : Fp,
  forall q : nat,
  naive_power (FpMul a b) q = FpMul (naive_power a q) (naive_power b q).
Proof.
  intros. induction q.  cbn in *. field; auto. cbn. rewrite IHq. field; auto.
Qed.

Lemma dist_power_over_add :
  forall a : Fp,
  forall x y : nat,
  naive_power a (x+y) = FpMul (naive_power a x) (naive_power a y).
Proof.
  intros. induction x.  cbn in *. field; auto. cbn. rewrite IHx. field; auto.
Qed.

(*Now define fast power*)
(* from A Gentle Introduction to Type Classes and
Relations in Coq Pierre Cast\u00e9ran and Matthieu Sozeau *)
Function binary_power_mult (acc x: Fp)(n:nat)
  {measure (fun i=>i) n} : Fp
  (* acc * (power x n) *) :=
  match n with 0%nat => acc
    | _ => if Even.even_odd_dec n
            then binary_power_mult
              acc (FpMul x x) (div2 n)
            else binary_power_mult
                (FpMul acc x) (FpMul x x) (div2 n)
end.
Proof.
  intros. apply lt_div2; auto with arith.
  intros; apply lt_div2; auto with arith.
Defined.

Definition binary_power (x:Fp)(n:nat) :=
  binary_power_mult FpOne x n.

Function binary_power_mult2 (x: Fp)(n: positive)(acc : Fp) :=
  match n with
  | xH => (FpMul x acc)
  | xO w => binary_power_mult2 (FpMul x x) w acc
  | xI w => binary_power_mult2 (FpMul x x) w (FpMul acc x)
  end.

Definition binary_power2 (x:Fp)(n: F) :=
  let e := (val Q n) in
  match e with
  | Z0 => FpOne
  | Zneg p => FpOne (*We could define this nicely *)
  | Zpos p => binary_power_mult2 x p FpOne
  end.

Lemma binary_power_mult_ok : forall (e : nat)(a x : Fp),
   binary_power_mult a x e = FpMul a (naive_power x e).
Proof.
  intro e; pattern e. apply lt_wf_ind.
  clear e; intros e Hn;   destruct e.
   intros. cbn. field; auto.
  intros.
    rewrite binary_power_mult_equation. destruct (Even.even_odd_dec (S e)).
  rewrite Hn.  rewrite dist_power_over_mult.  rewrite <- dist_power_over_add.
  (* a * x ** (Nat.div2 (S n) + Nat.div2 (S n)) = a * x ** S n *)

 pattern (S e) at 3;replace (S e) with (div2 (S e) + div2 (S e))%nat;auto.
 generalize (even_double _ e0);simpl;auto.
  apply lt_div2;auto with arith.
  rewrite Hn.
 rewrite dist_power_over_mult. rewrite <- dist_power_over_add.
  pattern (S e) at 3;replace (S e) with (S (div2 (S e) + div2 (S e)))%nat;auto.
  
  rewrite <- Rmul_assoc. cbn.  trivial. apply Fpfield.
  generalize (odd_double _ o);intro H;auto.
  apply lt_div2;auto with arith.
Qed.

Lemma binary_power_ok : forall (e : nat)(x : Fp),
   binary_power x e = naive_power x e.
Proof.
  intros. unfold binary_power. rewrite binary_power_mult_ok.
  field; auto.
Qed.

Lemma fpmul_assoc :
  forall x y z, FpMul x (FpMul y z) = FpMul (FpMul x y) z.
Proof.
  intros x y z.
  rewrite Rmul_assoc.
  auto.  apply Fpfield.
Qed.

  

Lemma binary_power_gen :
  forall x p ret,
    binary_power_mult2 x p ret =
    binary_power_mult ret x (Z.to_nat (Z.pos p)).
Proof.
  intros x p ret. rewrite binary_power_mult_ok.
  revert x ret.
  induction p.
  + cbn in *. intros x ret.
    rewrite Pos2Nat.inj_xI.
    rewrite (IHp (FpMul x x) (FpMul ret x)).
    (* At this point, We need Lemma that FpMul is associative *)
    rewrite <- fpmul_assoc.
    f_equal. cbn.  f_equal.
    rewrite dist_power_over_mult.
    rewrite dist_power_over_add.
    replace (Pos.to_nat p + 0)%nat with
        (Pos.to_nat p) by lia.
    auto.
  + cbn in *.  intros x ret.
    rewrite Pos2Nat.inj_xO.
    rewrite (IHp (FpMul x x) ret).
    f_equal. cbn.
    rewrite dist_power_over_mult.
    rewrite dist_power_over_add.
    replace (Pos.to_nat p + 0)%nat with
        (Pos.to_nat p) by lia.
    auto.
  + cbn in *. intros x ret.
    rewrite Pos2Nat.inj_1. cbn.
    field.
Qed.

    
Lemma binary_power_mult_ok2 : forall (x : Fp)(p : positive),
  binary_power_mult2 x p FpOne =
  binary_power_mult FpOne x (Z.to_nat (Z.pos p)).
Proof.
  intros. cbn.
  pose proof (binary_power_gen).
  apply H.
Qed.

Lemma binary_power2_ok : forall (x : Fp)(e  : F),
   binary_power2 x e = naive_power x (Z.to_nat (val Q e)).
Proof.
  intros. unfold binary_power2. rewrite <- binary_power_ok.
  (* Trivial case *)
  destruct e. cbn. elim val. cbn. trivial.
  (* Main case *)
  intros. unfold binary_power.
  unfold binary_power_mult. apply binary_power_mult_ok2.
  (* Condrictory case *)
  cbn. trivial.
Qed.

Lemma one_to_x_one :
  forall q : nat,
  naive_power FpOne q = FpOne.
Proof.
  intros.  induction q. auto.
  cbn.  rewrite IHq. field; auto.
Qed.

Lemma zero_to_x_zero :
  forall q : nat,
  q <> 0%nat ->
  naive_power FpZero q = FpZero.
Proof.
  intros.  induction q. unfold not in H. assert False.
  apply H. trivial. congruence.
  cbn.  field; auto.
Qed.


Lemma integral_domain :
   forall a b : Fp,
   a <> FpZero ->
   b <> FpZero ->
   FpMul a b <> FpZero.
Proof.
  intros. unfold not in H0. unfold not. intros. apply H0.
  apply left_cancel_Fp with (x:= (FpMulInv a)) in H1. rewrite inverse_Fp in H1.
  replace (FpMul (FpMulInv a) FpZero) with FpZero in H1. apply H1.
  field; auto. apply H. apply inverse_not_zero. apply H.
Qed.

Lemma power_pres :
  forall a : Fp,
  forall q : nat,
  a <> FpZero ->
  naive_power a q <> FpZero.
Proof.
  intros. induction q. unfold naive_power. apply one_neq_zero.
  cbn. apply integral_domain. apply H. apply IHq.
Qed.

Lemma inv_closed :
  forall a : Fp,
  forall q : nat,
   naive_power a q = FpOne ->
  a <> FpZero ->
  naive_power a q  = naive_power (FpMulInv a) q.
Proof.
  intros. rewrite <- left_cancel_Fp with (x:=naive_power a q).
  do 2 rewrite <- dist_power_over_mult. replace (FpMul a (FpMulInv a)) with FpOne.
  rewrite one_to_x_one.  rewrite dist_power_over_mult. rewrite H.
  field; auto. field; auto. apply power_pres. apply H0.
Qed.

Lemma inQSubGroup_closed :
  forall a b : Fp,
  forall q : nat,
  naive_power a q = FpOne ->
  naive_power b q = FpOne ->
  naive_power (FpMul a b) q = FpOne.
Proof.
  intros. rewrite dist_power_over_mult. rewrite H. rewrite H0. field; auto.
Qed.

Lemma inQSubGroup_zero_free :
 forall a : Fp,
  forall q : nat,
  naive_power a q = one P ->
  q <> 0%nat ->
  a <> FpZero.
Proof.
  intros. unfold not. intros. rewrite <- zero_to_x_zero with (q:=q) in H1.
  rewrite H1 in H. do 2 rewrite zero_to_x_zero in H. apply one_neq_zero.
  symmetry. apply H. apply H0. apply H0. apply H0. apply H0.
Qed.

Definition inQSubGroup (n : Fp) : Prop := binary_power n (Z.to_nat Q) = one P.

(* Let p_pos:= GZnZ.p_pos _ Q_prime. *)

Definition G : Set := { Fp | inQSubGroup Fp }.
Definition Gdot (a b : G) : G.
  pose (proj1_sig a). pose (proj1_sig b). pose (mul P f f0).
  pose (proj2_sig a). pose (proj2_sig b). cbn in *.
  unfold inQSubGroup in *. rewrite binary_power_ok in *. unfold G. assert (naive_power z (Z.to_nat Q) = one P).
  apply inQSubGroup_closed. apply i. apply i0.  exists z. rewrite <- binary_power_ok in H. apply H.
Defined.
Definition Gone : G.
  exists (one P). unfold inQSubGroup. rewrite binary_power_ok in *.  apply one_to_x_one.
Defined.
(* Definition twoEqTwo : 2 = 2 mod P. auto. Defined.
Definition Ggen : G.
  exists (mkznz P 2 twoEqTwo). unfold inQSubGroup. rewrite binary_power_ok in *. auto.
Defined. *)
Definition Gbool_eq_init (a b : G) : bool  := Z.eqb (val P (proj1_sig a)) (val P (proj1_sig b)).
Definition Ginv (a : G) : G.
  pose (proj1_sig a).  pose (proj2_sig a).
  exists (inv P f). cbn in *. unfold inQSubGroup in *. rewrite binary_power_ok in *. rewrite <- inv_closed. apply i.
  apply i. apply (inQSubGroup_zero_free (f)(Z.to_nat Q)). apply i. apply Q_nat_nonzero.
Defined.
Definition op (a:G)(b: F) : G.
  pose (proj2_sig a). exists (binary_power2 (proj1_sig a) b).
  rewrite binary_power2_ok in *.
  cbn in *. induction (Z.to_nat (val Q b)). cbn. unfold inQSubGroup.
  rewrite binary_power_ok in *.  apply one_to_x_one. unfold inQSubGroup.
  rewrite binary_power_ok in *. apply inQSubGroup_closed.
  unfold inQSubGroup in i. rewrite binary_power_ok in i. apply i.
  unfold inQSubGroup in IHn. rewrite binary_power_ok in IHn. apply IHn.
Defined.

Lemma Fp_decidable : forall (a b : Fp), Decidable.decidable (a = b).
Proof.
  intros [a ?] [b ?].
  destruct (Z.eq_decidable a b) as [?|H].
  + left.
    subst; f_equal.
    apply eq_proofs_unicity_on.
    apply Z.eq_decidable.
  + right.
    intro Heq; inversion Heq.
    apply H; assumption.
Qed.

(* We first prove equivlance *)
Lemma eq_proj:
  forall a b : G,
  a = b <-> proj1_sig(a) = proj1_sig(b).
Proof.
  split; intros.
  + rewrite H. auto.
  + destruct a, b. cbn in *.
    subst. f_equal. apply eq_proofs_unicity_on. apply Fp_decidable.
Qed.

Lemma Gdot_FpMul_eq :
  forall a b : G,
  proj1_sig (Gdot a b) = FpMul (proj1_sig a) (proj1_sig b).
Proof.
  intros. unfold Gdot. cbn.  trivial.
Qed.

Lemma Ginv_FpMulInv_eq : forall x : G,
  (proj1_sig (Ginv x)) = FpMulInv (proj1_sig x).
Proof.
  intros. unfold Ginv. cbn. trivial.
Qed.

Lemma op_binary_power_eq : forall (x :G)(a : F),
  (proj1_sig (op x a)) = binary_power (proj1_sig x) (Z.to_nat (val Q a)).
Proof.
  intros. unfold op. rewrite binary_power2_ok in *. cbn.
  rewrite binary_power_ok in *. trivial.
Qed.

Lemma nat_sub : forall a : nat,
  Nat.sub a a = 0%nat.
Proof.
  intros. induction a. cbn. auto.
  intros. cbn. apply IHa.
Qed.

Lemma dist_power_over_mul_2 :
  forall a : G,
  forall x y : nat,
  binary_power (proj1_sig a) (x*y) = binary_power (binary_power (proj1_sig a) x) y.
Proof.
  intros. induction x. cbn. rewrite binary_power_ok. rewrite one_to_x_one. trivial.
  cbn. do 3 rewrite binary_power_ok. rewrite dist_power_over_add. do 3 rewrite binary_power_ok in IHx.
  rewrite IHx. rewrite <- dist_power_over_mult. trivial.
Qed.

(* field; auto. seems like my bug, because Qed take too much time. Report
   to Coq or try newer version *)
Lemma dist_power_over_add_2 :
  forall a : G,
  forall x : nat,
  binary_power (proj1_sig a) (x mod (Z.to_nat Q)) =
    binary_power (proj1_sig a) x.
Proof.
  intros. remember (Nat.modulo x (Z.to_nat Q)) as y.
  rewrite (Nat.div_mod (x)(Z.to_nat Q)). do 2 rewrite binary_power_ok.
  rewrite dist_power_over_add. do 3 rewrite <- binary_power_ok.
  rewrite dist_power_over_mul_2. rewrite (proj2_sig a).
  do 3 rewrite binary_power_ok.  rewrite one_to_x_one.
  rewrite Heqy. remember (naive_power (proj1_sig a) (x mod Z.to_nat Q)) as b.
  symmetry.  (* field; auto. *) apply (Rmul_1_l (R:=Fp)(rO:=FpZero)(rI:=FpOne)(radd:=FpAdd)(rmul:=FpMul)(rsub:=FpSub)(ropp:=FpInv)(req:=(@eq Fp))).
  pose Fpfield. destruct f. apply F_R. apply Q_nat_nonzero.
Qed.

Lemma beq_F_ok :
  forall x y : F, Fbool_eq_init x y = true <-> x = y.
Proof.
  split. intros. unfold Fbool_eq_init in H. apply Z.eqb_eq in H. apply znz_bij. apply H.
    intros.  rewrite H. unfold Gbool_eq_init. apply Z.eqb_eq. trivial.
Qed.

Lemma beq_postive_ok_false :
  forall x y : positive, Pos.eqb x y = false <-> x <> y.
Proof.
  intros. split. intros. apply not_true_iff_false in H. unfold not in *.
  intros. apply H. rewrite H0. auto. apply Pos.eqb_eq. trivial.
  intros. apply not_true_iff_false. unfold not in *.
  intros. apply H. apply Pos.eqb_eq in H0. trivial.
Qed.


End HeliosIACR2018.

(* Group *)

Module HeliosIACR2018G <: GroupSig.
  Definition G := G.
  Definition Gdot := Gdot.
  Definition Gone := Gone.
  Definition Ggen := Gone.
  Definition Gbool_eq := Gbool_eq_init.
  Definition Gdisjoint a b := negb (Gbool_eq_init a b).
  Definition Ginv := Ginv.

  Lemma module_abegrp : AbeGroup G Gdot Gone Gbool_eq Gdisjoint Ginv.
  Proof.
    constructor. constructor. constructor.
    + intros. rewrite eq_proj. do 2 rewrite Gdot_FpMul_eq. rewrite Rmul_assoc.
    do 2 rewrite <- Gdot_FpMul_eq. trivial. apply Fpfield.
    + intros. rewrite eq_proj. rewrite Gdot_FpMul_eq. rewrite Rmul_1_l.
    trivial. apply Fpfield.
    + intros. rewrite eq_proj. rewrite Gdot_FpMul_eq. rewrite Rmul_comm.
     rewrite Rmul_1_l. trivial. apply Fpfield. apply Fpfield.
    + split. intros. unfold Gbool_eq in H. apply Z.eqb_eq in H.
      rewrite eq_proj. apply znz_bij. apply H.
      intros.  rewrite H. unfold Gbool_eq. apply Z.eqb_eq. trivial.
    + intros. unfold Gbool_eq, Gbool_eq_init. destruct (val P (proj1_sig a));
      destruct (val P (proj1_sig b)); trivial. apply eq_true_iff_eq. split;
      intros. apply Z.eqb_eq. apply Z.eqb_eq in H. symmetry. trivial.
      apply Z.eqb_eq. apply Z.eqb_eq in H. symmetry. trivial.
      apply eq_true_iff_eq. split;
      intros. apply Z.eqb_eq. apply Z.eqb_eq in H. symmetry. trivial.
      apply Z.eqb_eq. apply Z.eqb_eq in H. symmetry. trivial.
    + split. intros. unfold not. intros. rewrite eq_proj in H0. rewrite (znz_bij P) in H0.
      apply Z.eqb_eq in H0. unfold Gbool_eq in H.
      apply (eq_true_false_abs (val P (proj1_sig a) =? val P (proj1_sig b))).
      apply H0. apply H. intros. unfold Gbool_eq. unfold Gbool_eq_init.
      rewrite Z.eqb_neq. rewrite eq_proj in H.
      unfold not. intros. apply znz_bij in H0. auto.
    + intros.  unfold Gdisjoint, Gbool_eq_init. destruct (val P (proj1_sig a));
      destruct (val P (proj1_sig b)); trivial. apply eq_true_iff_eq. split;
      intros. apply negb_true_iff. apply negb_true_iff in H.
      apply beq_postive_ok_false in H. apply beq_postive_ok_false. unfold not in *.
      intros.  apply H. rewrite H0. trivial.
      apply negb_true_iff. apply negb_true_iff in H.
      apply beq_postive_ok_false in H. apply beq_postive_ok_false. unfold not in *.
      intros.  apply H. rewrite H0. trivial.
      apply eq_true_iff_eq. split;
      intros. apply negb_true_iff. apply negb_true_iff in H.
      apply beq_postive_ok_false in H. apply beq_postive_ok_false. unfold not in *.
      intros.  apply H. rewrite H0. trivial.
      apply negb_true_iff. apply negb_true_iff in H.
      apply beq_postive_ok_false in H. apply beq_postive_ok_false. unfold not in *.
      intros.  apply H. rewrite H0. trivial.
    + intros. unfold Gdisjoint, Gbool_eq_init in H. apply negb_true_iff in H.
      apply not_true_iff_false in H. unfold not in *. intros. apply H. rewrite H0.
      apply Z.eqb_eq. trivial.
    + intros. rewrite eq_proj. rewrite Gdot_FpMul_eq. symmetry. cbn in *.
       rewrite Finv_l. trivial. apply Fpfield. apply (inQSubGroup_zero_free (proj1_sig x)(Z.to_nat Q)).
       rewrite <- binary_power_ok. apply (proj2_sig x). apply Q_nat_nonzero.
    + intros. rewrite eq_proj. rewrite Gdot_FpMul_eq. symmetry. cbn in *. rewrite Rmul_comm.
       rewrite Finv_l. trivial. apply Fpfield. apply (inQSubGroup_zero_free (proj1_sig x)(Z.to_nat Q)).
       rewrite <- binary_power_ok. apply (proj2_sig x). apply Q_nat_nonzero. apply Fpfield.
    + intros. rewrite eq_proj. rewrite Gdot_FpMul_eq. cbn in *.  rewrite Rmul_comm.
       trivial. apply Fpfield.
  Qed.

End HeliosIACR2018G.

(* Field *)

Module HeliosIACR2018F <: FieldSig.
  Definition F := F.
  Definition Fadd := Fadd.
  Definition Fzero := Fzero.
  Definition Fbool_eq :=Fbool_eq_init.
  Definition Fsub := Fsub.
  Definition Finv := Finv.
  Definition Fmul := Fmul.
  Definition Fone := Fone.
  Definition FmulInv := FmulInv.
  Definition Fdiv := Fdiv.

  Lemma vs_field : field_theory Fzero Fone Fadd Fmul Fsub Finv Fdiv FmulInv (@eq F).
  Proof.
    apply Ffield.
  Qed.
  
  Lemma module_ring : ring_theory  Fzero Fone Fadd Fmul Fsub Finv (@eq F).
  Proof.
    apply vs_field.
  Qed.

  Lemma F_bool_eq_corr: forall a b : F, Fbool_eq a b = true <-> a=b.
  Proof.
    apply beq_F_ok.
  Qed.

  Lemma F_bool_eq_sym : forall a b : F, Fbool_eq a b = Fbool_eq b a.
  Proof.
    intros. apply eq_true_iff_eq. split; intros; apply beq_F_ok;
    apply beq_F_ok in H; rewrite H; trivial.
  Qed.

  Lemma F_bool_neq_corr: forall a b : F, Fbool_eq a b = false <-> a <> b.
  Proof.
    split. intros. unfold not. intros. rewrite (znz_bij Q) in H0. apply Z.eqb_eq in H0.
      unfold Fbool_eq in H.  apply (eq_true_false_abs (val Q a =? val Q b)).
      apply H0. apply H. intros. unfold Fbool_eq. unfold Fbool_eq_init.
      rewrite Z.eqb_neq. unfold not. intros. apply znz_bij in H0. auto.
  Qed.
  
  Add Field vs_field : vs_field.
  Add Ring module_ring : module_ring.
End HeliosIACR2018F.

(* The vector space *)

Module HeliosIACR2018VS <: VectorSpaceSig HeliosIACR2018G HeliosIACR2018F.

  Definition op := op.

  Lemma mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
  Proof.
      intros. rewrite eq_proj. rewrite op_binary_power_eq. do 2 rewrite Gdot_FpMul_eq.
      do 2 rewrite op_binary_power_eq. rewrite binary_power_ok.
     rewrite dist_power_over_mult. do 2 rewrite binary_power_ok. trivial.
  Qed.

  Lemma mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
  Proof.
       intros. rewrite eq_proj. rewrite Gdot_FpMul_eq. do 3 rewrite op_binary_power_eq.
       do 3 rewrite binary_power_ok. rewrite <- dist_power_over_add.
       rewrite Fadd_eq_Nadd_mod. do 2 rewrite <- binary_power_ok. apply dist_power_over_add_2.
  Qed.

  Lemma mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
  Proof.
      intros.  rewrite eq_proj. do 3 rewrite op_binary_power_eq.
      rewrite <- dist_power_over_mul_2. rewrite Fmul_eq_Nmul. rewrite dist_power_over_add_2.
      trivial.
  Qed.

  Lemma mod_id : forall (x : G), op x Fone = x.
  Proof.
    intros. rewrite eq_proj.  rewrite op_binary_power_eq. cbn. rewrite Pos2Nat.inj_1.
      cbn. apply Fpfield.
  Qed.
    
  Lemma mod_ann : forall (x : G), op x Fzero = Gone.
  Proof.
     intros. rewrite eq_proj.  rewrite op_binary_power_eq. cbn.
     trivial.
  Qed.

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

End HeliosIACR2018VS.




