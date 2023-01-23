Require Import Bool.
Require Import Setoid.
Require Import Ring.
Require Import Field.
Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import groups.
Require Import vectorspace.
Require Import module.

(* We now define the isomorphic vector spaces we will use in the mixnets *)

Module Type VectorSpaceModuleSameGroup (Group : GroupSig)(Ring : RingSig)
     (Field : FieldSig)(VS : VectorSpaceSig Group Field).
  Export Group.
  Export VS.

  Parameter op3 : Ring.F -> Field.F -> Ring.F.

  Axiom RopInv : forall a, op3 a (Field.Finv Fone) = Ring.Finv a.
  Axiom RopInvDis : forall a b, op3 (Ring.Finv a) b = Ring.Finv (op3 a b).
    Axiom RopFZero : forall x, op3 x Fzero = Ring.Fzero.
    Axiom RopFOne : forall x, op3 x Fone = x.
    Axiom RopRZero : forall x, op3 Ring.Fzero x = Ring.Fzero.
    Axiom RopDistRadd : forall x y z, op3 (Ring.Fadd x y) z = 
      Ring.Fadd (op3 x z) (op3 y z).
    Axiom RopDistFadd : forall (r s : F) (x : Ring.F), 
      op3 x (Fadd r s) = Ring.Fadd (op3 x r) (op3 x s).
    Axiom RopDistFmul : forall x y z, op3 (op3 x y) z = 
      op3 x (Fmul y z).
    Axiom RaddInv : forall (a : Ring.F)(b : F),
     (Ring.Fadd (op3 a b) (op3 a (Finv b))) = Ring.Fzero.
End VectorSpaceModuleSameGroup.

Module Type VectorSpaceModuleSameGroupIns (Group : GroupSig)
     (Field : FieldSig)(VS : VectorSpaceSig Group Field)
      <: VectorSpaceModuleSameGroup Group Field Field VS.
  Export Group.
  Export VS.

  Definition op3 := Field.Fmul.

  Lemma RopInv : forall a, op3 a (Field.Finv Fone) = Field.Finv a.
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
  Lemma RopInvDis : forall a b, op3 (Field.Finv a) b = Field.Finv (op3 a b).
  Proof.
    intros. unfold op3. field; auto.
  Qed.
  Lemma RopFZero : forall x, op3 x Fzero = Field.Fzero.
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
  Lemma RopFOne : forall x, op3 x Fone = x.
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
  Lemma RopRZero : forall x, op3 Field.Fzero x = Field.Fzero.
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
  Lemma RopDistRadd : forall x y z, op3 (Field.Fadd x y) z = 
      Field.Fadd (op3 x z) (op3 y z).
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
  Lemma RopDistFadd : forall (r s : F) (x : Field.F), 
      op3 x (Fadd r s) = Field.Fadd (op3 x r) (op3 x s).
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
  Lemma RopDistFmul : forall x y z, op3 (op3 x y) z = 
      op3 x (Fmul y z).
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
  Lemma RaddInv : forall (a : Field.F)(b : F),
     (Field.Fadd (op3 a b) (op3 a (Finv b))) = Field.Fzero.
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
End VectorSpaceModuleSameGroupIns.

(* Can the naming convention get any worse? *)
Module VectorSpaceModuleSameGroupInsIns (Group : GroupSig)
     (Field : FieldSig)(VS : VectorSpaceSig Group Field)
      <: VectorSpaceModuleSameGroup Group Field Field VS.
  Export Group.
  Export VS.

  Definition op3 := Field.Fmul.

  Lemma RopInv : forall a, op3 a (Field.Finv Fone) = Field.Finv a.
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
  Lemma RopInvDis : forall a b, op3 (Field.Finv a) b = Field.Finv (op3 a b).
  Proof.
    intros. unfold op3. field; auto.
  Qed.
  Lemma RopFZero : forall x, op3 x Fzero = Field.Fzero.
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
  Lemma RopFOne : forall x, op3 x Fone = x.
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
  Lemma RopRZero : forall x, op3 Field.Fzero x = Field.Fzero.
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
  Lemma RopDistRadd : forall x y z, op3 (Field.Fadd x y) z = 
      Field.Fadd (op3 x z) (op3 y z).
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
  Lemma RopDistFadd : forall (r s : F) (x : Field.F), 
      op3 x (Fadd r s) = Field.Fadd (op3 x r) (op3 x s).
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
  Lemma RopDistFmul : forall x y z, op3 (op3 x y) z = 
      op3 x (Fmul y z).
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
  Lemma RaddInv : forall (a : Field.F)(b : F),
     (Field.Fadd (op3 a b) (op3 a (Finv b))) = Field.Fzero.
  Proof. 
    intros. unfold op3. field; auto.
  Qed.
End VectorSpaceModuleSameGroupInsIns.