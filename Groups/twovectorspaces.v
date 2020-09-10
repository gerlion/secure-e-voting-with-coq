Require Import Bool.
Require Import Setoid.
Require Import Ring.
Require Import Field.
Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import groups.
Require Import vectorspace.
Require Import dualvectorspaces.
Require Import module.

(* We now define the isomorphic vector spaces we will use in the mixnets *)
(* The name is now slightly confusing *)

Module Type TwoVectorSpacesWithSameField (MVS : VectorSpaceModuleSameGroup).
  (* Field *)
  Parameter F : Set.
  Parameter Fadd : F -> F -> F. 
  Parameter Fzero : F.
  Parameter Fbool_eq : F-> F-> bool.
  Parameter Fsub : F -> F -> F.
  Parameter Finv : F -> F.
  Parameter Fmul : F -> F -> F.
  Parameter Fone : F.
  Parameter FmulInv : F -> F.
  Parameter Fdiv : F-> F-> F.

  Axiom vs_field : field_theory Fzero Fone Fadd Fmul Fsub Finv Fdiv FmulInv (@eq F).

  (* Ring *)
  Parameter R : Set.
  Parameter Radd : R -> R -> R. 
  Parameter Rzero : R.
  Parameter Rbool_eq : R-> R-> bool.
  Parameter Rsub : R -> R -> R.
  Parameter Rinv : R -> R.
  Parameter Rmul : R -> R -> R.
  Parameter Rone : R.

  Axiom vs_ring : ring_theory Rzero Rone Radd Rmul Rsub Rinv (@eq R).

  (* Group 1, by convetion the encryption scheme *)
  Parameter G1 : Set.
  Parameter G1dot : G1 -> G1 -> G1.
  Parameter G1one : G1.
  Parameter G1bool_eq : G1-> G1-> bool.
  Parameter G1inv : G1 -> G1.
  Parameter op1 : G1 -> F -> G1.

  (* Group 2, by convetion the commitments *)
  Parameter G2 : Set.
  Parameter G2dot : G2 -> G2 -> G2.
  Parameter G2one : G2.
  Parameter G2bool_eq : G2-> G2-> bool.
  Parameter G2inv : G2 -> G2.
  Parameter op2 : G2 -> F -> G2.

  Parameter op3 : G1 -> R -> G1.
  Parameter op4 : R -> F -> R.


  Parameter MVS : VectorSpaceModuleSameGroup.


    Definition F := F.
    Definition Fadd := Fadd. 
    Definition Fzero := Fzero.
    Definition Fbool_eq := Fbool_eq.
    Definition Fsub := Fsub.
    Definition Finv := Finv.
    Definition Fmul := Fmul.
    Definition Fone := Fone.
    Definition FmulInv := FmulInv.
    Definition Fdiv := Fdiv.

    Axiom vs_field : field_theory Fzero Fone Fadd Fmul Fsub Finv Fdiv FmulInv (@eq F).

    Definition R := R.
    Definition Radd := Radd. 
    Definition Rzero := Rzero.
    Definition Rbool_eq := Rbool_eq.
    Definition Rsub := Rsub.
    Definition Rinv := Rinv.
    Definition Rmul := Rmul.
    Definition Rone := Rone.

    Axiom vs_ring : ring_theory Rzero Rone Radd Rmul Rsub Rinv (@eq R).

    Definition G := G1.
    Definition Gdot (a b : G1) : G1 := G1dot a b.
    Definition Gone := G1one.
    Definition Gbool_eq (a b : G) := G1bool_eq a b.
    Definition Ginv a := G1inv a.
    Definition op1 := op1.
    Definition op2 := op3.
    Definition op3 := op4.

    Module VS <: VectorSpaceSig.
        Definition F := F.
        Definition Fadd := Fadd. 
        Definition Fzero := Fzero.
        Definition Fbool_eq := Fbool_eq.
        Definition Fsub := Fsub.
        Definition Finv := Finv.
        Definition Fmul := Fmul.
        Definition Fone := Fone.
        Definition FmulInv := FmulInv.
        Definition Fdiv := Fdiv.
        Definition G := G.
        Definition Gdot (a b : G) : G := Gdot a b.
        Definition Gone := Gone.
        Definition Gbool_eq (a b : G) := Gbool_eq a b.
        Definition Ginv a := Ginv a.
        Definition op a b := op1 a b.

        Axiom vs_field : field_theory Fzero Fone Fadd Fmul Fsub Finv Fdiv FmulInv (@eq F).
        Axiom module_ring : ring_theory Fzero Fone Fadd Fmul Fsub Finv (@eq F).
        Axiom module_abegrp : AbeGroup G Gdot Gone Gbool_eq Ginv.

        Axiom mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
        Axiom mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
        Axiom mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
        Axiom mod_id : forall (x : G), op x Fone = x.
        Axiom mod_ann : forall (x : G), op x Fzero = Gone.

        Axiom F_bool_eq_corr: forall a b : F, Fbool_eq a b = true <-> a=b.
        Axiom  F_bool_neq_corr: forall a b : F, Fbool_eq a b = false <-> a <> b.

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

        Add Field vs_field : vs_field.
        Add Ring module_ring : module_ring.
      End VS.

      Module M <: ModuleSig.
        Definition F := R.
        Definition Fadd := Radd. 
        Definition Fzero := Rzero.
        Definition Fbool_eq := Rbool_eq.
        Definition Fsub := Rsub.
        Definition Finv := Rinv.
        Definition Fmul := Rmul.
        Definition Fone := Rone.
        Definition G := G.
        Definition Gdot (a b : G) : G := Gdot a b.
        Definition Gone := Gone.
        Definition Gbool_eq (a b : G) := Gbool_eq a b.
        Definition Ginv a := Ginv a.
        Definition op a b := op2 a b.

        Axiom module_ring : ring_theory Fzero Fone Fadd Fmul Fsub Finv (@eq F).
        Axiom module_abegrp : AbeGroup G Gdot Gone Gbool_eq Ginv.

        Axiom mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
        Axiom mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
        Axiom mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
        Axiom mod_id : forall (x : G), op x Fone = x.
        Axiom mod_ann : forall (x : G), op x Fzero = Gone.

        Axiom F_bool_eq_corr: forall a b : F, Fbool_eq a b = true <-> a=b.
        Axiom  F_bool_neq_corr: forall a b : F, Fbool_eq a b = false <-> a <> b.

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

        Add Field vs_field : vs_field.
        Add Ring module_ring : module_ring.
      End M.
  End MVS.

  Module VS <: VectorSpaceSig.
    Definition F := F.
    Definition Fadd := Fadd. 
    Definition Fzero := Fzero.
    Definition Fbool_eq := Fbool_eq.
    Definition Fsub := Fsub.
    Definition Finv := Finv.
    Definition Fmul := Fmul.
    Definition Fone := Fone.
    Definition FmulInv := FmulInv.
    Definition Fdiv := Fdiv.
    Definition G := G2.
    Definition Gdot (a b : G2) : G2 := G2dot a b.
    Definition Gone := G2one.
    Definition Gbool_eq (a b : G) := G2bool_eq a b.
    Definition Ginv a := G2inv a.
    Definition op a b := op2 a b.

    Axiom vs_field : field_theory Fzero Fone Fadd Fmul Fsub Finv Fdiv FmulInv (@eq F).
    Axiom module_ring : ring_theory Fzero Fone Fadd Fmul Fsub Finv (@eq F).
    Axiom module_abegrp : AbeGroup G Gdot Gone Gbool_eq Ginv.

    Axiom mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
    Axiom mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
    Axiom mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
    Axiom mod_id : forall (x : G), op x Fone = x.
    Axiom mod_ann : forall (x : G), op x Fzero = Gone.

    Axiom F_bool_eq_corr: forall a b : F, Fbool_eq a b = true <-> a=b.
    Axiom  F_bool_neq_corr: forall a b : F, Fbool_eq a b = false <-> a <> b.

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

    Add Field vs_field : vs_field.
    Add Ring module_ring : module_ring.
  End VS.
End TwoVectorSpacesWithSameField.

(* Module to turn out a dual vector space basic ElGamal Style *)
Module TwoVectorSpacesWithSameFieldIns (VS : VectorSpaceSig) <: TwoVectorSpacesWithSameField.
  Definition F := VS.F.
  Definition Fadd := VS.Fadd.
  Definition Fzero := VS.Fzero.
  Definition Fbool_eq := VS.Fbool_eq.
  Definition Fsub := VS.Fsub.
  Definition Finv := VS.Finv.
  Definition Fmul := VS.Fmul.
  Definition Fone := VS.Fone.
  Definition FmulInv := VS.FmulInv.
  Definition Fdiv := VS.Fdiv.


  Lemma vs_field : field_theory Fzero Fone Fadd Fmul Fsub Finv Fdiv FmulInv (@eq F).
    Proof.
      apply VS.vs_field.
    Qed.

  (* Ring *)
  Definition R := VS.F.
  Definition Radd := VS.Fadd.
  Definition Rzero := VS.Fzero.
  Definition Rbool_eq := VS.Fbool_eq.
  Definition Rsub := VS.Fsub.
  Definition Rinv := VS.Finv.
  Definition Rmul := VS.Fmul.
  Definition Rone := VS.Fone.

  Lemma vs_ring : ring_theory Rzero Rone Radd Rmul Rsub Rinv (@eq R).
  Proof.
    intros. apply VS.vs_field.
  Qed.

  Module DVS := DualVectorSpaceIns VS.

  (* Group 1 *)
  Definition G1 := DVS.G.
  Definition G1dot := DVS.Gdot.
  Definition G1one := DVS.Gone.
  Definition G1bool_eq := DVS.Gbool_eq.
  Definition G1inv := DVS.Ginv.
  Definition op1 := DVS.op.

  (* Group 2 *)
  Definition G2 := VS.G.
  Definition G2dot := VS.Gdot.
  Definition G2one := VS.Gone.
  Definition G2bool_eq := VS.Gbool_eq.
  Definition G2inv := VS.Ginv.
  Definition op2 := VS.op.

  Definition op3 := DVS.op.
  Definition op4 := VS.Fmul.

  Module MVS <: VectorSpaceModuleSameGroup.
    Definition F := F.
    Definition Fadd := Fadd. 
    Definition Fzero := Fzero.
    Definition Fbool_eq := Fbool_eq.
    Definition Fsub := Fsub.
    Definition Finv := Finv.
    Definition Fmul := Fmul.
    Definition Fone := Fone.
    Definition FmulInv := FmulInv.
    Definition Fdiv := Fdiv.

    Axiom vs_field : field_theory Fzero Fone Fadd Fmul Fsub Finv Fdiv FmulInv (@eq F).

    Definition R := R.
    Definition Radd := Radd. 
    Definition Rzero := Rzero.
    Definition Rbool_eq := Rbool_eq.
    Definition Rsub := Rsub.
    Definition Rinv := Rinv.
    Definition Rmul := Rmul.
    Definition Rone := Rone.

    Axiom vs_ring : ring_theory Rzero Rone Radd Rmul Rsub Rinv (@eq R).

    Definition G := G1.
    Definition Gdot (a b : G1) : G1 := G1dot a b.
    Definition Gone := G1one.
    Definition Gbool_eq (a b : G) := G1bool_eq a b.
    Definition Ginv a := G1inv a.
    Definition op1 := op1.
    Definition op2 := op3.
    Definition op3 := op4.

    Module VS <: VectorSpaceSig.
        Definition F := F.
        Definition Fadd := Fadd. 
        Definition Fzero := Fzero.
        Definition Fbool_eq := Fbool_eq.
        Definition Fsub := Fsub.
        Definition Finv := Finv.
        Definition Fmul := Fmul.
        Definition Fone := Fone.
        Definition FmulInv := FmulInv.
        Definition Fdiv := Fdiv.
        Definition G := G.
        Definition Gdot (a b : G) : G := Gdot a b.
        Definition Gone := Gone.
        Definition Gbool_eq (a b : G) := Gbool_eq a b.
        Definition Ginv a := Ginv a.
        Definition op a b := op1 a b.

        Axiom vs_field : field_theory Fzero Fone Fadd Fmul Fsub Finv Fdiv FmulInv (@eq F).
        Axiom module_ring : ring_theory Fzero Fone Fadd Fmul Fsub Finv (@eq F).
        Axiom module_abegrp : AbeGroup G Gdot Gone Gbool_eq Ginv.

        Axiom mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
        Axiom mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
        Axiom mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
        Axiom mod_id : forall (x : G), op x Fone = x.
        Axiom mod_ann : forall (x : G), op x Fzero = Gone.

        Axiom F_bool_eq_corr: forall a b : F, Fbool_eq a b = true <-> a=b.
        Axiom  F_bool_neq_corr: forall a b : F, Fbool_eq a b = false <-> a <> b.

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

        Add Field vs_field : vs_field.
        Add Ring module_ring : module_ring.
      End VS.

      Module M <: ModuleSig.
        Definition F := R.
        Definition Fadd := Radd. 
        Definition Fzero := Rzero.
        Definition Fbool_eq := Rbool_eq.
        Definition Fsub := Rsub.
        Definition Finv := Rinv.
        Definition Fmul := Rmul.
        Definition Fone := Rone.
        Definition G := G.
        Definition Gdot (a b : G) : G := Gdot a b.
        Definition Gone := Gone.
        Definition Gbool_eq (a b : G) := Gbool_eq a b.
        Definition Ginv a := Ginv a.
        Definition op a b := op2 a b.

        Axiom module_ring : ring_theory Fzero Fone Fadd Fmul Fsub Finv (@eq F).
        Axiom module_abegrp : AbeGroup G Gdot Gone Gbool_eq Ginv.

        Axiom mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
        Axiom mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
        Axiom mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
        Axiom mod_id : forall (x : G), op x Fone = x.
        Axiom mod_ann : forall (x : G), op x Fzero = Gone.

        Axiom F_bool_eq_corr: forall a b : F, Fbool_eq a b = true <-> a=b.
        Axiom  F_bool_neq_corr: forall a b : F, Fbool_eq a b = false <-> a <> b.

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

        Add Field vs_field : vs_field.
        Add Ring module_ring : module_ring.
      End M.
  End MVS.

  Module VS <: VectorSpaceSig.
    Definition F := F.
    Definition Fadd := Fadd. 
    Definition Fzero := Fzero.
    Definition Fbool_eq := Fbool_eq.
    Definition Fsub := Fsub.
    Definition Finv := Finv.
    Definition Fmul := Fmul.
    Definition Fone := Fone.
    Definition FmulInv := FmulInv.
    Definition Fdiv := Fdiv.
    Definition G := G2.
    Definition Gdot (a b : G2) : G2 := G2dot a b.
    Definition Gone := G2one.
    Definition Gbool_eq (a b : G) := G2bool_eq a b.
    Definition Ginv a := G2inv a.
    Definition op a b := op2 a b.

    Axiom vs_field : field_theory Fzero Fone Fadd Fmul Fsub Finv Fdiv FmulInv (@eq F).
    Axiom module_ring : ring_theory Fzero Fone Fadd Fmul Fsub Finv (@eq F).
    Axiom module_abegrp : AbeGroup G Gdot Gone Gbool_eq Ginv.

    Axiom mod_dist_Gdot : forall (r : F) (x y : G), op (Gdot x y) r = Gdot (op x r) (op y r).
    Axiom mod_dist_Fadd : forall (r s : F) (x : G), op x (Fadd r s) = Gdot (op x r) (op x s).
    Axiom mod_dist_Fmul : forall (r s: F) (x : G), op x (Fmul r s) = op (op x s) r.
    Axiom mod_id : forall (x : G), op x Fone = x.
    Axiom mod_ann : forall (x : G), op x Fzero = Gone.

    Axiom F_bool_eq_corr: forall a b : F, Fbool_eq a b = true <-> a=b.
    Axiom  F_bool_neq_corr: forall a b : F, Fbool_eq a b = false <-> a <> b.

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

    Add Field vs_field : vs_field.
    Add Ring module_ring : module_ring.
  End VS.
End TwoVectorSpacesWithSameFieldIns. 