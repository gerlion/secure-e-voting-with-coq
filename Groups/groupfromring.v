Require Import Ring.
From Groups Require Import groups module.

Module Type GroupFromRing (Ring : RingSig) <: GroupSig.

  Import Ring.

  Definition G := F.
  Definition Gdot := Fadd.
  Definition Gone := Fzero.
  Definition Gbool_eq := Fbool_eq.
  Definition Ginv := Finv.

  Lemma module_abegrp : AbeGroup G Gdot Gone Gbool_eq Ginv.
  Proof.
    pose module_ring. 
    constructor. constructor. constructor. 
    intros. unfold Gdot, G in *. ring; auto.
    intros. unfold Gdot, G, Gone in *. ring; auto.
    intros. unfold Gdot, G, Gone in *. ring; auto.
    intros. apply F_bool_eq_corr.
    intros. apply F_bool_neq_corr.
    intros. unfold Gdot, G, Gone, Ginv in *. ring; auto.
    intros. unfold Gdot, G, Gone, Ginv in *. ring; auto.
    intros. unfold Gdot, G in *. ring; auto.
  Qed.

End GroupFromRing. 