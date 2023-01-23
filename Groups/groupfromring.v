Require Import Ring.
Require Import Field.
Require Import Bool.
Require Import Coq.Logic.Classical_Prop.
From Groups Require Import groups module vectorspace.

Module Type GroupFromRing (Ring : RingSig) <: GroupSig.

  Import Ring.

  Definition G := F.
  Definition Gdot := Fadd.
  Definition Gone := Fzero.
  Definition Ggen := Fone.
  Definition Gbool_eq := Fbool_eq.
  Definition Gdisjoint := (fun a b => negb (Fbool_eq a b)).
  Definition Ginv := Finv.

  Lemma module_abegrp : AbeGroup G Gdot Gone Gbool_eq Gdisjoint Ginv.
  Proof.
    pose module_ring. 
    constructor. constructor. constructor. 
    intros. unfold Gdot, G in *. ring; auto.
    intros. unfold Gdot, G, Gone in *. ring; auto.
    intros. unfold Gdot, G, Gone in *. ring; auto.
    intros. apply F_bool_eq_corr.
    intros. apply F_bool_eq_sym.
    intros. apply F_bool_neq_corr.
    intros. unfold Gdisjoint. rewrite F_bool_eq_sym. trivial.
    intros. unfold Gdisjoint in *. apply negb_true_iff in H.
    apply F_bool_neq_corr in H. trivial.
    intros. unfold Gdot, G, Gone, Ginv in *. ring; auto.
    intros. unfold Gdot, G, Gone, Ginv in *. ring; auto.
    intros. unfold Gdot, G in *. ring; auto.
  Qed.

End GroupFromRing. 

Module GroupFromRingIns (Ring : RingSig) <: GroupFromRing Ring.

  Import Ring.

  Definition G := F.
  Definition Gdot := Fadd.
  Definition Gone := Fzero.
  Definition Ggen := Fone.
  Definition Gbool_eq := Fbool_eq.
  Definition Gdisjoint := (fun a b => negb (Fbool_eq a b)).
  Definition Ginv := Finv.

  Lemma module_abegrp : AbeGroup G Gdot Gone Gbool_eq Gdisjoint Ginv.
  Proof.
    pose module_ring. 
    constructor. constructor. constructor. 
    intros. unfold Gdot, G in *. ring; auto.
    intros. unfold Gdot, G, Gone in *. ring; auto.
    intros. unfold Gdot, G, Gone in *. ring; auto.
    intros. apply F_bool_eq_corr.
    intros. apply F_bool_eq_sym.
    intros. apply F_bool_neq_corr.
    intros. unfold Gdisjoint. rewrite F_bool_eq_sym. trivial.
    intros. unfold Gdisjoint in *. apply negb_true_iff in H.
    apply F_bool_neq_corr in H. trivial.
    intros. unfold Gdot, G, Gone, Ginv in *. ring; auto.
    intros. unfold Gdot, G, Gone, Ginv in *. ring; auto.
    intros. unfold Gdot, G in *. ring; auto.
  Qed.

End GroupFromRingIns. 

Module Type GroupFromField (Field : FieldSig) <: GroupSig.

  Import Field.

  Definition G := {x : F | x <>0}.
  Definition Gdot (a b : G) : G.
  Proof.
    destruct a, b. exists (x*x0). unfold not in *. intros.
    case_eq (Fbool_eq x 0). intros. apply F_bool_eq_corr in H0.
    apply n. trivial. intros. apply F_bool_neq_corr in H0.
    apply n0. assert (forall (x y z : F),
    y = z -> x * y = x * z). intros. rewrite H1. trivial.
    apply (H1 (FmulInv x)) in H. destruct vs_field. destruct F_R.
    rewrite  Rmul_assoc in H. rewrite Finv_l in H. rewrite Rmul_1_l in H.
    rewrite H. field; auto. trivial.
  Defined.
  Definition Gone : G.
  Proof.
     exists Fone. destruct vs_field. trivial.
  Defined.
  Definition Ggen : G.
  Proof.
     exists Fone. destruct vs_field. trivial.
  Defined.
  Definition Gbool_eq : G -> G -> bool.
  Proof.
    intros. destruct H, H0. apply (Fbool_eq x x0).
  Defined.
  Definition Gdisjoint : G -> G -> bool.
  Proof.
    intros. destruct H, H0. apply (negb (Fbool_eq x x0)).
  Defined. 

  Definition Ginv : G -> G.
  Proof.
    intros. destruct H. exists (FmulInv x). destruct vs_field. destruct F_R.
    unfold not. intros. apply n. assert (forall (x y z : F),
    y = z -> y * x = z * x). intros. rewrite H0. trivial.
    apply (H0 x) in H. rewrite Finv_l in H. assert (0 * x = 0).
    field; auto. rewrite H1 in H. contradiction. trivial.
  Defined.

  Lemma eq_proj:
  forall a b : G,
  a = b <-> proj1_sig(a) = proj1_sig(b).
  Proof.
    split; intros.
    + rewrite H. auto.
    + destruct a, b. cbn in *.
      subst. f_equal. unfold not in *. apply proof_irrelevance.
  Qed.


  Lemma module_abegrp : AbeGroup G Gdot Gone Gbool_eq Gdisjoint Ginv.
  Proof.
    pose vs_field. destruct f. destruct F_R.
    constructor. constructor. constructor. 
    intros. destruct x, y, z. unfold Gdot. apply eq_proj.
    simpl. rewrite Rmul_assoc. trivial.
    intros. destruct x. unfold Gdot, G, Gone in *. apply eq_proj.
    simpl. ring; auto.
    intros. destruct x. unfold Gdot, G, Gone in *. apply eq_proj.
    simpl. ring; auto.
    intros.  destruct a,b. unfold Gbool_eq, G, Gone in *. split; intros. 
    apply eq_proj. simpl. apply F_bool_eq_corr. trivial. apply eq_proj in H.
    simpl in H. apply F_bool_eq_corr. trivial.
    intros. unfold Gbool_eq. destruct a, b. simpl. apply F_bool_eq_sym.
    intros. destruct a,b. unfold Gbool_eq, G, Gone in *. split; intros. 
    unfold not. intros. apply F_bool_neq_corr in H. unfold not in H. apply H.
    apply eq_proj in H0. simpl in H0.  trivial. apply F_bool_neq_corr. 
    unfold not in *. intros. apply H. apply eq_proj. simpl. trivial.
    intros. unfold Gdisjoint. destruct a, b. simpl. rewrite F_bool_eq_sym.
    trivial.
    intros. unfold Gdisjoint in H. destruct a, b. simpl. unfold not in *.
    apply negb_true_iff in H. apply F_bool_neq_corr in H. intros; simpl in *.
    unfold not in *. apply H. apply eq_proj in H0. simpl in *. trivial.
    intros. destruct x. unfold Gdot, G, Gone, Ginv in *. apply eq_proj. 
    simpl. field; auto.
    intros. destruct x. unfold Gdot, G, Gone, Ginv in *. apply eq_proj. 
    simpl. field; auto.
    intros. destruct a, b. unfold Gdot, G in *. apply eq_proj. 
    simpl. field; auto.
  Qed.

End GroupFromField. 

Module GroupFromFieldIns (Field : FieldSig) <: GroupSig.

  Import Field.

  Definition G := {x : F | x <>0}.
  Definition Gdot (a b : G) : G.
  Proof.
    destruct a, b. exists (x*x0). unfold not in *. intros.
    case_eq (Fbool_eq x 0). intros. apply F_bool_eq_corr in H0.
    apply n. trivial. intros. apply F_bool_neq_corr in H0.
    apply n0. assert (forall (x y z : F),
    y = z -> x * y = x * z). intros. rewrite H1. trivial.
    apply (H1 (FmulInv x)) in H. destruct vs_field. destruct F_R.
    rewrite  Rmul_assoc in H. rewrite Finv_l in H. rewrite Rmul_1_l in H.
    rewrite H. field; auto. trivial.
  Defined.
  Definition Gone : G.
  Proof.
     exists Fone. destruct vs_field. trivial.
  Defined.
  Definition Ggen : G.
  Proof.
     exists Fone. destruct vs_field. trivial.
  Defined.
  Definition Gbool_eq : G -> G -> bool.
  Proof.
    intros. destruct H, H0. apply (Fbool_eq x x0).
  Defined.
  Definition Gdisjoint : G -> G -> bool.
  Proof.
    intros. destruct H, H0. apply (negb (Fbool_eq x x0)).
  Defined. 
  Definition Ginv : G -> G.
  Proof.
    intros. destruct H. exists (FmulInv x). destruct vs_field. destruct F_R.
    unfold not. intros. apply n. assert (forall (x y z : F),
    y = z -> y * x = z * x). intros. rewrite H0. trivial.
    apply (H0 x) in H. rewrite Finv_l in H. assert (0 * x = 0).
    field; auto. rewrite H1 in H. contradiction. trivial.
  Defined.

  Lemma eq_proj:
  forall a b : G,
  a = b <-> proj1_sig(a) = proj1_sig(b).
  Proof.
    split; intros.
    + rewrite H. auto.
    + destruct a, b. cbn in *.
      subst. f_equal. unfold not in *. apply proof_irrelevance.
  Qed.


  Lemma module_abegrp : AbeGroup G Gdot Gone Gbool_eq Gdisjoint Ginv.
  Proof.
    pose vs_field. destruct f. destruct F_R.
    constructor. constructor. constructor. 
    intros. destruct x, y, z. unfold Gdot. apply eq_proj.
    simpl. rewrite Rmul_assoc. trivial.
    intros. destruct x. unfold Gdot, G, Gone in *. apply eq_proj.
    simpl. ring; auto.
    intros. destruct x. unfold Gdot, G, Gone in *. apply eq_proj.
    simpl. ring; auto.
    intros.  destruct a,b. unfold Gbool_eq, G, Gone in *. split; intros. 
    apply eq_proj. simpl. apply F_bool_eq_corr. trivial. apply eq_proj in H.
    simpl in H. apply F_bool_eq_corr. trivial.
    intros. unfold Gbool_eq. destruct a, b. simpl. apply F_bool_eq_sym.
    intros. destruct a,b. unfold Gbool_eq, G, Gone in *. split; intros. 
    unfold not. intros. apply F_bool_neq_corr in H. unfold not in H. apply H.
    apply eq_proj in H0. simpl in H0.  trivial. apply F_bool_neq_corr. 
    unfold not in *. intros. apply H. apply eq_proj. simpl. trivial.
    intros. unfold Gdisjoint. destruct a, b. simpl. rewrite F_bool_eq_sym.
    trivial.
    intros. unfold Gdisjoint in H. destruct a, b. simpl. unfold not in *.
    apply negb_true_iff in H. apply F_bool_neq_corr in H. intros; simpl in *.
    unfold not in *. apply H. apply eq_proj in H0. simpl in *. trivial.
    intros. destruct x. unfold Gdot, G, Gone, Ginv in *. apply eq_proj. 
    simpl. field; auto.
    intros. destruct x. unfold Gdot, G, Gone, Ginv in *. apply eq_proj. 
    simpl. field; auto.
    intros. destruct a, b. unfold Gdot, G in *. apply eq_proj. 
    simpl. field; auto.
  Qed.

End GroupFromFieldIns. 
