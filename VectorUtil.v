Require Coq.Program.Tactics.
From CoLoR Require Import RelDec OrdSemiRing LogicUtil RelExtras EqUtil NatUtil ZUtil SemiRing.
Require Import Coq.Vectors.Vector.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import CoLoR.Util.Vector.VecArith.
Require Import ssreflect ssrfun ssrbool.
Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Notation " [ ] " := Vnil.
Notation " [ x ] " := (Vcons x Vnil).
Notation " [ x ; .. ; y ] " := (Vcons x .. (Vcons y Vnil) ..).
Set Implicit Arguments.

Section VectorUtil.
  
  Lemma Vtail_imp : forall (A : Type)(n : nat)(a : A)(b : vector A n)
      (c : vector A (S n)),
    Vcons a b = c -> b = Vtail c.
  Proof.
    intros. rewrite <- H. auto.
  Qed.

  Lemma Vnth_map_nil : forall (A B : Type)(f : A -> B),
    Vmap f [] = [].
  Proof.
    intros. cbn. trivial.
  Qed.

  Lemma Vnth_map2_nil : forall (A B C : Type)(f : A -> B -> C),
    Vmap2 f [] [] = [].
  Proof.
    intros. cbn. trivial.
  Qed.

  Lemma Veq_nth3 : forall (n : nat)(A : Type)(v v' : vector A n),
    (forall i j (ip : i < n)(jp : j < n),
    i = j -> v = v' -> Vnth v ip = Vnth v' jp).
  Proof.
    intros. subst. apply Vnth_eq. trivial.
  Qed.

  Lemma Veq_nth4 : forall (n i : nat)(A : Type)(v v' : vector A n)(ip : i < n),
    v = v' -> Vnth v ip = Vnth v' ip.
  Proof.
   intros. rewrite H. trivial.
  Qed.

  Lemma Veq_nth2 : forall (n : nat)(A : Type)(v v' : vector A n),
    v = v' -> (forall i (ip : i < n), Vnth v ip = Vnth v' ip).
  Proof.
   intros. rewrite H. trivial.
  Qed.

  Lemma Vfold_left_eq : forall (n : nat)(A B : Type) (f : A->B->A)
    (v v' : vector B n)(a : A),
    v = v' -> Vfold_left f a v = Vfold_left f a v'.
  Proof.
    intros. rewrite H. trivial.
  Qed.

  Lemma Vcons_map2 : forall (A B C : Type) (f: A->B->C) (n :nat)
          (v : vector A n) (v' : vector B n)(a : A)(b : B),
      Vmap2 f (Vcons a v) (Vcons b v') = Vcons (f a b) (Vmap2 f v v').
  Proof. 
    intros. refl. 
  Qed.

  Lemma Vadd_map2 : forall (A B C : Type) (f: A->B->C) (n :nat)
          (v : vector A n) (v' : vector B n)(a : A)(b : B),
      Vmap2 f (Vadd v a) (Vadd v' b) = Vadd (Vmap2 f v v') (f a b).
  Proof. 
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_add. 
    destruct (Nat.eq_dec i n). trivial. rewrite Vnth_map2. trivial.
  Qed.

  Lemma Vapp_map2 : forall (A B C : Type) (f: A->B->C) (n n' :nat)
          (v : vector A n)(v' : vector B n)(u : vector A n')(u' : vector B n'),
    Vmap2 f (Vapp v u) (Vapp v' u') = Vapp (Vmap2 f v v') (Vmap2 f u u').
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_app.
    destruct (le_gt_dec n i). rewrite Vnth_map2. trivial.
    rewrite Vnth_map2. trivial.
  Qed.

  Lemma Vcons_map : forall (A B : Type) (f: A->B) (n :nat)
          (v : vector A n)(a : A),
      Vmap f (Vcons a v) = Vcons (f a) (Vmap f v).
  Proof. 
    intros. refl. 
  Qed.
  
 Definition Vector_0_is_nil (A : Type)(v : Vector.t A 0) : v = Vector.nil :=
  match v with Vector.nil => eq_refl end.

  Lemma Vfold_left_head : forall (A : Type) (f : A->A->A)(v : vector A 1)(a : A),
    (forall b, f a b = b) ->
    Vfold_left f a v = Vhead v.
  Proof.
    intros. cbn. rewrite (VSn_eq v). rewrite (Vector_0_is_nil (Vtail v)). cbn.
    rewrite H. trivial.
  Qed. 

  Lemma Vfold_left_eq_gen : forall (n n' : nat)(H : n = n')
   (A B : Type) (f : A->B->A)(v : vector B n)(v' : vector B n')(a : A),
    Vcast (v) H = v' -> Vfold_left f a v = Vfold_left f a v'.
  Proof.
    intros. subst. rewrite Vcast_refl. trivial.
  Qed.

  Lemma Vfold_left_cast_irr : forall (n n' : nat)(H : n = n')
   (A B : Type) (f : A->B->A)(v : vector B n)(a : A),
    Vfold_left f a v = Vfold_left f a (Vcast v H).
  Proof.
    intros. subst. rewrite Vcast_refl. trivial.
  Qed.

  Lemma Veq_nth3_gen : forall (n n' : nat)(H : n = n')(A : Type)
    (v : vector A n)(v' : vector A n'),
    (forall i j (ip : i < n)(jp : j < n'),
    i = j -> Vcast v H = v' -> Vnth v ip = Vnth v' jp).
  Proof.
    intros. subst. rewrite Vcast_refl. apply Vnth_eq. trivial.
  Qed.
  
  Lemma Vfold_left_const :forall (A : Type)(f : A -> A -> A)
    (n : nat)(v : vector A n)(acc h : A),
    (forall a b c, f (f a b) c = f a (f b c)) ->
    (forall a b, f a b = f b a) ->
    Vfold_left f (f acc h) v = f (Vfold_left f acc v) h.
  Proof.
    intros A f n v. induction v. intros. cbn. trivial.
    intros. simpl. replace (f (f acc h0) h) with (f (f acc h) h0).
    rewrite IHv; auto. do 2 rewrite H. replace (f h h0) with (f h0 h) by apply H0.
    trivial.
  Qed.

  Lemma Vfold_left_Vcons : forall (A : Type)(f : A -> A -> A)
    (n : nat)(v : vector A n)(acc h : A),
    (forall a b c, f (f a b) c = f a (f b c)) ->
    (forall a b, f a b = f b a) ->
    Vfold_left f acc (Vcons h v) = f h (Vfold_left f acc v).
  Proof.
    intros A f n v. induction v. intros. cbn. apply H0.
    cbn. intros. cbn. rewrite <- IHv; auto. cbn. 
    do 2 rewrite H. replace (f h h0) with (f h0 h) by apply H0.
    trivial.
  Qed.

  Lemma Vfold_left_induction : forall (A : Type)(f : A -> A -> A)
    (n : nat)(v : vector A (S n))(acc : A),
    (forall a b c, f (f a b) c = f a (f b c)) ->
    (forall a b, f a b = f b a) ->
    Vfold_left f acc v = f (Vhead v) (Vfold_left f acc (Vtail v)).
  Proof.
    intros. remember (f (Vhead v) (Vfold_left f acc (Vtail v))) as b.
    rewrite (VSn_eq v). rewrite Heqb. cbn. rewrite Vfold_left_const; auto.
  Qed.

  Lemma invertPos : forall i n (ip : i < n),
    (n-i-1) < n. 
  Proof.
    intros. lia.
  Defined.

  Lemma invertPosCancel : forall (A : Type) i n (ip : i < n)
      (a : vector A n),
    Vnth a (invertPos (invertPos ip)) = Vnth a ip.
  Proof.
    intros. apply Vnth_eq. lia.
  Qed.

  Definition rev (A : Type)(n : nat)(input : vector A n) :=
    Vbuild (fun i (ip : i < n) => Vnth input (invertPos ip)).

  Lemma rev_rev : forall (A : Type)(n : nat)(a : vector A n),
    rev (rev a) = a.
  Proof.
    intros. apply Veq_nth. intros. do 2 rewrite Vbuild_nth. apply Vnth_eq.
    lia.
  Qed.
  
  Lemma rev_Vcons : forall (A : Type)(n : nat)(a : A)(b : vector A n),
    rev (Vcons a b) = Vadd (rev b) a.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth.
    rewrite Vnth_add. case (Nat.eq_dec i n). intros.
    rewrite Vnth_cons_head. rewrite e. lia. trivial.
    intros. rewrite Vnth_cons_tail. intros. rewrite Vbuild_nth.
    apply Vnth_eq. lia. lia.
  Qed.

  Lemma Vcons_rev : forall (A : Type)(n : nat)(a : A)(b : vector A n),
    Vcons a (rev b) = rev (Vadd b a).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth.
    rewrite Vnth_add. case (Nat.eq_dec (S n - i - 1) n). intros.
    rewrite Vnth_cons_head.  lia. trivial.
    intros. rewrite Vnth_cons_tail. intros. rewrite Vbuild_nth.
    apply Vnth_eq. lia. lia.
  Qed.

  Lemma rev_switch: forall (A : Type)(n : nat)(a b : vector A n),
    rev a = b <-> a =rev b.
  Proof.
    intros. intros. unfold iff. refine (conj _ _).
    intros. rewrite <- H. rewrite rev_rev. trivial.
    intros. rewrite H.  rewrite rev_rev. trivial.
  Qed.

  Lemma Vmap2_Vcast_out : forall (A B C D E : Type)(n m : nat)(H : n=m)(H' : m=n)
    (f : A -> B -> E) (a : vector A n)(b: vector B m),
    Vmap2 f (Vcast a H) b = Vcast (Vmap2 f a (Vcast b H')) H.
  Proof.
    intros. subst. apply Veq_nth. intros. simpl. do 2 rewrite Vnth_map2.
    apply f_equal2; auto. rewrite Vnth_cast. apply Vnth_eq. trivial.
  Qed.

  Lemma Vmap2_Vcast : forall (A B C D E : Type)(n m : nat)(H : n=m)
    (f : A -> B -> E)(f' : C -> D -> E) (a : vector A n)
    (a' : vector C n)(b: vector B n)(b' : vector D n),
    Vmap2 f (Vcast a H) (Vcast b H) = 
      Vmap2 f' (Vcast a' H)(Vcast b' H) -> 
    Vmap2 f a b = Vmap2 f' a' b'.
  Proof.
    intros. subst. do 4 rewrite Vcast_refl in H0. apply H0.
  Qed. 

  Lemma rev_tail_last : forall (A : Type)(n : nat)(a : vector A (1+n)),
    Vtail (rev a) = rev (Vremove_last a).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_tail.
    do 2 rewrite Vbuild_nth. rewrite Vnth_remove_last. 
    apply Vnth_eq. lia. 
  Qed.
 
  Lemma rev_vmap2 : forall (A B C : Type)(f : A -> B -> C)
    (n : nat)(a : vector A n)(b : vector B n),
    rev (Vmap2 f a b) = Vmap2 f (rev a) (rev b).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth.
    do 2 rewrite Vnth_map2. do 2 rewrite Vbuild_nth. trivial.
  Qed.

  Lemma Vnth0 : forall (A : Type)(a : A),
    Vnth [a] (Nat.lt_0_succ 0) = a.
  Proof.
    intros. cbn. trivial.
  Qed.

  Lemma Vnth0_2 : forall (A : Type)(a : A)(n : nat)
      (h : 1 > n),
    Vnth [a] h = a.
  Proof.
    intros. assert (n = 0%nat). lia. subst. cbn. trivial.
  Qed.

  Lemma Vmap2_nil : forall (A B C : Type)
    (f : A -> B -> C)(v : vector A 0)(v' : vector B 0),
    Vmap2 f v v' = [].
  Proof.
    intros. cbn. trivial.
  Qed.

  Definition Zip (n : nat)(A B : Type)(a : vector A n)
    (b : vector B n) : vector (A*B) n :=
    Vmap2 (fun x y => (x,y)) a b.

  Definition UnzipLeft (n : nat)(A B : Type)
    (ab : vector (A*B) n) : 
    (vector A n) :=
    Vmap (fun x => x.1) ab.

  Definition UnzipRight (n : nat)(A B : Type)
    (ab : vector (A*B) n) : 
    (vector B n) :=
    Vmap (fun x => x.2) ab.

  Definition Unzip (n : nat)(A B : Type)
    (ab : vector (A*B) n) : 
    (vector A n)*(vector B n) :=
    (UnzipLeft ab, UnzipRight ab).

  Lemma UnzipLeftZip :
    forall (n : nat)(A B : Type)(a : vector A n)
    (b : vector B n),
    UnzipLeft (Zip a b) = a.
  Proof.
    intros. apply Veq_nth. intros. 
    rewrite Vnth_map. rewrite Vnth_map2.
    auto.
  Qed.

  Lemma UnzipRightZip :
    forall (n : nat)(A B : Type)(a : vector A n)
    (b : vector B n),
    UnzipRight (Zip a b) = b.
  Proof.
    intros. apply Veq_nth. intros. 
    rewrite Vnth_map. rewrite Vnth_map2.
    auto.
  Qed.
 
  Lemma UnzipZip :
    forall (n : nat)(A B : Type)(a : vector A n)
    (b : vector B n),
    Unzip (Zip a b) = (a,b).
  Proof.
    intros. unfold Unzip. 
    rewrite UnzipLeftZip. rewrite UnzipRightZip.
    trivial.
  Qed.

  Lemma Vnth_app_left : forall n1 (A : Type)(v1 : vector A n1) n2 
    (v2 : vector A n2) i (h : i < n1+n2)(p : n1 <= i), 
    Vnth (Vapp v1 v2) h = Vnth v2 (Vnth_app_aux n2 h p).
  Proof.
    intros. rewrite Vnth_app. destruct le_gt_dec.
    apply Vnth_eq. trivial. assert false.
    lia. congruence.
  Qed.

  Lemma Vapp_tail : forall n (A : Type)(v : vector A n) (a : A),
    Vtail (Vapp [a] v) = v.
  Proof.
    intros. cbn. trivial.
  Qed.

  Lemma Vbuild_0 : forall (A : Type)(gen : forall i, i < 0 -> A),
    Vbuild gen = Vnil.
  Proof.
    intros. cbn. trivial.
  Qed.

  Lemma Vnth_vbreak_1 : forall (n m : nat)(A : Type)(a : vector A (n+m)) 
      i (ip : i < n)(ip' : i < (n+m)),
    Vnth (Vbreak a).1 ip = Vnth a ip'.
  Proof.
    intros. rewrite (Vbreak_eq_app a). rewrite Vnth_app.
    destruct (le_gt_dec n i). assert false. lia. discriminate.
    rewrite Vbreak_app. simpl. apply Vnth_eq. trivial.
  Qed. 

  Lemma Vnth_vbreak_2 : forall (n m : nat)(A : Type)(a : vector A (n+m)) 
      i (ip : i < m)(ip' : (i + n) < (n+m)),
    Vnth (Vbreak a).2 ip = Vnth a ip'.
  Proof.
    intros. rewrite (Vbreak_eq_app a). rewrite Vnth_app.
    destruct (le_gt_dec n (i+n)). rewrite Vbreak_app. simpl.
    apply Vnth_eq. lia. assert false. lia. discriminate.
  Qed. 

  Lemma bVforall2Split : forall (n : nat)(A B : Type)(a : vector A n)
    (b : vector B n)(f f' : A -> B -> bool),
  bVforall2 (fun a' b' => f a' b' && f' a' b') a b ->
  bVforall2 (fun a' b' => f a' b') a b /\
    bVforall2 (fun a' b' => f' a' b') a b.
  Proof.
    intros. induction n. rewrite (Vector_0_is_nil a).
    rewrite (Vector_0_is_nil b). cbn. split; trivial.
    (* Induction case *)
    rewrite (VSn_eq a) in H. rewrite (VSn_eq b) in H.
    rewrite (VSn_eq a). rewrite (VSn_eq b). cbn in *. 
    apply andb_prop in H. destruct H. apply andb_prop in H. 
    destruct H. apply IHn in H0. destruct H0.
    split; apply andb_true_intro; split; auto. 
  Qed.

  Lemma Vtail_eqi : forall n (A : Type) a (v1 v2 : vector A n),
    Vcons a v1 = Vcons a v2 -> v1 = v2.
  Proof.
    intros. apply Vcons_eq in H. destruct H; auto.
  Qed.

  Lemma bVforall_elim_nth : forall n i 
    (ip : i < n)(A : Type)(v1 : vector A n) (R : A -> bool), 
   bVforall R v1 -> R (Vnth v1 ip).
  Proof.
    induction n; intros. absurd (i<0); omega.
    rewrite (VSn_eq v1) in H. cbn in H. apply andb_prop in H.
    destruct H. rewrite (Vhead_nth) in H. 
    destruct i; simpl; auto. assert (ip = (Nat.lt_0_succ n)).
    apply NatUtil.lt_unique. rewrite H1; auto.
    pose (IHn i (lt_S_n ip) A (Vtail v1) R H0).
    assert (Vnth (Vtail v1) (lt_S_n ip) = Vnth v1 ip). 
    rewrite Vnth_tail. apply Vnth_eq; auto. rewrite <- H1.
    apply i0.
  Qed.

  Lemma bVforall_elim_head : forall n (A : Type)(v1 : vector A (S n))
       (R : A -> bool), 
   bVforall R v1 -> R (Vhead v1).
  Proof.
    intros. assert (0 < S n). lia. apply (bVforall_elim_nth H0) in H.
    assert (Vnth v1 H0 = Vhead v1). rewrite Vhead_nth. apply Vnth_eq.
    trivial. rewrite <- H1. apply H.
  Qed.

  Lemma bVforall2_elim_nth : forall n i 
    (ip : i < n)(A B : Type)(v1 : vector A n) (v2 : vector B n) (R : A -> B -> bool), 
   bVforall2 R v1 v2 -> R (Vnth v1 ip) (Vnth v2 ip).
  Proof.
    induction n; intros. absurd (i<0); omega.
    rewrite (VSn_eq v1) in H. rewrite (VSn_eq v2) in H.
    cbn in H. apply andb_prop in H. destruct H.
    do 2 rewrite (Vhead_nth) in H. 
    destruct i; simpl; auto. assert (Vnth v1 (Nat.lt_0_succ n) = 
    Vnth v1 ip). apply Vnth_eq; auto. assert (Vnth v2 (Nat.lt_0_succ n) = 
    Vnth v2 ip). apply Vnth_eq; auto. rewrite <- H1. rewrite <- H2.
    auto. pose (IHn i (lt_S_n ip) A B (Vtail v1) (Vtail v2) R).
    assert (Vnth (Vtail v1) (lt_S_n ip) = Vnth v1 ip). 
    rewrite Vnth_tail. apply Vnth_eq; auto.
    assert (Vnth (Vtail v2) (lt_S_n ip) = Vnth v2 ip). 
    rewrite Vnth_tail. apply Vnth_eq; auto. rewrite <- H1.
    rewrite <- H2. apply i0; auto.
  Qed.

  Lemma bVforall2_elim_head : forall n (A B : Type)(v1 : vector A (S n))
     (v2 : vector B (S n)) (R : A -> B -> bool), 
   bVforall2 R v1 v2 -> R (Vhead v1) (Vhead v2).
  Proof.
    intros. assert (0 < S n). lia. apply (bVforall2_elim_nth H0) in H.
    assert (Vnth v1 H0 = Vhead v1). rewrite Vhead_nth. apply Vnth_eq.
    trivial. rewrite <- H1. assert (Vnth v2 H0 = Vhead v2). rewrite Vhead_nth. 
    apply Vnth_eq. trivial. rewrite <- H2.  apply H.
  Qed.

  Lemma bVforall2Clear : forall (n : nat)(A B : Type)(a : vector A (S n))
    (b : vector B (S n))(res : bool),
    bVforall2 (fun a' b' => res) a b ->
    res.
  Proof.
    intros. apply (bVforall2_elim_nth (lt_0_Sn n)) in H.
    apply H.
  Qed.

  Lemma bVforall_intro : forall n (A : Type)(v : vector A n)(R : A -> bool),
    (forall x, Vin x v -> R x) -> bVforall R v.
  Proof.
    induction v; simpl; intros; auto. apply Bool.andb_true_iff. split.
    apply H. left. trivial. apply IHv. intros. apply H. right. apply H0.
  Qed.

  Lemma bVforall_nth_intro : forall n (A : Type)(v : vector A n)
      (R : A -> bool),
    (forall i (ip : i < n), R (Vnth v ip)) -> bVforall R v.
  Proof.
    intros. apply bVforall_intro. intros.
    destruct (Vin_nth H0) as [i [ip v_i]].
    rewrite <- v_i. apply H.
  Qed.

  Lemma bVforall2_nth_intro : forall n (A B : Type)(v1 : vector A n)
      (v2 : vector B n)(R : A -> B -> bool),
    (forall i (ip : i < n), R (Vnth v1 ip) (Vnth v2 ip)) ->
       bVforall2 R v1 v2.
  Proof.
    unfold Vforall2. induction v1; intros. VOtac. simpl. auto.
    revert H. VSntac v2. intro. cbn. apply Bool.andb_true_iff. 
    split. apply (H0 0 (lt_O_Sn _)). unfold bVforall2 in IHv1.
    apply IHv1. intros. assert (S i< S n). omega.
    pose (H0 (S i) H1). simpl in i0. assert (ip = lt_S_n H1).
    apply NatUtil.lt_unique. rewrite H2. apply i0.
  Qed.

  Lemma bVforall_break_sub : forall n' n'' (A : Type)
    (v : vector A (n' + n''))(R : A -> bool),
    bVforall R v -> 
    let prod := Vbreak v in
    bVforall R prod.1 /\ bVforall R prod.2.
  Proof.
    intros. split.
    apply bVforall_nth_intro. intros. rewrite Vnth_vbreak_1. 
    intros. subst. apply (bVforall_elim_nth Hyp0) in H.
    apply H. lia. apply bVforall_nth_intro. intros. 
    rewrite Vnth_vbreak_2. intros. subst.
    apply (bVforall_elim_nth Hyp0) in H. apply H. lia. 
  Qed.

  Lemma bVforall_break : forall n n' n'' (A : Type)(v : vector A n)
      (R : A -> bool)(h : n = n' + n''),
    bVforall R v -> 
    let prod := Vbreak (Vcast v h) in
    bVforall R prod.1 /\ bVforall R prod.2.
  Proof.
    intros. assert (n' + n'' = n). omega. split.
    apply bVforall_nth_intro. intros. rewrite Vnth_vbreak_1. 
    intros. subst. apply (bVforall_elim_nth Hyp0) in H.
    apply H. lia. apply bVforall_nth_intro. intros. 
    rewrite Vnth_vbreak_2. intros. subst.
    apply (bVforall_elim_nth Hyp0) in H. apply H. lia. 
  Qed.

  Lemma bVforall2_break : forall n n' n'' (A B : Type)(v : vector A n)
      (v' : vector B n)(R : A -> B -> bool)(h : n = n' + n''),
    bVforall2 R v v' -> 
    let prodV  := Vbreak (Vcast v h) in
    let prodV' := Vbreak (Vcast v' h) in
    bVforall2 R prodV.1 prodV'.1 /\ 
      bVforall2 R prodV.2 prodV'.2.
  Proof.
    intros. assert (n' + n'' = n). omega. split.
    apply bVforall2_nth_intro. intros. rewrite Vnth_vbreak_1.
    intros. rewrite (Vnth_vbreak_1 n'' (Vcast v' h) ip Hyp0).
    subst. apply (bVforall2_elim_nth Hyp0) in H.
    apply H. lia. apply bVforall2_nth_intro. intros. 
    rewrite Vnth_vbreak_2. intros.  rewrite (Vnth_vbreak_2 n'
    (Vcast v' h) ip Hyp0). subst.
    apply (bVforall2_elim_nth Hyp0) in H. apply H. lia. 
  Qed.

  Lemma bVforall_follows : forall n (A : Type)
    (f f' : A -> bool)(v : vector A n),
    (forall a, f a -> f' a) ->
    bVforall f  v ->
    bVforall f' v.
  Proof.
    intros. induction v. cbn. trivial.
    cbn in *. apply Bool.andb_true_iff. 
    apply Bool.andb_true_iff in H0. destruct H0.
    apply IHv in H1. apply H in H0. split; auto.  
  Qed.

  Lemma casting_double_induct : forall j,
   Nat.add (S j) (S j) = S (S (Nat.add j j)).
  Proof.
    intros. lia.
  Qed.

  Definition double_induct (A : Type)(j : nat)
    (v : vector A ((S j)+(S j))) : vector A (j+j) :=
  Vremove_last (Vtail (Vcast v (casting_double_induct j))).

  Lemma Vhead_cast : forall (A : Type)(i j : nat)
    (v : vector A (S i))(H : S i = S j),
  Vhead (Vcast v H) = Vhead v.
  Proof.
    intros. do 2 rewrite Vhead_nth. rewrite Vnth_cast.
    apply Vnth_eq. trivial. 
  Qed.

  Lemma Vmap2_double_induct : forall (A B C : Type)(j : nat)
      (f : A -> B -> C)(v : vector A (S j + S j))
      (v' : vector B (S j + S j)),
    double_induct (Vmap2 f v v') = Vmap2 f (double_induct v)
    (double_induct v').
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2.
    assert (i < S (j+j)). lia. unfold double_induct. 
    do 3 rewrite Vnth_remove_last. do 3 rewrite Vnth_tail.
    do 3 rewrite Vnth_cast. rewrite Vnth_map2. trivial.
  Qed.

  Lemma Vhead_map : forall (A B : Type)(j : nat)(f : A -> B)
    (v : vector A (S j)), Vhead (Vmap f v) = f (Vhead v).
  Proof.
    intros. do 2 rewrite Vhead_nth. rewrite Vnth_map. trivial.
  Qed.

  Lemma Vhead_map2 : forall (A B C : Type)(j : nat)(f : A -> B -> C)
    (v : vector A (S j))(v' : vector B (S j)), 
      Vhead (Vmap2 f v v') = f (Vhead v)(Vhead v').
  Proof.
    intros. do 3 rewrite Vhead_nth. rewrite Vnth_map2. trivial.
  Qed.

  (* Takes a vector and a predicate and checks that it 
  holds for combinations without replacment *)
  Fixpoint PairwisePredicate (A : Type)(n : nat)(f : A -> A -> bool)
      (v : vector A n) : bool :=
    match v with
      | Vnil => true
      | Vcons a w => bVforall (f a) w && PairwisePredicate f w
    end.

  Lemma PairwisePredicateEq : forall (A : Type)(n n' : nat)
    (f : A -> A -> bool)
    (v : vector A n)(v' : vector A n')(h : n' = n),
    v = Vcast v' h ->
    PairwisePredicate f v = PairwisePredicate f v'.
  Proof.
    intros. subst. simpl. trivial.
  Qed.

  Lemma PairwiseInd : forall (A : Type)(n : nat)(f : A -> A -> bool)
    (v : vector A (S n)),
    PairwisePredicate f v ->
    bVforall (f (Vhead v)) (Vtail v) && PairwisePredicate f (Vtail v).
  Proof.
    intros. rewrite (VSn_eq v) in H. simpl in H. apply H.
  Qed.
  

  Lemma PairwisePredicate_break : forall n n' n'' (A : Type)
      (v : vector A n)
      (f : A -> A -> bool)(h : n = n' + n''),
    PairwisePredicate f v -> 
    let prod := Vbreak (Vcast v h) in
    PairwisePredicate f prod.1.
  Proof.
    intros. subst. simpl. induction n'. cbn. trivial.
    intros. simpl. apply andb_true_iff. assert (S n' + n'' = S (n' + n'')).
    lia. assert (S (n' + n'') = S n' + n''). lia. 
    assert (v = Vcast (Vcast v H0) H1). apply Veq_nth. intros.
    do 2 rewrite Vnth_cast. apply Vnth_eq. trivial.
    rewrite (PairwisePredicateEq f (Vcast v H0) H1 H2) in H.
    apply PairwiseInd in H. apply andb_true_iff in H. destruct H.
    assert (Vtail v = (Vtail (Vcast v H0))). apply Veq_nth. intros. 
    do 2 rewrite Vnth_tail. rewrite Vnth_cast. apply Vnth_eq. trivial.
    rewrite H4. split. rewrite Vhead_cast in H. 
    apply (bVforall_break_sub n' n'') in H. apply H. apply IHn'.
    apply H3. 
  Qed.

  (* No idea why f_equal2 is falling *)
  Lemma Vtail_equal : forall (A : Type)(a a' : A)(i : nat),
    a = a'-> 
    Vconst a i = Vconst a' i.
  Proof.
    intros. subst. trivial.
  Qed.

  Lemma Vtail_const : forall n (A : Type)(a : A),
    Vtail (Vconst a (S n)) = Vconst a n.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_tail. trivial.
  Qed.

  Lemma bVforall_false : forall n (A B : Type)(v : vector A n)
      (v' : vector B n)(R : A -> B -> bool),
    bVforall2 R v v' = false ->
    exists i (ip : i <n), R (Vnth v ip) (Vnth v' ip) = false.
  Proof.
    intros. induction n. rewrite (Vector_0_is_nil v) in H.
    rewrite (Vector_0_is_nil v') in H. cbn in H. discriminate.
    rewrite (VSn_eq v) in H. rewrite (VSn_eq v') in H.
    cbn in H. apply andb_false_iff in H. destruct H. exists 0.
    exists (Nat.lt_0_succ n). do 2 rewrite Vhead_nth in H.
    apply H.  apply IHn in H. destruct H. destruct H.
    exists (S x). exists (lt_n_S x0). rewrite <- H.
    do 2 rewrite Vnth_tail. trivial. 
  Qed.

  Lemma Vfold_add : forall (n : nat)(A : Type) 
    (f : A->A->A)(v : vector A n)(a b : A),
    (forall a0 b c : A, f (f a0 b) c = f a0 (f b c)) ->
    (forall a b, f a b = f b a) -> 
    Vfold_left f a (Vadd v b) = f (Vfold_left f a v) b.
  Proof.
    intros. induction n. rewrite (Vector_0_is_nil v).
    cbn. trivial. symmetry. rewrite Vfold_left_induction; auto.
    rewrite H. rewrite <- IHn. rewrite <- Vfold_left_Vcons; auto. 
    rewrite Vadd_cons. trivial.
  Qed.

  
  Lemma Vfold_left_eq_rev : forall (n : nat)(A : Type) 
    (f : A->A->A)(v : vector A n)(a : A),
    (forall a0 b c : A, f (f a0 b) c = f a0 (f b c)) ->
    (forall a b, f a b = f b a) -> 
    Vfold_left f a v = Vfold_left f a (rev v).
  Proof.
    intros. induction n. rewrite (Vector_0_is_nil v).
    cbn. trivial. rewrite Vfold_left_induction; auto.
    rewrite IHn. rewrite (VSn_eq v). rewrite rev_Vcons.
    simpl. rewrite Vfold_add; auto.
  Qed.

  Lemma Vapp_Vtail : forall n n' A (v : vector A (S n))(v' : vector A n'),
    Vapp (Vtail v) v' = Vtail (Vapp v v').
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_tail.
    assert (S i < S n + n'). lia. assert (Vnth (Vapp v v') (lt_n_S ip) =
    Vnth (Vapp v v') H). apply Vnth_eq. trivial. rewrite H0. do 2 rewrite Vnth_app.
    destruct (le_gt_dec n i). destruct (le_gt_dec (S n) (S i)). apply Vnth_eq.
    lia. assert False. lia. contradiction. destruct (le_gt_dec (S n) (S i)).
    assert False. lia. contradiction. rewrite Vnth_tail. apply Vnth_eq. trivial.
  Qed.

  Lemma Vapp_eq_intro_cast : forall n1 A (v1 v1' : vector A n1) n2 n2'
    (v2 v2' : vector A n2)(h : n2 = n2')(h' : n1+n2 = n1+n2'),
     v1 = v1' -> v2 = v2' -> Vcast (Vapp v1 v2) h'  = Vapp v1' (Vcast v2' h).
  Proof.
    intros. subst. cbn. rewrite Vcast_refl. trivial.
  Qed.

  (* Coq is being mean again *)
  Lemma Vapp_eq_intro_cast_hack : forall n1 A (v1 v1' : vector A n1) n2 n2'
    (v2 : vector A (S n2))(v2' : vector A (S n2))(a : A)
    (h : (S n2) = n2')(h' : n1+(S n2) = n1+n2'),
     v1 = v1' -> v2 = (Vcons a (Vtail v2')) -> 
  Vcast (Vapp v1 v2) h' = Vapp v1' (Vcast (Vcons a (Vtail v2')) h).
  Proof.
    intros. subst. cbn. rewrite Vcast_refl. trivial.
  Qed.
 
  Lemma Vapp_eq_cast : forall n1 A (v1 : vector A n1) n2 n2'
    (v2 : vector A n2)(h : n2 = n2')(h' : n1+n2 = n1+n2'),
    Vcast (Vapp v1 v2) h'  = Vapp v1 (Vcast v2 h).
  Proof.
    intros. subst. cbn. rewrite Vcast_refl. trivial.
  Qed.

  Lemma injective_projections_simp : forall A B (a b : A)(c d : B),
    a = b -> c = d -> (a,c) = (b,d).
  Proof.
    intros. rewrite H. rewrite H0. trivial.
  Qed.

  Lemma Prod_left : forall A B (a b : A) (c d : B),
    a = b -> (a,c).1 = (b,d).1.
  Proof.
    intros. simpl. auto.
  Qed.

  Lemma Prod_right : forall A B (a b : A) (c d : B),
    c = d -> (a,c).2 = (b,d).2.
  Proof.
    intros. simpl. auto.
  Qed.

  Lemma Prod_left_replace : forall A B (a : A) (b : B),
    (a,b).1 = a.
  Proof.
    intros. simpl. auto.
  Qed.

  Lemma Prod_right_replace : forall A B (a : A) (b : B),
    (a,b).2 = b.
  Proof.
    intros. simpl. auto.
  Qed.

  Lemma Vhead_app : forall n m A 
      (a : vector A (S n))(b : vector A m),
    Vhead (Vapp a b) = Vhead a.
  Proof.
    intros. assert (0 < (S n) + m). lia. assert (Vhead (Vapp a b) =
    Vnth (Vapp a b) H). rewrite Vhead_nth. apply Vnth_eq. lia.
    rewrite H0. rewrite Vnth_app. destruct (le_gt_dec (S n) 0).
    assert (False). lia. contradiction. rewrite Vhead_nth.
    apply Vnth_eq. trivial.
  Qed.

  Lemma Vhead_const : forall n A (a : A),
    Vhead (Vconst a (S n)) = a.
  Proof.
    intros. rewrite Vhead_nth. rewrite Vnth_const. trivial.
  Qed.

  Lemma Vapp_vcons : forall n A (a : A)(b : vector A n), 
    Vapp [a] b = Vcons a b.
  Proof.
    intros. cbn. trivial.
  Qed.

  Lemma Vfold_left_map2 : forall (A : Type)(f : A -> A -> A)
    (n : nat)(v v' : vector A n)(acc : A),
    (forall a b c, f (f a b) c = f a (f b c)) ->
    (forall a b, f a b = f b a) ->      
    (forall a, f acc a = a) ->
    Vfold_left f acc (Vmap2 f v v') = f (Vfold_left f acc v) (Vfold_left f acc v').
  Proof.
    intros. induction n. rewrite (Vector_0_is_nil v). rewrite (Vector_0_is_nil v').
    cbn. rewrite H1. trivial.
    rewrite Vfold_left_induction; auto. rewrite IHn. rewrite Vhead_map2.
    assert (forall a b c d, f (f a b) (f c d) = f (f a c) (f b d)).
    intros. do 2 rewrite H. apply f_equal2; auto. do 2 rewrite <- H. 
    apply f_equal2; auto. rewrite H2. rewrite <- Vfold_left_induction; auto. 
    rewrite <- Vfold_left_induction; auto.
  Qed. 

  Lemma Vfold_left_vapp : forall (A : Type)(f : A -> A -> A)
    (n n' : nat)(v : vector A n)(v' : vector A n')(acc : A),
    (forall a b c, f (f a b) c = f a (f b c)) ->
    (forall a b, f a b = f b a) ->      
    (forall a, f acc a = a) ->
    Vfold_left f acc (Vapp v v') = f (Vfold_left f acc v) (Vfold_left f acc v').
  Proof.
    intros. induction n. rewrite (Vector_0_is_nil v). cbn; auto.
    rewrite Vfold_left_induction; auto. rewrite H. rewrite <- IHn.
    rewrite <- Vfold_left_Vcons; auto. rewrite <- Vapp_cons. rewrite <- VSn_eq.
    trivial.
  Qed. 

  Lemma Vhead_rev : forall (A : Type)(n n' : nat)(v : vector (vector A n) (S n')),
    rev (Vhead v) = Vhead (Vmap (fun x => rev x) v).
  Proof.
    intros. rewrite Vhead_map. trivial.
  Qed.

End VectorUtil.
