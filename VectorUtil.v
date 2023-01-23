Require Coq.Program.Tactics.
From CoLoR Require Import RelDec OrdSemiRing LogicUtil RelExtras EqUtil NatUtil ZUtil SemiRing.
Require Import Coq.Vectors.Vector.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import CoLoR.Util.Vector.VecArith.
Require Import ssreflect ssrfun ssrbool.
Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FinFun.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Lists.List.

Notation " [ ] " := Vnil.
Notation " [ x ] " := (Vcons x Vnil).
Notation " [ x ; .. ; y ] " := (Vcons x .. (Vcons y Vnil) ..).
Set Implicit Arguments.

Section VectorUtil.

  Definition VlastS A n (a : vector A (S n)) := Vlast (Vhead a) a.

  Lemma VlastS_tail : forall A n (b : vector A (S (S n))),
    VlastS (Vtail b) = VlastS b.
  Proof.
    intros. unfold VlastS. do 2 rewrite Vlast_nth. rewrite Vnth_tail.
    apply Vnth_eq. lia.
  Qed.

  Lemma VlastS_add : forall  A n a (b : vector A n),
    VlastS (Vadd b a) = a.
  Proof.
    intros. unfold VlastS. rewrite Vlast_nth. rewrite Vnth_add.
    destruct (Nat.eq_dec n n). trivial. lia.
  Qed.

  Lemma VlastS_cons : forall  A n a (b : vector A (S n)),
    VlastS (Vcons a b) = VlastS b.
  Proof.
    intros. unfold VlastS. do 2 rewrite Vlast_nth. rewrite Vnth_cons.
    destruct (lt_ge_dec 0 (S n)). apply Vnth_eq. lia. lia.
  Qed.
  
  Lemma VlastS_nth : forall n (ip : n < S n) A (b : vector A (S n)),
    VlastS b = Vnth b ip.
  Proof.
    intros. unfold VlastS. rewrite Vlast_nth. trivial.
  Qed.

  Lemma VlastS_intro : forall A n (a b : vector A (S n)),
    a = b -> VlastS a = VlastS b.
  Proof.
    intros. rewrite H. trivial. 
  Qed.

  Lemma VlastS_Vhead : forall A (a : vector A 1),
    Vhead a = VlastS a.
  Proof.
    intros. rewrite Vhead_nth. rewrite VlastS_nth. apply Vnth_eq. trivial.
  Qed.

  Lemma VlastS_build : forall n A (gen : (forall i, i< S n -> A)),
    VlastS (Vbuild (fun i ip => gen i ip)) = gen n (le_n (S n)).
  Proof.
    intros. rewrite VlastS_nth. rewrite Vbuild_nth. apply f_equal.
    apply le_unique. 
  Qed. 

  Lemma Vhead_Vremove_last : forall (A : Type)(n : nat)(a : vector A (S (S n))),
    Vhead (Vremove_last a) = Vhead a.
  Proof.
    intros. do 2 rewrite Vhead_nth. rewrite Vnth_remove_last. apply Vnth_eq.
    trivial.
  Qed.

  Lemma Vremove_last_cons : forall (A : Type)(n : nat) b (a : vector A (S n)),
    Vremove_last (Vcons b a) = Vcons b (Vremove_last a).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_remove_last.
    do 2 rewrite Vnth_cons. destruct (lt_ge_dec 0 i). rewrite Vnth_remove_last.
    apply Vnth_eq. trivial. trivial.
  Qed.

  Lemma VlastS_remove_last_2 : forall (A : Type)(a : vector A 2),
    VlastS (Vremove_last a) = Vhead a.
  Proof.
    intros. rewrite VlastS_nth. rewrite Vnth_remove_last. rewrite Vhead_nth.
    apply Vnth_eq. trivial.
  Qed.

  Lemma Vhead_Vadd : forall (A : Type)(n : nat)(a : vector A (S n)) b,
    Vhead (Vadd a b) = Vhead a.
  Proof.
    intros. rewrite Vhead_nth. rewrite Vnth_add. destruct (Nat.eq_dec 0 (S n)).
    lia. rewrite Vhead_nth. apply Vnth_eq. trivial.
  Qed.

   Lemma Vtail_Vadd : forall (A : Type)(n : nat)(a : vector A (S n)) b,
    Vtail (Vadd a b) = Vadd (Vtail a) b.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_tail. do 2 rewrite Vnth_add.
    destruct (Nat.eq_dec (S i) (S n)). destruct (Nat.eq_dec i n). trivial.
    lia. destruct (Nat.eq_dec i n). lia. rewrite Vnth_tail. apply Vnth_eq.
    lia.
  Qed.

  Lemma VSn_addS : forall A n (v : vector A (S n)),
    v = Vadd (Vremove_last v) (VlastS v).
  Proof.
    intros. apply VSn_add.
  Qed.

  Lemma Vmap2_remove_last : forall A B C n (v : vector A (S n))
    (v' : vector B (S n))(f : A -> B -> C),
    Vremove_last (Vmap2 f v v') = Vmap2 f (Vremove_last v) (Vremove_last v').
  Proof.
    intros. apply Veq_nth; intros. rewrite Vnth_remove_last. do 2 rewrite Vnth_map2.
    do 2 rewrite Vnth_remove_last. trivial.
  Qed.

  Lemma Vmap_remove_last : forall A B n (v : vector A (S n))(f : A -> B),
    Vremove_last (Vmap f v) = Vmap f (Vremove_last v).
  Proof.
    intros. apply Veq_nth; intros. rewrite Vnth_remove_last. do 2 rewrite Vnth_map.
    rewrite Vnth_remove_last. trivial.
  Qed.

  Lemma VlastS_map : forall A B n (v : vector A (S n))(f : A -> B),
    VlastS (Vmap f v) = f (VlastS v).
  Proof.
    intros. do 2 rewrite VlastS_nth. rewrite Vnth_map. trivial.
  Qed.

  Lemma VlastS_map2 : forall A B C n (v : vector A (S n))
      (v' : vector B (S n))(f : A -> B -> C),
    VlastS (Vmap2 f v v') = f (VlastS v)(VlastS v').
  Proof.
    intros. do 3 rewrite VlastS_nth. rewrite Vnth_map2. trivial.
  Qed.

  Lemma VlastS_Vhead_Vtail : forall A (v : vector A 2),
    Vhead (Vtail v) = VlastS v.
  Proof.
    intros. rewrite Vhead_nth. rewrite VlastS_nth. rewrite Vnth_tail. 
    apply Vnth_eq. trivial.
  Qed.

  Lemma Vhead_cons : forall (A : Type)(n : nat)(a : A)(b : vector A n),
    Vhead (Vcons a b) = a.
  Proof.
    intros. auto.
  Qed.

  Lemma Vhead_eq : forall (A : Type)(n : nat)(a b : vector A (S n)),
    a = b -> Vhead a = Vhead b.
  Proof.
    intros. rewrite H. trivial. 
  Qed.

  Lemma Veq_tail: forall (A : Type)(n : nat)(a b : vector A (S n)),
    a = b -> Vtail a = Vtail b.
  Proof.
    intros. rewrite H. trivial. 
  Qed.

  Lemma Vtail_cons : forall (A : Type)(n : nat)(a : A)(b : vector A n),
    Vtail (Vcons a b) = b.
  Proof.
    intros. auto.
  Qed.

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

  Lemma Vfold_left_eq3 : forall (n : nat)(A B : Type) (f f' : A->B->A)
    (v v' : vector B n)(a a' : A),
    f = f' -> v = v' -> a = a' -> Vfold_left f a v = Vfold_left f' a' v'.
  Proof.
    intros. subst. trivial.
  Qed.

  Lemma Vcons_map2 : forall (A B C : Type) (f: A->B->C) (n :nat)
          (v : vector A n) (v' : vector B n)(a : A)(b : B),
      Vmap2 f (Vcons a v) (Vcons b v') = Vcons (f a b) (Vmap2 f v v').
  Proof. 
    intros. refl. 
  Qed.

  Lemma Vmap2_tail : forall (A B C : Type) (f: A->B->C) (n :nat)
          (v : vector A (S n)) (v' : vector B (S n)),
    Vmap2 f (Vtail v)  (Vtail v') = Vtail (Vmap2 f v v').
  Proof.
   intros. apply Veq_nth. intros. rewrite Vnth_tail. rewrite Vnth_map2.
   trivial.
  Qed.

  Lemma Vadd_map : forall (A B : Type) (f: A->B) (n :nat)
          (v : vector A n)(a : A),
      Vmap f (Vadd v a)= Vadd (Vmap f v) (f a).
  Proof. 
    intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_add. 
    destruct (Nat.eq_dec i n). trivial. rewrite Vnth_map. trivial.
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

  Lemma Vapp_map : forall (A B : Type) (f: A->B) (n n' :nat)
          (v : vector A n)(u : vector A n'),
    Vmap f (Vapp v u) = Vapp (Vmap f v) (Vmap f u).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_app.
    destruct (le_gt_dec n i). rewrite Vnth_map. trivial.
    rewrite Vnth_map. trivial.
  Qed.

  Lemma Vcons_map : forall (A B : Type) (f: A->B) (n :nat)
          (v : vector A n)(a : A),
      Vmap f (Vcons a v) = Vcons (f a) (Vmap f v).
  Proof. 
    intros. refl. 
  Qed.

  Lemma Vbuild_Vnth_Vbuild : forall n A (gen : (forall i, i<n -> A)),
    Vbuild (fun i ip => Vnth (Vbuild (fun j jp => gen j jp)) ip) = 
    Vbuild (fun i ip => gen i ip).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth. trivial.
  Qed.
  
 Definition Vector_0_is_nil (A : Type)(v : Vector.t A 0) : v = Vector.nil :=
  match v with Vector.nil => eq_refl end.

  Lemma Vfold_left_nil : forall (A B : Type) (f : A->B->A)
      (v : vector B 0)(a : A),
      Vfold_left f a v = a.
  Proof.
    intros. rewrite (Vector_0_is_nil v). cbn. trivial.
  Qed.

  Lemma Vfold_left_nil_gen : forall n (A B : Type) (f : A->B->A)
      (v : vector B n)(a : A),
      n = 0 ->
      Vfold_left f a v = a.
  Proof.
    intros. subst. apply Vfold_left_nil. 
  Qed.

  Lemma Vfold_left_head : forall (A : Type) (f : A->A->A)(v : vector A 1)(a : A),
    (forall b, f a b = b) ->
    Vfold_left f a v = Vhead v.
  Proof.
    intros. cbn. rewrite (VSn_eq v). rewrite (Vector_0_is_nil (Vtail v)). cbn.
    rewrite H. trivial.
  Qed. 

  Lemma Vfold_left_head_gen : forall (A : Type) n (f : A->A->A)(v : vector A (S n))(a : A),
    n = 0 ->
    (forall b, f a b = b) ->
    Vfold_left f a v = Vhead v.
  Proof.
    intros. subst. apply Vfold_left_head. apply H0.
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

  Lemma Veq_nth_mat : forall n n' (H : n = n')(A B : Type)(v : vector A n)(v' : vector A n')
                             (f : forall a, vector A a -> vector (vector B a) a) i j i' j'
                             (ip : i < n)(jp : j < n)(ip' : i' < n')(jp' : j' < n'),
      i = i' -> j = j' -> Vcast v H = v' -> Vnth (Vnth (f n v) ip) jp = Vnth (Vnth (f n' v') ip') jp'.
  Proof.
    intros. subst. apply Veq_nth3. trivial. rewrite Vcast_refl. apply Vnth_eq. trivial.
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

  Lemma rev_Vadd : forall (A : Type)(n : nat)(a : A)(b : vector A n),
    rev (Vcons a (rev b)) = Vadd b a.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth. rewrite Vnth_cons.
    rewrite Vnth_add. destruct (lt_ge_dec 0 (S n - i - 1)). intros.
    destruct (Nat.eq_dec i n). assert False. lia. contradiction.
    rewrite Vbuild_nth. apply Vnth_eq. lia. destruct (Nat.eq_dec i n).
    trivial. assert False. lia. contradiction.
  Qed.

  Lemma rev_one : forall (A : Type)(a : vector A 1),
    rev a = a.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth. apply Vnth_eq. lia.
  Defined.
  
  Lemma rev_zero : forall (A : Type)(a : vector A 0),
    rev a = [].
  Proof.
    intros. cbn. trivial.
  Qed. 

  Lemma rev_Vhead : forall n (A : Type)(a : vector A (S n)),
    Vhead (rev a) = VlastS a.
  Proof.
    intros. rewrite Vbuild_head. rewrite VlastS_nth. apply Vnth_eq. lia.  
  Qed.

 Lemma Vnth0Head : forall n (A : Type)(v : vector A (S n))(ip: 0 < S n),
    Vhead v = Vnth v ip.
  Proof.  
    intros. rewrite Vhead_nth. apply Vnth_eq. trivial.
  Defined.

  Lemma Vcons_rev : forall (A : Type)(n : nat)(a : A)(b : vector A n),
    Vcons a (rev b) = rev (Vadd b a).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth.
    rewrite Vnth_add. case (Nat.eq_dec (S n - i - 1) n). intros.
    rewrite Vnth_cons_head.  lia. trivial.
    intros. rewrite Vnth_cons_tail. intros. rewrite Vbuild_nth.
    apply Vnth_eq. lia. lia.
  Qed.

  Lemma rev_Vtail : forall (A : Type)(n : nat)(a : vector A (S n)),
    rev (Vtail a) = Vremove_last (rev a).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_remove_last. 
  do 2 rewrite Vbuild_nth. rewrite Vnth_tail. apply Vnth_eq. lia.
  Qed.

  Lemma gen_equal : forall (A : Type)(n : nat)(gen : forall i, i < n -> A) i i' ip ip',
    i = i' ->
    gen i ip = gen i' ip'.
  Proof.
    intros. subst. apply f_equal. apply le_unique. 
  Qed.

  Lemma rev_Vtail_build : forall (A : Type)(n : nat)(gen : forall i, i < S n -> A),
      Vtail (rev (Vbuild (fun i ip => gen i ip))) = 
      rev (Vbuild (fun i (ip : i < n) => gen i (le_S ip))).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_tail. do 4 rewrite Vbuild_nth. 
    apply gen_equal. lia.
  Qed.

  Lemma Vremove_last_Vtail : forall (A : Type)(n : nat)(v : vector A (S (S n))),
    Vremove_last (Vtail v) = Vtail (Vremove_last v).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_remove_last. do 2 rewrite Vnth_tail.
    rewrite Vnth_remove_last. apply Vnth_eq. trivial.
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

  Lemma UnzipLeftMap : forall (n : nat)(A B C : Type)(a : vector A n)
    (f : A -> B)(f' : A -> C),
    UnzipLeft (Vmap (fun a => (f a, f' a)) a) = Vmap f a.
  Proof.
    intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. trivial.
  Qed.

  Lemma UnzipRightMap : forall (n : nat)(A B C : Type)(a : vector A n)
    (f : A -> B)(f' : A -> C),
    UnzipRight (Vmap (fun a => (f a, f' a)) a) = Vmap f' a.
  Proof.
    intros. apply Veq_nth. intros. do 3 rewrite Vnth_map. trivial.
  Qed.

  Lemma UnzipLeftbVforall : forall (n : nat)(A B  : Type)(a : vector (A*B) n)
    (f : A -> bool),
    bVforall (fun a => f a.1) a = bVforall f (UnzipLeft a).
  Proof.
    intros. induction a. cbn. trivial.
    simpl. rewrite IHa. trivial.
  Qed.

  Lemma UnzipRightbVforall : forall (n : nat)(A B : Type)(a : vector (A*B) n)
    (f : B -> bool),
    bVforall (fun a => f a.2) a = bVforall f (UnzipRight a).
  Proof.
    intros. induction a. cbn. trivial.
    simpl. rewrite IHa. trivial.
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

  Lemma Vbuild_1 : forall (A : Type)(gen : forall i, i < 1 -> A),
    Vbuild gen = [gen 0 (lt_O_Sn 0)].
  Proof.
    intros. apply Veq_nth. intros. assert (i = 0). lia. subst. simpl. trivial.
  Qed.

  Lemma lessIsLess2 : forall j i N,
    j < S i -> i < N ->
    j < N.
  Proof.
    intros. lia.
  Qed.

  Lemma le_sub : forall i n (ip : i <= n),
      0+i <= n.
  Proof.
      intros. lia.
  Qed.

  Lemma le_sub2 : forall i n (ip : i <= n),
      (n-i)+i <= n.
  Proof.
      intros. lia.
  Qed.

  Lemma le_sub_eq : forall A n (ip : n <= n)(a : vector A n),
    Vsub a (le_sub ip) = a.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_sub. apply Vnth_eq. lia. 
  Qed.

  Lemma le_sub_eq_gen : forall A n n' (ip : n <= n')(a : vector A n')(ip' : n' = n),
    Vsub a (le_sub ip) = Vcast a ip'.
  Proof.
    intros. subst. apply le_sub_eq.
  Qed.

  Lemma le_sub_eq_last : forall A n (ip : n <= S n)(a : vector A (S n)),
    Vadd (Vsub a (le_sub ip)) (VlastS a) = a.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_add. destruct (Nat.eq_dec i n).
    rewrite VlastS_nth. apply Vnth_eq. trivial. rewrite e. trivial.
    rewrite Vnth_sub. apply Vnth_eq. lia.
  Qed.
    
  Lemma le_sub2_eq : forall A n (ip : n <= n)(a : vector A n),
    Vsub a (le_sub2 ip) = a.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_sub. apply Vnth_eq. lia. 
  Qed.

  Lemma Vsub_le_sub2_l : forall A n (a : vector A (S n))(ip : 1 <= S n),
    Vhead (Vsub a (le_sub2 ip)) = VlastS a.
  Proof.
    intros. rewrite Vhead_nth. rewrite VlastS_nth. rewrite Vnth_sub.
    apply Vnth_eq. lia. 
  Qed.

  Lemma Vsub_rev : forall (A : Type)(n : nat)(b : vector A n) i (ip : i < n),
    rev (Vsub b (le_sub ip)) = Vsub (rev b) (le_sub2 ip).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_sub. do 2 rewrite Vbuild_nth.
    rewrite Vnth_sub. apply Vnth_eq. lia.
  Qed.

  Lemma Vbuild_sub : forall A n (gen : forall i, i < n -> A) i (ip : i < n),
    (forall i ip ip', gen i ip = gen i ip') -> 
    Vsub (Vbuild (fun i0 ip0 => gen i0 ip0)) (le_sub ip) =
          Vbuild (fun i0 (ip0 : i0 < S i) => gen i0 (lessIsLess2 ip0 ip)).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_sub. do 2 rewrite Vbuild_nth.
    apply gen_equal.  lia.
  Qed. 

  Lemma Vremove_last_sub : forall A n (v : vector A n) i (ip : S i < n),
    Vremove_last (Vsub v (le_sub ip)) = Vsub v (le_sub (le_Sn_le (S i) n ip)).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_remove_last. do 2 rewrite Vnth_sub.
    apply Vnth_eq. trivial.
  Qed.

  Lemma Vhead_tail_sub : forall A n (v : vector A (S (S n))) i (ip : S (S i) <= S (S n)),
    Vhead (Vtail (Vsub v (le_sub ip))) = Vhead (Vtail v).
  Proof.
    intros. do 2 rewrite Vhead_nth. do 2 rewrite Vnth_tail. 
    rewrite Vnth_sub. apply Vnth_eq. trivial.  
  Qed. 

  Lemma Vtail_sub : forall A n (v : vector A n) i (ip : S i < n),
    Vtail (Vsub v (le_sub2 ip)) = Vsub v (le_sub2 (le_Sn_le (S i) n ip)).
  Proof.
    intros.  apply Veq_nth. intros. rewrite Vnth_tail. do 2 rewrite Vnth_sub.
    apply Vnth_eq. lia.
  Qed. 

  Lemma Less_neq : forall i n,
    i <= S n ->
    i <> S n ->
    i <= n.
  Proof.
    intros. lia.
  Qed.

  Lemma Vsub_cons2s : forall A n a (b : vector A n) i (ip : S i <= S n)
        (x : S i <> S n),
    Vsub (Vcons a b) (le_sub2 ip) = Vsub b (le_sub2 (Less_neq ip x)).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_sub. rewrite Vnth_cons.
    destruct (lt_ge_dec 0 (S n - S i + i0)). rewrite Vnth_sub. apply Vnth_eq.
    lia. lia.
  Qed.

  Lemma Vremove_last_sub_build  : forall A n (gen : forall i, i < n -> A) 
          i (ip : S i < n),
      Vremove_last (Vsub (Vbuild (fun i0 ip0 => gen i0 ip0)) (le_sub ip)) = 
      Vsub (Vbuild (fun i0 ip0 => gen i0 ip0)) (le_sub (le_Sn_le (S i) n ip)).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_remove_last. do 2 rewrite Vnth_sub.
    do 2 rewrite Vbuild_nth. apply gen_equal. lia.
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

  Lemma Vnth_tail_lt_S_n : forall n A (v: vector A (S n)) i (ip : S i < S n),
    Vnth (Vtail v) (lt_S_n ip) = Vnth v ip.
  Proof.
    intros. rewrite Vnth_tail. apply Vnth_eq. trivial.
  Qed.

  Lemma bVforall_elim_nth : forall n i 
    (ip : i < n)(A : Type)(v1 : vector A n) (R : A -> bool), 
   bVforall R v1 -> R (Vnth v1 ip).
  Proof.
    induction n; intros. absurd (i<0); lia.
    rewrite (VSn_eq v1) in H. cbn in H. apply andb_prop in H.
    destruct H. rewrite (Vhead_nth) in H. 
    destruct i; simpl; auto. assert (ip = (Nat.lt_0_succ n)).
    apply NatUtil.lt_unique. rewrite H1; auto.
    pose (IHn i (lt_S_n ip) A (Vtail v1) R H0). rewrite <- Vnth_tail_lt_S_n.
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
    induction n; intros. absurd (i<0); lia.
    rewrite (VSn_eq v1) in H. rewrite (VSn_eq v2) in H.
    cbn in H. apply andb_prop in H. destruct H.
    do 2 rewrite (Vhead_nth) in H. 
    destruct i; simpl; auto. assert (Vnth v1 (Nat.lt_0_succ n) = 
    Vnth v1 ip). apply Vnth_eq; auto. assert (Vnth v2 (Nat.lt_0_succ n) = 
    Vnth v2 ip). apply Vnth_eq; auto. rewrite <- H1. rewrite <- H2.
    auto. pose (IHn i (lt_S_n ip) A B (Vtail v1) (Vtail v2) R).
    do 2 rewrite <- Vnth_tail_lt_S_n. apply i0; auto.
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

  Lemma bVforall2_elim_2 : forall (A B : Type)(a : vector A 2)(b : vector B 2)
    (R : A-> B -> bool),
    bVforall2 R a b -> R (Vhead a)(Vhead b) /\ R (VlastS a)(VlastS b).
  Proof.
    intros. split. apply bVforall2_elim_head in H; auto.
    assert (1 < 2). lia. apply (bVforall2_elim_nth H0) in H. do 2 rewrite VlastS_nth.
    trivial.
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

  Lemma bVforall_elim_last  : forall n (A : Type)(v1 : vector A (S n))
       (R : A -> bool), 
   bVforall R v1 -> bVforall R (Vremove_last v1).
  Proof.
    intros. apply bVforall_nth_intro. intros. rewrite Vnth_remove_last.
    apply (bVforall_elim_nth (Nat.lt_lt_succ_r ip)) in H. trivial.
  Qed.

  Lemma bVforall2_nth_intro : forall n (A B : Type)(v1 : vector A n)
      (v2 : vector B n)(R : A -> B -> bool),
    (forall i (ip : i < n), R (Vnth v1 ip) (Vnth v2 ip)) ->
       bVforall2 R v1 v2.
  Proof.
    unfold Vforall2. induction v1; intros. VOtac. simpl. auto.
    revert H. VSntac v2. intro. cbn. apply Bool.andb_true_iff. 
    split. apply (H0 0 (lt_O_Sn _)). unfold bVforall2 in IHv1.
    apply IHv1. intros. assert (S i< S n). lia.
    pose (H0 (S i) H1). simpl in i0. assert (ip = lt_S_n H1).
    apply NatUtil.lt_unique. rewrite H2. apply i0.
  Qed.

  Lemma bVforall2_follows : forall n (A B B' : Type)
    (f' : B -> B')(f'' : A -> B' -> bool)
    (f : A -> B -> bool)(v : vector A n)(v' : vector B n),    
    bVforall2 f v v' ->
    (forall a b, f a b -> f'' a (f' b)) ->
    bVforall2 f'' v (Vmap f' v').
  Proof.
    intros. apply bVforall2_nth_intro. intros.
    pose (bVforall2_elim_nth ip v v' f H). rewrite Vnth_map. apply H0.
    apply i0.
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
    intros. assert (n' + n'' = n). lia. split.
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
    intros. assert (n' + n'' = n). lia. split.
    apply bVforall2_nth_intro. intros. rewrite Vnth_vbreak_1.
    intros. rewrite (Vnth_vbreak_1 n'' (Vcast v' h) ip Hyp0).
    subst. apply (bVforall2_elim_nth Hyp0) in H.
    apply H. lia. apply bVforall2_nth_intro. intros. 
    rewrite Vnth_vbreak_2. intros.  rewrite (Vnth_vbreak_2 n'
    (Vcast v' h) ip Hyp0). subst.
    apply (bVforall2_elim_nth Hyp0) in H. apply H. lia. 
  Qed.

  Lemma bVforall2_sub : forall n n' n'' (h : n' + n'' <= n)(A B : Type)
      (v : vector A n)(v' : vector B n)(R : A -> B -> bool),
    bVforall2 R v v' -> 
    bVforall2 R (Vsub v h) (Vsub v' h).
  Proof.
    intros. apply bVforall2_nth_intro. intros. do 2 rewrite Vnth_sub.
    apply (bVforall2_elim_nth (Vnth_sub_aux n' h ip)) in H. trivial.
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

  Lemma bVforall_split : forall n (A : Type)
    (f f' : A -> bool)(v : vector A n),
    bVforall (fun a => f a && f' a) v ->
    bVforall f v && bVforall f' v.
  Proof.
    intros. apply Bool.andb_true_iff. split.
    apply (bVforall_follows (fun a : A => f a && f' a)).
    intros. apply Bool.andb_true_iff in H0. destruct H0. apply H0. trivial.
    apply (bVforall_follows (fun a : A => f a && f' a)).
    intros. apply Bool.andb_true_iff in H0. destruct H0. apply H1. trivial.
  Qed.

  Lemma Vsub_map : forall n (A B : Type) (a : vector A n) i j (ip : i+j<=n)
      (f: A -> B),
    Vmap f (Vsub a ip) = Vsub (Vmap f a) ip.
  Proof.  
    intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_sub.
    rewrite Vnth_map. trivial.
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

  Lemma PairwisePredict_2 : forall (A : Type)(f : A -> A -> bool)(v : vector A 2),
    PairwisePredicate f v -> f (Vhead v) (VlastS v).
  Proof.
    intros. rewrite (VSn_eq v) in H. rewrite (VSn_eq (Vtail v)) in H.
    rewrite (Vector_0_is_nil (Vtail (Vtail v))) in H. simpl in H.
    apply andb_true_iff in H. destruct H. apply andb_true_iff in H. destruct H.
    replace (VlastS v) with (Vhead (Vtail v)). trivial. apply VlastS_Vhead_Vtail.
  Qed.

  Lemma PairwisePredicateSplit : forall (A : Type)(n : nat)(f f' : A -> A -> bool)
      (v : vector A n),
    PairwisePredicate (fun a b => f a b && f' a b) v ->
    PairwisePredicate f v && PairwisePredicate f' v.
  Proof.
    intros. apply andb_true_intro. induction v; simpl in *. split; trivial.
    (* inductive case *)
    apply andb_true_iff in H. destruct H. apply bVforall_split in H.
    apply andb_true_iff in H. destruct H. split; apply andb_true_intro; split; 
    trivial. apply IHv; trivial. apply IHv; trivial.
  Qed.

  Lemma PairwisePredicateSplitUnzip : 
    forall (A B : Type)(n : nat)(f : A -> A -> bool)(f' : B -> B -> bool)
      (v : vector (A*B) n),
    PairwisePredicate (fun a b => f a.1 b.1 && f' a.2 b.2) v ->
    PairwisePredicate f (UnzipLeft v) && PairwisePredicate f' (UnzipRight v).
  Proof.
    intros. apply andb_true_intro. induction v; simpl in *. split; trivial.
    (* inductive case *)
    apply andb_true_iff in H. destruct H. apply bVforall_split in H.
    apply andb_true_iff in H. destruct H. split; apply andb_true_intro; split.
    + apply bVforall_nth_intro. intros. apply (bVforall_elim_nth ip) in H.
    rewrite Vnth_map. trivial.
    + apply IHv; trivial.
    + apply bVforall_nth_intro. intros. apply (bVforall_elim_nth ip) in H1.
    rewrite Vnth_map. trivial.
    + apply IHv; trivial.
  Qed.

  Lemma PairwisePredicateVnth : forall (A : Type)(n : nat)(f : A -> A -> bool)
      (v : vector A n),
    (forall i j (ip : i < n)(jp : j < n), i <> j -> f (Vnth v ip) (Vnth v jp)) 
    -> PairwisePredicate f v.
  Proof.
    intros. induction v. trivial. simpl. apply andb_true_intro. split.
    apply bVforall_nth_intro. intros. assert (0 < S n). lia.
    pose (H 0 (S i) H0 (lt_n_S ip)). simpl in i0.
    assert (Vnth v (lt_S_n (lt_n_S ip)) = Vnth v ip). apply Vnth_eq. trivial.
    rewrite <- H1. apply i0. lia.
    apply IHv. intros. assert (S i <> S j). lia. 
    pose (H (S i) (S j) (lt_n_S ip) (lt_n_S jp) H1).
    assert (forall (v : vector A n)  i (ip : i < n), (Vnth v ip) = Vnth (Vcons h v) (lt_n_S ip)).
    intros. rewrite Vnth_cons. simpl. apply Vnth_eq. lia.
    do 2 rewrite H2. apply i0.
  Qed.
  
  Lemma PairwisePredicateImp : forall (A A' : Type)(n : nat)(f : A -> A')
        (f' : A' -> A' -> bool)(f'' : A -> A -> bool)(v : vector A n),
    (forall a b, f' (f a) (f b) = f'' a b) ->
    PairwisePredicate f' (Vmap f v) -> PairwisePredicate f'' v.
  Proof.
    intros. induction v. cbn. trivial. simpl in *. apply andb_prop in H0.
    destruct H0. apply andb_true_intro. split. apply bVforall_nth_intro.
    intros. apply (bVforall_elim_nth ip) in H0. rewrite Vnth_map in H0.
    rewrite H in H0. trivial. apply IHv. trivial.
  Qed.

  Lemma PairwisePredicateVnth2 : forall (A : Type)(f : A -> A -> bool),
    (forall a b, f a b = f b a) ->
    forall (n : nat)(v : vector A n),
    PairwisePredicate f v ->
    (forall i j (ip : i < n)(jp : j < n), i <> j -> f (Vnth v ip) (Vnth v jp)).
  Proof.
    induction n. intros. assert False. lia. contradiction.
    (* Inductive step *)
    intros. rewrite (VSn_eq v) in H0. simpl in H0. apply andb_prop in H0.
    destruct H0. destruct i. 
    (* Head *) destruct j. lia. assert (Vnth v ip = Vhead v).
    rewrite Vhead_nth. apply Vnth_eq. lia. rewrite H3. rewrite (VSn_eq v).
    rewrite Vnth_cons. destruct (lt_ge_dec 0 (S j)). rewrite <- VSn_eq.
    apply (bVforall_elim_nth (Vnth_cons_tail_aux jp l)) in H0. apply H0. lia.
    (* Tail *)
    rewrite (VSn_eq v). do 2 rewrite Vnth_cons. destruct (lt_ge_dec 0 (S i)).
    destruct (lt_ge_dec 0 j). apply IHn; auto. lia. assert (j=0). lia. subst.
    rewrite H.
    apply (bVforall_elim_nth (Vnth_cons_tail_aux ip l)) in H0. apply H0.
    lia. 
  Qed.

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
    PairwisePredicate f v =
    bVforall (f (Vhead v)) (Vtail v) && PairwisePredicate f (Vtail v).
  Proof.
    intros. rewrite (VSn_eq v). simpl. trivial.
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
    rewrite PairwiseInd in H. apply andb_true_iff in H. destruct H.
    assert (Vtail v = (Vtail (Vcast v H0))). apply Veq_nth. intros. 
    do 2 rewrite Vnth_tail. rewrite Vnth_cast. apply Vnth_eq. trivial.
    rewrite H4. split. rewrite Vhead_cast in H. 
    apply (bVforall_break_sub n' n'') in H. apply H. apply IHn'.
    apply H3. 
  Qed.
  
  Lemma PairwisePredicate_sub : forall (A : Type)(n n' n'' : nat)(h : n' + n'' <= n)
    (f : A -> A -> bool)(v : vector A n),
    (forall a b, f a b = f b a) ->
    PairwisePredicate f v -> PairwisePredicate f (Vsub v h).
  Proof.
    intros. apply PairwisePredicateVnth. intros.
    pose (PairwisePredicateVnth2 f H v H0 (Vnth_sub_aux n' h ip) 
    (Vnth_sub_aux n' h jp)). do 2 rewrite Vnth_sub. apply i0. lia.
  Qed.

  Lemma PairwisePredicate_cast : forall (A : Type)(n n' : nat)(h : n = n')
    (f : A -> A -> bool)(v : vector A n),
    (forall a b, f a b = f b a) ->
    PairwisePredicate f v -> PairwisePredicate f (Vcast v h).
  Proof.
    intros. apply PairwisePredicateVnth. intros. do 2 rewrite Vnth_cast.
    pose (PairwisePredicateVnth2 f H v H0 (Vnth_cast_aux h ip) 
    (Vnth_cast_aux h jp)). apply i0. lia.
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

  Lemma Vconst_cons : forall n (A : Type)(a : A),
    Vconst a (S n) = Vcons a (Vconst a n).
  Proof.
    intros. simpl. trivial. 
  Qed.

  Lemma Vfold_left_Vconst : forall n (A : Type)(a b : A)(f : A -> A -> A),
    (forall a0 b0 c : A, f (f a0 b0) c = f a0 (f b0 c)) ->
    (forall a0 b0 : A, f a0 b0 = f b0 a0) ->
    f (Vfold_left f b (Vconst a n)) a = Vfold_left f b (Vconst a (S n)).
  Proof.
    intros. induction n. cbn. trivial.
    replace (Vconst a (S (S n))) with (Vcons a (Vconst a (S n))). 
    rewrite Vfold_left_Vcons; auto. simpl. trivial.
  Qed. 

  Lemma Vconst_map2 : forall n (A B C : Type)(f : A -> B -> C)
      (v : vector A n)(b : B),
    Vmap2 f v (Vconst b n) = Vmap (fun x => f x b) v.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_map.
    rewrite Vnth_const. trivial.
  Qed.

  Lemma Vconst_map22 : forall n (A B C : Type)(f : B -> A -> C)
      (v : vector A n)(b : B),
    Vmap2 f (Vconst b n) v = Vmap (f b) v.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_map.
    rewrite Vnth_const. trivial.
  Qed.
  
  Lemma bVforall_false : forall n (A: Type)(v : vector A n)(R : A -> bool),
    bVforall R v = false ->
    exists i (ip : i <n), R (Vnth v ip) = false.
  Proof.
    intros. induction n. rewrite (Vector_0_is_nil v) in H. cbn in H. discriminate.
    rewrite (VSn_eq v) in H. cbn in H. apply andb_false_iff in H. destruct H. exists 0.
    exists (Nat.lt_0_succ n). rewrite Vhead_nth in H.
    apply H.  apply IHn in H. destruct H. destruct H.
    exists (S x). exists (lt_n_S x0). rewrite <- H.
    rewrite Vnth_tail. trivial.
  Qed.

  Lemma bVforall_false2 : forall n (A B : Type)(v : vector A n)
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

  Lemma Vfold_left_adduction : forall (n : nat)(A : Type) 
    (f : A->A->A)(v : vector A (S n))(a : A),
    (forall a0 b c : A, f (f a0 b) c = f a0 (f b c)) ->
    (forall a b, f a b = f b a) -> 
  Vfold_left f a v = f (Vfold_left f a (Vremove_last v)) (VlastS v).
  Proof.
    intros. rewrite (VSn_addS v). rewrite Vfold_add. trivial. trivial. 
    rewrite <- VSn_addS. trivial.
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

  Lemma Vbuild_remove_last : forall n (A : Type) (gen : forall i, i < S n -> A),
    Vremove_last (Vbuild gen) =
    Vbuild (fun (j : nat) (jp : j < n) => gen j (Nat.lt_lt_succ_r jp)).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_remove_last. do 2 rewrite Vbuild_nth.
    trivial. 
  Qed.


  Lemma Vfold_left_build : forall n (A : Type)(f : A->A->A)(a : A) 
      (gen : forall i, i < S n -> A),
    (forall a0 b c : A, f (f a0 b) c = f a0 (f b c)) ->
    (forall a b, f a b = f b a) -> 
    Vfold_left f a (Vbuild
     (fun (j : nat) (jp : j < S n) => gen j jp)) = 
    f (Vfold_left f a (Vbuild
     (fun (j : nat) (jp : j < n) => gen j (lt_S jp)))) (gen n (lt_n_Sn n)).
  Proof.
    intros. rewrite (VSn_addS (Vbuild (fun j : nat => [eta gen j]))).
    rewrite Vfold_add; auto. apply f_equal2. rewrite Vbuild_remove_last.
    trivial. rewrite VlastS_nth. rewrite Vbuild_nth. trivial.
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

  Lemma Vapp_Vtail2 : forall n n' A (v : vector A (S n))(v' : vector A n'),
    Vtail (Vapp v v') = Vapp (Vtail v) v'.
  Proof.
    intros. rewrite Vapp_Vtail. trivial.
  Qed.

  Lemma Vbreak_Vtail : forall n n' A (v : vector A (S n+n')),
    Vtail (Vbreak v).1 = (Vbreak (Vtail v)).1.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_tail. trivial.
  Qed.

  Lemma Vbreak_Vtail_clear : forall n n' A (v : vector A (S n+n')),
    (Vbreak (Vtail v)).2 = (Vbreak v).2.
  Proof.
    intros. cbn. trivial.
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
 
  Lemma Vapp_eq_cast : forall n2 n2' (h : n2 = n2') n1 A (v1 : vector A n1) 
    (v2 : vector A n2)(h' : n1+n2 = n1+n2'),
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

  (* Sadly the above to much with too many things and cause we problem 
     so we need less general cases *)

  Lemma Prod_left_left_replace : forall A B C
      (a : A) (b : B) (c : C),
    (a,b,c).1.1 = a.
  Proof.
    intros. simpl. auto.
  Qed.


  Lemma Prod_left_right_replace : forall A B C
      (a : A) (b : B) (c : C),
    (a,b,c).1.2 = b.
  Proof.
    intros. simpl. auto.
  Qed.

  Lemma Prod_left2_right_replace : forall A B C D
      (a : A) (b : B) (c : C)(d : D),
    (a,b,c,d).1.1.2 = b.
  Proof.
    intros. simpl. auto.
  Qed.

  Lemma Vhead_sub : forall A n (a : vector A (S n)) i (ip : 0+S i<=(S n)),
    Vhead (Vsub a ip) = Vhead a.
  Proof.
    intros. do 2 rewrite Vhead_nth. rewrite Vnth_sub.
    apply Vnth_eq. lia.
  Qed.

  Ltac simpl_prod := repeat progress (try rewrite Prod_left_replace; 
      try rewrite Prod_right_replace).

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

  Lemma Vhead_app2 : forall n m A 
      (a : vector A (S (S n)))(b : vector A m),
    Vhead (Vtail (Vapp a b)) = Vhead (Vtail a).
  Proof.
    intros. do 2 rewrite Vhead_nth. do 2 rewrite Vnth_tail.
    rewrite (Vnth_app (n1:= (S (S n)))). destruct (le_gt_dec (S (S n)) 1).
    assert (False). lia. contradiction. apply Vnth_eq. lia.
  Qed.

  Lemma Vhead_break2 : forall n m A 
      (a : vector A (S (S n)+m)),
    Vhead (Vtail (a)) = Vhead (Vtail (Vbreak a).1).
  Proof.
    intros. do 2 rewrite Vhead_nth. do 2 rewrite Vnth_tail.
    rewrite Vnth_vbreak_1. intros. apply Vnth_eq. lia. lia.
  Qed.

  Lemma Vhead_break3 : forall n m A 
      (a : vector A (S (S (S n))+m)),
    Vhead (Vtail (Vtail a)) = Vhead (Vtail (Vtail (Vbreak a).1)).
  Proof.
    intros. do 2 rewrite Vhead_nth. do 4 rewrite Vnth_tail.
    rewrite Vnth_vbreak_1. intros. apply Vnth_eq. lia. lia.
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

  Lemma Vhead_break : forall (A : Type) n n' (a : vector A (S n+n')),
    Vhead (Vbreak a).1 = Vhead a. 
  Proof.
    intros. cbn. trivial.
  Qed.

  Lemma Vbreak_vmap_1 : forall (A B : Type)(f: A -> B) n n'
    (a : vector A (n+n')),
    Vmap f (Vbreak a).1  = (Vbreak (Vmap f a)).1.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_vbreak_1.
    intros. rewrite Vnth_vbreak_1. rewrite Vnth_map. trivial. lia. 
  Qed.

  Lemma Vbreak_vmap_2 : forall (A B : Type)(f: A -> B) n n'
    (a : vector A (n+n')),
    Vmap f (Vbreak a).2  = (Vbreak (Vmap f a)).2.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_vbreak_2.
    intros. rewrite Vnth_vbreak_2. rewrite Vnth_map. trivial. lia. 
  Qed.

  Lemma Vbreak_vmap2_1 : forall (A B C : Type)(f: A -> B -> C) n n'
    (a : vector A (n+n'))(b : vector B (n+n')),
    Vmap2 f (Vbreak a).1 (Vbreak b).1 = (Vbreak (Vmap2 f a b)).1.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_vbreak_1.
    intros. do 2 rewrite Vnth_vbreak_1. rewrite Vnth_map2. trivial. lia. 
  Qed.

  Lemma Vbreak_vmap2_2 : forall (A B C : Type)(f: A -> B -> C) n n'
    (a : vector A (n+n'))(b : vector B (n+n')),
    Vmap2 f (Vbreak a).2 (Vbreak b).2 = (Vbreak (Vmap2 f a b)).2.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_vbreak_2.
    intros. do 2 rewrite Vnth_vbreak_2. rewrite Vnth_map2. trivial. lia. 
  Qed.

  Lemma Vbreak_Vconst : forall n n' (A : Type)(a : A),
    Vbreak (Vconst a (n+n')) = (Vconst a n, Vconst a n').
  Proof.
    intros. apply injective_projections. simpl. apply Veq_nth. intros.
    rewrite Vnth_vbreak_1. intros. do 2 rewrite Vnth_const. trivial. lia.
    apply Veq_nth. intros. rewrite Vnth_vbreak_2. intros. do 2 rewrite Vnth_const.
    trivial. lia.
  Qed.

  Lemma Vapp_Vconst : forall n n' (A : Type)(a : A),
    Vconst a (n+n') = Vapp (Vconst a n) (Vconst a n').
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_app. destruct (le_gt_dec n i).
    do 2 rewrite Vnth_const. trivial. do 2 rewrite Vnth_const. trivial.
  Qed.

  Lemma Vfold_left_zip : forall n (A B : Type)(v : vector (A*B) n)
      (acc : A*B)(f : A->A->A)(f' : B->B->B),
    (Vfold_left (fun a b : A*B => (f a.1 b.1, f' a.2 b.2)) acc v) =
     (Vfold_left (fun a b => (f a b)) acc.1 (UnzipLeft v),
        Vfold_left (fun a b => (f' a b)) acc.2 (UnzipRight v)).
  Proof.
    intros n A B. induction n. intros. rewrite (Vector_0_is_nil v). 
    cbn. apply surjective_pairing. intros. rewrite (VSn_eq v). simpl.
    apply IHn. 
  Qed.

  Fixpoint bVforall3 A B C n (f : A -> B -> C -> bool) :
      vector A n -> vector B n -> vector C n -> bool :=
    match n with
      | 0 => fun _ => fun _ => fun _ => true
      | S a => fun x => fun y => fun z => 
          f (Vhead x) (Vhead y) (Vhead z) && 
          bVforall3 f (Vtail x) (Vtail y) (Vtail z)
    end.

  Lemma bVforall3_elim_nth : forall n i 
    (ip : i < n)(A B C : Type)(v1 : vector A n) (v2 : vector B n)
    (v3 : vector C n) (R : A -> B -> C -> bool), 
   bVforall3 R v1 v2 v3 -> R (Vnth v1 ip) (Vnth v2 ip) (Vnth v3 ip).
  Proof.
    induction n; intros. absurd (i<0); lia.
    rewrite (VSn_eq v1) in H. rewrite (VSn_eq v2) in H.
    rewrite (VSn_eq v3) in H. cbn in H. apply andb_prop in H. destruct H.
    destruct i. do 3 rewrite <- Vnth0Head. trivial.
    do 3 rewrite <- Vnth_tail_lt_S_n.
    apply (IHn i (lt_S_n ip) A B C (Vtail v1) (Vtail v2) (Vtail v3) R); trivial.
  Qed.

  Lemma bVforall3_elim_head : forall n (A B C : Type)(v1 : vector A (S n)) 
    (v2 : vector B (S n))(v3 : vector C (S n)) (R : A -> B -> C -> bool), 
   bVforall3 R v1 v2 v3 -> R (Vhead v1) (Vhead v2) (Vhead v3).
  Proof.
    intros. do 3 rewrite Vhead_nth. apply bVforall3_elim_nth. trivial.
  Qed.

  Lemma bVforall3_nth_intro : forall n (A B C : Type)(v1 : vector A n)
      (v2 : vector B n)(v3 : vector C n)(R : A -> B -> C -> bool),
    (forall i (ip : i < n), R (Vnth v1 ip) (Vnth v2 ip) (Vnth v3 ip)) ->
       bVforall3 R v1 v2 v3.
  Proof.
    induction v1; intros. VOtac. simpl. auto.
    revert H. VSntac v2. VSntac v3. intro. cbn. apply Bool.andb_true_iff. 
    split. apply (H1 0 (lt_O_Sn _)). unfold bVforall3 in IHv1.
    apply IHv1. intros. assert (S i< S n). lia.
    pose (H1 (S i) H2). simpl in i0. assert (ip = lt_S_n H2).
    apply NatUtil.lt_unique. rewrite H3. apply i0.
  Qed.

  Lemma bVforall3_cast : forall n (A B C : Type) (v1 : vector A n)
    (v2 : vector B n)(v3 : vector C n) (f : A->B->C->bool) p p' (h:p+p'<=n),
    bVforall3 f v1 v2 v3 -> bVforall3 f (Vsub v1 h)(Vsub v2 h)(Vsub v3 h).
  Proof.
    intros. apply bVforall3_nth_intro. intros.
    apply (bVforall3_elim_nth (Vnth_sub_aux p h ip)) in H. 
    do 3 rewrite Vnth_sub. trivial.
  Qed.

  Lemma bVforall_false3 : forall n (A B C : Type)(v : vector A n)
      (v' : vector B n)(v'' : vector C n)(R : A -> B -> C-> bool),
    bVforall3 R v v' v'' = false ->
    exists i (ip : i <n), R (Vnth v ip) (Vnth v' ip) (Vnth v'' ip) = false.
  Proof.
    intros. induction n. rewrite (Vector_0_is_nil v) in H.
    rewrite (Vector_0_is_nil v') in H. cbn in H. discriminate.
    rewrite (VSn_eq v) in H. rewrite (VSn_eq v') in H.
    cbn in H. apply andb_false_iff in H. destruct H. exists 0.
    exists (Nat.lt_0_succ n). do 3 rewrite Vhead_nth in H.
    apply H.  apply IHn in H. destruct H. destruct H.
    exists (S x). exists (lt_n_S x0). rewrite <- H.
    do 3 rewrite Vnth_tail. trivial. 
  Qed.

  Fixpoint bVforall4 A B C D n (f : A -> B -> C -> D -> bool) :
      vector A n -> vector B n -> vector C n -> vector D n ->  bool :=
    match n with
      | 0 => fun _ => fun _ => fun _ => fun _ => true
      | S a => fun x => fun y => fun z => fun w =>
          f (Vhead x) (Vhead y) (Vhead z) (Vhead w) && 
          bVforall4 f (Vtail x) (Vtail y) (Vtail z) (Vtail w)
    end.

  Fixpoint bVforall5 A B C D E n (f : A -> B -> C -> D -> E -> bool) :
      vector A n -> vector B n -> vector C n -> vector D n ->
          vector E n -> bool :=
    match n with
      | 0 => fun _ => fun _ => fun _ => fun _ => fun _ => true
      | S a => fun x => fun y => fun z => fun w => fun r =>
          f (Vhead x) (Vhead y) (Vhead z) (Vhead w) (Vhead r) && 
          bVforall5 f (Vtail x) (Vtail y) (Vtail z) (Vtail w) (Vtail r) 
    end.

 Fixpoint Vexists2 A B n (f : A -> B -> Prop) : vector A n ->
      vector B n -> Prop :=
    match n with
      | 0 => fun _ => fun _ => False
      | S a => fun x => fun y => f (Vhead x) (Vhead y) \/ 
        Vexists2 f (Vtail x) (Vtail y)
    end.

  Lemma Vexists2_Vtail : forall A B n (f : A -> B -> Prop)
    (a : vector A (S n))(b : vector B (S n)),
    Vexists2 f (Vtail a) (Vtail b) -> Vexists2 f a b.
  Proof.  
    intros. destruct n; simpl in *. right. trivial.
    destruct H. right. left. trivial. right. right. trivial.
  Qed.

  Lemma Vexists2_nth_elim : forall n A B (R : A -> B -> Prop) i (ip : i < n)
    (v1 : vector A n)(v2 : vector B n),
      R (Vnth v1 ip) (Vnth v2 ip) -> Vexists2 R v1 v2.
  Proof.
    induction n. intros. assert False. lia. contradiction. 
    intros. simpl. destruct i. left. do 2 rewrite <- Vnth0Head in H. trivial.
    right. apply (IHn A B R i (lt_S_n ip)). 
    do 2 rewrite Vnth_tail_lt_S_n. trivial.
  Qed.

  Lemma Vforall2Comb_nth_intro : forall n (A B C D : Type)(v1 : vector A n)
      (v2 : vector B n)(v3 : vector C n)(v4 : vector D n)(R : A -> B -> bool)
        (R' : C -> D -> Prop), (forall i (ip : i < n), R (Vnth v1 ip) (Vnth v2 ip) 
        \/ R' (Vnth v3 ip) (Vnth v4 ip))
           -> bVforall2 R v1 v2 \/ Vexists2 R' v3 v4.
  Proof.
    intros. induction n. simpl. left. apply bVforall2_nth_intro.
    intros. assert False. lia. contradiction.
    (* Inductive step *)
   assert (0 < S n). lia. pose (H 0 H0). destruct o. 
   assert (forall (i : nat) (ip : i < n),
    R (Vnth (Vtail v1) ip) (Vnth (Vtail v2) ip) \/ 
    R' (Vnth (Vtail v3) ip) (Vnth (Vtail v4) ip)). intros. 
   pose (H (S i) (lt_n_S ip)). destruct o. left. do 2 rewrite Vnth_tail. 
   trivial. right. do 2 rewrite Vnth_tail. trivial.
   pose (IHn (Vtail v1) (Vtail v2) (Vtail v3) (Vtail v4) H2).
   destruct o. left. rewrite (VSn_eq v1). rewrite (VSn_eq v2).
   cbn. apply andb_true_iff. split. do 2 rewrite <- Vnth0Head in H1.
   trivial. apply H3. right. apply Vexists2_Vtail. trivial.
    (* dumb case where there is an exists *)
    right. apply (Vexists2_nth_elim R' H0). trivial.
  Qed.

   Lemma Vforall3Comb_nth_intro : forall n (A B C D E : Type)(v1 : vector A n)
      (v2 : vector B n)(v3 : vector C n)(v4 : vector D n)(v5 : vector E n)
      (R : A -> B -> C -> bool)(R' : D -> E -> Prop), 
      (forall i (ip : i < n), R (Vnth v1 ip) (Vnth v2 ip) (Vnth v3 ip)
        \/ R' (Vnth v4 ip) (Vnth v5 ip))
           -> bVforall3 R v1 v2 v3 \/ Vexists2 R' v4 v5.
  Proof.
    intros. induction n. simpl. left. trivial.
    (* Inductive step *)
   assert (0 < S n). lia. pose (H 0 H0). destruct o. 
   assert (forall (i : nat) (ip : i < n),
    R (Vnth (Vtail v1) ip) (Vnth (Vtail v2) ip) (Vnth (Vtail v3) ip) \/ 
    R' (Vnth (Vtail v4) ip) (Vnth (Vtail v5) ip)). intros. 
   pose (H (S i) (lt_n_S ip)). destruct o. left. do 3 rewrite Vnth_tail. 
   trivial. right. do 2 rewrite Vnth_tail. trivial.
   pose (IHn (Vtail v1) (Vtail v2) (Vtail v3) (Vtail v4) (Vtail v5) H2).
   destruct o. left. rewrite (VSn_eq v1). rewrite (VSn_eq v2). rewrite (VSn_eq v3).
   cbn. apply andb_true_iff. split. do 3 rewrite <- Vnth0Head in H1.
   trivial. apply H3. right. apply Vexists2_Vtail. trivial.
    (* dumb case where there is an exists *)
    right. apply (Vexists2_nth_elim R' H0). trivial.
  Qed.

  

  Lemma Lenght0Recon : forall (A :Type)(v : vector A 1),
    [Vhead v] = v.
  Proof.
    intros. rewrite (VSn_eq v). simpl. rewrite (VO_eq (Vtail v)). trivial.
  Qed. 

  (* I want a version of permutations on vectors which does what I want *)
  (* This has turned out to be much harder than I thought *)

  Definition Index N := {x:nat | x < N}. 

  Definition MakeIndex N i (ip : i < N): Index N :=  
   @exist nat (fun x => x < N) i ip.

  Lemma Index1 : forall (a : Index 1),
    sval a = 0.
  Proof.
    intros. destruct a. simpl. destruct x. trivial. lia.
  Qed.

  Definition MakeIndexPrev N (x : Index (S N)) :     
    sval x <> 0 -> Index N.
  Proof.
    intros. destruct x. simpl in *. exists (x -1). lia.
  Defined.

  Definition MakeIndexSucc N (x : Index N) : Index (S N).
  Proof.
    intros. destruct x. exists (S x). apply (lt_n_S l).
  Defined.

  Lemma MakeIndexSuccProj : forall N (x : Index N),
    sval (MakeIndexSucc x) = S (sval x).
  Proof.
    intros. destruct x. simpl. lia.
  Qed.

  Lemma MakeIndexSuccEq : forall A N (x x' : Index N)(v v' : vector A (S N)),
    Vnth (Vtail v) (proj2_sig x) = Vnth (Vtail v') (proj2_sig x') ->
    Vnth v (proj2_sig (MakeIndexSucc x)) = Vnth v' (proj2_sig (MakeIndexSucc x')).
  Proof.
    intros. destruct x, x'. simpl. do 2 rewrite Vnth_tail in H. simpl in H.
    trivial.
  Qed.

  Lemma MakeIndex_lt_0_succ : forall n,
    sval (MakeIndex (Nat.lt_0_succ n)) = 0.
  Proof.
    intros. cbn. trivial. 
  Qed.
  
  Lemma MakeIndexPrevCorr : forall N A (x : Index (S N))(a : vector A (S N))
    (b : sval x <> 0),
    Vnth a (proj2_sig x) = Vnth (Vtail a) (proj2_sig (MakeIndexPrev x b)).
  Proof.
    intros. rewrite Vnth_tail. apply Vnth_eq. destruct x. simpl in *. lia.
  Qed.

  Lemma MakeIndexPrevEq : forall N (x x1 : Index (S N))(b : sval x <> 0)
        (b' : sval x1 <> 0),
    sval x = sval x1 <->
    sval (MakeIndexPrev x b) = sval (MakeIndexPrev x1 b').
  Proof.
   split; intros; destruct x, x1; simpl in *; lia. 
  Qed.

  Lemma eq_proj N:
  forall a b : Index N,
  a = b <-> proj1_sig(a) = proj1_sig(b).
  Proof.
    split; intros.
    + rewrite H. auto.
    + destruct a, b. cbn in *.
      subst. f_equal. apply lt_unique.
  Qed.

  (* We are now ready to define permutations *)
  (* We do this using the inverse *)

  Definition Permutation N := {x: (vector (Index N) N)*(vector (Index N) N) |
     forall i (ip : i < N), Vnth x.1 (proj2_sig (Vnth x.2 ip)) = MakeIndex ip /\
     Vnth x.2 (proj2_sig (Vnth x.1 ip)) = MakeIndex ip
  }.

  Definition Perm_Id N : Permutation N.
  Proof.
    pose (Vbuild (fun i (ip : i < N) => MakeIndex ip)).
    exists (t, t). intros. simpl. do 2 rewrite Vbuild_nth. simpl.
    split; trivial.
  Defined.

  Definition Permute n (A : Type)(a : vector A n)(pi : Permutation n) : vector A n :=
    Vbuild (fun i (ip : i < n) => Vnth a (proj2_sig (Vnth (proj1_sig pi).1 ip))).

  Definition PermuteInv n (A : Type)(a : vector A n)(pi : Permutation n) : vector A n :=
    Vbuild (fun i (ip : i < n) => Vnth a (proj2_sig (Vnth (proj1_sig pi).2 ip))).

  Lemma eq_proj_perm : forall N (a b : Permutation N),
    a = b <-> proj1_sig(a) = proj1_sig(b).
  Proof.
    split; intros.
    + rewrite H. auto.
    + destruct a, b. cbn in *. apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat; auto.
  Qed.

  Definition InvPermutation N (pi : Permutation N) : Permutation N.
  Proof.
    destruct pi. exists (x.2, x.1). intros. simpl.
    split; apply a.
  Defined.

  Lemma InvCorrect : forall n (A : Type)(a : vector A n)(pi : Permutation n),
    Permute (Permute a pi) (InvPermutation pi) = a.
  Proof.
    intros. unfold Permute, InvPermutation. apply Veq_nth. intros. 
    rewrite Vbuild_nth. rewrite Vbuild_nth. apply Vnth_eq. destruct pi. simpl.
    destruct (a0 i ip). rewrite H. trivial.
  Qed.

  Lemma InvCorrProj : forall n A (a : vector A n)(pi : Permutation n) i (ip : i < n),
    Vnth a (proj2_sig (Vnth (sval pi).1
          (proj2_sig (Vnth (sval (InvPermutation pi)).1 ip)))) = Vnth a ip.
  Proof.
   intros. destruct pi. apply Vnth_eq. simpl. destruct (a0 i ip). rewrite H.
   trivial. 
  Qed.
 
  Lemma InvCorrProj2 : forall n A (a : vector A n)(pi : Permutation n) i (ip : i < n),
    Vnth a (proj2_sig (Vnth (sval (InvPermutation pi)).1
          (proj2_sig (Vnth (sval pi).1 ip)))) = Vnth a ip.
  Proof.
   intros. destruct pi. apply Vnth_eq. simpl. destruct (a0 i ip). rewrite H0.
   trivial. 
  Qed.
  

  Lemma InvCorrProj3 : forall n A (a : vector A n)(pi : Permutation n) i (ip : i < n),
    Vnth a (proj2_sig (Vnth (sval pi).2
          (proj2_sig (Vnth (sval (InvPermutation pi)).2 ip)))) = Vnth a ip.
  Proof.
   intros. destruct pi. apply Vnth_eq. simpl. destruct (a0 i ip). rewrite H0.
   trivial. 
  Qed.
 
  Lemma InvCorrProj4 : forall n A (a : vector A n)(pi : Permutation n) i (ip : i < n),
    Vnth a (proj2_sig (Vnth (sval (InvPermutation pi)).2
          (proj2_sig (Vnth (sval pi).2 ip)))) = Vnth a ip.
  Proof.
   intros. destruct pi. apply Vnth_eq. simpl. destruct (a0 i ip). rewrite H.
   trivial. 
  Qed.

  Lemma InvCorrComp : forall n (pi pi' : Permutation n) i (ip : i < n),
    Vnth (sval pi).1 (proj2_sig (Vnth (sval (InvPermutation pi)).1 
      (proj2_sig (Vnth (sval pi').1 ip)))) = Vnth (sval pi').1 ip.
  Proof.
    intros. destruct pi, pi'. simpl. destruct (a (sval (Vnth x0.1 ip)) (proj2_sig (Vnth x0.1 ip))).
    rewrite H. apply eq_proj. simpl. trivial.
  Qed.
    

  (* Now to compose *)

  Definition ComposePerm N (a b : Permutation N) : Permutation N.
  Proof.
    intros. exists (Permute (sval a).1 b, PermuteInv (sval b).2 a). intros.
    destruct a, b. simpl; do 4 rewrite Vbuild_nth. simpl. split.
    destruct (a0 (sval (Vnth x.2 ip)) (proj2_sig (Vnth x.2 ip))).
    rewrite H. simpl. apply a. destruct (a (sval (Vnth x0.1 ip))
    (proj2_sig (Vnth x0.1 ip))). rewrite H0. apply a0.
  Defined.

  Lemma CompPermutationId : forall N (pi : Permutation N),
    ComposePerm (Perm_Id N) pi = pi.
  Proof.
    intros. apply eq_proj_perm. simpl. apply injective_projections.
    simpl. apply Veq_nth. intros. do 2 rewrite Vbuild_nth. apply eq_proj.
    simpl. trivial. apply Veq_nth. intros. do 2 rewrite Vbuild_nth. apply eq_proj.
    simpl. trivial.
  Qed.
    
  Lemma CompPermutationId2 : forall N (pi : Permutation N),
    ComposePerm pi (Perm_Id N) = pi.
  Proof.
    intros. apply eq_proj_perm. simpl. apply injective_projections.
    simpl. apply Veq_nth. intros. do 2 rewrite Vbuild_nth. apply eq_proj.
    simpl. trivial. apply Veq_nth. intros. do 2 rewrite Vbuild_nth. apply eq_proj.
    simpl. trivial.
  Qed.

  Lemma CompPermutationInv : forall N (pi : Permutation N),
    ComposePerm (InvPermutation pi) pi = Perm_Id N.
  Proof.
    intros. apply eq_proj_perm. destruct pi. simpl. apply injective_projections.
    simpl. apply Veq_nth. intros. do 2 rewrite Vbuild_nth. destruct (a i ip).
    rewrite H0. trivial. simpl. apply Veq_nth. intros. do 2 rewrite Vbuild_nth. 
    destruct (a i ip). rewrite H0. trivial. 
  Qed.
    
  Lemma CompPermutationInv2 : forall N (pi : Permutation N),
    ComposePerm pi (InvPermutation pi) = Perm_Id N.
  Proof.
    intros. apply eq_proj_perm. destruct pi. simpl. apply injective_projections.
    simpl. apply Veq_nth. intros. do 2 rewrite Vbuild_nth. destruct (a i ip).
    rewrite H. trivial. simpl. apply Veq_nth. intros. do 2 rewrite Vbuild_nth. 
    destruct (a i ip). rewrite H. trivial. 
  Qed.

  Lemma ComposePermCorrect : forall N (A : Type)(a : vector A N)(p pi : Permutation N),
    Permute (Permute a pi) p = Permute a (ComposePerm pi p).
  Proof.
    intros. apply Veq_nth. intros. do 4 rewrite Vbuild_nth. trivial.
  Qed.

  Lemma ComposePermCorrectInv : forall N (A : Type)(a : vector A N)(p pi : Permutation N),
    PermuteInv (PermuteInv a pi) p = PermuteInv a (ComposePerm p pi).
  Proof.
    intros. apply Veq_nth. intros. do 4 rewrite Vbuild_nth. trivial.
  Qed.  

  Lemma ComposePermAss : forall N (a b c : Permutation N),
  ComposePerm a (ComposePerm b c) = ComposePerm (ComposePerm a b) c.
  Proof.
    intros. apply eq_proj_perm. destruct a, b, c. simpl. rewrite <- ComposePermCorrect.
    rewrite ComposePermCorrectInv. trivial.
  Qed.

  Lemma Vapp_Vmap2 :
    forall (A B C : Type)(f : A -> B -> C)(n m : nat)
    (a : vector A n)(b : vector A m)(c : vector B n)
    (d : vector B m),
    Vmap2 f (Vapp a b) (Vapp c d) = Vapp (Vmap2 f a c)
      (Vmap2 f b d).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2.
    case_eq (le_gt_dec n i). intros. 
    do 3 rewrite Vnth_app. rewrite H. rewrite Vnth_map2. trivial.
    intros. do 3 rewrite Vnth_app. rewrite H. 
    rewrite Vnth_map2. trivial.
  Qed.

  Lemma Vcons_Vadd : forall (A : Type) n (a : vector A n)(b c : A),
    Vcons b (Vadd a c) = Vadd (Vcons b a) c.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    rewrite Vnth_add. destruct (Nat.eq_dec (i - 1) n); trivial. trivial.
  Qed.

  Lemma Vadd_eq_elim_gen : forall (A : Type) n a (b : vector A n)
      (c : vector A (S n)), 
      Vadd b a = c <-> a = VlastS c /\ b = Vremove_last c.
  Proof.
    split. intros. split. rewrite <- H. cbn. rewrite VlastS_add. trivial.
    rewrite <- H. rewrite Vremove_last_add. trivial.
    intros. destruct H. rewrite H0. rewrite H. rewrite <- VSn_addS. trivial.
  Qed.

  Lemma Vcons_eq_elim_gen : forall (A : Type) n a (b : vector A n)
      (c : vector A (S n)), 
      Vcons a b = c <-> a = Vhead c /\ b = Vtail c.
  Proof.
    split. intros. split. rewrite <- H. rewrite Vhead_cons. trivial.
    rewrite <- H. rewrite Vtail_cons. trivial.
    intros. destruct H. rewrite H0. rewrite H. rewrite <- VSn_eq. trivial.
  Qed.

  Lemma Veq_elim_gen : forall (A : Type) n (a b : vector A (S n)),
    a = b <-> Vhead a = Vhead b /\ Vtail a = Vtail b.
  Proof.
    split. intros. rewrite H; split; trivial.
    intros. destruct H. rewrite (VSn_eq a). rewrite (VSn_eq b).
    rewrite H. rewrite H0. trivial. 
  Qed.

  Lemma Veq_elim_gen2 : forall (A : Type) n (a b : vector A (S n)),
    a = b <-> VlastS a = VlastS b /\ Vremove_last a = Vremove_last b.
  Proof.
    split. intros. rewrite H; split; trivial.
    intros. destruct H. rewrite (VSn_addS a). rewrite (VSn_addS b).
    rewrite H. rewrite H0. trivial. 
  Qed.


  Lemma bVexists_eq : forall A n (P : A -> bool)(v : vector A n),
    bVexists P v = true <-> exists i (ip : i < n), P (Vnth v ip) = true.
  Proof.
    intros.  induction v. split; intros. simpl in H. discriminate.
    elim H. intros.  elim H0. intros. lia.
    split; intros. simpl in H. apply orb_true_iff in H. destruct H. 
    exists 0. exists (lt_0_Sn n). rewrite Vnth_cons. destruct (lt_ge_dec 0 0).
    lia. trivial. apply IHv in H. elim H. intros. elim H0. intros.
    exists (S x). exists (lt_n_S x0). rewrite Vnth_cons. 
    destruct (lt_ge_dec 0 (S x)). rewrite <- H1. apply f_equal. apply Vnth_eq.
    lia. lia. elim H. intros. elim H0. intros. simpl. apply orb_true_iff.
    destruct x. left. rewrite <- H1. apply f_equal. rewrite Vnth_cons.
    destruct (lt_ge_dec 0 0). lia. trivial. right. apply IHv. exists x.
    exists (lt_S_n x0). rewrite <- H1. apply f_equal. rewrite Vnth_cons.
    destruct (lt_ge_dec 0 (S x)). apply Vnth_eq. lia. lia.
  Qed.

  Lemma Vremove_front : forall n i (ip : i < n), 0+i <= n.
  Proof.
    intros. lia.
  Qed.
  
  Lemma Vremove_back : forall n i (ip : i < n), 
    (S i)+(n - (S i)) <= n.
  Proof.
    intros. lia.
  Qed.

  Lemma Vremove_cast : forall n i (ip : i < (S n)), i + (S n - S i) = n.
  Proof.
    intros. lia.
  Qed.

  Definition Vremove A n (v : vector A (S n)) i (ip : i < (S n)) : vector A n :=   
    Vcast (Vapp (Vsub v (Vremove_front ip)) (Vsub v (Vremove_back ip))) 
      (Vremove_cast ip).

  Lemma Vremove_intro : forall i n (ip : i < (S n)) A (a b : vector A (S n)),
    a = b -> Vremove a ip = Vremove b ip.
  Proof.
    intros. rewrite H. trivial.
  Qed.

  Lemma Vremove_correct_sub1 : forall (i j : nat), nat. 
  Proof.
    intros. destruct (lt_ge_dec i j). apply i. apply (Nat.pred i).
  Defined.

  Lemma Vremove_correct_sub2 : forall n (i j : nat) (ip : i < S n)
    (jp : j < S n), 
    i <> j ->
    Vremove_correct_sub1 i j < n.
  Proof.
    intros. unfold Vremove_correct_sub1. destruct (lt_ge_dec i j). lia. lia.
  Qed.

  Lemma Vremove_corr : forall A n (v : vector A (S n)) i (ip : i < S n) j
    (jp : j < S n)(h : i <> j),
    Vnth v ip = Vnth (Vremove v jp) (Vremove_correct_sub2 ip jp h).
  Proof.
    intros. rewrite Vnth_cast. rewrite Vnth_app. 
    destruct (le_gt_dec j (Vremove_correct_sub1 i j)). 
    + rewrite Vnth_sub. apply Vnth_eq. unfold Vremove_correct_sub1 in *.
    destruct (lt_ge_dec i j). lia. lia.
    + rewrite Vnth_sub. apply Vnth_eq. unfold Vremove_correct_sub1 in *.
    destruct (lt_ge_dec i j). lia. lia.
  Qed.

  Lemma Vremove_correct_left : forall A n (v : vector A (S n)) i (ip : i < (S n)) j
     (jp : j < n),
     j < i ->
    Vnth (Vremove v ip) jp = Vnth v (le_S jp).
  Proof.
    intros. rewrite Vnth_cast. rewrite Vnth_app. destruct (le_gt_dec i j).
    lia. rewrite Vnth_sub. apply Vnth_eq. trivial.
  Qed.

  Lemma Vremove_correct_right : forall A n (v : vector A (S n)) i (ip : i < (S n)) j
     (jp : j < n),
     i <= j ->
    Vnth (Vremove v ip) jp = Vnth v (lt_n_S jp).
  Proof.
    intros. rewrite Vnth_cast. rewrite Vnth_app. destruct (le_gt_dec i j).
    rewrite Vnth_sub. apply Vnth_eq. lia. lia.
  Qed.

  Lemma Vremove_replace_const : forall i j n (ip : i < S n)(jp : j< S n) A 
    (a b : A)(ip' : i < n),
    i < j ->
    Vremove (Vreplace (Vconst a (S n)) ip b) jp = Vreplace (Vconst a n) ip' b.
  Proof.
    intros. apply Veq_nth. intros. destruct (le_lt_dec j i0). 
    rewrite Vremove_correct_right. trivial. destruct (Nat.eq_dec i (S i0)). lia.
    rewrite Vnth_replace_neq. lia. rewrite Vnth_replace_neq. lia.
    do 2 rewrite Vnth_const. trivial. rewrite Vremove_correct_left. trivial.
    destruct (Nat.eq_dec i i0). subst. do 2 rewrite Vnth_replace. trivial. 
    rewrite Vnth_replace_neq. lia. rewrite Vnth_replace_neq. lia. 
    do 2 rewrite Vnth_const. trivial.
  Qed.

  Lemma Vremove_replace_const2 : forall i j n (ip : S i < S n)(jp : j< S n) A 
    (a b : A),
    j < S i ->
  Vremove (Vreplace (Vconst a (S n)) ip b) jp = 
    Vreplace (Vconst a n) (lt_S_n ip) b.
  Proof.
    intros. apply Veq_nth. intros. destruct (le_lt_dec j i0). 
    rewrite Vremove_correct_right. trivial. destruct (Nat.eq_dec i i0). subst.
    rewrite Vnth_replace. rewrite Vnth_replace.  trivial. 
    rewrite Vnth_replace_neq. lia. rewrite Vnth_replace_neq. lia.
    do 2 rewrite Vnth_const. trivial.
    rewrite Vremove_correct_left. trivial.
    destruct (Nat.eq_dec i i0). subst. lia.
    rewrite Vnth_replace_neq. lia. rewrite Vnth_replace_neq. lia. 
    do 2 rewrite Vnth_const. trivial.
  Qed.

  Lemma Vremove_tail : forall A n (v : vector A (S n))(ip : 0 < (S n)) ,
    Vremove v ip = Vtail v.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_cast. rewrite Vnth_app. 
    destruct (le_gt_dec 0 i). rewrite Vnth_sub. rewrite Vnth_tail.
    apply Vnth_eq. lia. lia.
  Qed.

  Lemma Vremove_head: forall A n (v : vector A (S (S n))) i (ip : S i < S (S n)) ,
    Vhead (Vremove v ip) = Vhead v.
  Proof.
    intros. do 2 rewrite Vhead_nth. intros. rewrite Vnth_cast. rewrite Vnth_app. 
    destruct (le_gt_dec (S i) 0). rewrite Vnth_sub. apply Vnth_eq. lia. 
    rewrite Vnth_sub. apply Vnth_eq. lia. 
  Qed.

  Lemma Vremove_cons : forall A n (v : vector A (S n)) a i (ip : i < (S n)) ,
    Vremove (Vcons a v) (lt_n_S ip) = Vcons a (Vremove v ip).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_cast. rewrite Vnth_app. 
    destruct (le_gt_dec (S i) i0). rewrite Vnth_sub. do 2 rewrite Vnth_cons.
    destruct (lt_ge_dec 0 (S (S i) + (i0 - S i))). destruct (lt_ge_dec 0 i0).
    rewrite Vremove_correct_right. lia. apply Vnth_eq. lia. lia.
    destruct (lt_ge_dec 0 i0). lia. trivial. rewrite Vnth_sub.
    do 2 rewrite Vnth_cons. simpl. destruct (lt_ge_dec 0 i0).
    rewrite Vremove_correct_left. lia. apply Vnth_eq. lia. trivial.
  Qed.

  Lemma Vfold_left_Vremove : forall (A : Type)(f : A -> A -> A)
    (n : nat)(v : vector A (S n))(acc : A) i (ip : i < S n),
    (forall a b c, f (f a b) c = f a (f b c)) ->
    (forall a b, f a b = f b a) ->
    Vfold_left f acc v = f (Vnth v ip) (Vfold_left f acc (Vremove v ip)).
  Proof.
    intros A f n v. induction n. intros. assert (i = 0). lia. subst. 
    rewrite (Vector_0_is_nil (Vremove v ip)). rewrite (VSn_eq v).
    rewrite (Vector_0_is_nil (Vtail v)). cbn. rewrite H0. trivial.
    intros. destruct i. rewrite <- Vnth0Head. rewrite Vremove_tail.
    rewrite <- Vfold_left_Vcons; trivial. rewrite <- VSn_eq. trivial. 
    rewrite (VSn_eq v). rewrite Vfold_left_Vcons; trivial.
    rewrite (IHn (Vtail v) acc i (lt_S_n ip)); trivial.
     assert (forall a b c d e, b = d -> f a c = e -> f a (f b c) = f d e).
    intros. rewrite H0. rewrite H. rewrite H1. apply f_equal. rewrite H0. trivial.
     apply H1. rewrite Vnth_cons. destruct (lt_ge_dec 0 (S i)).
    apply Vnth_eq. trivial. lia. lia. simpl. rewrite <- Vfold_left_Vcons; trivial.
    rewrite <- Vremove_cons. apply f_equal. apply f_equal. apply le_unique.
  Qed.

  
  Lemma Vinsert_front : forall n i (ip : i < S n), 0+i <= n.
  Proof.
    intros. lia.
  Qed.
  
  Lemma Vinsert_back : forall n i (ip : i < S n), 
    i+(n - i) <= n.
  Proof.
    intros. lia.
  Qed.

  Lemma Vinsert_cast : forall n i (ip : i < (S n)), i + S (S n - S i) = S n.
  Proof.
    intros. lia.
  Qed.

  Definition Vinsert A a n (v : vector A n) i (ip : i < (S n)) : vector A (S n) := 
    Vcast (Vapp 
      (Vsub v (Vinsert_front ip))
      (Vcons a (Vsub v (Vinsert_back ip)))) 
    (Vinsert_cast ip).

  Lemma Vremove_correct : forall A n (v : vector A (S n)) i (ip : i < (S n)),
    v = Vinsert (Vnth v ip) (Vremove v ip) ip.
   Proof. 
    intros. unfold Vinsert, Vremove. apply Veq_nth. intros. rewrite Vnth_cast.
    rewrite Vnth_app. destruct (le_gt_dec i i0). rewrite Vnth_cons. 
    destruct (lt_ge_dec 0 (i0 - i)). rewrite Vnth_sub. rewrite Vnth_cast.
    rewrite Vnth_app. destruct (le_gt_dec i (i + (i0 - i - 1))). rewrite Vnth_sub.
    apply Vnth_eq. lia. lia. apply Vnth_eq. lia. rewrite Vnth_sub. rewrite Vnth_cast.
    rewrite Vnth_app. destruct (le_gt_dec i (0 + i0)). lia. rewrite Vnth_sub.
    apply Vnth_eq. lia.
   Qed.

  Lemma Vinsert_correct : forall A (a : A) n (v : vector A n) i (ip : i < (S n)),
    Vnth (Vinsert a v ip) ip = a.
   Proof. 
    intros. unfold Vinsert. rewrite Vnth_cast.
    rewrite Vnth_app. destruct (le_gt_dec i i). rewrite Vnth_cons. 
    destruct (lt_ge_dec 0 (i - i)). lia. trivial. lia.
   Qed.

  Definition VatMostOne A (f : A -> bool) n (v : vector A n): Prop :=
    Vfold_left Nat.add 0%nat (Vmap (fun b => if (f b) then 1 else 0) v) <= 1.
   
  Definition VatMostOne_tail : forall A (f : A -> bool) n (v : vector A (S n)),
    VatMostOne f v -> VatMostOne f (Vtail v).
  Proof.
    intros. simpl in H. rewrite (VSn_eq v) in H. unfold VatMostOne in *.
    rewrite Vcons_map in H. rewrite Vfold_left_Vcons in H; intros. lia. lia. 
    lia.
  Qed.

  Definition VatMostOne_remove : forall A (f : A -> bool) n (v : vector A (S n)),
    VatMostOne f v -> VatMostOne f (Vremove_last v).
  Proof.
    intros. rewrite (VSn_addS v) in H. unfold VatMostOne in *.
    rewrite Vadd_map in H. rewrite Vfold_add in H; intros. lia. lia.
    lia.
  Qed.

  Definition Vbuild_Vnth : forall A n (v : vector A n),
    v = Vbuild (fun j (jp : j < n) =>  Vnth v jp).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth. trivial.
  Qed.

  Fixpoint Vforall3 A B C n (f : A -> B -> C -> Prop) :
      vector A n -> vector B n -> vector C n -> Prop :=
    match n with
      | 0 => fun _ => fun _ => fun _ => true
      | S a => fun x => fun y => fun z => 
          f (Vhead x) (Vhead y) (Vhead z) /\
          Vforall3 f (Vtail x) (Vtail y) (Vtail z)
    end.

  Lemma Vforall3_elim_nth : forall n i 
    (ip : i < n)(A B C : Type)(v1 : vector A n) (v2 : vector B n)
    (v3 : vector C n) (R : A -> B -> C -> Prop), 
   Vforall3 R v1 v2 v3 -> R (Vnth v1 ip) (Vnth v2 ip) (Vnth v3 ip).
  Proof.
    induction n; intros. absurd (i<0); lia.
    rewrite (VSn_eq v1) in H. rewrite (VSn_eq v2) in H.
    rewrite (VSn_eq v3) in H. cbn in H. destruct H.
    destruct i. do 3 rewrite <- Vnth0Head. trivial.
    do 3 rewrite <- Vnth_tail_lt_S_n.
    apply (IHn i (lt_S_n ip) A B C (Vtail v1) (Vtail v2) (Vtail v3) R); trivial.
  Qed.

  Lemma Vforall3_elim_head : forall n (A B C : Type)(v1 : vector A (S n)) 
    (v2 : vector B (S n))(v3 : vector C (S n)) (R : A -> B -> C -> Prop), 
   Vforall3 R v1 v2 v3 -> R (Vhead v1) (Vhead v2) (Vhead v3).
  Proof.
    intros. do 3 rewrite Vhead_nth. apply Vforall3_elim_nth. trivial.
  Qed.

  Lemma Vforall3_nth_intro : forall n (A B C : Type)(v1 : vector A n)
      (v2 : vector B n)(v3 : vector C n)(R : A -> B -> C -> Prop),
    (forall i (ip : i < n), R (Vnth v1 ip) (Vnth v2 ip) (Vnth v3 ip)) ->
       Vforall3 R v1 v2 v3.
  Proof.
    induction v1; intros. VOtac. simpl. auto.
    revert H. VSntac v2. VSntac v3. intro. cbn. 
    split. apply (H1 0 (lt_O_Sn _)). unfold bVforall3 in IHv1.
    apply IHv1. intros. assert (S i< S n). lia.
    pose (H1 (S i) H2). simpl in r. assert (ip = lt_S_n H2).
    apply NatUtil.lt_unique. rewrite H3. apply r.
  Qed.

  Lemma VecToMatSub : forall N N' i (ip : i < N'),
    N*i+N<= N*N'.
  Proof.
    intros. induction N. lia. lia.
  Qed.

 Definition VecToMat A (N N' : nat) (v : vector A (N*N')) : vector (vector A N) N' :=
  (Vbuild (fun i (ip : i < N') => 
      Vsub v (VecToMatSub N ip))).

  Lemma div_modulo_sub : forall (b a c d : nat),
    a >= d ->
    (Nat.divmod b a c d).1 + a * (Nat.divmod b a c d).1 + 
      (a - (Nat.divmod b a c d).2) = b+c+(a*c)+(a-d).
  Proof.
    induction b. intros. cbn. lia.
    intros. simpl. destruct d. rewrite IHb. lia. lia. rewrite IHb. lia.
    lia. 
  Qed.

  Lemma div_modulo : forall (b a  : nat),
    (S a) * (b/(S a)) + b mod (S a) = b.
  Proof.
   unfold Nat.div, Nat.modulo. cbn. intros. rewrite div_modulo_sub. lia. lia.
  Qed.

  Lemma VecToMatSub2_sub : forall a b c,
      a < b <-> a*(S c) < b*(S c).
  Proof.
    intros. assert (forall a b c, a < b -> a*(S c) < b*(S c)). intros. 
    induction c0. lia. lia. split; intros. 
    + apply H; auto.
    + destruct b. lia. induction c. lia. apply IHc. apply H. lia.
  Qed.

  Lemma VecToMatSub2 : forall N N' i (ip : i < N*N'),
    i/N < N'.
  Proof.
    intros. destruct N. lia. apply (VecToMatSub2_sub (i/ S N) N' N).
    assert (i / S N * S N  <= i). pose (div_modulo i N). lia.
    apply (Nat.le_lt_trans H). lia.
  Qed.

  Lemma VecToMatSub3 : forall N N' i (ip : i < N*N'),
    i mod N < N.
  Proof.
    intros. unfold Nat.modulo. induction N. assert False. lia. contradiction.
    destruct N. cbn. lia. lia.
  Qed.

 Definition MatToVec A (N N' : nat)(v : vector (vector A N) N') : vector A (N*N') :=
    Vbuild (fun i (ip : i < N * N') => 
      Vnth (Vnth v (VecToMatSub2 N N' ip)) (VecToMatSub3 N N' ip)).

 Lemma MatToVec_VecToMat : forall A (N N' : nat) (v : vector A (N*N')),
    MatToVec (VecToMat N N' v) = v.
  Proof.
    intros. apply Veq_nth. intros. do 2 rewrite Vbuild_nth. rewrite Vnth_sub.
    apply Vnth_eq. destruct N. assert False. lia. contradiction. apply div_modulo.
  Qed.

  Lemma VecToMat_MatToVec : forall A (N N' : nat) (v : vector (vector A N) N'),
    VecToMat N N' (MatToVec v) = v.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth. apply Veq_nth. intros.
    intros. rewrite Vnth_sub. destruct N. assert False. lia. contradiction.
    rewrite Vbuild_nth. apply Veq_nth3. symmetry. apply (Nat.mod_unique 
    (S N * i + i0) (S N) i); trivial. apply Vnth_eq. symmetry.
    apply (Nat.div_unique (S N * i + i0) (S N) i i0). lia. lia.
  Qed.

  Lemma VecToMat_eq : forall A (N N' : nat)(v : vector (vector A N) N') 
      (v' : vector A (N*N')),
    MatToVec v = v' <-> v = VecToMat N N' v'.
  Proof.
    intros; split; intros. 
    + rewrite <- H. rewrite VecToMat_MatToVec. trivial.
    + rewrite H. rewrite MatToVec_VecToMat. trivial.
  Qed.

  Lemma VecToMatSubTail : forall N N',
    N+N*N'<= N*S N'.
  Proof.
    intros. induction N. lia. lia.
  Qed.
  
 Lemma VecToMatTail : forall A N N' (v : vector A (N*(S N'))),
    Vtail (VecToMat N (S N') v) = 
      VecToMat N N' (Vsub v (VecToMatSubTail N N')).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_tail. do 2 rewrite Vbuild_nth.
    apply Veq_nth. intros. do 3 rewrite Vnth_sub. apply Vnth_eq. lia. 
  Qed.

  Lemma VecToMatInd : forall A n n' (v : vector A (n*(S n'))),
    (VecToMat n (S n') v) = Vcons (Vsub v (VecToMatSub n (lt_0_Sn n')))
       (VecToMat n n' (Vsub v (VecToMatSubTail n n'))).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    do 2 rewrite Vbuild_nth. apply Veq_nth. intros. do 3 rewrite Vnth_sub.
    apply Vnth_eq. assert (forall a b c, a + b + c = a + (b + c)). lia.
    rewrite <- H. apply f_equal2; auto. clear v. clear ip0. induction n. 
    lia. lia. rewrite Vbuild_nth. assert (i = 0). lia. subst.
    apply f_equal. apply le_unique.
  Qed.

  Lemma Vfold_left_Vconst_acc : forall (A : Type)(f : A -> A -> A) n (acc : A),
    (forall a, f acc a = a) ->
    Vfold_left f acc (Vconst acc n) = acc.
  Proof.
    intros. induction n.  cbn. trivial. simpl. rewrite H. apply IHn.
  Qed. 

  Lemma Vfold_left_map2_VecToMat :  forall (A : Type)(f : A -> A -> A)
    (n n' : nat)(v : vector A (n*n'))(acc : A),
    (forall a b c, f (f a b) c = f a (f b c)) ->
    (forall a b, f a b = f b a) ->
    (forall a, f acc a = a) ->
    Vfold_left f acc 
      (Vfold_left (fun a b => Vmap2 f a b) (Vconst acc n) (VecToMat n n' v)) =
    Vfold_left f acc v.
  Proof.
    intros. induction n'. cbn. symmetry. rewrite Vfold_left_nil_gen. lia.
    symmetry. apply Vfold_left_Vconst_acc; auto.
    (* Begin inductive step *)
    rewrite VecToMatInd. rewrite Vfold_left_Vcons; auto. intros. apply Veq_nth.
    intros. do 4 rewrite Vnth_map2. auto. intros. apply Veq_nth. intros. 
    do 2 rewrite Vnth_map2. auto.
    rewrite Vfold_left_map2; auto. rewrite IHn'. rewrite <- Vfold_left_vapp; auto.
    assert (n+n*n' = n*S n'). lia. apply (Vfold_left_eq_gen H2).
    apply Veq_nth. intros. rewrite Vnth_cast. rewrite Vnth_app. destruct (le_gt_dec n i ).
    rewrite Vnth_sub. apply Vnth_eq. lia. rewrite Vnth_sub. apply Vnth_eq. lia.
  Qed.
    
  Lemma Vfold_left_nest_VecToMat : forall (A B C : Type)(f : A -> A -> A)
    (f' : B -> C -> A)(n n' : nat)(t : vector B (n*n'))(t' : vector C (n*n'))
      (acc : A),
    (forall a b c, f (f a b) c = f a (f b c)) ->
    (forall a b, f a b = f b a) ->
    (forall a, f acc a = a) ->
    Vfold_left f acc (Vmap2 (fun x y => Vfold_left f acc (Vmap2 f' x y)) 
        (VecToMat n n' t)(VecToMat n n' t')) = Vfold_left f acc (Vmap2 f' t t').
  Proof.
    intros. induction n'. cbn. symmetry. rewrite Vfold_left_nil_gen. lia.
    symmetry. trivial.
    (* Begin inductive step *)
    do 2 rewrite VecToMatInd. rewrite Vcons_map2. rewrite Vfold_left_Vcons; auto.
    rewrite IHn'. rewrite <- Vfold_left_vapp; auto. assert (n+n*n' = n*S n'). lia. 
    apply (Vfold_left_eq_gen H2). apply Veq_nth. intros. rewrite Vnth_cast. 
    rewrite Vnth_app. destruct (le_gt_dec n i ). 
    + do 2 rewrite Vnth_map2. do 2 rewrite Vnth_sub. apply f_equal2.
    ++ apply Vnth_eq. lia. 
    ++ apply Vnth_eq. lia. 
    + do 2 rewrite Vnth_map2. do 2 rewrite Vnth_sub. apply f_equal2.
    ++ apply Vnth_eq. lia. 
    ++ apply Vnth_eq. lia. 
  Qed.

  Fixpoint gen_comb A (l : list A) (k : nat) :=
      match k with
      | 0 => List.cons nil nil
      | S k' => 
        match l with
        | nil => nil
        | h :: t => 
          List.map (fun u => List.cons h u) (gen_comb t k') ++
          gen_comb t k
        end
      end.

  Lemma gen_comb_0 : forall A (l : list A),
    gen_comb l 0 = List.cons nil nil. 
  Proof.
    intros. unfold gen_comb. induction l; trivial.
  Qed.

  Lemma gen_comb_nil : forall A l,
    gen_comb (@List.nil A) (S l) = List.nil.
  Proof.
    intros. unfold gen_comb. auto. 
  Qed.

  Lemma gen_comb_1 : forall A (l : list A),
    length l = 1 ->
    gen_comb l 1 = List.cons l nil.
  Proof.
    intros. unfold gen_comb. destruct l. assert (length (@Datatypes.nil A) = 0).
    auto. rewrite H in H0. lia. assert (l = nil). destruct l. trivial.
    assert (length (a :: a0 :: l) > 1). cbn. lia. lia.
    rewrite H0. cbn. trivial.
  Qed. 

  Lemma gen_comb_ind : forall A (l : list A) k b,
    gen_comb (List.cons b l) (S k)  =
    List.map (fun u => List.cons b u) (gen_comb l k) ++ gen_comb l (S k).
  Proof.
    intros. cbn. trivial.
  Qed.

  Definition gen_comb_vec A n k (l : vector A n) :=
     vec_of_list (gen_comb (list_of_vec l) k).

  Lemma gen_comb_len_eq : forall A n (v : vector A (S n)) k,
    length (gen_comb (list_of_vec (Vtail v)) k) +
     length (gen_comb (list_of_vec (Vtail v)) (S k)) =
    length (gen_comb (list_of_vec v) (S k)).
  Proof.
    intros. rewrite (VSn_eq v). rewrite Vtail_cons.
    rewrite gen_comb_ind. rewrite app_length. apply f_equal2.
    auto. rewrite map_length. trivial. trivial. 
  Qed.

  Lemma gen_comb_vec_cons_len : forall A n (v : vector A (S n)) k,
    length (gen_comb (list_of_vec (Vcons (Vhead v) (Vtail v))) (S k)) = 
    length (gen_comb (list_of_vec v) (S k)).
  Proof.
    intros. rewrite <- VSn_eq. trivial.
  Qed.

  Lemma gen_comb_vec_cons : forall A n (v : vector A (S n)) k,
    gen_comb_vec (S k) v = Vcast (gen_comb_vec (S k) (Vcons (Vhead v) (Vtail v)))
    (gen_comb_vec_cons_len v k).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_cast. 
    do 2 rewrite (@Vnth_vec_of_list _ _ (List.cons (Vhead v) List.nil)).
    clear ip. rewrite <- VSn_eq. trivial.
  Qed.

  Lemma gen_comb_vec_ind : forall A n (v : vector A (S n)) k,
    gen_comb_vec (S k) v = Vcast (Vapp 
      (Vmap [eta List.cons (Vhead v)] (gen_comb_vec k (Vtail v))) 
      (gen_comb_vec (S k) (Vtail v))) (gen_comb_len_eq v k).
  Proof.
    intros. rewrite gen_comb_vec_cons. apply Veq_nth. intros.
    rewrite Vnth_cast. rewrite (@Vnth_vec_of_list _ _ (List.cons (Vhead v) List.nil)).
    rewrite gen_comb_ind. rewrite Vnth_cast. rewrite Vnth_app.
    destruct (le_gt_dec (length (gen_comb (list_of_vec (Vtail v)) k)) i).
    + rewrite (@Vnth_vec_of_list _ _ (List.cons (Vhead v) List.nil)).
    rewrite app_nth2. rewrite map_length. unfold ge. trivial. 
    rewrite map_length. trivial.
    + rewrite Vnth_map. rewrite (@Vnth_vec_of_list _ _ (List.cons (Vhead v) List.nil)).
    rewrite app_nth1. rewrite map_length. unfold gt in *. trivial. 
    rewrite map_nth. apply f_equal. apply nth_indep. trivial.
  Qed.

  Lemma list_fold_left_const : forall A (l : list A) (f : A->A->A) b c,
    (forall a b c, f (f a b) c = f a (f b c)) ->
    (forall a b, f a b = f b a) ->
    List.fold_left f (b :: l) c = f (List.fold_left f l c) b.
  Proof.
    induction l. intros. cbn. trivial.
    intros. simpl. rewrite <- IHl. simpl. trivial. rewrite (H c a). rewrite (H0 a b).
    rewrite <- H. trivial. trivial. trivial.
  Qed.

End VectorUtil.
