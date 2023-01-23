Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
From Groups Require Import groups module vectorspace 
    dualvectorspaces matrices matricesF matricesField modulevectorspace.
Require Import List.
Require Import Field.
Require Import cryptoprim.
Require Coq.Classes.RelationClasses.
From Coq Require Import Basics Morphisms Setoid.
From CoLoR Require Import RelDec OrdSemiRing LogicUtil RelExtras EqUtil NatUtil ZUtil SemiRing.
Require Import Coq.Vectors.Vector.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import CoLoR.Util.Vector.VecArith.
Require Import CoLoRmatrix.
Require Import VectorUtil.
Set Implicit Arguments.

Module Type BGSupport (Message Ciphertext Commitment : GroupSig)(Ring : RingSig)
    (Field : FieldSig)(VS2 : VectorSpaceSig Commitment Field)
    (VS1 : VectorSpaceSig Ciphertext Field)
    (MVS : VectorSpaceModuleSameGroup Ciphertext Ring Field VS1)
    (VS3 : VectorSpaceSig Message Field)(Hack : Nat)(M : Nat)
    (enc : EncryptionSchemePlus Message Ciphertext Ring Field VS1 VS3 MVS).
  
  (* N = nm *)
  Let n := S (S (S Hack.N)).      (* n *)
  Let m := S (S M.N).     (* m *)
  Import Field.

  Module Mo := MatricesFieldIns Field.
  Import Mo.
  Import Mo.mat.
  Module MoR := MatricesFIns Ring.
  Module MoC := MatricesG Ciphertext Field VS1 mat.

  (* Make commitment scheme and matrix *)
  Module EPC := ExtendComScheme Commitment Field VS2 mat.
  Import EPC.
  Import EPC.MoM.
  Module PC := BasicComScheme Commitment Field VS2 mat.
  Import PC.

  Module MoM := MatricesG Message Field VS3 mat.

  (* Addational vector lemma *)
  Module ALVS1 := VectorSpaceAddationalLemmas Ciphertext Field VS1.
  Module ALVS2 := VectorSpaceAddationalLemmas Commitment Field VS2.
  Module ALVS3 := VectorSpaceAddationalLemmas Message Field VS3.

  Module ALenc := EncryptionSchemeProp Message Ciphertext Ring Field VS1 MVS enc.
  Import ALenc.
  Module HardProb := HardProblems Commitment Field VS2.
  Import HardProb.

  Module ALR := RingAddationalLemmas Ring.

  Import VS2.
  Import Commitment.

  Lemma moreIsLess : forall a,
    0 < S a.
  Proof.
    intros. lia.
  Qed.

  Lemma lessIsLess : forall j i N,
    j < S i -> i < S N ->
    j < S N.
  Proof.
    intros. lia.
  Qed.

  Lemma lessIsLessShift : forall j i N,
    j < S i -> i < S N ->
    j+(N - i) < S N.
  Proof.
    intros. lia.
  Qed.

  Lemma leS : forall i j,
    i < j -> i < S j.
  Proof.
   intros. lia.
  Qed.

  (* At the momment I have written this to only work for square matrices *)
  Definition ProdOfDiagonals (T : Type)(a : T)(f : T->T->T) N
     (A : vector (vector T (S N)) (S N)) : vector T (S N + N) :=
    let left := Vbuild (fun i (ip : i < S N) => (* For i = 0 to N *)
      Vfold_left f a (Vbuild (fun j (jp : j < S i) => (* For j = 0 to i *)
        (* let jpc := lessIsLess jp ip in (* x = j *)
        let jpt := lessIsLessShift jp ip in (* y = h+(N-i) *) *)
        Vnth (Vnth A (lessIsLess jp ip)) (lessIsLessShift jp ip) (* Get A x y *)
      ))
    ) in
    let right := Vbuild (fun i (ip : i < N) => (* For i = 0 to N-1 *)
      Vfold_left f a (Vbuild (fun j (jp : j < S i) =>  (* For j = 0 to i *)
        (* let jpc := lessIsLessShift jp (leS ip) in (* x = j+(N-i) *)
        let jpt := lessIsLess jp (leS ip) in (* y = j *) *)
        Vnth (Vnth A (lessIsLessShift jp (leS ip))) (lessIsLess jp (leS ip))
      ))
    ) in
    Vapp left (rev right).

  (* Inital lemmas *)
  Lemma TheSMdiag : forall (T : Type)(a : T)(f : T->T->T) N 
     (A : vector (vector T (S (S N))) (S (S N))),
    Vhead (Vbreak (ProdOfDiagonals a f A)).2 = 
      Vfold_left f a (Vbuild (fun i (ip : i < (S N)) => 
        Vnth (Vremove_last (Vnth (Vtail A) ip)) ip)).
  Proof.
    intros. rewrite Vhead_nth. rewrite Vnth_vbreak_2. lia. intros. rewrite Vnth_app.
    destruct (le_gt_dec (S (S N)) (0 + S (S N))). rewrite Vbuild_nth. 
    rewrite Vbuild_nth. assert (S ((S N) - (0 + S (S N) - S (S N)) - 1) = S N).    
    lia. apply (Vfold_left_eq_cast H). apply Veq_nth. intros. rewrite Vnth_cast.
    do 2 rewrite Vbuild_nth. rewrite Vnth_remove_last. apply Veq_nth3. trivial.
    rewrite Vnth_tail. apply Vnth_eq. lia. assert False. lia. contradiction.
  Qed.

  Definition ProdOfDiagonalsF := ProdOfDiagonals 0 Fadd.

  Definition ProdOfDiagonalsVF (N : nat) := ProdOfDiagonals (VF_zero N) (VF_add (n:=N)).
  Definition ProdOfDiagonalsG := ProdOfDiagonals Gone Gdot.

  Lemma ProdOfDiagonalsF_ProdOfDiagonalsVF: forall gen l (lp : l < n),
  Vnth (FMatrix.mat_transpose (ProdOfDiagonalsVF
   (Vbuild (fun (i : nat) (ip : i < S m) => Vbuild (
   fun (j : nat) (jp : j < S m) => gen i j ip jp))))) lp  = 
  ProdOfDiagonalsF (Vbuild (fun (i : nat) (ip : i < S m) =>
   Vbuild (fun (j : nat) (jp : j < S m) => Vnth (gen i j ip jp) lp))).
  Proof.
    intros. apply Veq_nth. intros. rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_elem. unfold FMatrix.get_row. do 2 rewrite Vnth_app.
    (* case 1 *)
    destruct (le_gt_dec (S m) i). do 4 rewrite Vbuild_nth. rewrite Vfold_left_VF_add.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_map. do 6 rewrite Vbuild_nth. trivial.
    (* case 2 *)
    do 2 rewrite Vbuild_nth. rewrite Vfold_left_VF_add. apply f_equal. 
    apply Veq_nth. intros. rewrite Vnth_map. do 6 rewrite Vbuild_nth. trivial.
  Qed.

  Lemma SubMatrixRight : forall T (f : T -> T -> F) N (A : vector T (S (S N)))
        (B : vector T (S (S N))),
    Vtail (Vbreak (ProdOfDiagonalsF
     (FMatrix.mat_build (fun i j (ip: i < S (S N))(jp : j < S (S N)) => 
      f (Vnth A ip) (Vnth B jp))))).2  = 
  (Vbreak (ProdOfDiagonalsF (FMatrix.mat_build (fun i j (ip: i < S N)(jp : j < S N) => 
      f (Vnth (Vtail A) ip) (Vnth (Vremove_last B) jp))))).2.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_tail. rewrite Vnth_vbreak_2. lia.
    intros. rewrite Vnth_vbreak_2. lia. intros. do 2 rewrite Vnth_app.
    destruct (le_gt_dec (S (S N)) (S i + S (S N))). destruct (le_gt_dec (S N) (i + S N)).
    do 4 rewrite Vbuild_nth. assert (S (S N - (S i + S (S N) - S (S N)) - 1) = 
    S (N - (i + S N - S N) - 1)). lia. apply (Vfold_left_eq_cast H).
    apply Veq_nth. intros. rewrite Vnth_cast. do 2 rewrite Vbuild_nth.
    do 2 rewrite FMatrix.mat_build_nth. apply f_equal2. rewrite Vnth_tail.
    apply Vnth_eq. lia. rewrite Vnth_remove_last. apply Vnth_eq. lia. 
    assert (False). lia. contradiction.  assert (False). lia. contradiction.
  Qed.

  Lemma FMatrix_mat_build_vcons_tail : forall T (f : T -> T -> F) N 
    (A B : vector T (S N))(a b : T),
    FMatrix.mat_build (fun i j (ip: i < (S N))(jp : j < (S N)) => 
      f (Vnth (Vtail (Vcons a A)) ip) (Vnth (Vremove_last (Vadd B b)) jp))  = 
    FMatrix.mat_build (fun i j (ip: i < S N)(jp : j < S N) => 
      f (Vnth A ip) (Vnth B jp)).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros. 
    do 2 rewrite FMatrix.mat_build_nth. rewrite Vtail_cons.
    rewrite Vremove_last_add. trivial.
  Qed.
  
  Lemma ProdOfDiagonalsHead : forall (T : Type)(a : T)(f : T->T->T) N
      (A : vector (vector T (S N)) (S N)),
    Vhead (ProdOfDiagonals a f A) = f a (Vhead (rev (Vhead A))).
  Proof.
    intros. rewrite Vhead_app. rewrite Vbuild_head. simpl.  apply f_equal.
    rewrite Vhead_nth. apply Veq_nth3.
    lia. apply Vnth_eq. trivial.
  Qed.

  Lemma ProdOfDiagonalsFVhead : forall n n' (a b : VF n)(A B : vector (VF n) n')
    (f : VF n -> VF n -> F),
    Vhead (ProdOfDiagonalsF (FMatrix.mat_build  (fun i j ip jp =>
            f (Vnth (Vcons a A) ip)
              (Vnth (Vadd B b) jp)))) = f a b.
  Proof.
    intros. unfold ProdOfDiagonalsF. rewrite ProdOfDiagonalsHead. 
    rewrite Vhead_mat_build. rewrite Vhead_nth. do 2 rewrite Vbuild_nth.
    rewrite <- rev_Vadd. rewrite Vbuild_nth. rewrite invertPosCancel.
    do 2 rewrite Vnth_cons. destruct (lt_ge_dec 0 0). 
    assert False. lia. contradiction. field; auto.
  Qed.

  Lemma ProdOfDiagonalsOne : forall (T : Type)(a : T)(f : T->T->T)
      (A : vector (vector T 1) 1),
    (forall b : T, f a b = b) ->
    ProdOfDiagonals a f A = Vhead A.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_app. destruct (le_gt_dec 1 i).
    assert False. lia. contradiction. rewrite Vbuild_nth. assert (i=0%nat). lia.
    subst. rewrite Vfold_left_head; auto. rewrite Vbuild_head. apply Veq_nth3. trivial.
    rewrite Vhead_nth. 
    apply Veq_nth3; auto.
  Qed.


  Lemma ProdOfDiagonalsOneF : forall (A : vector (VF 1) 1),
    ProdOfDiagonalsF A = Vhead A.
  Proof.
    intros. apply ProdOfDiagonalsOne. intros. ring; auto.
  Qed.

  (* We assume the main operation is commutive and assocative *)
 Lemma ProdOfDiagonalsSum : forall (T U V : Type)(a : T)(f : T->T->T) N  
    (A : vector U (S N))(B : vector V (S N))(f' : U->V->T),
    (forall b : T, f a b = b) ->
    (forall a0 b c : T, f (f a0 b) c = f a0 (f b c)) -> 
    (forall a0 b : T, f a0 b = f b a0) ->
  Vfold_left f a (ProdOfDiagonals a f (Vbuild (fun i (ip: i < S N) =>
    (Vbuild (fun j (jp : j < S N) => f' (Vnth A ip) (Vnth B jp)))))) = 
    Vfold_left f a (Vmap (fun x => Vfold_left f a x) (Vbuild (fun i (ip: i < S N) =>
    (Vbuild (fun j (jp : j < S N) => f' (Vnth A ip) (Vnth B jp)))))).
  Proof.
    intros. induction N. rewrite ProdOfDiagonalsOne; auto. apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_map. rewrite Vhead_nth. do 3 rewrite Vbuild_nth.
   simpl. rewrite H.  apply f_equal2. 
    apply Vnth_eq. lia. apply Vnth_eq. lia.
   rewrite Vfold_left_induction; auto. rewrite Vhead_map. rewrite Vbuild_head.
  symmetry. rewrite Vfold_left_eq_rev; auto. symmetry. rewrite Vtail_map. 
    (* Dealing with inside *)
    assert (Vfold_left f a
     (Vmap [eta Vfold_left f a] (Vtail (Vbuild (fun (i : nat) (ip : i < S (S N)) =>
      Vbuild (fun (j : nat) (jp : j < S (S N)) => f' (Vnth A ip) (Vnth B jp)))))) =
    Vfold_left f a (Vmap2 f (Vmap (fun x => f' x (Vhead B)) (Vtail A)) (Vmap [eta Vfold_left f a] (Vbuild (fun (i : nat) (ip : i < S N) =>
      Vbuild (fun (j : nat) (jp : j < S N) => f' (Vnth (Vtail A) ip) 
    (Vnth (Vtail B) jp))))))). apply f_equal. apply Veq_nth. intros. rewrite Vnth_map2.
    do 2 rewrite Vnth_map. rewrite Vfold_left_induction; auto. rewrite Vbuild_tail. 
    rewrite Vbuild_nth. rewrite Vbuild_head. apply f_equal2. rewrite Vhead_nth. 
    rewrite Vnth_tail. trivial. rewrite Vnth_map. rewrite Vbuild_tail. apply f_equal.
    rewrite Vbuild_nth. apply Veq_nth. intros. do 2 rewrite Vbuild_nth. 
    do 2 rewrite Vnth_tail. trivial.
    (* Apply Induction hypo *)
    rewrite H2. rewrite Vfold_left_map2; auto.
    rewrite <- IHN. rewrite <- H0. 
    rewrite <- Vfold_left_vapp; auto. assert (forall (c : vector T (S N + N)),
    Vfold_left f a c = Vfold_left f a (Vcons a (Vadd c a))). intros. 
    rewrite VectorUtil.Vfold_left_Vcons; auto. rewrite H. rewrite Vfold_add; auto.
    rewrite H1. rewrite H. trivial.
    rewrite H3. assert (S (S (S N + N)) = Nat.add (S (S N)) (S N)). lia.
    rewrite (Vfold_left_cast_irr H4). rewrite <- Vfold_left_map2; auto.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_app.
    rewrite Vnth_app. destruct (le_gt_dec (S (S N)) i).
    (* case 1 *)
    rewrite Vnth_cast. do 2 rewrite Vbuild_nth. rewrite Vnth_cons.
    destruct (lt_ge_dec 0 i). rewrite Vnth_add. destruct (Nat.eq_dec (i - 1) (S N + N)).
    rewrite Vnth_map. rewrite H1. rewrite H. assert (S (S N - (i - S (S N)) - 1) = 1%nat). lia.
    rewrite (Vfold_left_cast_irr H5). rewrite Vfold_left_head; auto.
    rewrite Vhead_cast. rewrite Vbuild_head. do 2 rewrite Vbuild_nth. apply f_equal2.
    rewrite Vnth_tail. apply Vnth_eq. lia. rewrite Vhead_nth. apply Vnth_eq. trivial.
    rewrite Vfold_left_induction; auto. apply f_equal2. rewrite Vbuild_head.
    do 2 rewrite Vbuild_nth. rewrite Vnth_map. apply f_equal2. rewrite Vnth_tail.
    apply Vnth_eq. lia. rewrite Vhead_nth. apply Vnth_eq. lia.
    rewrite Vnth_app. destruct (le_gt_dec (S N) (i - 1)). do 2 rewrite Vbuild_nth.
    assert (Nat.sub (Nat.sub (S N) (i - S (S N))) 1 = S (N - (i - 1 - S N) - 1)). lia.
    apply (Vfold_left_eq_gen H5). apply Veq_nth. intros. rewrite Vnth_cast.
    rewrite Vnth_tail. do 6 rewrite Vbuild_nth. apply f_equal2. rewrite Vnth_tail.
     apply Vnth_eq. lia. rewrite Vnth_tail. apply Vnth_eq. lia. 
      (* clean up *) assert (False). lia. contradiction. 
                     assert (False). lia. contradiction.
    (* case 2*)
    rewrite Vnth_cast. rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    do 3 rewrite Vbuild_nth. rewrite Vnth_add. destruct (Nat.eq_dec (i - 1) (S N + N)).
    assert (False). lia. contradiction. rewrite Vfold_left_induction; auto. apply f_equal2. 
    rewrite Vbuild_head. do 2 rewrite Vbuild_nth. apply f_equal2. apply Vnth_eq. trivial.
    apply Vnth_eq. lia. rewrite Vnth_app. destruct (le_gt_dec (S N) (i - 1)).
    assert (False). lia. contradiction.
    rewrite Vbuild_nth. assert (i = S (i -1)). lia.
    apply (Vfold_left_eq_gen H5). apply Veq_nth. intros. rewrite Vnth_cast.
    rewrite Vnth_tail. do 6 rewrite Vbuild_nth. do 2 rewrite Vnth_tail.
    apply f_equal2. apply Vnth_eq. lia. apply Vnth_eq. lia.
      (* Head *)
    do 2 rewrite Vbuild_nth. assert (i = 0%nat). lia. subst.
    rewrite Vfold_left_head; auto. rewrite Vbuild_head. do 3 rewrite Vbuild_nth.
    rewrite H1. rewrite H. apply f_equal2. apply Vnth_eq. trivial. apply Vnth_eq. lia.
  Qed.

  Lemma ProdOfDiagonalsIndF : forall n N (a : VF n -> VF n ->F) (A B : vector (VF n) (S (S N)))
        (H : S (S (S N + N)) = Nat.add (S (S N)) (S N)),
    (* The product of the origional matrix *)
    ProdOfDiagonalsF (FMatrix.mat_build (fun i j (ip: i < S (S N))(jp : j < S (S N)) => 
      a (Vnth A ip) (Vnth B jp))) = 
    VF_add 
    (* The smaller matrix *)
    (Vcast (Vadd (Vcons 0 (ProdOfDiagonalsF (FMatrix.mat_build (fun i j (ip: i < S N)(jp : j < S N) => 
      a (Vnth (Vtail A) ip) (Vnth (Vtail B) jp))))) 0) H)
    (* The rest *)
    (Vapp (Vbuild (fun i (ip : i < S (S N)) => a (Vhead A) (Vnth B (lessIsLessShift (moreIsLess i) ip))))
     (Vbuild (fun i (ip : i < S N) => a (Vnth (Vtail A) ip) (Vhead B)))).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vnth_app. 
    destruct (le_gt_dec (S (S N)) i). do 2 rewrite Vbuild_nth.
    (* Spliting on the main matrix - S (S N) <= i *)
    rewrite Vnth_cast. rewrite Vnth_add.  destruct (Nat.eq_dec i (S (S N + N))).
      (* i = S (S N + N) *)
    subst. destruct module_ring. unfold FSemiRingT.Aplus.
    rewrite Radd_0_l. rewrite Vbuild_nth. assert (S (S N - (S (S N + N) - S (S N)) - 1) = 1%nat).
    lia. unfold VF_sum. rewrite (Vfold_left_cast H0). pose VF_sum_1_head.
    unfold VF_sum in e. rewrite e. rewrite Vhead_cast. rewrite Vhead_nth.
    rewrite Vbuild_nth. rewrite FMatrix.mat_build_nth. assert (Nat.sub (S (S N + N)) (S (S N)) = N). 
    lia. apply f_equal2. rewrite Vnth_tail. apply Vnth_eq.  rewrite H1. lia.
    rewrite Vhead_nth. apply Vnth_eq. trivial.
      (*  i <> S (S N + N) *)
    unfold FSemiRingT.Aplus. rewrite Vnth_cons.
    destruct (lt_ge_dec 0 i). rewrite Vnth_app. destruct (le_gt_dec (S N) (i - 1)).
    do 2 rewrite Vbuild_nth. unfold VF_sum. rewrite <- Vfold_left_Vcons_Fadd.
    assert (S (S N - (i - S (S N)) - 1) = S (S (N - (i - 1 - (S N)) - 1))). lia.
    apply (Vfold_left_eq_cast H0). apply Veq_nth. intros. rewrite Vnth_cast. 
    rewrite Vbuild_nth. rewrite Vnth_cons. destruct (lt_ge_dec 0 i0).
    rewrite Vbuild_nth. do 2 rewrite FMatrix.mat_build_nth. apply f_equal2.
    rewrite Vnth_tail. apply Vnth_eq. lia. rewrite Vnth_tail. apply Vnth_eq. lia.
    rewrite FMatrix.mat_build_nth. rewrite Vbuild_nth. apply f_equal2.
    rewrite Vnth_tail. apply Vnth_eq. lia. rewrite Vhead_nth. apply Vnth_eq. lia.
    assert (False). lia. contradiction.
    assert (False). lia. contradiction.
    (* S (S N) > i *)
    do 2 rewrite Vbuild_nth. rewrite Vnth_cast. rewrite Vnth_add.
    destruct (Nat.eq_dec i (S (S N + N))).  assert (False). lia. contradiction.
    rewrite Vnth_cons. destruct (lt_ge_dec 0 i). 
      (* 0 < i *)
    rewrite Vnth_app.
    destruct (le_gt_dec (S N) (i - 1)). assert (False). lia. contradiction.
    rewrite Vbuild_nth. unfold VF_sum. rewrite <- Vfold_left_Vcons_Fadd.
    assert (S i =  S (S (i-1))). lia. apply (Vfold_left_eq_cast H0).
    apply Veq_nth. intros. rewrite Vnth_cast. rewrite Vbuild_nth.
    rewrite Vnth_cons. destruct (lt_ge_dec 0 i0). rewrite Vbuild_nth.
    do 2 rewrite FMatrix.mat_build_nth. apply f_equal2. rewrite Vnth_tail.
    apply Vnth_eq. lia. rewrite Vnth_tail. apply Vnth_eq. lia.
    rewrite FMatrix.mat_build_nth. apply f_equal2. rewrite Vhead_nth. apply Vnth_eq. 
    lia. apply Vnth_eq. lia.
      (* i = 0 *)
    assert (i = 0%nat). lia. subst. pose VF_sum_1_head. unfold VF_sum in e.
    rewrite e. rewrite Vhead_nth.
    rewrite Vbuild_nth. simpl. rewrite FMatrix.mat_build_nth. destruct vs_field.
    destruct F_R. unfold FSemiRingT.Aplus. rewrite Radd_0_l. apply f_equal2.
    rewrite Vhead_nth. apply Vnth_eq. trivial. apply Vnth_eq. trivial.
  Qed.

  Lemma prod_exp : forall (n n' : nat)(a b : vector (VF n) (S n')),
    Vfold_left (VF_add (n:=n)) (VF_zero n)
      (ProdOfDiagonalsVF (Vbuild (fun (i0 : nat) (ip0 : i0 < S n') =>
      Vbuild (fun (j : nat) (jp : j < S n') => VF_mult (Vnth a ip0) (Vnth b jp)))))
     = VF_mult (Vfold_left (VF_add (n:=n)) (VF_zero n) a)
  (Vfold_left (VF_add (n:=n)) (VF_zero n) b).
  Proof.
    assert (forall n a, VF_add (VF_zero n) a = a). intros. rewrite VF_comm. 
    rewrite VF_add_zero. trivial. pose VF_comm. pose VF_add_ass.
    intros. rewrite ProdOfDiagonalsSum; auto. apply VF_sum_dist.
  Qed.

  (* We use the same argument to compute commitment opening *)
  Lemma commitOpen : forall (n m : nat)(e : VF (S m))(T : Type)(f : T->VF n)
    (f' : T->F)(c : VG (S m))(h : G)(hs : VG n)(t : vector T (S m)),
    PairwisePredicate (fun c1 c2 => negb (Fbool_eq c1 c2)) e ->
    bVforall2
       (fun (a' : F) (b' : T) =>
        Gbool_eq (VG_prod (VG_Pexp c (VandermondeCol (S m) a')))
          (EPC h hs (f b') (f' b'))) e t ->
    c = comEPC h hs(FMatrix.mat_mult (VandermondeInv e) (Vmap f t))
          (Vhead (FMatrix.mat_mult [(Vmap f' t)] 
    (FMatrix.mat_transpose (VandermondeInv e)))).
  Proof.
    pose module_abegrp.
    intros. symmetry. rewrite <- VG_MF_exp_row_id. apply invVandermondeLeft in H.
    rewrite <- H.  rewrite <- VG_MF_exp_row_dist.
    apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vbuild_nth.
    (* Time to use the verification equation *)
    assert (VG_MF_exp_row c (Vandermonde e) = comEPC h hs (Vmap f t) (Vmap f' t)).
    apply Veq_nth. intros. apply (bVforall2_elim_nth ip0 e t) in H0.
    apply bool_eq_corr in H0. rewrite Vbuild_nth. rewrite Vnth_map2.
    do 3 rewrite Vnth_map. auto.
    (* Finished *)
    rewrite H1. rewrite Vbuild_nth. unfold VG_Pexp, VG_MF_exp_row.  
    rewrite comEPCDis. unfold VG_prod. 
    rewrite <- EPCMultExt. apply f_equal2. apply Veq_nth. intros.
    rewrite FMatrix.mat_mult_elem. rewrite Vfold_left_VF_add. unfold FMatrix.VA.dot_product.
    rewrite Vfold_left_Fadd_eq. apply f_equal. apply Veq_nth. intros.
    rewrite Vnth_map. do 2 rewrite Vnth_map2. do 4 rewrite Vnth_map. 
    unfold FMatrix.get_row, FSemiRingT.Amult. destruct module_ring.
    apply Rmul_comm.
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq. apply f_equal.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. rewrite FMatrix.mat_transpose_row_col.
    unfold FSemiRingT.Amult, FMatrix.get_row. rewrite Vnth_map. trivial. 
  Qed.

  Lemma commitOpenPC : forall (m : nat)(e : VF (S m))(T : Type)(f : T->F)
    (f' : T->F)(c : VG (S m))(h hs : G)(t : vector T (S m)),
  PairwisePredicate (fun c1 c2 => negb (Fbool_eq c1 c2)) e ->
  bVforall2 (fun (a' : F) (b' : T) => Gbool_eq (VG_prod
   (VG_Pexp c (VandermondeCol (S m) a')))
   (PC h hs (f b') (f' b'))) e t ->
  c = comPC h hs (Vhead (FMatrix.mat_mult [(Vmap f t)] 
    (FMatrix.mat_transpose (VandermondeInv e)))) (Vhead (FMatrix.mat_mult [(Vmap f' t)] 
    (FMatrix.mat_transpose (VandermondeInv e)))).
  Proof.
    pose module_abegrp.
    intros. symmetry. rewrite <- VG_MF_exp_row_id. apply invVandermondeLeft in H.
    rewrite <- H. rewrite <- VG_MF_exp_row_dist.
    apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vbuild_nth.
    (* Time to use the verification equation *)
    assert (VG_MF_exp_row c (Vandermonde e) = comPC h hs (Vmap f t) (Vmap f' t)).
    apply Veq_nth. intros. apply (bVforall2_elim_nth ip0 e t) in H0.
    apply bool_eq_corr in H0. rewrite Vbuild_nth. rewrite Vnth_map2.
    do 3 rewrite Vnth_map. auto.
    (* Finished *)
    rewrite H1. do 2 rewrite Vbuild_nth. unfold VG_Pexp. rewrite comPCDis. 
    unfold VG_prod. rewrite <- PCMultExt. apply f_equal2. 
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq. apply f_equal.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. rewrite FMatrix.mat_transpose_row_col.
    unfold FSemiRingT.Amult, FMatrix.get_row. rewrite Vnth_map. trivial. 
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq. apply f_equal.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. rewrite FMatrix.mat_transpose_row_col.
    unfold FSemiRingT.Amult, FMatrix.get_row. rewrite Vnth_map. trivial. 
    
  Qed.

  (* Casting amd misc - 
      this needs to be shared with other BG sub *)

  Definition RF_inProd (N : nat)(a : VF N)(b : MoR.VF N) : Ring.F :=
    Vfold_left Ring.Fadd Ring.Fzero (Vmap2 MVS.op3 b a).

  Definition RF_VCmult (N : nat)(M : MF N)(v : MoR.VF N) : MoR.VF N :=
    Vmap (fun a => RF_inProd a v) M.

  Lemma castingM0 : Nat.add 1 (m - 1) 
    = m.
  Proof.
    intros. unfold m. cbn. lia.
  Qed.

  Lemma castingM : Nat.add m (Nat.add 1 (m - 1)) 
    = Nat.add m m.
  Proof.
    intros. unfold m. cbn. lia.
  Qed.

  Lemma castingM3 : Nat.add 1 (Nat.sub (Nat.mul 2 m) 1)
      = Nat.add m m.
  Proof.
    unfold m. lia.
  Qed.

  Lemma castingM4 : Nat.mul 2 m = 
     Nat.add (Nat.add 1 m) (Nat.sub m 1).
  Proof.
    unfold m. lia.
  Qed.

  Lemma castingM5 : S (S (M.N + S (S (M.N + 0)))) =
    Nat.add m m.
  Proof.
    unfold m. lia.
  Qed.

  Lemma castingM7 : Nat.add m m = S (S (M.N + S (S (M.N + 0)))).
  Proof.
    unfold m. lia.
  Qed. 

  Lemma castingM6 : Nat.mul 2 m =
    Nat.add m m.
  Proof.
    unfold m. lia.
  Qed.

  Lemma castingM8 : forall j,
      Nat.add(S j) (S j) = Nat.add j (S (S j)).
  Proof.
    lia.
  Qed.

  Theorem index0 : Nat.lt 0%nat n.
  Proof.
    unfold n. cbn. apply neq_0_lt. auto.
  Defined. 

  Theorem indexM : Nat.lt m (m+m).
  Proof.
    cbn. unfold Nat.lt. lia.
  Defined. 

  Lemma indexMhead : forall A (v : vector A (m+m)),
    Vnth v indexM = Vhead (Vbreak v).2.
  Proof.
    intros. rewrite Vhead_nth. rewrite Vnth_vbreak_2. lia. intros.
    apply Vnth_eq. lia. 
  Qed.

  Theorem indexSM : Nat.lt (S m) ((S m)+m).
  Proof.
    cbn. unfold Nat.lt. unfold m. lia.
  Defined. 

  Lemma EkGenIndexFirstI: forall (i l : nat),
     i < l -> 0 + (1+i) <= l.
  Proof.
    intros. lia.
  Qed.

  Lemma EkGenIndexLastI : forall (i l : nat),
     i < l -> (l-(1+i)) + (1+i) <= l.
  Proof.
    intros. lia.
  Qed.

  Lemma makeSVectorsIndexRev : forall (i l : nat),
    i < l -> (l-i-1) + (1+l) <= l+l.
  Proof.
    intros. lia.
  Qed.

  (* Inital lemmas *)
  Lemma TheSMdiagindexSM : forall (T : Type)(a : T)(f : T->T->T) 
     (A : vector (vector T (S m)) (S m)),
    Vnth (ProdOfDiagonals a f A) indexSM = 
      Vfold_left f a (Vbuild (fun i (ip : i < m) => 
        Vnth (Vremove_last (Vnth (Vtail A) ip)) ip)).
  Proof.
    intros. assert (Vnth (ProdOfDiagonals a f A) indexSM = Vhead (Vbreak (ProdOfDiagonals a f A)).2).
    rewrite Vhead_nth. rewrite Vnth_vbreak_2. lia. intros. apply Vnth_eq. lia.
    rewrite H. apply TheSMdiag.
  Qed.

  Lemma TheSMinfold : forall (T : Type)(a : T)(f : T->T->T) 
     (A : vector (vector T (S m)) (S m)),
  Vcons (Vnth (ProdOfDiagonals a f A) indexSM)
        (Vtail (Vbreak (ProdOfDiagonals a f A)).2) = (Vbreak (ProdOfDiagonals a f A)).2.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    rewrite Vnth_tail. apply Vnth_eq. lia. rewrite Vnth_vbreak_2. lia. intros.
    apply Vnth_eq. lia.
  Qed.


  (* Start crazy stuff - this function exists to generate the vector under
    the exponent on the right *)

  Definition WeirdCs (a j : nat)(cBar : vector (vector Ciphertext.G a) j) 
      (a : vector (VF a) (1+j)) : MoC.VG (j+j) :=
    let first := Vbuild (fun i (ip : i < j) => MoC.VG_prod (Vmap2 (fun x y =>
         MoC.VG_prod (MoC.VG_Pexp x y))
      (Vsub cBar (EkGenIndexLastI ip)) (Vsub a (EkGenIndexFirstI (le_S ip))))) in
    let second := Vbuild (fun i (ip : i < j) => MoC.VG_prod (Vmap2 (fun x y =>
        MoC.VG_prod (MoC.VG_Pexp x y))
      (Vsub cBar (EkGenIndexFirstI ip)) (Vsub a (EkGenIndexLastI (le_S ip))))) in
    Vapp first (rev second).

  Lemma WeirdCs_one : forall (cBar : vector (vector Ciphertext.G n) 1) 
    (a : vector (VF n) 2),
  WeirdCs cBar a =
    Vmap (fun x => MoC.VG_prod (MoC.VG_Pexp (Vhead cBar) x)) a.
  Proof.
    intros. unfold WeirdCs. apply Veq_nth. intros. rewrite Vnth_app.
    destruct (le_gt_dec 1 i). do 2 rewrite Vbuild_nth. rewrite Vnth_map.
    assert (i = 1%nat). lia. subst. rewrite MoC.VG_prod_one_vec.
    do 2 rewrite Vhead_nth. rewrite Vnth_map2. apply Vfold_left_eq.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. apply f_equal2.
    rewrite Vnth_sub. apply Veq_nth3; auto. apply Vnth_eq. lia.
    rewrite Vnth_sub. apply Veq_nth3; auto. apply Vnth_eq. lia.
    (* part 2 *)
    rewrite Vbuild_nth. rewrite Vnth_map. assert (i = 0%nat). lia.
    subst. rewrite MoC.VG_prod_one_vec.
    do 2 rewrite Vhead_nth. rewrite Vnth_map2. apply Vfold_left_eq.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. apply f_equal2.
    rewrite Vnth_sub. apply Veq_nth3; auto. apply Vnth_eq. lia.
    rewrite Vnth_sub. apply Veq_nth3; auto. apply Vnth_eq. lia.
  Qed.
  
  Lemma WeirdCs_induct : forall (j : nat)(cBar : vector 
    (vector Ciphertext.G n) (S j))(a : vector (VF n) (S (S j)))(b : VF ((S j)+(S j))),
    MoC.VG_prod (MoC.VG_Pexp (WeirdCs cBar a) b) =
    Ciphertext.Gdot (Ciphertext.Gdot (MoC.VG_prod (MoC.VG_Pexp 
    (WeirdCs (Vtail cBar) (Vtail a))(double_induct b)))
    (* and what's left *)
  (MoC.VG_prod (MoC.VG_Pexp (Vmap (fun xi => MoC.VG_prod (MoC.VG_Pexp xi (Vhead a))) 
  (rev (Vtail cBar))) (Vbreak (Vcast b (castingM8 j))).1)))
  (MoC.VG_prod (MoC.VG_Pexp (Vmap (fun y => MoC.VG_prod (MoC.VG_Pexp (Vhead cBar) y)) 
   a) (Vbreak (Vcast b (castingM8 j))).2)).
  Proof.
    pose Ciphertext.module_abegrp. intros. rewrite <- dot_assoc.
    rewrite <- MoC.Vapp_VG_prod. 
    (* It is usefult to deal with the case where j = 0 first *)
    destruct (Nat.eq_dec j 0). subst. rewrite (Vector_0_is_nil (Vtail cBar)).
    rewrite Vnth_map_nil. rewrite (Vector_0_is_nil (Vbreak (Vcast b (castingM8 0))).1).
    unfold MoC.VG_Pexp. rewrite Vnth_map2_nil. rewrite MoC.VG_prod_zero.
    rewrite one_left. apply Vfold_left_eq. apply Veq_nth. intros. 
    do 2 rewrite Vnth_map2. rewrite Vnth_map. rewrite Vnth_vbreak_2. lia.
    intros. rewrite WeirdCs_one. rewrite Vnth_map. apply f_equal2; trivial.
    rewrite Vnth_cast. apply Vnth_eq. lia. 
    (* Resuming main *)
    assert (S (S (Nat.add j j)) = 
    Nat.add j (S (S j))). lia.
    (* sub lemma about cleaning up the product *)
    assert (MoC.VG_prod (MoC.VG_Pexp 
    (WeirdCs (Vtail cBar) (Vtail a0))(double_induct b)) = 
    MoC.VG_prod (Vcast (Vcons Ciphertext.Gone (Vadd (MoC.VG_Pexp (WeirdCs (Vtail cBar) (Vtail a0))
        (double_induct b)) Ciphertext.Gone)) H)). rewrite <- MoC.VG_prod_cast.
    rewrite MoC.VG_prod_Vcons. rewrite one_right. rewrite MoC.VG_prod_add.
    rewrite one_right. trivial.
    (* Resuming main *)
    rewrite H0. rewrite <- MoC.VG_Prod_mult_dist.
    assert (Nat.add j (S (S j)) = Nat.add (S j) (S j)). lia.
    rewrite (MoC.VG_prod_cast H1). apply Vfold_left_eq. apply Veq_nth. intros.
    (* Proving for each diagional *)
    rewrite Vnth_cast. do 2 rewrite Vnth_map2. rewrite Vnth_app.
    rewrite Vnth_cast. destruct (le_gt_dec j i).
    (* *)
    (* First we split on the diagonal 1/2 *)
    (* *)
    assert (i>0). lia. rewrite (Vnth_cons_tail); auto. 
    (* Breaking on final position *)
    rewrite Vnth_add. destruct (Nat.eq_dec (i - 1) (j + j)). rewrite one_left.
    rewrite Vnth_map2. apply f_equal2. rewrite Vnth_map. unfold WeirdCs.
    rewrite Vnth_app. destruct (le_gt_dec (S j) i). do 2 rewrite Vbuild_nth.
    assert (i = Nat.add (Nat.add j j) 1). lia. subst.
    rewrite MoC.VG_prod_one_vec_gen. rewrite Vhead_nth. rewrite Vnth_map2.
    apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    apply f_equal2. rewrite Vhead_nth. apply Veq_nth3; auto. rewrite Vnth_sub.
    apply Vnth_eq. lia. apply Veq_nth3; auto. rewrite Vnth_sub. apply Vnth_eq. lia.
    lia.  lia. rewrite Vnth_vbreak_2. lia. intros. rewrite Vnth_cast. apply Vnth_eq.
    lia. 
    (* Non final position *)
    do 2 rewrite Vnth_map2. rewrite <- ALVS1.mod_dist_Gdot_eq. apply f_equal2.
    rewrite Vnth_map. unfold WeirdCs. rewrite Vnth_app. destruct (le_gt_dec (S j) i).
    do 2 rewrite Vbuild_nth. rewrite Vnth_app. destruct (le_gt_dec j (i - 1)).
    do 2 rewrite Vbuild_nth. symmetry. rewrite <- MoC.VG_prod_Vcons.
    assert (S (1 + (j - (i - 1 - j) - 1)) = Nat.add 1 (Nat.sub (Nat.sub (S j) (i - S j)) 1%nat)). lia.
    rewrite (MoC.VG_prod_cast H3). apply Vfold_left_eq. apply Veq_nth.
    intros. rewrite Vnth_map2. rewrite Vnth_cast. rewrite Vnth_cons. destruct (lt_ge_dec 0 i0).
    rewrite Vnth_map2. apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    apply f_equal2. do 2 rewrite Vnth_sub. apply Veq_nth3; auto. 
    rewrite Vnth_tail. apply Vnth_eq. lia. do 2 rewrite Vnth_sub.
    apply Veq_nth3; auto. rewrite Vnth_tail. apply Vnth_eq. lia.
    apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    apply f_equal2. rewrite Vnth_sub. apply Veq_nth3; auto. rewrite Vhead_nth.
    apply Vnth_eq. lia. rewrite Vnth_sub. apply Veq_nth3; auto.
    apply Vnth_eq. lia.
    assert (false). lia.
    discriminate. assert (j = i). lia. subst. rewrite Vbuild_nth.
    rewrite Vnth_app. destruct (le_gt_dec i (i - 1)). assert (false). lia.
    discriminate. rewrite Vbuild_nth. rewrite <- MoC.VG_prod_Vcons.
    assert (S (1 + (i - 1)) = Nat.add 1 i). lia.
    rewrite (MoC.VG_prod_cast H3). apply Vfold_left_eq. apply Veq_nth. intros.
    rewrite Vnth_map2. rewrite Vnth_cast. rewrite Vnth_cons.
    destruct (lt_ge_dec 0 i0). rewrite Vnth_map2. apply Vfold_left_eq.
    apply Veq_nth.  intros. do 2 rewrite Vnth_map2. apply f_equal2.
    do 2 rewrite Vnth_sub. rewrite Vnth_tail. apply Veq_nth3; auto.
    apply Vnth_eq. lia.  do 2 rewrite Vnth_sub. rewrite Vnth_tail. 
    apply Veq_nth3; auto. apply Vnth_eq. lia. do 2 rewrite Vnth_sub.
    apply Vfold_left_eq. apply f_equal2. rewrite Vhead_nth. apply Vnth_eq.
    lia. apply Vnth_eq. lia. 
      (* Clean up *)
    rewrite Vnth_remove_last. rewrite Vnth_tail. rewrite Vnth_cast.
    apply Vnth_eq. lia. rewrite Vnth_vbreak_2. lia. intros. rewrite Vnth_remove_last.
    rewrite Vnth_tail. do 2 rewrite Vnth_cast. apply Vnth_eq. lia. 
    (* *)
    (* split on the diagonal 2/2 *)
    (* *)
    rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    (* main case *)
    rewrite Vnth_add. destruct (Nat.eq_dec (i - 1) (j + j)). assert (false). 
    lia. discriminate. do 2 rewrite Vnth_map2. rewrite Vnth_map. rewrite <- ALVS1.mod_dist_Gdot_eq.
    unfold double_induct. rewrite Vnth_remove_last. rewrite Vnth_tail.
    apply f_equal2. unfold WeirdCs. rewrite Vnth_app. destruct (le_gt_dec (S j) i).
    (* Main case 1/2  *)
    rewrite Vnth_app. destruct (le_gt_dec j (i - 1)).
    do 4 rewrite Vbuild_nth. rewrite <- MoC.VG_prod_Vcons.
    assert (S (1 + (j - (i - 1 - j) - 1)) = Nat.add 1 (Nat.sub (Nat.sub (S j) (i - S j)) 1%nat)). lia.
    rewrite (MoC.VG_prod_cast H2). apply Vfold_left_eq. apply Veq_nth.
    intros. rewrite Vnth_map2. rewrite Vnth_cast. rewrite Vnth_cons. 
    destruct (lt_ge_dec 0 i0). rewrite Vnth_map2. do 4 rewrite Vnth_sub.
    apply Vfold_left_eq. apply f_equal2. rewrite Vnth_tail. apply Vnth_eq. lia.
    rewrite Vnth_tail. apply Vnth_eq. lia. apply Vfold_left_eq. apply f_equal2. 
    rewrite Vnth_sub. rewrite Vbuild_nth. rewrite Vnth_tail. apply Vnth_eq. lia.
    rewrite Vnth_sub. rewrite Vhead_nth. apply Vnth_eq. lia.
    assert (false). lia.  discriminate.
    (*  Main case 2/2  *)
    rewrite Vnth_app. destruct (le_gt_dec j (i - 1)). assert (false). 
    lia. discriminate. do 2 rewrite Vbuild_nth. rewrite <- MoC.VG_prod_Vcons.
    assert (S (1 + (i - 1)) = Nat.add 1 i). lia.
    rewrite (MoC.VG_prod_cast H2). apply Vfold_left_eq. apply Veq_nth.
    intros. rewrite Vnth_map2. rewrite Vnth_cast. rewrite Vnth_cons. 
    destruct (lt_ge_dec 0 i0). rewrite Vnth_map2. do 4 rewrite Vnth_sub.
    apply Vfold_left_eq. apply f_equal2. rewrite Vnth_tail. apply Vnth_eq. lia.
    rewrite Vnth_tail. apply Vnth_eq. lia. apply Vfold_left_eq. apply f_equal2. 
    rewrite Vnth_sub. rewrite Vbuild_nth. rewrite Vnth_tail. apply Vnth_eq. lia.
    rewrite Vnth_sub. rewrite Vhead_nth. apply Vnth_eq. lia.
    (*resume*)
    rewrite Vnth_cast. apply Vnth_eq. lia.
    unfold double_induct. rewrite Vnth_remove_last. rewrite Vnth_tail.
    rewrite Vnth_vbreak_1. lia. intros. do 2 rewrite Vnth_cast. apply Vnth_eq. lia.
    (* i = 0 *)
    assert (i = 0%nat). lia. rewrite one_left. rewrite Vnth_map2.
    rewrite Vnth_map. unfold WeirdCs. rewrite Vnth_app. destruct (le_gt_dec (S j) i).
    assert (false). lia. discriminate. rewrite Vbuild_nth. apply f_equal2.
    subst. rewrite MoC.VG_prod_one_vec_gen. rewrite Vhead_nth.
    rewrite Vnth_map2. do 2 rewrite Vnth_sub. rewrite Vbuild_nth.
    rewrite Vnth_tail. apply Vfold_left_eq. apply Veq_nth. intros.
    do 2 rewrite Vnth_map2. apply f_equal2. apply Veq_nth3; auto. 
    apply Vnth_eq. lia. apply Veq_nth3; auto. rewrite Vhead_nth.
    apply Vnth_eq. lia. lia. rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_cast.
    apply Vnth_eq. lia.
  Qed. 

  Lemma WeirdCs_Expand_sub : forall (b c : nat)(cBar : vector (vector Ciphertext.G n) b) 
      (e : F)(Aj : vector (VF n) (S b)),
    MoC.VG_prod (Vbuild (fun i (ip : i < b) =>
      MoC.VG_prod (MoC.VG_Pexp (Vnth cBar ip)
      (Vhead (FMatrix.mat_mult [VandermondeColGen (S b) e (b - i + c - 1)] Aj))))) =
    MoC.VG_prod (MoC.VG_Pexp (WeirdCs cBar Aj)(VandermondeColGen (b + b) e c)). 
  Proof.
    (* Base case *)
    induction b. intros. cbn. trivial.
    (* Main case *)
    intros. rewrite WeirdCs_induct. rewrite VandermondeCol_induct.
    rewrite <- IHb. rewrite MoC.VG_prod_induction. apply f_equal2.
    (* Tacking matrix less top row *) 
    rewrite MoC.VG_prod_rev. symmetry. rewrite MoC.VG_prod_rev. 
    rewrite <- MoC.VG_Prod_mult_dist.
    apply Vfold_left_eq.
    (* Prove for each row *)
    apply Veq_nth. intros. rewrite Vbuild_nth. rewrite Vnth_tail. 
    rewrite Vnth_map2. do 3 rewrite Vbuild_nth. rewrite Vnth_map2. 
    rewrite Vnth_map. rewrite MoC.Sexp_dist0. rewrite <- MoC.VG_Prod_mult_dist.
    apply Vfold_left_eq. apply Veq_nth. 
    intros. rewrite Vbuild_nth. do 3 rewrite Vnth_map2.
    rewrite Vnth_map. rewrite Vnth_map2. rewrite <- VS1.mod_dist_Fmul.
    do 2 rewrite Vbuild_nth. rewrite <- VS1.mod_dist_Fadd. rewrite Vnth_tail.
    apply f_equal2; auto.
    unfold FMatrix.VA.dot_product. do 2 rewrite Vfold_left_Fadd_eq.
    rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_cast.
    rewrite <- Vfold_left_Vcons_Fadd; auto.
    apply Vfold_left_eq. apply Veq_nth.
    intros. rewrite Vnth_cons. destruct (lt_ge_dec 0 i1).
    (* Breaking across the exp *)
    do 2 rewrite Vnth_map2. apply f_equal2. do 2 rewrite Vbuild_nth.  
    apply VG_prod_const_index. lia.
    do 2 rewrite Vnth_map. rewrite Vnth_tail. apply Veq_nth3; auto.
    apply Vnth_eq. lia. 
    (* First point *)
    rewrite Vnth_map2. apply f_equal2. do 2 rewrite Vbuild_nth.
    apply VG_prod_const_index. lia. rewrite Vhead_nth. rewrite Vnth_map.
    apply Veq_nth3; auto. apply Vnth_eq. lia. 
     
    (* Main case top row *)
    do 2 rewrite Vhead_nth. rewrite Vbuild_nth.
    rewrite MoC.double_exp_over_fixed_base. rewrite MoC.Vmap_prod_pexp. 
    apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    apply f_equal2; auto. rewrite Vhead_nth. rewrite Vnth_map. 
    rewrite FMatrix.mat_mult_elem. unfold FMatrix.VA.dot_product.
    rewrite Vfold_left_Fadd_eq. apply Vfold_left_eq. apply Veq_nth.
    intros. rewrite FMatrix.mat_build_nth. rewrite Vnth_map2.
    unfold FMatrix.get_elem, FMatrix.get_row. rewrite Vnth_map2.
    do 2 rewrite Vnth_map. destruct module_ring. rewrite Rmul_comm.
    apply f_equal2. rewrite Vnth_vbreak_2. lia. intros. rewrite Vnth_cast. 
    do 2 rewrite Vbuild_nth. apply VG_prod_const_index. lia. trivial.
  Qed.
  
  Lemma WeirdCs_Expand : forall (b : nat)(cBar : vector (vector Ciphertext.G n) b) 
      (e : F)(Aj : vector (VF n) (S b)), 
    MoC.VG_prod (Vmap2 (fun (Ci : MoC.VG n) (xi : F) =>
      MoC.VG_prod (MoC.VG_Pexp Ci (VF_scale (Vhead (FMatrix.mat_mult
      [VandermondeCol (S b) e] Aj)) xi))) cBar
     (rev (VandermondeCol b e))) 
      =
    MoC.VG_prod (MoC.VG_Pexp (WeirdCs cBar Aj) (VandermondeCol (b + b) e)).
  Proof.
    intros. assert (MoC.VG_prod (Vmap2 (fun (Ci : MoC.VG n) (xi : F) =>
    MoC.VG_prod (MoC.VG_Pexp Ci (VF_scale (Vhead (FMatrix.mat_mult
    [VandermondeCol (S b) e] Aj)) xi))) cBar (rev (VandermondeCol b e))) = 
    MoC.VG_prod (Vbuild (fun i (ip :  i < b) => MoC.VG_prod (MoC.VG_Pexp (Vnth cBar ip)
   (Vhead (FMatrix.mat_mult  [VandermondeColGen (S b) e (b-i-1)] Aj)))))).
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vbuild_nth. apply f_equal. apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vhead_nth.
    do 2 rewrite FMatrix.mat_mult_elem. destruct module_ring.
    rewrite Rmul_comm. pose FMatrix.VA.dot_product_distr_mult.
    unfold FSemiRingT.Amult in e0. rewrite e0. apply f_equal2; auto.
    apply Veq_nth. intros. rewrite Vbuild_nth. unfold FMatrix.get_row.
    rewrite Vbuild_nth. do 3 rewrite Vbuild_nth.
    rewrite VF_prod_const. assert (Nat.add (Nat.sub (Nat.sub b i) 1) i1 =
    (Nat.add i1 (Nat.sub (Nat.sub b i) 1))). lia. rewrite H. trivial.
    rewrite H. rewrite VandermondeColGe_eq. assert (Vbuild
     (fun (i : nat) (ip : i < b) => MoC.VG_prod
     (MoC.VG_Pexp (Vnth cBar ip) (Vhead (FMatrix.mat_mult
     [VandermondeColGen (S b) e (b - i - 1)] Aj)))) = Vbuild
     (fun (i : nat) (ip : i < b) => MoC.VG_prod (MoC.VG_Pexp (Vnth cBar ip)
     (Vhead (FMatrix.mat_mult [VandermondeColGen (S b) e (b - i + 0 - 1)] Aj))))).
    apply Veq_nth. intros. do 2 rewrite Vbuild_nth. apply Vfold_left_eq.
    apply f_equal2; auto. apply f_equal. apply f_equal2; auto. apply Vcons_eq.
    split; auto. apply f_equal. lia. rewrite H0. rewrite WeirdCs_Expand_sub. trivial.
  Qed. 
  (* End crazy stuff *) 

  Definition EkGeneratorsSub 
    (j : nat)(cBar : vector (vector Ciphertext.G n) j)
      (A : vector (VF n) j) : MoC.VG j :=
    Vbuild (fun i (ip : i < j) => 
              (* C_i,...,C_(l-j) *)
              let cBarSub := Vsub cBar (EkGenIndexLastI ip)  in
              (* A_0,...,A_(i-1) *)
              let Asub := Vsub A (EkGenIndexFirstI ip) in 
      MoC.VG_prod (Vmap2 (fun x y =>
             MoC.VG_prod (MoC.VG_Pexp x y)) cBarSub Asub)
    ).

  (* EkGeneratorSub rearranged *)
  Definition EkGeneratorsSubAlt 
      (j : nat)(cBar : vector (vector Ciphertext.G n) j)
      (A : vector (VF n) j)(x : VF j) : MoC.VG j :=
      Vbuild (fun i (ip : i < j) => 
         MoC.VG_prod (Vmap (fun y => MoC.VG_prod 
          (* C_i^(x_(j-i)a_1+...+x_(j)a_i *)
          (MoC.VG_Pexp (Vnth cBar ip) y)) (Vmap2 (VF_scale (n:=n)) 
      (Vsub A (EkGenIndexFirstI ip)) 
         (Vsub x (EkGenIndexLastI ip))))).

  Lemma EkGeneratorsSubAltTail : forall (j : nat)(A : vector (VF n) (S j))
    (cBar : vector (vector Ciphertext.G n) (S j))(x : VF (S j)),
    Vremove_last (EkGeneratorsSubAlt cBar A x) = 
      EkGeneratorsSubAlt (Vremove_last cBar) (Vremove_last A) (Vtail x).
   Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_remove_last.
      do 2 rewrite Vbuild_nth. rewrite Vnth_remove_last. 
      apply Vfold_left_eq. apply Veq_nth. intros.
      do 2 rewrite Vnth_map. apply Vfold_left_eq. apply Veq_nth.
      intros. do 4 rewrite Vnth_map2. apply ALVS1.scaleEq.
      do 2 rewrite Vnth_map. do 4 rewrite Vnth_sub.
      apply ALVS1.F_mul_split. rewrite Vnth_remove_last.
      apply Veq_nth2. apply Vnth_eq. trivial.
      rewrite Vnth_tail. apply Vnth_eq. lia.
    Qed.

   Lemma EkGenSubComb : forall (j : nat)(A : vector (VF n) (S j))
    (cBar : vector (vector Ciphertext.G n) j)(x : VF (j+j)),
    Vmap2 Ciphertext.Gdot 
      (* c_0^(a_0*x_2),...,c_2^(a_0x_0+...+a_2x_2) *)
      (EkGeneratorsSubAlt cBar (Vremove_last A) (Vbreak x).1)
      (* c_0^(a_1x_3+...,a_3x_5),...,c_2^(a_3x_3) *) 
     (rev (EkGeneratorsSubAlt (rev cBar) (rev (Vtail A))(rev (Vbreak x).2))) 
        = Vbuild (fun i (ip : i < j) => 
        (* x_(j-i),...x_(j+j) *)
        let xSub := Vsub x (makeSVectorsIndexRev ip) in  
        (* A_0,...,A_(i-1) *)
         let Asub := Vmap2 (VF_scale (n:=n)) A xSub in 
         MoC.VG_prod (Vmap (fun y => MoC.VG_prod 
          (MoC.VG_Pexp (Vnth cBar ip) y)) Asub)). 
   Proof.
    pose Ciphertext.module_abegrp.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 5 rewrite Vbuild_nth.
    rewrite comm. rewrite MoC.VG_prod_rev. rewrite comm. rewrite <- MoC.Vapp_VG_prod.
    (* Ready to break down *)
    assert (Nat.add (Nat.add 1 i) (Nat.add 1 (Nat.sub (Nat.sub j i) 1)) = S j). lia.
    rewrite (MoC.VG_prod_cast H). apply Vfold_left_eq.
    apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_cast.
    rewrite Vnth_app. destruct (le_gt_dec (1 + i) i0).
    (* Moving into base case *)
    rewrite Vbuild_nth. rewrite Vnth_map. rewrite invertPosCancel. unfold MoC.VG_prod.
    apply Vfold_left_eq. apply Veq_nth. intros. do 4 rewrite Vnth_map2.
    (* Down to the inner product *)  
    apply ALVS1.scaleEq. do 2 rewrite Vnth_map. apply ALVS1.F_mul_split.
    apply Veq_nth2. rewrite Vnth_sub. rewrite Vbuild_nth. rewrite Vnth_tail.
    apply Vnth_eq. lia. 
    (* Other part of exp *)
    rewrite Vnth_sub. rewrite Vbuild_nth. rewrite Vnth_vbreak_2. lia.
    intros. rewrite Vnth_sub. apply Vnth_eq. lia.
    (* Onwards *)
    rewrite Vnth_map2. rewrite Vnth_map.  apply Vfold_left_eq. apply Veq_nth. 
    intros. do 3 rewrite Vnth_map2. apply ALVS1.scaleEq. do 2 rewrite Vnth_map.
    apply ALVS1.F_mul_split. apply Veq_nth2. rewrite Vnth_sub. rewrite Vnth_remove_last.
    apply Vnth_eq. lia. rewrite Vnth_sub. rewrite Vnth_vbreak_1. lia. intros. 
    rewrite Vnth_sub. apply Vnth_eq. lia.
   Qed.

  (* The proof of this is harder than expected *)
   Lemma EkGenSubAltEq : forall (j : nat)(A : vector (VF n) j)
    (cBar : vector (vector Ciphertext.G n) j)(x : VF j),
      MoC.VG_prod (MoC.VG_Pexp (EkGeneratorsSub cBar A) x) =
      MoC.VG_prod (EkGeneratorsSubAlt cBar A x).
   Proof.
    pose Ciphertext.module_abegrp.
    intros. induction j. cbn. trivial. symmetry.
    rewrite MoC.VG_prod_rev. rewrite MoC.VG_prod_induction.
    rewrite rev_tail_last. rewrite EkGeneratorsSubAltTail.
    rewrite <- MoC.VG_prod_rev. rewrite <- IHj.
    (* Induction Hypotsis applied *)
    rewrite Vhead_nth. do 2 rewrite Vbuild_nth.
    do 2 rewrite MoC.VG_prod_induction. symmetry.
    rewrite <- MoC.VG_prod_induction. symmetry.
    rewrite dot_assoc. assert (Nat.sub (Nat.sub (S j)
    0) 1 = j). lia. rewrite (MoC.VG_prod_cast H).
    rewrite <- MoC.VG_Prod_mult_dist. rewrite <- MoC.VG_prod_Vcons.
    apply Vfold_left_eq. 
    apply Veq_nth. intros. rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    (* We have now rearranged sub and broken to main case *)
    do 3 rewrite Vnth_map2. rewrite Vnth_cast. do 2 rewrite Vnth_tail. 
    rewrite Vnth_map. rewrite Vnth_map2. rewrite <- MoC.VG_prod_VG_Pexp_scale. 
    do 2 rewrite Vnth_sub. assert (Vnth x (lt_n_S (Vnth_cons_tail_aux ip l)) =
    Vnth x ip). apply Vnth_eq. lia. rewrite H0. assert (Vnth x
    (Vnth_sub_aux (S j - (1 + (S j - 0 - 1))) (EkGenIndexLastI
    (invertPos (Nat.lt_0_succ j)))(lt_n_S (Vnth_cast_aux H
    (Vnth_cons_tail_aux ip l)))) = Vnth x ip). apply Vnth_eq.
    destruct i. pose (lt_le_S l). lia. lia. rewrite H1.
    rewrite <- VS1.mod_dist_Gdot. apply ALVS1.scaleEqFull.
    do 2 rewrite Vbuild_nth. rewrite <- MoC.VG_prod_add.
    assert (S (Nat.add 1 (Nat.sub i 1)) = Nat.add 1 i). pose (lt_le_S l).
    lia. rewrite (MoC.VG_prod_cast H2). apply Vfold_left_eq.
    apply Veq_nth. intros. rewrite Vnth_cast. rewrite Vnth_map2.
    rewrite Vnth_add. destruct (Nat.eq_dec i0 (1 + (i - 1))).
    (* Clean up inner base *)
    subst. do 2 rewrite Vnth_sub. apply Vfold_left_eq. apply Veq_nth. intros.
    do 2 rewrite Vnth_map2.
    apply ALVS1.scaleEqFull. apply Veq_nth3. trivial.
    apply Vnth_eq. rewrite H. assert (Nat.add 1 (Nat.sub i 1) = i).
    lia. rewrite H3. pose (lt_le_S ip). lia. apply Veq_nth3. trivial. 
    apply Vnth_eq. lia.
    (* The middle *)
    rewrite Vnth_map2. do 6 rewrite Vnth_sub. apply Vfold_left_eq.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. apply ALVS1.scaleEqFull.
    apply Veq_nth3. trivial. apply Vnth_eq. lia. apply Veq_nth3. 
    trivial. apply Veq_nth3. lia. trivial. trivial. 
    (* Clearing base case *)
    assert (i = 0%nat). lia. subst. rewrite Vhead_nth. rewrite Vnth_map.
    do 2 rewrite Vnth_map2. rewrite Vbuild_nth. rewrite MoC.Sexp_dist0.
    rewrite MoC.VG_prod_one. rewrite MoC.Sexp_dist0. apply Vfold_left_eq.
    apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vnth_map.
    rewrite Vnth_map2. rewrite <- VS1.mod_dist_Fmul. apply ALVS1.scaleEqFull.
    rewrite Vhead_nth. rewrite Vnth_sub. apply Veq_nth3. trivial.
    apply Vnth_eq. lia. destruct module_ring. rewrite Rmul_comm.
    apply ALVS1.F_mul_split. rewrite Vnth_sub. apply Vnth_eq. lia.
    apply Veq_nth3. trivial. rewrite Vhead_nth. do 2 rewrite Vnth_sub.
    apply Vnth_eq. lia.
  Qed.

  Definition EkGenerators (pk : enc.PK)(l : nat)
    (g : enc.M)(cBar : (vector (vector Ciphertext.G n) l))
    (a0 : (vector (VF n) (1+l)))(tau : vector Ring.F (l+l))
    (b : VF (l+l))(x : VF (l+l)) :=

      let E1 := Vmap2 (fun x y => enc.enc pk (VS3.op g x) y) b tau in

      (* E_0,...,E_(m-1) : m elements *)
      let Epre := EkGeneratorsSub cBar (Vremove_last a0) in
      (* E_(m),...,E_(2*m-1) : m-1 elements *)
      let Epost := rev (EkGeneratorsSub (rev cBar) (rev (Vtail a0))) in

      let E2 := Vapp Epre Epost in
    
      Vmap2 Ciphertext.Gdot E1 (MoC.VG_Pexp E2 x).

  Definition EkGeneratorsSubRawM (j : nat)(Ca : vector (VF n) j)
      (A : vector (VF n) j) : VF j :=
    Vbuild (fun i (ip : i < j) => 
              (* C_i,...,C_(l-j) *)
              let cBarSub := Vsub Ca (EkGenIndexLastI ip)  in
              (* A_0,...,A_(i-1) *)
              let Asub := Vsub A (EkGenIndexFirstI ip) in 
      VF_sum (Vmap2 (fun x y =>
             VF_sum (VF_mult x y)) cBarSub Asub)
    ).


  Definition EkGeneratorsSubRawR(j : nat)(Ctau : vector (vector Ring.F n) j)
      (A : vector (VF n) j) : vector Ring.F j :=
    Vbuild (fun i (ip : i < j) => 
              (* C_i,...,C_(l-j) *)
              let cBarSub := Vsub Ctau (EkGenIndexLastI ip)  in
              (* A_0,...,A_(i-1) *)
              let Asub := Vsub A (EkGenIndexFirstI ip) in 
      MoR.VF_sum (Vmap2 (fun x y =>
             MoR.VF_sum (Vmap2 MVS.op3 x y)) cBarSub Asub)
    ).


  Definition EkGeneratorsRawM (l : nat)
    (Ca : vector (VF n) l)
    (a0 : (vector (VF n) (1+l)))
    (b : VF (l+l))  :=

      let messagePre := EkGeneratorsSubRawM Ca (Vremove_last a0) in 
      let messagePost := rev (EkGeneratorsSubRawM (rev Ca) (rev (Vtail a0))) in

      VF_add b (Vapp messagePre messagePost).

  Definition EkGeneratorsRawR (l : nat)
    (Ctau : vector (vector Ring.F n) l)
    (a0 : (vector (VF n) (1+l)))(tau : vector Ring.F (l+l)) := 

      let randomnessPre := EkGeneratorsSubRawR Ctau (Vremove_last a0) in 
      let randomnessPost := rev (EkGeneratorsSubRawR (rev Ctau) (rev (Vtail a0))) in

      MoR.VF_add tau (Vapp randomnessPre randomnessPost).

  Lemma EkGeneratorsRawM_switch : forall (l : nat)(b' : VF (S l))(c' : VF l)
    (Ca : vector (VF n) (S l))(a0 : (vector (VF n) (1+(S l))))
     (b : VF (S l))(a : F)(c : VF l),
    Vhead (Vbreak (EkGeneratorsRawM Ca a0 (Vapp b (Vcons a c)))).2 = 
    Vhead (Vbreak (EkGeneratorsRawM Ca a0 (Vapp b' (Vcons a c')))).2.
  Proof.
    intros. unfold EkGeneratorsRawM, VF_add, FMatrix.VA.vector_plus.
    do 2 rewrite <- Vbreak_vmap2_2. do 3 rewrite Vbreak_app. simpl. trivial. 
  Qed.

  Lemma EkGeneratorsRawR_switch : forall (l : nat)(b' : vector Ring.F (S l))
      (c' : vector Ring.F l)
    (Ctau : vector (vector Ring.F n) (S l))(a0 : (vector (VF n) (1+(S l))))
     (b : vector Ring.F (S l))(a : Ring.F)(c : vector Ring.F l),
    Vhead (Vbreak (EkGeneratorsRawR Ctau a0 (Vapp b (Vcons a c)))).2 = 
    Vhead (Vbreak (EkGeneratorsRawR Ctau a0 (Vapp b' (Vcons a c')))).2.
  Proof.
    intros. unfold EkGeneratorsRawR, MoR.VF_add, MoR.FMatrix.VA.vector_plus.
    do 2 rewrite <- Vbreak_vmap2_2. do 3 rewrite Vbreak_app. simpl. trivial. 
  Qed.

  Lemma EkGeneratorsRaw_conv : forall (pk : enc.PK)(l : nat)
    (g : enc.M)(Ca : vector (VF n) l)(Ctau : vector (vector Ring.F n) l)
    (a0 : (vector (VF n) (1+l)))(tau : vector Ring.F (l+l))
    (b : VF (l+l))(cBar : (vector (vector Ciphertext.G n) l)),
     cBar = Vmap2 (fun y z => Vmap2 (fun w v => enc.enc pk (VS3.op g w) v) y z) Ca Ctau ->
     Vmap2 (fun w v => enc.enc pk (VS3.op g w) v) (EkGeneratorsRawM Ca a0 b) 
     (EkGeneratorsRawR Ctau a0 tau) = EkGenerators pk g cBar a0 tau b (VF_one (l+l)).
  Proof.
    pose Ciphertext.module_abegrp.
    intros. apply Veq_nth. intros. do 6 rewrite Vnth_map2. rewrite H. 
    rewrite Vnth_const. rewrite VS1.mod_id. rewrite VS3.mod_dist_Fadd. 
    rewrite <- enc.homomorphism. rewrite comm. apply f_equal.
    rewrite Vnth_app. rewrite Vnth_app. rewrite Vnth_app.
    destruct (le_gt_dec l i). 
    (* case 1 *)
    do 6 rewrite Vbuild_nth. rewrite MoM.VF_sum_op. rewrite comHomomorphism.
    unfold MoC.VG_prod. rewrite enc.encZero. apply f_equal. apply Veq_nth.
    intros. do 3 rewrite Vnth_map2. rewrite Vnth_map. rewrite Vnth_map2. 
    rewrite MoM.VF_sum_op. rewrite comHomomorphism. rewrite enc.encZero.
    apply f_equal. apply Veq_nth. intros. do 3 rewrite Vnth_map2. do 4 rewrite Vnth_sub.
    do 4 rewrite Vbuild_nth. do 2 rewrite Vnth_map2. rewrite Vnth_map. 
    rewrite enc.encDis. rewrite Vnth_map2. trivial.
    (* case 2 *)
    do 3 rewrite Vbuild_nth. rewrite MoM.VF_sum_op. rewrite comHomomorphism.
    unfold MoC.VG_prod. rewrite enc.encZero. apply f_equal. apply Veq_nth.
    intros. do 3 rewrite Vnth_map2. rewrite Vnth_map. rewrite Vnth_map2. 
    rewrite MoM.VF_sum_op. rewrite comHomomorphism. rewrite enc.encZero.
    apply f_equal. apply Veq_nth. intros. do 3 rewrite Vnth_map2. do 5 rewrite Vnth_sub.
    do 2 rewrite Vnth_map2. rewrite Vnth_map. rewrite enc.encDis. rewrite Vnth_map2.
    trivial.
  Qed.
    

  (* Describes Pexp EkGenerators *)
  Lemma EkGeneratorsPexp :
    forall (pk : enc.PK)
    (g : enc.M)(cBar : (vector (vector Ciphertext.G n) m))
    (a0 : (vector (VF n) (1+m)))(tau : vector Ring.F (m+m))
    (k : VF (m+m))(x y : VF (m+m)),
    MoC.VG_Pexp (EkGenerators pk g cBar a0 tau k x) y
      = (EkGenerators pk g cBar a0
          (Vmap2 MVS.op3 tau y) (VF_mult k y))
          (VF_mult x y).
  Proof.
    pose Ciphertext.module_abegrp.
    intros. apply Veq_nth. intros. unfold EkGenerators.  
    do 8 rewrite Vnth_map2. rewrite VS1.mod_dist_Gdot.
    apply eqImplProd. split. rewrite enc.encDis.
    trivial.
    do 2 rewrite Vnth_map2. rewrite ALVS1.mod_dist_FMul2.
    trivial.
  Qed.

  Definition makeSVectors (l : nat)(s : VF (l+l)) :  
      vector (VF (1+l)) l :=
    Vbuild (fun i (ip : i < l) => 
      Vsub s (makeSVectorsIndexRev ip)).

  Lemma pexpOfCiphertext : forall (n : nat)(pk : enc.PK)
      (g : enc.M)(k e : VF n)(tau : vector Ring.F n),
   MoC.VG_Pexp (Vmap2 (fun x y =>
         enc.enc pk (VS3.op g x) y) k tau) e = 
    Vmap2 (fun x y => enc.enc pk (VS3.op g x) y) (VF_mult k e) 
      (Vmap2 MVS.op3 tau e).
  Proof.
    intros. apply Veq_nth. intros. do 5 rewrite Vnth_map2.
    rewrite enc.encDis. trivial.
  Qed.

  Lemma prodOfCiphertext : forall (n : nat)(pk : enc.PK)
      (g : enc.M)(k : VF n)(tau : vector Ring.F n),
    MoC.VG_prod (Vmap2 (fun x0 : F => 
          [eta enc.enc pk (VS3.op g x0)]
     ) k tau) =
            enc.enc pk (VS3.op g (VF_sum k)) (MoR.VF_sum tau).
    Proof.
      intros. induction n0. rewrite (Vector_0_is_nil k).
      rewrite (Vector_0_is_nil tau). cbn. rewrite VS3.mod_ann.
      rewrite enc.encZero. trivial.
      rewrite MoC.VG_prod_induction. rewrite <- Vtail_map2.
      rewrite IHn0. rewrite Vhead_nth. rewrite Vnth_map2.
      rewrite enc.homomorphism. do 2 rewrite <- Vhead_nth.
      rewrite <- VS3.mod_dist_Fadd. rewrite MoR.VF_sum_induction.
      rewrite VF_sum_induction. apply EncEq. apply f_equal2; auto.
      ring; auto. destruct Ring.module_ring. apply Radd_comm.
    Qed. 

  (* Describes VG_Prod EkGenerators *)  
  Lemma EkGeneratorsProd :
    forall (pk : enc.PK)
    (g : enc.M)(cBar : (vector (vector Ciphertext.G n) m))
    (a0 : (vector (VF n) (1+m)))(tau : vector Ring.F (m+m))
    (k : VF (m+m))(s : VF (m+m)),
    let sVectors : vector (VF (1+m)) m:= 
      makeSVectors m s in 

    MoC.VG_prod (EkGenerators pk g cBar a0 tau k s)
      = Ciphertext.Gdot (enc.enc pk (VS3.op g (VF_sum k))
        (MoR.VF_sum tau))
      (MoC.VG_prod  (Vmap2 
        (fun x scaleV => MoC.VG_prod (Vmap2 (fun y scale => 
          MoC.VG_prod (MoC.VG_Pexp x (VF_scale y scale))) 
          a0 scaleV)) cBar sVectors)).
  Proof.
    pose Ciphertext.module_abegrp.
    intros. unfold EkGenerators. rewrite MoC.VG_Prod_mult_dist.
    apply eqImplProd. split. apply prodOfCiphertext.
    rewrite MoC.VG_prod_VG_Pexp_app. rewrite MoC.VG_prod_VG_Pexp_rev.
    do 2 rewrite EkGenSubAltEq. rewrite comm. rewrite MoC.VG_prod_rev.
    rewrite comm. rewrite MoC.Vfold_Gdot_dob. rewrite EkGenSubComb.
    (* Up this point I beleive it works *)
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vbuild_nth. apply Vfold_left_eq. apply Veq_nth. intros.
    rewrite Vnth_map. rewrite Vnth_map2. apply Vfold_left_eq.
    apply Veq_nth. intros. do 3 rewrite Vnth_map2. apply ALVS1.scaleEq.
    do 2 rewrite Vnth_map. apply ALVS1.F_mul_split. trivial.
    rewrite Vnth_sub. rewrite Vbuild_nth. rewrite Vnth_sub.
    apply Vnth_eq. trivial.
  Qed.

  Lemma EkGeneratorsRawR_clear : forall (l : nat) (Ctau : vector (vector Ring.F n) l)
    (a0 : (vector (VF n) (1+l)))(tau : vector Ring.F (l+l)),
      Vmap2 Ring.Fadd (EkGeneratorsRawR Ctau a0 tau)
       (Vmap Ring.Finv (EkGeneratorsRawR Ctau a0 (MoR.VF_zero (l + l)))) = tau.
  Proof.
    intros. unfold EkGeneratorsRawR. rewrite (MoR.VF_comm (MoR.VF_zero (l + l))).
    rewrite MoR.VF_add_zero. pose MoR.VF_add_neg. unfold MoR.VF_add, MoR.VF_neg,
    MoR.FMatrix.VA.vector_plus in *. rewrite e. trivial.
  Qed.

  Lemma EkGeneratorsRawM_clear : forall (l : nat) (Ctau : vector (VF n) l)
    (a0 : (vector (VF n) (1+l)))(tau : VF (l+l)),
      Vmap2 Fadd (EkGeneratorsRawM Ctau a0 tau)
       (Vmap Finv (EkGeneratorsRawM Ctau a0 (VF_zero (l + l)))) = tau.
  Proof.
    intros. unfold EkGeneratorsRawM. rewrite (VF_comm (VF_zero (l + l))).
    rewrite VF_add_zero. pose VF_add_neg. unfold VF_add, VF_neg,
    FMatrix.VA.vector_plus in *. rewrite e. trivial.
  Qed.

End BGSupport.

Module BGSupportIns (Message Ciphertext Commitment : GroupSig)(Ring : RingSig)
    (Field : FieldSig)(VS2 : VectorSpaceSig Commitment Field)
    (VS1 : VectorSpaceSig Ciphertext Field)
    (MVS : VectorSpaceModuleSameGroup Ciphertext Ring Field VS1)
    (VS3 : VectorSpaceSig Message Field)(Hack : Nat)(M : Nat)
    (enc : EncryptionSchemePlus Message Ciphertext Ring Field VS1 VS3 MVS).
  
  (* N = nm *)
  Let n := S (S (S Hack.N)).      (* n *)
  Let m := S (S M.N).     (* m *)
  Import Field.

  Module Mo := MatricesFieldIns Field.
  Import Mo.
  Import Mo.mat.
  Module MoR := MatricesFIns Ring.
  Module MoC := MatricesG Ciphertext Field VS1 mat.

  (* Make commitment scheme and matrix *)
  Module EPC := ExtendComScheme Commitment Field VS2 mat.
  Import EPC.
  Import EPC.MoM.
  Module PC := BasicComScheme Commitment Field VS2 mat.
  Import PC.

  Module MoM := MatricesG Message Field VS3 mat.

  (* Addational vector lemma *)
  Module ALVS1 := VectorSpaceAddationalLemmas Ciphertext Field VS1.
  Module ALVS2 := VectorSpaceAddationalLemmas Commitment Field VS2.
  Module ALVS3 := VectorSpaceAddationalLemmas Message Field VS3.

  Module ALenc := EncryptionSchemeProp Message Ciphertext Ring Field VS1 MVS enc.
  Import ALenc.
  Module HardProb := HardProblems Commitment Field VS2.
  Import HardProb.

  Module ALR := RingAddationalLemmas Ring.

  Import VS2.
  Import Commitment.

  Lemma moreIsLess : forall a,
    0 < S a.
  Proof.
    intros. lia.
  Qed.

  Lemma lessIsLess : forall j i N,
    j < S i -> i < S N ->
    j < S N.
  Proof.
    intros. lia.
  Qed.

  Lemma lessIsLessShift : forall j i N,
    j < S i -> i < S N ->
    j+(N - i) < S N.
  Proof.
    intros. lia.
  Qed.

  Lemma leS : forall i j,
    i < j -> i < S j.
  Proof.
   intros. lia.
  Qed.

  (* At the momment I have written this to only work for square matrices *)
  Definition ProdOfDiagonals (T : Type)(a : T)(f : T->T->T) N
     (A : vector (vector T (S N)) (S N)) : vector T (S N + N) :=
    let left := Vbuild (fun i (ip : i < S N) => (* For i = 0 to N *)
      Vfold_left f a (Vbuild (fun j (jp : j < S i) => (* For j = 0 to i *)
        (* let jpc := lessIsLess jp ip in (* x = j *)
        let jpt := lessIsLessShift jp ip in (* y = h+(N-i) *) *)
        Vnth (Vnth A (lessIsLess jp ip)) (lessIsLessShift jp ip) (* Get A x y *)
      ))
    ) in
    let right := Vbuild (fun i (ip : i < N) => (* For i = 0 to N-1 *)
      Vfold_left f a (Vbuild (fun j (jp : j < S i) =>  (* For j = 0 to i *)
        (* let jpc := lessIsLessShift jp (leS ip) in (* x = j+(N-i) *)
        let jpt := lessIsLess jp (leS ip) in (* y = j *) *)
        Vnth (Vnth A (lessIsLessShift jp (leS ip))) (lessIsLess jp (leS ip))
      ))
    ) in
    Vapp left (rev right).

  (* Inital lemmas *)
  Lemma TheSMdiag : forall (T : Type)(a : T)(f : T->T->T) N
     (A : vector (vector T (S (S N))) (S (S N))),
    Vhead (Vbreak (ProdOfDiagonals a f A)).2 =
      Vfold_left f a (Vbuild (fun i (ip : i < (S N)) =>
        Vnth (Vremove_last (Vnth (Vtail A) ip)) ip)).
  Proof.
    intros. rewrite Vhead_nth. rewrite Vnth_vbreak_2. lia. intros. rewrite Vnth_app.
    destruct (le_gt_dec (S (S N)) (0 + S (S N))). rewrite Vbuild_nth.
    rewrite Vbuild_nth. assert (S ((S N) - (0 + S (S N) - S (S N)) - 1) = S N).
    lia. apply (Vfold_left_eq_cast H). apply Veq_nth. intros. rewrite Vnth_cast.
    do 2 rewrite Vbuild_nth. rewrite Vnth_remove_last. apply Veq_nth3. trivial.
    rewrite Vnth_tail. apply Vnth_eq. lia. assert False. lia. contradiction.
  Qed.

  Definition ProdOfDiagonalsF := ProdOfDiagonals 0 Fadd.

  Definition ProdOfDiagonalsVF (N : nat) := ProdOfDiagonals (VF_zero N) (VF_add (n:=N)).
  Definition ProdOfDiagonalsG := ProdOfDiagonals Gone Gdot.

  Lemma ProdOfDiagonalsF_ProdOfDiagonalsVF: forall gen l (lp : l < n),
  Vnth (FMatrix.mat_transpose (ProdOfDiagonalsVF
   (Vbuild (fun (i : nat) (ip : i < S m) => Vbuild (
   fun (j : nat) (jp : j < S m) => gen i j ip jp))))) lp  =
  ProdOfDiagonalsF (Vbuild (fun (i : nat) (ip : i < S m) =>
   Vbuild (fun (j : nat) (jp : j < S m) => Vnth (gen i j ip jp) lp))).
  Proof.
    intros. apply Veq_nth. intros. rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_elem. unfold FMatrix.get_row. do 2 rewrite Vnth_app.
    (* case 1 *)
    destruct (le_gt_dec (S m) i). do 4 rewrite Vbuild_nth. rewrite Vfold_left_VF_add.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_map. do 6 rewrite Vbuild_nth. trivial.
    (* case 2 *)
    do 2 rewrite Vbuild_nth. rewrite Vfold_left_VF_add. apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_map. do 6 rewrite Vbuild_nth. trivial.
  Qed.

  Lemma SubMatrixRight : forall T (f : T -> T -> F) N (A : vector T (S (S N)))
        (B : vector T (S (S N))),
    Vtail (Vbreak (ProdOfDiagonalsF
     (FMatrix.mat_build (fun i j (ip: i < S (S N))(jp : j < S (S N)) =>
      f (Vnth A ip) (Vnth B jp))))).2  =
  (Vbreak (ProdOfDiagonalsF (FMatrix.mat_build (fun i j (ip: i < S N)(jp : j < S N) =>
      f (Vnth (Vtail A) ip) (Vnth (Vremove_last B) jp))))).2.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_tail. rewrite Vnth_vbreak_2. lia.
    intros. rewrite Vnth_vbreak_2. lia. intros. do 2 rewrite Vnth_app.
    destruct (le_gt_dec (S (S N)) (S i + S (S N))). destruct (le_gt_dec (S N) (i + S N)).
    do 4 rewrite Vbuild_nth. assert (S (S N - (S i + S (S N) - S (S N)) - 1) =
    S (N - (i + S N - S N) - 1)). lia. apply (Vfold_left_eq_cast H).
    apply Veq_nth. intros. rewrite Vnth_cast. do 2 rewrite Vbuild_nth.
    do 2 rewrite FMatrix.mat_build_nth. apply f_equal2. rewrite Vnth_tail.
    apply Vnth_eq. lia. rewrite Vnth_remove_last. apply Vnth_eq. lia.
    assert (False). lia. contradiction.  assert (False). lia. contradiction.
  Qed.

  Lemma FMatrix_mat_build_vcons_tail : forall T (f : T -> T -> F) N
    (A B : vector T (S N))(a b : T),
    FMatrix.mat_build (fun i j (ip: i < (S N))(jp : j < (S N)) =>
      f (Vnth (Vtail (Vcons a A)) ip) (Vnth (Vremove_last (Vadd B b)) jp))  =
    FMatrix.mat_build (fun i j (ip: i < S N)(jp : j < S N) =>
      f (Vnth A ip) (Vnth B jp)).
  Proof.
    intros. apply Veq_nth. intros. apply Veq_nth. intros.
    do 2 rewrite FMatrix.mat_build_nth. rewrite Vtail_cons.
    rewrite Vremove_last_add. trivial.
  Qed.
  
  Lemma ProdOfDiagonalsHead : forall (T : Type)(a : T)(f : T->T->T) N
      (A : vector (vector T (S N)) (S N)),
    Vhead (ProdOfDiagonals a f A) = f a (Vhead (rev (Vhead A))).
  Proof.
    intros. rewrite Vhead_app. rewrite Vbuild_head. simpl.  apply f_equal.
    rewrite Vhead_nth. apply Veq_nth3.
    lia. apply Vnth_eq. trivial.
  Qed.

  Lemma ProdOfDiagonalsFVhead : forall n n' (a b : VF n)(A B : vector (VF n) n')
    (f : VF n -> VF n -> F),
    Vhead (ProdOfDiagonalsF (FMatrix.mat_build  (fun i j ip jp =>
            f (Vnth (Vcons a A) ip)
              (Vnth (Vadd B b) jp)))) = f a b.
  Proof.
    intros. unfold ProdOfDiagonalsF. rewrite ProdOfDiagonalsHead.
    rewrite Vhead_mat_build. rewrite Vhead_nth. do 2 rewrite Vbuild_nth.
    rewrite <- rev_Vadd. rewrite Vbuild_nth. rewrite invertPosCancel.
    do 2 rewrite Vnth_cons. destruct (lt_ge_dec 0 0).
    assert False. lia. contradiction. field; auto.
  Qed.

  Lemma ProdOfDiagonalsOne : forall (T : Type)(a : T)(f : T->T->T)
      (A : vector (vector T 1) 1),
    (forall b : T, f a b = b) ->
    ProdOfDiagonals a f A = Vhead A.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_app. destruct (le_gt_dec 1 i).
    assert False. lia. contradiction. rewrite Vbuild_nth. assert (i=0%nat). lia.
    subst. rewrite Vfold_left_head; auto. rewrite Vbuild_head. apply Veq_nth3. trivial.
    rewrite Vhead_nth.
    apply Veq_nth3; auto.
  Qed.


  Lemma ProdOfDiagonalsOneF : forall (A : vector (VF 1) 1),
    ProdOfDiagonalsF A = Vhead A.
  Proof.
    intros. apply ProdOfDiagonalsOne. intros. ring; auto.
  Qed.

  (* We assume the main operation is commutive and assocative *)
 Lemma ProdOfDiagonalsSum : forall (T U V : Type)(a : T)(f : T->T->T) N
    (A : vector U (S N))(B : vector V (S N))(f' : U->V->T),
    (forall b : T, f a b = b) ->
    (forall a0 b c : T, f (f a0 b) c = f a0 (f b c)) ->
    (forall a0 b : T, f a0 b = f b a0) ->
  Vfold_left f a (ProdOfDiagonals a f (Vbuild (fun i (ip: i < S N) =>
    (Vbuild (fun j (jp : j < S N) => f' (Vnth A ip) (Vnth B jp)))))) =
    Vfold_left f a (Vmap (fun x => Vfold_left f a x) (Vbuild (fun i (ip: i < S N) =>
    (Vbuild (fun j (jp : j < S N) => f' (Vnth A ip) (Vnth B jp)))))).
  Proof.
    intros. induction N. rewrite ProdOfDiagonalsOne; auto. apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_map. rewrite Vhead_nth. do 3 rewrite Vbuild_nth.
   simpl. rewrite H.  apply f_equal2.
    apply Vnth_eq. lia. apply Vnth_eq. lia.
   rewrite Vfold_left_induction; auto. rewrite Vhead_map. rewrite Vbuild_head.
  symmetry. rewrite Vfold_left_eq_rev; auto. symmetry. rewrite Vtail_map.
    (* Dealing with inside *)
    assert (Vfold_left f a
     (Vmap [eta Vfold_left f a] (Vtail (Vbuild (fun (i : nat) (ip : i < S (S N)) =>
      Vbuild (fun (j : nat) (jp : j < S (S N)) => f' (Vnth A ip) (Vnth B jp)))))) =
    Vfold_left f a (Vmap2 f (Vmap (fun x => f' x (Vhead B)) (Vtail A)) (Vmap [eta Vfold_left f a] (Vbuild (fun (i : nat) (ip : i < S N) =>
      Vbuild (fun (j : nat) (jp : j < S N) => f' (Vnth (Vtail A) ip)
    (Vnth (Vtail B) jp))))))). apply f_equal. apply Veq_nth. intros. rewrite Vnth_map2.
    do 2 rewrite Vnth_map. rewrite Vfold_left_induction; auto. rewrite Vbuild_tail.
    rewrite Vbuild_nth. rewrite Vbuild_head. apply f_equal2. rewrite Vhead_nth.
    rewrite Vnth_tail. trivial. rewrite Vnth_map. rewrite Vbuild_tail. apply f_equal.
    rewrite Vbuild_nth. apply Veq_nth. intros. do 2 rewrite Vbuild_nth.
    do 2 rewrite Vnth_tail. trivial.
    (* Apply Induction hypo *)
    rewrite H2. rewrite Vfold_left_map2; auto.
    rewrite <- IHN. rewrite <- H0.
    rewrite <- Vfold_left_vapp; auto. assert (forall (c : vector T (S N + N)),
    Vfold_left f a c = Vfold_left f a (Vcons a (Vadd c a))). intros.
    rewrite VectorUtil.Vfold_left_Vcons; auto. rewrite H. rewrite Vfold_add; auto.
    rewrite H1. rewrite H. trivial.
    rewrite H3. assert (S (S (S N + N)) = Nat.add (S (S N)) (S N)). lia.
    rewrite (Vfold_left_cast_irr H4). rewrite <- Vfold_left_map2; auto.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vnth_app.
    rewrite Vnth_app. destruct (le_gt_dec (S (S N)) i).
    (* case 1 *)
    rewrite Vnth_cast. do 2 rewrite Vbuild_nth. rewrite Vnth_cons.
    destruct (lt_ge_dec 0 i). rewrite Vnth_add. destruct (Nat.eq_dec (i - 1) (S N + N)).
    rewrite Vnth_map. rewrite H1. rewrite H. assert (S (S N - (i - S (S N)) - 1) = 1%nat). lia.
    rewrite (Vfold_left_cast_irr H5). rewrite Vfold_left_head; auto.
    rewrite Vhead_cast. rewrite Vbuild_head. do 2 rewrite Vbuild_nth. apply f_equal2.
    rewrite Vnth_tail. apply Vnth_eq. lia. rewrite Vhead_nth. apply Vnth_eq. trivial.
    rewrite Vfold_left_induction; auto. apply f_equal2. rewrite Vbuild_head.
    do 2 rewrite Vbuild_nth. rewrite Vnth_map. apply f_equal2. rewrite Vnth_tail.
    apply Vnth_eq. lia. rewrite Vhead_nth. apply Vnth_eq. lia.
    rewrite Vnth_app. destruct (le_gt_dec (S N) (i - 1)). do 2 rewrite Vbuild_nth.
    assert (Nat.sub (Nat.sub (S N) (i - S (S N))) 1 = S (N - (i - 1 - S N) - 1)). lia.
    apply (Vfold_left_eq_gen H5). apply Veq_nth. intros. rewrite Vnth_cast.
    rewrite Vnth_tail. do 6 rewrite Vbuild_nth. apply f_equal2. rewrite Vnth_tail.
     apply Vnth_eq. lia. rewrite Vnth_tail. apply Vnth_eq. lia.
      (* clean up *) assert (False). lia. contradiction.
                     assert (False). lia. contradiction.
    (* case 2*)
    rewrite Vnth_cast. rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    do 3 rewrite Vbuild_nth. rewrite Vnth_add. destruct (Nat.eq_dec (i - 1) (S N + N)).
    assert (False). lia. contradiction. rewrite Vfold_left_induction; auto. apply f_equal2.
    rewrite Vbuild_head. do 2 rewrite Vbuild_nth. apply f_equal2. apply Vnth_eq. trivial.
    apply Vnth_eq. lia. rewrite Vnth_app. destruct (le_gt_dec (S N) (i - 1)).
    assert (False). lia. contradiction.
    rewrite Vbuild_nth. assert (i = S (i -1)). lia.
    apply (Vfold_left_eq_gen H5). apply Veq_nth. intros. rewrite Vnth_cast.
    rewrite Vnth_tail. do 6 rewrite Vbuild_nth. do 2 rewrite Vnth_tail.
    apply f_equal2. apply Vnth_eq. lia. apply Vnth_eq. lia.
      (* Head *)
    do 2 rewrite Vbuild_nth. assert (i = 0%nat). lia. subst.
    rewrite Vfold_left_head; auto. rewrite Vbuild_head. do 3 rewrite Vbuild_nth.
    rewrite H1. rewrite H. apply f_equal2. apply Vnth_eq. trivial. apply Vnth_eq. lia.
  Qed.

  Lemma ProdOfDiagonalsIndF : forall n N (a : VF n -> VF n ->F) (A B : vector (VF n) (S (S N)))
        (H : S (S (S N + N)) = Nat.add (S (S N)) (S N)),
    (* The product of the origional matrix *)
    ProdOfDiagonalsF (FMatrix.mat_build (fun i j (ip: i < S (S N))(jp : j < S (S N)) =>
      a (Vnth A ip) (Vnth B jp))) =
    VF_add
    (* The smaller matrix *)
    (Vcast (Vadd (Vcons 0 (ProdOfDiagonalsF (FMatrix.mat_build (fun i j (ip: i < S N)(jp : j < S N) =>
      a (Vnth (Vtail A) ip) (Vnth (Vtail B) jp))))) 0) H)
    (* The rest *)
    (Vapp (Vbuild (fun i (ip : i < S (S N)) => a (Vhead A) (Vnth B (lessIsLessShift (moreIsLess i) ip))))
     (Vbuild (fun i (ip : i < S N) => a (Vnth (Vtail A) ip) (Vhead B)))).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vnth_app.
    destruct (le_gt_dec (S (S N)) i). do 2 rewrite Vbuild_nth.
    (* Spliting on the main matrix - S (S N) <= i *)
    rewrite Vnth_cast. rewrite Vnth_add.  destruct (Nat.eq_dec i (S (S N + N))).
      (* i = S (S N + N) *)
    subst. destruct module_ring. unfold FSemiRingT.Aplus.
    rewrite Radd_0_l. rewrite Vbuild_nth. assert (S (S N - (S (S N + N) - S (S N)) - 1) = 1%nat).
    lia. unfold VF_sum. rewrite (Vfold_left_cast H0). pose VF_sum_1_head.
    unfold VF_sum in e. rewrite e. rewrite Vhead_cast. rewrite Vhead_nth.
    rewrite Vbuild_nth. rewrite FMatrix.mat_build_nth. assert (Nat.sub (S (S N + N)) (S (S N)) = N).
    lia. apply f_equal2. rewrite Vnth_tail. apply Vnth_eq.  rewrite H1. lia.
    rewrite Vhead_nth. apply Vnth_eq. trivial.
      (*  i <> S (S N + N) *)
    unfold FSemiRingT.Aplus. rewrite Vnth_cons.
    destruct (lt_ge_dec 0 i). rewrite Vnth_app. destruct (le_gt_dec (S N) (i - 1)).
    do 2 rewrite Vbuild_nth. unfold VF_sum. rewrite <- Vfold_left_Vcons_Fadd.
    assert (S (S N - (i - S (S N)) - 1) = S (S (N - (i - 1 - (S N)) - 1))). lia.
    apply (Vfold_left_eq_cast H0). apply Veq_nth. intros. rewrite Vnth_cast.
    rewrite Vbuild_nth. rewrite Vnth_cons. destruct (lt_ge_dec 0 i0).
    rewrite Vbuild_nth. do 2 rewrite FMatrix.mat_build_nth. apply f_equal2.
    rewrite Vnth_tail. apply Vnth_eq. lia. rewrite Vnth_tail. apply Vnth_eq. lia.
    rewrite FMatrix.mat_build_nth. rewrite Vbuild_nth. apply f_equal2.
    rewrite Vnth_tail. apply Vnth_eq. lia. rewrite Vhead_nth. apply Vnth_eq. lia.
    assert (False). lia. contradiction.
    assert (False). lia. contradiction.
    (* S (S N) > i *)
    do 2 rewrite Vbuild_nth. rewrite Vnth_cast. rewrite Vnth_add.
    destruct (Nat.eq_dec i (S (S N + N))).  assert (False). lia. contradiction.
    rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
      (* 0 < i *)
    rewrite Vnth_app.
    destruct (le_gt_dec (S N) (i - 1)). assert (False). lia. contradiction.
    rewrite Vbuild_nth. unfold VF_sum. rewrite <- Vfold_left_Vcons_Fadd.
    assert (S i =  S (S (i-1))). lia. apply (Vfold_left_eq_cast H0).
    apply Veq_nth. intros. rewrite Vnth_cast. rewrite Vbuild_nth.
    rewrite Vnth_cons. destruct (lt_ge_dec 0 i0). rewrite Vbuild_nth.
    do 2 rewrite FMatrix.mat_build_nth. apply f_equal2. rewrite Vnth_tail.
    apply Vnth_eq. lia. rewrite Vnth_tail. apply Vnth_eq. lia.
    rewrite FMatrix.mat_build_nth. apply f_equal2. rewrite Vhead_nth. apply Vnth_eq.
    lia. apply Vnth_eq. lia.
      (* i = 0 *)
    assert (i = 0%nat). lia. subst. pose VF_sum_1_head. unfold VF_sum in e.
    rewrite e. rewrite Vhead_nth.
    rewrite Vbuild_nth. simpl. rewrite FMatrix.mat_build_nth. destruct vs_field.
    destruct F_R. unfold FSemiRingT.Aplus. rewrite Radd_0_l. apply f_equal2.
    rewrite Vhead_nth. apply Vnth_eq. trivial. apply Vnth_eq. trivial.
  Qed.

  Lemma prod_exp : forall (n n' : nat)(a b : vector (VF n) (S n')),
    Vfold_left (VF_add (n:=n)) (VF_zero n)
      (ProdOfDiagonalsVF (Vbuild (fun (i0 : nat) (ip0 : i0 < S n') =>
      Vbuild (fun (j : nat) (jp : j < S n') => VF_mult (Vnth a ip0) (Vnth b jp)))))
     = VF_mult (Vfold_left (VF_add (n:=n)) (VF_zero n) a)
  (Vfold_left (VF_add (n:=n)) (VF_zero n) b).
  Proof.
    assert (forall n a, VF_add (VF_zero n) a = a). intros. rewrite VF_comm.
    rewrite VF_add_zero. trivial. pose VF_comm. pose VF_add_ass.
    intros. rewrite ProdOfDiagonalsSum; auto. apply VF_sum_dist.
  Qed.

  (* We use the same argument to compute commitment opening *)
  Lemma commitOpen : forall (n m : nat)(e : VF (S m))(T : Type)(f : T->VF n)
    (f' : T->F)(c : VG (S m))(h : G)(hs : VG n)(t : vector T (S m)),
    PairwisePredicate (fun c1 c2 => negb (Fbool_eq c1 c2)) e ->
    bVforall2
       (fun (a' : F) (b' : T) =>
        Gbool_eq (VG_prod (VG_Pexp c (VandermondeCol (S m) a')))
          (EPC h hs (f b') (f' b'))) e t ->
    c = comEPC h hs(FMatrix.mat_mult (VandermondeInv e) (Vmap f t))
          (Vhead (FMatrix.mat_mult [(Vmap f' t)]
    (FMatrix.mat_transpose (VandermondeInv e)))).
  Proof.
    pose module_abegrp.
    intros. symmetry. rewrite <- VG_MF_exp_row_id. apply invVandermondeLeft in H.
    rewrite <- H. rewrite <- VG_MF_exp_row_dist.
    apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vbuild_nth.
    (* Time to use the verification equation *)
    assert (VG_MF_exp_row c (Vandermonde e) = comEPC h hs (Vmap f t) (Vmap f' t)).
    apply Veq_nth. intros. apply (bVforall2_elim_nth ip0 e t) in H0.
    apply bool_eq_corr in H0. rewrite Vbuild_nth. rewrite Vnth_map2.
    do 3 rewrite Vnth_map. auto.
    (* Finished *)
    rewrite H1. rewrite Vbuild_nth. unfold VG_Pexp, VG_MF_exp_row.
    rewrite comEPCDis. unfold VG_prod.
    rewrite <- EPCMultExt. apply f_equal2. apply Veq_nth. intros.
    rewrite FMatrix.mat_mult_elem. rewrite Vfold_left_VF_add. unfold FMatrix.VA.dot_product.
    rewrite Vfold_left_Fadd_eq. apply f_equal. apply Veq_nth. intros.
    rewrite Vnth_map. do 2 rewrite Vnth_map2. do 4 rewrite Vnth_map.
    unfold FMatrix.get_row, FSemiRingT.Amult. destruct module_ring.
    apply Rmul_comm.
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq. apply f_equal.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. rewrite FMatrix.mat_transpose_row_col.
    unfold FSemiRingT.Amult, FMatrix.get_row. rewrite Vnth_map. trivial.
  Qed.

  Lemma commitOpenPC : forall (m : nat)(e : VF (S m))(T : Type)(f : T->F)
    (f' : T->F)(c : VG (S m))(h hs : G)(t : vector T (S m)),
  PairwisePredicate (fun c1 c2 => negb (Fbool_eq c1 c2)) e ->
  bVforall2 (fun (a' : F) (b' : T) => Gbool_eq (VG_prod
   (VG_Pexp c (VandermondeCol (S m) a')))
   (PC h hs (f b') (f' b'))) e t ->
  c = comPC h hs (Vhead (FMatrix.mat_mult [(Vmap f t)]
    (FMatrix.mat_transpose (VandermondeInv e)))) (Vhead (FMatrix.mat_mult [(Vmap f' t)]
    (FMatrix.mat_transpose (VandermondeInv e)))).
  Proof.
    pose module_abegrp.
    intros. symmetry. rewrite <- VG_MF_exp_row_id. apply invVandermondeLeft in H.
    rewrite <- H. rewrite <- VG_MF_exp_row_dist.
    apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vbuild_nth.
    (* Time to use the verification equation *)
    assert (VG_MF_exp_row c (Vandermonde e) = comPC h hs (Vmap f t) (Vmap f' t)).
    apply Veq_nth. intros. apply (bVforall2_elim_nth ip0 e t) in H0.
    apply bool_eq_corr in H0. rewrite Vbuild_nth. rewrite Vnth_map2.
    do 3 rewrite Vnth_map. auto.
    (* Finished *)
    rewrite H1. do 2 rewrite Vbuild_nth. unfold VG_Pexp. rewrite comPCDis.
    unfold VG_prod. rewrite <- PCMultExt. apply f_equal2.
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq. apply f_equal.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. rewrite FMatrix.mat_transpose_row_col.
    unfold FSemiRingT.Amult, FMatrix.get_row. rewrite Vnth_map. trivial.
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq. apply f_equal.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. rewrite FMatrix.mat_transpose_row_col.
    unfold FSemiRingT.Amult, FMatrix.get_row. rewrite Vnth_map. trivial.
    
  Qed.

  (* Casting amd misc -
      this needs to be shared with other BG sub *)

  Definition RF_inProd (N : nat)(a : VF N)(b : MoR.VF N) : Ring.F :=
    Vfold_left Ring.Fadd Ring.Fzero (Vmap2 MVS.op3 b a).

  Definition RF_VCmult (N : nat)(M : MF N)(v : MoR.VF N) : MoR.VF N :=
    Vmap (fun a => RF_inProd a v) M.

  Lemma castingM0 : Nat.add 1 (m - 1)
    = m.
  Proof.
    intros. unfold m. cbn. lia.
  Qed.

  Lemma castingM : Nat.add m (Nat.add 1 (m - 1))
    = Nat.add m m.
  Proof.
    intros. unfold m. cbn. lia.
  Qed.

  Lemma castingM3 : Nat.add 1 (Nat.sub (Nat.mul 2 m) 1)
      = Nat.add m m.
  Proof.
    unfold m. lia.
  Qed.

  Lemma castingM4 : Nat.mul 2 m =
     Nat.add (Nat.add 1 m) (Nat.sub m 1).
  Proof.
    unfold m. lia.
  Qed.

  Lemma castingM5 : S (S (M.N + S (S (M.N + 0)))) =
    Nat.add m m.
  Proof.
    unfold m. lia.
  Qed.

  Lemma castingM7 : Nat.add m m = S (S (M.N + S (S (M.N + 0)))).
  Proof.
    unfold m. lia.
  Qed.

  Lemma castingM6 : Nat.mul 2 m =
    Nat.add m m.
  Proof.
    unfold m. lia.
  Qed.

  Lemma castingM8 : forall j,
      Nat.add(S j) (S j) = Nat.add j (S (S j)).
  Proof.
    lia.
  Qed.

  Theorem index0 : Nat.lt 0%nat n.
  Proof.
    unfold n. cbn. apply neq_0_lt. auto.
  Defined.

  Theorem indexM : Nat.lt m (m+m).
  Proof.
    cbn. unfold Nat.lt. lia.
  Defined.

  Lemma indexMhead : forall A (v : vector A (m+m)),
    Vnth v indexM = Vhead (Vbreak v).2.
  Proof.
    intros. rewrite Vhead_nth. rewrite Vnth_vbreak_2. lia. intros.
    apply Vnth_eq. lia.
  Qed.

  Theorem indexSM : Nat.lt (S m) ((S m)+m).
  Proof.
    cbn. unfold Nat.lt. unfold m. lia.
  Defined.

  Lemma EkGenIndexFirstI: forall (i l : nat),
     i < l -> 0 + (1+i) <= l.
  Proof.
    intros. lia.
  Qed.

  Lemma EkGenIndexLastI : forall (i l : nat),
     i < l -> (l-(1+i)) + (1+i) <= l.
  Proof.
    intros. lia.
  Qed.

  Lemma makeSVectorsIndexRev : forall (i l : nat),
    i < l -> (l-i-1) + (1+l) <= l+l.
  Proof.
    intros. lia.
  Qed.

  (* Inital lemmas *)
  Lemma TheSMdiagindexSM : forall (T : Type)(a : T)(f : T->T->T)
     (A : vector (vector T (S m)) (S m)),
    Vnth (ProdOfDiagonals a f A) indexSM =
      Vfold_left f a (Vbuild (fun i (ip : i < m) =>
        Vnth (Vremove_last (Vnth (Vtail A) ip)) ip)).
  Proof.
    intros. assert (Vnth (ProdOfDiagonals a f A) indexSM = Vhead (Vbreak (ProdOfDiagonals a f A)).2).
    rewrite Vhead_nth. rewrite Vnth_vbreak_2. lia. intros. apply Vnth_eq. lia.
    rewrite H. apply TheSMdiag.
  Qed.

  Lemma TheSMinfold : forall (T : Type)(a : T)(f : T->T->T)
     (A : vector (vector T (S m)) (S m)),
  Vcons (Vnth (ProdOfDiagonals a f A) indexSM)
        (Vtail (Vbreak (ProdOfDiagonals a f A)).2) = (Vbreak (ProdOfDiagonals a f A)).2.
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    rewrite Vnth_tail. apply Vnth_eq. lia. rewrite Vnth_vbreak_2. lia. intros.
    apply Vnth_eq. lia.
  Qed.


  (* Start crazy stuff - this function exists to generate the vector under
    the exponent on the right *)

  Definition WeirdCs (a j : nat)(cBar : vector (vector Ciphertext.G a) j)
      (a : vector (VF a) (1+j)) : MoC.VG (j+j) :=
    let first := Vbuild (fun i (ip : i < j) => MoC.VG_prod (Vmap2 (fun x y =>
         MoC.VG_prod (MoC.VG_Pexp x y))
      (Vsub cBar (EkGenIndexLastI ip)) (Vsub a (EkGenIndexFirstI (le_S ip))))) in
    let second := Vbuild (fun i (ip : i < j) => MoC.VG_prod (Vmap2 (fun x y =>
        MoC.VG_prod (MoC.VG_Pexp x y))
      (Vsub cBar (EkGenIndexFirstI ip)) (Vsub a (EkGenIndexLastI (le_S ip))))) in
    Vapp first (rev second).

  Lemma WeirdCs_one : forall (cBar : vector (vector Ciphertext.G n) 1)
    (a : vector (VF n) 2),
  WeirdCs cBar a =
    Vmap (fun x => MoC.VG_prod (MoC.VG_Pexp (Vhead cBar) x)) a.
  Proof.
    intros. unfold WeirdCs. apply Veq_nth. intros. rewrite Vnth_app.
    destruct (le_gt_dec 1 i). do 2 rewrite Vbuild_nth. rewrite Vnth_map.
    assert (i = 1%nat). lia. subst. rewrite MoC.VG_prod_one_vec.
    do 2 rewrite Vhead_nth. rewrite Vnth_map2. apply Vfold_left_eq.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. apply f_equal2.
    rewrite Vnth_sub. apply Veq_nth3; auto. apply Vnth_eq. lia.
    rewrite Vnth_sub. apply Veq_nth3; auto. apply Vnth_eq. lia.
    (* part 2 *)
    rewrite Vbuild_nth. rewrite Vnth_map. assert (i = 0%nat). lia.
    subst. rewrite MoC.VG_prod_one_vec.
    do 2 rewrite Vhead_nth. rewrite Vnth_map2. apply Vfold_left_eq.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. apply f_equal2.
    rewrite Vnth_sub. apply Veq_nth3; auto. apply Vnth_eq. lia.
    rewrite Vnth_sub. apply Veq_nth3; auto. apply Vnth_eq. lia.
  Qed.
  
  Lemma WeirdCs_induct : forall (j : nat)(cBar : vector
    (vector Ciphertext.G n) (S j))(a : vector (VF n) (S (S j)))(b : VF ((S j)+(S j))),
    MoC.VG_prod (MoC.VG_Pexp (WeirdCs cBar a) b) =
    Ciphertext.Gdot (Ciphertext.Gdot (MoC.VG_prod (MoC.VG_Pexp
    (WeirdCs (Vtail cBar) (Vtail a))(double_induct b)))
    (* and what's left *)
  (MoC.VG_prod (MoC.VG_Pexp (Vmap (fun xi => MoC.VG_prod (MoC.VG_Pexp xi (Vhead a)))
  (rev (Vtail cBar))) (Vbreak (Vcast b (castingM8 j))).1)))
  (MoC.VG_prod (MoC.VG_Pexp (Vmap (fun y => MoC.VG_prod (MoC.VG_Pexp (Vhead cBar) y))
   a) (Vbreak (Vcast b (castingM8 j))).2)).
  Proof.
    pose Ciphertext.module_abegrp. intros. rewrite <- dot_assoc.
    rewrite <- MoC.Vapp_VG_prod.
    (* It is usefult to deal with the case where j = 0 first *)
    destruct (Nat.eq_dec j 0). subst. rewrite (Vector_0_is_nil (Vtail cBar)).
    rewrite Vnth_map_nil. rewrite (Vector_0_is_nil (Vbreak (Vcast b (castingM8 0))).1).
    unfold MoC.VG_Pexp. rewrite Vnth_map2_nil. rewrite MoC.VG_prod_zero.
    rewrite one_left. apply Vfold_left_eq. apply Veq_nth. intros.
    do 2 rewrite Vnth_map2. rewrite Vnth_map. rewrite Vnth_vbreak_2. lia.
    intros. rewrite WeirdCs_one. rewrite Vnth_map. apply f_equal2; trivial.
    rewrite Vnth_cast. apply Vnth_eq. lia.
    (* Resuming main *)
    assert (S (S (Nat.add j j)) =
    Nat.add j (S (S j))). lia.
    (* sub lemma about cleaning up the product *)
    assert (MoC.VG_prod (MoC.VG_Pexp
    (WeirdCs (Vtail cBar) (Vtail a0))(double_induct b)) =
    MoC.VG_prod (Vcast (Vcons Ciphertext.Gone (Vadd (MoC.VG_Pexp (WeirdCs (Vtail cBar) (Vtail a0))
        (double_induct b)) Ciphertext.Gone)) H)). rewrite <- MoC.VG_prod_cast.
    rewrite MoC.VG_prod_Vcons. rewrite one_right. rewrite MoC.VG_prod_add.
    rewrite one_right. trivial.
    (* Resuming main *)
    rewrite H0. rewrite <- MoC.VG_Prod_mult_dist.
    assert (Nat.add j (S (S j)) = Nat.add (S j) (S j)). lia.
    rewrite (MoC.VG_prod_cast H1). apply Vfold_left_eq. apply Veq_nth. intros.
    (* Proving for each diagional *)
    rewrite Vnth_cast. do 2 rewrite Vnth_map2. rewrite Vnth_app.
    rewrite Vnth_cast. destruct (le_gt_dec j i).
    (* *)
    (* First we split on the diagonal 1/2 *)
    (* *)
    assert (i>0). lia. rewrite (Vnth_cons_tail); auto.
    (* Breaking on final position *)
    rewrite Vnth_add. destruct (Nat.eq_dec (i - 1) (j + j)). rewrite one_left.
    rewrite Vnth_map2. apply f_equal2. rewrite Vnth_map. unfold WeirdCs.
    rewrite Vnth_app. destruct (le_gt_dec (S j) i). do 2 rewrite Vbuild_nth.
    assert (i = Nat.add (Nat.add j j) 1). lia. subst.
    rewrite MoC.VG_prod_one_vec_gen. rewrite Vhead_nth. rewrite Vnth_map2.
    apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    apply f_equal2. rewrite Vhead_nth. apply Veq_nth3; auto. rewrite Vnth_sub.
    apply Vnth_eq. lia. apply Veq_nth3; auto. rewrite Vnth_sub. apply Vnth_eq. lia.
    lia.  lia. rewrite Vnth_vbreak_2. lia. intros. rewrite Vnth_cast. apply Vnth_eq.
    lia.
    (* Non final position *)
    do 2 rewrite Vnth_map2. rewrite <- ALVS1.mod_dist_Gdot_eq. apply f_equal2.
    rewrite Vnth_map. unfold WeirdCs. rewrite Vnth_app. destruct (le_gt_dec (S j) i).
    do 2 rewrite Vbuild_nth. rewrite Vnth_app. destruct (le_gt_dec j (i - 1)).
    do 2 rewrite Vbuild_nth. symmetry. rewrite <- MoC.VG_prod_Vcons.
    assert (S (1 + (j - (i - 1 - j) - 1)) = Nat.add 1 (Nat.sub (Nat.sub (S j) (i - S j)) 1%nat)). lia.
    rewrite (MoC.VG_prod_cast H3). apply Vfold_left_eq. apply Veq_nth.
    intros. rewrite Vnth_map2. rewrite Vnth_cast. rewrite Vnth_cons. destruct (lt_ge_dec 0 i0).
    rewrite Vnth_map2. apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    apply f_equal2. do 2 rewrite Vnth_sub. apply Veq_nth3; auto.
    rewrite Vnth_tail. apply Vnth_eq. lia. do 2 rewrite Vnth_sub.
    apply Veq_nth3; auto. rewrite Vnth_tail. apply Vnth_eq. lia.
    apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    apply f_equal2. rewrite Vnth_sub. apply Veq_nth3; auto. rewrite Vhead_nth.
    apply Vnth_eq. lia. rewrite Vnth_sub. apply Veq_nth3; auto.
    apply Vnth_eq. lia.
    assert (false). lia.
    discriminate. assert (j = i). lia. subst. rewrite Vbuild_nth.
    rewrite Vnth_app. destruct (le_gt_dec i (i - 1)). assert (false). lia.
    discriminate. rewrite Vbuild_nth. rewrite <- MoC.VG_prod_Vcons.
    assert (S (1 + (i - 1)) = Nat.add 1 i). lia.
    rewrite (MoC.VG_prod_cast H3). apply Vfold_left_eq. apply Veq_nth. intros.
    rewrite Vnth_map2. rewrite Vnth_cast. rewrite Vnth_cons.
    destruct (lt_ge_dec 0 i0). rewrite Vnth_map2. apply Vfold_left_eq.
    apply Veq_nth.  intros. do 2 rewrite Vnth_map2. apply f_equal2.
    do 2 rewrite Vnth_sub. rewrite Vnth_tail. apply Veq_nth3; auto.
    apply Vnth_eq. lia.  do 2 rewrite Vnth_sub. rewrite Vnth_tail.
    apply Veq_nth3; auto. apply Vnth_eq. lia. do 2 rewrite Vnth_sub.
    apply Vfold_left_eq. apply f_equal2. rewrite Vhead_nth. apply Vnth_eq.
    lia. apply Vnth_eq. lia.
      (* Clean up *)
    rewrite Vnth_remove_last. rewrite Vnth_tail. rewrite Vnth_cast.
    apply Vnth_eq. lia. rewrite Vnth_vbreak_2. lia. intros. rewrite Vnth_remove_last.
    rewrite Vnth_tail. do 2 rewrite Vnth_cast. apply Vnth_eq. lia.
    (* *)
    (* split on the diagonal 2/2 *)
    (* *)
    rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    (* main case *)
    rewrite Vnth_add. destruct (Nat.eq_dec (i - 1) (j + j)). assert (false).
    lia. discriminate. do 2 rewrite Vnth_map2. rewrite Vnth_map. rewrite <- ALVS1.mod_dist_Gdot_eq.
    unfold double_induct. rewrite Vnth_remove_last. rewrite Vnth_tail.
    apply f_equal2. unfold WeirdCs. rewrite Vnth_app. destruct (le_gt_dec (S j) i).
    (* Main case 1/2  *)
    rewrite Vnth_app. destruct (le_gt_dec j (i - 1)).
    do 4 rewrite Vbuild_nth. rewrite <- MoC.VG_prod_Vcons.
    assert (S (1 + (j - (i - 1 - j) - 1)) = Nat.add 1 (Nat.sub (Nat.sub (S j) (i - S j)) 1%nat)). lia.
    rewrite (MoC.VG_prod_cast H2). apply Vfold_left_eq. apply Veq_nth.
    intros. rewrite Vnth_map2. rewrite Vnth_cast. rewrite Vnth_cons.
    destruct (lt_ge_dec 0 i0). rewrite Vnth_map2. do 4 rewrite Vnth_sub.
    apply Vfold_left_eq. apply f_equal2. rewrite Vnth_tail. apply Vnth_eq. lia.
    rewrite Vnth_tail. apply Vnth_eq. lia. apply Vfold_left_eq. apply f_equal2.
    rewrite Vnth_sub. rewrite Vbuild_nth. rewrite Vnth_tail. apply Vnth_eq. lia.
    rewrite Vnth_sub. rewrite Vhead_nth. apply Vnth_eq. lia.
    assert (false). lia.  discriminate.
    (*  Main case 2/2  *)
    rewrite Vnth_app. destruct (le_gt_dec j (i - 1)). assert (false).
    lia. discriminate. do 2 rewrite Vbuild_nth. rewrite <- MoC.VG_prod_Vcons.
    assert (S (1 + (i - 1)) = Nat.add 1 i). lia.
    rewrite (MoC.VG_prod_cast H2). apply Vfold_left_eq. apply Veq_nth.
    intros. rewrite Vnth_map2. rewrite Vnth_cast. rewrite Vnth_cons.
    destruct (lt_ge_dec 0 i0). rewrite Vnth_map2. do 4 rewrite Vnth_sub.
    apply Vfold_left_eq. apply f_equal2. rewrite Vnth_tail. apply Vnth_eq. lia.
    rewrite Vnth_tail. apply Vnth_eq. lia. apply Vfold_left_eq. apply f_equal2.
    rewrite Vnth_sub. rewrite Vbuild_nth. rewrite Vnth_tail. apply Vnth_eq. lia.
    rewrite Vnth_sub. rewrite Vhead_nth. apply Vnth_eq. lia.
    (*resume*)
    rewrite Vnth_cast. apply Vnth_eq. lia.
    unfold double_induct. rewrite Vnth_remove_last. rewrite Vnth_tail.
    rewrite Vnth_vbreak_1. lia. intros. do 2 rewrite Vnth_cast. apply Vnth_eq. lia.
    (* i = 0 *)
    assert (i = 0%nat). lia. rewrite one_left. rewrite Vnth_map2.
    rewrite Vnth_map. unfold WeirdCs. rewrite Vnth_app. destruct (le_gt_dec (S j) i).
    assert (false). lia. discriminate. rewrite Vbuild_nth. apply f_equal2.
    subst. rewrite MoC.VG_prod_one_vec_gen. rewrite Vhead_nth.
    rewrite Vnth_map2. do 2 rewrite Vnth_sub. rewrite Vbuild_nth.
    rewrite Vnth_tail. apply Vfold_left_eq. apply Veq_nth. intros.
    do 2 rewrite Vnth_map2. apply f_equal2. apply Veq_nth3; auto.
    apply Vnth_eq. lia. apply Veq_nth3; auto. rewrite Vhead_nth.
    apply Vnth_eq. lia. lia. rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_cast.
    apply Vnth_eq. lia.
  Qed.

  Lemma WeirdCs_Expand_sub : forall (b c : nat)(cBar : vector (vector Ciphertext.G n) b)
      (e : F)(Aj : vector (VF n) (S b)),
    MoC.VG_prod (Vbuild (fun i (ip : i < b) =>
      MoC.VG_prod (MoC.VG_Pexp (Vnth cBar ip)
      (Vhead (FMatrix.mat_mult [VandermondeColGen (S b) e (b - i + c - 1)] Aj))))) =
    MoC.VG_prod (MoC.VG_Pexp (WeirdCs cBar Aj)(VandermondeColGen (b + b) e c)).
  Proof.
    (* Base case *)
    induction b. intros. cbn. trivial.
    (* Main case *)
    intros. rewrite WeirdCs_induct. rewrite VandermondeCol_induct.
    rewrite <- IHb. rewrite MoC.VG_prod_induction. apply f_equal2.
    (* Tacking matrix less top row *)
    rewrite MoC.VG_prod_rev. symmetry. rewrite MoC.VG_prod_rev.
    rewrite <- MoC.VG_Prod_mult_dist.
    apply Vfold_left_eq.
    (* Prove for each row *)
    apply Veq_nth. intros. rewrite Vbuild_nth. rewrite Vnth_tail.
    rewrite Vnth_map2. do 3 rewrite Vbuild_nth. rewrite Vnth_map2.
    rewrite Vnth_map. rewrite MoC.Sexp_dist0. rewrite <- MoC.VG_Prod_mult_dist.
    apply Vfold_left_eq. apply Veq_nth.
    intros. rewrite Vbuild_nth. do 3 rewrite Vnth_map2.
    rewrite Vnth_map. rewrite Vnth_map2. rewrite <- VS1.mod_dist_Fmul.
    do 2 rewrite Vbuild_nth. rewrite <- VS1.mod_dist_Fadd. rewrite Vnth_tail.
    apply f_equal2; auto.
    unfold FMatrix.VA.dot_product. do 2 rewrite Vfold_left_Fadd_eq.
    rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_cast.
    rewrite <- Vfold_left_Vcons_Fadd; auto.
    apply Vfold_left_eq. apply Veq_nth.
    intros. rewrite Vnth_cons. destruct (lt_ge_dec 0 i1).
    (* Breaking across the exp *)
    do 2 rewrite Vnth_map2. apply f_equal2. do 2 rewrite Vbuild_nth.
    apply VG_prod_const_index. lia.
    do 2 rewrite Vnth_map. rewrite Vnth_tail. apply Veq_nth3; auto.
    apply Vnth_eq. lia.
    (* First point *)
    rewrite Vnth_map2. apply f_equal2. do 2 rewrite Vbuild_nth.
    apply VG_prod_const_index. lia. rewrite Vhead_nth. rewrite Vnth_map.
    apply Veq_nth3; auto. apply Vnth_eq. lia.
     
    (* Main case top row *)
    do 2 rewrite Vhead_nth. rewrite Vbuild_nth.
    rewrite MoC.double_exp_over_fixed_base. rewrite MoC.Vmap_prod_pexp.
    apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    apply f_equal2; auto. rewrite Vhead_nth. rewrite Vnth_map.
    rewrite FMatrix.mat_mult_elem. unfold FMatrix.VA.dot_product.
    rewrite Vfold_left_Fadd_eq. apply Vfold_left_eq. apply Veq_nth.
    intros. rewrite FMatrix.mat_build_nth. rewrite Vnth_map2.
    unfold FMatrix.get_elem, FMatrix.get_row. rewrite Vnth_map2.
    do 2 rewrite Vnth_map. destruct module_ring. rewrite Rmul_comm.
    apply f_equal2. rewrite Vnth_vbreak_2. lia. intros. rewrite Vnth_cast.
    do 2 rewrite Vbuild_nth. apply VG_prod_const_index. lia. trivial.
  Qed.
  
  Lemma WeirdCs_Expand : forall (b : nat)(cBar : vector (vector Ciphertext.G n) b)
      (e : F)(Aj : vector (VF n) (S b)),
    MoC.VG_prod (Vmap2 (fun (Ci : MoC.VG n) (xi : F) =>
      MoC.VG_prod (MoC.VG_Pexp Ci (VF_scale (Vhead (FMatrix.mat_mult
      [VandermondeCol (S b) e] Aj)) xi))) cBar
     (rev (VandermondeCol b e)))
      =
    MoC.VG_prod (MoC.VG_Pexp (WeirdCs cBar Aj) (VandermondeCol (b + b) e)).
  Proof.
    intros. assert (MoC.VG_prod (Vmap2 (fun (Ci : MoC.VG n) (xi : F) =>
    MoC.VG_prod (MoC.VG_Pexp Ci (VF_scale (Vhead (FMatrix.mat_mult
    [VandermondeCol (S b) e] Aj)) xi))) cBar (rev (VandermondeCol b e))) =
    MoC.VG_prod (Vbuild (fun i (ip :  i < b) => MoC.VG_prod (MoC.VG_Pexp (Vnth cBar ip)
   (Vhead (FMatrix.mat_mult  [VandermondeColGen (S b) e (b-i-1)] Aj)))))).
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vbuild_nth. apply f_equal. apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vhead_nth.
    do 2 rewrite FMatrix.mat_mult_elem. destruct module_ring.
    rewrite Rmul_comm. pose FMatrix.VA.dot_product_distr_mult.
    unfold FSemiRingT.Amult in e0. rewrite e0. apply f_equal2; auto.
    apply Veq_nth. intros. rewrite Vbuild_nth. unfold FMatrix.get_row.
    rewrite Vbuild_nth. do 3 rewrite Vbuild_nth.
    rewrite VF_prod_const. assert (Nat.add (Nat.sub (Nat.sub b i) 1) i1 =
    (Nat.add i1 (Nat.sub (Nat.sub b i) 1))). lia. rewrite H. trivial.
    rewrite H. rewrite VandermondeColGe_eq. assert (Vbuild
     (fun (i : nat) (ip : i < b) => MoC.VG_prod
     (MoC.VG_Pexp (Vnth cBar ip) (Vhead (FMatrix.mat_mult
     [VandermondeColGen (S b) e (b - i - 1)] Aj)))) = Vbuild
     (fun (i : nat) (ip : i < b) => MoC.VG_prod (MoC.VG_Pexp (Vnth cBar ip)
     (Vhead (FMatrix.mat_mult [VandermondeColGen (S b) e (b - i + 0 - 1)] Aj))))).
    apply Veq_nth. intros. do 2 rewrite Vbuild_nth. apply Vfold_left_eq.
    apply f_equal2; auto. apply f_equal. apply f_equal2; auto. apply Vcons_eq.
    split; auto. apply f_equal. lia. rewrite H0. rewrite WeirdCs_Expand_sub. trivial.
  Qed.
  (* End crazy stuff *)

  Definition EkGeneratorsSub
    (j : nat)(cBar : vector (vector Ciphertext.G n) j)
      (A : vector (VF n) j) : MoC.VG j :=
    Vbuild (fun i (ip : i < j) =>
              (* C_i,...,C_(l-j) *)
              let cBarSub := Vsub cBar (EkGenIndexLastI ip)  in
              (* A_0,...,A_(i-1) *)
              let Asub := Vsub A (EkGenIndexFirstI ip) in
      MoC.VG_prod (Vmap2 (fun x y =>
             MoC.VG_prod (MoC.VG_Pexp x y)) cBarSub Asub)
    ).

  (* EkGeneratorSub rearranged *)
  Definition EkGeneratorsSubAlt
      (j : nat)(cBar : vector (vector Ciphertext.G n) j)
      (A : vector (VF n) j)(x : VF j) : MoC.VG j :=
      Vbuild (fun i (ip : i < j) =>
         MoC.VG_prod (Vmap (fun y => MoC.VG_prod
          (* C_i^(x_(j-i)a_1+...+x_(j)a_i *)
          (MoC.VG_Pexp (Vnth cBar ip) y)) (Vmap2 (VF_scale (n:=n))
      (Vsub A (EkGenIndexFirstI ip))
         (Vsub x (EkGenIndexLastI ip))))).

  Lemma EkGeneratorsSubAltTail : forall (j : nat)(A : vector (VF n) (S j))
    (cBar : vector (vector Ciphertext.G n) (S j))(x : VF (S j)),
    Vremove_last (EkGeneratorsSubAlt cBar A x) =
      EkGeneratorsSubAlt (Vremove_last cBar) (Vremove_last A) (Vtail x).
   Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_remove_last.
      do 2 rewrite Vbuild_nth. rewrite Vnth_remove_last.
      apply Vfold_left_eq. apply Veq_nth. intros.
      do 2 rewrite Vnth_map. apply Vfold_left_eq. apply Veq_nth.
      intros. do 4 rewrite Vnth_map2. apply ALVS1.scaleEq.
      do 2 rewrite Vnth_map. do 4 rewrite Vnth_sub.
      apply ALVS1.F_mul_split. rewrite Vnth_remove_last.
      apply Veq_nth2. apply Vnth_eq. trivial.
      rewrite Vnth_tail. apply Vnth_eq. lia.
    Qed.

   Lemma EkGenSubComb : forall (j : nat)(A : vector (VF n) (S j))
    (cBar : vector (vector Ciphertext.G n) j)(x : VF (j+j)),
    Vmap2 Ciphertext.Gdot
      (* c_0^(a_0*x_2),...,c_2^(a_0x_0+...+a_2x_2) *)
      (EkGeneratorsSubAlt cBar (Vremove_last A) (Vbreak x).1)
      (* c_0^(a_1x_3+...,a_3x_5),...,c_2^(a_3x_3) *)
     (rev (EkGeneratorsSubAlt (rev cBar) (rev (Vtail A))(rev (Vbreak x).2)))
        = Vbuild (fun i (ip : i < j) =>
        (* x_(j-i),...x_(j+j) *)
        let xSub := Vsub x (makeSVectorsIndexRev ip) in
        (* A_0,...,A_(i-1) *)
         let Asub := Vmap2 (VF_scale (n:=n)) A xSub in
         MoC.VG_prod (Vmap (fun y => MoC.VG_prod
          (MoC.VG_Pexp (Vnth cBar ip) y)) Asub)).
   Proof.
    pose Ciphertext.module_abegrp.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 5 rewrite Vbuild_nth.
    rewrite comm. rewrite MoC.VG_prod_rev. rewrite comm. rewrite <- MoC.Vapp_VG_prod.
    (* Ready to break down *)
    assert (Nat.add (Nat.add 1 i) (Nat.add 1 (Nat.sub (Nat.sub j i) 1)) = S j). lia.
    rewrite (MoC.VG_prod_cast H). apply Vfold_left_eq.
    apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_cast.
    rewrite Vnth_app. destruct (le_gt_dec (1 + i) i0).
    (* Moving into base case *)
    rewrite Vbuild_nth. rewrite Vnth_map. rewrite invertPosCancel. unfold MoC.VG_prod.
    apply Vfold_left_eq. apply Veq_nth. intros. do 4 rewrite Vnth_map2.
    (* Down to the inner product *)
    apply ALVS1.scaleEq. do 2 rewrite Vnth_map. apply ALVS1.F_mul_split.
    apply Veq_nth2. rewrite Vnth_sub. rewrite Vbuild_nth. rewrite Vnth_tail.
    apply Vnth_eq. lia.
    (* Other part of exp *)
    rewrite Vnth_sub. rewrite Vbuild_nth. rewrite Vnth_vbreak_2. lia.
    intros. rewrite Vnth_sub. apply Vnth_eq. lia.
    (* Onwards *)
    rewrite Vnth_map2. rewrite Vnth_map.  apply Vfold_left_eq. apply Veq_nth.
    intros. do 3 rewrite Vnth_map2. apply ALVS1.scaleEq. do 2 rewrite Vnth_map.
    apply ALVS1.F_mul_split. apply Veq_nth2. rewrite Vnth_sub. rewrite Vnth_remove_last.
    apply Vnth_eq. lia. rewrite Vnth_sub. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_sub. apply Vnth_eq. lia.
   Qed.

  (* The proof of this is harder than expected *)
   Lemma EkGenSubAltEq : forall (j : nat)(A : vector (VF n) j)
    (cBar : vector (vector Ciphertext.G n) j)(x : VF j),
      MoC.VG_prod (MoC.VG_Pexp (EkGeneratorsSub cBar A) x) =
      MoC.VG_prod (EkGeneratorsSubAlt cBar A x).
   Proof.
    pose Ciphertext.module_abegrp.
    intros. induction j. cbn. trivial. symmetry.
    rewrite MoC.VG_prod_rev. rewrite MoC.VG_prod_induction.
    rewrite rev_tail_last. rewrite EkGeneratorsSubAltTail.
    rewrite <- MoC.VG_prod_rev. rewrite <- IHj.
    (* Induction Hypotsis applied *)
    rewrite Vhead_nth. do 2 rewrite Vbuild_nth.
    do 2 rewrite MoC.VG_prod_induction. symmetry.
    rewrite <- MoC.VG_prod_induction. symmetry.
    rewrite dot_assoc. assert (Nat.sub (Nat.sub (S j)
    0) 1 = j). lia. rewrite (MoC.VG_prod_cast H).
    rewrite <- MoC.VG_Prod_mult_dist. rewrite <- MoC.VG_prod_Vcons.
    apply Vfold_left_eq.
    apply Veq_nth. intros. rewrite Vnth_cons. destruct (lt_ge_dec 0 i).
    (* We have now rearranged sub and broken to main case *)
    do 3 rewrite Vnth_map2. rewrite Vnth_cast. do 2 rewrite Vnth_tail.
    rewrite Vnth_map. rewrite Vnth_map2. rewrite <- MoC.VG_prod_VG_Pexp_scale.
    do 2 rewrite Vnth_sub. assert (Vnth x (lt_n_S (Vnth_cons_tail_aux ip l)) =
    Vnth x ip). apply Vnth_eq. lia. rewrite H0. assert (Vnth x
    (Vnth_sub_aux (S j - (1 + (S j - 0 - 1))) (EkGenIndexLastI
    (invertPos (Nat.lt_0_succ j)))(lt_n_S (Vnth_cast_aux H
    (Vnth_cons_tail_aux ip l)))) = Vnth x ip). apply Vnth_eq.
    destruct i. pose (lt_le_S l). lia. lia. rewrite H1.
    rewrite <- VS1.mod_dist_Gdot. apply ALVS1.scaleEqFull.
    do 2 rewrite Vbuild_nth. rewrite <- MoC.VG_prod_add.
    assert (S (Nat.add 1 (Nat.sub i 1)) = Nat.add 1 i). pose (lt_le_S l).
    lia. rewrite (MoC.VG_prod_cast H2). apply Vfold_left_eq.
    apply Veq_nth. intros. rewrite Vnth_cast. rewrite Vnth_map2.
    rewrite Vnth_add. destruct (Nat.eq_dec i0 (1 + (i - 1))).
    (* Clean up inner base *)
    subst. do 2 rewrite Vnth_sub. apply Vfold_left_eq. apply Veq_nth. intros.
    do 2 rewrite Vnth_map2.
    apply ALVS1.scaleEqFull. apply Veq_nth3. trivial.
    apply Vnth_eq. rewrite H. assert (Nat.add 1 (Nat.sub i 1) = i).
    lia. rewrite H3. pose (lt_le_S ip). lia. apply Veq_nth3. trivial.
    apply Vnth_eq. lia.
    (* The middle *)
    rewrite Vnth_map2. do 6 rewrite Vnth_sub. apply Vfold_left_eq.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. apply ALVS1.scaleEqFull.
    apply Veq_nth3. trivial. apply Vnth_eq. lia. apply Veq_nth3.
    trivial. apply Veq_nth3. lia. trivial. trivial.
    (* Clearing base case *)
    assert (i = 0%nat). lia. subst. rewrite Vhead_nth. rewrite Vnth_map.
    do 2 rewrite Vnth_map2. rewrite Vbuild_nth. rewrite MoC.Sexp_dist0.
    rewrite MoC.VG_prod_one. rewrite MoC.Sexp_dist0. apply Vfold_left_eq.
    apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vnth_map.
    rewrite Vnth_map2. rewrite <- VS1.mod_dist_Fmul. apply ALVS1.scaleEqFull.
    rewrite Vhead_nth. rewrite Vnth_sub. apply Veq_nth3. trivial.
    apply Vnth_eq. lia. destruct module_ring. rewrite Rmul_comm.
    apply ALVS1.F_mul_split. rewrite Vnth_sub. apply Vnth_eq. lia.
    apply Veq_nth3. trivial. rewrite Vhead_nth. do 2 rewrite Vnth_sub.
    apply Vnth_eq. lia.
  Qed.

  Definition EkGenerators (pk : enc.PK)(l : nat)
    (g : enc.M)(cBar : (vector (vector Ciphertext.G n) l))
    (a0 : (vector (VF n) (1+l)))(tau : vector Ring.F (l+l))
    (b : VF (l+l))(x : VF (l+l)) :=

      let E1 := Vmap2 (fun x y => enc.enc pk (VS3.op g x) y) b tau in

      (* E_0,...,E_(m-1) : m elements *)
      let Epre := EkGeneratorsSub cBar (Vremove_last a0) in
      (* E_(m),...,E_(2*m-1) : m-1 elements *)
      let Epost := rev (EkGeneratorsSub (rev cBar) (rev (Vtail a0))) in

      let E2 := Vapp Epre Epost in
    
      Vmap2 Ciphertext.Gdot E1 (MoC.VG_Pexp E2 x).

  Definition EkGeneratorsSubRawM (j : nat)(Ca : vector (VF n) j)
      (A : vector (VF n) j) : VF j :=
    Vbuild (fun i (ip : i < j) =>
              (* C_i,...,C_(l-j) *)
              let cBarSub := Vsub Ca (EkGenIndexLastI ip)  in
              (* A_0,...,A_(i-1) *)
              let Asub := Vsub A (EkGenIndexFirstI ip) in
      VF_sum (Vmap2 (fun x y =>
             VF_sum (VF_mult x y)) cBarSub Asub)
    ).


  Definition EkGeneratorsSubRawR(j : nat)(Ctau : vector (vector Ring.F n) j)
      (A : vector (VF n) j) : vector Ring.F j :=
    Vbuild (fun i (ip : i < j) =>
              (* C_i,...,C_(l-j) *)
              let cBarSub := Vsub Ctau (EkGenIndexLastI ip)  in
              (* A_0,...,A_(i-1) *)
              let Asub := Vsub A (EkGenIndexFirstI ip) in
      MoR.VF_sum (Vmap2 (fun x y =>
             MoR.VF_sum (Vmap2 MVS.op3 x y)) cBarSub Asub)
    ).


  Definition EkGeneratorsRawM (l : nat)
    (Ca : vector (VF n) l)
    (a0 : (vector (VF n) (1+l)))
    (b : VF (l+l))  :=

      let messagePre := EkGeneratorsSubRawM Ca (Vremove_last a0) in
      let messagePost := rev (EkGeneratorsSubRawM (rev Ca) (rev (Vtail a0))) in

      VF_add b (Vapp messagePre messagePost).

  Definition EkGeneratorsRawR (l : nat)
    (Ctau : vector (vector Ring.F n) l)
    (a0 : (vector (VF n) (1+l)))(tau : vector Ring.F (l+l)) :=

      let randomnessPre := EkGeneratorsSubRawR Ctau (Vremove_last a0) in
      let randomnessPost := rev (EkGeneratorsSubRawR (rev Ctau) (rev (Vtail a0))) in

      MoR.VF_add tau (Vapp randomnessPre randomnessPost).

  Lemma EkGeneratorsRawM_switch : forall (l : nat)(b' : VF (S l))(c' : VF l)
    (Ca : vector (VF n) (S l))(a0 : (vector (VF n) (1+(S l))))
     (b : VF (S l))(a : F)(c : VF l),
    Vhead (Vbreak (EkGeneratorsRawM Ca a0 (Vapp b (Vcons a c)))).2 =
    Vhead (Vbreak (EkGeneratorsRawM Ca a0 (Vapp b' (Vcons a c')))).2.
  Proof.
    intros. unfold EkGeneratorsRawM, VF_add, FMatrix.VA.vector_plus.
    do 2 rewrite <- Vbreak_vmap2_2. do 3 rewrite Vbreak_app. simpl. trivial.
  Qed.

  Lemma EkGeneratorsRawR_switch : forall (l : nat)(b' : vector Ring.F (S l))
      (c' : vector Ring.F l)
    (Ctau : vector (vector Ring.F n) (S l))(a0 : (vector (VF n) (1+(S l))))
     (b : vector Ring.F (S l))(a : Ring.F)(c : vector Ring.F l),
    Vhead (Vbreak (EkGeneratorsRawR Ctau a0 (Vapp b (Vcons a c)))).2 =
    Vhead (Vbreak (EkGeneratorsRawR Ctau a0 (Vapp b' (Vcons a c')))).2.
  Proof.
    intros. unfold EkGeneratorsRawR, MoR.VF_add, MoR.FMatrix.VA.vector_plus.
    do 2 rewrite <- Vbreak_vmap2_2. do 3 rewrite Vbreak_app. simpl. trivial.
  Qed.

  Lemma EkGeneratorsRaw_conv : forall (pk : enc.PK)(l : nat)
    (g : enc.M)(Ca : vector (VF n) l)(Ctau : vector (vector Ring.F n) l)
    (a0 : (vector (VF n) (1+l)))(tau : vector Ring.F (l+l))
    (b : VF (l+l))(cBar : (vector (vector Ciphertext.G n) l)),
     cBar = Vmap2 (fun y z => Vmap2 (fun w v => enc.enc pk (VS3.op g w) v) y z) Ca Ctau ->
     Vmap2 (fun w v => enc.enc pk (VS3.op g w) v) (EkGeneratorsRawM Ca a0 b)
     (EkGeneratorsRawR Ctau a0 tau) = EkGenerators pk g cBar a0 tau b (VF_one (l+l)).
  Proof.
    pose Ciphertext.module_abegrp.
    intros. apply Veq_nth. intros. do 6 rewrite Vnth_map2. rewrite H.
    rewrite Vnth_const. rewrite VS1.mod_id. rewrite VS3.mod_dist_Fadd.
    rewrite <- enc.homomorphism. rewrite comm. apply f_equal.
    rewrite Vnth_app. rewrite Vnth_app. rewrite Vnth_app.
    destruct (le_gt_dec l i).
    (* case 1 *)
    do 6 rewrite Vbuild_nth. rewrite MoM.VF_sum_op. rewrite comHomomorphism.
    unfold MoC.VG_prod. rewrite enc.encZero. apply f_equal. apply Veq_nth.
    intros. do 3 rewrite Vnth_map2. rewrite Vnth_map. rewrite Vnth_map2.
    rewrite MoM.VF_sum_op. rewrite comHomomorphism. rewrite enc.encZero.
    apply f_equal. apply Veq_nth. intros. do 3 rewrite Vnth_map2. do 4 rewrite Vnth_sub.
    do 4 rewrite Vbuild_nth. do 2 rewrite Vnth_map2. rewrite Vnth_map.
    rewrite enc.encDis. rewrite Vnth_map2. trivial.
    (* case 2 *)
    do 3 rewrite Vbuild_nth. rewrite MoM.VF_sum_op. rewrite comHomomorphism.
    unfold MoC.VG_prod. rewrite enc.encZero. apply f_equal. apply Veq_nth.
    intros. do 3 rewrite Vnth_map2. rewrite Vnth_map. rewrite Vnth_map2.
    rewrite MoM.VF_sum_op. rewrite comHomomorphism. rewrite enc.encZero.
    apply f_equal. apply Veq_nth. intros. do 3 rewrite Vnth_map2. do 5 rewrite Vnth_sub.
    do 2 rewrite Vnth_map2. rewrite Vnth_map. rewrite enc.encDis. rewrite Vnth_map2.
    trivial.
  Qed.
    

  (* Describes Pexp EkGenerators *)
  Lemma EkGeneratorsPexp :
    forall (pk : enc.PK)
    (g : enc.M)(cBar : (vector (vector Ciphertext.G n) m))
    (a0 : (vector (VF n) (1+m)))(tau : vector Ring.F (m+m))
    (k : VF (m+m))(x y : VF (m+m)),
    MoC.VG_Pexp (EkGenerators pk g cBar a0 tau k x) y
      = (EkGenerators pk g cBar a0
          (Vmap2 MVS.op3 tau y) (VF_mult k y))
          (VF_mult x y).
  Proof.
    pose Ciphertext.module_abegrp.
    intros. apply Veq_nth. intros. unfold EkGenerators.
    do 8 rewrite Vnth_map2. rewrite VS1.mod_dist_Gdot.
    apply eqImplProd. split. rewrite enc.encDis.
    trivial.
    do 2 rewrite Vnth_map2. rewrite ALVS1.mod_dist_FMul2.
    trivial.
  Qed.

  Definition makeSVectors (l : nat)(s : VF (l+l)) :
      vector (VF (1+l)) l :=
    Vbuild (fun i (ip : i < l) =>
      Vsub s (makeSVectorsIndexRev ip)).

  Lemma pexpOfCiphertext : forall (n : nat)(pk : enc.PK)
      (g : enc.M)(k e : VF n)(tau : vector Ring.F n),
   MoC.VG_Pexp (Vmap2 (fun x y =>
         enc.enc pk (VS3.op g x) y) k tau) e =
    Vmap2 (fun x y => enc.enc pk (VS3.op g x) y) (VF_mult k e)
      (Vmap2 MVS.op3 tau e).
  Proof.
    intros. apply Veq_nth. intros. do 5 rewrite Vnth_map2.
    rewrite enc.encDis. trivial.
  Qed.

  Lemma prodOfCiphertext : forall (n : nat)(pk : enc.PK)
      (g : enc.M)(k : VF n)(tau : vector Ring.F n),
    MoC.VG_prod (Vmap2 (fun x0 : F =>
          [eta enc.enc pk (VS3.op g x0)]
     ) k tau) =
            enc.enc pk (VS3.op g (VF_sum k)) (MoR.VF_sum tau).
    Proof.
      intros. induction n0. rewrite (Vector_0_is_nil k).
      rewrite (Vector_0_is_nil tau). cbn. rewrite VS3.mod_ann.
      rewrite enc.encZero. trivial.
      rewrite MoC.VG_prod_induction. rewrite <- Vtail_map2.
      rewrite IHn0. rewrite Vhead_nth. rewrite Vnth_map2.
      rewrite enc.homomorphism. do 2 rewrite <- Vhead_nth.
      rewrite <- VS3.mod_dist_Fadd. rewrite MoR.VF_sum_induction.
      rewrite VF_sum_induction. apply EncEq. apply f_equal2; auto.
      ring; auto. destruct Ring.module_ring. apply Radd_comm.
    Qed.

  (* Describes VG_Prod EkGenerators *)
  Lemma EkGeneratorsProd :
    forall (pk : enc.PK)
    (g : enc.M)(cBar : (vector (vector Ciphertext.G n) m))
    (a0 : (vector (VF n) (1+m)))(tau : vector Ring.F (m+m))
    (k : VF (m+m))(s : VF (m+m)),
    let sVectors : vector (VF (1+m)) m:=
      makeSVectors m s in

    MoC.VG_prod (EkGenerators pk g cBar a0 tau k s)
      = Ciphertext.Gdot (enc.enc pk (VS3.op g (VF_sum k))
        (MoR.VF_sum tau))
      (MoC.VG_prod  (Vmap2
        (fun x scaleV => MoC.VG_prod (Vmap2 (fun y scale =>
          MoC.VG_prod (MoC.VG_Pexp x (VF_scale y scale)))
          a0 scaleV)) cBar sVectors)).
  Proof.
    pose Ciphertext.module_abegrp.
    intros. unfold EkGenerators. rewrite MoC.VG_Prod_mult_dist.
    apply eqImplProd. split. apply prodOfCiphertext.
    rewrite MoC.VG_prod_VG_Pexp_app. rewrite MoC.VG_prod_VG_Pexp_rev.
    do 2 rewrite EkGenSubAltEq. rewrite comm. rewrite MoC.VG_prod_rev.
    rewrite comm. rewrite MoC.Vfold_Gdot_dob. rewrite EkGenSubComb.
    (* Up this point I beleive it works *)
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vbuild_nth. apply Vfold_left_eq. apply Veq_nth. intros.
    rewrite Vnth_map. rewrite Vnth_map2. apply Vfold_left_eq.
    apply Veq_nth. intros. do 3 rewrite Vnth_map2. apply ALVS1.scaleEq.
    do 2 rewrite Vnth_map. apply ALVS1.F_mul_split. trivial.
    rewrite Vnth_sub. rewrite Vbuild_nth. rewrite Vnth_sub.
    apply Vnth_eq. trivial.
  Qed.

  Lemma EkGeneratorsRawR_clear : forall (l : nat) (Ctau : vector (vector Ring.F n) l)
    (a0 : (vector (VF n) (1+l)))(tau : vector Ring.F (l+l)),
      Vmap2 Ring.Fadd (EkGeneratorsRawR Ctau a0 tau)
       (Vmap Ring.Finv (EkGeneratorsRawR Ctau a0 (MoR.VF_zero (l + l)))) = tau.
  Proof.
    intros. unfold EkGeneratorsRawR. rewrite (MoR.VF_comm (MoR.VF_zero (l + l))).
    rewrite MoR.VF_add_zero. pose MoR.VF_add_neg. unfold MoR.VF_add, MoR.VF_neg,
    MoR.FMatrix.VA.vector_plus in *. rewrite e. trivial.
  Qed.

  Lemma EkGeneratorsRawM_clear : forall (l : nat) (Ctau : vector (VF n) l)
    (a0 : (vector (VF n) (1+l)))(tau : VF (l+l)),
      Vmap2 Fadd (EkGeneratorsRawM Ctau a0 tau)
       (Vmap Finv (EkGeneratorsRawM Ctau a0 (VF_zero (l + l)))) = tau.
  Proof.
    intros. unfold EkGeneratorsRawM. rewrite (VF_comm (VF_zero (l + l))).
    rewrite VF_add_zero. pose VF_add_neg. unfold VF_add, VF_neg,
    FMatrix.VA.vector_plus in *. rewrite e. trivial.
  Qed.

End BGSupportIns.

