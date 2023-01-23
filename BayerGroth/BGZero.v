Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
From Groups Require Import groups module vectorspace dualvectorspaces matrices 
  matricesF matricesField modulevectorspace groupfromring.
Require Import sigmaprotocolPlus.
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
Require Import BayerGrothSupport.
Set Implicit Arguments.

(*                                              *)
(*  Proof of the zero arg from BG               *)

Module Type BGZeroArg (Message Ciphertext Commitment : GroupSig)(Ring : RingSig)
    (Field : FieldSig)(VS2 : VectorSpaceSig Commitment Field)
    (VS1 : VectorSpaceSig Ciphertext Field)
    (Chal : GroupFromRing Field)
    (MVS : VectorSpaceModuleSameGroup Ciphertext Ring Field VS1)
    (VS3 : VectorSpaceSig Message Field)(Hack : Nat)(M : Nat)
    (enc : EncryptionSchemePlus Message Ciphertext Ring Field VS1 VS3 MVS)
    (support : BGSupport Message Ciphertext Commitment Ring Field VS2 VS1 MVS VS3 
    Hack M enc) <: SigmaPlus Chal.

  Import support.

  (* N = nm *)
  Let n := S (S (S Hack.N)).      (* n *)
  Let m := S (S M.N).     (* m *)
  Import Field.


  Import Mo.
  Import Mo.mat.

  Import EPC.
  Import EPC.MoM.
  Import PC.
 
  Import ALenc.
  Import HardProb.

  Module ALR := RingAddationalLemmas Ring.

  Import VS2.
  Import Commitment.

  (* The billinear map *)
  Definition BM (y : F)(A B : (VF n)) : F :=
    let Y := VandermondeColGen n y 1 in 
    VF_sum (Vmap2 Fmul (Vmap2 Fmul A B) Y).

  Lemma BM_VF_scale_l : forall (y : F)(a b : (VF n))(c : F), 
    BM y a b * c = BM y (VF_scale a c) b.
  Proof.
    intros. unfold BM. rewrite VF_sum_scale. apply f_equal. apply Veq_nth.
    intros. rewrite Vnth_map. do 4 rewrite Vnth_map2. rewrite Vnth_map. 
    field; auto.
  Qed.

  Lemma BM_VF_scale_r : forall (y : F)(a b : (VF n))(c : F), 
    BM y a b * c = BM y a (VF_scale b c).
  Proof.
    intros. unfold BM. rewrite VF_sum_scale. apply f_equal. apply Veq_nth.
    intros. rewrite Vnth_map. do 4 rewrite Vnth_map2. rewrite Vnth_map. 
    field; auto.
  Qed.

  Lemma  VM_VF_scale : forall (N : nat)(y : F)(a : VF n)(b : vector (VF n) N)(c: VF N),
    (Vmap2 Fmul (Vmap (BM y a) b) c)  = Vmap (BM y a) (Vmap2 (VF_scale (n:=n)) b c).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vnth_map.
    rewrite Vnth_map2. rewrite BM_VF_scale_r. trivial.
  Qed.

  Lemma BM_VF_add_r : forall (y : F)(a c d : (VF n)),
    BM y a (VF_add c d) = BM y a c + BM y a d.
  Proof.
    intros. unfold BM. rewrite VF_sum_add. apply f_equal. apply Veq_nth.
    intros. do 8 rewrite Vnth_map2. unfold FSemiRingT.Aplus. destruct module_ring.
    rewrite <- Rmul_assoc. rewrite Rdistr_l. rewrite Rmul_comm. rewrite Rdistr_l.
    apply f_equal2. rewrite Rmul_comm. rewrite Rmul_assoc. trivial. 
    rewrite Rmul_comm. rewrite Rmul_assoc. trivial.
  Qed. 

  Lemma BM_VF_add_r_com : forall n' (y : F)(a : VF n)(b : vector (VF n) n'),
    BM y a (Vfold_left (VF_add (n:=n)) (VF_zero n) b) =
  Vfold_left Fadd 0 (Vbuild (fun (i : nat) (ip : i < n') =>
         BM y a (Vnth b ip))).
  Proof.
    intros. induction n'. rewrite (Vector_0_is_nil b). simpl. unfold BM.
    assert (Vmap2 Fmul (Vmap2 Fmul a (Vcons 0 (Vcons 0 (Vcons 0 (VF_zero Hack.N))))) (VandermondeColGen n y 1) = 
    VF_zero n). apply Veq_nth. intros. do 2 rewrite Vnth_map2. rewrite Vnth_const.
    ring; auto. rewrite H. rewrite VF_sum_VF_zero. trivial.
    rewrite (VSn_eq b). rewrite Vfold_left_Vcons_VFadd. rewrite <- VSn_eq.
    rewrite BM_VF_add_r.  rewrite IHn'. rewrite <- Vfold_left_Vcons_Fadd. 
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_cons. 
    destruct (lt_ge_dec 0 i). do 2 rewrite Vbuild_nth.
    apply f_equal2; auto. rewrite Vnth_tail. apply Vnth_eq. lia.
    rewrite Vbuild_nth. apply f_equal2; auto. rewrite Vhead_nth. apply Vnth_eq.
    lia.
  Qed.

  Lemma BM_neg : forall y (a b : VF n),
    BM y (VF_neg a) b = Finv (BM y a b).
  Proof.
    intros. unfold BM. rewrite VF_neg_sum. apply f_equal. apply Veq_nth.
    intros. do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map. do 2 rewrite Vnth_map2.
    field; auto.
  Qed.

  Lemma BM_simp : forall y (a b c d : VF n),
    Vmap2 Fmul a b = Vmap2 Fmul c d ->
    BM y a b = BM y c d.
  Proof.
    intros. unfold BM. rewrite H. trivial.
  Qed.


  Lemma BM_VF_comm : forall (y : F)(a b: (VF n)),
    BM y a b = BM y b a.
  Proof.
    intros. unfold BM. apply f_equal. apply Veq_nth. intros. do 4 rewrite Vnth_map2.
    apply f_equal2; auto. destruct module_ring. apply Rmul_comm.
  Qed.

  Lemma BM_VF_add_l : forall (y : F)(a c d : (VF n)),
    BM y (VF_add c d) a = BM y c a + BM y d a.
  Proof.
    intros. unfold BM. rewrite VF_sum_add. apply f_equal. apply Veq_nth.
    intros. do 8 rewrite Vnth_map2. unfold FSemiRingT.Aplus. destruct module_ring.
    rewrite <- Rmul_assoc. rewrite Rdistr_l. 
    apply f_equal2. rewrite Rmul_assoc. trivial. 
    rewrite Rmul_assoc. trivial.
  Qed. 

  Definition St : Type := 
  (* ck=(h,hs) y C_A C_B *)
  G*(VG n)*F*(VG m)*(VG m). 
  (* A, r, B, s *)
  Definition W : Type := (vector (VF n) m)*(VF m)*(vector (VF n) m)*(VF m).
  (* a0 r0 b s tau *)
  Definition R : Type := (VF n)*(VF n)*F*F*(VF (S m)*(VF (S M.N))).
  (* cA0 cBm Cd *)
  Definition C : Type := (G*G*(VG (S m+m))).
  (* a r b s t *) 
  Definition T : Type := ((VF n)*F*(VF n)*F*F).
  Definition X : Type := (VF n).
  Definition TE : Type := ((VF n)*F*(VF n)*F*F)*(VF m*VF (S M.N)).

  Definition simMapHelp (s : St)(x : X) :=
    let '(h,hs,y,CA,CB) := s in

    hs = Vmap (op h) x.

  Definition Rel (s : St)(w : W) : bool := 
    let '(h,hs,y,CA,CB) := s in
    let '(A,r,B,s)      := w in

      VG_eq CA (comEPC h hs A r) && 
      VG_eq CB (comEPC h hs B s) &&
      Fbool_eq 0 (VF_sum (Vmap2 (BM y) A B)).

  Definition fail_event (s : St)(c : C)(e : VF (S m+m)) : Prop :=
    let '(h,hs,y,CA,CB) := s in

      (* The commitments are broken *)
      (exists c m0 m1 r0 r1, relComPC h (Vnth hs index0) c m0 m1 r0 r1) \/ 

      (* Schwartz Zipple lemma failed (Two matrices a and b), vector d and opening *)
      (* The big idea is that prover commits to the coefficents, which determine the
       polynomial, before the challenge. If the polynomial sampled at the challenge
      is zero we conclude the polynomial is zero *)
      (exists (a b : vector (VF n) (S m)) d r sOpen t, 
        (* Matrix of all the commitments *)
      let mat := Vbuild (fun i (ip: i < S m) => Vbuild (fun j (jp : j < S m) =>
        Gdot (Vnth (Vcons c.1.1 s.1.2) ip)(Vnth (Vadd s.2 c.1.2) jp))) in
        (* Matrix of the openings *)
      let matF2 := Vbuild (fun i (ip: i < S m) => Vbuild (fun j (jp : j < S m) =>
        VF_mult (Vnth a ip)(Vnth b jp))) in

        (* Check to that polynomials are commited hence are indepedent from challenges
         under binding *)
      (Vcons c.1.1 s.1.2) = comEPC h hs a r /\
      (Vadd s.2 c.1.2) = comEPC h hs b sOpen /\
      c.2 = comPC h (Vhead hs) d t /\ 

        (* If the commited polyonimals are evaluate to zero at the challenge but not equal then 
        we allow soundness not to hold (The Schwatz Zippel Lemma says this occurs with 
        negligble probabilty). *)
      VF_inProd (VF_sub (Vmap (BM s.1.1.2 (VF_one n)) (ProdOfDiagonalsVF matF2))
                           d) (VandermondeCol (S m + m) (Vhead e)) = 0 /\ 
      (Vmap (BM s.1.1.2 (VF_one n)) (ProdOfDiagonalsVF matF2)) <> d).

  Definition P0 (stat : St)(rand : R)(wit : W) : St*C :=
    let '(h,hs,y,CA,CB) := stat in

    let a0 := rand.1.1.1.1 in
    let bm := rand.1.1.1.2 in
    let r0 := rand.1.1.2 in
    let sm := rand.1.2 in
    let t  := rand.2 in

    let A := wit.1.1.1 in
    let r := wit.1.1.2 in
    let B := wit.1.2 in
    let s := wit.2 in

    let CA0 := EPC h hs a0 r0 in
    let CBM := EPC h hs bm sm in

    let mat := FMatrix.mat_build (fun i j (ip: i < S m)(jp : j < S m) => 
      (BM y) (Vnth (Vcons a0 A) ip) (Vnth (Vadd B bm) jp)) in

    let CD := comPC h (Vhead hs) (ProdOfDiagonalsF mat) 
      (Vapp t.1 (Vcons 0 t.2))   in

    (stat,(CA0, CBM, CD)).


  Definition V0 (ggtoxgtor: St*C) 
      (c: F): (St*C*F)
    := (ggtoxgtor, c).

  Definition P1 (ggtoxgtorc: St*C*F) 
      (r : R) (w: W) : St*C*F*T :=

    let stat := ggtoxgtorc.1.1 in
    let wit  := w in
    let rand := r in
    let c := ggtoxgtorc.2 in
    
    let '(h,hs,y,CA,CB) := stat in

    let a0 := rand.1.1.1.1 in
    let bm := rand.1.1.1.2 in
    let r0 := rand.1.1.2 in
    let sm := rand.1.2 in
    let t  := rand.2 in

    let A := wit.1.1.1 in
    let r := wit.1.1.2 in
    let B := wit.1.2 in
    let s := wit.2 in

    let xBar := VandermondeCol (S m) c in
    let xK := VandermondeCol (S m + m) c in

    (* aBar = a0 + A xBar , since we tranpose both A and xBar *)
    let aT := Vfold_left (VF_add (n:=n)) (VF_zero n) 
      (Vmap2 (VF_scale (n:=n)) (Vcons a0 A) xBar) in
    let rT := VF_sum (VF_mult xBar (Vcons r0 r)) in
    let bT := Vfold_left (VF_add (n:=n)) (VF_zero n) 
      (Vmap2 (VF_scale (n:=n)) (Vadd B bm) (rev xBar)) in 
    let sT := VF_sum (VF_mult (rev xBar) (Vadd s sm)) in
    let tT := VF_sum (VF_mult xK (Vapp t.1 (Vcons 0 t.2))) in

    (ggtoxgtorc, (aT, rT, bT, sT, tT)).

  Definition V1 (transcript : St*C*F*T) :bool :=
    let stat := transcript.1.1.1 in
    let comm := transcript.1.1.2 in
    let chal := transcript.1.2 in
    let resp := transcript.2 in

    let '(h,hs,y,CA,CB) := stat in

    let CA0 := comm.1.1 in 
    let CBM := comm.1.2 in
    let CD := comm.2 in

    let xBar := VandermondeCol (S m) chal in
    let xK := VandermondeCol (S m + m) chal in

    let aT := resp.1.1.1.1 in
    let rT := resp.1.1.1.2 in
    let bT := resp.1.1.2 in 
    let sT := resp.1.2 in
    let tT := resp.2 in

    let eq1 := Gbool_eq (VG_prod (VG_Pexp (Vcons CA0 CA) xBar))
       (EPC h hs aT rT) in

    let eq2 := Gbool_eq (VG_prod (VG_Pexp (Vadd CB CBM) (rev xBar)))
      (EPC h hs bT sT) in

    let eq3 := Gbool_eq (VG_prod (VG_Pexp CD xK))
      (PC h (Vnth hs index0) (BM y aT bT) tT) in
    
    let eq4 := Gbool_eq (Vnth CD indexSM) 
      (PC h (Vnth hs index0) 0 0) in

    eq1 && eq2 && eq3 && eq4.

  Definition simMap (s : St)(w : W)(c :F)
    (x : X)(r : R) : TE :=

    let '(h,hs,y,CA,CB) := s in

    let a0 := r.1.1.1.1 in
    let bm := r.1.1.1.2 in
    let r0 := r.1.1.2 in
    let sm := r.1.2 in
    let t  := r.2 in

    let A := w.1.1.1 in
    let r := w.1.1.2 in
    let B := w.1.2 in
    let s := w.2 in

    let xBar := VandermondeCol (S m) c in
    let xK := VandermondeCol (S m + m) c in

    (* aBar = a0 + A xBar , since we tranpose both A and xBar *)
    let aT := Vfold_left (VF_add (n:=n)) (VF_zero n) 
      (Vmap2 (VF_scale (n:=n)) (Vcons a0 A) xBar) in
    let rT := VF_sum (VF_mult xBar (Vcons r0 r)) in
    let bT := Vfold_left (VF_add (n:=n)) (VF_zero n) 
      (Vmap2 (VF_scale (n:=n)) (Vadd B bm) (rev xBar)) in 
    let sT := VF_sum (VF_mult (rev xBar) (Vadd s sm)) in
    let tT := VF_sum (VF_mult xK (Vapp t.1 (Vcons 0 t.2))) in

    let mat := FMatrix.mat_build (fun i j (ip: i < S m)(jp : j < S m) => 
      (BM y) (Vnth (Vcons a0 A) ip) (Vnth (Vadd B bm) jp)) in

    let CDFirst := VF_add (Vtail t.1)
      (VF_scale (Vtail (Vbreak (ProdOfDiagonalsF mat)).1) (Vhead x))  in
    let CDSecond := VF_add t.2
      (VF_scale (Vtail (Vbreak (ProdOfDiagonalsF mat)).2) (Vhead x))  in

    ((aT, rT, bT, sT, tT),(CDFirst,CDSecond)).

  Definition simMapInv (s : St)(w : W)(c :F)
    (x : X)(t : TE) : R :=

    let '(h,hs,y,CA,CB) := s in

    let aT := t.1.1.1.1.1 in
    let rT := t.1.1.1.1.2 in
    let bT := t.1.1.1.2 in
    let sT := t.1.1.2 in
    let tT := t.1.2 in
    let CDFirst  := t.2.1 in
    let CDSecond := t.2.2 in

    let A := w.1.1.1 in
    let r := w.1.1.2 in
    let B := w.1.2 in
    let s := w.2 in

    let xBar := VandermondeCol (S m) c in
    let xK := VandermondeCol (S m + m) c in

    (* aBar = a0 + A xBar , since we tranpose both A and xBar *)
    let a0 := VF_sub aT (Vfold_left (VF_add (n:=n)) (VF_zero n) 
      (Vmap2 (VF_scale (n:=n)) A (Vtail xBar))) in
    let r0 := rT - VF_sum (VF_mult (Vtail xBar) r) in
    let b := VF_sub bT (Vfold_left (VF_add (n:=n)) (VF_zero n) 
      (Vmap2 (VF_scale (n:=n)) B (rev (Vtail xBar)))) in 
    let s := sT - VF_sum (VF_mult (rev (Vtail xBar)) s) in

    let mat := FMatrix.mat_build (fun i j (ip: i < S m)(jp : j < S m) => 
      (BM y) (Vnth (Vcons a0 A) ip) (Vnth (Vadd B b) jp)) in

    let t1 := VF_sub CDFirst (VF_scale (Vtail (Vbreak (ProdOfDiagonalsF mat)).1) (Vhead x))
         in
    let t2 := VF_sub CDSecond (VF_scale (Vtail (Vbreak (ProdOfDiagonalsF mat)).2) (Vhead x))
         in

    let tau := tT - VF_sum (VF_mult (Vtail xK) (Vapp t1 (Vcons 0 t2))) in

    (* a0 r0 b s tau *)
    (a0, b, r0, s, ((Vcons tau t1), t2)).

  Definition simulator (s : St)(z : TE)(e : F) : 
    (St*C*F*T) :=
    
    let '(h,hs,y,CA,CB) := s in

    let xBar := VandermondeCol (S m) e in
    let xK := VandermondeCol (S m + m) e in

    let aT := z.1.1.1.1.1 in
    let rT := z.1.1.1.1.2 in
    let bT := z.1.1.1.2 in 
    let sT := z.1.1.2 in
    let tT := z.1.2 in

    let CDFirst := Vmap (fun x => h^x) z.2.1 in
    let CDSecond := Vmap (fun x => h^x) z.2.2 in

    let CA0 := EPC h hs aT rT o - VG_prod (VG_Pexp CA (Vtail xBar)) in 
    let CBM := EPC h hs bT sT o - VG_prod (VG_Pexp CB (Vremove_last (rev xBar)))  in

    let CDM := PC h (Vnth hs index0) 0 0 in
    let CD0 := PC h (Vnth hs index0) (BM y aT bT) tT o - 
        VG_prod (VG_Pexp (Vapp CDFirst (Vcons CDM CDSecond)) (Vtail xK))  in
    let CD := Vapp (Vcons CD0 CDFirst) (Vcons CDM CDSecond) in

    (s,(CA0,CBM,CD),e,z.1). 

  Definition extractor (s : vector T (S m + m))
        (c : vector F (S m + m)): W :=

    let sM := (Vbreak s).1 in
    let cM := (Vbreak c).1 in

    let aT := FMatrix.mat_transpose (Vmap (fun s1 => s1.1.1.1.1) sM) in
    let rT := Vmap (fun s1 => s1.1.1.1.2) sM in
    let bT := FMatrix.mat_transpose (Vmap (fun s1 => s1.1.1.2) sM) in 
    let sT := Vmap (fun s1 => s1.1.2) sM in
    let YM1 := FMatrix.mat_transpose (VandermondeInv cM) in
    let YM2 := FMatrix.mat_transpose (rev (VandermondeInv cM)) in

    (Vtail (FMatrix.mat_transpose (FMatrix.mat_mult aT YM1)), 
      Vtail (Vhead (FMatrix.mat_mult [rT] YM1)),
      Vremove_last (FMatrix.mat_transpose (FMatrix.mat_mult bT YM2)), 
      Vremove_last (Vhead (FMatrix.mat_mult [sT] YM2))).

  (* Inital lemmas *)
  Lemma TheSMdiagBM : forall (s : St)(w : W)(r : R), 
   VF_sum (Vmap2 (BM s.1.1.2) w.1.1.1 w.1.2) = 
    Vhead (Vbreak (ProdOfDiagonalsF (FMatrix.mat_build
     (fun (i j : nat) (ip : i < S m) (jp : j < S m) =>
     BM s.1.1.2 (Vnth (Vcons r.1.1.1.1 w.1.1.1) ip)
                 (Vnth (Vadd w.1.2 r.1.1.1.2) jp))))).2.
  Proof.
    intros. rewrite TheSMdiag. apply f_equal. apply Veq_nth. intros.
    rewrite Vbuild_nth. rewrite Vnth_remove_last. rewrite Vnth_tail.
    rewrite FMatrix.mat_build_nth. rewrite Vnth_map2. apply f_equal2.
    rewrite Vnth_cons_tail. apply Vnth_eq. lia. rewrite Vnth_addl. trivial.
  Qed.

  Lemma MatrixAndBillinear_sub : forall (n' l : nat)(y : F)(A B : (vector (VF n) (S n')))
      (c : F),
    Vfold_left Fadd 0
    (Vmap2 Fmul
     (ProdOfDiagonalsF
        (FMatrix.mat_build
           (fun (i j : nat) (ip : i < S n') (jp : j < S n') =>
            BM y (Vnth A ip)
              (Vnth B jp)))) (VandermondeColGen (S n' + n') c l)) =
    BM y
      (Vfold_left (VF_add (n:=n)) (VF_zero n)
         (Vmap2 (VF_scale (n:=n)) A (VandermondeColGen (S n') c l)))
      (Vfold_left (VF_add (n:=n)) (VF_zero n)
         (Vmap2 (VF_scale (n:=n)) B (rev (VandermondeColGen (S n') c 0)))).
   Proof.
    induction n'. intros.
    (* Base case *)
    rewrite ProdOfDiagonalsOneF. pose VF_sum_1_head. unfold VF_sum in e. rewrite e.
    do 2 rewrite Vhead_nth. rewrite Vnth_map2. rewrite FMatrix.mat_build_nth.
    rewrite Vbuild_nth. do 2 rewrite VF_sum_vadd_1_head. do 2 rewrite Vhead_map2.
    do 2 rewrite Vbuild_head. rewrite Vbuild_nth. assert (VF_prod (Vconst c (1 - 0 - 1)) = 1).
    cbn. trivial. rewrite H. 
    rewrite VF_scale_1. rewrite BM_VF_scale_l. do 2 rewrite Vhead_nth. trivial. 
    (* Extened case *)
    intros. rewrite ProdOfDiagonalsIndF. lia. intros. pose VF_dist. unfold VF_mult in e.
    rewrite e.  pose VF_sum_add. unfold VF_sum in e0. rewrite <- e0.
      (* An absurdly verbose lemma which says that zeros are irrelvant *) 
    assert (Vfold_left Fadd 0 (Vmap2 Fmul (Vcast (Vadd (Vcons 0
      (ProdOfDiagonalsF (FMatrix.mat_build (fun (i j : nat) (ip : i < S n') 
      (jp : j < S n') => BM y (Vnth (Vtail A) ip) (Vnth (Vtail B) jp))))) 0) Hyp0)
     (VandermondeColGen (S (S n') + S n') c l)) = Vfold_left Fadd 0 (Vmap2 Fmul 
      (ProdOfDiagonalsF (FMatrix.mat_build (fun (i j : nat) (ip : i < S n') 
      (jp : j < S n') => BM y (Vnth (Vtail A) ip) (Vnth (Vtail B) jp))))
     (VandermondeColGen (S n' + n') c (S l)))).  rewrite Vmap2_Vcast_out. lia. intros. 
    rewrite <- Vfold_left_cast_irr. 
    rewrite (VSn_add (Vcast (VandermondeColGen (S (S n') + S n') c l) Hyp1)).
    rewrite Vadd_map2. destruct module_ring. rewrite Rmul_comm. 
    rewrite ALVS1.whenAutoFail4. rewrite Vfold_left_Vadd_Fadd.
    rewrite Radd_comm. rewrite Radd_0_l. 
    rewrite (VSn_eq (Vremove_last (Vcast (VandermondeColGen (S (S n') + S n') c l) Hyp1))).
    rewrite Vcons_map2. rewrite Rmul_comm. rewrite ALVS1.whenAutoFail4.
    rewrite Vfold_left_Vcons_Fadd. rewrite Radd_comm. rewrite Radd_0_l.
    apply f_equal. apply f_equal2; auto. apply Veq_nth. intros. rewrite Vnth_tail.
    rewrite Vnth_remove_last. rewrite Vnth_cast. do 2 rewrite Vbuild_nth.
    apply VG_prod_const_index. lia. exact F. exact F. 
    (* Resuming main *)
    rewrite H. rewrite IHn'. rewrite (VSn_eq A). rewrite (VSn_eq B). symmetry. 
    rewrite (VSn_eq (rev (VandermondeColGen (S (S n')) c 0))).
    rewrite (VSn_eq (VandermondeColGen (S (S n')) c l)). do 2 rewrite Vcons_map2.
    do 2 rewrite Vfold_left_Vcons_VFadd. rewrite BM_VF_add_l. 
    do 2 rewrite BM_VF_add_r. do 2 rewrite <- VSn_eq. destruct module_ring. 
    rewrite <- Radd_assoc. apply f_equal2. rewrite VandermondeColGen_tail.
    do 2 rewrite <- VandermondeColGe_eq.
    rewrite VandermondeCol_tail_rev. trivial.
    (* Discharge core matrix only need edges *)
    rewrite (Vbreak_eq_app (VandermondeColGen (S (S n') + S n') c l)). 
    rewrite Vapp_map2. rewrite Vfold_left_Vapp_Fadd. rewrite Radd_comm.
    apply f_equal2; auto. rewrite <- BM_VF_add_r. rewrite VandermondeColBreakGen.
      (* First *)
    rewrite <- Vfold_left_Vcons_VFadd. rewrite <- Vcons_map2. do 2 rewrite <- VSn_eq.
    rewrite BM_VF_add_r_com. rewrite Vfold_left_eq_rev; auto. apply f_equal.
     apply Veq_nth. intros.  rewrite Vnth_map2.
    do 3 rewrite Vbuild_nth. rewrite Vnth_map2. unfold BM. rewrite VF_sum_scale.
    apply f_equal. apply Veq_nth. intros. do 2 rewrite Vnth_map2. do 3 rewrite Vnth_map.
    do 2 rewrite Vnth_map2. do 5 rewrite <- Rmul_assoc. apply f_equal2; auto.
    rewrite Rmul_comm. rewrite <- Rmul_assoc. apply f_equal2. apply Veq_nth3; auto.
    apply Vnth_eq. lia. rewrite Rmul_comm. rewrite Rmul_assoc. rewrite Rmul_comm.
    apply f_equal2; auto. rewrite Vhead_nth. do 4 rewrite Vbuild_nth.
    rewrite VF_prod_const. apply VG_prod_const_index. lia.
      (* Last *)
    rewrite BM_VF_comm. rewrite BM_VF_add_r_com. apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vbuild_nth.
    unfold BM. rewrite VF_sum_scale.
    apply f_equal. apply Veq_nth. intros. do 3 rewrite Vnth_map2. do 3 rewrite Vnth_map.
    do 2 rewrite Vnth_map2. assert (forall a b c d e f, b*d=e -> a * b * (c * d)*f  = c * a * f* e).
    intros. rewrite <- H0. ring; auto. apply H0. rewrite Vnth_vbreak_2. lia. intros.
    rewrite Vhead_nth. rewrite Vnth_tail. do 4 rewrite Vbuild_nth. rewrite VF_prod_const. 
    apply VG_prod_const_index. lia. 
    (* and done *)
  Qed.

  Lemma MatrixAndBillinear : forall (n' : nat)(y : F)(A B : (vector (VF n) (S n')))
      (c : F),
    Vfold_left Fadd 0
    (Vmap2 Fmul
     (ProdOfDiagonalsF
        (FMatrix.mat_build
           (fun (i j : nat) (ip : i < S n') (jp : j < S n') =>
            BM y (Vnth A ip)
              (Vnth B jp)))) (VandermondeCol (S n' + n') c)) =
    BM y
      (Vfold_left (VF_add (n:=n)) (VF_zero n)
         (Vmap2 (VF_scale (n:=n)) A (VandermondeCol (S n') c)))
      (Vfold_left (VF_add (n:=n)) (VF_zero n)
         (Vmap2 (VF_scale (n:=n)) B (rev (VandermondeCol (S n') c)))).
   Proof.
    intros. remember (rev (VandermondeCol (S n') c)) as d.
    do 2 rewrite VandermondeColGe_eq. rewrite Heqd. rewrite VandermondeColGe_eq. 
    apply MatrixAndBillinear_sub.
  Qed.

  Lemma Matrix_infold : forall (A B : vector (VF n) (S m))(c: F),
    ProdOfDiagonalsVF (Vbuild (fun (i : nat) (ip : i < S m) =>
     Vbuild (fun (j : nat) (jp : j < S m) =>  VF_mult
     (Vnth (Vmap2 (VF_scale (n:=n)) A (VandermondeCol (S m) c)) ip)
     (Vnth (Vmap2 (VF_scale (n:=n)) B (rev (VandermondeCol (S  m) c)))  jp)))) =
     Vmap2 (VF_scale (n:=n)) (ProdOfDiagonalsVF (Vbuild (fun (i : nat) (ip : i < S m) =>
     Vbuild (fun (j : nat) (jp : j < S m) =>  VF_mult (Vnth A ip) (Vnth B jp)))))
        (VandermondeCol (S m + m) c).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. unfold ProdOfDiagonalsVF,
    ProdOfDiagonals. rewrite Vnth_app. rewrite Vnth_app. destruct (le_gt_dec (S m) i).
    (* 1 of 2 *)
    rewrite Vbuild_nth. do 3 rewrite Vbuild_nth. rewrite VF_scale_VF_add. apply f_equal.
    apply Veq_nth.  intros. rewrite Vnth_map. do 7 rewrite Vbuild_nth. do 2 rewrite Vnth_map2.
    apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_map. rewrite Vnth_map2.
    destruct module_ring. do 2 rewrite <- Rmul_assoc. apply f_equal2; auto.
    rewrite Rmul_comm. rewrite <- Rmul_assoc. apply f_equal2; auto.
    do 3 rewrite Vbuild_nth. rewrite VF_prod_const. apply VG_prod_const_index. lia. 
    (* 2 of 2 *)
    rewrite Vbuild_nth. rewrite Vbuild_nth. rewrite VF_scale_VF_add. apply f_equal.
    apply Veq_nth.  intros. rewrite Vnth_map. do 7 rewrite Vbuild_nth. do 2 rewrite Vnth_map2.
    apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_map. rewrite Vnth_map2.
    destruct module_ring. do 2 rewrite <- Rmul_assoc. apply f_equal2; auto.
    rewrite Rmul_comm. rewrite <- Rmul_assoc. apply f_equal2; auto.
    do 3 rewrite Vbuild_nth. rewrite VF_prod_const. apply VG_prod_const_index. lia.
  Qed.

  (* Main theorem *)
    Ltac simpl_prod := repeat progress (try rewrite Prod_left_replace; 
      try rewrite Prod_right_replace).

  Definition M := (Nat.add (S m) m).
  
  Lemma pres_p0 : forall (s : St)(r : R)(w : W), (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. unfold P0. destruct s, p, p, p. trivial.
  Qed.

  Lemma pres_v0 : forall (sc : St*C)(e : Chal.G), (V0 sc e) = (sc,(V0 sc e).2).
  Proof.
    intros. destruct sc. destruct s, p, p, p. trivial.
  Qed.

  Lemma pres_p1 : forall (sce : St*C*Chal.G)(r : R)(w : W), 
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Proof.
    intros. destruct sce. destruct p. destruct s, p, p, p. trivial.
  Qed.

  Lemma pres_sim : forall (s: St)(t : TE)(e : Chal.G),
      s = (simulator s t e).1.1.1.  Proof.
    intros. destruct s, p, p, p. trivial.
  Qed.

  Lemma chal_sim : forall (s: St)(t : TE)(e : Chal.G),
    e = (simulator s t e).1.2.  
  Proof.
    intros. destruct s, p, p, p. trivial.
  Qed.


  (** Properties *)
  Lemma correctness : forall (s :St)(w:W)(r:R)(c: Chal.G),
    Rel s w ->
    V1 (P1 (V0 (P0 s r w) c) r w) = true.
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.  
    pose Commitment.module_abegrp. 
    intros. unfold V1. unfold V0. unfold P1.
    unfold P0. unfold Rel in *. destruct s, p, p, p. destruct w,p,p.
    do 9 rewrite Prod_right_replace. do 6 rewrite Prod_left_replace.
    apply andb_true_iff in H. destruct H. apply andb_true_iff in H.
    destruct H. apply VGeq in H. apply VGeq in H1. apply F_bool_eq_corr in H0.
    apply andb_true_iff. split. apply andb_true_iff. split.
    apply andb_true_iff. split. apply bool_eq_corr. rewrite H.
    (* 1/4 *)
    rewrite comEPCVcons. unfold VG_Pexp. rewrite comEPCDis. rewrite EPCMultExt.
    apply f_equal. apply f_equal2. trivial. rewrite VF_comm_mult.
    unfold VF_mult. trivial.
    (* 2/4 *)
    apply bool_eq_corr. rewrite H1. rewrite comEPCVadd. unfold VG_Pexp. 
    rewrite comEPCDis. rewrite EPCMultExt. apply f_equal. apply f_equal2.
    trivial. rewrite VF_comm_mult. unfold VF_mult. trivial.
    (* 3/4 *)
    apply bool_eq_corr. unfold VG_Pexp. rewrite comPCDis. unfold VG_prod.
    rewrite <- PCMultExt. apply f_equal3. rewrite Vhead_nth. apply Vnth_eq. 
    trivial. 
    (* The part with the matrix *)
    apply MatrixAndBillinear.
    (* and we're back *)
    rewrite VF_comm_mult. trivial.
    (* 4/4 *)
    apply bool_eq_corr. rewrite Vnth_map2. do 2 rewrite Vnth_app.
    destruct (le_gt_dec (S m) (S support.m)). apply f_equal3.
    rewrite Vhead_nth. apply Vnth_eq. trivial. 
    (* Proving the m+1 diagonal is equal relation and hence 0 *)
    rewrite Vbuild_nth. rewrite Vbuild_nth. remember (Vfold_left Fadd 0) as sum. rewrite H0.
    assert (m = S (m - (S support.m - S m) - 1)).
    unfold support.m, m. lia. rewrite Heqsum. unfold VF_sum in *. symmetry. 
    apply (Vfold_left_eq_cast H2).
    apply Veq_nth. intros. rewrite Vbuild_nth. rewrite FMatrix.mat_build_nth.
    rewrite Vnth_cast. rewrite Vnth_map2. 
    (* time to prove a and b separately *)
    apply f_equal2. rewrite Vnth_cons.
    assert (Nat.sub (S support.m) (S m) = 0%nat). unfold m, support.m in *. lia.
    destruct (lt_ge_dec 0 (i + (m - (m - (S support.m - S m) - 1)))).
    (* normal a case *)
    apply Vnth_eq. rewrite H3. lia.
    (* absurd a case *)
    rewrite H3 in g0. assert False. lia. contradiction. 
    (* absurd b case *)
    rewrite Vnth_add. destruct (Nat.eq_dec i m). 
    assert (i < S (m - (S support.m - S m) - 1)). trivial. 
    rewrite <- H2 in H3. assert False. lia. contradiction. 
    (* normal b case *)
    apply Vnth_eq. trivial.
    (* And now the rest is easy *)
    rewrite Vnth_cons. destruct (lt_ge_dec 0 (S support.m - S m)).
    assert False. unfold support.m in l0. unfold m in l0. lia. contradiction.
    trivial.
    assert False. unfold support.m in g0. unfold m in g0. lia. contradiction.
  Qed.

  Definition allDifferent (e : vector Chal.G M) := PairwisePredicate Chal.Gdisjoint e.

  Lemma special_soundness : forall (s : St)(c : C)(e : vector Chal.G M)(t : vector T M),
    (* Forall e it is disjoint from all e *)
    allDifferent e  ->
    bVforall2 (fun e1 t1 => V1 (s, c, e1, t1)) e t -> 
    Rel s (extractor t e) = true \/ fail_event s c e.
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.  
    pose Commitment.module_abegrp. intros.  unfold V1. unfold V0. unfold P1.
    unfold P0. unfold Rel in *. unfold fail_event. unfold V1 in H0. 
    destruct s, p, p, p.
    do 3 (apply bVforall2Split in H0; destruct H0).
    remember (VandermondeCol (S m)) as d. remember (VG_Pexp) as f0. simpl in H0.
    simpl in H3. simpl in H2. simpl in H1. rewrite Heqd in H0. rewrite Heqf0 in H0.
    assert (S (S (S (M.N + m))) = Nat.add (S (S (S M.N))) (S (S M.N))). unfold m. lia. unfold m in *.
     pose (Vbreak (Vcast e H4)).1 as e'. pose (Vbreak (Vcast t H4)).1 as t'.
    assert (PairwisePredicate Chal.Gdisjoint e); auto.
    apply (PairwisePredicate_break (S (S (S M.N))) (S (S M.N)) e Chal.Gdisjoint H4) in H5.
    apply (bVforall2_break (S (S (S M.N))) (S (S M.N)) e t (fun (a' : F) (b' : T) =>
        Gbool_eq
          (VG_prod (VG_Pexp (Vcons c.1.1 v0) (VandermondeCol (S (S (S M.N))) a')))
          (EPC g v1 b'.1.1.1.1 b'.1.1.1.2)) H4) in H0. destruct H0.
    (* Ca *)
    pose (commitOpen e' (fun x => x.1.1.1.1) (fun x => x.1.1.1.2) (Vcons c.1.1 v0) 
    g v1 t' H5 H0). 
    (* Cb *)
    apply (bVforall2_break (S (S (S M.N))) (S (S M.N)) e t (fun (a' : F) (b' : T) =>
        Gbool_eq (VG_prod (f0 (S (S (S M.N))) (Vadd v c.1.2) (rev (d a'))))
          (EPC g v1 b'.1.1.2 b'.1.2)) H4) in H3. destruct H3.
    rewrite Heqf0 in H3. assert (bVforall2
       (fun (a' : F) (b' : T) =>
        Gbool_eq (VG_prod (VG_Pexp (rev (Vadd v c.1.2)) (VandermondeCol (S(S (S M.N))) a')))
          (EPC g v1 b'.1.1.2 b'.1.2)) e' t'). apply bVforall2_nth_intro.
    intros. apply (bVforall2_elim_nth ip e' t') in H3. apply bool_eq_corr.
    apply bool_eq_corr in H3. rewrite VG_prod_rev. rewrite rev_vmap2. rewrite rev_rev.
    rewrite <- H3. rewrite Heqd. unfold VG_Pexp. trivial.
    pose (commitOpen e' (fun x => x.1.1.2) (fun x => x.1.2) (rev (Vadd v c.1.2))
    g v1 t' H5 H8).
    (* Cd *)
    rewrite Heqf0 in H2.
    pose (commitOpenPC e (fun b' => BM f b'.1.1.1.1 b'.1.1.2) (fun b => b.2)
       c.2 g (Vnth v1 index0) t H H2).
    
    apply bVforall2Clear in H1. apply bool_eq_corr in H1.
    assert (Vnth c.2 indexSM = PC g (Vnth v1 index0) 
    (VF_inProd (Vmap (fun b'=> BM f b'.1.1.1.1 b'.1.1.2) t) (Vnth (VandermondeInv e) indexSM))
    (VF_inProd (Vmap (fun b'=> b'.2) t) (Vnth (VandermondeInv e) indexSM))).
    rewrite e2. rewrite Vnth_map2. do 2 rewrite Vhead_nth. do 2 rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_row. do 2 rewrite Vnth0. unfold VF_inProd. rewrite FMatrix.mat_transpose_row_col.
    unfold FMatrix.get_row. trivial.
    (* Final *)
     (* Commitments were broken *)
     destruct_with_eqn (Fbool_eq 0 (VF_inProd (Vmap
     (fun b' : VF n * F * VF n * F * F =>
      BM f b'.1.1.1.1 b'.1.1.2) t)
      (Vnth (VandermondeInv e) indexSM))). 
    (* The case where SZ fails *)
    destruct_with_eqn (VF_beq (Vmap (BM f (VF_one n)) (ProdOfDiagonalsVF 
      (Vbuild (fun i (ip: i < S m) => Vbuild (fun j (jp : j < S m) =>
        Vmap2 Fmul (Vnth (FMatrix.mat_mult (VandermondeInv e') (Vmap (fun x => x.1.1.1.1) t')) ip)
          (Vnth (FMatrix.mat_mult (rev (VandermondeInv e')) (Vmap (fun x => x.1.1.2) t')) jp)))))
    ) (Vhead
        (FMatrix.mat_mult
           [Vmap
              (fun b' : VF n * F * VF n * F * F =>
               BM f b'.1.1.1.1 b'.1.1.2) t]
           (FMatrix.mat_transpose (VandermondeInv e))))). intros.
    (* 1 of 3 *)
    + intros. left. apply andb_true_iff. split. apply andb_true_iff. split. 
    apply Vtail_imp in e0. rewrite e0. apply VGeq. apply Veq_nth.
    intros. rewrite Vnth_tail. do 2 rewrite Vnth_map2. apply f_equal2.
    unfold extractor. rewrite Prod_left_replace. rewrite transpose_move_gen.
    do 2 rewrite FMatrix.mat_transpose_idem. rewrite Vnth_tail. apply Veq_nth.
    intros. do 2 rewrite FMatrix.mat_build_nth. apply f_equal2. unfold FMatrix.get_row.
    unfold e'. apply Veq_nth3; auto. apply f_equal. apply Veq_nth. intros.
    rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_vbreak_1. rewrite Vnth_cast.
    apply Vnth_eq. trivial. apply Veq_nth. intros.
    do 4 rewrite Vnth_map. rewrite Vnth_vbreak_1. lia. intros. 
    rewrite Vnth_vbreak_1. rewrite Vnth_cast. apply Veq_nth3; auto.
    apply f_equal. apply f_equal. apply f_equal. apply f_equal. 
    apply Vnth_eq. trivial.  unfold extractor. 
    rewrite Vnth_tail. do 2 rewrite Vhead_nth. do 2 rewrite FMatrix.mat_build_nth.
     apply f_equal2. unfold FMatrix.get_row. do 2 rewrite Vnth0_2. apply Veq_nth. 
    intros. do 2 rewrite Vnth_map. rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_vbreak_1.
    do 4 apply f_equal. rewrite Vnth_cast. apply Vnth_eq. trivial. 
    apply Veq_nth. intros. do 2 rewrite Vnth_map.
    apply Veq_nth3; auto. apply Veq_nth3; auto. apply f_equal. apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_vbreak_1.
    rewrite Vnth_cast. apply Vnth_eq. trivial. 
    (* 2 of 3 *)
    assert (Vtail (rev (Vadd v c.1.2)) = Vtail (comEPC g v1
     (FMatrix.mat_mult (VandermondeInv e')
        (Vmap (fun x : VF n * F * VF n * F * F => x.1.1.2) t')) (Vhead
        (FMatrix.mat_mult [Vmap (fun x : VF n * F * VF n * F * F => x.1.2) t']
           (FMatrix.mat_transpose (VandermondeInv e')))))). rewrite e1. trivial.
    rewrite <- Vcons_rev in H10. assert (forall (a : G) (b :VG m), Vtail (Vcons a b) = b).
    intros. simpl. trivial. rewrite H11 in H10. apply rev_switch in H10. rewrite H10.
    apply VGeq. apply Veq_nth. intros. rewrite Vbuild_nth. rewrite Vnth_tail.
    unfold extractor. do 2 rewrite Vnth_map2.
    apply f_equal2. rewrite Vnth_remove_last. rewrite transpose_move_gen.
    do 2 rewrite FMatrix.mat_transpose_idem. apply Veq_nth. intros.
    do 2 rewrite FMatrix.mat_build_nth. apply f_equal2. unfold FMatrix.get_row.
    do 1 rewrite Vbuild_nth. apply Veq_nth3. unfold m. lia. unfold e'.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_vbreak_1.
    rewrite Vnth_cast. apply Vnth_eq. lia.  unfold t'. 
    apply Veq_nth. intros.  
    intros. do 4 rewrite Vnth_map. apply Veq_nth3; auto. do 3 apply f_equal.
    rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_vbreak_1. rewrite Vnth_cast.
    apply Vnth_eq. trivial. 
    rewrite Vnth_remove_last. do 2 rewrite Vhead_nth. do 2 rewrite FMatrix.mat_build_nth.
    apply f_equal2. unfold FMatrix.get_row. do 2 rewrite Vnth0_2. apply Veq_nth. 
    intros. do 2 rewrite Vnth_map. rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_vbreak_1.
    do 2 apply f_equal. rewrite Vnth_cast. apply Vnth_eq. trivial. 
    apply Veq_nth. intros. do 2 rewrite Vnth_map. do 2 rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_elem. unfold FMatrix.get_row. rewrite Vbuild_nth.
    apply Veq_nth3; auto. unfold e'. apply Veq_nth3. unfold m. lia.
    apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_vbreak_1. lia.  intros. rewrite Vnth_vbreak_1.
    rewrite Vnth_cast. apply Vnth_eq. lia. unfold t'. 
    (* 3 of 3 *)
    assert (VF_inProd (Vmap (fun b' => BM f b'.1.1.1.1 b'.1.1.2) t) 
      (Vnth (VandermondeInv e) indexSM) = VF_sum (Vmap2 (BM f) (extractor t e).1.1.1
     (extractor t e).1.2)).
    (* The bit with the Schwatz Zippel Lemma *)
      ++ apply VF_beq_true in Heqb0. apply (Veq_nth4 indexSM) in Heqb0.
         rewrite Vhead_nth in Heqb0.
    rewrite FMatrix.mat_build_nth in Heqb0. rewrite FMatrix.mat_transpose_row_col in Heqb0.
    unfold FMatrix.get_row in Heqb0. unfold VF_inProd. assert (Vnth
    [Vmap (fun b' => BM f b'.1.1.1.1 b'.1.1.2) t] (Nat.lt_0_succ 0) = 
    Vmap (fun b' => BM f b'.1.1.1.1 b'.1.1.2) t). simpl. trivial. rewrite H10 in Heqb0.
    symmetry in Heqb0. rewrite Heqb0. rewrite Vnth_map. unfold BM. rewrite TheSMdiagindexSM.
    rewrite Prod_left_replace. rewrite Prod_right_replace. do 2 rewrite  transpose_move_gen.
    do 4 rewrite FMatrix.mat_transpose_idem. assert (forall a, Vmap2 Fmul (VF_one n) a = a).
    intros. pose VF_comm_mult. pose VF_mult_one. unfold VF_mult in *. rewrite e3. apply e4.
    rewrite H11. pose VF_Fadd_dist. pose VF_comm_mult. unfold VF_mult in *. rewrite e4. rewrite e3.
    rewrite VF_sum_sum. apply f_equal. apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_map2.
    apply f_equal. rewrite Vnth_map. rewrite e4. apply f_equal2; auto. rewrite Vbuild_nth.
    do 2 rewrite Vnth_remove_last. do 2 rewrite Vnth_tail. do 2 rewrite Vbuild_nth. unfold e'.
    unfold t'. apply f_equal2. apply Veq_nth. intros. do 2 rewrite FMatrix.mat_mult_elem.
    apply f_equal2. unfold FMatrix.get_row. rewrite Vcast_refl. trivial.
    rewrite Vcast_refl. trivial. do 2 rewrite Vcast_refl. trivial.
      ++ apply F_bool_eq_corr. apply F_bool_eq_corr in Heqb. rewrite Heqb. rewrite H10.
         trivial. 
    (* SZ failed. *)
    (* And we go *)
    + intros. right. right. 
    exists (FMatrix.mat_mult (VandermondeInv e') (Vmap (fun x =>  x.1.1.1.1) t')).
    exists (FMatrix.mat_mult (rev (VandermondeInv e')) (Vmap (fun x => x.1.1.2) t')).
    exists (Vhead (FMatrix.mat_mult [Vmap (fun b' => BM f 
      b'.1.1.1.1 b'.1.1.2) t] (FMatrix.mat_transpose (VandermondeInv e)))).
    exists (Vhead (FMatrix.mat_mult
           [Vmap (fun x : VF n * F * VF n * F * F => x.1.1.1.2) t']
           (FMatrix.mat_transpose (VandermondeInv e')))).
    exists (rev (Vhead (FMatrix.mat_mult
           [Vmap (fun x : VF n * F * VF n * F * F => x.1.2) t']
           (FMatrix.mat_transpose (VandermondeInv e'))))).
    exists (Vhead (FMatrix.mat_mult [Vmap [eta snd] t] (FMatrix.mat_transpose (VandermondeInv e)))).
    split; auto.
    (* Opens commitment 2 *)
    split. apply comEPCrev in e1. rewrite rev_rev in e1. rewrite e1. apply f_equal2; auto.
    apply Veq_nth. intros. rewrite Vbuild_nth. apply Veq_nth. intros.
    do 2 rewrite FMatrix.mat_mult_elem.  unfold FMatrix.get_row. do 1 rewrite Vbuild_nth.
    trivial.
    (* Opens commitment 3 *)
    split. rewrite e2. apply f_equal3; auto.
    rewrite Vhead_nth. apply Vnth_eq. trivial. split.
    (* Look at polynomial *)
    ++++ rewrite VF_sub_corr. rewrite InProd_Sum. pose VF_dist. unfold VF_mult in e3.
    rewrite e3. rewrite <- VF_sum_add. pose VF_neg_mul. unfold VF_mult in e4.
    rewrite <- e4. rewrite <- VF_neg_sum. rewrite <- shift. 
    (* I'm pretty sure this should hold by defintion but anyway. *)
    assert (VF_sum (Vmap2 Fmul (Vmap (BM f (VF_one n)) (ProdOfDiagonalsVF
    (Vbuild (fun (i : nat) (ip : i < S (S (S M.N))) => Vbuild
    (fun (j : nat) (jp : j < S (S (S M.N))) => VF_mult
    (Vnth (FMatrix.mat_mult (VandermondeInv e') (Vmap (fun x => x.1.1.1.1) t')) ip)
    (Vnth (FMatrix.mat_mult (rev (VandermondeInv e')) (Vmap (fun x => x.1.1.2) t')) jp))))))
     (VandermondeCol (S (S (S M.N)) + S (S M.N)) (Vhead e))) = BM f (Vhead t').1.1.1.1 (Vhead t').1.1.2).
    (* Now for the hard part *)
    rewrite VM_VF_scale.
    rewrite <- Matrix_infold. unfold BM. assert (forall n' (a : vector (VF n) n'), Vmap  (fun B : VF n =>
    VF_sum (Vmap2 Fmul (Vmap2 Fmul (VF_one n) B) (VandermondeColGen n f 1))) a =
    Vmap (VF_sum (n:=n)) (Vmap (fun B : VF n => (Vmap2 Fmul (Vmap2 Fmul (VF_one n) B) 
    (VandermondeColGen n f 1))) a)). intros. apply Veq_nth. intros.
    do 3 rewrite Vnth_map. trivial. rewrite H10. rewrite <- VF_sum_sum. unfold BM.
    apply f_equal. apply Veq_nth. intros. rewrite Vfold_left_VF_add.
    (* Seems pretty sensiable to here *)
    do 2 rewrite Vnth_map2. assert (Vmap (fun v : vector F n => Vnth v ip)
    (Vmap (fun B : VF n =>  Vmap2 Fmul (Vmap2 Fmul (VF_one n) B) (VandermondeColGen n f 1))
    (ProdOfDiagonalsVF (Vbuild (fun (i0 : nat) (ip0 : i0 < S m) => Vbuild
    (fun (j : nat) (jp : j < S m) => VF_mult (Vnth (Vmap2 (VF_scale (n:=n))
    (FMatrix.mat_mult (VandermondeInv e') (Vmap (fun x  => x.1.1.1.1)
                                t')) (VandermondeCol (S m) (Vhead e))) ip0)
    (Vnth (Vmap2 (VF_scale (n:=n)) (FMatrix.mat_mult (rev (VandermondeInv e'))
    (Vmap (fun x => x.1.1.2) t')) (rev (VandermondeCol (S m) (Vhead e)))) jp))))))  = 
    Vmap (fun x => Vnth (VF_mult x (VandermondeColGen n f 1)) ip) (ProdOfDiagonalsVF
           (Vbuild
              (fun (i0 : nat) (ip0 : i0 < S m) =>
               Vbuild
                 (fun (j : nat) (jp : j < S m) =>
                  VF_mult
                    (Vnth
                       (Vmap2 (VF_scale (n:=n))
                          (FMatrix.mat_mult (VandermondeInv e')
                             (Vmap (fun x : VF n * F * VF n * F * F => x.1.1.1.1)
                                t')) (VandermondeCol (S m) (Vhead e))) ip0)
                    (Vnth
                       (Vmap2 (VF_scale (n:=n))
                          (FMatrix.mat_mult (rev (VandermondeInv e'))
                             (Vmap (fun x : VF n * F * VF n * F * F => x.1.1.2) t'))
                          (rev (VandermondeCol (S m) (Vhead e)))) jp)))))).
    apply Veq_nth. intros. do 2 rewrite Vnth_map. 
    assert (forall n a, Vmap2 Fmul (VF_one n) a = a). intros. apply Veq_nth.
   intros. rewrite Vnth_map2. rewrite Vnth_const. ring; auto. rewrite H11.
   rewrite Vnth_map. rewrite Vnth_map2. trivial. rewrite H11.
   assert (forall n' (a : vector (VF n) n'), Vfold_left Fadd 0
  (Vmap (fun x : VF n => Vnth (VF_mult x (VandermondeColGen n f 1)) ip) a) = 
    Vfold_left Fadd 0 (Vmap (fun x => Vnth x ip) a) * Vnth (VandermondeColGen n f 1) ip).
    intros. rewrite VF_sum_scale. apply f_equal. apply Veq_nth. intros.
    do 3 rewrite Vnth_map. rewrite Vnth_map2. trivial. rewrite H12. apply f_equal2; auto.
    rewrite <- Vfold_left_VF_add. assert (Vnth (Vhead t').1.1.1.1 ip * Vnth (Vhead t').1.1.2 ip =
    Vnth (VF_mult ((Vhead t').1.1.1.1) ((Vhead t').1.1.2)) ip).
    rewrite Vnth_map2. trivial. rewrite H13.  apply Veq_nth3; auto.
    (* We have now discharged the billinear map *) clear e0.
    remember (FMatrix.mat_mult (VandermondeInv e')
                       (Vmap (fun x : VF n * F * VF n * F * F => x.1.1.1.1) t')) as TempA.
    remember (FMatrix.mat_mult (rev (VandermondeInv e'))
                       (Vmap (fun x : VF n * F * VF n * F * F => x.1.1.2) t')) as TempB.
    assert (VandermondeCol (S m) (Vhead e) = Vhead (Vandermonde e')). rewrite Vhead_map.
    unfold m. apply f_equal. unfold e'. do 2 rewrite Vhead_nth. rewrite Vnth_vbreak_1. lia.
    intros. rewrite Vnth_cast. apply Vnth_eq. trivial. 
    (* Case 1 *)    
    assert ((Vhead t').1.1.1.1 = Vfold_left (VF_add (n:=n)) (VF_zero n) 
     (Vmap2 (VF_scale (n:=n)) TempA (VandermondeCol (S m) (Vhead e)))). 
    rewrite HeqTempA. rewrite scale_mult. rewrite VF_add_transpose. apply Veq_nth. intros.
    do 2 rewrite Vnth_map. rewrite <- InProd_Sum. pose FMatrix.mat_transpose_col_row.
    unfold FMatrix.get_row in e0. rewrite e0. rewrite <- MF_getCol_prod_gen.
    rewrite <- mat_mult_assoc_gen. rewrite H14. rewrite <- Vhead_mat_mult.
    pose invVandermondeRight. unfold MF_mult in e5. rewrite e5; auto. do 3 rewrite Vhead_nth.
    rewrite FMatrix.mat_build_nth. rewrite Vbuild_nth. unfold FMatrix.get_row.
    rewrite Vnth0. rewrite FMatrix.VA.dot_product_id. do 2 rewrite Vnth_map. trivial.
    (* Case 2 *)
    assert ((Vhead t').1.1.2 = Vfold_left (VF_add (n:=n)) (VF_zero n) 
     (Vmap2 (VF_scale (n:=n)) TempB (rev (VandermondeCol (S m) (Vhead e))))). 
    rewrite HeqTempB. rewrite scale_mult. rewrite VF_add_transpose. apply Veq_nth. intros.
    do 2 rewrite Vnth_map. rewrite <- InProd_Sum. pose FMatrix.mat_transpose_col_row.
    unfold FMatrix.get_row in e0. rewrite e0. rewrite <- MF_getCol_prod_gen.
    rewrite <- mat_mult_assoc_gen. assert (rev (VandermondeCol (S m) (Vhead e)) =
    Vhead (Vmap (fun x => rev x) (Vandermonde e'))). apply Veq_nth. intros.
    rewrite Vbuild_nth. do 2 rewrite Vhead_map. do 3 rewrite Vbuild_nth. 
    unfold m. apply f_equal. apply Veq_nth. intros. do 2 rewrite Vnth_const. 
    do 2 rewrite Vhead_nth. unfold e'. rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_cast.
    apply Vnth_eq. trivial. 
    rewrite H16. rewrite <- Vhead_mat_mult. 
    assert (FMatrix.mat_mult (Vmap [eta rev (n:=S (S (S M.N)))] (Vandermonde e'))
              (rev (VandermondeInv e')) = (MF_id (S (S (S M.N))))). apply Veq_nth. intros.
     apply Veq_nth. intros. rewrite FMatrix.mat_build_nth. unfold FMatrix.get_row.
    rewrite Vnth_map. rewrite <- (@invVandermondeRight (S (S (S M.N))) e'); auto. (* rewrite Vbuild_nth. *)
    rewrite FMatrix.mat_build_nth. rewrite rev_col. assert (forall n (a b : VF n), 
    FMatrix.VA.dot_product (rev a) (rev b) = FMatrix.VA.dot_product a b). intros.
    unfold FMatrix.VA.dot_product. do 2 rewrite Vfold_left_Fadd_eq.
    rewrite Vfold_left_eq_rev.
    rewrite rev_vmap2. do 2 rewrite rev_rev. trivial.
     intros. ring; auto. intros. ring; auto.
    apply H17. rewrite H17. do 2 rewrite Vhead_nth. rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_row. rewrite Vnth0. rewrite Vbuild_head. rewrite FMatrix.VA.dot_product_id.
    do 2 rewrite Vnth_map. trivial.
    (* Utilise *)
    rewrite H15. rewrite H16. remember (Vmap2 (VF_scale (n:=n)) TempA (VandermondeCol (S m) (Vhead e))) as TempC.
    remember (Vmap2 (VF_scale (n:=n)) TempB (rev (VandermondeCol (S m) (Vhead e)))) as TempD.
    apply prod_exp.
    (* On the home strech *)
    rewrite H10. rewrite <- InProd_Sum. assert (VandermondeCol ((S (S (S M.N)) + S (S M.N)))
   (Vhead e) = Vhead (Vandermonde e)). rewrite Vhead_map. apply f_equal. trivial. rewrite H11.
    do 3 rewrite Vhead_nth. rewrite <- MF_getRow_prod_gen. rewrite mat_mult_assoc_gen.
    rewrite <- transpose_move_gen. do 3 rewrite <- Vhead_nth. rewrite <- Vhead_mat_mult.
    pose invVandermondeRight. unfold MF_mult in e5. rewrite e5; auto.
    rewrite Vhead_nth. do 2 rewrite Vhead_nth. rewrite FMatrix.mat_build_nth.
    rewrite FMatrix.mat_transpose_row_col. unfold FMatrix.get_row. do 2 rewrite Vnth0.
    rewrite Vbuild_head. rewrite FMatrix.VA.dot_product_comm. rewrite FMatrix.VA.dot_product_id.
    rewrite Vnth_map. apply f_equal2. do 4 apply f_equal. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_cast. apply Vnth_eq. trivial. do 3 apply f_equal. rewrite Vnth_vbreak_1. lia.
    intros.  rewrite Vnth_cast. apply Vnth_eq. trivial. 
    (* It was zero *) 
    ++++ apply VF_beq_false in Heqb0. unfold not in *. intros.
    rewrite <- H10 in Heqb0. apply Heqb0. unfold m, VF_mult in *. 
    do 3 apply f_equal. trivial.
    (* commitments are broken *)
    + intros. right. left. unfold relComPC. exists (Vnth c.2 indexSM). exists 0.   
    exists (VF_inProd  (Vmap (fun b' => BM f b'.1.1.1.1 b'.1.1.2) t) (Vnth (VandermondeInv e) indexSM)).
    exists 0. exists (VF_inProd (Vmap [eta snd] t) (Vnth (VandermondeInv e) indexSM)).
    split. apply F_bool_neq_corr in Heqb. trivial. split; auto.
  Qed.

  Lemma honest_verifier_ZK :
    forall (s : St)(w : W)(e : Chal.G)(x : X)(r : R)(t : TE),
      simMapHelp s x ->
      Rel s w ->
      ((P1(V0 (P0 s r w) e) r w) =
      simulator s (simMap s w e x r) e) /\ 
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.
  Proof. 
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.  
    pose Commitment.module_abegrp. intros.  unfold V1. unfold V0. unfold P1.
    unfold P0.
    unfold simMap, simMapInv. rewrite Prod_right_replace.
    simpl in x. simpl in t. simpl in H. destruct s, p, p, p. destruct w,p,p.
    split. intros. 
    do 3 rewrite Prod_left_replace. apply injective_projections.
    do 2 rewrite Prod_left_replace. apply injective_projections.
    do 2 rewrite Prod_left_replace. apply injective_projections.
    (* Statment *)
    trivial. 
    (* Commitments *)
    ++ do 7 rewrite Prod_right_replace. apply andb_true_iff in H0. destruct H0.
    apply andb_true_iff in H0. destruct H0. apply VGeq in H0. 
    apply VGeq in H2. apply F_bool_eq_corr in H1.
    apply injective_projections.
    do 2 rewrite Prod_left_replace. apply injective_projections.
    do 2 rewrite Prod_left_replace.
    (* Commitments 1/3 *)
    +++ do 4 rewrite Prod_left_replace. rewrite Prod_right_replace. rewrite H0.
    rewrite (VSn_eq (VandermondeCol (S m) e)). unfold VG_Pexp.
    rewrite Vcons_map2. unfold VF_mult. rewrite Vcons_map2. 
    rewrite VF_sum_vcons. rewrite Vfold_left_Vcons_VFadd. rewrite <- EPCMult.
    rewrite comm. rewrite dot_assoc. rewrite Vtail_cons. rewrite comEPCDis.
    rewrite EPCMultExt. pose VF_comm_mult. unfold VF_mult in e0.
    rewrite e0. rewrite <- inv_left. rewrite one_left. rewrite Vbuild_head.
    apply f_equal2. apply Veq_nth. intros. rewrite Vnth_map. cbn. field; auto.
    cbn. field; auto.
    (* Commitments 2/3 *)
    +++ do 4 rewrite Prod_right_replace. rewrite H2. rewrite EPCMultExt.
    unfold VF_mult. pose VF_comm_mult. unfold VF_mult in e0. rewrite e0.
    rewrite <- comEPCDis. rewrite <- comEPCVadd.
    rewrite (VSn_add (rev (VandermondeCol (S m) e))).  rewrite Vadd_map2.
    rewrite <- VSn_add. pose VG_prod_add. unfold VG_prod in e1. rewrite e1.
    rewrite comm. rewrite dot_assoc. rewrite <- inv_left. rewrite one_left.
    rewrite Vlast_nth. rewrite Vbuild_nth. rewrite Vbuild_nth. 
    replace (Nat.sub (Nat.sub (S m) m) 1) with 0%nat. cbn. rewrite mod_id. trivial.
    lia.
    (* Commitments 3/3 *)
    +++ do 2 rewrite Prod_right_replace. do 4 rewrite Prod_left_replace. 
    rewrite (Vbreak_eq_app (ProdOfDiagonalsF
     (FMatrix.mat_build
        (fun (i j : nat) (ip : i < S m) (jp : j < S m) =>
         BM f (Vnth (Vcons r.1.1.1.1 t1) ip)
           (Vnth (Vadd t0 r.1.1.1.2) jp))))).
    rewrite <- comPCVapp. apply f_equal2.
    ++++
    remember Vbreak as d. do 2 rewrite Prod_right_replace. do 2 rewrite Prod_left_replace.
    rewrite Heqd. rewrite <- Vbreak_eq_app.
    rewrite (VSn_eq (comPC g (Vhead v1)
  (Vbreak
     (ProdOfDiagonalsF
        (FMatrix.mat_build
           (fun (i j : nat) (ip : i < S m) (jp : j < S m) =>
            BM f (Vnth (Vcons r.1.1.1.1 t1) ip)
              (Vnth (Vadd t0 r.1.1.1.2) jp))))).1 r.2.1)). 
    apply Vcons_eq_intro.
    +++++ 
    rewrite Vbreak_Vtail. rewrite Vhead_map2. rewrite Vhead_break.
    rewrite ProdOfDiagonalsFVhead. pose  MatrixAndBillinear_sub. 
    symmetry in e0. rewrite VandermondeColGe_eq. 
    rewrite (e0 m 0%nat f (Vcons r.1.1.1.1 t1) (Vadd t0 r.1.1.1.2) e).
    rewrite (VSn_eq (Vmap2 Fmul
        (ProdOfDiagonalsF
           (FMatrix.mat_build
              (fun (i j : nat) (ip : i < S m) (jp : j < S m) =>
               BM f (Vnth (Vcons r.1.1.1.1 t1) ip)
                 (Vnth (Vadd t0 r.1.1.1.2) jp))))
        (VandermondeColGen (S m + m) e 0))).
    rewrite (VSn_eq (VF_mult (VandermondeCol (S m + m) e) (Vapp r.2.1 (Vcons 0 r.2.2)))).
    rewrite VF_sum_vcons. pose VF_sum_vcons. unfold VF_sum in e1.
    rewrite e1. rewrite <- PCMult. assert (forall a b c d, a= b -> c = d ->
    a = (c o b) o - d). intros. rewrite H3. rewrite H4. rewrite comm.
    rewrite dot_assoc. rewrite <- inv_left. rewrite one_left. trivial.
    apply H3.
    ++++++
    apply f_equal3. rewrite Vhead_nth. apply Vnth_eq. trivial. rewrite Vhead_map2.
    rewrite (ProdOfDiagonalsFVhead r.1.1.1.1 r.1.1.1.2 t1 t0).
    rewrite Vbuild_head. cbn. field; auto. rewrite Vhead_map2. rewrite Vbuild_head.
    rewrite (Vhead_app r.2.1). cbn. destruct vs_field. destruct F_R.
    rewrite Rmul_1_l. trivial.
    ++++++
    unfold simMapHelp in H. apply Vhead_eq in H. rewrite Vhead_map in H. 
    pose (comPCfromOp H).
    do 2 rewrite <- e2. assert (Vnth v1 index0 = Vhead v1).
    rewrite Vhead_nth. apply Vnth_eq. lia. rewrite H4. rewrite comPCVcons.
    rewrite comPCVapp. unfold VG_Pexp. rewrite comPCDis. unfold VG_prod.
    rewrite <- PCMultExt. apply f_equal2. apply f_equal. apply Veq_nth.
    intros. rewrite <- Vtail_map2. rewrite (Vapp_Vtail2 (n:=m)). 
    do 2 rewrite Vnth_map2. do 2 rewrite (Vnth_app (n1:=m)). destruct (le_gt_dec m i).
    rewrite Vbreak_app. rewrite Prod_right_replace. rewrite VandermondeColGe_eq.
    apply f_equal2; trivial. symmetry. rewrite Vnth_cons. destruct (lt_ge_dec 0 (i - m)).
    rewrite Vnth_tail. apply Vnth_eq. lia. rewrite H1. do 2 rewrite Vbuild_nth.
    assert (i = m). lia. subst. assert (forall n a (b : VF n), VF_sum b = 0 -> 
    Vfold_left Fadd a b = a). intros. replace a2 with (0+a2). 
    rewrite <- Vfold_Fadd_const. unfold VF_sum in H0. rewrite H0.
    trivial. field; auto. symmetry. apply H0. rewrite H1.
    assert (S (m - (m - m) - 1) = m). unfold m. lia. apply (Vfold_left_eq_gen H2).
    apply Veq_nth. intros. rewrite Vnth_cast. rewrite Vbuild_nth.
    rewrite (FMatrix.mat_build_nth). rewrite Vnth_map2. apply f_equal2.
    rewrite Vnth_cons. destruct (lt_ge_dec 0 (i + (m - (m - (m - m) - 1)))).
    apply Vnth_eq. lia. assert False. lia. contradiction. rewrite Vnth_add.
    destruct (Nat.eq_dec i m). assert False. lia. contradiction.
    apply Vnth_eq. lia.
    rewrite Vbreak_app. rewrite Prod_left_replace. rewrite VandermondeColGe_eq.
    trivial. apply f_equal. unfold VF_mult. rewrite <- Vtail_map2.
    pose VF_comm_mult. unfold VF_mult in e3. rewrite e3. rewrite Vapp_Vtail.
    trivial. 
    +++++
    unfold simMapHelp in H. apply Vhead_eq in H. rewrite Vhead_map in H. 
    rewrite <- (comPCfromOp H); auto.  
    ++++
    rewrite Vbreak_app. rewrite Prod_right_replace.
    rewrite (VSn_eq (Vbreak
     (ProdOfDiagonalsF
        (FMatrix.mat_build
           (fun (i j : nat) (ip : i < S m) (jp : j < S m) =>
            BM f (Vnth (Vcons r.1.1.1.1 t1) ip)
              (Vnth (Vadd t0 r.1.1.1.2) jp))))).2).
    rewrite <- comPCVcons. rewrite <- VSn_eq. apply Vcons_eq_intro.
    apply f_equal3. rewrite Vhead_nth. apply Vnth_eq. trivial.

    pose TheSMinfold. symmetry in e0. rewrite e0. rewrite Vhead_cons.
    rewrite TheSMdiagindexSM. remember (Vfold_left Fadd 0) as b.
    rewrite H1. rewrite Heqb. apply f_equal. apply Veq_nth. intros.
    rewrite Vbuild_nth. rewrite Vnth_remove_last. rewrite Vnth_tail.
    rewrite FMatrix.mat_build_nth. rewrite Vnth_map2. rewrite Vnth_cons.
    rewrite Vnth_add. destruct (lt_ge_dec 0 (S i)). destruct (Nat.eq_dec i m).
    assert (False). unfold m, support.m in *. lia. contradiction.    
    apply f_equal2; apply Vnth_eq; lia. assert (False). unfold m, support.m in *. 
    lia. contradiction. trivial. apply Veq_nth. intros. rewrite Vnth_map.
    unfold simMapHelp in H. unfold X in x. apply Vhead_eq in H. rewrite Vhead_map in H. 
    pose (comPCfromOp H). rewrite e0. 
    rewrite Vnth_map. apply f_equal. trivial.

    (* Challenges *)
    ++ do 2 rewrite Prod_right_replace. trivial.
    (* Response *)
    ++ do 5 rewrite Prod_right_replace. trivial. 

    (* And it's bijective! *)
    ++ intros.  split. 
    
    
    (* Case 1 *)
    +++ rewrite (surjective_pairing r). rewrite (surjective_pairing r.2).
    rewrite (surjective_pairing r.1). rewrite (surjective_pairing r.1.1).
    rewrite (surjective_pairing r.1.1.1). remember Vbreak as h.
    do 10 rewrite Prod_right_replace. do 14 rewrite Prod_left_replace.
    rewrite Heqh.
    apply injective_projections_simp. 
    ++++  apply injective_projections_simp. 
    +++++  apply injective_projections_simp. 
    ++++++ apply injective_projections_simp. 
    +++++++  apply Vfold_left_vcons_cancel. rewrite Vbuild_head. cbn. trivial.
    +++++++ apply Vfold_left_vadd_cancel. rewrite Vbuild_head. cbn. trivial.
    ++++++ apply VF_sum_vcons_cancel. rewrite Vbuild_head. cbn. trivial.
    +++++ apply VF_sum_vadd_cancel. rewrite Vbuild_head. cbn. trivial.
    ++++ apply injective_projections_simp. 
    +++++ rewrite (VSn_eq r.2.1). rewrite Vapp_cons. rewrite Vfold_left_vcons_cancel.
    rewrite Prod_right_replace. rewrite Vfold_left_vadd_cancel. unfold VF_sub.
    rewrite VF_add_neg.  rewrite VF_add_neg. rewrite <- VSn_eq.
    rewrite VF_sum_vcons_cancel. rewrite <- VSn_eq. trivial.
    cbn; auto. cbn; auto. cbn; auto.
    +++++ 
      rewrite Vfold_left_vcons_cancel.
    rewrite Vfold_left_vadd_cancel.
     unfold VF_sub. rewrite VF_add_neg. trivial.
    rewrite Vbuild_head. cbn. trivial. rewrite Vbuild_head. cbn. trivial.

    
    (* Case 2 *)
    +++ rewrite (surjective_pairing t). rewrite (surjective_pairing t.2).
    rewrite (surjective_pairing t.1). rewrite (surjective_pairing t.1.1). 
    rewrite (surjective_pairing t.1.1.1). rewrite (surjective_pairing t.1.1.1.1).
    assert (Vhead (VandermondeCol (S m) e) = 1). rewrite Vbuild_head. cbn. trivial.
    ++++  apply injective_projections_simp. 
    +++++  apply injective_projections_simp. 
    ++++++  apply injective_projections_simp. 
    +++++++  apply injective_projections_simp. 
    ++++++++  apply injective_projections_simp.
    +++++++++ do 6 rewrite Prod_left_replace. apply Vfold_left_vsub_cancel. 
    rewrite Vbuild_head. cbn. trivial.
    +++++++++ do 6 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
     apply VF_sum_vsub_cancel. rewrite Vbuild_head. cbn. trivial.
    ++++++++  do 6 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
    rewrite Vfold_left_vsub_add_cancel. trivial. rewrite Vbuild_head. cbn. trivial.
    +++++++ do 6 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
    rewrite VF_sum_vsub_add_cancel. trivial.  rewrite Vbuild_head. cbn. trivial.
    ++++++ do 6 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
    rewrite Vapp_cons. rewrite VF_sum_vsub_cancel. trivial. rewrite Vbuild_head. cbn. 
    trivial.
    +++++ do 6 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
    apply injective_projections_simp. 
    ++++++ rewrite Prod_left_replace. do 4 rewrite Prod_right_replace.
    rewrite Vtail_cons. rewrite (SubMatrixRight (BM f)). 
    rewrite FMatrix_mat_build_vcons_tail. rewrite Prod_left_replace.
    rewrite Vtail_cons.  unfold VF_sub. rewrite VF_add_neg2. trivial.
    ++++++ rewrite Prod_left_replace. do 5 rewrite Prod_right_replace.
    unfold m. rewrite (SubMatrixRight (BM f)). rewrite Vtail_cons.
    rewrite Vremove_last_add. unfold VF_sub. rewrite VF_add_neg2. trivial.
  Qed.

  Lemma simulator_correct : forall (s : St)(t : TE)(e : Chal.G),
    V1(simulator s t e) = true.
  Proof. 
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.  
    pose Commitment.module_abegrp. intros.  unfold V1. unfold V0. unfold P1.
    unfold P0. unfold Rel in *. 
    unfold simulator. destruct s, p, p, p. 
    apply andb_true_iff. split. apply andb_true_iff. split.
    apply andb_true_iff. split. apply bool_eq_corr.
    (* 1 of 4 *)
    ++ do 3 rewrite Prod_right_replace. rewrite Prod_left_replace.
    rewrite (VSn_eq (VandermondeCol (S m) e)). unfold VG_Pexp. rewrite Vcons_map2.
    unfold VG_prod. rewrite Vfold_left_Vcons. rewrite <- VSn_eq.
    rewrite comm. replace (Vhead (VandermondeCol (S m) e)) with 1.
    rewrite mod_id. rewrite <- dot_assoc. rewrite <- inv_left. rewrite one_right. 
    trivial. rewrite Vbuild_head. cbn. trivial.
    (* 2 of 4 *)
    ++ apply bool_eq_corr. do 3 rewrite Prod_right_replace. 
    rewrite (VSn_add (rev (VandermondeCol (S m) e))). unfold VG_Pexp. 
    rewrite Vadd_map2. rewrite VG_prod_add. rewrite <- VSn_add.
    replace (Vlast (Vhead (rev (VandermondeCol (S m) e))) (rev (VandermondeCol (S m) e)))
    with 1. rewrite comm. rewrite mod_id. rewrite <- dot_assoc. 
    rewrite <- inv_left. rewrite one_right. 
    trivial. rewrite Vlast_nth. do 2 rewrite Vbuild_nth. replace (Nat.sub (Nat.sub (S m) m) 1) with 0%nat.
    cbn. trivial. lia. 
    (* 3 of 4 *)
    ++ apply bool_eq_corr. do 3 rewrite Prod_right_replace. 
    unfold VG_Pexp. rewrite (Vbreak_eq_app (VandermondeCol (S m + m) e)).
    rewrite Vapp_Vmap2. rewrite Vapp_VG_prod. rewrite <- Vbreak_eq_app.
    rewrite VandermondeColBreak. rewrite (VSn_eq (VandermondeCol (S m) e)).
    rewrite Vcons_map2. unfold VG_prod. rewrite Vfold_left_Vcons.
    replace ( Vhead (VandermondeCol (S m) e)) with 1. rewrite mod_id.
    rewrite comm. rewrite dot_assoc. pose Vapp_VG_prod.  unfold VG_prod in e0.
    assert (forall a b c d, (a o b)o(c o d)=(b o a)o(c o d)). intros. apply right_cancel.
    apply comm. rewrite H. rewrite <- e0. rewrite <- Vapp_Vmap2.
    replace ((Vapp (Vtail (VandermondeCol (S m) e)) (Vbreak (VandermondeCol (S m + m) e)).2)) with
    (Vtail (VandermondeCol (S m + m) e)). rewrite comm.  rewrite <- dot_assoc.
    rewrite <- inv_left. apply one_right. rewrite <- (VandermondeColBreak (S m) m e).
    rewrite Vapp_Vtail. rewrite <- Vbreak_eq_app. trivial. rewrite Vbuild_head. cbn. trivial.
    (* 4 of 4 *)
    ++ apply bool_eq_corr. rewrite Prod_right_replace. 
    rewrite Vnth_app. destruct (le_gt_dec (S m) (S support.m)). rewrite Vnth_cons.
    destruct (lt_ge_dec 0 (S support.m - S m)). assert False. unfold support.m in *.
    unfold m in *. lia. contradiction. trivial. assert False. unfold support.m in *.
    unfold m in *. lia. contradiction. 
  Qed. 

End BGZeroArg.

Module BGZeroArgIns (Message Ciphertext Commitment : GroupSig)(Ring : RingSig)
    (Field : FieldSig)(VS2 : VectorSpaceSig Commitment Field)
    (VS1 : VectorSpaceSig Ciphertext Field)
    (Chal : GroupFromRing Field)
    (MVS : VectorSpaceModuleSameGroup Ciphertext Ring Field VS1)
    (VS3 : VectorSpaceSig Message Field)(Hack : Nat)(M : Nat)
    (enc : EncryptionSchemePlus Message Ciphertext Ring Field VS1 VS3 MVS)
    (support : BGSupport Message Ciphertext Commitment Ring Field VS2 VS1 MVS VS3
    Hack M enc) <: SigmaPlus Chal.

  Import support.

  (* N = nm *)
  Let n := S (S (S Hack.N)).      (* n *)
  Let m := S (S M.N).     (* m *)
  Import Field.


  Import Mo.
  Import Mo.mat.

  Import EPC.
  Import EPC.MoM.
  Import PC.
 
  Import ALenc.
  Import HardProb.

  Module ALR := RingAddationalLemmas Ring.

  Import VS2.
  Import Commitment.

  (* The billinear map *)
  Definition BM (y : F)(A B : (VF n)) : F :=
    let Y := VandermondeColGen n y 1 in
    VF_sum (Vmap2 Fmul (Vmap2 Fmul A B) Y).

  Lemma BM_VF_scale_l : forall (y : F)(a b : (VF n))(c : F),
    BM y a b * c = BM y (VF_scale a c) b.
  Proof.
    intros. unfold BM. rewrite VF_sum_scale. apply f_equal. apply Veq_nth.
    intros. rewrite Vnth_map. do 4 rewrite Vnth_map2. rewrite Vnth_map.
    field; auto.
  Qed.

  Lemma BM_VF_scale_r : forall (y : F)(a b : (VF n))(c : F),
    BM y a b * c = BM y a (VF_scale b c).
  Proof.
    intros. unfold BM. rewrite VF_sum_scale. apply f_equal. apply Veq_nth.
    intros. rewrite Vnth_map. do 4 rewrite Vnth_map2. rewrite Vnth_map.
    field; auto.
  Qed.

  Lemma  VM_VF_scale : forall (N : nat)(y : F)(a : VF n)(b : vector (VF n) N)(c: VF N),
    (Vmap2 Fmul (Vmap (BM y a) b) c)  = Vmap (BM y a) (Vmap2 (VF_scale (n:=n)) b c).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vnth_map.
    rewrite Vnth_map2. rewrite BM_VF_scale_r. trivial.
  Qed.

  Lemma BM_VF_add_r : forall (y : F)(a c d : (VF n)),
    BM y a (VF_add c d) = BM y a c + BM y a d.
  Proof.
    intros. unfold BM. rewrite VF_sum_add. apply f_equal. apply Veq_nth.
    intros. do 8 rewrite Vnth_map2. unfold FSemiRingT.Aplus. destruct module_ring.
    rewrite <- Rmul_assoc. rewrite Rdistr_l. rewrite Rmul_comm. rewrite Rdistr_l.
    apply f_equal2. rewrite Rmul_comm. rewrite Rmul_assoc. trivial.
    rewrite Rmul_comm. rewrite Rmul_assoc. trivial.
  Qed.

  Lemma BM_VF_add_r_com : forall n' (y : F)(a : VF n)(b : vector (VF n) n'),
    BM y a (Vfold_left (VF_add (n:=n)) (VF_zero n) b) =
  Vfold_left Fadd 0 (Vbuild (fun (i : nat) (ip : i < n') =>
         BM y a (Vnth b ip))).
  Proof.
    intros. induction n'. rewrite (Vector_0_is_nil b). simpl. unfold BM.
    assert (Vmap2 Fmul (Vmap2 Fmul a (Vcons 0 (Vcons 0 (Vcons 0 (VF_zero Hack.N))))) (VandermondeColGen n y 1) =
    VF_zero n). apply Veq_nth. intros. do 2 rewrite Vnth_map2. rewrite Vnth_const.
    ring; auto. rewrite H. rewrite VF_sum_VF_zero. trivial.
    rewrite (VSn_eq b). rewrite Vfold_left_Vcons_VFadd. rewrite <- VSn_eq.
    rewrite BM_VF_add_r.  rewrite IHn'. rewrite <- Vfold_left_Vcons_Fadd.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_cons.
    destruct (lt_ge_dec 0 i). do 2 rewrite Vbuild_nth.
    apply f_equal2; auto. rewrite Vnth_tail. apply Vnth_eq. lia.
    rewrite Vbuild_nth. apply f_equal2; auto. rewrite Vhead_nth. apply Vnth_eq.
    lia.
  Qed.

  Lemma BM_neg : forall y (a b : VF n),
    BM y (VF_neg a) b = Finv (BM y a b).
  Proof.
    intros. unfold BM. rewrite VF_neg_sum. apply f_equal. apply Veq_nth.
    intros. do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map. do 2 rewrite Vnth_map2.
    field; auto.
  Qed.

  Lemma BM_simp : forall y (a b c d : VF n),
    Vmap2 Fmul a b = Vmap2 Fmul c d ->
    BM y a b = BM y c d.
  Proof.
    intros. unfold BM. rewrite H. trivial.
  Qed.


  Lemma BM_VF_comm : forall (y : F)(a b: (VF n)),
    BM y a b = BM y b a.
  Proof.
    intros. unfold BM. apply f_equal. apply Veq_nth. intros. do 4 rewrite Vnth_map2.
    apply f_equal2; auto. destruct module_ring. apply Rmul_comm.
  Qed.

  Lemma BM_VF_add_l : forall (y : F)(a c d : (VF n)),
    BM y (VF_add c d) a = BM y c a + BM y d a.
  Proof.
    intros. unfold BM. rewrite VF_sum_add. apply f_equal. apply Veq_nth.
    intros. do 8 rewrite Vnth_map2. unfold FSemiRingT.Aplus. destruct module_ring.
    rewrite <- Rmul_assoc. rewrite Rdistr_l.
    apply f_equal2. rewrite Rmul_assoc. trivial.
    rewrite Rmul_assoc. trivial.
  Qed.

  Definition St : Type :=
  (* ck=(h,hs) y C_A C_B *)
  G*(VG n)*F*(VG m)*(VG m).
  (* A, r, B, s *)
  Definition W : Type := (vector (VF n) m)*(VF m)*(vector (VF n) m)*(VF m).
  (* a0 r0 b s tau *)
  Definition R : Type := (VF n)*(VF n)*F*F*(VF (S m)*(VF (S M.N))).
  (* cA0 cBm Cd *)
  Definition C : Type := (G*G*(VG (S m+m))).
  (* a r b s t *)
  Definition T : Type := ((VF n)*F*(VF n)*F*F).
  Definition X : Type := (VF n).
  Definition TE : Type := ((VF n)*F*(VF n)*F*F)*(VF m*VF (S M.N)).

  Definition simMapHelp (s : St)(x : X) :=
    let '(h,hs,y,CA,CB) := s in

    hs = Vmap (op h) x.

  Definition Rel (s : St)(w : W) : bool :=
    let '(h,hs,y,CA,CB) := s in
    let '(A,r,B,s)      := w in

      VG_eq CA (comEPC h hs A r) &&
      VG_eq CB (comEPC h hs B s) &&
      Fbool_eq 0 (VF_sum (Vmap2 (BM y) A B)).

  Definition fail_event (s : St)(c : C)(e : VF (S m+m)) : Prop :=
    let '(h,hs,y,CA,CB) := s in

      (* The commitments are broken *)
      (exists c m0 m1 r0 r1, relComPC h (Vnth hs index0) c m0 m1 r0 r1) \/

      (* Schwartz Zipple lemma failed (Two matrices a and b), vector d and opening *)
      (* The big idea is that prover commits to the coefficents, which determine the
       polynomial, before the challenge. If the polynomial sampled at the challenge
      is zero we conclude the polynomial is zero *)
      (exists (a b : vector (VF n) (S m)) d r sOpen t,
        (* Matrix of all the commitments *)
      let mat := Vbuild (fun i (ip: i < S m) => Vbuild (fun j (jp : j < S m) =>
        Gdot (Vnth (Vcons c.1.1 s.1.2) ip)(Vnth (Vadd s.2 c.1.2) jp))) in
        (* Matrix of the openings *)
      let matF2 := Vbuild (fun i (ip: i < S m) => Vbuild (fun j (jp : j < S m) =>
        VF_mult (Vnth a ip)(Vnth b jp))) in

        (* Check to that polynomials are commited hence are indepedent from challenges
         under binding *)
      (Vcons c.1.1 s.1.2) = comEPC h hs a r /\
      (Vadd s.2 c.1.2) = comEPC h hs b sOpen /\
      c.2 = comPC h (Vhead hs) d t /\

        (* If the commited polyonimals are evaluate to zero at the challenge but not equal then
        we allow soundness not to hold (The Schwatz Zippel Lemma says this occurs with
        negligble probabilty). *)
      VF_inProd (VF_sub (Vmap (BM s.1.1.2 (VF_one n)) (ProdOfDiagonalsVF matF2))
                           d) (VandermondeCol (S m + m) (Vhead e)) = 0 /\
      (Vmap (BM s.1.1.2 (VF_one n)) (ProdOfDiagonalsVF matF2)) <> d).

  Definition P0 (stat : St)(rand : R)(wit : W) : St*C :=
    let '(h,hs,y,CA,CB) := stat in

    let a0 := rand.1.1.1.1 in
    let bm := rand.1.1.1.2 in
    let r0 := rand.1.1.2 in
    let sm := rand.1.2 in
    let t  := rand.2 in

    let A := wit.1.1.1 in
    let r := wit.1.1.2 in
    let B := wit.1.2 in
    let s := wit.2 in

    let CA0 := EPC h hs a0 r0 in
    let CBM := EPC h hs bm sm in

    let mat := FMatrix.mat_build (fun i j (ip: i < S m)(jp : j < S m) =>
      (BM y) (Vnth (Vcons a0 A) ip) (Vnth (Vadd B bm) jp)) in

    let CD := comPC h (Vhead hs) (ProdOfDiagonalsF mat)
      (Vapp t.1 (Vcons 0 t.2))   in

    (stat,(CA0, CBM, CD)).


  Definition V0 (ggtoxgtor: St*C)
      (c: F): (St*C*F)
    := (ggtoxgtor, c).

  Definition P1 (ggtoxgtorc: St*C*F)
      (r : R) (w: W) : St*C*F*T :=

    let stat := ggtoxgtorc.1.1 in
    let wit  := w in
    let rand := r in
    let c := ggtoxgtorc.2 in
    
    let '(h,hs,y,CA,CB) := stat in

    let a0 := rand.1.1.1.1 in
    let bm := rand.1.1.1.2 in
    let r0 := rand.1.1.2 in
    let sm := rand.1.2 in
    let t  := rand.2 in

    let A := wit.1.1.1 in
    let r := wit.1.1.2 in
    let B := wit.1.2 in
    let s := wit.2 in

    let xBar := VandermondeCol (S m) c in
    let xK := VandermondeCol (S m + m) c in

    (* aBar = a0 + A xBar , since we tranpose both A and xBar *)
    let aT := Vfold_left (VF_add (n:=n)) (VF_zero n)
      (Vmap2 (VF_scale (n:=n)) (Vcons a0 A) xBar) in
    let rT := VF_sum (VF_mult xBar (Vcons r0 r)) in
    let bT := Vfold_left (VF_add (n:=n)) (VF_zero n)
      (Vmap2 (VF_scale (n:=n)) (Vadd B bm) (rev xBar)) in
    let sT := VF_sum (VF_mult (rev xBar) (Vadd s sm)) in
    let tT := VF_sum (VF_mult xK (Vapp t.1 (Vcons 0 t.2))) in

    (ggtoxgtorc, (aT, rT, bT, sT, tT)).

  Definition V1 (transcript : St*C*F*T) :bool :=
    let stat := transcript.1.1.1 in
    let comm := transcript.1.1.2 in
    let chal := transcript.1.2 in
    let resp := transcript.2 in

    let '(h,hs,y,CA,CB) := stat in

    let CA0 := comm.1.1 in
    let CBM := comm.1.2 in
    let CD := comm.2 in

    let xBar := VandermondeCol (S m) chal in
    let xK := VandermondeCol (S m + m) chal in

    let aT := resp.1.1.1.1 in
    let rT := resp.1.1.1.2 in
    let bT := resp.1.1.2 in
    let sT := resp.1.2 in
    let tT := resp.2 in

    let eq1 := Gbool_eq (VG_prod (VG_Pexp (Vcons CA0 CA) xBar))
       (EPC h hs aT rT) in

    let eq2 := Gbool_eq (VG_prod (VG_Pexp (Vadd CB CBM) (rev xBar)))
      (EPC h hs bT sT) in

    let eq3 := Gbool_eq (VG_prod (VG_Pexp CD xK))
      (PC h (Vnth hs index0) (BM y aT bT) tT) in
    
    let eq4 := Gbool_eq (Vnth CD indexSM)
      (PC h (Vnth hs index0) 0 0) in

    eq1 && eq2 && eq3 && eq4.

  Definition simMap (s : St)(w : W)(c :F)
    (x : X)(r : R) : TE :=

    let '(h,hs,y,CA,CB) := s in

    let a0 := r.1.1.1.1 in
    let bm := r.1.1.1.2 in
    let r0 := r.1.1.2 in
    let sm := r.1.2 in
    let t  := r.2 in

    let A := w.1.1.1 in
    let r := w.1.1.2 in
    let B := w.1.2 in
    let s := w.2 in

    let xBar := VandermondeCol (S m) c in
    let xK := VandermondeCol (S m + m) c in

    (* aBar = a0 + A xBar , since we tranpose both A and xBar *)
    let aT := Vfold_left (VF_add (n:=n)) (VF_zero n)
      (Vmap2 (VF_scale (n:=n)) (Vcons a0 A) xBar) in
    let rT := VF_sum (VF_mult xBar (Vcons r0 r)) in
    let bT := Vfold_left (VF_add (n:=n)) (VF_zero n)
      (Vmap2 (VF_scale (n:=n)) (Vadd B bm) (rev xBar)) in
    let sT := VF_sum (VF_mult (rev xBar) (Vadd s sm)) in
    let tT := VF_sum (VF_mult xK (Vapp t.1 (Vcons 0 t.2))) in

    let mat := FMatrix.mat_build (fun i j (ip: i < S m)(jp : j < S m) =>
      (BM y) (Vnth (Vcons a0 A) ip) (Vnth (Vadd B bm) jp)) in

    let CDFirst := VF_add (Vtail t.1)
      (VF_scale (Vtail (Vbreak (ProdOfDiagonalsF mat)).1) (Vhead x))  in
    let CDSecond := VF_add t.2
      (VF_scale (Vtail (Vbreak (ProdOfDiagonalsF mat)).2) (Vhead x))  in

    ((aT, rT, bT, sT, tT),(CDFirst,CDSecond)).

  Definition simMapInv (s : St)(w : W)(c :F)
    (x : X)(t : TE) : R :=

    let '(h,hs,y,CA,CB) := s in

    let aT := t.1.1.1.1.1 in
    let rT := t.1.1.1.1.2 in
    let bT := t.1.1.1.2 in
    let sT := t.1.1.2 in
    let tT := t.1.2 in
    let CDFirst  := t.2.1 in
    let CDSecond := t.2.2 in

    let A := w.1.1.1 in
    let r := w.1.1.2 in
    let B := w.1.2 in
    let s := w.2 in

    let xBar := VandermondeCol (S m) c in
    let xK := VandermondeCol (S m + m) c in

    (* aBar = a0 + A xBar , since we tranpose both A and xBar *)
    let a0 := VF_sub aT (Vfold_left (VF_add (n:=n)) (VF_zero n)
      (Vmap2 (VF_scale (n:=n)) A (Vtail xBar))) in
    let r0 := rT - VF_sum (VF_mult (Vtail xBar) r) in
    let b := VF_sub bT (Vfold_left (VF_add (n:=n)) (VF_zero n)
      (Vmap2 (VF_scale (n:=n)) B (rev (Vtail xBar)))) in
    let s := sT - VF_sum (VF_mult (rev (Vtail xBar)) s) in

    let mat := FMatrix.mat_build (fun i j (ip: i < S m)(jp : j < S m) =>
      (BM y) (Vnth (Vcons a0 A) ip) (Vnth (Vadd B b) jp)) in

    let t1 := VF_sub CDFirst (VF_scale (Vtail (Vbreak (ProdOfDiagonalsF mat)).1) (Vhead x))
         in
    let t2 := VF_sub CDSecond (VF_scale (Vtail (Vbreak (ProdOfDiagonalsF mat)).2) (Vhead x))
         in

    let tau := tT - VF_sum (VF_mult (Vtail xK) (Vapp t1 (Vcons 0 t2))) in

    (* a0 r0 b s tau *)
    (a0, b, r0, s, ((Vcons tau t1), t2)).

  Definition simulator (s : St)(z : TE)(e : F) :
    (St*C*F*T) :=
    
    let '(h,hs,y,CA,CB) := s in

    let xBar := VandermondeCol (S m) e in
    let xK := VandermondeCol (S m + m) e in

    let aT := z.1.1.1.1.1 in
    let rT := z.1.1.1.1.2 in
    let bT := z.1.1.1.2 in
    let sT := z.1.1.2 in
    let tT := z.1.2 in

    let CDFirst := Vmap (fun x => h^x) z.2.1 in
    let CDSecond := Vmap (fun x => h^x) z.2.2 in

    let CA0 := EPC h hs aT rT o - VG_prod (VG_Pexp CA (Vtail xBar)) in
    let CBM := EPC h hs bT sT o - VG_prod (VG_Pexp CB (Vremove_last (rev xBar)))  in

    let CDM := PC h (Vnth hs index0) 0 0 in
    let CD0 := PC h (Vnth hs index0) (BM y aT bT) tT o -
        VG_prod (VG_Pexp (Vapp CDFirst (Vcons CDM CDSecond)) (Vtail xK))  in
    let CD := Vapp (Vcons CD0 CDFirst) (Vcons CDM CDSecond) in

    (s,(CA0,CBM,CD),e,z.1).

  Definition extractor (s : vector T (S m + m))
        (c : vector F (S m + m)): W :=

    let sM := (Vbreak s).1 in
    let cM := (Vbreak c).1 in

    let aT := FMatrix.mat_transpose (Vmap (fun s1 => s1.1.1.1.1) sM) in
    let rT := Vmap (fun s1 => s1.1.1.1.2) sM in
    let bT := FMatrix.mat_transpose (Vmap (fun s1 => s1.1.1.2) sM) in
    let sT := Vmap (fun s1 => s1.1.2) sM in
    let YM1 := FMatrix.mat_transpose (VandermondeInv cM) in
    let YM2 := FMatrix.mat_transpose (rev (VandermondeInv cM)) in

    (Vtail (FMatrix.mat_transpose (FMatrix.mat_mult aT YM1)),
      Vtail (Vhead (FMatrix.mat_mult [rT] YM1)),
      Vremove_last (FMatrix.mat_transpose (FMatrix.mat_mult bT YM2)),
      Vremove_last (Vhead (FMatrix.mat_mult [sT] YM2))).

  (* Inital lemmas *)
  Lemma TheSMdiagBM : forall (s : St)(w : W)(r : R),
   VF_sum (Vmap2 (BM s.1.1.2) w.1.1.1 w.1.2) =
    Vhead (Vbreak (ProdOfDiagonalsF (FMatrix.mat_build
     (fun (i j : nat) (ip : i < S m) (jp : j < S m) =>
     BM s.1.1.2 (Vnth (Vcons r.1.1.1.1 w.1.1.1) ip)
                 (Vnth (Vadd w.1.2 r.1.1.1.2) jp))))).2.
  Proof.
    intros. rewrite TheSMdiag. apply f_equal. apply Veq_nth. intros.
    rewrite Vbuild_nth. rewrite Vnth_remove_last. rewrite Vnth_tail.
    rewrite FMatrix.mat_build_nth. rewrite Vnth_map2. apply f_equal2.
    rewrite Vnth_cons_tail. apply Vnth_eq. lia. rewrite Vnth_addl. trivial.
  Qed.

  Lemma MatrixAndBillinear_sub : forall (n' l : nat)(y : F)(A B : (vector (VF n) (S n')))
      (c : F),
    Vfold_left Fadd 0
    (Vmap2 Fmul
     (ProdOfDiagonalsF
        (FMatrix.mat_build
           (fun (i j : nat) (ip : i < S n') (jp : j < S n') =>
            BM y (Vnth A ip)
              (Vnth B jp)))) (VandermondeColGen (S n' + n') c l)) =
    BM y
      (Vfold_left (VF_add (n:=n)) (VF_zero n)
         (Vmap2 (VF_scale (n:=n)) A (VandermondeColGen (S n') c l)))
      (Vfold_left (VF_add (n:=n)) (VF_zero n)
         (Vmap2 (VF_scale (n:=n)) B (rev (VandermondeColGen (S n') c 0)))).
   Proof.
    induction n'. intros.
    (* Base case *)
    rewrite ProdOfDiagonalsOneF. pose VF_sum_1_head. unfold VF_sum in e. rewrite e.
    do 2 rewrite Vhead_nth. rewrite Vnth_map2. rewrite FMatrix.mat_build_nth.
    rewrite Vbuild_nth. do 2 rewrite VF_sum_vadd_1_head. do 2 rewrite Vhead_map2.
    do 2 rewrite Vbuild_head. rewrite Vbuild_nth. assert (VF_prod (Vconst c (1 - 0 - 1)) = 1).
    cbn. trivial. rewrite H.
    rewrite VF_scale_1. rewrite BM_VF_scale_l. do 2 rewrite Vhead_nth. trivial.
    (* Extened case *)
    intros. rewrite ProdOfDiagonalsIndF. lia. intros. pose VF_dist. unfold VF_mult in e.
    rewrite e.  pose VF_sum_add. unfold VF_sum in e0. rewrite <- e0.
      (* An absurdly verbose lemma which says that zeros are irrelvant *)
    assert (Vfold_left Fadd 0 (Vmap2 Fmul (Vcast (Vadd (Vcons 0
      (ProdOfDiagonalsF (FMatrix.mat_build (fun (i j : nat) (ip : i < S n')
      (jp : j < S n') => BM y (Vnth (Vtail A) ip) (Vnth (Vtail B) jp))))) 0) Hyp0)
     (VandermondeColGen (S (S n') + S n') c l)) = Vfold_left Fadd 0 (Vmap2 Fmul
      (ProdOfDiagonalsF (FMatrix.mat_build (fun (i j : nat) (ip : i < S n')
      (jp : j < S n') => BM y (Vnth (Vtail A) ip) (Vnth (Vtail B) jp))))
     (VandermondeColGen (S n' + n') c (S l)))).  rewrite Vmap2_Vcast_out. lia. intros.
    rewrite <- Vfold_left_cast_irr.
    rewrite (VSn_add (Vcast (VandermondeColGen (S (S n') + S n') c l) Hyp1)).
    rewrite Vadd_map2. destruct module_ring. rewrite Rmul_comm.
    rewrite ALVS1.whenAutoFail4. rewrite Vfold_left_Vadd_Fadd.
    rewrite Radd_comm. rewrite Radd_0_l.
    rewrite (VSn_eq (Vremove_last (Vcast (VandermondeColGen (S (S n') + S n') c l) Hyp1))).
    rewrite Vcons_map2. rewrite Rmul_comm. rewrite ALVS1.whenAutoFail4.
    rewrite Vfold_left_Vcons_Fadd. rewrite Radd_comm. rewrite Radd_0_l.
    apply f_equal. apply f_equal2; auto. apply Veq_nth. intros. rewrite Vnth_tail.
    rewrite Vnth_remove_last. rewrite Vnth_cast. do 2 rewrite Vbuild_nth.
    apply VG_prod_const_index. lia. exact F. exact F.
    (* Resuming main *)
    rewrite H. rewrite IHn'. rewrite (VSn_eq A). rewrite (VSn_eq B). symmetry.
    rewrite (VSn_eq (rev (VandermondeColGen (S (S n')) c 0))).
    rewrite (VSn_eq (VandermondeColGen (S (S n')) c l)). do 2 rewrite Vcons_map2.
    do 2 rewrite Vfold_left_Vcons_VFadd. rewrite BM_VF_add_l.
    do 2 rewrite BM_VF_add_r. do 2 rewrite <- VSn_eq. destruct module_ring.
    rewrite <- Radd_assoc. apply f_equal2. rewrite VandermondeColGen_tail.
    do 2 rewrite <- VandermondeColGe_eq.
    rewrite VandermondeCol_tail_rev. trivial.
    (* Discharge core matrix only need edges *)
    rewrite (Vbreak_eq_app (VandermondeColGen (S (S n') + S n') c l)).
    rewrite Vapp_map2. rewrite Vfold_left_Vapp_Fadd. rewrite Radd_comm.
    apply f_equal2; auto. rewrite <- BM_VF_add_r. rewrite VandermondeColBreakGen.
      (* First *)
    rewrite <- Vfold_left_Vcons_VFadd. rewrite <- Vcons_map2. do 2 rewrite <- VSn_eq.
    rewrite BM_VF_add_r_com. rewrite Vfold_left_eq_rev; auto. apply f_equal.
     apply Veq_nth. intros.  rewrite Vnth_map2.
    do 3 rewrite Vbuild_nth. rewrite Vnth_map2. unfold BM. rewrite VF_sum_scale.
    apply f_equal. apply Veq_nth. intros. do 2 rewrite Vnth_map2. do 3 rewrite Vnth_map.
    do 2 rewrite Vnth_map2. do 5 rewrite <- Rmul_assoc. apply f_equal2; auto.
    rewrite Rmul_comm. rewrite <- Rmul_assoc. apply f_equal2. apply Veq_nth3; auto.
    apply Vnth_eq. lia. rewrite Rmul_comm. rewrite Rmul_assoc. rewrite Rmul_comm.
    apply f_equal2; auto. rewrite Vhead_nth. do 4 rewrite Vbuild_nth.
    rewrite VF_prod_const. apply VG_prod_const_index. lia.
      (* Last *)
    rewrite BM_VF_comm. rewrite BM_VF_add_r_com. apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vbuild_nth.
    unfold BM. rewrite VF_sum_scale.
    apply f_equal. apply Veq_nth. intros. do 3 rewrite Vnth_map2. do 3 rewrite Vnth_map.
    do 2 rewrite Vnth_map2. assert (forall a b c d e f, b*d=e -> a * b * (c * d)*f  = c * a * f* e).
    intros. rewrite <- H0. ring; auto. apply H0. rewrite Vnth_vbreak_2. lia. intros.
    rewrite Vhead_nth. rewrite Vnth_tail. do 4 rewrite Vbuild_nth. rewrite VF_prod_const.
    apply VG_prod_const_index. lia.
    (* and done *)
  Qed.

  Lemma MatrixAndBillinear : forall (n' : nat)(y : F)(A B : (vector (VF n) (S n')))
      (c : F),
    Vfold_left Fadd 0
    (Vmap2 Fmul
     (ProdOfDiagonalsF
        (FMatrix.mat_build
           (fun (i j : nat) (ip : i < S n') (jp : j < S n') =>
            BM y (Vnth A ip)
              (Vnth B jp)))) (VandermondeCol (S n' + n') c)) =
    BM y
      (Vfold_left (VF_add (n:=n)) (VF_zero n)
         (Vmap2 (VF_scale (n:=n)) A (VandermondeCol (S n') c)))
      (Vfold_left (VF_add (n:=n)) (VF_zero n)
         (Vmap2 (VF_scale (n:=n)) B (rev (VandermondeCol (S n') c)))).
   Proof.
    intros. remember (rev (VandermondeCol (S n') c)) as d.
    do 2 rewrite VandermondeColGe_eq. rewrite Heqd. rewrite VandermondeColGe_eq.
    apply MatrixAndBillinear_sub.
  Qed.

  Lemma Matrix_infold : forall (A B : vector (VF n) (S m))(c: F),
    ProdOfDiagonalsVF (Vbuild (fun (i : nat) (ip : i < S m) =>
     Vbuild (fun (j : nat) (jp : j < S m) =>  VF_mult
     (Vnth (Vmap2 (VF_scale (n:=n)) A (VandermondeCol (S m) c)) ip)
     (Vnth (Vmap2 (VF_scale (n:=n)) B (rev (VandermondeCol (S  m) c)))  jp)))) =
     Vmap2 (VF_scale (n:=n)) (ProdOfDiagonalsVF (Vbuild (fun (i : nat) (ip : i < S m) =>
     Vbuild (fun (j : nat) (jp : j < S m) =>  VF_mult (Vnth A ip) (Vnth B jp)))))
        (VandermondeCol (S m + m) c).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. unfold ProdOfDiagonalsVF,
    ProdOfDiagonals. rewrite Vnth_app. rewrite Vnth_app. destruct (le_gt_dec (S m) i).
    (* 1 of 2 *)
    rewrite Vbuild_nth. do 3 rewrite Vbuild_nth. rewrite VF_scale_VF_add. apply f_equal.
    apply Veq_nth.  intros. rewrite Vnth_map. do 7 rewrite Vbuild_nth. do 2 rewrite Vnth_map2.
    apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_map. rewrite Vnth_map2.
    destruct module_ring. do 2 rewrite <- Rmul_assoc. apply f_equal2; auto.
    rewrite Rmul_comm. rewrite <- Rmul_assoc. apply f_equal2; auto.
    do 3 rewrite Vbuild_nth. rewrite VF_prod_const. apply VG_prod_const_index. lia.
    (* 2 of 2 *)
    rewrite Vbuild_nth. rewrite Vbuild_nth. rewrite VF_scale_VF_add. apply f_equal.
    apply Veq_nth.  intros. rewrite Vnth_map. do 7 rewrite Vbuild_nth. do 2 rewrite Vnth_map2.
    apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_map. rewrite Vnth_map2.
    destruct module_ring. do 2 rewrite <- Rmul_assoc. apply f_equal2; auto.
    rewrite Rmul_comm. rewrite <- Rmul_assoc. apply f_equal2; auto.
    do 3 rewrite Vbuild_nth. rewrite VF_prod_const. apply VG_prod_const_index. lia.
  Qed.

  (* Main theorem *)
    Ltac simpl_prod := repeat progress (try rewrite Prod_left_replace;
      try rewrite Prod_right_replace).

  Definition M := (Nat.add (S m) m).
  
  Lemma pres_p0 : forall (s : St)(r : R)(w : W), (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. unfold P0. destruct s, p, p, p. trivial.
  Qed.

  Lemma pres_v0 : forall (sc : St*C)(e : Chal.G), (V0 sc e) = (sc,(V0 sc e).2).
  Proof.
    intros. destruct sc. destruct s, p, p, p. trivial.
  Qed.

  Lemma pres_p1 : forall (sce : St*C*Chal.G)(r : R)(w : W),
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Proof.
    intros. destruct sce. destruct p. destruct s, p, p, p. trivial.
  Qed.

  Lemma pres_sim : forall (s: St)(t : TE)(e : Chal.G),
      s = (simulator s t e).1.1.1.  Proof.
    intros. destruct s, p, p, p. trivial.
  Qed.

  Lemma chal_sim : forall (s: St)(t : TE)(e : Chal.G),
    e = (simulator s t e).1.2.
  Proof.
    intros. destruct s, p, p, p. trivial.
  Qed.


  (** Properties *)
  Lemma correctness : forall (s :St)(w:W)(r:R)(c: Chal.G),
    Rel s w ->
    V1 (P1 (V0 (P0 s r w) c) r w) = true.
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.
    pose Commitment.module_abegrp.
    intros. unfold V1. unfold V0. unfold P1.
    unfold P0. unfold Rel in *. destruct s, p, p, p. destruct w,p,p.
    do 9 rewrite Prod_right_replace. do 6 rewrite Prod_left_replace.
    apply andb_true_iff in H. destruct H. apply andb_true_iff in H.
    destruct H. apply VGeq in H. apply VGeq in H1. apply F_bool_eq_corr in H0.
    apply andb_true_iff. split. apply andb_true_iff. split.
    apply andb_true_iff. split. apply bool_eq_corr. rewrite H.
    (* 1/4 *)
    rewrite comEPCVcons. unfold VG_Pexp. rewrite comEPCDis. rewrite EPCMultExt.
    apply f_equal. apply f_equal2. trivial. rewrite VF_comm_mult.
    unfold VF_mult. trivial.
    (* 2/4 *)
    apply bool_eq_corr. rewrite H1. rewrite comEPCVadd. unfold VG_Pexp.
    rewrite comEPCDis. rewrite EPCMultExt. apply f_equal. apply f_equal2.
    trivial. rewrite VF_comm_mult. unfold VF_mult. trivial.
    (* 3/4 *)
    apply bool_eq_corr. unfold VG_Pexp. rewrite comPCDis. unfold VG_prod.
    rewrite <- PCMultExt. apply f_equal3. rewrite Vhead_nth. apply Vnth_eq.
    trivial.
    (* The part with the matrix *)
    apply MatrixAndBillinear.
    (* and we're back *)
    rewrite VF_comm_mult. trivial.
    (* 4/4 *)
    apply bool_eq_corr. rewrite Vnth_map2. do 2 rewrite Vnth_app.
    destruct (le_gt_dec (S m) (S support.m)). apply f_equal3.
    rewrite Vhead_nth. apply Vnth_eq. trivial.
    (* Proving the m+1 diagonal is equal relation and hence 0 *)
    rewrite Vbuild_nth. rewrite Vbuild_nth. remember (Vfold_left Fadd 0) as sum. rewrite H0.
    assert (m = S (m - (S support.m - S m) - 1)).
    unfold support.m, m. lia. rewrite Heqsum. unfold VF_sum in *. symmetry.
    apply (Vfold_left_eq_cast H2).
    apply Veq_nth. intros. rewrite Vbuild_nth. rewrite FMatrix.mat_build_nth.
    rewrite Vnth_cast. rewrite Vnth_map2.
    (* time to prove a and b separately *)
    apply f_equal2. rewrite Vnth_cons.
    assert (Nat.sub (S support.m) (S m) = 0%nat). unfold m, support.m in *. lia.
    destruct (lt_ge_dec 0 (i + (m - (m - (S support.m - S m) - 1)))).
    (* normal a case *)
    apply Vnth_eq. rewrite H3. lia.
    (* absurd a case *)
    rewrite H3 in g0. assert False. lia. contradiction.
    (* absurd b case *)
    rewrite Vnth_add. destruct (Nat.eq_dec i m).
    assert (i < S (m - (S support.m - S m) - 1)). trivial.
    rewrite <- H2 in H3. assert False. lia. contradiction.
    (* normal b case *)
    apply Vnth_eq. trivial.
    (* And now the rest is easy *)
    rewrite Vnth_cons. destruct (lt_ge_dec 0 (S support.m - S m)).
    assert False. unfold support.m in l0. unfold m in l0. lia. contradiction.
    trivial.
    assert False. unfold support.m in g0. unfold m in g0. lia. contradiction.
  Qed.

  Definition allDifferent (e : vector Chal.G M) := PairwisePredicate Chal.Gdisjoint e.

  Lemma special_soundness : forall (s : St)(c : C)(e : vector Chal.G M)(t : vector T M),
    (* Forall e it is disjoint from all e *)
    allDifferent e  ->
    bVforall2 (fun e1 t1 => V1 (s, c, e1, t1)) e t ->
    Rel s (extractor t e) = true \/ fail_event s c e.
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.
    pose Commitment.module_abegrp. intros.  unfold V1. unfold V0. unfold P1.
    unfold P0. unfold Rel in *. unfold fail_event. unfold V1 in H0.
    destruct s, p, p, p.
    do 3 (apply bVforall2Split in H0; destruct H0).
    remember (VandermondeCol (S m)) as d. remember (VG_Pexp) as f0. simpl in H0.
    simpl in H3. simpl in H2. simpl in H1. rewrite Heqd in H0. rewrite Heqf0 in H0.
    assert (S (S (S (M.N + m))) = Nat.add (S (S (S M.N))) (S (S M.N))). unfold m. lia. unfold m in *.
     pose (Vbreak (Vcast e H4)).1 as e'. pose (Vbreak (Vcast t H4)).1 as t'.
    assert (PairwisePredicate Chal.Gdisjoint e); auto.
    apply (PairwisePredicate_break (S (S (S M.N))) (S (S M.N)) e Chal.Gdisjoint H4) in H5.
    apply (bVforall2_break (S (S (S M.N))) (S (S M.N)) e t (fun (a' : F) (b' : T) =>
        Gbool_eq
          (VG_prod (VG_Pexp (Vcons c.1.1 v0) (VandermondeCol (S (S (S M.N))) a')))
          (EPC g v1 b'.1.1.1.1 b'.1.1.1.2)) H4) in H0. destruct H0.
    (* Ca *)
    pose (commitOpen e' (fun x => x.1.1.1.1) (fun x => x.1.1.1.2) (Vcons c.1.1 v0)
    g v1 t' H5 H0).
    (* Cb *)
    apply (bVforall2_break (S (S (S M.N))) (S (S M.N)) e t (fun (a' : F) (b' : T) =>
        Gbool_eq (VG_prod (f0 (S (S (S M.N))) (Vadd v c.1.2) (rev (d a'))))
          (EPC g v1 b'.1.1.2 b'.1.2)) H4) in H3. destruct H3.
    rewrite Heqf0 in H3. assert (bVforall2
       (fun (a' : F) (b' : T) =>
        Gbool_eq (VG_prod (VG_Pexp (rev (Vadd v c.1.2)) (VandermondeCol (S(S (S M.N))) a')))
          (EPC g v1 b'.1.1.2 b'.1.2)) e' t'). apply bVforall2_nth_intro.
    intros. apply (bVforall2_elim_nth ip e' t') in H3. apply bool_eq_corr.
    apply bool_eq_corr in H3. rewrite VG_prod_rev. rewrite rev_vmap2. rewrite rev_rev.
    rewrite <- H3. rewrite Heqd. unfold VG_Pexp. trivial.
    pose (commitOpen e' (fun x => x.1.1.2) (fun x => x.1.2) (rev (Vadd v c.1.2))
    g v1 t' H5 H8).
    (* Cd *)
    rewrite Heqf0 in H2.
    pose (commitOpenPC e (fun b' => BM f b'.1.1.1.1 b'.1.1.2) (fun b => b.2)
       c.2 g (Vnth v1 index0) t H H2).
    
    apply bVforall2Clear in H1. apply bool_eq_corr in H1.
    assert (Vnth c.2 indexSM = PC g (Vnth v1 index0)
    (VF_inProd (Vmap (fun b'=> BM f b'.1.1.1.1 b'.1.1.2) t) (Vnth (VandermondeInv e) indexSM))
    (VF_inProd (Vmap (fun b'=> b'.2) t) (Vnth (VandermondeInv e) indexSM))).
    rewrite e2. rewrite Vnth_map2. do 2 rewrite Vhead_nth. do 2 rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_row. do 2 rewrite Vnth0. unfold VF_inProd. rewrite FMatrix.mat_transpose_row_col.
    unfold FMatrix.get_row. trivial.
    (* Final *)
     (* Commitments were broken *)
     destruct_with_eqn (Fbool_eq 0 (VF_inProd (Vmap
     (fun b' : VF n * F * VF n * F * F =>
      BM f b'.1.1.1.1 b'.1.1.2) t)
      (Vnth (VandermondeInv e) indexSM))).
    (* The case where SZ fails *)
    destruct_with_eqn (VF_beq (Vmap (BM f (VF_one n)) (ProdOfDiagonalsVF
      (Vbuild (fun i (ip: i < S m) => Vbuild (fun j (jp : j < S m) =>
        Vmap2 Fmul (Vnth (FMatrix.mat_mult (VandermondeInv e') (Vmap (fun x => x.1.1.1.1) t')) ip)
          (Vnth (FMatrix.mat_mult (rev (VandermondeInv e')) (Vmap (fun x => x.1.1.2) t')) jp)))))
    ) (Vhead
        (FMatrix.mat_mult
           [Vmap
              (fun b' : VF n * F * VF n * F * F =>
               BM f b'.1.1.1.1 b'.1.1.2) t]
           (FMatrix.mat_transpose (VandermondeInv e))))). intros.
    (* 1 of 3 *)
    + intros. left. apply andb_true_iff. split. apply andb_true_iff. split.
    apply Vtail_imp in e0. rewrite e0. apply VGeq. apply Veq_nth.
    intros. rewrite Vnth_tail. do 2 rewrite Vnth_map2. apply f_equal2.
    unfold extractor. rewrite Prod_left_replace. rewrite transpose_move_gen.
    do 2 rewrite FMatrix.mat_transpose_idem. rewrite Vnth_tail. apply Veq_nth.
    intros. do 2 rewrite FMatrix.mat_build_nth. apply f_equal2. unfold FMatrix.get_row.
    unfold e'. apply Veq_nth3; auto. apply f_equal. apply Veq_nth. intros.
    rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_vbreak_1. rewrite Vnth_cast.
    apply Vnth_eq. trivial. apply Veq_nth. intros.
    do 4 rewrite Vnth_map. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_vbreak_1. rewrite Vnth_cast. apply Veq_nth3; auto.
    apply f_equal. apply f_equal. apply f_equal. apply f_equal.
    apply Vnth_eq. trivial.  unfold extractor.
    rewrite Vnth_tail. do 2 rewrite Vhead_nth. do 2 rewrite FMatrix.mat_build_nth.
     apply f_equal2. unfold FMatrix.get_row. do 2 rewrite Vnth0_2. apply Veq_nth.
    intros. do 2 rewrite Vnth_map. rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_vbreak_1.
    do 4 apply f_equal. rewrite Vnth_cast. apply Vnth_eq. trivial.
    apply Veq_nth. intros. do 2 rewrite Vnth_map.
    apply Veq_nth3; auto. apply Veq_nth3; auto. apply f_equal. apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_vbreak_1.
    rewrite Vnth_cast. apply Vnth_eq. trivial.
    (* 2 of 3 *)
    assert (Vtail (rev (Vadd v c.1.2)) = Vtail (comEPC g v1
     (FMatrix.mat_mult (VandermondeInv e')
        (Vmap (fun x : VF n * F * VF n * F * F => x.1.1.2) t')) (Vhead
        (FMatrix.mat_mult [Vmap (fun x : VF n * F * VF n * F * F => x.1.2) t']
           (FMatrix.mat_transpose (VandermondeInv e')))))). rewrite e1. trivial.
    rewrite <- Vcons_rev in H10. assert (forall (a : G) (b :VG m), Vtail (Vcons a b) = b).
    intros. simpl. trivial. rewrite H11 in H10. apply rev_switch in H10. rewrite H10.
    apply VGeq. apply Veq_nth. intros. rewrite Vbuild_nth. rewrite Vnth_tail.
    unfold extractor. do 2 rewrite Vnth_map2.
    apply f_equal2. rewrite Vnth_remove_last. rewrite transpose_move_gen.
    do 2 rewrite FMatrix.mat_transpose_idem. apply Veq_nth. intros.
    do 2 rewrite FMatrix.mat_build_nth. apply f_equal2. unfold FMatrix.get_row.
    do 1 rewrite Vbuild_nth. apply Veq_nth3. unfold m. lia. unfold e'.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_vbreak_1.
    rewrite Vnth_cast. apply Vnth_eq. lia.  unfold t'.
    apply Veq_nth. intros.
    intros. do 4 rewrite Vnth_map. apply Veq_nth3; auto. do 3 apply f_equal.
    rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_vbreak_1. rewrite Vnth_cast.
    apply Vnth_eq. trivial.
    rewrite Vnth_remove_last. do 2 rewrite Vhead_nth. do 2 rewrite FMatrix.mat_build_nth.
    apply f_equal2. unfold FMatrix.get_row. do 2 rewrite Vnth0_2. apply Veq_nth.
    intros. do 2 rewrite Vnth_map. rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_vbreak_1.
    do 2 apply f_equal. rewrite Vnth_cast. apply Vnth_eq. trivial.
    apply Veq_nth. intros. do 2 rewrite Vnth_map. do 2 rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_elem. unfold FMatrix.get_row. rewrite Vbuild_nth.
    apply Veq_nth3; auto. unfold e'. apply Veq_nth3. unfold m. lia.
    apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_vbreak_1. lia.  intros. rewrite Vnth_vbreak_1.
    rewrite Vnth_cast. apply Vnth_eq. lia. unfold t'.
    (* 3 of 3 *)
    assert (VF_inProd (Vmap (fun b' => BM f b'.1.1.1.1 b'.1.1.2) t)
      (Vnth (VandermondeInv e) indexSM) = VF_sum (Vmap2 (BM f) (extractor t e).1.1.1
     (extractor t e).1.2)).
    (* The bit with the Schwatz Zippel Lemma *)
      ++ apply VF_beq_true in Heqb0. apply (Veq_nth4 indexSM) in Heqb0.
         rewrite Vhead_nth in Heqb0.
    rewrite FMatrix.mat_build_nth in Heqb0. rewrite FMatrix.mat_transpose_row_col in Heqb0.
    unfold FMatrix.get_row in Heqb0. unfold VF_inProd. assert (Vnth
    [Vmap (fun b' => BM f b'.1.1.1.1 b'.1.1.2) t] (Nat.lt_0_succ 0) =
    Vmap (fun b' => BM f b'.1.1.1.1 b'.1.1.2) t). simpl. trivial. rewrite H10 in Heqb0.
    symmetry in Heqb0. rewrite Heqb0. rewrite Vnth_map. unfold BM. rewrite TheSMdiagindexSM.
    rewrite Prod_left_replace. rewrite Prod_right_replace. do 2 rewrite  transpose_move_gen.
    do 4 rewrite FMatrix.mat_transpose_idem. assert (forall a, Vmap2 Fmul (VF_one n) a = a).
    intros. pose VF_comm_mult. pose VF_mult_one. unfold VF_mult in *. rewrite e3. apply e4.
    rewrite H11. pose VF_Fadd_dist. pose VF_comm_mult. unfold VF_mult in *. rewrite e4. rewrite e3.
    rewrite VF_sum_sum. apply f_equal. apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_map2.
    apply f_equal. rewrite Vnth_map. rewrite e4. apply f_equal2; auto. rewrite Vbuild_nth.
    do 2 rewrite Vnth_remove_last. do 2 rewrite Vnth_tail. do 2 rewrite Vbuild_nth. unfold e'.
    unfold t'. apply f_equal2. apply Veq_nth. intros. do 2 rewrite FMatrix.mat_mult_elem.
    apply f_equal2. unfold FMatrix.get_row. rewrite Vcast_refl. trivial.
    rewrite Vcast_refl. trivial. do 2 rewrite Vcast_refl. trivial.
      ++ apply F_bool_eq_corr. apply F_bool_eq_corr in Heqb. rewrite Heqb. rewrite H10.
         trivial.
    (* SZ failed. *)
    (* And we go *)
    + intros. right. right.
    exists (FMatrix.mat_mult (VandermondeInv e') (Vmap (fun x =>  x.1.1.1.1) t')).
    exists (FMatrix.mat_mult (rev (VandermondeInv e')) (Vmap (fun x => x.1.1.2) t')).
    exists (Vhead (FMatrix.mat_mult [Vmap (fun b' => BM f
      b'.1.1.1.1 b'.1.1.2) t] (FMatrix.mat_transpose (VandermondeInv e)))).
    exists (Vhead (FMatrix.mat_mult
           [Vmap (fun x : VF n * F * VF n * F * F => x.1.1.1.2) t']
           (FMatrix.mat_transpose (VandermondeInv e')))).
    exists (rev (Vhead (FMatrix.mat_mult
           [Vmap (fun x : VF n * F * VF n * F * F => x.1.2) t']
           (FMatrix.mat_transpose (VandermondeInv e'))))).
    exists (Vhead (FMatrix.mat_mult [Vmap [eta snd] t] (FMatrix.mat_transpose (VandermondeInv e)))).
    split; auto.
    (* Opens commitment 2 *)
    split. apply comEPCrev in e1. rewrite rev_rev in e1. rewrite e1. apply f_equal2; auto.
    apply Veq_nth. intros. rewrite Vbuild_nth. apply Veq_nth. intros.
    do 2 rewrite FMatrix.mat_mult_elem.  unfold FMatrix.get_row. do 1 rewrite Vbuild_nth.
    trivial.
    (* Opens commitment 3 *)
    split. rewrite e2. apply f_equal3; auto.
    rewrite Vhead_nth. apply Vnth_eq. trivial. split.
    (* Look at polynomial *)
    ++++ rewrite VF_sub_corr. rewrite InProd_Sum. pose VF_dist. unfold VF_mult in e3.
    rewrite e3. rewrite <- VF_sum_add. pose VF_neg_mul. unfold VF_mult in e4.
    rewrite <- e4. rewrite <- VF_neg_sum. rewrite <- shift.
    (* I'm pretty sure this should hold by defintion but anyway. *)
    assert (VF_sum (Vmap2 Fmul (Vmap (BM f (VF_one n)) (ProdOfDiagonalsVF
    (Vbuild (fun (i : nat) (ip : i < S (S (S M.N))) => Vbuild
    (fun (j : nat) (jp : j < S (S (S M.N))) => VF_mult
    (Vnth (FMatrix.mat_mult (VandermondeInv e') (Vmap (fun x => x.1.1.1.1) t')) ip)
    (Vnth (FMatrix.mat_mult (rev (VandermondeInv e')) (Vmap (fun x => x.1.1.2) t')) jp))))))
     (VandermondeCol (S (S (S M.N)) + S (S M.N)) (Vhead e))) = BM f (Vhead t').1.1.1.1 (Vhead t').1.1.2).
    (* Now for the hard part *)
    rewrite VM_VF_scale.
    rewrite <- Matrix_infold. unfold BM. assert (forall n' (a : vector (VF n) n'), Vmap  (fun B : VF n =>
    VF_sum (Vmap2 Fmul (Vmap2 Fmul (VF_one n) B) (VandermondeColGen n f 1))) a =
    Vmap (VF_sum (n:=n)) (Vmap (fun B : VF n => (Vmap2 Fmul (Vmap2 Fmul (VF_one n) B)
    (VandermondeColGen n f 1))) a)). intros. apply Veq_nth. intros.
    do 3 rewrite Vnth_map. trivial. rewrite H10. rewrite <- VF_sum_sum. unfold BM.
    apply f_equal. apply Veq_nth. intros. rewrite Vfold_left_VF_add.
    (* Seems pretty sensiable to here *)
    do 2 rewrite Vnth_map2. assert (Vmap (fun v : vector F n => Vnth v ip)
    (Vmap (fun B : VF n =>  Vmap2 Fmul (Vmap2 Fmul (VF_one n) B) (VandermondeColGen n f 1))
    (ProdOfDiagonalsVF (Vbuild (fun (i0 : nat) (ip0 : i0 < S m) => Vbuild
    (fun (j : nat) (jp : j < S m) => VF_mult (Vnth (Vmap2 (VF_scale (n:=n))
    (FMatrix.mat_mult (VandermondeInv e') (Vmap (fun x  => x.1.1.1.1)
                                t')) (VandermondeCol (S m) (Vhead e))) ip0)
    (Vnth (Vmap2 (VF_scale (n:=n)) (FMatrix.mat_mult (rev (VandermondeInv e'))
    (Vmap (fun x => x.1.1.2) t')) (rev (VandermondeCol (S m) (Vhead e)))) jp))))))  =
    Vmap (fun x => Vnth (VF_mult x (VandermondeColGen n f 1)) ip) (ProdOfDiagonalsVF
           (Vbuild
              (fun (i0 : nat) (ip0 : i0 < S m) =>
               Vbuild
                 (fun (j : nat) (jp : j < S m) =>
                  VF_mult
                    (Vnth
                       (Vmap2 (VF_scale (n:=n))
                          (FMatrix.mat_mult (VandermondeInv e')
                             (Vmap (fun x : VF n * F * VF n * F * F => x.1.1.1.1)
                                t')) (VandermondeCol (S m) (Vhead e))) ip0)
                    (Vnth
                       (Vmap2 (VF_scale (n:=n))
                          (FMatrix.mat_mult (rev (VandermondeInv e'))
                             (Vmap (fun x : VF n * F * VF n * F * F => x.1.1.2) t'))
                          (rev (VandermondeCol (S m) (Vhead e)))) jp)))))).
    apply Veq_nth. intros. do 2 rewrite Vnth_map.
    assert (forall n a, Vmap2 Fmul (VF_one n) a = a). intros. apply Veq_nth.
   intros. rewrite Vnth_map2. rewrite Vnth_const. ring; auto. rewrite H11.
   rewrite Vnth_map. rewrite Vnth_map2. trivial. rewrite H11.
   assert (forall n' (a : vector (VF n) n'), Vfold_left Fadd 0
  (Vmap (fun x : VF n => Vnth (VF_mult x (VandermondeColGen n f 1)) ip) a) =
    Vfold_left Fadd 0 (Vmap (fun x => Vnth x ip) a) * Vnth (VandermondeColGen n f 1) ip).
    intros. rewrite VF_sum_scale. apply f_equal. apply Veq_nth. intros.
    do 3 rewrite Vnth_map. rewrite Vnth_map2. trivial. rewrite H12. apply f_equal2; auto.
    rewrite <- Vfold_left_VF_add. assert (Vnth (Vhead t').1.1.1.1 ip * Vnth (Vhead t').1.1.2 ip =
    Vnth (VF_mult ((Vhead t').1.1.1.1) ((Vhead t').1.1.2)) ip).
    rewrite Vnth_map2. trivial. rewrite H13.  apply Veq_nth3; auto.
    (* We have now discharged the billinear map *) clear e0.
    remember (FMatrix.mat_mult (VandermondeInv e')
                       (Vmap (fun x : VF n * F * VF n * F * F => x.1.1.1.1) t')) as TempA.
    remember (FMatrix.mat_mult (rev (VandermondeInv e'))
                       (Vmap (fun x : VF n * F * VF n * F * F => x.1.1.2) t')) as TempB.
    assert (VandermondeCol (S m) (Vhead e) = Vhead (Vandermonde e')). rewrite Vhead_map.
    unfold m. apply f_equal. unfold e'. do 2 rewrite Vhead_nth. rewrite Vnth_vbreak_1. lia.
    intros. rewrite Vnth_cast. apply Vnth_eq. trivial.
    (* Case 1 *)
    assert ((Vhead t').1.1.1.1 = Vfold_left (VF_add (n:=n)) (VF_zero n)
     (Vmap2 (VF_scale (n:=n)) TempA (VandermondeCol (S m) (Vhead e)))).
    rewrite HeqTempA. rewrite scale_mult. rewrite VF_add_transpose. apply Veq_nth. intros.
    do 2 rewrite Vnth_map. rewrite <- InProd_Sum. pose FMatrix.mat_transpose_col_row.
    unfold FMatrix.get_row in e0. rewrite e0. rewrite <- MF_getCol_prod_gen.
    rewrite <- mat_mult_assoc_gen. rewrite H14. rewrite <- Vhead_mat_mult.
    pose invVandermondeRight. unfold MF_mult in e5. rewrite e5; auto. do 3 rewrite Vhead_nth.
    rewrite FMatrix.mat_build_nth. rewrite Vbuild_nth. unfold FMatrix.get_row.
    rewrite Vnth0. rewrite FMatrix.VA.dot_product_id. do 2 rewrite Vnth_map. trivial.
    (* Case 2 *)
    assert ((Vhead t').1.1.2 = Vfold_left (VF_add (n:=n)) (VF_zero n)
     (Vmap2 (VF_scale (n:=n)) TempB (rev (VandermondeCol (S m) (Vhead e))))).
    rewrite HeqTempB. rewrite scale_mult. rewrite VF_add_transpose. apply Veq_nth. intros.
    do 2 rewrite Vnth_map. rewrite <- InProd_Sum. pose FMatrix.mat_transpose_col_row.
    unfold FMatrix.get_row in e0. rewrite e0. rewrite <- MF_getCol_prod_gen.
    rewrite <- mat_mult_assoc_gen. assert (rev (VandermondeCol (S m) (Vhead e)) =
    Vhead (Vmap (fun x => rev x) (Vandermonde e'))). apply Veq_nth. intros.
    rewrite Vbuild_nth. do 2 rewrite Vhead_map. do 3 rewrite Vbuild_nth.
    unfold m. apply f_equal. apply Veq_nth. intros. do 2 rewrite Vnth_const.
    do 2 rewrite Vhead_nth. unfold e'. rewrite Vnth_vbreak_1. lia. intros. rewrite Vnth_cast.
    apply Vnth_eq. trivial.
    rewrite H16. rewrite <- Vhead_mat_mult.
    assert (FMatrix.mat_mult (Vmap [eta rev (n:=S (S (S M.N)))] (Vandermonde e'))
              (rev (VandermondeInv e')) = (MF_id (S (S (S M.N))))). apply Veq_nth. intros.
     apply Veq_nth. intros. rewrite FMatrix.mat_build_nth. unfold FMatrix.get_row.
    rewrite Vnth_map. rewrite <- (@invVandermondeRight (S (S (S M.N))) e'); auto. (* rewrite Vbuild_nth. *)
    rewrite FMatrix.mat_build_nth. rewrite rev_col. assert (forall n (a b : VF n),
    FMatrix.VA.dot_product (rev a) (rev b) = FMatrix.VA.dot_product a b). intros.
    unfold FMatrix.VA.dot_product. do 2 rewrite Vfold_left_Fadd_eq.
    rewrite Vfold_left_eq_rev.
    rewrite rev_vmap2. do 2 rewrite rev_rev. trivial.
     intros. ring; auto. intros. ring; auto.
    apply H17. rewrite H17. do 2 rewrite Vhead_nth. rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_row. rewrite Vnth0. rewrite Vbuild_head. rewrite FMatrix.VA.dot_product_id.
    do 2 rewrite Vnth_map. trivial.
    (* Utilise *)
    rewrite H15. rewrite H16. remember (Vmap2 (VF_scale (n:=n)) TempA (VandermondeCol (S m) (Vhead e))) as TempC.
    remember (Vmap2 (VF_scale (n:=n)) TempB (rev (VandermondeCol (S m) (Vhead e)))) as TempD.
    apply prod_exp.
    (* On the home strech *)
    rewrite H10. rewrite <- InProd_Sum. assert (VandermondeCol ((S (S (S M.N)) + S (S M.N)))
   (Vhead e) = Vhead (Vandermonde e)). rewrite Vhead_map. apply f_equal. trivial. rewrite H11.
    do 3 rewrite Vhead_nth. rewrite <- MF_getRow_prod_gen. rewrite mat_mult_assoc_gen.
    rewrite <- transpose_move_gen. do 3 rewrite <- Vhead_nth. rewrite <- Vhead_mat_mult.
    pose invVandermondeRight. unfold MF_mult in e5. rewrite e5; auto.
    rewrite Vhead_nth. do 2 rewrite Vhead_nth. rewrite FMatrix.mat_build_nth.
    rewrite FMatrix.mat_transpose_row_col. unfold FMatrix.get_row. do 2 rewrite Vnth0.
    rewrite Vbuild_head. rewrite FMatrix.VA.dot_product_comm. rewrite FMatrix.VA.dot_product_id.
    rewrite Vnth_map. apply f_equal2. do 4 apply f_equal. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_cast. apply Vnth_eq. trivial. do 3 apply f_equal. rewrite Vnth_vbreak_1. lia.
    intros.  rewrite Vnth_cast. apply Vnth_eq. trivial.
    (* It was zero *)
    ++++ apply VF_beq_false in Heqb0. unfold not in *. intros.
    rewrite <- H10 in Heqb0. apply Heqb0. unfold m, VF_mult in *.
    do 3 apply f_equal. trivial.
    (* commitments are broken *)
    + intros. right. left. unfold relComPC. exists (Vnth c.2 indexSM). exists 0.
    exists (VF_inProd  (Vmap (fun b' => BM f b'.1.1.1.1 b'.1.1.2) t) (Vnth (VandermondeInv e) indexSM)).
    exists 0. exists (VF_inProd (Vmap [eta snd] t) (Vnth (VandermondeInv e) indexSM)).
    split. apply F_bool_neq_corr in Heqb. trivial. split; auto.
  Qed.

  Lemma honest_verifier_ZK :
    forall (s : St)(w : W)(e : Chal.G)(x : X)(r : R)(t : TE),
      simMapHelp s x ->
      Rel s w ->
      ((P1(V0 (P0 s r w) e) r w) =
      simulator s (simMap s w e x r) e) /\
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.
    pose Commitment.module_abegrp. intros.  unfold V1. unfold V0. unfold P1.
    unfold P0.
    unfold simMap, simMapInv. rewrite Prod_right_replace.
    simpl in x. simpl in t. simpl in H. destruct s, p, p, p. destruct w,p,p.
    split. intros.
    do 3 rewrite Prod_left_replace. apply injective_projections.
    do 2 rewrite Prod_left_replace. apply injective_projections.
    do 2 rewrite Prod_left_replace. apply injective_projections.
    (* Statment *)
    trivial.
    (* Commitments *)
    ++ do 7 rewrite Prod_right_replace. apply andb_true_iff in H0. destruct H0.
    apply andb_true_iff in H0. destruct H0. apply VGeq in H0.
    apply VGeq in H2. apply F_bool_eq_corr in H1.
    apply injective_projections.
    do 2 rewrite Prod_left_replace. apply injective_projections.
    do 2 rewrite Prod_left_replace.
    (* Commitments 1/3 *)
    +++ do 4 rewrite Prod_left_replace. rewrite Prod_right_replace. rewrite H0.
    rewrite (VSn_eq (VandermondeCol (S m) e)). unfold VG_Pexp.
    rewrite Vcons_map2. unfold VF_mult. rewrite Vcons_map2.
    rewrite VF_sum_vcons. rewrite Vfold_left_Vcons_VFadd. rewrite <- EPCMult.
    rewrite comm. rewrite dot_assoc. rewrite Vtail_cons. rewrite comEPCDis.
    rewrite EPCMultExt. pose VF_comm_mult. unfold VF_mult in e0.
    rewrite e0. rewrite <- inv_left. rewrite one_left. rewrite Vbuild_head.
    apply f_equal2. apply Veq_nth. intros. rewrite Vnth_map. cbn. field; auto.
    cbn. field; auto.
    (* Commitments 2/3 *)
    +++ do 4 rewrite Prod_right_replace. rewrite H2. rewrite EPCMultExt.
    unfold VF_mult. pose VF_comm_mult. unfold VF_mult in e0. rewrite e0.
    rewrite <- comEPCDis. rewrite <- comEPCVadd.
    rewrite (VSn_add (rev (VandermondeCol (S m) e))).  rewrite Vadd_map2.
    rewrite <- VSn_add. pose VG_prod_add. unfold VG_prod in e1. rewrite e1.
    rewrite comm. rewrite dot_assoc. rewrite <- inv_left. rewrite one_left.
    rewrite Vlast_nth. rewrite Vbuild_nth. rewrite Vbuild_nth.
    replace (Nat.sub (Nat.sub (S m) m) 1) with 0%nat. cbn. rewrite mod_id. trivial.
    lia.
    (* Commitments 3/3 *)
    +++ do 2 rewrite Prod_right_replace. do 4 rewrite Prod_left_replace.
    rewrite (Vbreak_eq_app (ProdOfDiagonalsF
     (FMatrix.mat_build
        (fun (i j : nat) (ip : i < S m) (jp : j < S m) =>
         BM f (Vnth (Vcons r.1.1.1.1 t1) ip)
           (Vnth (Vadd t0 r.1.1.1.2) jp))))).
    rewrite <- comPCVapp. apply f_equal2.
    ++++
    remember Vbreak as d. do 2 rewrite Prod_right_replace. do 2 rewrite Prod_left_replace.
    rewrite Heqd. rewrite <- Vbreak_eq_app.
    rewrite (VSn_eq (comPC g (Vhead v1)
  (Vbreak
     (ProdOfDiagonalsF
        (FMatrix.mat_build
           (fun (i j : nat) (ip : i < S m) (jp : j < S m) =>
            BM f (Vnth (Vcons r.1.1.1.1 t1) ip)
              (Vnth (Vadd t0 r.1.1.1.2) jp))))).1 r.2.1)).
    apply Vcons_eq_intro.
    +++++
    rewrite Vbreak_Vtail. rewrite Vhead_map2. rewrite Vhead_break.
    rewrite ProdOfDiagonalsFVhead. pose  MatrixAndBillinear_sub.
    symmetry in e0. rewrite VandermondeColGe_eq.
    rewrite (e0 m 0%nat f (Vcons r.1.1.1.1 t1) (Vadd t0 r.1.1.1.2) e).
    rewrite (VSn_eq (Vmap2 Fmul
        (ProdOfDiagonalsF
           (FMatrix.mat_build
              (fun (i j : nat) (ip : i < S m) (jp : j < S m) =>
               BM f (Vnth (Vcons r.1.1.1.1 t1) ip)
                 (Vnth (Vadd t0 r.1.1.1.2) jp))))
        (VandermondeColGen (S m + m) e 0))).
    rewrite (VSn_eq (VF_mult (VandermondeCol (S m + m) e) (Vapp r.2.1 (Vcons 0 r.2.2)))).
    rewrite VF_sum_vcons. pose VF_sum_vcons. unfold VF_sum in e1.
    rewrite e1. rewrite <- PCMult. assert (forall a b c d, a= b -> c = d ->
    a = (c o b) o - d). intros. rewrite H3. rewrite H4. rewrite comm.
    rewrite dot_assoc. rewrite <- inv_left. rewrite one_left. trivial.
    apply H3.
    ++++++
    apply f_equal3. rewrite Vhead_nth. apply Vnth_eq. trivial. rewrite Vhead_map2.
    rewrite (ProdOfDiagonalsFVhead r.1.1.1.1 r.1.1.1.2 t1 t0).
    rewrite Vbuild_head. cbn. field; auto. rewrite Vhead_map2. rewrite Vbuild_head.
    rewrite (Vhead_app r.2.1). cbn. destruct vs_field. destruct F_R.
    rewrite Rmul_1_l. trivial.
    ++++++
    unfold simMapHelp in H. apply Vhead_eq in H. rewrite Vhead_map in H.
    pose (comPCfromOp H).
    do 2 rewrite <- e2. assert (Vnth v1 index0 = Vhead v1).
    rewrite Vhead_nth. apply Vnth_eq. lia. rewrite H4. rewrite comPCVcons.
    rewrite comPCVapp. unfold VG_Pexp. rewrite comPCDis. unfold VG_prod.
    rewrite <- PCMultExt. apply f_equal2. apply f_equal. apply Veq_nth.
    intros. rewrite <- Vtail_map2. rewrite (Vapp_Vtail2 (n:=m)).
    do 2 rewrite Vnth_map2. do 2 rewrite (Vnth_app (n1:=m)). destruct (le_gt_dec m i).
    rewrite Vbreak_app. rewrite Prod_right_replace. rewrite VandermondeColGe_eq.
    apply f_equal2; trivial. symmetry. rewrite Vnth_cons. destruct (lt_ge_dec 0 (i - m)).
    rewrite Vnth_tail. apply Vnth_eq. lia. rewrite H1. do 2 rewrite Vbuild_nth.
    assert (i = m). lia. subst. assert (forall n a (b : VF n), VF_sum b = 0 ->
    Vfold_left Fadd a b = a). intros. replace a2 with (0+a2).
    rewrite <- Vfold_Fadd_const. unfold VF_sum in H0. rewrite H0.
    trivial. field; auto. symmetry. apply H0. rewrite H1.
    assert (S (m - (m - m) - 1) = m). unfold m. lia. apply (Vfold_left_eq_gen H2).
    apply Veq_nth. intros. rewrite Vnth_cast. rewrite Vbuild_nth.
    rewrite (FMatrix.mat_build_nth). rewrite Vnth_map2. apply f_equal2.
    rewrite Vnth_cons. destruct (lt_ge_dec 0 (i + (m - (m - (m - m) - 1)))).
    apply Vnth_eq. lia. assert False. lia. contradiction. rewrite Vnth_add.
    destruct (Nat.eq_dec i m). assert False. lia. contradiction.
    apply Vnth_eq. lia.
    rewrite Vbreak_app. rewrite Prod_left_replace. rewrite VandermondeColGe_eq.
    trivial. apply f_equal. unfold VF_mult. rewrite <- Vtail_map2.
    pose VF_comm_mult. unfold VF_mult in e3. rewrite e3. rewrite Vapp_Vtail.
    trivial.
    +++++
    unfold simMapHelp in H. apply Vhead_eq in H. rewrite Vhead_map in H.
    rewrite <- (comPCfromOp H); auto.
    ++++
    rewrite Vbreak_app. rewrite Prod_right_replace.
    rewrite (VSn_eq (Vbreak
     (ProdOfDiagonalsF
        (FMatrix.mat_build
           (fun (i j : nat) (ip : i < S m) (jp : j < S m) =>
            BM f (Vnth (Vcons r.1.1.1.1 t1) ip)
              (Vnth (Vadd t0 r.1.1.1.2) jp))))).2).
    rewrite <- comPCVcons. rewrite <- VSn_eq. apply Vcons_eq_intro.
    apply f_equal3. rewrite Vhead_nth. apply Vnth_eq. trivial.

    pose TheSMinfold. symmetry in e0. rewrite e0. rewrite Vhead_cons.
    rewrite TheSMdiagindexSM. remember (Vfold_left Fadd 0) as b.
    rewrite H1. rewrite Heqb. apply f_equal. apply Veq_nth. intros.
    rewrite Vbuild_nth. rewrite Vnth_remove_last. rewrite Vnth_tail.
    rewrite FMatrix.mat_build_nth. rewrite Vnth_map2. rewrite Vnth_cons.
    rewrite Vnth_add. destruct (lt_ge_dec 0 (S i)). destruct (Nat.eq_dec i m).
    assert (False). unfold m, support.m in *. lia. contradiction.
    apply f_equal2; apply Vnth_eq; lia. assert (False). unfold m, support.m in *.
    lia. contradiction. trivial. apply Veq_nth. intros. rewrite Vnth_map.
    unfold simMapHelp in H. unfold X in x. apply Vhead_eq in H. rewrite Vhead_map in H.
    pose (comPCfromOp H). rewrite e0.
    rewrite Vnth_map. apply f_equal. trivial.

    (* Challenges *)
    ++ do 2 rewrite Prod_right_replace. trivial.
    (* Response *)
    ++ do 5 rewrite Prod_right_replace. trivial.

    (* And it's bijective! *)
    ++ intros.  split.
    
    
    (* Case 1 *)
    +++ rewrite (surjective_pairing r). rewrite (surjective_pairing r.2).
    rewrite (surjective_pairing r.1). rewrite (surjective_pairing r.1.1).
    rewrite (surjective_pairing r.1.1.1). remember Vbreak as h.
    do 10 rewrite Prod_right_replace. do 14 rewrite Prod_left_replace.
    rewrite Heqh.
    apply injective_projections_simp.
    ++++  apply injective_projections_simp.
    +++++  apply injective_projections_simp.
    ++++++ apply injective_projections_simp.
    +++++++  apply Vfold_left_vcons_cancel. rewrite Vbuild_head. cbn. trivial.
    +++++++ apply Vfold_left_vadd_cancel. rewrite Vbuild_head. cbn. trivial.
    ++++++ apply VF_sum_vcons_cancel. rewrite Vbuild_head. cbn. trivial.
    +++++ apply VF_sum_vadd_cancel. rewrite Vbuild_head. cbn. trivial.
    ++++ apply injective_projections_simp.
    +++++ rewrite (VSn_eq r.2.1). rewrite Vapp_cons. rewrite Vfold_left_vcons_cancel.
    rewrite Prod_right_replace. rewrite Vfold_left_vadd_cancel. unfold VF_sub.
    rewrite VF_add_neg.  rewrite VF_add_neg. rewrite <- VSn_eq.
    rewrite VF_sum_vcons_cancel. rewrite <- VSn_eq. trivial.
    cbn; auto. cbn; auto. cbn; auto.
    +++++
      rewrite Vfold_left_vcons_cancel.
    rewrite Vfold_left_vadd_cancel.
     unfold VF_sub. rewrite VF_add_neg. trivial.
    rewrite Vbuild_head. cbn. trivial. rewrite Vbuild_head. cbn. trivial.

    
    (* Case 2 *)
    +++ rewrite (surjective_pairing t). rewrite (surjective_pairing t.2).
    rewrite (surjective_pairing t.1). rewrite (surjective_pairing t.1.1).
    rewrite (surjective_pairing t.1.1.1). rewrite (surjective_pairing t.1.1.1.1).
    assert (Vhead (VandermondeCol (S m) e) = 1). rewrite Vbuild_head. cbn. trivial.
    ++++  apply injective_projections_simp.
    +++++  apply injective_projections_simp.
    ++++++  apply injective_projections_simp.
    +++++++  apply injective_projections_simp.
    ++++++++  apply injective_projections_simp.
    +++++++++ do 6 rewrite Prod_left_replace. apply Vfold_left_vsub_cancel.
    rewrite Vbuild_head. cbn. trivial.
    +++++++++ do 6 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
     apply VF_sum_vsub_cancel. rewrite Vbuild_head. cbn. trivial.
    ++++++++  do 6 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
    rewrite Vfold_left_vsub_add_cancel. trivial. rewrite Vbuild_head. cbn. trivial.
    +++++++ do 6 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
    rewrite VF_sum_vsub_add_cancel. trivial.  rewrite Vbuild_head. cbn. trivial.
    ++++++ do 6 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
    rewrite Vapp_cons. rewrite VF_sum_vsub_cancel. trivial. rewrite Vbuild_head. cbn.
    trivial.
    +++++ do 6 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
    apply injective_projections_simp.
    ++++++ rewrite Prod_left_replace. do 4 rewrite Prod_right_replace.
    rewrite Vtail_cons. rewrite (SubMatrixRight (BM f)).
    rewrite FMatrix_mat_build_vcons_tail. rewrite Prod_left_replace.
    rewrite Vtail_cons.  unfold VF_sub. rewrite VF_add_neg2. trivial.
    ++++++ rewrite Prod_left_replace. do 5 rewrite Prod_right_replace.
    unfold m. rewrite (SubMatrixRight (BM f)). rewrite Vtail_cons.
    rewrite Vremove_last_add. unfold VF_sub. rewrite VF_add_neg2. trivial.
  Qed.

  Lemma simulator_correct : forall (s : St)(t : TE)(e : Chal.G),
    V1(simulator s t e) = true.
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.
    pose Commitment.module_abegrp. intros.  unfold V1. unfold V0. unfold P1.
    unfold P0. unfold Rel in *.
    unfold simulator. destruct s, p, p, p.
    apply andb_true_iff. split. apply andb_true_iff. split.
    apply andb_true_iff. split. apply bool_eq_corr.
    (* 1 of 4 *)
    ++ do 3 rewrite Prod_right_replace. rewrite Prod_left_replace.
    rewrite (VSn_eq (VandermondeCol (S m) e)). unfold VG_Pexp. rewrite Vcons_map2.
    unfold VG_prod. rewrite Vfold_left_Vcons. rewrite <- VSn_eq.
    rewrite comm. replace (Vhead (VandermondeCol (S m) e)) with 1.
    rewrite mod_id. rewrite <- dot_assoc. rewrite <- inv_left. rewrite one_right.
    trivial. rewrite Vbuild_head. cbn. trivial.
    (* 2 of 4 *)
    ++ apply bool_eq_corr. do 3 rewrite Prod_right_replace.
    rewrite (VSn_add (rev (VandermondeCol (S m) e))). unfold VG_Pexp.
    rewrite Vadd_map2. rewrite VG_prod_add. rewrite <- VSn_add.
    replace (Vlast (Vhead (rev (VandermondeCol (S m) e))) (rev (VandermondeCol (S m) e)))
    with 1. rewrite comm. rewrite mod_id. rewrite <- dot_assoc.
    rewrite <- inv_left. rewrite one_right.
    trivial. rewrite Vlast_nth. do 2 rewrite Vbuild_nth. replace (Nat.sub (Nat.sub (S m) m) 1) with 0%nat.
    cbn. trivial. lia.
    (* 3 of 4 *)
    ++ apply bool_eq_corr. do 3 rewrite Prod_right_replace.
    unfold VG_Pexp. rewrite (Vbreak_eq_app (VandermondeCol (S m + m) e)).
    rewrite Vapp_Vmap2. rewrite Vapp_VG_prod. rewrite <- Vbreak_eq_app.
    rewrite VandermondeColBreak. rewrite (VSn_eq (VandermondeCol (S m) e)).
    rewrite Vcons_map2. unfold VG_prod. rewrite Vfold_left_Vcons.
    replace ( Vhead (VandermondeCol (S m) e)) with 1. rewrite mod_id.
    rewrite comm. rewrite dot_assoc. pose Vapp_VG_prod.  unfold VG_prod in e0.
    assert (forall a b c d, (a o b)o(c o d)=(b o a)o(c o d)). intros. apply right_cancel.
    apply comm. rewrite H. rewrite <- e0. rewrite <- Vapp_Vmap2.
    replace ((Vapp (Vtail (VandermondeCol (S m) e)) (Vbreak (VandermondeCol (S m + m) e)).2)) with
    (Vtail (VandermondeCol (S m + m) e)). rewrite comm.  rewrite <- dot_assoc.
    rewrite <- inv_left. apply one_right. rewrite <- (VandermondeColBreak (S m) m e).
    rewrite Vapp_Vtail. rewrite <- Vbreak_eq_app. trivial. rewrite Vbuild_head. cbn. trivial.
    (* 4 of 4 *)
    ++ apply bool_eq_corr. rewrite Prod_right_replace.
    rewrite Vnth_app. destruct (le_gt_dec (S m) (S support.m)). rewrite Vnth_cons.
    destruct (lt_ge_dec 0 (S support.m - S m)). assert False. unfold support.m in *.
    unfold m in *. lia. contradiction. trivial. assert False. unfold support.m in *.
    unfold m in *. lia. contradiction.
  Qed.

End BGZeroArgIns.
