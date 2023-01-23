Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
From Groups Require Import groups module vectorspace 
    dualvectorspaces matrices matricesF matricesField modulevectorspace 
    groupfromring.
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
(*  Proof of the multi-exponent arg from BG     *)
(*                                              *)
(*  Most of this is pretty straight forward     *)
(*  expect for the soundness                    *)
(*                                              *)
(*  I have annonated the soundness proofs       *)
(*  with line numbers from my paper proof       *)
(*                                              *)

(* A proof of BGMultiArg in Coq *)

Module Type BGMultiArg (Message Ciphertext Commitment : GroupSig)(Ring : RingSig)
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
  Let n := S ( S (S Hack.N)).    (* n *)
  Let m := S (S M.N).            (* m *)
  Import Field.

  Import Mo.
  Import Mo.mat.

  Import EPC.
  Import EPC.MoM.

  Import PC.

  Import ALenc.
  (* Module HardProb := HardProblems Commitment Field VS2. *)
  Import HardProb.

  (* Module ALR := RingAddationalLemmas Ring.*)

  Import VS2.
  Import Commitment.

  (* End casting *)

  Definition St : Type := 
  (* pk ck=(h,hs) (Cbar_1=(H_1,...,H_n),...,Cbar_m) *)
  enc.PK*G*(VG n)*(vector (vector Ciphertext.G n) m)*
        Ciphertext.G*(VG m)*enc.M. (* C cA G *)
  (* A = {aBar_1=(a_1,..,a_n),..,aBar_m} r p *)
  Definition W : Type := (vector (VF n) m)*(VF m)*Ring.F.
  (* a0 r0 b s tau *)
  Definition R : Type := (VF n)*F*((VF m)*(VF (S M.N)))
      *((VF m)*(VF (S M.N)))*((vector Ring.F m)*(vector Ring.F (S M.N))).
  (* cA0 cB0 cB1 E0 E1 *)
  Definition C : Type := (G*(VG (m+m))*
    (vector Ciphertext.G (m+m))).
  (* a r b s tau *) (* R = T when m = 1 *)
  Definition T : Type := ((VF n)*F*F*F*Ring.F).
  Definition X : Type := (VF n*vector (VF n) m*vector (vector Ring.F n) m).
  Definition TE : Type := (((VF n)*F*F*F*Ring.F)*((VF (S M.N)*VF (S M.N))*
    (VF (S M.N)*VF (S M.N))*((vector Ring.F (S M.N))*(vector Ring.F (S M.N))))).

  Definition simMapHelp (s : St)(x : X) :=
    let '(pk, h, hs, Cbar, C, cA, G) := s in 

    hs = Vmap (op h) x.1.1 /\
    Cbar = Vmap2 (fun y z => Vmap2 (fun w v => enc.enc pk (VS3.op G w) v) y z) x.1.2 x.2 .

  Definition Rel (s : St)(w : W) : bool := 
    let '(pk, h, hs, Cbar, C, cA, G) := s in
    (* let '(A, r, p) := w in *)
    let A := w.1.1 in
    let r := w.1.2 in 
    let p := w.2 in

      (* cA_1 = EPC A_1 r_1 *)
      VG_eq cA (comEPC h hs A r) &&
      (* C = (Enc pk 1 p) o (Prod C_i^a_i) *)
      Ciphertext.Gbool_eq C (Ciphertext.Gdot (enc.enc pk enc.Mzero p) (MoC.VG_prod 
        (Vmap2 (fun x y => MoC.VG_prod  (MoC.VG_Pexp x y)) 
          Cbar A))).

  Definition fail_event (s : St)(c : C)(e : VF (2*m)) : Prop :=
    let '(pk, h, hs, Cbar, C, cA, G) := s in

      (exists c m0 r, relComPC h (Vhead hs) c 0 m0 0 r) \/
      (exists c m0 m1 r r', relComEPC h hs c m0 m1 r r').

  Definition P0 (st : St)(r : R)(w : W) : St*C :=
    let '(pk, h, hs, Cbar, C, cA, G) := st in
    let '(a0, r0, b, s, tau) := r in

    let b   := Vapp b.1 (Vcons 0 b.2)  in
    let s0  := Vapp s.1 (Vcons 0 s.2) in

    let A := Vcons a0 (w.1.1) in
    let p := w.2 in

    let tau := Vapp tau.1 (Vcons p tau.2)  in

    let cA0 := EPC h hs a0 r0 in
    let cB0 := comPC h (Vhead hs) b s0 in

    let E0 := EkGenerators pk G Cbar A tau b (VF_one (m+m)) in
    
    
    (st,(cA0, cB0, E0)).

  Definition P1 (ggtoxgtorc: St*C*F) 
      (r : R) (w: W) : St*C*F*T :=
    let c := ggtoxgtorc.2 in

    let A := w.1.1 in
    let p := w.2 in

    let a0  := r.1.1.1.1 in
    let r0  := r.1.1.1.2 in
    let b   := Vapp r.1.1.2.1 (Vcons 0 r.1.1.2.2)  in
    let s0  := Vapp r.1.2.1 (Vcons 0 r.1.2.2) in
    let tau := Vapp r.2.1 (Vcons w.2 r.2.2) in

    let r := w.1.2 in

    let xBar := (VandermondeCol (1+m) c) in
    let xK := VandermondeCol (m+m) c in

    (* aBar = a0 + A xBar , since we tranpose both A and xBar *)
    let aT := Vhead (FMatrix.mat_mult [xBar] (Vcons a0 A)) in
    let rT := VF_inProd (Vcons r0 r) xBar in
    let bT := (VF_inProd b xK) in 
    let sT := (VF_inProd s0 xK) in
    let tauT := MoR.VF_sum (Vmap2 MVS.op3 tau xK) in

    (ggtoxgtorc, (aT, rT, bT, sT, tauT)).

  Definition V1 (transcript : St*C*F*T) :bool :=
    let '(stat, comm, chal, resp) := transcript in 
    let '(pk, h, hs, Cbar, C, cA, G) := stat in
    let '(cA0, cB, E) := comm in

    let x := rev (VandermondeCol m chal)in
    let xBar := VandermondeCol (1+m) chal in
    let xK := VandermondeCol (m+m) chal  in

    let aT := resp.1.1.1.1 in
    let rT := resp.1.1.1.2 in
    let bT := resp.1.1.2 in
    let sT := resp.1.2 in
    let tauT := resp.2 in 

    let eq1 := Gbool_eq (VG_prod (VG_Pexp (Vcons cA0 cA) xBar))
       (EPC h hs aT rT) in

    let eq2 := Gbool_eq (VG_prod (VG_Pexp cB xK))
      (PC h (Vhead hs) bT sT) in

    (* Prod E^xK = (Enc G^b tau) o Prod Prod C_i *)
    let eq3 := Ciphertext.Gbool_eq 
        (MoC.VG_prod (MoC.VG_Pexp E xK)) 
          (Ciphertext.Gdot (enc.enc pk (VS3.op G bT) tauT) 
            (MoC.VG_prod (Vmap2 (fun Ci xi => MoC.VG_prod 
              (MoC.VG_Pexp Ci (VF_scale aT xi))) Cbar x))) in
    
    let eq4 := Gbool_eq (Vnth cB indexM) 
      (PC h (Vhead hs) 0 0) in

    let eq5 := Ciphertext.Gbool_eq (Vnth E indexM) C in

    eq1 && eq2 && eq3 && eq4 && eq5.

  Definition simMap (s : St)(w : W)(c :F)(x : X)(r : R)
     : TE :=
    
    (* Unpack statment *)
    let '(pk, h, hs, Cbar, C, cA, G) := s in

    (* Unpack witness *)
    let A := w.1.1 in
    let p := w.2 in

    (* Unpack random coins *)
     let '(a0, r0, (b0, b1), (s0, s1), (tau0, tau1)) := r in

    let b   := (Vapp b0 (Vcons 0 b1)) in
    let s  :=  (Vapp s0 (Vcons 0 s1))  in
    let tau := (Vapp tau0 (Vcons p tau1)) in

    let xBar := (VandermondeCol (1+m) c) in
    let xK := VandermondeCol (m+m) c in

    (* aBar = a0 + A xBar , since we tranpose both A and xBar *)
    let aT := Vhead (FMatrix.mat_mult [xBar] (Vcons a0 A)) in
    let rT := VF_inProd (Vcons r0 w.1.2) xBar in
    let bT := (VF_inProd b xK) in 
    let sT := (VF_inProd s xK) in
    let tauT := MoR.VF_sum (Vmap2 MVS.op3 tau xK) in

    let bs := EkGeneratorsRawM x.1.2 (Vcons a0 A) b in
    let taus := EkGeneratorsRawR x.2 (Vcons a0 A) tau in 
    let ss := VF_add s (VF_scale b (Vhead x.1.1)) in

    ((aT, rT, bT, sT, tauT),
      ((Vtail (Vbreak bs).1, Vtail (Vbreak bs).2), (Vtail (Vbreak ss).1, Vtail (Vbreak ss).2),
         (Vtail (Vbreak taus).1, Vtail (Vbreak taus).2))). 

  Definition simMapInv (s : St)(w : W)(c :F)(x : X)(t : TE)
     : R :=
    
    (* Unpack statment *)
    let '(pk, h, hs, Cbar, C, cA, G) := s in

    (* Unpack witness *)
    let A := w.1.1 in

    (* Unpack response coins *)
    let '((aT, rT, bT, sT,tauT),((cB0, cB1), (s0, s1), (E1, E2))) := t in

    let xBar := (VandermondeCol (1+m) c) in
    let xK := (VandermondeCol (m+m) c) in

    let a0 := VF_sub aT (Vhead (FMatrix.mat_mult [(Vtail xBar)] A)) in

    let p := Vhead (Vbreak (EkGeneratorsRawR x.2 (Vcons a0 A) 
      (Vapp (MoR.VF_zero m) (Vcons w.2 (MoR.VF_zero (S M.N)))))).2 in
    let b0 := Vhead (Vbreak (EkGeneratorsRawM x.1.2 (Vcons a0 A)
      (Vapp (VF_zero m) (Vcons 0 (VF_zero (S M.N)))))).2 in 
    let s2  := 0 in


    let bb := VF_sub (Vapp cB0 (Vcons b0 cB1)) 
      (Vtail (EkGeneratorsRawM x.1.2 (Vcons a0 A) (VF_zero (m+m))))  in 
    let ss := VF_sub (Vapp s0 (Vcons s2 s1)) (VF_scale bb (Vhead x.1.1)) in
    let taus := MoR.VF_sub (Vapp E1 (Vcons p E2))
      (Vtail (EkGeneratorsRawR x.2 (Vcons a0 A) (MoR.VF_zero (m+m)))) in

    let r0 := rT - (VF_inProd w.1.2 (Vtail xBar))  in
    let b := bT - (VF_inProd bb (Vtail xK))in
    let s := sT - (VF_inProd ss (Vtail xK)) in
    let tau := Ring.Fsub tauT (MoR.VF_sum ((Vmap2 MVS.op3 taus) (Vtail xK))) in

    (* a0 r0 b s tau *)
    (* (VF n)*F*((VF m)*(VF (m-1)))
      *((VF m)*(VF (m-1)))*((vector Ring.F m)*(vector Ring.F (m-1))).*)
    (a0,r0,(Vcons b (Vbreak bb).1,Vtail(Vbreak bb).2),
      (Vcons s (Vbreak ss).1, Vtail (Vbreak ss).2),
      (Vcons tau (Vbreak taus).1, Vtail (Vbreak taus).2)).
 
  Definition simulator (s : St)(z : TE)(e : F) : (St*C*F*T) :=
    
    let '(pk, h, hs, Cbar, C, cA, G) := s in

    let '((aT, rT, bT, sT,tauT),((cB0, cB1), (s0, s1), (E1, E2))) := z in

    let cB := Vmap (op h) (Vapp s0 (Vcons 0 s1)) in

    let E := Vapp (Vmap2 (fun w v => enc.enc pk (VS3.op G w) v) cB0 E1) 
      (Vcons C (Vmap2 (fun w v => enc.enc pk (VS3.op G w) v) cB1 E2)) in

    let x := rev (VandermondeCol m e)in
    let xBar := VandermondeCol (1+m) e in
    let xK := VandermondeCol (m+m) e  in

    let CA0 := EPC h hs aT rT o - VG_prod (VG_Pexp cA (Vtail xBar)) in 
    let CB := PC h (Vhead hs) bT sT o - VG_prod (VG_Pexp cB (Vtail xK))  in
    let EK := Ciphertext.Gdot (Ciphertext.Gdot 
                (enc.enc pk (VS3.op G bT) tauT) 
                (MoC.VG_prod (Vmap2 (fun Ci xi => MoC.VG_prod 
                (MoC.VG_Pexp Ci (VF_scale aT xi))) Cbar x)))
              (Ciphertext.Ginv (MoC.VG_prod (MoC.VG_Pexp E (Vtail xK)))) in 



    (s,(CA0,Vcons CB cB,Vcons EK E),e,z.1). 

  Definition M := Nat.mul 2 m.

  Definition extractor (s : vector T (2*m))
        (c : vector F (2*m)): W :=

    let sM1 := (Vbreak (Vcast s castingM4)).1 in

    let aT := FMatrix.mat_transpose (Vmap (fun s1 => s1.1.1.1.1) sM1) in
    let rT := (Vmap (fun s1 => s1.1.1.1.2) sM1) in
    let bT := Vmap (fun s1 => s1.1.1.2) s in 
    let sT := Vmap (fun s1 => s1.1.2) s in
    let tauT := Vcast (Vmap (fun s1 => s1.2) s) castingM6 in
    let YM1 := FMatrix.mat_transpose (VandermondeInv (Vbreak (Vcast c castingM4)).1) in

    let Y2M := 
        VandermondeInv (Vcast c castingM6)  in

    (Vtail (FMatrix.mat_transpose (FMatrix.mat_mult aT YM1)), 
      Vtail (Vhead (FMatrix.mat_mult [rT] YM1)),
       RF_inProd (Vnth Y2M indexM) tauT).
     
  Definition disjoint (c1 c2 : F) :=
    negb (Fbool_eq c1 c2).

  Lemma Ek_ck : forall (w11 : vector (VF n) m)(s111111 : enc.PK)
    (s1112 : vector (vector Ciphertext.G n) m)
    (w2 : Ring.F)(s2 : enc.M)(r1111 : VF n)(r1122 : VF (S M.N))
    (r1121 : VF m)(r22 : vector Ring.F (S M.N))
    (r21 : vector Ring.F m)(c : F),
    MoC.VG_prod
  (MoC.VG_Pexp
     (EkGenerators s111111 s2 s1112
        (Vcons r1111 w11)
        (Vapp r21 (Vcons w2 r22))
        (Vapp r1121 (Vcons 0 r1122))
        (VF_one (m + m))) (VandermondeCol (m + m) c)) =
Ciphertext.Gdot
  (enc.enc s111111
     (VS3.op s2
        (VF_inProd (Vapp r1121 (Vcons 0 r1122))
         (VandermondeCol (m+m) c)))
     (MoR.VF_sum
        (Vmap2 MVS.op3 (Vapp r21 (Vcons w2 r22)) (VandermondeCol (m+m) c))))
  (MoC.VG_prod
     (Vmap2
        (fun (Ci : MoC.VG n) (xi : F) =>
         MoC.VG_prod
           (MoC.VG_Pexp Ci
              (VF_scale
                 (Vhead
                    (FMatrix.mat_mult
                       [VandermondeCol (1 + m) c]
                       (Vcons r1111 w11))) xi)))
        s1112 (rev (VandermondeCol m c)))).
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.  
    pose Commitment.module_abegrp.
    intros. rewrite EkGeneratorsPexp. rewrite EkGeneratorsProd.
    apply eqImplProd. split. 
    apply EncEq. apply ALVS3.scaleEq.
    rewrite InProd_Sum. unfold VF_mult. apply Vfold_left_eq.
    apply f_equal2; auto. trivial.
    apply Vfold_left_eq. apply Veq_nth. intros.
    do 2 rewrite Vnth_map2. rewrite Vbuild_nth.
    rewrite MoC.VG_prod_VG_Pexp. apply Vfold_left_eq.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    apply ALVS1.scaleEq. rewrite Vnth_map. rewrite Vfold_left_VF_add.
    rewrite Vhead_nth. rewrite FMatrix.mat_mult_elem.
    assert (forall (a b : VF (1+m)), 
      FMatrix.VA.dot_product a b = VF_inProd a b). intros.
      unfold FMatrix.VA.dot_product. rewrite InProd_Sum.
      rewrite Vfold_left_Fadd_eq. trivial.
    rewrite H. rewrite InProd_Sum. rewrite VF_sum_scale.
    (* Trying to simply *)
    apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vnth_map.
    do 2 rewrite Vnth_map2. rewrite Vnth_map. rewrite <- FMatrix.get_elem_swap.
    unfold FMatrix.get_row. assert (forall a b c d,
      b = c * d -> a * b = c * a * d). intros. rewrite H0.
    ring; auto. apply H0. rewrite Vnth_sub. rewrite Vnth_map2. 
    do 2 rewrite Vnth_const. do 2 rewrite Vbuild_nth.
    do 2 rewrite Vbuild_nth. 
    rewrite VF_prod_const. destruct vs_field, F_R. rewrite Rmul_1_l.
    apply VG_prod_const_index. unfold support.m, m. lia.
  Qed.

  Lemma Sim_com : forall (s : St)(r : R)(c : F)(w : W)(x : X),
    simMapHelp s x ->
    V1 (P1 ((P0 s r w), c) r w) = true  ->
    (P0 s r w).2 = (simulator s (simMap s w c x r) c).1.1.2.
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.  
    pose Commitment.module_abegrp. intros. unfold P0. unfold simulator. 
    unfold simMap. destruct s, p, p, p, p, p.
    destruct r, p0, p0, p0. destruct w, p0. destruct p2, p3, p1. remember Vbreak as d.
    do 7 rewrite Prod_right_replace. do 5 rewrite Prod_left_replace.  
    unfold V1, P1, P0 in H0. do 14 rewrite Prod_right_replace in H0.
    do 10 rewrite Prod_left_replace in H0.
    apply andb_true_iff in H0. destruct H0. apply andb_true_iff in H0. destruct H0.
    apply andb_true_iff in H0. destruct H0.  apply andb_true_iff in H0. destruct H0.
    destruct vs_field. destruct F_R. apply bool_eq_corr in H0.
    apply bool_eq_corr in H4. apply bool_eq_corr in H2.
     apply injective_projections. apply injective_projections.
    (* CA *)
    + do 2 rewrite Prod_left_replace. rewrite <- H0. rewrite (VSn_eq (VandermondeCol (1 + m) c)).
    unfold VG_Pexp. rewrite Vcons_map2. rewrite VG_prod_Vcons. rewrite <- VSn_eq.
    rewrite comm. rewrite dot_assoc. rewrite <- inv_left. rewrite one_left.
    rewrite Vbuild_head. cbn. rewrite mod_id. trivial.
    (* CB *)
    + do 2 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace. rewrite <- H4.
    (* First thing we need to do is to simplify the vectors *)
    assert (0 = Vhead (d F m (S (S M.N)) (VF_add (Vapp v3 (Vcons 0 v4)) 
    (VF_scale (Vapp v5 (Vcons 0 v6)) (Vhead x.1.1)))).2).
    rewrite Vhead_nth. rewrite Heqd. rewrite Vnth_vbreak_2. lia.  intros. unfold VF_add,
    FMatrix.VA.vector_plus. rewrite Vnth_map2. rewrite Vnth_map. 
    unfold m in *. do 2 rewrite (Vnth_app). destruct (le_gt_dec (S (S M.N)) (0 + S (S M.N))).
    do 2 rewrite Vnth_cons. destruct (lt_ge_dec 0 (0 + S M.N - S M.N)). assert (False). lia. contradiction.
    destruct (lt_ge_dec 0 (0 + S (S M.N) - S (S M.N))). assert (False). lia. contradiction.
    unfold FSemiRingT.Aplus. field. assert (False). lia. contradiction. 
    (* Now we can simply the vectors *)
    remember (d F m (S (S M.N)) (VF_add (Vapp v3 (Vcons 0 v4))
    (VF_scale (Vapp v5 (Vcons 0 v6)) (Vhead x.1.1)))). rewrite H5. rewrite <- VSn_eq.
    rewrite <- Vapp_Vtail2. unfold VG_Pexp. rewrite <- Vtail_map. rewrite Vtail_map2.
    assert ((Vhead v0) = g0 ^ (Vhead x.1.1)). destruct H. rewrite H. rewrite Vhead_map. auto.
    pose(comPCfromOp H6). rewrite <- H5. rewrite Heqp0. 
    rewrite Heqd. rewrite <- Vbreak_eq_app. rewrite <- e. unfold comPC.  
    rewrite VG_prod_cancel. (* Most cleaning is now done *)
    rewrite Vhead_map2. replace (Vhead (VandermondeCol (m + m) c)) with 1.
    rewrite mod_id. rewrite <- VSn_eq. trivial. unfold VandermondeCol.
    rewrite Vbuild_head. unfold VF_prod. rewrite Vfold_left_nil. trivial.
    (* Ek *)
    + do 2 rewrite Prod_right_replace. 
    apply bool_eq_corr in H1. rewrite <- H1. rewrite Vtail_map2. rewrite Vapp_Vtail.
    destruct H. rewrite <- (EkGeneratorsRaw_conv p m0 x.1.2 x.2); auto.
    rewrite indexMhead. rewrite Vtail_map2. rewrite Heqd. rewrite Vbreak_vmap2_2. 
    rewrite <- VSn_eq. rewrite Vbreak_vmap2_1. rewrite <- Vbreak_eq_app.
    apply bool_eq_corr in H3. rewrite <- H3. 
    rewrite <- (EkGeneratorsRaw_conv p m0 x.1.2 x.2); auto.
    unfold MoC.VG_Pexp. rewrite Vtail_map2. rewrite MoC.VG_prod_cancel.
    rewrite Vhead_map2. replace (Vhead (VandermondeCol (m + m) c)) with 1.
    rewrite VS1.mod_id. rewrite <- VSn_eq. trivial. rewrite Vbuild_head. cbn.
    trivial. 
  Qed. 
  
  Lemma pres_p0 : forall (s : St)(r : R)(w : W), (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. unfold P0. destruct s, p, p, p, p, p.
    destruct r, p0, p0, p0. trivial.
  Qed.

  Lemma pres_p1 : forall (sce : St*C*F)(r : R)(w : W), 
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Proof.
    intros. unfold P1. destruct sce, p. destruct s, p, p, p, p, p.
    destruct r, p0, p0, p0. trivial.
  Qed.

  Lemma pres_sim : forall (s: St)(t : TE)(e : F),
      s = (simulator s t e).1.1.1.
  Proof.
    intros. unfold simulator. destruct s, p, p, p, p, p.
    destruct t, p0, p0, p0, p0, p1, p0, p0, p1, p2. trivial.
  Qed.

  Lemma chal_sim : forall (s: St)(t : TE)(e : F),
    e = (simulator s t e).1.2. 
  Proof.
    intros. unfold simulator. destruct s, p, p, p, p, p.
    destruct t, p0, p0, p0, p0, p1, p0, p0, p1, p2.  trivial.
  Qed. 

  (** Properties *)
  Lemma correctness : forall (s :St)(w:W)(r:R)(c: F),
    Rel s w ->
    V1 (P1 ((P0 s r w), c) r w) = true.
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.  
    pose Commitment.module_abegrp.
     intros. unfold V1. unfold P1.
    unfold P0. unfold Rel in H.  destruct s, p, p, p, p, p.
    destruct r, p0, p0, p0. destruct w, p0. apply andb_true_iff in H.
    destruct H. apply VGeq in H. apply bool_eq_corr in H0.
    (* End verbose simpl *)
    apply andb_true_iff. split. apply andb_true_iff. split. 
    apply andb_true_iff. split.  apply andb_true_iff. split. 
    - apply bool_eq_corr. 
    rewrite H. rewrite comEPCVcons.  unfold VG_Pexp.
    rewrite comEPCDis. unfold VG_prod. rewrite <- EPCMultExt.
    apply EPC_m_r_eq. apply Veq_nth. intros. 
    rewrite Vfold_left_VF_add. rewrite Vhead_nth.
    rewrite FMatrix.mat_mult_elem. unfold FMatrix.VA.dot_product.
    rewrite Vfold_left_Fadd_eq. apply Vfold_left_eq.
    apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vnth_map. rewrite Vnth_map2. 
    rewrite Vnth_map. rewrite <- FMatrix.get_elem_swap.
    unfold FMatrix.get_row. rewrite Vnth0.
    pose Field.vs_field. unfold FSemiRingT.Amult.
    destruct f1. destruct F_R. apply Rmul_comm.
    unfold VF_inProd, FMatrix.VA.dot_product.
    rewrite Vfold_left_Fadd_eq. trivial.
    (* Completeness 2/5 *)
    - intros. apply bool_eq_corr.
    unfold VG_Pexp. rewrite comPCDis.
    unfold VG_prod. rewrite <- PCMultExt.
    apply PC_m_r_eq. unfold VF_inProd, FMatrix.VA.dot_product.
    do 5 rewrite Prod_right_replace. rewrite Vfold_left_Fadd_eq. trivial.
     do 5 rewrite Prod_right_replace.  rewrite InProd_Sum. unfold VF_sum. trivial.
    (* Completeness 3/5 *)
    - intros. apply bool_eq_corr. apply Ek_ck.
    
    (* Completeness 4/5 *)
    - apply bool_eq_corr. cbn. rewrite Vnth_map2.
      do 4 rewrite Vnth_tail. apply PC_m_r_eq.
    pose (Vnth_app_cons p3.1 p3.2).
    rewrite e. trivial. 
    pose (Vnth_app_cons p2.1 p2.2).
    rewrite e. trivial.
    (* Completeness 5/5 *)
    - apply bool_eq_corr. do 2 rewrite Vnth_map2.
    rewrite Prod_left_replace.
    rewrite H0. apply eqImplProd. split. 
    do 2 rewrite Vnth_app_cons.
    rewrite VS3.mod_ann. trivial. rewrite Vnth_map2.
    rewrite Vnth_app_left. rewrite Vnth_const. rewrite VS1.mod_id.
    do 2 rewrite Vbuild_nth. assert (m = Nat.add 1 (Nat.sub 
    (Nat.sub m (m - m)) 1)). unfold m. lia.
    rewrite (MoC.VG_prod_cast H1). rewrite MoC.VG_prod_rev.  
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vbuild_nth.
    rewrite Vnth_cast. do 2 rewrite Vnth_map2. apply Vfold_left_eq. 
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. 
    apply ALVS1.scaleEqFull. apply Veq_nth2. rewrite Vnth_sub. 
    rewrite Vbuild_nth. apply Vnth_eq. rewrite <- H1. unfold support.m, m.  lia.
    rewrite Vapp_tail. apply Veq_nth2. rewrite Vnth_sub. rewrite Vbuild_nth.
    apply Vnth_eq. rewrite <- H1. lia. 
  Qed.

   Definition allDifferent (e : vector F M) := PairwisePredicate disjoint e.
  
  Lemma special_soundness : forall (s : St)(c : C)(e : vector F M)(t : vector T M),
    (* Forall e it is disjoint from all e *)
    allDifferent e  ->
    bVforall2 (fun e1 t1 => V1 (s, c, e1, t1)) e t -> 
    Rel s (extractor t e) = true \/ fail_event s c e.
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.  
    pose Commitment.module_abegrp. intros. unfold Rel, extractor, fail_event. 
    unfold V1 in H0. destruct s, p, p, p, p, p. destruct c, p0.
    apply bVforall2Split in H0. destruct H0.
    apply bVforall2Split in H0. destruct H0. simpl in H1. simpl in H2.
    apply bVforall2Split in H0. destruct H0. apply bVforall2Split in H0.
    destruct H0. apply bVforall2Clear in H2. apply bool_eq_corr in H2.
    (* We need to prove Cb zero - Corollary 2 *)
    pose (Vmap (fun s1 => s1.1.2) t) as sT.
    pose (Vmap (fun s1 => s1.1.1.2) t) as bT.
    pose (FMatrix.mat_transpose (VandermondeInv e)) as Y2M.
    pose (castingM6). symmetry in e0. 
    assert (Vcast v1 e0 = comPC g0 (Vhead v0)
     (Vhead (FMatrix.mat_mult [bT] Y2M)) (Vhead (FMatrix.mat_mult [sT] Y2M))). 
    symmetry. rewrite <- VG_MF_exp_row_id. symmetry.
    pose (invVandermondeLeft H).  unfold M, m, support.m in *. 
    rewrite <- e1. rewrite <- VG_MF_exp_row_dist. apply Veq_nth. intros.
    assert (VG_MF_exp_row (Vcast v1 e0) (Vandermonde e) =
    Vmap (fun x => PC g0 (Vhead v0)
    x.1.1.2 x.1.2) t). apply Veq_nth. intros.
    apply (bVforall2_elim_nth ip0) in H4. apply bool_eq_corr in H4.
    assert (VG_prod (VG_Pexp v1
    (VandermondeCol (m+m) (Vnth e ip0))
    ) = Vnth (VG_MF_exp_row (Vcast v1 e0) (Vandermonde e))
    ip0). rewrite Vbuild_nth. apply (Vfold_left_eq_gen e0). apply Veq_nth.
    intros. rewrite Vnth_cast. do 2 rewrite Vnth_map2. apply f_equal2.
    simpl. rewrite Vnth_cast. simpl. trivial. rewrite Vnth_map.
    do 2 rewrite Vbuild_nth. simpl. trivial.
     rewrite <- H5. rewrite H4. simpl. rewrite Vnth_map. trivial.
    rewrite H5. rewrite Vnth_map2. rewrite Vbuild_nth. assert (Vmap
    (fun x => PC g0 (Vhead v0) x.1.1.2 x.1.2) t =
    comPC g0 (Vhead v0) (Vmap (fun x => x.1.1.2) t)
    (Vmap (fun x => x.1.2) t)). apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_map.
    trivial. rewrite H6. unfold VG_Pexp. rewrite comPCDis. unfold VG_prod.
    rewrite <- PCMultExt. apply PC_m_r_eq. rewrite Vhead_nth. rewrite FMatrix.mat_mult_elem.
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq. apply f_equal.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map.
    apply f_equal2; auto. unfold Y2M. pose FMatrix.mat_transpose_col_row.
    unfold FMatrix.get_row in e2. rewrite e2. rewrite Vnth_map. trivial.
    rewrite Vhead_nth. rewrite FMatrix.mat_mult_elem.
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq. apply f_equal.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map.
    apply f_equal2; auto. unfold Y2M. pose FMatrix.mat_transpose_col_row.
    unfold FMatrix.get_row in e2. rewrite e2. rewrite Vnth_map. trivial.
    assert (m < S (S (M.N + S (S (M.N + 0))))). unfold m. lia.
    assert (Vnth v1 indexM = PC g0 (Vhead v0)
      (VF_inProd bT (FMatrix.get_col Y2M H6))
      (VF_inProd sT (FMatrix.get_col Y2M H6))) as Col2. apply (Vcast_lr v1 e0 castingM5) in H5.
    rewrite H5. rewrite Vnth_cast. rewrite Vnth_map2. do 3 rewrite Vhead_nth. 
    do 2 rewrite FMatrix.mat_mult_elem. simpl. assert (forall n (a b : VF n),
    FMatrix.VA.dot_product a b = VF_inProd a b). intros. unfold FMatrix.VA.dot_product.
    unfold VF_inProd, FMatrix.VA.dot_product. apply f_equal.
    trivial. do 2 rewrite H7. apply f_equal2. apply f_equal.
    apply Veq_nth. intros. do 2 rewrite Vnth_map. apply Vnth_eq. trivial.
    apply f_equal. apply Veq_nth. intros. do 2 rewrite Vnth_map. apply Vnth_eq. trivial.
    (* Prepping to prove lemma 1 *)
    assert (S (S (M.N + S (S (M.N + 0)))) = Nat.add (S (S (S M.N))) (S M.N)). lia. 
     pose (Vbreak (Vcast e H7)) as chal. 
    pose (Vbreak (Vcast t H7)) as resp. 
    remember (FMatrix.mat_mult (VandermondeInv chal.1)
      (Vmap (fun x => x.1.1.1.1) resp.1)) as Aj.
     assert (MF_mult (Vandermonde e) (VandermondeInv e) = 
      MF_id (S (S (M.N + (S (S (M.N + 0))))))).
     apply invVandermondeRight; auto. assert (MF_mult (Vandermonde chal.1) 
    (VandermondeInv chal.1) = MF_id (S (S (S M.N)))).
     apply (PairwisePredicate_break (S (S (S M.N))) (S M.N) e disjoint H7) in H.
    apply invVandermondeRight; auto. assert (PairwisePredicate disjoint chal.1). 
    apply (PairwisePredicate_break); auto. 
    remember (Vhead (FMatrix.mat_mult [(Vmap (fun s1 => s1.1.1.1.2) resp.1)] 
    (FMatrix.mat_transpose (VandermondeInv chal.1)))) as Rj.
    (* We want to prove Aj = Etractor *)
    assert ((extractor t e).1.1 = Vtail Aj).
    apply Veq_nth. intros. apply Veq_nth. intros. 
    do 2 rewrite Vnth_tail. rewrite transpose_move_gen.
    do 2 rewrite FMatrix.mat_transpose_idem.
    rewrite HeqAj. do 2 rewrite FMatrix.mat_mult_elem. 
    apply f_equal2. unfold FMatrix.get_row. unfold chal.
    apply Veq_nth3. trivial. apply f_equal. apply Veq_nth. intros. 
    rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_vbreak_1. intros. do 2 rewrite Vnth_cast.
    apply Vnth_eq. lia.  apply Veq_nth. intros.
    do 4 rewrite Vnth_map. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_vbreak_1. intros. do 2 rewrite Vnth_cast.
    apply Veq_nth3; auto. apply f_equal. apply f_equal.
    apply f_equal. apply f_equal. apply Vnth_eq. lia. 
    (* Same with Rj *)
    assert ((extractor t e).1.2 = Vtail Rj). apply Veq_nth.
    intros. do 2 rewrite Vnth_tail. rewrite HeqRj. do 2 rewrite Vhead_nth.
    do 2 rewrite FMatrix.mat_mult_elem. apply f_equal2; auto. unfold FMatrix.get_row.
    apply Veq_nth3; auto. apply Vcons_eq_intro; auto.
    apply Veq_nth. intros. do 2 rewrite Vnth_map. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_vbreak_1. intros. do 2 rewrite Vnth_cast.
    apply f_equal. apply f_equal. apply f_equal. apply f_equal.
    apply Vnth_eq. lia. apply Veq_nth. intros.
    do 2 rewrite Vnth_map. do 2 rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_elem, FMatrix.get_row. apply Veq_nth4. apply Veq_nth4.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_vbreak_1. intros. do 2 rewrite Vnth_cast.
    apply Veq_nth3; auto. 
    (* Prove commitment - Lemma 1 *)
    assert (VG_eq (Vcons g1 v) (comEPC g0 v0 Aj Rj) = true) as Lemma1.
    apply (bVforall2_break (S (S (S M.N))) (S M.N) e t (fun (a' : F) (b' : T) =>
        Gbool_eq
          (VG_prod
             (VG_Pexp
                (Vcons g1 v)
                (VandermondeCol (1+m) a')))
          (EPC g0 v0 b'.1.1.1.1 b'.1.1.1.2)) H7) in H0. destruct H0.
    apply VGeq.
    symmetry. rewrite <- VG_MF_exp_row_id. symmetry. unfold m. rewrite <- H9.
    assert (MF_mult (Vandermonde chal.1) (VandermondeInv chal.1) = 
              MF_mult (VandermondeInv chal.1) (Vandermonde chal.1)).
    rewrite invVandermondeLeft. rewrite invVandermondeRight. trivial.
    trivial. trivial.
    rewrite H14. rewrite <- VG_MF_exp_row_dist.
    assert (VG_MF_exp_row (Vcons g1 v) (Vandermonde chal.1)
      = comEPC g0 v0 (Vmap (fun x => 
        x.1.1.1.1) resp.1) (Vmap (fun x =>  x.1.1.1.2) resp.1)).
    apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vbuild_nth.
    apply (bVforall2_elim_nth ip chal.1 resp.1) in H0.
    apply bool_eq_corr in H0. rewrite Vnth_map. unfold m in H0. 
    rewrite H0. do 2 rewrite Vnth_map. trivial. rewrite H15.
    unfold VG_MF_exp_row. apply Veq_nth. intros. rewrite Vbuild_nth.
    unfold VG_Pexp. rewrite comEPCDis. unfold VG_prod.
    rewrite <- EPCMultExt. rewrite Vnth_map2. rewrite HeqAj.
    rewrite HeqRj. destruct module_ring. apply f_equal2. apply Veq_nth.
    intros. rewrite FMatrix.mat_mult_elem. rewrite Vfold_left_VF_add.
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq.
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_map.
    do 2 rewrite Vnth_map2. do 4 rewrite Vnth_map. rewrite Rmul_comm.
    apply f_equal2. unfold FMatrix.get_row. trivial. trivial.
    rewrite Vhead_nth. rewrite FMatrix.mat_mult_elem. unfold FMatrix.VA.dot_product.
    rewrite Vfold_left_Fadd_eq. apply Vfold_left_eq. apply Veq_nth. intros. 
    do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map.
    apply f_equal2. trivial. rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_elem. unfold FMatrix.get_row. trivial.


    (* Case both of the cases where the commitment breaks to be dealt with later *)
    case_eq (Fbool_eq (VF_inProd bT (FMatrix.get_col Y2M H6)) 0).
    case_eq (bVforall2 (VF_beq (n:= n))
       (Vmap (fun x => x.1.1.1.1) t) 
      (Vbuild (fun i (ip : i < S (S (M.N + S (S (M.N + 0))))) =>
        Vhead (FMatrix.mat_mult [(VandermondeCol (S (S (S M.N)))
        (Vnth e ip))] Aj)))). 
    
    + intros.  left. apply andb_true_iff. split. 
    (* We are about to split the two parts of the relationship
    but before we need to prep some stuff for the ciphertexts *)
    ++ apply VGeq in Lemma1. apply VGeq. apply Vcons_eq_elim_gen in Lemma1.
    destruct Lemma1. rewrite H16. unfold extractor in *.
    rewrite Prod_right_replace in H12. rewrite Prod_left_replace in H11.
    rewrite H12. rewrite H11. trivial.
    (* Prove ciphertexts - begin lemma 2 *)
    ++ clear H0.
    apply bool_eq_corr. apply bVforall2Clear in H1. apply bool_eq_corr in H1.
    rewrite <- H1.
    (* Prove ciphertexts - begin properites over all Es (Lemma 2) *)
    assert (Nat.add m m = M). unfold M, m. lia.
    assert (Vcast t1 H0 = Vmap 
        (fun q => MoC.VG_prod (MoC.VG_Pexp (Vmap2 (fun x y =>
           Ciphertext.Gdot (enc.enc p (VS3.op m0 y.1.1.2) y.2)
            (MoC.VG_prod (Vmap2 (fun (Ci : MoC.VG n) (xi : F) =>
            MoC.VG_prod (MoC.VG_Pexp Ci (VF_scale y.1.1.1.1 xi)))
            t0 (rev (VandermondeCol (m) x))))) e t) q)) 
    (VandermondeInv e)) as Lemma2. clear H2 H5 Col2 HeqRj H13.
    +++ symmetry. rewrite <- (MoC.VG_MF_exp_row_id). symmetry. 
    pose (invVandermondeRight H). rewrite <- e1. assert (MF_mult (Vandermonde e) (VandermondeInv e) = 
                                                           MF_mult (VandermondeInv e) (Vandermonde e)). rewrite invVandermondeLeft.
    rewrite invVandermondeRight. trivial. trivial. trivial.
    rewrite H2. rewrite <- MoC.VG_MF_exp_row_dist. apply Veq_nth.
    intros. rewrite Vbuild_nth. rewrite Vnth_map.
    (* Prove ciphertext - begin inner most *)
    assert (MoC.VG_MF_exp_row (Vcast t1 H0) (Vandermonde e) =
    Vmap2 (fun x y => Ciphertext.Gdot (enc.enc p
     (VS3.op m0 y.1.1.2) y.2) (MoC.VG_prod (Vmap2
     (fun (Ci : MoC.VG n) (xi : F) => MoC.VG_prod (MoC.VG_Pexp Ci
     (VF_scale y.1.1.1.1 xi))) t0 (rev (VandermondeCol m x))))) e t). 
    apply Veq_nth. intros. rewrite Vbuild_nth. apply (bVforall2_elim_nth ip0) in H3.
    apply bool_eq_corr in H3. assert (MoC.VG_prod (MoC.VG_Pexp t1
    (VandermondeCol (m+m) (Vnth e ip0))) = MoC.VG_prod
  (MoC.VG_Pexp (Vcast t1 H0) (Vnth (Vandermonde e) ip0))). 
    apply (Vfold_left_eq_gen H0). apply Veq_nth. intros.
    rewrite Vnth_cast. do 2 rewrite Vnth_map2. apply f_equal2.
    simpl. rewrite Vnth_cast. trivial.
    rewrite Vnth_map. do 2 rewrite Vbuild_nth. simpl. trivial.
    rewrite H5 in H3. rewrite H3. rewrite Vnth_map2. apply eqImplProd.
    split. simpl. trivial. apply Vfold_left_eq. apply f_equal2; auto. 
    (* End inner most *)
    rewrite H5. trivial. 
    (* Lemma 2 is now proved *)
    +++ assert (M = Nat.add m m). lia. apply (Vcast_lr t1 H0 H15) in Lemma2. 
    rewrite Lemma2. rewrite Vnth_cast.
    rewrite Vnth_map. rewrite MoC.VG_mult_Vmap2. rewrite MoC.VG_Pexp_mult.
    rewrite MoC.VG_Prod_mult_dist. apply eqImplProd. split.
    (* We are finishing up the consquence of Lemma 2 *)
    (* Proving enc *)
    ++++ assert (Vmap2 (fun (_ : F) (y : VF n * F * F * F * Ring.F) =>
    enc.enc p (VS3.op m0 y.1.1.2) y.2) e t = 
    Vmap2 (fun x y => enc.enc p (VS3.op m0 x) y)
    (Vmap (fun x => x.1.1.2) t) (Vmap (fun x => x.2) t)). apply Veq_nth.
    intros. do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map. trivial.
    rewrite H16. rewrite pexpOfCiphertext. rewrite prodOfCiphertext.
    apply EncEq. apply F_bool_eq_corr in H14. assert (VF_sum
     (VF_mult (Vmap (fun x : VF n * F * F * F * Ring.F => x.1.1.2)
     t) (Vnth (VandermondeInv e) (Vnth_cast_aux H15 indexM))) = 
    VF_inProd bT (FMatrix.get_col Y2M H6)). rewrite InProd_Sum. 
    apply f_equal. unfold VF_mult. apply f_equal2. auto.
    unfold Y2M. rewrite FMatrix.mat_transpose_row_col.
    unfold FMatrix.get_row. apply f_equal. apply le_unique.
    rewrite H17. rewrite H14.
    rewrite VS3.mod_ann. trivial. rewrite Prod_right_replace.  unfold RF_inProd, MoR.VF_sum.
    apply (Vfold_left_eq_gen castingM6).  apply Veq_nth. intros. rewrite Vnth_cast.
    do 2 rewrite Vnth_map2. apply f_equal2. rewrite Vnth_cast. trivial. apply (Veq_nth_mat castingM6); trivial.
    (* We have discharged the encryption part of lemma 2 *)
    ++++ assert (Vmap2 (fun (x : F) (y : VF n * F * F * F * Ring.F) =>
    MoC.VG_prod (Vmap2 (fun (Ci : MoC.VG n) (xi : F) => MoC.VG_prod
    (MoC.VG_Pexp Ci (VF_scale y.1.1.1.1 xi))) t0 (rev
    (VandermondeCol m x)))) e t = 
    Vmap2 (fun (x : F) (y : VF n) =>
    MoC.VG_prod (Vmap2 (fun (Ci : MoC.VG n) (xi : F) => MoC.VG_prod
    (MoC.VG_Pexp Ci (VF_scale y xi))) t0 (rev (Vcast
    (VandermondeCol (1 + (m - 1)) x)  castingM0)))) e (Vmap 
    (fun x => x.1.1.1.1) t)). apply Veq_nth. intros. 
    do 2 rewrite Vnth_map2. rewrite Vnth_map. apply f_equal.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. apply f_equal.
    apply f_equal2; auto.  apply f_equal. do 3 rewrite Vbuild_nth.
    rewrite Vnth_cast. rewrite Vbuild_nth. unfold m, support.m. trivial.
    rewrite H16.
    (* We will now prove Corollary 1 *)
    assert (Vmap2 (fun (x : F) (y : VF n) => MoC.VG_prod
     (Vmap2 (fun (Ci : MoC.VG n) (xi : F) =>
         MoC.VG_prod (MoC.VG_Pexp Ci (VF_scale y xi))) t0
        (rev (Vcast (VandermondeCol (1 + (m - 1)) x)
        castingM0)))) e (Vmap (fun x : VF n * F * F * F * Ring.F =>
        x.1.1.1.1) t) =
     Vcast (Vmap (fun (x : VF (m+m))  => MoC.VG_prod
     (MoC.VG_Pexp (WeirdCs t0 Aj) x))
     (Vandermonde (Vcast e castingM5))) castingM7) as Col1. 
    +++++ 
    assert ((Vmap (fun x : VF n * F * F * F * Ring.F => x.1.1.1.1) t) =
    (Vbuild (fun (i : nat) (ip : i < S (S (M.N + S (S (M.N + 0))))) =>
    Vhead (FMatrix.mat_mult [VandermondeCol (S (S (S M.N))) (Vnth e ip)] Aj)))).
    apply Veq_nth. intros. apply (bVforall2_elim_nth ip) in H13.
    apply VF_beq_true in H13. rewrite H13. trivial.
    rewrite H17. apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vbuild_nth. rewrite Vnth_cast. rewrite Vnth_map.
    rewrite Vnth_map. rewrite Vnth_cast. assert (Vnth e
    (Vnth_cast_aux castingM5 (Vnth_cast_aux castingM7 ip)) =
    Vnth e ip). apply Vnth_eq. trivial. rewrite H18.
    assert (Vcast (VandermondeCol (1 + (m - 1)) (Vnth e ip)) castingM0 =
    VandermondeCol m (Vnth e ip)). apply Veq_nth. intros.
    rewrite Vnth_cast. do 2 rewrite Vbuild_nth. trivial. 
    rewrite H19. apply WeirdCs_Expand.
    (* Resuming Main proof *)
    (* Proving product *)
    +++++ rewrite Col1. rewrite MoC.VG_prod_pexp_fixed_base.
    (* Prove fact about index *)
    assert ((Vhead
        (FMatrix.mat_mult
           [Vcast
              (Vnth (VandermondeInv e)
                 (Vnth_cast_aux H15 indexM)) H15]
           (Vandermonde (Vcast e castingM5)))) = 
    VF_n_id indexM). 
    assert (Vcast (Vnth (MF_mult (VandermondeInv e)
        (Vandermonde e)) (Vnth_cast_aux H15 indexM)) H15  = Vnth 
    (MF_id (m+m)) indexM). rewrite invVandermondeLeft. do 2 rewrite Vbuild_nth. apply Veq_nth.
    intros. rewrite Vnth_cast. destruct (Nat.eq_dec m i).
    subst. do 2 rewrite Vnth_replace. trivial. rewrite Vnth_replace_neq; auto.
    rewrite Vnth_replace_neq; auto. do 2 rewrite Vnth_const. trivial. trivial.
    assert (VF_n_id indexM =  Vnth (MF_id (m + m)) indexM).
    apply Veq_nth. intros. rewrite Vbuild_nth.
    rewrite Vbuild_nth in H17. unfold VF_n_id. trivial. 
    rewrite H18. rewrite <- H17. rewrite Fmatrix_mult_vnth.
    apply Veq_nth. intros. symmetry. rewrite Vnth_cast. do 2 rewrite Vhead_nth. 
    do 2 rewrite FMatrix.mat_build_nth.
    unfold FMatrix.VA.dot_product. 
    do 2 rewrite Vfold_left_Fadd_eq. apply (Vfold_left_eq_cast H15).
    apply Veq_nth. intros. rewrite Vnth_cast. do 2 rewrite Vnth_map2.
    apply f_equal2. unfold FMatrix.get_row. symmetry. rewrite Vnth_cast.
    apply Veq_nth3. trivial. rewrite Vnth0. trivial.
    do 4 rewrite Vnth_map.  do 2 rewrite Vbuild_nth. apply Vfold_left_eq.
    apply Vtail_equal. rewrite Vnth_cast. apply Vnth_eq. trivial.
    (* Back to mainline *)
    rewrite H17. rewrite MoC.VG_n_exp.
    rewrite Vnth_app. destruct (le_gt_dec m support.m). do 2 rewrite Vbuild_nth.
    assert (Nat.add 1 (Nat.sub (Nat.sub m (m - m)) 1) = m). replace (Nat.sub m m) with 0%nat.
    unfold m. lia. lia. 
    rewrite (MoC.VG_prod_cast H18). apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_cast. do 2 rewrite Vnth_map2.
    do 2 rewrite Vnth_sub. apply f_equal. apply f_equal2.
    apply Vnth_eq. lia. apply Veq_nth. intros. rewrite HeqAj.
    rewrite FMatrix.mat_mult_elem. unfold extractor. 
    rewrite Vnth_tail. rewrite transpose_move_gen.
    rewrite FMatrix.mat_mult_elem. do 2 rewrite FMatrix.mat_transpose_idem.
    apply f_equal2. unfold FMatrix.get_row.  apply Veq_nth3. unfold m, support.m. lia.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_vbreak_1. intros. do 2 rewrite Vnth_cast.
    apply Vnth_eq. trivial.   apply Veq_nth. intros.
    do 4 rewrite Vnth_map. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_vbreak_1. intros. do 2 rewrite Vnth_cast.
    apply Veq_nth3; auto. apply f_equal. apply f_equal.
    apply f_equal. apply f_equal. apply Vnth_eq. lia.
    unfold m, support.m in *. assert False. lia. contradiction.


    (* The case where the commitments are broken (1/2) *)
    + intros. right. right. apply bVforall_false2 in H13.
    destruct H13. destruct H13. apply VF_beq_false in H13.
    exists (VG_prod (VG_Pexp (Vcons g1 v) (VandermondeCol (S m) (Vnth e x0)))).
    rewrite Vnth_map in H13. rewrite Vbuild_nth in H13.
    exists ((Vnth t x0).1.1.1.1). exists (Vhead
    (FMatrix.mat_mult [VandermondeCol (S (S (S M.N))) (Vnth e x0)] Aj)).
    exists (Vnth t x0).1.1.1.2. exists (Vfold_left Fadd 0
    (Vmap2 Fmul Rj (VandermondeCol (S m) (Vnth e x0)))). unfold relComEPC. split; auto.
    split. apply (bVforall2_elim_nth x0) in H0. apply bool_eq_corr in H0. 
    rewrite H0. simpl. trivial. apply VGeq in Lemma1. rewrite Lemma1.
    unfold VG_Pexp, VG_prod. rewrite comEPCDis. rewrite <- EPCMultExt.
    apply f_equal2. apply Veq_nth. intros. rewrite Vhead_nth.
    rewrite FMatrix.mat_mult_elem. rewrite Vfold_left_VF_add.
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq.
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_map. 
    do 2 rewrite Vnth_map2. rewrite Vnth_map. destruct module_ring.
    rewrite Rmul_comm. apply f_equal2. unfold FMatrix.get_row.
    apply Veq_nth3; auto. rewrite Vnth_map. trivial. trivial. 

    
    (* The case where the commitments are broken (2/2) *)
    + intros. right. left. exists (Vnth v1 indexM).
    apply F_bool_neq_corr in H13. exists (VF_inProd bT (FMatrix.get_col Y2M H6)).
    exists (VF_inProd sT (FMatrix.get_col Y2M H6)). unfold relComPC; auto. 
  Qed.

  Lemma honest_verifier_ZK :
    forall (s : St)(w : W)(e : F)(x : X)(r : R)(t : TE),
      simMapHelp s x ->
      Rel s w ->
      (P1 ((P0 s r w), e) r w) =
      simulator s (simMap s w e x r) e /\ 
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.
  Proof.
    
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.  
    pose Commitment.module_abegrp.
    intros. unfold Rel, P1, P0, simulator, simMap, simMapInv in *.
    destruct s, p, p, p, p, p. destruct r, p0, p0, p0. destruct w, p0, p2, p3, p1.
    split. intros.
    + (* First we need to prove the simulator produces same proof *)
    apply injective_projections. - apply injective_projections. 
    -- apply injective_projections. --- simpl. trivial.
    (* Commitments *)
    --- remember Vbreak as d. do 9 rewrite Prod_right_replace.
    do 5 rewrite Prod_left_replace. rewrite Heqd.
    assert (V1 (P1 (P0 (p, g0, v0, t0, g, v, m0) (v1, f, (v5, v6), (v3, v4), (t2, t3))
    (t1, v2, f0), e) (v1, f, (v5, v6), (v3, v4), (t2, t3)) (t1, v2, f0)) = true ->
   (P0 (p, g0, v0, t0, g, v, m0) (v1, f, (v5, v6), (v3, v4), (t2, t3)) (t1, v2, f0)).2 =
   (simulator (p, g0, v0, t0, g, v, m0)
      (simMap (p, g0, v0, t0, g, v, m0) (t1, v2, f0) e x
        (v1, f, (v5, v6), (v3, v4), (t2, t3))) e).1.1.2).
    intros. apply Sim_com. apply H. apply H1. apply H1.
     pose (correctness (p, g0, v0, t0, g, v, m0)(t1, v2, f0)(v1, f, (v5, v6), (v3, v4), (t2, t3))). 
    unfold P0 in e0. apply e0. trivial. 
    (* challenge *)
    -- simpl. trivial.
    (* response *)
    - apply injective_projections. apply injective_projections.
    trivial. trivial. trivial.

    (* Time to deal with the Bijection   *)
    + unfold simMapInv. unfold simMap. 
    assert (forall n', Vhead (VandermondeCol (S n') e) = 1). intros.
    rewrite Vbuild_head. cbn. trivial. split.
    (* Lets deal with the first part of bijection *)
    ++ 
    apply injective_projections. apply injective_projections. apply injective_projections.
    apply injective_projections.
    --- do 2 rewrite Prod_left_replace. 
    unfold VF_sub. rewrite VF_mat_cancel; auto. 
    --- do 2 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
    do 2 rewrite InProd_Sum. apply VF_sum_vcons_cancel_gen; auto.
    --- do 4 rewrite Prod_left_replace. do 3 rewrite Prod_right_replace.
    apply injective_projections. 
    ---- rewrite Prod_left_replace. 
    remember Vbreak as c. rewrite Prod_right_replace.
    unfold VF_sub. rewrite VF_mat_cancel; auto. rewrite Heqc.
    rewrite (EkGeneratorsRawM_switch v5 v6). rewrite <- VSn_eq.
    rewrite Vapp_Vtail. pose Vbreak_eq_app. symmetry in e0. rewrite e0.
     unfold VF_add, VF_neg, FMatrix.VA.vector_plus, FSemiRingT.Aplus.
    rewrite <- Vtail_map. rewrite Vtail_map2. rewrite (EkGeneratorsRawM_clear x.1.2).
    do 2 rewrite InProd_Sum. rewrite VF_sum_vcons_cancel_gen; auto.
    rewrite Prod_left_replace. rewrite (Vhead_app (n:=S M.N)). rewrite <- Vapp_Vtail.
    rewrite Vbreak_app. rewrite <- VSn_eq. trivial.
    ---- rewrite Prod_right_replace. rewrite Prod_left_left_replace.
    remember Vbreak as c. rewrite Prod_right_replace. rewrite Heqc.
     unfold VF_sub. rewrite VF_mat_cancel; auto.
    rewrite (EkGeneratorsRawM_switch v5 v6). rewrite <- VSn_eq.
    rewrite Vapp_Vtail. pose Vbreak_eq_app. symmetry in e0. rewrite e0. 
    unfold VF_add, VF_neg, FMatrix.VA.vector_plus, FSemiRingT.Aplus.
    rewrite <- Vtail_map. rewrite Vtail_map2. rewrite (EkGeneratorsRawM_clear x.1.2).
    rewrite Vbreak_Vtail_clear. rewrite Vbreak_app. simpl. trivial.
    --- rewrite Prod_left_replace. remember Vbreak as c. 
    do 4 rewrite Prod_right_replace. rewrite Prod_left_replace. 
    rewrite Heqc. apply injective_projections.
    ---- rewrite <- Heqc. do 2 rewrite Prod_left_replace. 
    rewrite Heqc.
    unfold VF_sub. rewrite VF_mat_cancel; auto. 
    rewrite (EkGeneratorsRawM_switch v5 v6). 
    rewrite (Vapp_Vtail (n:=S M.N)). 
    pose Vbreak_eq_app. symmetry in e0. rewrite <- VSn_eq. rewrite e0.
    unfold VF_add, FMatrix.VA.vector_plus. do 2 rewrite <- Vbreak_vmap2_1.
    rewrite <- (Vapp_Vtail (n:=S M.N)). do 2 rewrite Vbreak_app. do 2 rewrite Prod_left_replace.
    remember (Vapp v3 (Vcons 0 v4)) as d. 
    remember (Vapp v5 (Vcons 0 v6)) as l.
    assert (0 = Vhead (Vbreak (Vmap2 FSemiRingT.Aplus d (VF_scale l (Vhead x.1.1)))).2).
    intros. rewrite <- Vbreak_vmap2_2. unfold VF_scale. rewrite <- Vbreak_vmap_2. 
    rewrite Heqd. rewrite Heql. do 2 rewrite Vbreak_app.  do 2 rewrite Prod_right_replace. 
    rewrite Vhead_map2. rewrite Vhead_map. simpl. unfold FSemiRingT.Aplus. ring; auto. 
    rewrite H2. rewrite <- VSn_eq. rewrite Heqd. rewrite Heql.
    rewrite <- Vbreak_vmap2_2. unfold VF_scale. rewrite <- Vbreak_vmap_2.
    rewrite <- Vbreak_vmap_1. do 2 rewrite Vbreak_app.  do 2 rewrite Prod_right_replace. 
    rewrite Prod_left_replace. unfold VF_neg, FSemiRingT.Aplus. rewrite <- Vtail_map.
    rewrite Vtail_map2. rewrite (EkGeneratorsRawM_clear x.1.2). rewrite Vapp_Vtail.
    rewrite <- Vapp_map2. rewrite <- VectorUtil.Vapp_map. do 2 rewrite <- Vtail_map.
    rewrite Vtail_map2. pose VF_add_ass. pose VF_neg_corr. pose VF_add_zero. 
    unfold VF_add, FMatrix.VA.vector_plus, FSemiRingT.Aplus, VF_neg in *.
    rewrite e1. rewrite e2. rewrite e3. do 2 rewrite InProd_Sum. rewrite Vtail_map2.
    rewrite VF_sum_vcons_cancel_gen; auto. rewrite (Vhead_app (n:=S M.N)).
    rewrite <- Vbreak_Vtail. rewrite Vtail_map2. pose Vbreak_vmap_1. symmetry in e4.
    do 2 rewrite e4. rewrite Vbreak_app. rewrite Prod_left_replace.
    rewrite e1. rewrite e2. rewrite e3.
    symmetry. apply VSn_eq.
    
    ---- do 2 rewrite Prod_right_replace. unfold VF_sub.
    unfold VF_add, VF_neg, FMatrix.VA.vector_plus. rewrite <- Vbreak_vmap2_2.
    rewrite Vbreak_app. rewrite Prod_right_replace. pose VF_mat_cancel.
    unfold VF_add, VF_neg, FMatrix.VA.vector_plus in e0. rewrite e0; auto.
    rewrite (EkGeneratorsRawM_switch v5 v6). rewrite <- VSn_eq.
    pose Vbreak_eq_app. symmetry in e1. rewrite e1.
     rewrite <- Vtail_map2. 
    rewrite Vtail_cons. rewrite <- Vtail_map. do 2 rewrite Vtail_map2. unfold FSemiRingT.Aplus.
    rewrite (EkGeneratorsRawM_clear x.1.2). pose Vbreak_vmap2_2. symmetry in e2.
    rewrite e2. rewrite <- Vbreak_vmap_2. unfold VF_scale.
    rewrite <- Vbreak_vmap_2.
     do 2 rewrite (Vbreak_app (n1 := m)).
    rewrite <- Vbreak_vmap_2. rewrite Vbreak_Vtail_clear. rewrite (Vbreak_app (n1 := m)).
    do 2 rewrite <- Vtail_map2. rewrite Vtail_cons. do 3 rewrite Vtail_map.
    rewrite Vtail_cons. pose VF_add_ass. pose VF_neg_corr.
    unfold VF_add, FMatrix.VA.vector_plus in *. rewrite e3. rewrite e4.
    pose VF_add_zero. unfold VF_add, FMatrix.VA.vector_plus in e5. apply e5.
    --- remember Vbreak as d. do 2 rewrite Prod_left_replace. 
    do 4 rewrite Prod_right_replace. apply injective_projections.
    ---- do 2 rewrite Prod_left_replace. rewrite Heqd. 
    unfold VF_sub. rewrite VF_mat_cancel; auto. rewrite Prod_right_replace.
    rewrite (EkGeneratorsRawR_switch t2 t3). rewrite <- VSn_eq.
    rewrite Vapp_Vtail. rewrite <- Vbreak_eq_app. unfold MoR.VF_sub, MoR.VF_neg, 
    MoR.VF_add, MoR.FMatrix.VA.vector_plus. rewrite <- Vtail_map. rewrite Vtail_map2. 
    unfold MoR.FSemiRingT.Aplus. rewrite (EkGeneratorsRawR_clear x.2). 
    rewrite <- Vbreak_Vtail. rewrite Vbreak_app.
    rewrite Prod_left_replace. rewrite MoR.VF_sum_induction.
    rewrite Vtail_map2. assert (forall a b, Ring.Fsub (Ring.Fadd a b) a = b).
    intros. destruct Ring.module_ring. rewrite Rsub_def. rewrite (Radd_comm a2).
    rewrite <- Radd_assoc. rewrite Ropp_def. rewrite Radd_comm. apply Radd_0_l.
    rewrite H2. rewrite Vhead_map2. rewrite (Vhead_app (n:=S M.N)). rewrite Vbuild_head.
    cbn. rewrite MVS.RopFOne. rewrite <- VSn_eq. trivial.
    ---- do 2 rewrite Prod_right_replace. 
    unfold VF_sub. rewrite VF_mat_cancel; auto. rewrite Heqd.
    rewrite (EkGeneratorsRawR_switch t2 t3). 
    rewrite <- VSn_eq. rewrite Vapp_Vtail. rewrite <- Vbreak_eq_app.
    unfold MoR.VF_sub, MoR.VF_neg, MoR.VF_add, MoR.FMatrix.VA.vector_plus, MoR.FSemiRingT.Aplus. 
    rewrite <- Vtail_map. rewrite Vtail_map2. rewrite (EkGeneratorsRawR_clear x.2).
    rewrite Vbreak_Vtail_clear.  rewrite Vbreak_app. simpl. trivial.


    (* and the other way *)
    (* (((VF n)*F*F*F*Ring.F)*((VF M.N*VF M.N)*
    (VF M.N*VF M.N)*((vector Ring.F M.N)*(vector Ring.F M.N)))).*)
    ++ remember Vbreak as C. destruct t, p1, p1, p1, p0, p3, p2, p0, p0, p0. 
    do 2 rewrite Prod_right_replace. do 2 rewrite Prod_left_replace. 
    apply injective_projections.
    --- (* ((VF n)*F*F*F*Ring.F) *)
    apply injective_projections.  apply injective_projections.
    apply injective_projections. apply injective_projections. 
    (* 1 of 5 *)
    ---- do 6 rewrite Prod_left_replace. rewrite VF_mat_cancel_rev; auto. 
    (* 2 of 5 *)
    ---- do 2 rewrite Prod_right_replace.
    do 2 rewrite InProd_Sum. pose VF_comm_mult. pose VF_sum_vsub_cancel_gen.
    unfold VF_mult in *. rewrite <- (e0 (Nat.add 1 m) ((VandermondeCol (1 + m) e))).
    rewrite (e0 m v2). rewrite e1; auto.   
    (* 3 of 5 *)
    ---- do 2 rewrite Prod_right_replace. 
    do 2 rewrite InProd_Sum. pose VF_sum_vsub_cancel_gen. pose VF_comm_mult.
    unfold VF_mult in *. rewrite Vapp_cons. rewrite e1.
    rewrite <- (e1 (Nat.add (S M.N) m) (Vtail (VandermondeCol (m + m) e))). rewrite e0; auto.
    unfold VF_sub, VF_add, FMatrix.VA.vector_plus.
    rewrite HeqC. rewrite <- Vbreak_vmap2_2. rewrite <- Vbreak_vmap2_1. 
    rewrite Vbreak_app. rewrite Prod_right_replace. rewrite Prod_left_replace.
    rewrite <- Vtail_map2. rewrite (Vtail_cons _ v8). apply Veq_nth. intros. 
    rewrite Vnth_map2. do 2 rewrite (Vnth_app (n1:=S M.N)). 
    destruct (le_gt_dec (S M.N) i). 
    ----- do 2 rewrite Vnth_cons. destruct (lt_ge_dec 0 (i - S M.N)).
    ------ rewrite Vnth_map2. apply f_equal2; auto. rewrite Vnth_tail.
    rewrite Vnth_vbreak_2.
    assert (i < S M.N + S (S M.N)). apply ip. lia. intros. apply Vnth_eq. lia.
    ------ unfold EkGeneratorsRawM. unfold VF_add, FMatrix.VA.vector_plus.
    rewrite <- Vbreak_vmap2_2. do 2 rewrite Vbreak_app. 
    do 2 rewrite Prod_right_replace.  rewrite Vhead_map2. rewrite <- Vtail_map2. 
    rewrite Vhead_cons. rewrite Vnth_map. rewrite Vnth_map2. unfold FSemiRingT.Aplus.
    do 2 rewrite Vnth_tail. assert (S i < (S (S M.N)) + (S (S M.N))). lia.  
    assert (lt_n_S ip = H2). apply le_unique. rewrite H3. unfold X, m in *.
    rewrite (Vnth_app (n1:=S (S M.N))). destruct (le_gt_dec (S (S M.N)) (S i)).
    rewrite Vnth_const. assert (forall a a', a= a'-> 0+a-(0+a') = 0). intros.
    rewrite H4. field. apply H4. rewrite Vhead_nth. apply Vnth_eq. lia.
    assert False. lia. contradiction.

    ----- rewrite Vnth_map2. apply f_equal2; auto. rewrite Vnth_vbreak_1.
    trivial.
    (* 4 of 5 *)
    ---- do 3 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace. 
    unfold VF_sub, VF_add, VF_neg, VF_scale, FMatrix.VA.vector_plus. 
    pose Vbreak_vmap2_2. symmetry in e0. rewrite HeqC. rewrite e0. 
    rewrite <- Vbreak_vmap2_1. do 2 rewrite <- Vbreak_vmap_1.
    do 2 rewrite Vbreak_app. rewrite <- HeqC. do 2 rewrite Prod_right_replace.  
    rewrite HeqC. rewrite <- Vbreak_vmap2_1. do 2 rewrite Vbreak_app.
    do 2 rewrite Prod_left_replace. rewrite <- Vbreak_vmap2_2.
    do 2 rewrite <- Vbreak_vmap_2.  rewrite <- Vbreak_vmap2_2. do 2 rewrite Vbreak_app.
    do 2 rewrite Prod_right_replace. rewrite <- Vtail_map2. do 2 rewrite Vtail_map.
    rewrite <- Vtail_map2. rewrite (Vtail_cons _ v8). unfold EkGeneratorsRawM.
    unfold VF_add, FMatrix.VA.vector_plus. rewrite Vhead_map2.
    rewrite Vbuild_head. rewrite <- Vbreak_vmap_2. rewrite <- Vbreak_vmap_1.
    rewrite Vbreak_Vtail_clear. rewrite <- Vbreak_vmap2_2. rewrite Vbreak_app.
    rewrite Prod_right_replace. rewrite Vtail_cons. 
    do 2 rewrite InProd_Sum. pose VF_sum_vsub_cancel_gen.
    unfold VF_mult in e1. rewrite Vapp_cons. pose VF_comm_mult. unfold VF_mult in *.
    rewrite e2. rewrite (e2 _ _ (Vtail (VandermondeCol (m + m) e))). apply e1.
    rewrite Vbuild_head.  cbn. trivial. apply Veq_nth. intros.
    rewrite Vnth_map2. do 2 rewrite Vnth_map. rewrite Vnth_map2.
    rewrite Vhead_cons. rewrite <- Vtail_map2. unfold X, m, n in *.
    rewrite (Vapp_Vtail2 (n:=S M.N)). rewrite <- Vbreak_vmap2_1.
    rewrite Vbreak_app. rewrite Prod_left_replace. rewrite Vnth_map.
    rewrite Vnth_map2. 
    do 4 rewrite Vnth_app. destruct (le_gt_dec (S M.N) i).
    ----- do 3 rewrite Vnth_cons. destruct (lt_ge_dec 0 (i - S M.N)). 
    rewrite Vnth_map2. rewrite (Vtail_cons _ v10). do 2 rewrite Vnth_map. 
    rewrite Vnth_map2. apply f_equal. apply f_equal. apply f_equal2. apply f_equal2.
    apply Vnth_eq. trivial. rewrite Vnth_tail. rewrite Vnth_map. rewrite Vnth_map2.
    ------ apply f_equal. apply f_equal2. rewrite Vnth_vbreak_2. lia. intros.
    rewrite Vnth_tail. do 2 rewrite Vnth_const. trivial. apply Vnth_eq.
    lia. 
    ------ trivial.
    ------ unfold FSemiRingT.Aplus. rewrite Vnth_tail. rewrite Vnth_const.
    assert (forall a a', a = a' -> (0 + a -(0 +a')) = 0). intros. rewrite H2.
    field. rewrite H2. field. symmetry. rewrite Vbuild_nth. apply Vnth_eq. lia. 
    ----- rewrite Vnth_map2. do 2 rewrite Vnth_map. rewrite Vnth_map2.
    rewrite Vnth_map. rewrite Vnth_map2. apply f_equal. apply f_equal.
    apply f_equal2; auto. apply f_equal. rewrite Vnth_vbreak_1.
    do 2 rewrite Vnth_tail. rewrite Vnth_const. trivial.

    (* 5 of 5 *)
    ---- do 2 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace. 
    rewrite HeqC. unfold MoR.VF_sub, MoR.VF_add, MoR.VF_neg, MoR.FMatrix.VA.vector_plus. 
    rewrite <- Vbreak_vmap2_2. rewrite <- Vbreak_vmap2_1. 
    rewrite Vbreak_app. rewrite <- HeqC. rewrite Prod_left_replace. 
    rewrite Prod_right_replace. rewrite <- Vtail_map2.  rewrite (Vtail_cons _ t4).
    assert (forall n' (a : Ring.F)(b b' : MoR.VF n')(c : VF (S n')),
     Vhead c = 1 -> b = b' -> MoR.VF_sum (Vmap2 MVS.op3
      (Vcons (Ring.Fsub a (MoR.VF_sum (Vmap2 MVS.op3 b (Vtail c) ))) b') c) = a).
    intros. rewrite H3. rewrite (VSn_eq c). rewrite Vcons_map2. 
    rewrite <- VSn_eq. rewrite H2. rewrite MVS.RopFOne. rewrite MoR.VF_sum_vcons. 
    destruct Ring.module_ring. rewrite Rsub_def. rewrite Radd_comm. rewrite <- Radd_assoc.
    rewrite (Radd_comm (Ring.Finv (MoR.VF_sum (Vmap2 MVS.op3 b' (Vtail c))))).
    rewrite Ropp_def. rewrite Radd_comm. apply Radd_0_l. rewrite Vapp_cons.
    apply H2. (* We have now cleaned up the goal and applied a simplifying lemma *)
    rewrite Vbuild_head. cbn. trivial. 
    apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vnth_app.
    destruct (le_gt_dec (S M.N) i). 
    ----- do 2 rewrite Vnth_cons. destruct (lt_ge_dec 0 (i - S M.N)).
    ------ rewrite Vnth_map2. symmetry. apply f_equal2; auto.
    rewrite HeqC. rewrite Vnth_tail. rewrite Vnth_vbreak_2. lia. intros.
    apply Vnth_eq. lia. 
    ------ rewrite Vnth_map. rewrite HeqC. unfold EkGeneratorsRawR. unfold MoR.VF_add, 
    MoR.FMatrix.VA.vector_plus. rewrite <- Vbreak_vmap2_2. do 2 rewrite Vbreak_app.
    do 2 rewrite Prod_right_replace. rewrite Vnth_tail.
    rewrite Vtail_cons. rewrite Vnth_map2. rewrite Vhead_map2. rewrite Vhead_cons.
    rewrite Vnth_const. unfold MoR.FSemiRingT.Aplus. assert (forall a b c, 
    a = b -> Ring.Fadd (Ring.Fadd c b) (Ring.Finv a) = c). intros. rewrite H3.
    destruct Ring.module_ring. rewrite <- Radd_assoc. rewrite Ropp_def. 
    rewrite Radd_comm. apply Radd_0_l. apply H3. destruct Ring.module_ring.
    rewrite Radd_0_l. assert (i = S M.N). lia. subst. assert (S (S M.N) <
    S (S M.N) + S (S M.N)). lia. assert (H4 = (lt_n_S ip)). apply le_unique.
    rewrite <- H5. unfold X, m in *. rewrite (Vnth_app (n1:=S (S M.N))).
    destruct (le_gt_dec (S (S M.N)) (S (S M.N))). rewrite Vhead_nth. apply Vnth_eq.
    lia. assert False. lia. contradiction. 
    ----- rewrite Vnth_map2. apply f_equal2; auto. rewrite HeqC. 
    rewrite Vnth_vbreak_1. apply Vnth_eq. trivial.
    (* ((VF M.N*VF M.N)* 



    (VF M.N*VF M.N)*((vector Ring.F M.N)*(vector Ring.F M.N)) *)
    --- do 2 rewrite Prod_right_replace. 
    apply injective_projections. apply injective_projections. 
    (* 1 of 3 *)
    ---- do 3 rewrite Prod_left_replace. 
    apply injective_projections. 
    ----- do 2 rewrite Prod_left_replace. unfold EkGeneratorsRawM.
    unfold VF_add, FMatrix.VA.vector_plus. rewrite HeqC. rewrite <- Vbreak_vmap2_1.
    do 2 rewrite Vbreak_app. do 2 rewrite Prod_left_replace. rewrite <- Vmap2_tail. 
    rewrite Vtail_cons. unfold VF_sub, VF_add, FMatrix.VA.vector_plus, VF_neg.
    rewrite <- Vbreak_vmap2_1. rewrite <- Vbreak_vmap_1. rewrite <- Vbreak_Vtail.
    rewrite <- Vbreak_vmap2_1. do 2 rewrite Vbreak_app. do 2 rewrite Prod_left_replace.
    rewrite Vbreak_Vconst. rewrite Prod_left_replace. pose VF_comm. pose VF_add_zero.
    pose VF_add_neg2. unfold VF_add, FMatrix.VA.vector_plus, VF_neg in *. 
    rewrite (e0 m (Vconst Fzero m)). rewrite e1. rewrite e2. trivial. 
    ----- do 2 rewrite Prod_right_replace. unfold EkGeneratorsRawM.
    unfold VF_add, FMatrix.VA.vector_plus. rewrite HeqC.
    rewrite <- Vbreak_vmap2_2. do 2 rewrite Vbreak_app. do 2 rewrite Prod_right_replace. 
    rewrite <- Vmap2_tail.  rewrite Vtail_cons. unfold VF_sub, VF_add, FMatrix.VA.vector_plus, VF_neg. 
    rewrite <- Vbreak_vmap2_2. rewrite <- Vbreak_vmap_2. rewrite Vbreak_Vtail_clear.
    rewrite <- Vbreak_vmap2_2. do 2 rewrite Vbreak_app. do 2 rewrite Prod_right_replace.
    rewrite <- Vmap2_tail. rewrite Vtail_cons. 
    rewrite <- Vbreak_vmap2_2. rewrite Vbreak_app. rewrite Prod_right_replace.
    rewrite Vbreak_Vconst. rewrite Prod_right_replace. pose VF_comm. pose VF_add_zero.
    pose VF_add_neg2. unfold VF_add, FMatrix.VA.vector_plus, VF_neg in *. 
    rewrite (e0 m (Vconst Fzero m)). rewrite e1. rewrite Vtail_map. rewrite e2. trivial. 
    (* 2 of 3 *)
    ---- do 2 rewrite Prod_right_replace. apply injective_projections. 
    ----- do 2 rewrite Prod_left_replace. 
    unfold VF_sub. unfold VF_add,
    VF_neg, FMatrix.VA.vector_plus. rewrite HeqC. rewrite <- Vbreak_vmap2_1. 
    rewrite Vbreak_app. rewrite Prod_left_replace. rewrite <- Vtail_map2. 
    rewrite Vtail_cons.
    rewrite <- Vbreak_vmap2_1. unfold VF_scale. do 2 rewrite <- Vbreak_vmap_1. 
    rewrite <- Vbreak_vmap2_1. do 2 rewrite (Vbreak_app (n1:=S M.N)). 
    do 2 rewrite Prod_left_replace. do 2 rewrite <- Vbreak_vmap_1.
    rewrite (Vbreak_app (n1:=m)). rewrite Prod_left_replace.
    rewrite Vtail_map. rewrite Vtail_cons. unfold FSemiRingT.Aplus. 
    assert (forall n (a b b' : VF n) , b= b' -> Vmap2 Fadd (
    Vmap2 Fadd a (Vmap Finv b)) b' = a). intros. rewrite H2. pose VF_add_neg2.
    unfold VF_add, FMatrix.VA.vector_plus in *. apply e0. apply H2.  trivial. 
    ----- do 2 rewrite Prod_right_replace. rewrite HeqC.
    unfold VF_sub, VF_add, VF_neg, FMatrix.VA.vector_plus. 
     rewrite <- Vbreak_vmap2_2. rewrite Vbreak_app. rewrite Prod_right_replace.
    rewrite <- Vtail_map2. rewrite Vtail_cons. pose Vbreak_vmap2_2. symmetry in e0.
    rewrite e0. unfold VF_scale. do 2 rewrite e0. do 4 rewrite <- Vbreak_vmap_2.
    rewrite <- Vbreak_vmap2_2. do 5 rewrite Vbreak_app. do 5 rewrite Prod_right_replace.
    rewrite Vtail_map. rewrite Vtail_cons. do 2 rewrite <- Vtail_map2.
    rewrite (Vtail_cons _ v8). do 2 rewrite Vtail_map. rewrite <- Vtail_map2.
    rewrite (Vtail_cons _ v8). rewrite Vtail_cons. pose VF_add_neg2.
    unfold VF_add, FMatrix.VA.vector_plus, VF_neg in *. rewrite Vbreak_vmap_2. 
    apply e1.
    (* 3 of 3 *)
    ---- do 2 rewrite Prod_right_replace. 
    unfold EkGeneratorsRawR. apply injective_projections.
    ----- do 2 rewrite Prod_left_replace. unfold MoR.VF_add, MoR.FMatrix.VA.vector_plus.
    rewrite HeqC. rewrite <- Vbreak_vmap2_1. do 2 rewrite Vbreak_app. do 2 rewrite Prod_left_replace.
    do 2 rewrite <- Vtail_map2. rewrite Vtail_cons.
    rewrite <- Vbreak_vmap2_2. rewrite (Vapp_Vtail2 (n:=S M.N)). 
    do 2 rewrite Vbreak_app. do 2 rewrite Prod_right_replace. unfold MoR.VF_zero.
    rewrite Vapp_Vconst. unfold MoR.VF_sub.
    unfold MoR.VF_sub. pose VectorUtil.Vapp_map. unfold MoR.VF_neg.
    unfold MoR.VF_add, MoR.FMatrix.VA.vector_plus. rewrite <- Vbreak_vmap2_1.
    rewrite Vbreak_app. rewrite Prod_left_replace.  pose MoR.VF_add_zero. 
    pose MoR.VF_comm. pose MoR.VF_add_neg2. unfold MoR.VF_add, 
    MoR.FMatrix.VA.vector_plus, MoR.VF_neg in *. rewrite <- Vbreak_vmap_1.
    rewrite <- Vbreak_vmap2_1. rewrite <- Vbreak_Vtail. do 2 rewrite Vbreak_app.
    do 2 rewrite Prod_left_replace. 
    rewrite (e2 (S M.N) (Vtail (Vconst Ring.Fzero m))). rewrite e1. apply e3. 
    ----- rewrite Prod_right_replace. unfold MoR.VF_add, MoR.FMatrix.VA.vector_plus.
    rewrite HeqC. rewrite <- Vbreak_vmap2_2. do 2 rewrite Vbreak_app.
    do 2 rewrite Prod_right_replace. rewrite <- Vmap2_tail. rewrite Vtail_cons.
    unfold MoR.VF_sub, MoR.VF_add, MoR.VF_neg, MoR.FMatrix.VA.vector_plus. 
    pose Vbreak_vmap2_2. symmetry in e0. do 2 rewrite e0. 
    do 2 rewrite Vbreak_app. rewrite <- HeqC. do 2 rewrite Prod_right_replace.
    rewrite <- Vmap2_tail. rewrite Vtail_cons. rewrite HeqC.
    rewrite <- Vbreak_vmap_2. rewrite Vbreak_Vtail_clear. rewrite <- Vbreak_vmap2_2.
    rewrite Vbreak_app. rewrite Prod_right_replace. rewrite Vtail_map. 
    rewrite Vbreak_Vconst. rewrite Prod_right_replace. pose MoR.VF_add_zero.
    pose MoR.VF_comm. unfold  MoR.VF_add, MoR.FMatrix.VA.vector_plus in e2.
    unfold  MoR.VF_add, MoR.FMatrix.VA.vector_plus in e1.
    rewrite (e2 m (Vconst Ring.Fzero m)). rewrite e1. rewrite Vtail_cons.
    rewrite e2. pose MoR.VF_add_neg3. 
    unfold MoR.VF_add, MoR.FMatrix.VA.vector_plus, MoR.VF_neg in e3.
    pose MoR.VF_add_ass. rewrite e3. trivial. 
  Qed.

  Lemma simulator_correct : forall (s : St)(t : TE)(e : F),
    V1(simulator s t e) = true.
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.  
    pose Commitment.module_abegrp. intros. unfold V1. unfold simulator. 
    destruct s, p, p, p, p, p. destruct t, p0, p0, p0, p0, p1, p0, p1, p0, p2.
    apply andb_true_iff. split. apply andb_true_iff. split. 
    apply andb_true_iff. split.  apply andb_true_iff. split.
    (* Correct 1 of 5 *)
    ++ apply bool_eq_corr. remember (VandermondeCol (1 + m)) as x.
    simpl. rewrite <- VG_Pexp_Vcons. rewrite <- VSn_eq. rewrite <- VSn_eq.
    replace (Vhead (x e)) with 1. rewrite mod_id. rewrite VG_prod_Vcons.
    rewrite comm. rewrite <- dot_assoc. rewrite <- inv_left. rewrite one_right. trivial.
    rewrite Heqx. rewrite Vbuild_head. cbn. trivial. 
    (* Correct 2 of 5 *)
    ++ apply bool_eq_corr. simpl. rewrite VG_prod_Vcons. rewrite comm.
    replace (VF_prod [ ]) with 1. rewrite mod_id. rewrite <- dot_assoc.
    rewrite <- inv_left. rewrite one_right. trivial. cbn. trivial.
    (* Correct 3 of 5 *)
    ++ apply bool_eq_corr. remember rev as x. remember VandermondeCol as y.
    simpl. rewrite MoC.VG_prod_Vcons. replace (Vhead (y (S (S (M.N + m))) e)) with 1.
    rewrite VS1.mod_id. rewrite <- dot_assoc. rewrite comm. rewrite <- dot_assoc.
    apply f_equal2. trivial. rewrite <- dot_assoc. rewrite <- inv_left. rewrite one_right.
    trivial. rewrite Heqy. rewrite Vbuild_head. cbn. trivial.
    (* Correct 4 of 5 *)
    ++ apply bool_eq_corr. simpl. rewrite Vnth_map. rewrite (Vnth_app (n1:=S M.N)).
     destruct (le_gt_dec (S M.N) (S M.N)).
    rewrite Vnth_cons. destruct (lt_ge_dec 0 (S M.N - S M.N)).
    assert False. lia. contradiction. unfold PC. do 2 rewrite mod_ann. symmetry. 
    apply one_right. assert False. lia. contradiction. 
    (* Correct 5 of 5 *) 
    ++ apply bool_eq_corr. simpl. rewrite Vnth_app. destruct (le_gt_dec M.N M.N).
    rewrite Vnth_cons. destruct (lt_ge_dec 0 (M.N - M.N)).
    assert False. lia. contradiction. trivial. assert False. lia. contradiction.
  Qed.

End BGMultiArg.

Module BGMultiArgIns (Message Ciphertext Commitment : GroupSig)(Ring : RingSig)
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
  Let n := S ( S (S Hack.N)).    (* n *)
  Let m := S (S M.N).            (* m *)
  Import Field.

  Import Mo.
  Import Mo.mat.

  Import EPC.
  Import EPC.MoM.

  Import PC.

  Import ALenc.
  (* Module HardProb := HardProblems Commitment Field VS2. *)
  Import HardProb.

  (* Module ALR := RingAddationalLemmas Ring.*)

  Import VS2.
  Import Commitment.

  (* End casting *)

  Definition St : Type :=
  (* pk ck=(h,hs) (Cbar_1=(H_1,...,H_n),...,Cbar_m) *)
  enc.PK*G*(VG n)*(vector (vector Ciphertext.G n) m)*
        Ciphertext.G*(VG m)*enc.M. (* C cA G *)
  (* A = {aBar_1=(a_1,..,a_n),..,aBar_m} r p *)
  Definition W : Type := (vector (VF n) m)*(VF m)*Ring.F.
  (* a0 r0 b s tau *)
  Definition R : Type := (VF n)*F*((VF m)*(VF (S M.N)))
      *((VF m)*(VF (S M.N)))*((vector Ring.F m)*(vector Ring.F (S M.N))).
  (* cA0 cB0 cB1 E0 E1 *)
  Definition C : Type := (G*(VG (m+m))*
    (vector Ciphertext.G (m+m))).
  (* a r b s tau *) (* R = T when m = 1 *)
  Definition T : Type := ((VF n)*F*F*F*Ring.F).
  Definition X : Type := (VF n*vector (VF n) m*vector (vector Ring.F n) m).
  Definition TE : Type := (((VF n)*F*F*F*Ring.F)*((VF (S M.N)*VF (S M.N))*
    (VF (S M.N)*VF (S M.N))*((vector Ring.F (S M.N))*(vector Ring.F (S M.N))))).

  Definition simMapHelp (s : St)(x : X) :=
    let '(pk, h, hs, Cbar, C, cA, G) := s in

    hs = Vmap (op h) x.1.1 /\
    Cbar = Vmap2 (fun y z => Vmap2 (fun w v => enc.enc pk (VS3.op G w) v) y z) x.1.2 x.2 .

  Definition Rel (s : St)(w : W) : bool :=
    let '(pk, h, hs, Cbar, C, cA, G) := s in
    (* let '(A, r, p) := w in *)
    let A := w.1.1 in
    let r := w.1.2 in
    let p := w.2 in

      (* cA_1 = EPC A_1 r_1 *)
      VG_eq cA (comEPC h hs A r) &&
      (* C = (Enc pk 1 p) o (Prod C_i^a_i) *)
      Ciphertext.Gbool_eq C (Ciphertext.Gdot (enc.enc pk enc.Mzero p) (MoC.VG_prod
        (Vmap2 (fun x y => MoC.VG_prod  (MoC.VG_Pexp x y))
          Cbar A))).

  Definition fail_event (s : St)(c : C)(e : VF (2*m)) : Prop :=
    let '(pk, h, hs, Cbar, C, cA, G) := s in

      (exists c m0 r, relComPC h (Vhead hs) c 0 m0 0 r) \/
      (exists c m0 m1 r r', relComEPC h hs c m0 m1 r r').

  Definition P0 (st : St)(r : R)(w : W) : St*C :=
    let '(pk, h, hs, Cbar, C, cA, G) := st in
    let '(a0, r0, b, s, tau) := r in

    let b   := Vapp b.1 (Vcons 0 b.2)  in
    let s0  := Vapp s.1 (Vcons 0 s.2) in

    let A := Vcons a0 (w.1.1) in
    let p := w.2 in

    let tau := Vapp tau.1 (Vcons p tau.2)  in

    let cA0 := EPC h hs a0 r0 in
    let cB0 := comPC h (Vhead hs) b s0 in

    let E0 := EkGenerators pk G Cbar A tau b (VF_one (m+m)) in
    
    
    (st,(cA0, cB0, E0)).

  Definition P1 (ggtoxgtorc: St*C*F)
      (r : R) (w: W) : St*C*F*T :=
    let c := ggtoxgtorc.2 in

    let A := w.1.1 in
    let p := w.2 in

    let a0  := r.1.1.1.1 in
    let r0  := r.1.1.1.2 in
    let b   := Vapp r.1.1.2.1 (Vcons 0 r.1.1.2.2)  in
    let s0  := Vapp r.1.2.1 (Vcons 0 r.1.2.2) in
    let tau := Vapp r.2.1 (Vcons w.2 r.2.2) in

    let r := w.1.2 in

    let xBar := (VandermondeCol (1+m) c) in
    let xK := VandermondeCol (m+m) c in

    (* aBar = a0 + A xBar , since we tranpose both A and xBar *)
    let aT := Vhead (FMatrix.mat_mult [xBar] (Vcons a0 A)) in
    let rT := VF_inProd (Vcons r0 r) xBar in
    let bT := (VF_inProd b xK) in
    let sT := (VF_inProd s0 xK) in
    let tauT := MoR.VF_sum (Vmap2 MVS.op3 tau xK) in

    (ggtoxgtorc, (aT, rT, bT, sT, tauT)).

  Definition V1 (transcript : St*C*F*T) :bool :=
    let '(stat, comm, chal, resp) := transcript in
    let '(pk, h, hs, Cbar, C, cA, G) := stat in
    let '(cA0, cB, E) := comm in

    let x := rev (VandermondeCol m chal)in
    let xBar := VandermondeCol (1+m) chal in
    let xK := VandermondeCol (m+m) chal  in

    let aT := resp.1.1.1.1 in
    let rT := resp.1.1.1.2 in
    let bT := resp.1.1.2 in
    let sT := resp.1.2 in
    let tauT := resp.2 in

    let eq1 := Gbool_eq (VG_prod (VG_Pexp (Vcons cA0 cA) xBar))
       (EPC h hs aT rT) in

    let eq2 := Gbool_eq (VG_prod (VG_Pexp cB xK))
      (PC h (Vhead hs) bT sT) in

    (* Prod E^xK = (Enc G^b tau) o Prod Prod C_i *)
    let eq3 := Ciphertext.Gbool_eq
        (MoC.VG_prod (MoC.VG_Pexp E xK))
          (Ciphertext.Gdot (enc.enc pk (VS3.op G bT) tauT)
            (MoC.VG_prod (Vmap2 (fun Ci xi => MoC.VG_prod
              (MoC.VG_Pexp Ci (VF_scale aT xi))) Cbar x))) in
    
    let eq4 := Gbool_eq (Vnth cB indexM)
      (PC h (Vhead hs) 0 0) in

    let eq5 := Ciphertext.Gbool_eq (Vnth E indexM) C in

    eq1 && eq2 && eq3 && eq4 && eq5.

  Definition simMap (s : St)(w : W)(c :F)(x : X)(r : R)
     : TE :=
    
    (* Unpack statment *)
    let '(pk, h, hs, Cbar, C, cA, G) := s in

    (* Unpack witness *)
    let A := w.1.1 in
    let p := w.2 in

    (* Unpack random coins *)
     let '(a0, r0, (b0, b1), (s0, s1), (tau0, tau1)) := r in

    let b   := (Vapp b0 (Vcons 0 b1)) in
    let s  :=  (Vapp s0 (Vcons 0 s1))  in
    let tau := (Vapp tau0 (Vcons p tau1)) in

    let xBar := (VandermondeCol (1+m) c) in
    let xK := VandermondeCol (m+m) c in

    (* aBar = a0 + A xBar , since we tranpose both A and xBar *)
    let aT := Vhead (FMatrix.mat_mult [xBar] (Vcons a0 A)) in
    let rT := VF_inProd (Vcons r0 w.1.2) xBar in
    let bT := (VF_inProd b xK) in
    let sT := (VF_inProd s xK) in
    let tauT := MoR.VF_sum (Vmap2 MVS.op3 tau xK) in

    let bs := EkGeneratorsRawM x.1.2 (Vcons a0 A) b in
    let taus := EkGeneratorsRawR x.2 (Vcons a0 A) tau in
    let ss := VF_add s (VF_scale b (Vhead x.1.1)) in

    ((aT, rT, bT, sT, tauT),
      ((Vtail (Vbreak bs).1, Vtail (Vbreak bs).2), (Vtail (Vbreak ss).1, Vtail (Vbreak ss).2),
         (Vtail (Vbreak taus).1, Vtail (Vbreak taus).2))).

  Definition simMapInv (s : St)(w : W)(c :F)(x : X)(t : TE)
     : R :=
    
    (* Unpack statment *)
    let '(pk, h, hs, Cbar, C, cA, G) := s in

    (* Unpack witness *)
    let A := w.1.1 in

    (* Unpack response coins *)
    let '((aT, rT, bT, sT,tauT),((cB0, cB1), (s0, s1), (E1, E2))) := t in

    let xBar := (VandermondeCol (1+m) c) in
    let xK := (VandermondeCol (m+m) c) in

    let a0 := VF_sub aT (Vhead (FMatrix.mat_mult [(Vtail xBar)] A)) in

    let p := Vhead (Vbreak (EkGeneratorsRawR x.2 (Vcons a0 A)
      (Vapp (MoR.VF_zero m) (Vcons w.2 (MoR.VF_zero (S M.N)))))).2 in
    let b0 := Vhead (Vbreak (EkGeneratorsRawM x.1.2 (Vcons a0 A)
      (Vapp (VF_zero m) (Vcons 0 (VF_zero (S M.N)))))).2 in
    let s2  := 0 in


    let bb := VF_sub (Vapp cB0 (Vcons b0 cB1))
      (Vtail (EkGeneratorsRawM x.1.2 (Vcons a0 A) (VF_zero (m+m))))  in
    let ss := VF_sub (Vapp s0 (Vcons s2 s1)) (VF_scale bb (Vhead x.1.1)) in
    let taus := MoR.VF_sub (Vapp E1 (Vcons p E2))
      (Vtail (EkGeneratorsRawR x.2 (Vcons a0 A) (MoR.VF_zero (m+m)))) in

    let r0 := rT - (VF_inProd w.1.2 (Vtail xBar))  in
    let b := bT - (VF_inProd bb (Vtail xK))in
    let s := sT - (VF_inProd ss (Vtail xK)) in
    let tau := Ring.Fsub tauT (MoR.VF_sum ((Vmap2 MVS.op3 taus) (Vtail xK))) in

    (* a0 r0 b s tau *)
    (* (VF n)*F*((VF m)*(VF (m-1)))
      *((VF m)*(VF (m-1)))*((vector Ring.F m)*(vector Ring.F (m-1))).*)
    (a0,r0,(Vcons b (Vbreak bb).1,Vtail(Vbreak bb).2),
      (Vcons s (Vbreak ss).1, Vtail (Vbreak ss).2),
      (Vcons tau (Vbreak taus).1, Vtail (Vbreak taus).2)).
 
  Definition simulator (s : St)(z : TE)(e : F) : (St*C*F*T) :=
    
    let '(pk, h, hs, Cbar, C, cA, G) := s in

    let '((aT, rT, bT, sT,tauT),((cB0, cB1), (s0, s1), (E1, E2))) := z in

    let cB := Vmap (op h) (Vapp s0 (Vcons 0 s1)) in

    let E := Vapp (Vmap2 (fun w v => enc.enc pk (VS3.op G w) v) cB0 E1)
      (Vcons C (Vmap2 (fun w v => enc.enc pk (VS3.op G w) v) cB1 E2)) in

    let x := rev (VandermondeCol m e)in
    let xBar := VandermondeCol (1+m) e in
    let xK := VandermondeCol (m+m) e  in

    let CA0 := EPC h hs aT rT o - VG_prod (VG_Pexp cA (Vtail xBar)) in
    let CB := PC h (Vhead hs) bT sT o - VG_prod (VG_Pexp cB (Vtail xK))  in
    let EK := Ciphertext.Gdot (Ciphertext.Gdot
                (enc.enc pk (VS3.op G bT) tauT)
                (MoC.VG_prod (Vmap2 (fun Ci xi => MoC.VG_prod
                (MoC.VG_Pexp Ci (VF_scale aT xi))) Cbar x)))
              (Ciphertext.Ginv (MoC.VG_prod (MoC.VG_Pexp E (Vtail xK)))) in



    (s,(CA0,Vcons CB cB,Vcons EK E),e,z.1).

  Definition M := Nat.mul 2 m.

  Definition extractor (s : vector T (2*m))
        (c : vector F (2*m)): W :=

    let sM1 := (Vbreak (Vcast s castingM4)).1 in

    let aT := FMatrix.mat_transpose (Vmap (fun s1 => s1.1.1.1.1) sM1) in
    let rT := (Vmap (fun s1 => s1.1.1.1.2) sM1) in
    let bT := Vmap (fun s1 => s1.1.1.2) s in
    let sT := Vmap (fun s1 => s1.1.2) s in
    let tauT := Vcast (Vmap (fun s1 => s1.2) s) castingM6 in
    let YM1 := FMatrix.mat_transpose (VandermondeInv (Vbreak (Vcast c castingM4)).1) in

    let Y2M :=
        VandermondeInv (Vcast c castingM6)  in

    (Vtail (FMatrix.mat_transpose (FMatrix.mat_mult aT YM1)),
      Vtail (Vhead (FMatrix.mat_mult [rT] YM1)),
       RF_inProd (Vnth Y2M indexM) tauT).
     
  Definition disjoint (c1 c2 : F) :=
    negb (Fbool_eq c1 c2).

  Lemma Ek_ck : forall (w11 : vector (VF n) m)(s111111 : enc.PK)
    (s1112 : vector (vector Ciphertext.G n) m)
    (w2 : Ring.F)(s2 : enc.M)(r1111 : VF n)(r1122 : VF (S M.N))
    (r1121 : VF m)(r22 : vector Ring.F (S M.N))
    (r21 : vector Ring.F m)(c : F),
    MoC.VG_prod
  (MoC.VG_Pexp
     (EkGenerators s111111 s2 s1112
        (Vcons r1111 w11)
        (Vapp r21 (Vcons w2 r22))
        (Vapp r1121 (Vcons 0 r1122))
        (VF_one (m + m))) (VandermondeCol (m + m) c)) =
Ciphertext.Gdot
  (enc.enc s111111
     (VS3.op s2
        (VF_inProd (Vapp r1121 (Vcons 0 r1122))
         (VandermondeCol (m+m) c)))
     (MoR.VF_sum
        (Vmap2 MVS.op3 (Vapp r21 (Vcons w2 r22)) (VandermondeCol (m+m) c))))
  (MoC.VG_prod
     (Vmap2
        (fun (Ci : MoC.VG n) (xi : F) =>
         MoC.VG_prod
           (MoC.VG_Pexp Ci
              (VF_scale
                 (Vhead
                    (FMatrix.mat_mult
                       [VandermondeCol (1 + m) c]
                       (Vcons r1111 w11))) xi)))
        s1112 (rev (VandermondeCol m c)))).
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.
    pose Commitment.module_abegrp.
    intros. rewrite EkGeneratorsPexp. rewrite EkGeneratorsProd.
    apply eqImplProd. split.
    apply EncEq. apply ALVS3.scaleEq.
    rewrite InProd_Sum. unfold VF_mult. apply Vfold_left_eq.
    apply f_equal2; auto. trivial.
    apply Vfold_left_eq. apply Veq_nth. intros.
    do 2 rewrite Vnth_map2. rewrite Vbuild_nth.
    rewrite MoC.VG_prod_VG_Pexp. apply Vfold_left_eq.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    apply ALVS1.scaleEq. rewrite Vnth_map. rewrite Vfold_left_VF_add.
    rewrite Vhead_nth. rewrite FMatrix.mat_mult_elem.
    assert (forall (a b : VF (1+m)),
      FMatrix.VA.dot_product a b = VF_inProd a b). intros.
      unfold FMatrix.VA.dot_product. rewrite InProd_Sum.
      rewrite Vfold_left_Fadd_eq. trivial.
    rewrite H. rewrite InProd_Sum. rewrite VF_sum_scale.
    (* Trying to simply *)
    apply Vfold_left_eq. apply Veq_nth. intros. do 2 rewrite Vnth_map.
    do 2 rewrite Vnth_map2. rewrite Vnth_map. rewrite <- FMatrix.get_elem_swap.
    unfold FMatrix.get_row. assert (forall a b c d,
      b = c * d -> a * b = c * a * d). intros. rewrite H0.
    ring; auto. apply H0. rewrite Vnth_sub. rewrite Vnth_map2.
    do 2 rewrite Vnth_const. do 2 rewrite Vbuild_nth.
    do 2 rewrite Vbuild_nth.
    rewrite VF_prod_const. destruct vs_field, F_R. rewrite Rmul_1_l.
    apply VG_prod_const_index. unfold support.m, m. lia.
  Qed.

  Lemma Sim_com : forall (s : St)(r : R)(c : F)(w : W)(x : X),
    simMapHelp s x ->
    V1 (P1 ((P0 s r w), c) r w) = true  ->
    (P0 s r w).2 = (simulator s (simMap s w c x r) c).1.1.2.
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.
    pose Commitment.module_abegrp. intros. unfold P0. unfold simulator.
    unfold simMap. destruct s, p, p, p, p, p.
    destruct r, p0, p0, p0. destruct w, p0. destruct p2, p3, p1. remember Vbreak as d.
    do 7 rewrite Prod_right_replace. do 5 rewrite Prod_left_replace.
    unfold V1, P1, P0 in H0. do 14 rewrite Prod_right_replace in H0.
    do 10 rewrite Prod_left_replace in H0.
    apply andb_true_iff in H0. destruct H0. apply andb_true_iff in H0. destruct H0.
    apply andb_true_iff in H0. destruct H0.  apply andb_true_iff in H0. destruct H0.
    destruct vs_field. destruct F_R. apply bool_eq_corr in H0.
    apply bool_eq_corr in H4. apply bool_eq_corr in H2.
     apply injective_projections. apply injective_projections.
    (* CA *)
    + do 2 rewrite Prod_left_replace. rewrite <- H0. rewrite (VSn_eq (VandermondeCol (1 + m) c)).
    unfold VG_Pexp. rewrite Vcons_map2. rewrite VG_prod_Vcons. rewrite <- VSn_eq.
    rewrite comm. rewrite dot_assoc. rewrite <- inv_left. rewrite one_left.
    rewrite Vbuild_head. cbn. rewrite mod_id. trivial.
    (* CB *)
    + do 2 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace. rewrite <- H4.
    (* First thing we need to do is to simplify the vectors *)
    assert (0 = Vhead (d F m (S (S M.N)) (VF_add (Vapp v3 (Vcons 0 v4))
    (VF_scale (Vapp v5 (Vcons 0 v6)) (Vhead x.1.1)))).2).
    rewrite Vhead_nth. rewrite Heqd. rewrite Vnth_vbreak_2. lia.  intros. unfold VF_add,
    FMatrix.VA.vector_plus. rewrite Vnth_map2. rewrite Vnth_map.
    unfold m in *. do 2 rewrite (Vnth_app). destruct (le_gt_dec (S (S M.N)) (0 + S (S M.N))).
    do 2 rewrite Vnth_cons. destruct (lt_ge_dec 0 (0 + S M.N - S M.N)). assert (False). lia. contradiction.
    destruct (lt_ge_dec 0 (0 + S (S M.N) - S (S M.N))). assert (False). lia. contradiction.
    unfold FSemiRingT.Aplus. field. assert (False). lia. contradiction.
    (* Now we can simply the vectors *)
    remember (d F m (S (S M.N)) (VF_add (Vapp v3 (Vcons 0 v4))
    (VF_scale (Vapp v5 (Vcons 0 v6)) (Vhead x.1.1)))). rewrite H5. rewrite <- VSn_eq.
    rewrite <- Vapp_Vtail2. unfold VG_Pexp. rewrite <- Vtail_map. rewrite Vtail_map2.
    assert ((Vhead v0) = g0 ^ (Vhead x.1.1)). destruct H. rewrite H. rewrite Vhead_map. auto.
    pose(comPCfromOp H6). rewrite <- H5. rewrite Heqp0.
    rewrite Heqd. rewrite <- Vbreak_eq_app. rewrite <- e. unfold comPC.
    rewrite VG_prod_cancel. (* Most cleaning is now done *)
    rewrite Vhead_map2. replace (Vhead (VandermondeCol (m + m) c)) with 1.
    rewrite mod_id. rewrite <- VSn_eq. trivial. unfold VandermondeCol.
    rewrite Vbuild_head. unfold VF_prod. rewrite Vfold_left_nil. trivial.
    (* Ek *)
    + do 2 rewrite Prod_right_replace.
    apply bool_eq_corr in H1. rewrite <- H1. rewrite Vtail_map2. rewrite Vapp_Vtail.
    destruct H. rewrite <- (EkGeneratorsRaw_conv p m0 x.1.2 x.2); auto.
    rewrite indexMhead. rewrite Vtail_map2. rewrite Heqd. rewrite Vbreak_vmap2_2.
    rewrite <- VSn_eq. rewrite Vbreak_vmap2_1. rewrite <- Vbreak_eq_app.
    apply bool_eq_corr in H3. rewrite <- H3.
    rewrite <- (EkGeneratorsRaw_conv p m0 x.1.2 x.2); auto.
    unfold MoC.VG_Pexp. rewrite Vtail_map2. rewrite MoC.VG_prod_cancel.
    rewrite Vhead_map2. replace (Vhead (VandermondeCol (m + m) c)) with 1.
    rewrite VS1.mod_id. rewrite <- VSn_eq. trivial. rewrite Vbuild_head. cbn.
    trivial.
  Qed.
  
  Lemma pres_p0 : forall (s : St)(r : R)(w : W), (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. unfold P0. destruct s, p, p, p, p, p.
    destruct r, p0, p0, p0. trivial.
  Qed.

  Lemma pres_p1 : forall (sce : St*C*F)(r : R)(w : W),
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Proof.
    intros. unfold P1. destruct sce, p. destruct s, p, p, p, p, p.
    destruct r, p0, p0, p0. trivial.
  Qed.

  Lemma pres_sim : forall (s: St)(t : TE)(e : F),
      s = (simulator s t e).1.1.1.
  Proof.
    intros. unfold simulator. destruct s, p, p, p, p, p.
    destruct t, p0, p0, p0, p0, p1, p0, p0, p1, p2. trivial.
  Qed.

  Lemma chal_sim : forall (s: St)(t : TE)(e : F),
    e = (simulator s t e).1.2.
  Proof.
    intros. unfold simulator. destruct s, p, p, p, p, p.
    destruct t, p0, p0, p0, p0, p1, p0, p0, p1, p2.  trivial.
  Qed.

  (** Properties *)
  Lemma correctness : forall (s :St)(w:W)(r:R)(c: F),
    Rel s w ->
    V1 (P1 ((P0 s r w), c) r w) = true.
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.
    pose Commitment.module_abegrp.
     intros. unfold V1. unfold P1.
    unfold P0. unfold Rel in H.  destruct s, p, p, p, p, p.
    destruct r, p0, p0, p0. destruct w, p0. apply andb_true_iff in H.
    destruct H. apply VGeq in H. apply bool_eq_corr in H0.
    (* End verbose simpl *)
    apply andb_true_iff. split. apply andb_true_iff. split.
    apply andb_true_iff. split.  apply andb_true_iff. split.
    - apply bool_eq_corr.
    rewrite H. rewrite comEPCVcons.  unfold VG_Pexp.
    rewrite comEPCDis. unfold VG_prod. rewrite <- EPCMultExt.
    apply EPC_m_r_eq. apply Veq_nth. intros.
    rewrite Vfold_left_VF_add. rewrite Vhead_nth.
    rewrite FMatrix.mat_mult_elem. unfold FMatrix.VA.dot_product.
    rewrite Vfold_left_Fadd_eq. apply Vfold_left_eq.
    apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vnth_map. rewrite Vnth_map2.
    rewrite Vnth_map. rewrite <- FMatrix.get_elem_swap.
    unfold FMatrix.get_row. rewrite Vnth0.
    pose Field.vs_field. unfold FSemiRingT.Amult.
    destruct f1. destruct F_R. apply Rmul_comm.
    unfold VF_inProd, FMatrix.VA.dot_product.
    rewrite Vfold_left_Fadd_eq. trivial.
    (* Completeness 2/5 *)
    - intros. apply bool_eq_corr.
    unfold VG_Pexp. rewrite comPCDis.
    unfold VG_prod. rewrite <- PCMultExt.
    apply PC_m_r_eq. unfold VF_inProd, FMatrix.VA.dot_product.
    do 5 rewrite Prod_right_replace. rewrite Vfold_left_Fadd_eq. trivial.
     do 5 rewrite Prod_right_replace.  rewrite InProd_Sum. unfold VF_sum. trivial.
    (* Completeness 3/5 *)
    - intros. apply bool_eq_corr. apply Ek_ck.
    
    (* Completeness 4/5 *)
    - apply bool_eq_corr. cbn. rewrite Vnth_map2.
      do 4 rewrite Vnth_tail. apply PC_m_r_eq.
    pose (Vnth_app_cons p3.1 p3.2).
    rewrite e. trivial.
    pose (Vnth_app_cons p2.1 p2.2).
    rewrite e. trivial.
    (* Completeness 5/5 *)
    - apply bool_eq_corr. do 2 rewrite Vnth_map2.
    rewrite Prod_left_replace.
    rewrite H0. apply eqImplProd. split.
    do 2 rewrite Vnth_app_cons.
    rewrite VS3.mod_ann. trivial. rewrite Vnth_map2.
    rewrite Vnth_app_left. rewrite Vnth_const. rewrite VS1.mod_id.
    do 2 rewrite Vbuild_nth. assert (m = Nat.add 1 (Nat.sub
    (Nat.sub m (m - m)) 1)). unfold m. lia.
    rewrite (MoC.VG_prod_cast H1). rewrite MoC.VG_prod_rev.
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vbuild_nth.
    rewrite Vnth_cast. do 2 rewrite Vnth_map2. apply Vfold_left_eq.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    apply ALVS1.scaleEqFull. apply Veq_nth2. rewrite Vnth_sub.
    rewrite Vbuild_nth. apply Vnth_eq. rewrite <- H1. unfold support.m, m.  lia.
    rewrite Vapp_tail. apply Veq_nth2. rewrite Vnth_sub. rewrite Vbuild_nth.
    apply Vnth_eq. rewrite <- H1. lia.
  Qed.

   Definition allDifferent (e : vector F M) := PairwisePredicate disjoint e.
  
  Lemma special_soundness : forall (s : St)(c : C)(e : vector F M)(t : vector T M),
    (* Forall e it is disjoint from all e *)
    allDifferent e  ->
    bVforall2 (fun e1 t1 => V1 (s, c, e1, t1)) e t ->
    Rel s (extractor t e) = true \/ fail_event s c e.
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.
    pose Commitment.module_abegrp. intros. unfold Rel, extractor, fail_event.
    unfold V1 in H0. destruct s, p, p, p, p, p. destruct c, p0.
    apply bVforall2Split in H0. destruct H0.
    apply bVforall2Split in H0. destruct H0. simpl in H1. simpl in H2.
    apply bVforall2Split in H0. destruct H0. apply bVforall2Split in H0.
    destruct H0. apply bVforall2Clear in H2. apply bool_eq_corr in H2.
    (* We need to prove Cb zero - Corollary 2 *)
    pose (Vmap (fun s1 => s1.1.2) t) as sT.
    pose (Vmap (fun s1 => s1.1.1.2) t) as bT.
    pose (FMatrix.mat_transpose (VandermondeInv e)) as Y2M.
    pose (castingM6). symmetry in e0.
    assert (Vcast v1 e0 = comPC g0 (Vhead v0)
     (Vhead (FMatrix.mat_mult [bT] Y2M)) (Vhead (FMatrix.mat_mult [sT] Y2M))).
    symmetry. rewrite <- VG_MF_exp_row_id. symmetry.
    pose (invVandermondeLeft H).  unfold M, m, support.m in *.
    rewrite <- e1.  rewrite <- VG_MF_exp_row_dist. apply Veq_nth. intros.
    assert (VG_MF_exp_row (Vcast v1 e0) (Vandermonde e) =
    Vmap (fun x => PC g0 (Vhead v0)
    x.1.1.2 x.1.2) t). apply Veq_nth. intros.
    apply (bVforall2_elim_nth ip0) in H4. apply bool_eq_corr in H4.
    assert (VG_prod (VG_Pexp v1
    (VandermondeCol (m+m) (Vnth e ip0))
    ) = Vnth (VG_MF_exp_row (Vcast v1 e0) (Vandermonde e))
    ip0). rewrite Vbuild_nth. apply (Vfold_left_eq_gen e0). apply Veq_nth.
    intros. rewrite Vnth_cast. do 2 rewrite Vnth_map2. apply f_equal2.
    simpl. rewrite Vnth_cast. simpl. trivial. rewrite Vnth_map.
    do 2 rewrite Vbuild_nth. simpl. trivial.
     rewrite <- H5. rewrite H4. simpl. rewrite Vnth_map. trivial.
    rewrite H5. rewrite Vnth_map2. rewrite Vbuild_nth. assert (Vmap
    (fun x => PC g0 (Vhead v0) x.1.1.2 x.1.2) t =
    comPC g0 (Vhead v0) (Vmap (fun x => x.1.1.2) t)
    (Vmap (fun x => x.1.2) t)). apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_map.
    trivial. rewrite H6. unfold VG_Pexp. rewrite comPCDis. unfold VG_prod.
    rewrite <- PCMultExt. apply PC_m_r_eq. rewrite Vhead_nth. rewrite FMatrix.mat_mult_elem.
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq. apply f_equal.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map.
    apply f_equal2; auto. unfold Y2M. pose FMatrix.mat_transpose_col_row.
    unfold FMatrix.get_row in e2. rewrite e2. rewrite Vnth_map. trivial.
    rewrite Vhead_nth. rewrite FMatrix.mat_mult_elem.
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq. apply f_equal.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map.
    apply f_equal2; auto. unfold Y2M. pose FMatrix.mat_transpose_col_row.
    unfold FMatrix.get_row in e2. rewrite e2. rewrite Vnth_map. trivial.
    assert (m < S (S (M.N + S (S (M.N + 0))))). unfold m. lia.
    assert (Vnth v1 indexM = PC g0 (Vhead v0)
      (VF_inProd bT (FMatrix.get_col Y2M H6))
      (VF_inProd sT (FMatrix.get_col Y2M H6))) as Col2. apply (Vcast_lr v1 e0 castingM5) in H5.
    rewrite H5. rewrite Vnth_cast. rewrite Vnth_map2. do 3 rewrite Vhead_nth.
    do 2 rewrite FMatrix.mat_mult_elem. simpl. assert (forall n (a b : VF n),
    FMatrix.VA.dot_product a b = VF_inProd a b). intros. unfold FMatrix.VA.dot_product.
    unfold VF_inProd, FMatrix.VA.dot_product. apply f_equal.
    trivial. do 2 rewrite H7. apply f_equal2. apply f_equal.
    apply Veq_nth. intros. do 2 rewrite Vnth_map. apply Vnth_eq. trivial.
    apply f_equal. apply Veq_nth. intros. do 2 rewrite Vnth_map. apply Vnth_eq. trivial.
    (* Prepping to prove lemma 1 *)
    assert (S (S (M.N + S (S (M.N + 0)))) = Nat.add (S (S (S M.N))) (S M.N)). lia.
     pose (Vbreak (Vcast e H7)) as chal.
    pose (Vbreak (Vcast t H7)) as resp.
    remember (FMatrix.mat_mult (VandermondeInv chal.1)
      (Vmap (fun x => x.1.1.1.1) resp.1)) as Aj.
     assert (MF_mult (Vandermonde e) (VandermondeInv e) =
      MF_id (S (S (M.N + (S (S (M.N + 0))))))).
     apply invVandermondeRight; auto. assert (MF_mult (Vandermonde chal.1)
    (VandermondeInv chal.1) = MF_id (S (S (S M.N)))).
     apply (PairwisePredicate_break (S (S (S M.N))) (S M.N) e disjoint H7) in H.
    apply invVandermondeRight; auto. assert (PairwisePredicate disjoint chal.1).
    apply (PairwisePredicate_break); auto.
    remember (Vhead (FMatrix.mat_mult [(Vmap (fun s1 => s1.1.1.1.2) resp.1)]
    (FMatrix.mat_transpose (VandermondeInv chal.1)))) as Rj.
    (* We want to prove Aj = Etractor *)
    assert ((extractor t e).1.1 = Vtail Aj).
    apply Veq_nth. intros. apply Veq_nth. intros.
    do 2 rewrite Vnth_tail. rewrite transpose_move_gen.
    do 2 rewrite FMatrix.mat_transpose_idem.
    rewrite HeqAj. do 2 rewrite FMatrix.mat_mult_elem.
    apply f_equal2. unfold FMatrix.get_row. unfold chal.
    apply Veq_nth3. trivial. apply f_equal. apply Veq_nth. intros.
    rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_vbreak_1. intros. do 2 rewrite Vnth_cast.
    apply Vnth_eq. lia.  apply Veq_nth. intros.
    do 4 rewrite Vnth_map. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_vbreak_1. intros. do 2 rewrite Vnth_cast.
    apply Veq_nth3; auto. apply f_equal. apply f_equal.
    apply f_equal. apply f_equal. apply Vnth_eq. lia.
    (* Same with Rj *)
    assert ((extractor t e).1.2 = Vtail Rj). apply Veq_nth.
    intros. do 2 rewrite Vnth_tail. rewrite HeqRj. do 2 rewrite Vhead_nth.
    do 2 rewrite FMatrix.mat_mult_elem. apply f_equal2; auto. unfold FMatrix.get_row.
    apply Veq_nth3; auto. apply Vcons_eq_intro; auto.
    apply Veq_nth. intros. do 2 rewrite Vnth_map. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_vbreak_1. intros. do 2 rewrite Vnth_cast.
    apply f_equal. apply f_equal. apply f_equal. apply f_equal.
    apply Vnth_eq. lia. apply Veq_nth. intros.
    do 2 rewrite Vnth_map. do 2 rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_elem, FMatrix.get_row. apply Veq_nth4. apply Veq_nth4.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_vbreak_1. intros. do 2 rewrite Vnth_cast.
    apply Veq_nth3; auto.
    (* Prove commitment - Lemma 1 *)
    assert (VG_eq (Vcons g1 v) (comEPC g0 v0 Aj Rj) = true) as Lemma1.
    apply (bVforall2_break (S (S (S M.N))) (S M.N) e t (fun (a' : F) (b' : T) =>
        Gbool_eq
          (VG_prod
             (VG_Pexp
                (Vcons g1 v)
                (VandermondeCol (1+m) a')))
          (EPC g0 v0 b'.1.1.1.1 b'.1.1.1.2)) H7) in H0. destruct H0.
    apply VGeq.
    symmetry. rewrite <- VG_MF_exp_row_id. symmetry. unfold m. rewrite <- H9.
    assert (MF_mult (Vandermonde chal.1) (VandermondeInv chal.1) =
              MF_mult (VandermondeInv chal.1) (Vandermonde chal.1)). rewrite invVandermondeLeft.
    rewrite invVandermondeRight. trivial. trivial. trivial.
    rewrite H14. rewrite <- VG_MF_exp_row_dist.
    assert (VG_MF_exp_row (Vcons g1 v) (Vandermonde chal.1)
      = comEPC g0 v0 (Vmap (fun x =>
        x.1.1.1.1) resp.1) (Vmap (fun x =>  x.1.1.1.2) resp.1)).
    apply Veq_nth. intros. rewrite Vnth_map2. rewrite Vbuild_nth.
    apply (bVforall2_elim_nth ip chal.1 resp.1) in H0.
    apply bool_eq_corr in H0. rewrite Vnth_map. unfold m in H0.
    rewrite H0. do 2 rewrite Vnth_map. trivial. rewrite H15.
    unfold VG_MF_exp_row. apply Veq_nth. intros. rewrite Vbuild_nth.
    unfold VG_Pexp. rewrite comEPCDis. unfold VG_prod.
    rewrite <- EPCMultExt. rewrite Vnth_map2. rewrite HeqAj.
    rewrite HeqRj. destruct module_ring. apply f_equal2. apply Veq_nth.
    intros. rewrite FMatrix.mat_mult_elem. rewrite Vfold_left_VF_add.
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq.
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_map.
    do 2 rewrite Vnth_map2. do 4 rewrite Vnth_map. rewrite Rmul_comm.
    apply f_equal2. unfold FMatrix.get_row. trivial. trivial.
    rewrite Vhead_nth. rewrite FMatrix.mat_mult_elem. unfold FMatrix.VA.dot_product.
    rewrite Vfold_left_Fadd_eq. apply Vfold_left_eq. apply Veq_nth. intros.
    do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map.
    apply f_equal2. trivial. rewrite FMatrix.mat_build_nth.
    unfold FMatrix.get_elem. unfold FMatrix.get_row. trivial.

    (* Case both of the cases where the commitment breaks to be dealt with later *)
    case_eq (Fbool_eq (VF_inProd bT (FMatrix.get_col Y2M H6)) 0).
    case_eq (bVforall2 (VF_beq (n:= n))
       (Vmap (fun x => x.1.1.1.1) t)
      (Vbuild (fun i (ip : i < S (S (M.N + S (S (M.N + 0))))) =>
        Vhead (FMatrix.mat_mult [(VandermondeCol (S (S (S M.N)))
        (Vnth e ip))] Aj)))).
    
    + intros.  left. apply andb_true_iff. split.
    (* We are about to split the two parts of the relationship
    but before we need to prep some stuff for the ciphertexts *)
    ++ apply VGeq in Lemma1. apply VGeq. apply Vcons_eq_elim_gen in Lemma1.
    destruct Lemma1. rewrite H16. unfold extractor in *.
    rewrite Prod_right_replace in H12. rewrite Prod_left_replace in H11.
    rewrite H12. rewrite H11. trivial.
    (* Prove ciphertexts - begin lemma 2 *)
    ++ clear H0.
    apply bool_eq_corr. apply bVforall2Clear in H1. apply bool_eq_corr in H1.
    rewrite <- H1.
    (* Prove ciphertexts - begin properites over all Es (Lemma 2) *)
    assert (Nat.add m m = M). unfold M, m. lia.
    assert (Vcast t1 H0 = Vmap
        (fun q => MoC.VG_prod (MoC.VG_Pexp (Vmap2 (fun x y =>
           Ciphertext.Gdot (enc.enc p (VS3.op m0 y.1.1.2) y.2)
            (MoC.VG_prod (Vmap2 (fun (Ci : MoC.VG n) (xi : F) =>
            MoC.VG_prod (MoC.VG_Pexp Ci (VF_scale y.1.1.1.1 xi)))
            t0 (rev (VandermondeCol (m) x))))) e t) q))
    (VandermondeInv e)) as Lemma2. clear H2 H5 Col2 HeqRj H13.
    +++ symmetry. rewrite <- (MoC.VG_MF_exp_row_id). symmetry.
    pose (invVandermondeRight H). rewrite <- e1. assert (MF_mult (Vandermonde e) (VandermondeInv e) =
                                                           MF_mult (VandermondeInv e) (Vandermonde e)). rewrite invVandermondeLeft.
    rewrite invVandermondeRight. trivial. trivial. trivial.
    rewrite H2. rewrite <- MoC.VG_MF_exp_row_dist. apply Veq_nth.
    intros. rewrite Vbuild_nth. rewrite Vnth_map.
    (* Prove ciphertext - begin inner most *)
    assert (MoC.VG_MF_exp_row (Vcast t1 H0) (Vandermonde e) =
    Vmap2 (fun x y => Ciphertext.Gdot (enc.enc p
     (VS3.op m0 y.1.1.2) y.2) (MoC.VG_prod (Vmap2
     (fun (Ci : MoC.VG n) (xi : F) => MoC.VG_prod (MoC.VG_Pexp Ci
     (VF_scale y.1.1.1.1 xi))) t0 (rev (VandermondeCol m x))))) e t).
    apply Veq_nth. intros. rewrite Vbuild_nth. apply (bVforall2_elim_nth ip0) in H3.
    apply bool_eq_corr in H3. assert (MoC.VG_prod (MoC.VG_Pexp t1
    (VandermondeCol (m+m) (Vnth e ip0))) = MoC.VG_prod
  (MoC.VG_Pexp (Vcast t1 H0) (Vnth (Vandermonde e) ip0))).
    apply (Vfold_left_eq_gen H0). apply Veq_nth. intros.
    rewrite Vnth_cast. do 2 rewrite Vnth_map2. apply f_equal2.
    simpl. rewrite Vnth_cast. trivial.
    rewrite Vnth_map. do 2 rewrite Vbuild_nth. simpl. trivial.
    rewrite H5 in H3. rewrite H3. rewrite Vnth_map2. apply eqImplProd.
    split. simpl. trivial. apply Vfold_left_eq. apply f_equal2; auto.
    (* End inner most *)
    rewrite H5. trivial.
    (* Lemma 2 is now proved *)
    +++ assert (M = Nat.add m m). lia. apply (Vcast_lr t1 H0 H15) in Lemma2.
    rewrite Lemma2. rewrite Vnth_cast.
    rewrite Vnth_map. rewrite MoC.VG_mult_Vmap2. rewrite MoC.VG_Pexp_mult.
    rewrite MoC.VG_Prod_mult_dist. apply eqImplProd. split.
    (* We are finishing up the consquence of Lemma 2 *)
    (* Proving enc *)
    ++++ assert (Vmap2 (fun (_ : F) (y : VF n * F * F * F * Ring.F) =>
    enc.enc p (VS3.op m0 y.1.1.2) y.2) e t =
    Vmap2 (fun x y => enc.enc p (VS3.op m0 x) y)
    (Vmap (fun x => x.1.1.2) t) (Vmap (fun x => x.2) t)). apply Veq_nth.
    intros. do 2 rewrite Vnth_map2. do 2 rewrite Vnth_map. trivial.
    rewrite H16. rewrite pexpOfCiphertext. rewrite prodOfCiphertext.
    apply EncEq. apply F_bool_eq_corr in H14. assert (VF_sum
     (VF_mult (Vmap (fun x : VF n * F * F * F * Ring.F => x.1.1.2)
     t) (Vnth (VandermondeInv e) (Vnth_cast_aux H15 indexM))) =
    VF_inProd bT (FMatrix.get_col Y2M H6)). rewrite InProd_Sum.
    apply f_equal. unfold VF_mult. apply f_equal2. auto.
    unfold Y2M. rewrite FMatrix.mat_transpose_row_col.
    unfold FMatrix.get_row. apply f_equal. apply le_unique.
    rewrite H17. rewrite H14.
    rewrite VS3.mod_ann. trivial. rewrite Prod_right_replace.  unfold RF_inProd, MoR.VF_sum.
    apply (Vfold_left_eq_gen castingM6).  apply Veq_nth. intros. rewrite Vnth_cast.
    do 2 rewrite Vnth_map2. apply f_equal2. rewrite Vnth_cast. trivial. apply (Veq_nth_mat castingM6); trivial.
    (* We have discharged the encryption part of lemma 2 *)
    ++++ assert (Vmap2 (fun (x : F) (y : VF n * F * F * F * Ring.F) =>
    MoC.VG_prod (Vmap2 (fun (Ci : MoC.VG n) (xi : F) => MoC.VG_prod
    (MoC.VG_Pexp Ci (VF_scale y.1.1.1.1 xi))) t0 (rev
    (VandermondeCol m x)))) e t =
    Vmap2 (fun (x : F) (y : VF n) =>
    MoC.VG_prod (Vmap2 (fun (Ci : MoC.VG n) (xi : F) => MoC.VG_prod
    (MoC.VG_Pexp Ci (VF_scale y xi))) t0 (rev (Vcast
    (VandermondeCol (1 + (m - 1)) x)  castingM0)))) e (Vmap
    (fun x => x.1.1.1.1) t)). apply Veq_nth. intros.
    do 2 rewrite Vnth_map2. rewrite Vnth_map. apply f_equal.
    apply Veq_nth. intros. do 2 rewrite Vnth_map2. apply f_equal.
    apply f_equal2; auto.  apply f_equal. do 3 rewrite Vbuild_nth.
    rewrite Vnth_cast. rewrite Vbuild_nth. unfold m, support.m. trivial.
    rewrite H16.
    (* We will now prove Corollary 1 *)
    assert (Vmap2 (fun (x : F) (y : VF n) => MoC.VG_prod
     (Vmap2 (fun (Ci : MoC.VG n) (xi : F) =>
         MoC.VG_prod (MoC.VG_Pexp Ci (VF_scale y xi))) t0
        (rev (Vcast (VandermondeCol (1 + (m - 1)) x)
        castingM0)))) e (Vmap (fun x : VF n * F * F * F * Ring.F =>
        x.1.1.1.1) t) =
     Vcast (Vmap (fun (x : VF (m+m))  => MoC.VG_prod
     (MoC.VG_Pexp (WeirdCs t0 Aj) x))
     (Vandermonde (Vcast e castingM5))) castingM7) as Col1.
    +++++
    assert ((Vmap (fun x : VF n * F * F * F * Ring.F => x.1.1.1.1) t) =
    (Vbuild (fun (i : nat) (ip : i < S (S (M.N + S (S (M.N + 0))))) =>
    Vhead (FMatrix.mat_mult [VandermondeCol (S (S (S M.N))) (Vnth e ip)] Aj)))).
    apply Veq_nth. intros. apply (bVforall2_elim_nth ip) in H13.
    apply VF_beq_true in H13. rewrite H13. trivial.
    rewrite H17. apply Veq_nth. intros. rewrite Vnth_map2.
    rewrite Vbuild_nth. rewrite Vnth_cast. rewrite Vnth_map.
    rewrite Vnth_map. rewrite Vnth_cast. assert (Vnth e
    (Vnth_cast_aux castingM5 (Vnth_cast_aux castingM7 ip)) =
    Vnth e ip). apply Vnth_eq. trivial. rewrite H18.
    assert (Vcast (VandermondeCol (1 + (m - 1)) (Vnth e ip)) castingM0 =
    VandermondeCol m (Vnth e ip)). apply Veq_nth. intros.
    rewrite Vnth_cast. do 2 rewrite Vbuild_nth. trivial.
    rewrite H19. apply WeirdCs_Expand.
    (* Resuming Main proof *)
    (* Proving product *)
    +++++ rewrite Col1. rewrite MoC.VG_prod_pexp_fixed_base.
    (* Prove fact about index *)
    assert ((Vhead
        (FMatrix.mat_mult
           [Vcast
              (Vnth (VandermondeInv e)
                 (Vnth_cast_aux H15 indexM)) H15]
           (Vandermonde (Vcast e castingM5)))) =
    VF_n_id indexM).
    assert (Vcast (Vnth (MF_mult (VandermondeInv e)
        (Vandermonde e)) (Vnth_cast_aux H15 indexM)) H15  = Vnth
    (MF_id (m+m)) indexM). rewrite invVandermondeLeft. do 2 rewrite Vbuild_nth. apply Veq_nth.
    intros. rewrite Vnth_cast. destruct (Nat.eq_dec m i).
    subst. do 2 rewrite Vnth_replace. trivial. rewrite Vnth_replace_neq; auto.
    rewrite Vnth_replace_neq; auto. do 2 rewrite Vnth_const. trivial. trivial.
    assert (VF_n_id indexM =  Vnth (MF_id (m + m)) indexM).
    apply Veq_nth. intros. rewrite Vbuild_nth.
    rewrite Vbuild_nth in H17. unfold VF_n_id. trivial.
    rewrite H18. rewrite <- H17. rewrite Fmatrix_mult_vnth.
    apply Veq_nth. intros. symmetry. rewrite Vnth_cast. do 2 rewrite Vhead_nth.
    do 2 rewrite FMatrix.mat_build_nth.
    unfold FMatrix.VA.dot_product.
    do 2 rewrite Vfold_left_Fadd_eq. apply (Vfold_left_eq_cast H15).
    apply Veq_nth. intros. rewrite Vnth_cast. do 2 rewrite Vnth_map2.
    apply f_equal2. unfold FMatrix.get_row. symmetry. rewrite Vnth_cast.
    apply Veq_nth3. trivial. rewrite Vnth0. trivial.
    do 4 rewrite Vnth_map.  do 2 rewrite Vbuild_nth. apply Vfold_left_eq.
    apply Vtail_equal. rewrite Vnth_cast. apply Vnth_eq. trivial.
    (* Back to mainline *)
    rewrite H17. rewrite MoC.VG_n_exp.
    rewrite Vnth_app. destruct (le_gt_dec m support.m). do 2 rewrite Vbuild_nth.
    assert (Nat.add 1 (Nat.sub (Nat.sub m (m - m)) 1) = m). replace (Nat.sub m m) with 0%nat.
    unfold m. lia. lia.
    rewrite (MoC.VG_prod_cast H18). apply f_equal.
    apply Veq_nth. intros. rewrite Vnth_cast. do 2 rewrite Vnth_map2.
    do 2 rewrite Vnth_sub. apply f_equal. apply f_equal2.
    apply Vnth_eq. lia. apply Veq_nth. intros. rewrite HeqAj.
    rewrite FMatrix.mat_mult_elem. unfold extractor.
    rewrite Vnth_tail. rewrite transpose_move_gen.
    rewrite FMatrix.mat_mult_elem. do 2 rewrite FMatrix.mat_transpose_idem.
    apply f_equal2. unfold FMatrix.get_row.  apply Veq_nth3. unfold m, support.m. lia.
    apply f_equal. apply Veq_nth. intros. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_vbreak_1. intros. do 2 rewrite Vnth_cast.
    apply Vnth_eq. trivial.   apply Veq_nth. intros.
    do 4 rewrite Vnth_map. rewrite Vnth_vbreak_1. lia. intros.
    rewrite Vnth_vbreak_1. intros. do 2 rewrite Vnth_cast.
    apply Veq_nth3; auto. apply f_equal. apply f_equal.
    apply f_equal. apply f_equal. apply Vnth_eq. lia.
    unfold m, support.m in *. assert False. lia. contradiction.


    (* The case where the commitments are broken (1/2) *)
    + intros. right. right. apply bVforall_false2 in H13.
    destruct H13. destruct H13. apply VF_beq_false in H13.
    exists (VG_prod (VG_Pexp (Vcons g1 v) (VandermondeCol (S m) (Vnth e x0)))).
    rewrite Vnth_map in H13. rewrite Vbuild_nth in H13.
    exists ((Vnth t x0).1.1.1.1). exists (Vhead
    (FMatrix.mat_mult [VandermondeCol (S (S (S M.N))) (Vnth e x0)] Aj)).
    exists (Vnth t x0).1.1.1.2. exists (Vfold_left Fadd 0
    (Vmap2 Fmul Rj (VandermondeCol (S m) (Vnth e x0)))). unfold relComEPC. split; auto.
    split. apply (bVforall2_elim_nth x0) in H0. apply bool_eq_corr in H0.
    rewrite H0. simpl. trivial. apply VGeq in Lemma1. rewrite Lemma1.
    unfold VG_Pexp, VG_prod. rewrite comEPCDis. rewrite <- EPCMultExt.
    apply f_equal2. apply Veq_nth. intros. rewrite Vhead_nth.
    rewrite FMatrix.mat_mult_elem. rewrite Vfold_left_VF_add.
    unfold FMatrix.VA.dot_product. rewrite Vfold_left_Fadd_eq.
    apply Vfold_left_eq. apply Veq_nth. intros. rewrite Vnth_map.
    do 2 rewrite Vnth_map2. rewrite Vnth_map. destruct module_ring.
    rewrite Rmul_comm. apply f_equal2. unfold FMatrix.get_row.
    apply Veq_nth3; auto. rewrite Vnth_map. trivial. trivial.

    
    (* The case where the commitments are broken (2/2) *)
    + intros. right. left. exists (Vnth v1 indexM).
    apply F_bool_neq_corr in H13. exists (VF_inProd bT (FMatrix.get_col Y2M H6)).
    exists (VF_inProd sT (FMatrix.get_col Y2M H6)). unfold relComPC; auto.
  Qed.

  Lemma honest_verifier_ZK :
    forall (s : St)(w : W)(e : F)(x : X)(r : R)(t : TE),
      simMapHelp s x ->
      Rel s w ->
      (P1 ((P0 s r w), e) r w) =
      simulator s (simMap s w e x r) e /\
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.
  Proof.
    
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.
    pose Commitment.module_abegrp.
    intros. unfold Rel, P1, P0, simulator, simMap, simMapInv in *.
    destruct s, p, p, p, p, p. destruct r, p0, p0, p0. destruct w, p0, p2, p3, p1.
    split. intros.
    + (* First we need to prove the simulator produces same proof *)
    apply injective_projections. - apply injective_projections.
    -- apply injective_projections. --- simpl. trivial.
    (* Commitments *)
    --- remember Vbreak as d. do 9 rewrite Prod_right_replace.
    do 5 rewrite Prod_left_replace. rewrite Heqd.
    assert (V1 (P1 (P0 (p, g0, v0, t0, g, v, m0) (v1, f, (v5, v6), (v3, v4), (t2, t3))
    (t1, v2, f0), e) (v1, f, (v5, v6), (v3, v4), (t2, t3)) (t1, v2, f0)) = true ->
   (P0 (p, g0, v0, t0, g, v, m0) (v1, f, (v5, v6), (v3, v4), (t2, t3)) (t1, v2, f0)).2 =
   (simulator (p, g0, v0, t0, g, v, m0)
      (simMap (p, g0, v0, t0, g, v, m0) (t1, v2, f0) e x
        (v1, f, (v5, v6), (v3, v4), (t2, t3))) e).1.1.2).
    intros. apply Sim_com. apply H. apply H1. apply H1.
     pose (correctness (p, g0, v0, t0, g, v, m0)(t1, v2, f0)(v1, f, (v5, v6), (v3, v4), (t2, t3))).
    unfold P0 in e0. apply e0. trivial.
    (* challenge *)
    -- simpl. trivial.
    (* response *)
    - apply injective_projections. apply injective_projections.
    trivial. trivial. trivial.

    (* Time to deal with the Bijection   *)
    + unfold simMapInv. unfold simMap.
    assert (forall n', Vhead (VandermondeCol (S n') e) = 1). intros.
    rewrite Vbuild_head. cbn. trivial. split.
    (* Lets deal with the first part of bijection *)
    ++
    apply injective_projections. apply injective_projections. apply injective_projections.
    apply injective_projections.
    --- do 2 rewrite Prod_left_replace.
    unfold VF_sub. rewrite VF_mat_cancel; auto.
    --- do 2 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
    do 2 rewrite InProd_Sum. apply VF_sum_vcons_cancel_gen; auto.
    --- do 4 rewrite Prod_left_replace. do 3 rewrite Prod_right_replace.
    apply injective_projections.
    ---- rewrite Prod_left_replace.
    remember Vbreak as c. rewrite Prod_right_replace.
    unfold VF_sub. rewrite VF_mat_cancel; auto. rewrite Heqc.
    rewrite (EkGeneratorsRawM_switch v5 v6). rewrite <- VSn_eq.
    rewrite Vapp_Vtail. pose Vbreak_eq_app. symmetry in e0. rewrite e0.
     unfold VF_add, VF_neg, FMatrix.VA.vector_plus, FSemiRingT.Aplus.
    rewrite <- Vtail_map. rewrite Vtail_map2. rewrite (EkGeneratorsRawM_clear x.1.2).
    do 2 rewrite InProd_Sum. rewrite VF_sum_vcons_cancel_gen; auto.
    rewrite Prod_left_replace. rewrite (Vhead_app (n:=S M.N)). rewrite <- Vapp_Vtail.
    rewrite Vbreak_app. rewrite <- VSn_eq. trivial.
    ---- rewrite Prod_right_replace. rewrite Prod_left_left_replace.
    remember Vbreak as c. rewrite Prod_right_replace. rewrite Heqc.
     unfold VF_sub. rewrite VF_mat_cancel; auto.
    rewrite (EkGeneratorsRawM_switch v5 v6). rewrite <- VSn_eq.
    rewrite Vapp_Vtail. pose Vbreak_eq_app. symmetry in e0. rewrite e0.
    unfold VF_add, VF_neg, FMatrix.VA.vector_plus, FSemiRingT.Aplus.
    rewrite <- Vtail_map. rewrite Vtail_map2. rewrite (EkGeneratorsRawM_clear x.1.2).
    rewrite Vbreak_Vtail_clear. rewrite Vbreak_app. simpl. trivial.
    --- rewrite Prod_left_replace. remember Vbreak as c.
    do 4 rewrite Prod_right_replace. rewrite Prod_left_replace.
    rewrite Heqc. apply injective_projections.
    ---- rewrite <- Heqc. do 2 rewrite Prod_left_replace.
    rewrite Heqc.
    unfold VF_sub. rewrite VF_mat_cancel; auto.
    rewrite (EkGeneratorsRawM_switch v5 v6).
    rewrite (Vapp_Vtail (n:=S M.N)).
    pose Vbreak_eq_app. symmetry in e0. rewrite <- VSn_eq. rewrite e0.
    unfold VF_add, FMatrix.VA.vector_plus. do 2 rewrite <- Vbreak_vmap2_1.
    rewrite <- (Vapp_Vtail (n:=S M.N)). do 2 rewrite Vbreak_app. do 2 rewrite Prod_left_replace.
    remember (Vapp v3 (Vcons 0 v4)) as d.
    remember (Vapp v5 (Vcons 0 v6)) as l.
    assert (0 = Vhead (Vbreak (Vmap2 FSemiRingT.Aplus d (VF_scale l (Vhead x.1.1)))).2).
    intros. rewrite <- Vbreak_vmap2_2. unfold VF_scale. rewrite <- Vbreak_vmap_2.
    rewrite Heqd. rewrite Heql. do 2 rewrite Vbreak_app.  do 2 rewrite Prod_right_replace.
    rewrite Vhead_map2. rewrite Vhead_map. simpl. unfold FSemiRingT.Aplus. ring; auto.
    rewrite H2. rewrite <- VSn_eq. rewrite Heqd. rewrite Heql.
    rewrite <- Vbreak_vmap2_2. unfold VF_scale. rewrite <- Vbreak_vmap_2.
    rewrite <- Vbreak_vmap_1. do 2 rewrite Vbreak_app.  do 2 rewrite Prod_right_replace.
    rewrite Prod_left_replace. unfold VF_neg, FSemiRingT.Aplus. rewrite <- Vtail_map.
    rewrite Vtail_map2. rewrite (EkGeneratorsRawM_clear x.1.2). rewrite Vapp_Vtail.
    rewrite <- Vapp_map2. rewrite <- VectorUtil.Vapp_map. do 2 rewrite <- Vtail_map.
    rewrite Vtail_map2. pose VF_add_ass. pose VF_neg_corr. pose VF_add_zero.
    unfold VF_add, FMatrix.VA.vector_plus, FSemiRingT.Aplus, VF_neg in *.
    rewrite e1. rewrite e2. rewrite e3. do 2 rewrite InProd_Sum. rewrite Vtail_map2.
    rewrite VF_sum_vcons_cancel_gen; auto. rewrite (Vhead_app (n:=S M.N)).
    rewrite <- Vbreak_Vtail. rewrite Vtail_map2. pose Vbreak_vmap_1. symmetry in e4.
    do 2 rewrite e4. rewrite Vbreak_app. rewrite Prod_left_replace.
    rewrite e1. rewrite e2. rewrite e3.
    symmetry. apply VSn_eq.
    
    ---- do 2 rewrite Prod_right_replace. unfold VF_sub.
    unfold VF_add, VF_neg, FMatrix.VA.vector_plus. rewrite <- Vbreak_vmap2_2.
    rewrite Vbreak_app. rewrite Prod_right_replace. pose VF_mat_cancel.
    unfold VF_add, VF_neg, FMatrix.VA.vector_plus in e0. rewrite e0; auto.
    rewrite (EkGeneratorsRawM_switch v5 v6). rewrite <- VSn_eq.
    pose Vbreak_eq_app. symmetry in e1. rewrite e1.
     rewrite <- Vtail_map2.
    rewrite Vtail_cons. rewrite <- Vtail_map. do 2 rewrite Vtail_map2. unfold FSemiRingT.Aplus.
    rewrite (EkGeneratorsRawM_clear x.1.2). pose Vbreak_vmap2_2. symmetry in e2.
    rewrite e2. rewrite <- Vbreak_vmap_2. unfold VF_scale.
    rewrite <- Vbreak_vmap_2.
     do 2 rewrite (Vbreak_app (n1 := m)).
    rewrite <- Vbreak_vmap_2. rewrite Vbreak_Vtail_clear. rewrite (Vbreak_app (n1 := m)).
    do 2 rewrite <- Vtail_map2. rewrite Vtail_cons. do 3 rewrite Vtail_map.
    rewrite Vtail_cons. pose VF_add_ass. pose VF_neg_corr.
    unfold VF_add, FMatrix.VA.vector_plus in *. rewrite e3. rewrite e4.
    pose VF_add_zero. unfold VF_add, FMatrix.VA.vector_plus in e5. apply e5.
    --- remember Vbreak as d. do 2 rewrite Prod_left_replace.
    do 4 rewrite Prod_right_replace. apply injective_projections.
    ---- do 2 rewrite Prod_left_replace. rewrite Heqd.
    unfold VF_sub. rewrite VF_mat_cancel; auto. rewrite Prod_right_replace.
    rewrite (EkGeneratorsRawR_switch t2 t3). rewrite <- VSn_eq.
    rewrite Vapp_Vtail. rewrite <- Vbreak_eq_app. unfold MoR.VF_sub, MoR.VF_neg,
    MoR.VF_add, MoR.FMatrix.VA.vector_plus. rewrite <- Vtail_map. rewrite Vtail_map2.
    unfold MoR.FSemiRingT.Aplus. rewrite (EkGeneratorsRawR_clear x.2).
    rewrite <- Vbreak_Vtail. rewrite Vbreak_app.
    rewrite Prod_left_replace. rewrite MoR.VF_sum_induction.
    rewrite Vtail_map2. assert (forall a b, Ring.Fsub (Ring.Fadd a b) a = b).
    intros. destruct Ring.module_ring. rewrite Rsub_def. rewrite (Radd_comm a2).
    rewrite <- Radd_assoc. rewrite Ropp_def. rewrite Radd_comm. apply Radd_0_l.
    rewrite H2. rewrite Vhead_map2. rewrite (Vhead_app (n:=S M.N)). rewrite Vbuild_head.
    cbn. rewrite MVS.RopFOne. rewrite <- VSn_eq. trivial.
    ---- do 2 rewrite Prod_right_replace.
    unfold VF_sub. rewrite VF_mat_cancel; auto. rewrite Heqd.
    rewrite (EkGeneratorsRawR_switch t2 t3).
    rewrite <- VSn_eq. rewrite Vapp_Vtail. rewrite <- Vbreak_eq_app.
    unfold MoR.VF_sub, MoR.VF_neg, MoR.VF_add, MoR.FMatrix.VA.vector_plus, MoR.FSemiRingT.Aplus.
    rewrite <- Vtail_map. rewrite Vtail_map2. rewrite (EkGeneratorsRawR_clear x.2).
    rewrite Vbreak_Vtail_clear.  rewrite Vbreak_app. simpl. trivial.


    (* and the other way *)
    (* (((VF n)*F*F*F*Ring.F)*((VF M.N*VF M.N)*
    (VF M.N*VF M.N)*((vector Ring.F M.N)*(vector Ring.F M.N)))).*)
    ++ remember Vbreak as C. destruct t, p1, p1, p1, p0, p3, p2, p0, p0, p0.
    do 2 rewrite Prod_right_replace. do 2 rewrite Prod_left_replace.
    apply injective_projections.
    --- (* ((VF n)*F*F*F*Ring.F) *)
    apply injective_projections.  apply injective_projections.
    apply injective_projections. apply injective_projections.
    (* 1 of 5 *)
    ---- do 6 rewrite Prod_left_replace. rewrite VF_mat_cancel_rev; auto.
    (* 2 of 5 *)
    ---- do 2 rewrite Prod_right_replace.
    do 2 rewrite InProd_Sum. pose VF_comm_mult. pose VF_sum_vsub_cancel_gen.
    unfold VF_mult in *. rewrite <- (e0 (Nat.add 1 m) ((VandermondeCol (1 + m) e))).
    rewrite (e0 m v2). rewrite e1; auto.
    (* 3 of 5 *)
    ---- do 2 rewrite Prod_right_replace.
    do 2 rewrite InProd_Sum. pose VF_sum_vsub_cancel_gen. pose VF_comm_mult.
    unfold VF_mult in *. rewrite Vapp_cons. rewrite e1.
    rewrite <- (e1 (Nat.add (S M.N) m) (Vtail (VandermondeCol (m + m) e))). rewrite e0; auto.
    unfold VF_sub, VF_add, FMatrix.VA.vector_plus.
    rewrite HeqC. rewrite <- Vbreak_vmap2_2. rewrite <- Vbreak_vmap2_1.
    rewrite Vbreak_app. rewrite Prod_right_replace. rewrite Prod_left_replace.
    rewrite <- Vtail_map2. rewrite (Vtail_cons _ v8). apply Veq_nth. intros.
    rewrite Vnth_map2. do 2 rewrite (Vnth_app (n1:=S M.N)).
    destruct (le_gt_dec (S M.N) i).
    ----- do 2 rewrite Vnth_cons. destruct (lt_ge_dec 0 (i - S M.N)).
    ------ rewrite Vnth_map2. apply f_equal2; auto. rewrite Vnth_tail.
    rewrite Vnth_vbreak_2.
    assert (i < S M.N + S (S M.N)). apply ip. lia. intros. apply Vnth_eq. lia.
    ------ unfold EkGeneratorsRawM. unfold VF_add, FMatrix.VA.vector_plus.
    rewrite <- Vbreak_vmap2_2. do 2 rewrite Vbreak_app.
    do 2 rewrite Prod_right_replace.  rewrite Vhead_map2. rewrite <- Vtail_map2.
    rewrite Vhead_cons. rewrite Vnth_map. rewrite Vnth_map2. unfold FSemiRingT.Aplus.
    do 2 rewrite Vnth_tail. assert (S i < (S (S M.N)) + (S (S M.N))). lia.
    assert (lt_n_S ip = H2). apply le_unique. rewrite H3. unfold X, m in *.
    rewrite (Vnth_app (n1:=S (S M.N))). destruct (le_gt_dec (S (S M.N)) (S i)).
    rewrite Vnth_const. assert (forall a a', a= a'-> 0+a-(0+a') = 0). intros.
    rewrite H4. field. apply H4. rewrite Vhead_nth. apply Vnth_eq. lia.
    assert False. lia. contradiction.

    ----- rewrite Vnth_map2. apply f_equal2; auto. rewrite Vnth_vbreak_1.
    trivial.
    (* 4 of 5 *)
    ---- do 3 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
    unfold VF_sub, VF_add, VF_neg, VF_scale, FMatrix.VA.vector_plus.
    pose Vbreak_vmap2_2. symmetry in e0. rewrite HeqC. rewrite e0.
    rewrite <- Vbreak_vmap2_1. do 2 rewrite <- Vbreak_vmap_1.
    do 2 rewrite Vbreak_app. rewrite <- HeqC. do 2 rewrite Prod_right_replace.
    rewrite HeqC. rewrite <- Vbreak_vmap2_1. do 2 rewrite Vbreak_app.
    do 2 rewrite Prod_left_replace. rewrite <- Vbreak_vmap2_2.
    do 2 rewrite <- Vbreak_vmap_2.  rewrite <- Vbreak_vmap2_2. do 2 rewrite Vbreak_app.
    do 2 rewrite Prod_right_replace. rewrite <- Vtail_map2. do 2 rewrite Vtail_map.
    rewrite <- Vtail_map2. rewrite (Vtail_cons _ v8). unfold EkGeneratorsRawM.
    unfold VF_add, FMatrix.VA.vector_plus. rewrite Vhead_map2.
    rewrite Vbuild_head. rewrite <- Vbreak_vmap_2. rewrite <- Vbreak_vmap_1.
    rewrite Vbreak_Vtail_clear. rewrite <- Vbreak_vmap2_2. rewrite Vbreak_app.
    rewrite Prod_right_replace. rewrite Vtail_cons.
    do 2 rewrite InProd_Sum. pose VF_sum_vsub_cancel_gen.
    unfold VF_mult in e1. rewrite Vapp_cons. pose VF_comm_mult. unfold VF_mult in *.
    rewrite e2. rewrite (e2 _ _ (Vtail (VandermondeCol (m + m) e))). apply e1.
    rewrite Vbuild_head.  cbn. trivial. apply Veq_nth. intros.
    rewrite Vnth_map2. do 2 rewrite Vnth_map. rewrite Vnth_map2.
    rewrite Vhead_cons. rewrite <- Vtail_map2. unfold X, m, n in *.
    rewrite (Vapp_Vtail2 (n:=S M.N)). rewrite <- Vbreak_vmap2_1.
    rewrite Vbreak_app. rewrite Prod_left_replace. rewrite Vnth_map.
    rewrite Vnth_map2.
    do 4 rewrite Vnth_app. destruct (le_gt_dec (S M.N) i).
    ----- do 3 rewrite Vnth_cons. destruct (lt_ge_dec 0 (i - S M.N)).
    rewrite Vnth_map2. rewrite (Vtail_cons _ v10). do 2 rewrite Vnth_map.
    rewrite Vnth_map2. apply f_equal. apply f_equal. apply f_equal2. apply f_equal2.
    apply Vnth_eq. trivial. rewrite Vnth_tail. rewrite Vnth_map. rewrite Vnth_map2.
    ------ apply f_equal. apply f_equal2. rewrite Vnth_vbreak_2. lia. intros.
    rewrite Vnth_tail. do 2 rewrite Vnth_const. trivial. apply Vnth_eq.
    lia.
    ------ trivial.
    ------ unfold FSemiRingT.Aplus. rewrite Vnth_tail. rewrite Vnth_const.
    assert (forall a a', a = a' -> (0 + a -(0 +a')) = 0). intros. rewrite H2.
    field. rewrite H2. field. symmetry. rewrite Vbuild_nth. apply Vnth_eq. lia.
    ----- rewrite Vnth_map2. do 2 rewrite Vnth_map. rewrite Vnth_map2.
    rewrite Vnth_map. rewrite Vnth_map2. apply f_equal. apply f_equal.
    apply f_equal2; auto. apply f_equal. rewrite Vnth_vbreak_1.
    do 2 rewrite Vnth_tail. rewrite Vnth_const. trivial.

    (* 5 of 5 *)
    ---- do 2 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
    rewrite HeqC. unfold MoR.VF_sub, MoR.VF_add, MoR.VF_neg, MoR.FMatrix.VA.vector_plus.
    rewrite <- Vbreak_vmap2_2. rewrite <- Vbreak_vmap2_1.
    rewrite Vbreak_app. rewrite <- HeqC. rewrite Prod_left_replace.
    rewrite Prod_right_replace. rewrite <- Vtail_map2.  rewrite (Vtail_cons _ t4).
    assert (forall n' (a : Ring.F)(b b' : MoR.VF n')(c : VF (S n')),
     Vhead c = 1 -> b = b' -> MoR.VF_sum (Vmap2 MVS.op3
      (Vcons (Ring.Fsub a (MoR.VF_sum (Vmap2 MVS.op3 b (Vtail c) ))) b') c) = a).
    intros. rewrite H3. rewrite (VSn_eq c). rewrite Vcons_map2.
    rewrite <- VSn_eq. rewrite H2. rewrite MVS.RopFOne. rewrite MoR.VF_sum_vcons.
    destruct Ring.module_ring. rewrite Rsub_def. rewrite Radd_comm. rewrite <- Radd_assoc.
    rewrite (Radd_comm (Ring.Finv (MoR.VF_sum (Vmap2 MVS.op3 b' (Vtail c))))).
    rewrite Ropp_def. rewrite Radd_comm. apply Radd_0_l. rewrite Vapp_cons.
    apply H2. (* We have now cleaned up the goal and applied a simplifying lemma *)
    rewrite Vbuild_head. cbn. trivial.
    apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vnth_app.
    destruct (le_gt_dec (S M.N) i).
    ----- do 2 rewrite Vnth_cons. destruct (lt_ge_dec 0 (i - S M.N)).
    ------ rewrite Vnth_map2. symmetry. apply f_equal2; auto.
    rewrite HeqC. rewrite Vnth_tail. rewrite Vnth_vbreak_2. lia. intros.
    apply Vnth_eq. lia.
    ------ rewrite Vnth_map. rewrite HeqC. unfold EkGeneratorsRawR. unfold MoR.VF_add,
    MoR.FMatrix.VA.vector_plus. rewrite <- Vbreak_vmap2_2. do 2 rewrite Vbreak_app.
    do 2 rewrite Prod_right_replace. rewrite Vnth_tail.
    rewrite Vtail_cons. rewrite Vnth_map2. rewrite Vhead_map2. rewrite Vhead_cons.
    rewrite Vnth_const. unfold MoR.FSemiRingT.Aplus. assert (forall a b c,
    a = b -> Ring.Fadd (Ring.Fadd c b) (Ring.Finv a) = c). intros. rewrite H3.
    destruct Ring.module_ring. rewrite <- Radd_assoc. rewrite Ropp_def.
    rewrite Radd_comm. apply Radd_0_l. apply H3. destruct Ring.module_ring.
    rewrite Radd_0_l. assert (i = S M.N). lia. subst. assert (S (S M.N) <
    S (S M.N) + S (S M.N)). lia. assert (H4 = (lt_n_S ip)). apply le_unique.
    rewrite <- H5. unfold X, m in *. rewrite (Vnth_app (n1:=S (S M.N))).
    destruct (le_gt_dec (S (S M.N)) (S (S M.N))). rewrite Vhead_nth. apply Vnth_eq.
    lia. assert False. lia. contradiction.
    ----- rewrite Vnth_map2. apply f_equal2; auto. rewrite HeqC.
    rewrite Vnth_vbreak_1. apply Vnth_eq. trivial.
    (* ((VF M.N*VF M.N)*



    (VF M.N*VF M.N)*((vector Ring.F M.N)*(vector Ring.F M.N)) *)
    --- do 2 rewrite Prod_right_replace.
    apply injective_projections. apply injective_projections.
    (* 1 of 3 *)
    ---- do 3 rewrite Prod_left_replace.
    apply injective_projections.
    ----- do 2 rewrite Prod_left_replace. unfold EkGeneratorsRawM.
    unfold VF_add, FMatrix.VA.vector_plus. rewrite HeqC. rewrite <- Vbreak_vmap2_1.
    do 2 rewrite Vbreak_app. do 2 rewrite Prod_left_replace. rewrite <- Vmap2_tail.
    rewrite Vtail_cons. unfold VF_sub, VF_add, FMatrix.VA.vector_plus, VF_neg.
    rewrite <- Vbreak_vmap2_1. rewrite <- Vbreak_vmap_1. rewrite <- Vbreak_Vtail.
    rewrite <- Vbreak_vmap2_1. do 2 rewrite Vbreak_app. do 2 rewrite Prod_left_replace.
    rewrite Vbreak_Vconst. rewrite Prod_left_replace. pose VF_comm. pose VF_add_zero.
    pose VF_add_neg2. unfold VF_add, FMatrix.VA.vector_plus, VF_neg in *.
    rewrite (e0 m (Vconst Fzero m)). rewrite e1. rewrite e2. trivial.
    ----- do 2 rewrite Prod_right_replace. unfold EkGeneratorsRawM.
    unfold VF_add, FMatrix.VA.vector_plus. rewrite HeqC.
    rewrite <- Vbreak_vmap2_2. do 2 rewrite Vbreak_app. do 2 rewrite Prod_right_replace.
    rewrite <- Vmap2_tail.  rewrite Vtail_cons. unfold VF_sub, VF_add, FMatrix.VA.vector_plus, VF_neg.
    rewrite <- Vbreak_vmap2_2. rewrite <- Vbreak_vmap_2. rewrite Vbreak_Vtail_clear.
    rewrite <- Vbreak_vmap2_2. do 2 rewrite Vbreak_app. do 2 rewrite Prod_right_replace.
    rewrite <- Vmap2_tail. rewrite Vtail_cons.
    rewrite <- Vbreak_vmap2_2. rewrite Vbreak_app. rewrite Prod_right_replace.
    rewrite Vbreak_Vconst. rewrite Prod_right_replace. pose VF_comm. pose VF_add_zero.
    pose VF_add_neg2. unfold VF_add, FMatrix.VA.vector_plus, VF_neg in *.
    rewrite (e0 m (Vconst Fzero m)). rewrite e1. rewrite Vtail_map. rewrite e2. trivial.
    (* 2 of 3 *)
    ---- do 2 rewrite Prod_right_replace. apply injective_projections.
    ----- do 2 rewrite Prod_left_replace.
    unfold VF_sub. unfold VF_add,
    VF_neg, FMatrix.VA.vector_plus. rewrite HeqC. rewrite <- Vbreak_vmap2_1.
    rewrite Vbreak_app. rewrite Prod_left_replace. rewrite <- Vtail_map2.
    rewrite Vtail_cons.
    rewrite <- Vbreak_vmap2_1. unfold VF_scale. do 2 rewrite <- Vbreak_vmap_1.
    rewrite <- Vbreak_vmap2_1. do 2 rewrite (Vbreak_app (n1:=S M.N)).
    do 2 rewrite Prod_left_replace. do 2 rewrite <- Vbreak_vmap_1.
    rewrite (Vbreak_app (n1:=m)). rewrite Prod_left_replace.
    rewrite Vtail_map. rewrite Vtail_cons. unfold FSemiRingT.Aplus.
    assert (forall n (a b b' : VF n) , b= b' -> Vmap2 Fadd (
    Vmap2 Fadd a (Vmap Finv b)) b' = a). intros. rewrite H2. pose VF_add_neg2.
    unfold VF_add, FMatrix.VA.vector_plus in *. apply e0. apply H2.  trivial.
    ----- do 2 rewrite Prod_right_replace. rewrite HeqC.
    unfold VF_sub, VF_add, VF_neg, FMatrix.VA.vector_plus.
     rewrite <- Vbreak_vmap2_2. rewrite Vbreak_app. rewrite Prod_right_replace.
    rewrite <- Vtail_map2. rewrite Vtail_cons. pose Vbreak_vmap2_2. symmetry in e0.
    rewrite e0. unfold VF_scale. do 2 rewrite e0. do 4 rewrite <- Vbreak_vmap_2.
    rewrite <- Vbreak_vmap2_2. do 5 rewrite Vbreak_app. do 5 rewrite Prod_right_replace.
    rewrite Vtail_map. rewrite Vtail_cons. do 2 rewrite <- Vtail_map2.
    rewrite (Vtail_cons _ v8). do 2 rewrite Vtail_map. rewrite <- Vtail_map2.
    rewrite (Vtail_cons _ v8). rewrite Vtail_cons. pose VF_add_neg2.
    unfold VF_add, FMatrix.VA.vector_plus, VF_neg in *. rewrite Vbreak_vmap_2.
    apply e1.
    (* 3 of 3 *)
    ---- do 2 rewrite Prod_right_replace.
    unfold EkGeneratorsRawR. apply injective_projections.
    ----- do 2 rewrite Prod_left_replace. unfold MoR.VF_add, MoR.FMatrix.VA.vector_plus.
    rewrite HeqC. rewrite <- Vbreak_vmap2_1. do 2 rewrite Vbreak_app. do 2 rewrite Prod_left_replace.
    do 2 rewrite <- Vtail_map2. rewrite Vtail_cons.
    rewrite <- Vbreak_vmap2_2. rewrite (Vapp_Vtail2 (n:=S M.N)).
    do 2 rewrite Vbreak_app. do 2 rewrite Prod_right_replace. unfold MoR.VF_zero.
    rewrite Vapp_Vconst. unfold MoR.VF_sub.
    unfold MoR.VF_sub. pose VectorUtil.Vapp_map. unfold MoR.VF_neg.
    unfold MoR.VF_add, MoR.FMatrix.VA.vector_plus. rewrite <- Vbreak_vmap2_1.
    rewrite Vbreak_app. rewrite Prod_left_replace.  pose MoR.VF_add_zero.
    pose MoR.VF_comm. pose MoR.VF_add_neg2. unfold MoR.VF_add,
    MoR.FMatrix.VA.vector_plus, MoR.VF_neg in *. rewrite <- Vbreak_vmap_1.
    rewrite <- Vbreak_vmap2_1. rewrite <- Vbreak_Vtail. do 2 rewrite Vbreak_app.
    do 2 rewrite Prod_left_replace.
    rewrite (e2 (S M.N) (Vtail (Vconst Ring.Fzero m))). rewrite e1. apply e3.
    ----- rewrite Prod_right_replace. unfold MoR.VF_add, MoR.FMatrix.VA.vector_plus.
    rewrite HeqC. rewrite <- Vbreak_vmap2_2. do 2 rewrite Vbreak_app.
    do 2 rewrite Prod_right_replace. rewrite <- Vmap2_tail. rewrite Vtail_cons.
    unfold MoR.VF_sub, MoR.VF_add, MoR.VF_neg, MoR.FMatrix.VA.vector_plus.
    pose Vbreak_vmap2_2. symmetry in e0. do 2 rewrite e0.
    do 2 rewrite Vbreak_app. rewrite <- HeqC. do 2 rewrite Prod_right_replace.
    rewrite <- Vmap2_tail. rewrite Vtail_cons. rewrite HeqC.
    rewrite <- Vbreak_vmap_2. rewrite Vbreak_Vtail_clear. rewrite <- Vbreak_vmap2_2.
    rewrite Vbreak_app. rewrite Prod_right_replace. rewrite Vtail_map.
    rewrite Vbreak_Vconst. rewrite Prod_right_replace. pose MoR.VF_add_zero.
    pose MoR.VF_comm. unfold  MoR.VF_add, MoR.FMatrix.VA.vector_plus in e2.
    unfold  MoR.VF_add, MoR.FMatrix.VA.vector_plus in e1.
    rewrite (e2 m (Vconst Ring.Fzero m)). rewrite e1. rewrite Vtail_cons.
    rewrite e2. pose MoR.VF_add_neg3.
    unfold MoR.VF_add, MoR.FMatrix.VA.vector_plus, MoR.VF_neg in e3.
    pose MoR.VF_add_ass. rewrite e3. trivial.
  Qed.

  Lemma simulator_correct : forall (s : St)(t : TE)(e : F),
    V1(simulator s t e) = true.
  Proof.
    pose Message.module_abegrp. pose Ciphertext.module_abegrp.
    pose Commitment.module_abegrp. intros. unfold V1. unfold simulator.
    destruct s, p, p, p, p, p. destruct t, p0, p0, p0, p0, p1, p0, p1, p0, p2.
    apply andb_true_iff. split. apply andb_true_iff. split.
    apply andb_true_iff. split.  apply andb_true_iff. split.
    (* Correct 1 of 5 *)
    ++ apply bool_eq_corr. remember (VandermondeCol (1 + m)) as x.
    simpl. rewrite <- VG_Pexp_Vcons. rewrite <- VSn_eq. rewrite <- VSn_eq.
    replace (Vhead (x e)) with 1. rewrite mod_id. rewrite VG_prod_Vcons.
    rewrite comm. rewrite <- dot_assoc. rewrite <- inv_left. rewrite one_right. trivial.
    rewrite Heqx. rewrite Vbuild_head. cbn. trivial.
    (* Correct 2 of 5 *)
    ++ apply bool_eq_corr. simpl. rewrite VG_prod_Vcons. rewrite comm.
    replace (VF_prod [ ]) with 1. rewrite mod_id. rewrite <- dot_assoc.
    rewrite <- inv_left. rewrite one_right. trivial. cbn. trivial.
    (* Correct 3 of 5 *)
    ++ apply bool_eq_corr. remember rev as x. remember VandermondeCol as y.
    simpl. rewrite MoC.VG_prod_Vcons. replace (Vhead (y (S (S (M.N + m))) e)) with 1.
    rewrite VS1.mod_id. rewrite <- dot_assoc. rewrite comm. rewrite <- dot_assoc.
    apply f_equal2. trivial. rewrite <- dot_assoc. rewrite <- inv_left. rewrite one_right.
    trivial. rewrite Heqy. rewrite Vbuild_head. cbn. trivial.
    (* Correct 4 of 5 *)
    ++ apply bool_eq_corr. simpl. rewrite Vnth_map. rewrite (Vnth_app (n1:=S M.N)).
     destruct (le_gt_dec (S M.N) (S M.N)).
    rewrite Vnth_cons. destruct (lt_ge_dec 0 (S M.N - S M.N)).
    assert False. lia. contradiction. unfold PC. do 2 rewrite mod_ann. symmetry.
    apply one_right. assert False. lia. contradiction.
    (* Correct 5 of 5 *)
    ++ apply bool_eq_corr. simpl. rewrite Vnth_app. destruct (le_gt_dec M.N M.N).
    rewrite Vnth_cons. destruct (lt_ge_dec 0 (M.N - M.N)).
    assert False. lia. contradiction. trivial. assert False. lia. contradiction.
  Qed.

End BGMultiArgIns.




