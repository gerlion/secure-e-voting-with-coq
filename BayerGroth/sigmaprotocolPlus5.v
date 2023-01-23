Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Groups.groups.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import CoLoR.Util.Vector.VecArith.
Require Import VectorUtil.
Require Import sigmaprotocolPlus.
Require Import Lia.
Set Implicit Arguments.

Module Type SigmaPlus5.

  Parameter E0 : Set. (* First challenge *)
  Parameter E1 : Set. (* Second challenge *)
  
   Parameter St:Type.                                (* The set of statements *)
   Parameter W:Type.                                (* The set of witness *)
   Parameter Rel :St -> W -> bool.                  (* The relation function *)
   Parameter C0 : Type.                             (* The first set of commitments *)
   Parameter C1 : Type.                             (* Second set of commitments *)

   Parameter R0 : Type.                              (* The set of random coins for the prover *)
   Parameter R1 : Type.

    (*;                                   (* The set of challenges *) *)
   Parameter add0 : E0 -> E0 -> E0.                    (* We will require the set challenges of to be a ring *)
   Parameter zero0 : E0.      
   Parameter inv0 : E0 -> E0.
   Parameter bool_eq0 : E0 -> E0 -> bool.
   Parameter disjoint0 : E0 -> E0 -> bool.            (* disjoint is required for product groups *)

   Parameter add1 : E1 -> E1 -> E1.                    (* We will require the set challenges of to be a ring *)
   Parameter zero1 : E1.      
   Parameter inv1 : E1 -> E1.
   Parameter bool_eq1 : E1 -> E1 -> bool.
   Parameter disjoint1 : E1 -> E1 -> bool. 

   Parameter T : Type.                              (* The set of responses  *)
   Parameter P0 : St -> R0 -> W -> (St*C0).           (* The initial step of the prover, outputs a commit *)
   Parameter P1 : (St*C0*E0) -> R0*R1 -> W -> (St*C0*E0*C1).            
   Parameter P2 : (St*C0*E0*C1*E1) -> R0*R1 -> W -> (St*C0*E0*C1*E1*T).  (* The final step of the prover, outputs a response *)
   Parameter V2 : (St*C0*E0*C1*E1*T) -> bool.               (* The final step of the verifier *)

   Parameter TE0 : Type.                             (* The output produced by simulator maper *)
   Parameter TE1 : Type. 
   Parameter X  : Type. 
   Parameter simMapHelp : St -> X -> Prop.    (* We allow simpMap have information no ones else has *)
                                           
   Parameter simulator : St -> (TE0*TE1) -> (E0*E1) -> (St*C0*E0*C1*E1*T). (* The simulator *)
   Parameter simMap    : St -> W -> (E0*E1) -> X -> (R0*R1)  -> (TE0*TE1).    (* An explicit mapping between honest and simulated *)
   Parameter simMapInv : St -> W -> (E0*E1) -> X -> (TE0*TE1) -> (R0*R1).    (* A function we use to show simMap is a bijection 
      between R and T when fixing the other variables *)

   Parameter M0 : nat.
   Parameter M1 : nat.
   Parameter extractor : vector (vector T M1) M0 -> vector (E0*(vector E1 M1)) M0 -> (W).   (* The extractor *)
   Parameter fail_event : St -> C0*(vector C1 M0) -> vector (E0*(vector E1 M1)) M0 -> Prop.

  Axiom e_abgrp0 : AbeGroup E0 add0 zero0 bool_eq0 disjoint0 inv0.
  Axiom e_abgrp1 : AbeGroup E1 add1 zero1 bool_eq1 disjoint1 inv1.
  
  (** We require the functions do not modifiy the previous transcript *)
  Axiom pres_p0 : forall (s : St)(r : R0)(w : W), 
      (P0 s r w) = (s,(P0 s r w).2).
  Axiom pres_p1 : forall (sce : St*C0*E0)(r : R0*R1)(w : W), 
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Axiom pres_p2 : forall (sce : St*C0*E0*C1*E1)(r : R0*R1)(w : W), 
    (P2 sce r w) = (sce,(P2 sce r w).2).


  Axiom pres_sim : forall (s: St)(t : TE0*TE1)(e : E0*E1),
     s = (simulator s t e).1.1.1.1.1.
  Axiom chal_sim0 : forall (s: St)(t : TE0*TE1)(e : E0*E1),
    e.1 = (simulator s t e).1.1.1.2.
  Axiom chal_sim1 : forall (s: St)(t : TE0*TE1)(e : E0*E1),
    e.2 = (simulator s t e).1.2.  

  (** Properties *)
  Axiom correctness : forall (s :St)(w:W)(r0:R0)(r1:R1)(c0: E0)(c1 : E1),
    Rel s w ->
    V2 (P2 
      ((P1 ((P0 s r0 w), c0) (r0,r1) w), c1)
      (r0,r1) w) = true.

  Definition allDifferent (e : vector (E0*vector E1 M1) M0) :=
    PairwisePredicate disjoint0 (UnzipLeft e) /\
      bVforall (fun a => PairwisePredicate disjoint1 a.2) e.

  
  Definition allValid  (s : St)(c0 : C0)(c1 : vector C1 M0)
        (e : vector (E0*vector E1 M1) M0)
        (t : vector (vector T M1) M0) :=
    bVforall3 (fun c e0 t0 => 
      bVforall2 (fun e1 t1 => V2 (s, c0, e0.1, c, e1, t1)) e0.2 t0) c1 e t.


  Axiom special_soundness : forall (s : St)(c0 : C0)(c1 : vector C1 M0)
        (e : vector (E0*vector E1 M1) M0)
        (t : vector (vector T M1) M0),
      (* Forall e it is disjoint from all e *)
      allDifferent e ->
      allValid s c0 c1 e t -> 
    Rel s (extractor t e) = true \/ fail_event s (c0,c1) e.

  Axiom honest_verifier_ZK :
    forall (s : St)(w : W)(e : E0*E1)(x : X)(r : R0*R1)(t : TE0*TE1),
      simMapHelp s x ->
      Rel s w ->
      (P2 ((P1 ((P0 s r.1 w), e.1) r w), e.2) r w =
      simulator s (simMap s w e x r) e) /\ 
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.

  Axiom simulator_correct : forall (s : St)(t : TE0*TE1)(e : E0*E1),
    V2(simulator s t e) = true.
End SigmaPlus5.

Module Type SigmaPlusTo5 (E0 : GroupSig)(sig : SigmaPlus E0).

  Parameter E : Set.

  Parameter St:Type.                                (* The set of statements *)
  Parameter W:Type.                                (* The set of witness *)
  Parameter Rel :St -> W -> bool.                  (* The relation function *)
  Parameter C : Type.                              (* The set of commitments *)

  Parameter R : Type.

  Parameter add : E -> E -> E.                   
  Parameter zero : E.     
  Parameter inv : E -> E.
  Parameter bool_eq : E -> E -> bool.
  Parameter disjoint : E -> E -> bool.  

  Parameter P0 : St -> R -> W -> (St*C).   
  
  Parameter C1 : Type.                              
  Parameter R1 : Type.

  Parameter P1 : (St*C*E) -> R1 -> W -> St*C*E*C1.   

  Parameter ToSt : St*C*E*C1 -> sig.St.  
  Parameter ToWit : St*C*E -> R -> R1 -> W -> sig.W.

  Axiom ToValid : forall s w r r1 e,
    Rel s w ->
   sig.Rel (ToSt (P1 (P0 s r w, e) r1 w)) (ToWit (P0 s r w, e) r r1 w).

  Parameter TE : Type. 

  Axiom pres_p0 : forall (s : St)(r : R)(w : W), 
      (P0 s r w) = (s,(P0 s r w).2).

  Axiom pres_p1 : forall (s : St*C*E)(r : R1)(w : W), 
      (P1 s r w) = (s,(P1 s r w).2).

  Parameter M : nat.

  Parameter extractor :  vector sig.W M -> vector E M -> W.

  Parameter fail_event : St -> C -> vector E M -> Prop.

  Axiom special_soundness : forall s c (e : vector E M)(c1 : vector C1 M)
        (w : vector sig.W M),
    bVforall3 (fun a b d => sig.Rel (ToSt (s,c,a,b)) d) e c1 w ->
    PairwisePredicate (fun a b => disjoint a b) e  ->
    Rel s (extractor w e) \/ fail_event s c e.

  Axiom e_abgrp : AbeGroup E add zero bool_eq disjoint inv.

  Parameter X : Type. 

  Parameter simulator : St -> TE -> E -> C*C1.
  Parameter simMap    : St -> W -> E -> X -> R*R1  ->  TE. 
  Parameter simMapInv : St -> W -> E -> X -> TE -> R*R1.

  Parameter simMapHelp : St -> X -> Prop.

  Parameter sigXcomp : St -> X -> sig.X.

  Axiom simMapInvValid :  forall (st : St)(w : W)(x : X)
        (e : E)(r : R*R1)(t : TE),
     Rel st w ->
     simMapHelp st x ->
    simMap st w e x (simMapInv st w e x t) = t /\
    simMapInv st w e x (simMap st w e x r) = r.

  (* This may need more preconditions otherwise it might be too strong *)
  Axiom simMapHelpValid : forall (st : St)(x : X)(c : C)(c1 : C1)(e : E),
    simMapHelp st x ->
    sig.simMapHelp (ToSt (st,c,e,c1)) (sigXcomp st x).

  Axiom simulatorZK1 : forall s w r e x,
     Rel s w ->
     simMapHelp s x ->
     (P0 s r.1 w).2 = (simulator s (simMap s w e x r) e).1.

  Axiom simulatorZK2 : forall s w r e x,
     Rel s w ->
     simMapHelp s x ->
      (P1 (P0 s r.1 w, e) r.2 w).2 = 
      (simulator s (simMap s w e x r) e).2.

End SigmaPlusTo5. 

Module Type SigmaPlus5Comp (E : GroupSig)(sig : SigmaPlus E)
    (exp : SigmaPlusTo5 E sig) <: SigmaPlus5.

  Definition E0 : Set := exp.E.
  Definition E1 : Set := E.G.
  
   Definition St:Type := exp.St.
   Definition W:Type := exp.W.                
   Definition Rel :St -> W -> bool := exp.Rel.
   Definition C0 : Type := exp.C.             
   Definition C1 : Type := exp.C1*sig.C.

   Definition R0 : Type := exp.R.    
   Definition R1 : Type := exp.R1*sig.R.

   Definition add0 : E0 -> E0 -> E0 := exp.add.                   
   Definition zero0 : E0 := exp.zero.      
   Definition inv0 : E0 -> E0 := exp.inv.
   Definition bool_eq0 : E0 -> E0 -> bool := exp.bool_eq.
   Definition disjoint0 : E0 -> E0 -> bool := exp.disjoint.  
          
   Definition add1 : E1 -> E1 -> E1 := E.Gdot.                   
   Definition zero1 : E1 := E.Gone.      
   Definition inv1 : E1 -> E1 := E.Ginv.
   Definition bool_eq1 : E1 -> E1 -> bool := E.Gbool_eq.
   Definition disjoint1 (a b : E1) : bool := E.Gdisjoint a b. 

   Definition T : Type := sig.T.                             
   Definition P0 : St -> R0 -> W -> (St*C0) := exp.P0.    

   Definition P1 (tran : St*C0*E0)(r : R0*R1)(w : W) : (St*C0*E0*C1) :=
    (tran, ((exp.P1 tran r.2.1 w).2, 
      (sig.P0 (exp.ToSt (tran, (exp.P1 tran r.2.1 w).2)) r.2.2
              (exp.ToWit tran r.1 r.2.1 w)).2)).        

   Definition P2 (tran : St*C0*E0*C1*E1)(r : R0*R1)(w : W) : (St*C0*E0*C1*E1*T) := 
    (tran, (sig.P1 (exp.ToSt (tran.1.1, tran.1.2.1),tran.1.2.2,tran.2) r.2.2 
      (exp.ToWit tran.1.1 r.1 r.2.1 w)).2). 
   Definition V2 (tran : St*C0*E0*C1*E1*T) : bool :=
    sig.V1 (exp.ToSt (tran.1.1.1, tran.1.1.2.1),tran.1.1.2.2,tran.1.2,tran.2).           

   Definition TE0 : Type := exp.TE.                            
   Definition TE1 : Type := sig.TE. 
   Definition X  : Type := exp.X. 
   Definition simMapHelp : St -> X -> Prop := exp.simMapHelp.    
                                           
   Definition simulator (st : St)(t : TE0*TE1)(e : E0*E1) : (St*C0*E0*C1*E1*T) :=
    (st, (exp.simulator st t.1 e.1).1, e.1, ((exp.simulator st t.1 e.1).2,
      (sig.simulator (exp.ToSt (st, (exp.simulator st t.1 e.1).1, e.1, (exp.simulator st t.1 e.1).2)) t.2 e.2).1.1.2), e.2, 
      (sig.simulator (exp.ToSt (st, (exp.simulator st t.1 e.1).1, e.1, (exp.simulator st t.1 e.1).2)) t.2 e.2).2).

   Definition simMap (st : St)(w : W)(e : E0*E1)(x : X)(r : R0*R1) : (TE0*TE1) :=
    (exp.simMap st w e.1 x (r.1,r.2.1), 
      sig.simMap (exp.ToSt (exp.P1 ((exp.P0 st r.1 w), e.1) r.2.1 w)) 
        (exp.ToWit ((exp.P0 st r.1 w), e.1) r.1 r.2.1 w) e.2 (exp.sigXcomp st x) r.2.2).
          
   Definition simMapInv (st : St)(w : W)(e : E0*E1)(x : X)(t : TE0*TE1) : (R0*R1) :=
      ((exp.simMapInv st w e.1 x t.1).1, 
      ((exp.simMapInv st w e.1 x t.1).2,
      sig.simMapInv (exp.ToSt (st, (exp.simulator st t.1 e.1).1, e.1, 
        (exp.simulator st t.1 e.1).2)) 
      (exp.ToWit (st, (exp.simulator st t.1 e.1).1, e.1) (exp.simMapInv st w e.1 x t.1).1
        (exp.simMapInv st w e.1 x t.1).2 w) e.2 (exp.sigXcomp st x) t.2)).

   Definition M0 : nat := exp.M.
   Definition M1 : nat := sig.M.
   Definition extractor (t : vector (vector T M1) M0)(e : vector (E0*(vector E1 M1)) M0) : W := 
    exp.extractor (Vmap2 (fun a b => sig.extractor a b.2) t e) (Vmap (fun a => a.1) e).

   Definition fail_event (t : St)(c : C0*(vector C1 M0))(e :vector (E0*(vector E1 M1)) M0) : Prop :=
    exp.fail_event t c.1 (UnzipLeft e) \/
    Vexists2 (fun a b => sig.fail_event (exp.ToSt (t,c.1,b.1,a.1)) a.2 b.2) c.2 e.
      
  Lemma e_abgrp0 : AbeGroup E0 add0 zero0 bool_eq0 disjoint0 inv0.
  Proof.
    apply exp.e_abgrp.
  Qed.

  Lemma e_abgrp1 : AbeGroup E1 add1 zero1 bool_eq1 disjoint1 inv1.
  Proof.
    apply E.module_abegrp.
  Qed.
  
  (** We require the functions do not modifiy the previous transcript *)
  Lemma pres_p0 : forall (s : St)(r : R0)(w : W), 
      (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. apply exp.pres_p0.
  Qed.

  Lemma pres_p1 : forall (sce : St*C0*E0)(r : R0*R1)(w : W), 
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Proof.
    intros. unfold P1. simpl. trivial.
  Qed.

  Lemma pres_p2 : forall (sce : St*C0*E0*C1*E1)(r : R0*R1)(w : W), 
    (P2 sce r w) = (sce,(P2 sce r w).2).
  Proof.
    intros. unfold P2. simpl. trivial.
  Qed.
  
  Lemma pres_sim : forall (s: St)(t : TE0*TE1)(e : E0*E1),
     s = (simulator s t e).1.1.1.1.1.
  Proof.
    intros.  trivial.
  Qed.

  Lemma chal_sim0 : forall (s: St)(t : TE0*TE1)(e : E0*E1),
    e.1 = (simulator s t e).1.1.1.2.
  Proof.
    intros.  trivial.
  Qed.
  
  Lemma chal_sim1 : forall (s: St)(t : TE0*TE1)(e : E0*E1),
    e.2 = (simulator s t e).1.2. 
  Proof.
    intros.  trivial.
  Qed.

  
  Definition allDifferent (e : vector (E0*vector E1 M1) M0) :=
    PairwisePredicate disjoint0 (UnzipLeft e) /\
      bVforall (fun a => PairwisePredicate disjoint1 a.2) e.

  Definition allValid  (s : St)(c0 : C0)(c1 : vector C1 M0)
        (e : vector (E0*vector E1 M1) M0)
        (t : vector (vector T M1) M0) :=
    bVforall3 (fun c e0 t0 => 
      bVforall2 (fun e1 t1 => V2 (s, c0, e0.1, c, e1, t1)) e0.2 t0) c1 e t.

  (** Properties *)
  Lemma correctness : forall (s :St)(w:W)(r0:R0)(r1:R1)(c0: E0)(c1 : E1),
    Rel s w ->
    V2 (P2 
      ((P1 ((P0 s r0 w), c0) (r0,r1) w), c1)
   (r0,r1) w) = true.
  Proof.
    intros. unfold V2, P2, P1, P0. simpl. rewrite <- sig.pres_p0.
    rewrite <- sig.pres_p1. apply sig.correctness. rewrite <- exp.pres_p1.
    apply exp.ToValid; auto.
  Qed.

  Lemma special_soundness : forall (s : St)(c0 : C0)(c1 : vector C1 M0)
        (e : vector (E0*vector E1 M1) M0)
        (t : vector (vector T M1) M0),
    (* Forall e it is disjoint from all e *)
      allDifferent e ->
      allValid s c0 c1 e t -> 
    Rel s (extractor t e) = true \/ fail_event s (c0,c1) e.
  Proof.
    intros. unfold fail_event. assert (bVforall3 (fun a d b => sig.Rel (exp.ToSt (s,c0,a,d)) b) 
    (UnzipLeft e) (UnzipLeft c1) (Vmap2 (fun a b => sig.extractor a b.2) t e)  \/
    Vexists2 (fun (a : C1) (b : exp.E * vector E1 sig.M) =>
    sig.fail_event (exp.ToSt (s, (c0, c1).1, b.1, a.1)) a.2 b.2) 
    (c0, c1).2 e). apply Vforall3Comb_nth_intro. 
    (* Main case *)
    intros. apply (bVforall3_elim_nth ip) in H0. destruct H.
    apply (bVforall_elim_nth ip) in H1.
    unfold V2 in H0. simpl in H0. rewrite Vnth_map.
    pose (sig.special_soundness (exp.ToSt (s, c0, (Vnth e ip).1, (Vnth c1 ip).1)) 
    (Vnth c1 ip).2 (Vnth e ip).2 (Vnth t ip) H1 H0). rewrite Vnth_map2. rewrite Vnth_map.
     trivial.
    (* Clean up *)
    destruct 0. destruct H. pose (exp.special_soundness s c0 (UnzipLeft e) (UnzipLeft c1)
    (Vmap2 (fun (a : vector sig.T sig.M) (b : E0 * vector E1 sig.M) =>
           sig.extractor a b.2) t e) H1 H). destruct o. left. apply H3.
    right. left. apply H3. right. right. apply H1.
  Qed.

  Lemma honest_verifier_ZK :
    forall (s : St)(w : W)(e : E0*E1)(x : X)(r : R0*R1)(t : TE0*TE1),
      simMapHelp s x ->
      Rel s w ->
      (P2 ((P1 ((P0 s r.1 w), e.1) r w), e.2) r w =
      simulator s (simMap s w e x r) e) /\ 
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.
  Proof.
    intros. unfold V2, P2, P1, P0, simulator, simMap, simMapInv. simpl.
    pose sig.honest_verifier_ZK. unfold simMapHelp in H. split.
    (* The map work *)
    + intros. pose (exp.simMapHelpValid (exp.P0 s r.1 w).2 
    (exp.P1 (exp.P0 s r.1 w,e.1) r.2.1 w).2 e.1 H).
    pose (exp.ToValid r.1 r.2.1 e.1 H0). rewrite <- exp.pres_p0 in s0.
    rewrite <- exp.pres_p1 in s0.
    pose (a (exp.ToSt (exp.P1 ((exp.P0 s r.1 w), e.1) r.2.1 w))
    (exp.ToWit ((exp.P0 s r.1 w), e.1) r.1 r.2.1 w) e.2 (exp.sigXcomp s x) 
    r.2.2 t.2 s0 i).
    destruct a0. clear a. destruct H2.
    apply injective_projections; simpl. apply injective_projections; simpl. 
    apply injective_projections; simpl. apply injective_projections; simpl. trivial.
    rewrite <- exp.simulatorZK1; trivial. rewrite <- exp.pres_p0. trivial.
    trivial. apply injective_projections; simpl. rewrite <- exp.simulatorZK2; trivial.
    rewrite <- exp.simulatorZK1; trivial.  rewrite <- exp.simulatorZK2; trivial.
    rewrite <- exp.pres_p0. do 2 rewrite <- exp.pres_p1.
    symmetry in H1. rewrite H1. rewrite sig.pres_p1. trivial. trivial.
    rewrite <- sig.pres_p0. rewrite <- exp.pres_p1. rewrite H1. 
    rewrite <- exp.simulatorZK1; trivial. rewrite <- exp.simulatorZK2; trivial.
    rewrite <- exp.pres_p0. rewrite <- exp.pres_p1. trivial.
    (* and it bijects *)
    + pose (exp.simMapInvValid  e.1 (r.1,r.2.1) t.1 H0 H). destruct a0. split.
    ++ pose (exp.simMapHelpValid (exp.P0 s r.1 w).2 
    (exp.P1 (exp.P0 s r.1 w, e.1) r.2.1 w).2 e.1 H).
    pose (exp.ToValid r.1 r.2.1 e.1 H0).  rewrite <- exp.pres_p0 in s0.
    rewrite <- exp.pres_p1 in s0. pose (a (exp.ToSt (exp.P1 (exp.P0 s r.1 w, e.1) r.2.1 w))
    (exp.ToWit (exp.P0 s r.1 w, e.1) r.1 r.2.1 w) e.2 (exp.sigXcomp s x) 
    r.2.2 t.2 s0 i).
    destruct a0. rewrite <- exp.simulatorZK1; trivial. 
    rewrite <- exp.simulatorZK2; trivial. destruct H4. 
    rewrite H2. rewrite <- exp.pres_p0. rewrite <- exp.pres_p1.  rewrite H4.
    symmetry. simpl. rewrite <- surjective_pairing. apply surjective_pairing.
    ++ pose (exp.simMapHelpValid (exp.P0 s (exp.simMapInv s w e.1 x t.1).1 w).2 
     (exp.P1 (exp.P0 s (exp.simMapInv s w e.1 x t.1).1 w, e.1)
        (exp.simMapInv s w e.1 x t.1).2 w).2 e.1 H). 
    pose (exp.ToValid (exp.simMapInv s w e.1 x t.1).1 
        (exp.simMapInv s w e.1 x t.1).2 e.1 H0).
    rewrite <- exp.pres_p0 in s0. rewrite <- exp.pres_p1 in s0.  
    pose (a (exp.ToSt (exp.P1 (exp.P0 s 
      (exp.simMapInv s w e.1 x t.1).1 w, e.1)(exp.simMapInv s w e.1 x t.1).2 w))
    (exp.ToWit ((exp.P0 s (exp.simMapInv s w e.1 x t.1).1 w), e.1) 
    (exp.simMapInv s w e.1 x t.1).1 (exp.simMapInv s w e.1 x t.1).2 w) 
    e.2 (exp.sigXcomp s x) r.2.2 t.2 s0 i).
     destruct a0. destruct H4. rewrite <- surjective_pairing. rewrite H1. 
    apply injective_projections. trivial. simpl. 
    assert (sig.simMapInv (exp.ToSt
     (exp.P1 (exp.P0 s (exp.simMapInv s w e.1 x t.1).1 w, e.1)
        (exp.simMapInv s w e.1 x t.1).2 w))
  (exp.ToWit (exp.P0 s (exp.simMapInv s w e.1 x t.1).1 w, e.1)
     (exp.simMapInv s w e.1 x t.1).1 (exp.simMapInv s w e.1 x t.1).2 w) e.2 
     (exp.sigXcomp s x) t.2 =
   sig.simMapInv
     (exp.ToSt (s, (exp.simulator s t.1 e.1).1, e.1, (exp.simulator s t.1 e.1).2))
     (exp.ToWit (s, (exp.simulator s t.1 e.1).1, e.1) (exp.simMapInv s w e.1 x t.1).1
        (exp.simMapInv s w e.1 x t.1).2 w) e.2 (exp.sigXcomp s x) t.2). 
    +++ apply f_equal5; trivial. rewrite exp.pres_p1.
    rewrite (exp.simulatorZK2 (exp.simMapInv s w e.1 x t.1) e.1 H0 H).
    rewrite exp.pres_p0. rewrite (exp.simulatorZK1 (exp.simMapInv s w e.1 x t.1) 
    e.1 H0 H). rewrite H1. trivial. rewrite exp.pres_p0. rewrite 
    (exp.simulatorZK1 (exp.simMapInv s w e.1 x t.1) e.1 H0 H). rewrite H1. trivial.
    +++ rewrite <- H6. apply H5.
  Qed.

  Lemma simulator_correct : forall (s : St)(t : TE0*TE1)(e : E0*E1),
    V2(simulator s t e) = true.
  Proof.
    intros. unfold V2. simpl. remember (sig.simulator 
    (exp.ToSt (s, (exp.simulator s t.1 e.1).1, e.1, (exp.simulator s t.1 e.1).2))) as a.
    rewrite (sig.pres_sim (exp.ToSt (s, (exp.simulator s t.1 e.1).1, e.1, 
    (exp.simulator s t.1 e.1).2)) t.2 e.2). 
    rewrite <- Heqa. remember (a t.2 e.2) as b.
    rewrite (sig.chal_sim (exp.ToSt (s, (exp.simulator s t.1 e.1).1, e.1, 
    (exp.simulator s t.1 e.1).2)) t.2 e.2).
    rewrite <- Heqa. rewrite <- Heqb. rewrite <- surjective_pairing. 
    do 2 rewrite <- surjective_pairing. rewrite Heqb. rewrite Heqa.
    apply sig.simulator_correct.
  Qed. 

End SigmaPlus5Comp.

Module SigmaPlus5CompIns (E : GroupSig)(sig : SigmaPlus E)
    (exp : SigmaPlusTo5 E sig) <: SigmaPlus5Comp E sig exp.

  Definition E0 : Set := exp.E.
  Definition E1 : Set := E.G.
  
   Definition St:Type := exp.St.
   Definition W:Type := exp.W.
   Definition Rel :St -> W -> bool := exp.Rel.
   Definition C0 : Type := exp.C.
   Definition C1 : Type := exp.C1*sig.C.

   Definition R0 : Type := exp.R.
   Definition R1 : Type := exp.R1*sig.R.

   Definition add0 : E0 -> E0 -> E0 := exp.add.
   Definition zero0 : E0 := exp.zero.
   Definition inv0 : E0 -> E0 := exp.inv.
   Definition bool_eq0 : E0 -> E0 -> bool := exp.bool_eq.
   Definition disjoint0 : E0 -> E0 -> bool := exp.disjoint.
          
   Definition add1 : E1 -> E1 -> E1 := E.Gdot.
   Definition zero1 : E1 := E.Gone.
   Definition inv1 : E1 -> E1 := E.Ginv.
   Definition bool_eq1 : E1 -> E1 -> bool := E.Gbool_eq.
   Definition disjoint1 (a b : E1) : bool := E.Gdisjoint a b.

   Definition T : Type := sig.T.
   Definition P0 : St -> R0 -> W -> (St*C0) := exp.P0.

   Definition P1 (tran : St*C0*E0)(r : R0*R1)(w : W) : (St*C0*E0*C1) :=
    (tran, ((exp.P1 tran r.2.1 w).2,
      (sig.P0 (exp.ToSt (tran, (exp.P1 tran r.2.1 w).2)) r.2.2
              (exp.ToWit tran r.1 r.2.1 w)).2)).

   Definition P2 (tran : St*C0*E0*C1*E1)(r : R0*R1)(w : W) : (St*C0*E0*C1*E1*T) :=
    (tran, (sig.P1 (exp.ToSt (tran.1.1, tran.1.2.1),tran.1.2.2,tran.2) r.2.2
      (exp.ToWit tran.1.1 r.1 r.2.1 w)).2).
   Definition V2 (tran : St*C0*E0*C1*E1*T) : bool :=
    sig.V1 (exp.ToSt (tran.1.1.1, tran.1.1.2.1),tran.1.1.2.2,tran.1.2,tran.2).

   Definition TE0 : Type := exp.TE.
   Definition TE1 : Type := sig.TE.
   Definition X  : Type := exp.X.
   Definition simMapHelp : St -> X -> Prop := exp.simMapHelp.
                                           
   Definition simulator (st : St)(t : TE0*TE1)(e : E0*E1) : (St*C0*E0*C1*E1*T) :=
    (st, (exp.simulator st t.1 e.1).1, e.1, ((exp.simulator st t.1 e.1).2,
      (sig.simulator (exp.ToSt (st, (exp.simulator st t.1 e.1).1, e.1, (exp.simulator st t.1 e.1).2)) t.2 e.2).1.1.2), e.2,
      (sig.simulator (exp.ToSt (st, (exp.simulator st t.1 e.1).1, e.1, (exp.simulator st t.1 e.1).2)) t.2 e.2).2).

   Definition simMap (st : St)(w : W)(e : E0*E1)(x : X)(r : R0*R1) : (TE0*TE1) :=
    (exp.simMap st w e.1 x (r.1,r.2.1),
      sig.simMap (exp.ToSt (exp.P1 ((exp.P0 st r.1 w), e.1) r.2.1 w))
        (exp.ToWit ((exp.P0 st r.1 w), e.1) r.1 r.2.1 w) e.2 (exp.sigXcomp st x) r.2.2).
          
   Definition simMapInv (st : St)(w : W)(e : E0*E1)(x : X)(t : TE0*TE1) : (R0*R1) :=
      ((exp.simMapInv st w e.1 x t.1).1,
      ((exp.simMapInv st w e.1 x t.1).2,
      sig.simMapInv (exp.ToSt (st, (exp.simulator st t.1 e.1).1, e.1,
        (exp.simulator st t.1 e.1).2))
      (exp.ToWit (st, (exp.simulator st t.1 e.1).1, e.1) (exp.simMapInv st w e.1 x t.1).1
        (exp.simMapInv st w e.1 x t.1).2 w) e.2 (exp.sigXcomp st x) t.2)).

   Definition M0 : nat := exp.M.
   Definition M1 : nat := sig.M.
   Definition extractor (t : vector (vector T M1) M0)(e : vector (E0*(vector E1 M1)) M0) : W :=
    exp.extractor (Vmap2 (fun a b => sig.extractor a b.2) t e) (Vmap (fun a => a.1) e).

   Definition fail_event (t : St)(c : C0*(vector C1 M0))(e :vector (E0*(vector E1 M1)) M0) : Prop :=
    exp.fail_event t c.1 (UnzipLeft e) \/
    Vexists2 (fun a b => sig.fail_event (exp.ToSt (t,c.1,b.1,a.1)) a.2 b.2) c.2 e.
      
  Lemma e_abgrp0 : AbeGroup E0 add0 zero0 bool_eq0 disjoint0 inv0.
  Proof.
    apply exp.e_abgrp.
  Qed.

  Lemma e_abgrp1 : AbeGroup E1 add1 zero1 bool_eq1 disjoint1 inv1.
  Proof.
    apply E.module_abegrp.
  Qed.
  
  (** We require the functions do not modifiy the previous transcript *)
  Lemma pres_p0 : forall (s : St)(r : R0)(w : W),
      (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. apply exp.pres_p0.
  Qed.

  Lemma pres_p1 : forall (sce : St*C0*E0)(r : R0*R1)(w : W),
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Proof.
    intros. unfold P1. simpl. trivial.
  Qed.

  Lemma pres_p2 : forall (sce : St*C0*E0*C1*E1)(r : R0*R1)(w : W),
    (P2 sce r w) = (sce,(P2 sce r w).2).
  Proof.
    intros. unfold P2. simpl. trivial.
  Qed.
  
  Lemma pres_sim : forall (s: St)(t : TE0*TE1)(e : E0*E1),
     s = (simulator s t e).1.1.1.1.1.
  Proof.
    intros.  trivial.
  Qed.

  Lemma chal_sim0 : forall (s: St)(t : TE0*TE1)(e : E0*E1),
    e.1 = (simulator s t e).1.1.1.2.
  Proof.
    intros.  trivial.
  Qed.
  
  Lemma chal_sim1 : forall (s: St)(t : TE0*TE1)(e : E0*E1),
    e.2 = (simulator s t e).1.2.
  Proof.
    intros.  trivial.
  Qed.

  (** Properties *)
  Lemma correctness : forall (s :St)(w:W)(r0:R0)(r1:R1)(c0: E0)(c1 : E1),
    Rel s w ->
    V2 (P2
      ((P1 ((P0 s r0 w), c0) (r0,r1) w), c1)
   (r0,r1) w) = true.
  Proof.
    intros. unfold V2, P2, P1, P0. simpl. rewrite <- sig.pres_p0.
    rewrite <- sig.pres_p1. apply sig.correctness. rewrite <- exp.pres_p1.
    apply exp.ToValid; auto.
  Qed.
  
  Definition allDifferent (e : vector (E0*vector E1 M1) M0) :=
    PairwisePredicate disjoint0 (UnzipLeft e) /\
      bVforall (fun a => PairwisePredicate disjoint1 a.2) e.

  
  Definition allValid  (s : St)(c0 : C0)(c1 : vector C1 M0)
        (e : vector (E0*vector E1 M1) M0)
        (t : vector (vector T M1) M0) :=
    bVforall3 (fun c e0 t0 => 
      bVforall2 (fun e1 t1 => V2 (s, c0, e0.1, c, e1, t1)) e0.2 t0) c1 e t.

  Lemma special_soundness : forall (s : St)(c0 : C0)(c1 : vector C1 M0)
        (e : vector (E0*vector E1 M1) M0)
        (t : vector (vector T M1) M0),
    (* Forall e it is disjoint from all e *)
      allDifferent e ->
      allValid s c0 c1 e t ->
    Rel s (extractor t e) = true \/ fail_event s (c0,c1) e.
  Proof.
    intros. unfold fail_event. assert (bVforall3 (fun a d b => sig.Rel (exp.ToSt (s,c0,a,d)) b)
    (UnzipLeft e) (UnzipLeft c1) (Vmap2 (fun a b => sig.extractor a b.2) t e)  \/
    Vexists2 (fun (a : C1) (b : exp.E * vector E1 sig.M) =>
    sig.fail_event (exp.ToSt (s, (c0, c1).1, b.1, a.1)) a.2 b.2)
    (c0, c1).2 e). apply Vforall3Comb_nth_intro.
    (* Main case *)
    intros. apply (bVforall3_elim_nth ip) in H0. destruct H. apply (bVforall_elim_nth ip) in H1.
    unfold V2 in H1. simpl in H1. rewrite Vnth_map.
    pose (sig.special_soundness (exp.ToSt (s, c0, (Vnth e ip).1, (Vnth c1 ip).1))
    (Vnth c1 ip).2 (Vnth e ip).2 (Vnth t ip) H1 H0). rewrite Vnth_map2. rewrite Vnth_map.
     trivial.
    (* Clean up *)
    destruct H1. destruct H. pose (exp.special_soundness s c0 (UnzipLeft e) (UnzipLeft c1)
    (Vmap2 (fun (a : vector sig.T sig.M) (b : E0 * vector E1 sig.M) =>
           sig.extractor a b.2) t e) H1 H). destruct o. left. apply H3.
    right. left. apply H3. right. right. apply H1.
  Qed.

  Lemma honest_verifier_ZK :
    forall (s : St)(w : W)(e : E0*E1)(x : X)(r : R0*R1)(t : TE0*TE1),
      simMapHelp s x ->
      Rel s w ->
      (P2 ((P1 ((P0 s r.1 w), e.1) r w), e.2) r w =
      simulator s (simMap s w e x r) e) /\
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.
  Proof.
    intros. unfold V2, P2, P1, P0, simulator, simMap, simMapInv. simpl.
    pose sig.honest_verifier_ZK. unfold simMapHelp in H. split.
    (* The map work *)
    + intros. pose (exp.simMapHelpValid (exp.P0 s r.1 w).2
    (exp.P1 (exp.P0 s r.1 w,e.1) r.2.1 w).2 e.1 H).
    pose (exp.ToValid r.1 r.2.1 e.1 H0). rewrite <- exp.pres_p0 in s0.
    rewrite <- exp.pres_p1 in s0.
    pose (a (exp.ToSt (exp.P1 ((exp.P0 s r.1 w), e.1) r.2.1 w))
    (exp.ToWit ((exp.P0 s r.1 w), e.1) r.1 r.2.1 w) e.2 (exp.sigXcomp s x)
    r.2.2 t.2 s0 i).
    destruct a0. clear a. destruct H2.
    apply injective_projections; simpl. apply injective_projections; simpl.
    apply injective_projections; simpl. apply injective_projections; simpl. trivial.
    rewrite <- exp.simulatorZK1; trivial. rewrite <- exp.pres_p0. trivial.
    trivial. apply injective_projections; simpl. rewrite <- exp.simulatorZK2; trivial.
    rewrite <- exp.simulatorZK1; trivial.  rewrite <- exp.simulatorZK2; trivial.
    rewrite <- exp.pres_p0. do 2 rewrite <- exp.pres_p1.
    symmetry in H1. rewrite H1. rewrite sig.pres_p1. trivial. trivial.
    rewrite <- sig.pres_p0. rewrite <- exp.pres_p1. rewrite H1.
    rewrite <- exp.simulatorZK1; trivial. rewrite <- exp.simulatorZK2; trivial.
    rewrite <- exp.pres_p0. rewrite <- exp.pres_p1. trivial.
    (* and it bijects *)
    + pose (exp.simMapInvValid  e.1 (r.1,r.2.1) t.1 H0 H). destruct a0. split.
    ++ pose (exp.simMapHelpValid (exp.P0 s r.1 w).2
    (exp.P1 (exp.P0 s r.1 w, e.1) r.2.1 w).2 e.1 H).
    pose (exp.ToValid r.1 r.2.1 e.1 H0).  rewrite <- exp.pres_p0 in s0.
    rewrite <- exp.pres_p1 in s0. pose (a (exp.ToSt (exp.P1 (exp.P0 s r.1 w, e.1) r.2.1 w))
    (exp.ToWit (exp.P0 s r.1 w, e.1) r.1 r.2.1 w) e.2 (exp.sigXcomp s x)
    r.2.2 t.2 s0 i).
    destruct a0. rewrite <- exp.simulatorZK1; trivial.
    rewrite <- exp.simulatorZK2; trivial. destruct H4.
    rewrite H2. rewrite <- exp.pres_p0. rewrite <- exp.pres_p1.  rewrite H4.
    symmetry. simpl. rewrite <- surjective_pairing. apply surjective_pairing.
    ++ pose (exp.simMapHelpValid (exp.P0 s (exp.simMapInv s w e.1 x t.1).1 w).2
     (exp.P1 (exp.P0 s (exp.simMapInv s w e.1 x t.1).1 w, e.1)
        (exp.simMapInv s w e.1 x t.1).2 w).2 e.1 H).
    pose (exp.ToValid (exp.simMapInv s w e.1 x t.1).1
        (exp.simMapInv s w e.1 x t.1).2 e.1 H0).
    rewrite <- exp.pres_p0 in s0. rewrite <- exp.pres_p1 in s0.
    pose (a (exp.ToSt (exp.P1 (exp.P0 s
      (exp.simMapInv s w e.1 x t.1).1 w, e.1)(exp.simMapInv s w e.1 x t.1).2 w))
    (exp.ToWit ((exp.P0 s (exp.simMapInv s w e.1 x t.1).1 w), e.1)
    (exp.simMapInv s w e.1 x t.1).1 (exp.simMapInv s w e.1 x t.1).2 w)
    e.2 (exp.sigXcomp s x) r.2.2 t.2 s0 i).
     destruct a0. destruct H4. rewrite <- surjective_pairing. rewrite H1.
    apply injective_projections. trivial. simpl.
    assert (sig.simMapInv (exp.ToSt
     (exp.P1 (exp.P0 s (exp.simMapInv s w e.1 x t.1).1 w, e.1)
        (exp.simMapInv s w e.1 x t.1).2 w))
  (exp.ToWit (exp.P0 s (exp.simMapInv s w e.1 x t.1).1 w, e.1)
     (exp.simMapInv s w e.1 x t.1).1 (exp.simMapInv s w e.1 x t.1).2 w) e.2
     (exp.sigXcomp s x) t.2 =
   sig.simMapInv
     (exp.ToSt (s, (exp.simulator s t.1 e.1).1, e.1, (exp.simulator s t.1 e.1).2))
     (exp.ToWit (s, (exp.simulator s t.1 e.1).1, e.1) (exp.simMapInv s w e.1 x t.1).1
        (exp.simMapInv s w e.1 x t.1).2 w) e.2 (exp.sigXcomp s x) t.2).
    +++ apply f_equal5; trivial. rewrite exp.pres_p1.
    rewrite (exp.simulatorZK2 (exp.simMapInv s w e.1 x t.1) e.1 H0 H).
    rewrite exp.pres_p0. rewrite (exp.simulatorZK1 (exp.simMapInv s w e.1 x t.1)
    e.1 H0 H). rewrite H1. trivial. rewrite exp.pres_p0. rewrite
    (exp.simulatorZK1 (exp.simMapInv s w e.1 x t.1) e.1 H0 H). rewrite H1. trivial.
    +++ rewrite <- H6. apply H5.
  Qed.

  Lemma simulator_correct : forall (s : St)(t : TE0*TE1)(e : E0*E1),
    V2(simulator s t e) = true.
  Proof.
    intros. unfold V2. simpl. remember (sig.simulator
    (exp.ToSt (s, (exp.simulator s t.1 e.1).1, e.1, (exp.simulator s t.1 e.1).2))) as a.
    rewrite (sig.pres_sim (exp.ToSt (s, (exp.simulator s t.1 e.1).1, e.1,
    (exp.simulator s t.1 e.1).2)) t.2 e.2).
    rewrite <- Heqa. remember (a t.2 e.2) as b.
    rewrite (sig.chal_sim (exp.ToSt (s, (exp.simulator s t.1 e.1).1, e.1,
    (exp.simulator s t.1 e.1).2)) t.2 e.2).
    rewrite <- Heqa. rewrite <- Heqb. rewrite <- surjective_pairing.
    do 2 rewrite <- surjective_pairing. rewrite Heqb. rewrite Heqa.
    apply sig.simulator_correct.
  Qed.

End SigmaPlus5CompIns.

(* This is a simplified version of SigmaPlusTo5 for use with BGzero for example *)
Module Type SigmaPlusTo5sim (E0 : GroupSig)(sig : SigmaPlus E0).

  Parameter E : Set.

  Parameter St:Type.                                (* The set of statements *)
  Parameter W:Type.                                (* The set of witness *)
  Parameter Rel :St -> W -> bool.                  (* The relation function *)
  Parameter C : Type.                              (* The set of commitments *)

  Parameter R : Type.

  Parameter add : E -> E -> E.                   
  Parameter zero : E.     
  Parameter inv : E -> E.
  Parameter bool_eq : E -> E -> bool.
  Parameter disjoint : E -> E -> bool.  

  Parameter P0 : St -> R -> W -> (St*C).   

  Parameter ToSt : St*C*E -> sig.St.  
  Parameter ToWit : St*C*E -> R -> W -> sig.W.

  Axiom ToValid : forall s w r e,
    Rel s w ->
   sig.Rel (ToSt (P0 s r w, e)) (ToWit (P0 s r w, e) r w).

  Parameter TE : Type. 

  Axiom pres_p0 : forall (s : St)(r : R)(w : W), 
      (P0 s r w) = (s,(P0 s r w).2).

  Parameter extractor : sig.W -> E -> W.

  Parameter argument : St -> C -> E -> Prop.

  Axiom special_soundness : forall s c (e : E)
        (w : sig.W),
    sig.Rel (ToSt (s,c,e)) w ->
    Rel s (extractor w e) \/ argument s c e.

  Axiom e_abgrp : AbeGroup E add zero bool_eq disjoint inv.

  Parameter X : Type. 

  Parameter simulator : St -> TE -> E -> C.
  Parameter simMap    : St -> W -> E -> X -> R  ->  TE. 
  Parameter simMapInv : St -> W -> E -> X -> TE -> R.

  Parameter simMapHelp : St -> X -> Prop.

  Parameter sigXcomp : St -> X -> sig.X.

  Axiom simMapInvValid :  forall (st : St)(w : W)(x : X)
        (e : E)(r : R)(t : TE),
     Rel st w ->
     simMapHelp st x ->
    simMap st w e x (simMapInv st w e x t) = t /\
    simMapInv st w e x (simMap st w e x r) = r.

  (* This may need more preconditions otherwise it might be too strong *)
  Axiom simMapHelpValid : forall (st : St)(x : X)(c : C)(e : E),
    simMapHelp st x ->
    sig.simMapHelp (ToSt (st,c,e)) (sigXcomp st x).

  Axiom simulatorZK1 : forall s w r e x,
     Rel s w ->
     simMapHelp s x ->
     (P0 s r w).2 = (simulator s (simMap s w e x r) e).

End SigmaPlusTo5sim.

Module Type SigmaPlusTo5simTofull (E0 : GroupSig)(sig : SigmaPlus E0)
  (sigSim : SigmaPlusTo5sim E0 sig) <: SigmaPlusTo5 E0 sig.

  Definition E := sigSim.E.

  Definition St:Type := sigSim.St.                               
  Definition W:Type := sigSim.W.                                
  Definition Rel := sigSim.Rel.            
  Definition C := sigSim.C.                              

  Definition R := sigSim.R.

  Definition add := sigSim.add.                   
  Definition zero : E := sigSim.zero.     
  Definition inv : E -> E := sigSim.inv.
  Definition bool_eq : E -> E -> bool := sigSim.bool_eq.
  Definition disjoint : E -> E -> bool := sigSim.disjoint.

  Definition P0 : St -> R -> W -> (St*C) := sigSim.P0.  
  
  Definition C1 : Type := unit.                            
  Definition R1 : Type := unit.

  Definition P1 (sce : St*C*E)(r : R1)(w : W) : St*C*E*C1 :=
    (sce,tt).

  Definition ToSt (s : St*C*E*C1) : sig.St := sigSim.ToSt s.1.
  Definition ToWit (s : St*C*E)(r : R)(r1 : R1)(w : W) : sig.W :=
    sigSim.ToWit s r w.

  Lemma ToValid : forall s w r r1 e,
    Rel s w ->
   sig.Rel (ToSt (P1 (P0 s r w, e) r1 w)) (ToWit (P0 s r w, e) r r1 w).
  Proof.
    intros. unfold ToSt, P1. simpl. apply sigSim.ToValid. auto.
  Qed.

  Definition TE : Type := sigSim.TE.

  Lemma pres_p0 : forall (s : St)(r : R)(w : W), 
      (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. apply sigSim.pres_p0.
  Qed.

  Lemma pres_p1 : forall (s : St*C*E)(r : R1)(w : W), 
      (P1 s r w) = (s,(P1 s r w).2).
  Proof.
    intros. unfold P1. simpl. trivial.
  Qed.

  Definition M : nat := 1.

  Definition extractor (w : vector sig.W M)(e : vector E M) : W :=
    sigSim.extractor (Vhead w) (Vhead e).

  Definition fail_event (s : St)(c : C)(e : vector E M) : Prop :=
    sigSim.argument s c (Vhead e).

  Lemma special_soundness : forall s c (e : vector E M)(c1 : vector C1 M)
        (w : vector sig.W M),
    bVforall3 (fun a b d => sig.Rel (ToSt (s,c,a,b)) d) e c1 w ->
    PairwisePredicate (fun a b => disjoint a b) e  ->
    Rel s (extractor w e) \/ fail_event s c e.
  Proof.
    intros. apply bVforall3_elim_head in H. 
    apply sigSim.special_soundness in H. apply H.
  Qed.

  Lemma e_abgrp : AbeGroup E add zero bool_eq disjoint inv.
  Proof.
    apply sigSim.e_abgrp.
  Qed.

  Definition X : Type := sigSim.X.

  Definition simulator (s : St)(t : TE)(e : E) : C*C1 := 
    (sigSim.simulator s t e, tt).
  Definition simMap    (s : St)(w : W)(e : E)(x : X)(r : R*R1) : TE := 
    sigSim.simMap s w e x r.1.
  Definition simMapInv (s : St)(w : W)(e : E)(x : X)(t : TE) : R*R1 :=
    (sigSim.simMapInv s w e x t, tt).

  Definition simMapHelp (s : St)(x : X) : Prop := sigSim.simMapHelp s x.

  Definition sigXcomp   (s : St)(x : X) : sig.X := sigSim.sigXcomp s x.

  Lemma simMapInvValid :  forall (st : St)(w : W)(x : X)
        (e : E)(r : R*R1)(t : TE),
     Rel st w ->
     simMapHelp st x ->
    simMap st w e x (simMapInv st w e x t) = t /\
    simMapInv st w e x (simMap st w e x r) = r.
  Proof.
    intros. unfold simMap, simMapInv. simpl. split. apply sigSim.simMapInvValid; 
    trivial. apply r.1. destruct r. destruct r0. simpl. apply injective_projections; 
    simpl. apply sigSim.simMapInvValid; trivial. trivial.
  Qed.

  (* This may need more preconditions otherwise it might be too strong *)
  Lemma simMapHelpValid : forall (st : St)(x : X)(c : C)(c1 : C1)(e : E),
    simMapHelp st x ->
    sig.simMapHelp (ToSt (st,c,e,c1)) (sigXcomp st x).
  Proof.
    intros. apply sigSim.simMapHelpValid. trivial.
  Qed.

  Lemma simulatorZK1 : forall s w r e x,
     Rel s w ->
     simMapHelp s x ->
     (P0 s r.1 w).2 = (simulator s (simMap s w e x r) e).1.
  Proof.
    intros. apply sigSim.simulatorZK1; trivial.
  Qed.

  Lemma simulatorZK2 : forall s w r e x,
     Rel s w ->
     simMapHelp s x ->
      (P1 (P0 s r.1 w, e) r.2 w).2 = 
      (simulator s (simMap s w e x r) e).2.
  Proof.
    intros. simpl. trivial.
  Qed.

End SigmaPlusTo5simTofull.

Module SigmaPlusTo5simTofullIns (E0 : GroupSig)(sig : SigmaPlus E0)
  (sigSim : SigmaPlusTo5sim E0 sig) <: SigmaPlusTo5simTofull E0 sig sigSim.

  Definition E := sigSim.E.

  Definition St:Type := sigSim.St.
  Definition W:Type := sigSim.W.
  Definition Rel := sigSim.Rel.
  Definition C := sigSim.C.

  Definition R := sigSim.R.

  Definition add := sigSim.add.
  Definition zero : E := sigSim.zero.
  Definition inv : E -> E := sigSim.inv.
  Definition bool_eq : E -> E -> bool := sigSim.bool_eq.
  Definition disjoint : E -> E -> bool := sigSim.disjoint.

  Definition P0 : St -> R -> W -> (St*C) := sigSim.P0.
  
  Definition C1 : Type := unit.
  Definition R1 : Type := unit.

  Definition P1 (sce : St*C*E)(r : R1)(w : W) : St*C*E*C1 :=
    (sce,tt).

  Definition ToSt (s : St*C*E*C1) : sig.St := sigSim.ToSt s.1.
  Definition ToWit (s : St*C*E)(r : R)(r1 : R1)(w : W) : sig.W :=
    sigSim.ToWit s r w.

  Lemma ToValid : forall s w r r1 e,
    Rel s w ->
   sig.Rel (ToSt (P1 (P0 s r w, e) r1 w)) (ToWit (P0 s r w, e) r r1 w).
  Proof.
    intros. unfold ToSt, P1. simpl. apply sigSim.ToValid. auto.
  Qed.

  Definition TE : Type := sigSim.TE.

  Lemma pres_p0 : forall (s : St)(r : R)(w : W),
      (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. apply sigSim.pres_p0.
  Qed.

  Lemma pres_p1 : forall (s : St*C*E)(r : R1)(w : W),
      (P1 s r w) = (s,(P1 s r w).2).
  Proof.
    intros. unfold P1. simpl. trivial.
  Qed.

  Definition M : nat := 1.

  Definition extractor (w : vector sig.W M)(e : vector E M) : W :=
    sigSim.extractor (Vhead w) (Vhead e).

  Definition fail_event (s : St)(c : C)(e : vector E M) : Prop :=
    sigSim.argument s c (Vhead e).

  Lemma special_soundness : forall s c (e : vector E M)(c1 : vector C1 M)
        (w : vector sig.W M),
    bVforall3 (fun a b d => sig.Rel (ToSt (s,c,a,b)) d) e c1 w ->
    PairwisePredicate (fun a b => disjoint a b) e  ->
    Rel s (extractor w e) \/ fail_event s c e.
  Proof.
    intros. apply bVforall3_elim_head in H.
    apply sigSim.special_soundness in H. apply H.
  Qed.

  Lemma e_abgrp : AbeGroup E add zero bool_eq disjoint inv.
  Proof.
    apply sigSim.e_abgrp.
  Qed.

  Definition X : Type := sigSim.X.

  Definition simulator (s : St)(t : TE)(e : E) : C*C1 :=
    (sigSim.simulator s t e, tt).
  Definition simMap    (s : St)(w : W)(e : E)(x : X)(r : R*R1) : TE :=
    sigSim.simMap s w e x r.1.
  Definition simMapInv (s : St)(w : W)(e : E)(x : X)(t : TE) : R*R1 :=
    (sigSim.simMapInv s w e x t, tt).

  Definition simMapHelp (s : St)(x : X) : Prop := sigSim.simMapHelp s x.

  Definition sigXcomp   (s : St)(x : X) : sig.X := sigSim.sigXcomp s x.

  Lemma simMapInvValid :  forall (st : St)(w : W)(x : X)
        (e : E)(r : R*R1)(t : TE),
     Rel st w ->
     simMapHelp st x ->
    simMap st w e x (simMapInv st w e x t) = t /\
    simMapInv st w e x (simMap st w e x r) = r.
  Proof.
    intros. unfold simMap, simMapInv. simpl. split. apply sigSim.simMapInvValid;
    trivial. apply r.1. destruct r. destruct r0. simpl. apply injective_projections;
    simpl. apply sigSim.simMapInvValid; trivial. trivial.
  Qed.

  (* This may need more preconditions otherwise it might be too strong *)
  Lemma simMapHelpValid : forall (st : St)(x : X)(c : C)(c1 : C1)(e : E),
    simMapHelp st x ->
    sig.simMapHelp (ToSt (st,c,e,c1)) (sigXcomp st x).
  Proof.
    intros. apply sigSim.simMapHelpValid. trivial.
  Qed.

  Lemma simulatorZK1 : forall s w r e x,
     Rel s w ->
     simMapHelp s x ->
     (P0 s r.1 w).2 = (simulator s (simMap s w e x r) e).1.
  Proof.
    intros. apply sigSim.simulatorZK1; trivial.
  Qed.

  Lemma simulatorZK2 : forall s w r e x,
     Rel s w ->
     simMapHelp s x ->
      (P1 (P0 s r.1 w, e) r.2 w).2 =
      (simulator s (simMap s w e x r) e).2.
  Proof.
    intros. simpl. trivial.
  Qed.

End SigmaPlusTo5simTofullIns.

(* We are going to define a new combiner to make the product argument in BG *)

Module Type SigmaPlus5To5 (E0 : GroupSig)(sig : SigmaPlus E0)(sig5 : SigmaPlus5).

  Parameter St:Type.                                (* The set of statements *)
  Parameter W:Type.                                (* The set of witness *)
  Parameter Rel :St -> W -> bool.                  (* The relation function *)
  Parameter C : Type.                              (* The set of commitments *)

  Parameter R : Type.

  Parameter P0 : St -> R -> W -> (St*C).   

  Parameter ToStSig : St*C -> sig.St.  
  Parameter ToWitSig : St*C -> R -> W -> sig.W.

  Parameter ToStSig5 : St*C -> sig5.St.  
  Parameter ToWitSig5 : St*C -> R -> W -> sig5.W.

  Axiom ToValid : forall s w r,
    Rel s w ->
   sig.Rel (ToStSig (P0 s r w)) (ToWitSig (P0 s r w) r w) /\
   sig5.Rel (ToStSig5 (P0 s r w)) (ToWitSig5 (P0 s r w) r w).

  Parameter TE : Type. 

  Axiom pres_p0 : forall (s : St)(r : R)(w : W), 
      (P0 s r w) = (s,(P0 s r w).2).

  Parameter extractor :  sig5.W -> sig.W -> W.

  Parameter argument : St -> C -> Prop.

  Axiom M1_nonzero : sig5.M1 > 0. (* This is an edge case we had to take care of *) 

  Axiom special_soundness : forall s c (w : sig.W)(w1 : sig5.W),
    sig.Rel (ToStSig (s,c)) w ->
    sig5.Rel (ToStSig5 (s,c)) w1 ->
    Rel s (extractor w1 w) \/ argument s c.

  Parameter X : Type. 

  Parameter simulator : St -> TE -> C.
  Parameter simMap    : St -> W -> X -> R  ->  TE. 
  Parameter simMapInv : St -> W -> X -> TE -> R.

  Parameter simMapHelp : St -> X -> Prop.

  Parameter sigXcomp : St -> X -> sig.X.
  Parameter sig5Xcomp : St -> X -> sig5.X.

  Axiom simMapInvValid :  forall (st : St)(w : W)(x : X)(r : R)(t : TE),
     Rel st w ->
     simMapHelp st x ->
    simMap st w x (simMapInv st w x t) = t /\
    simMapInv st w x (simMap st w x r) = r.

  (* This may need more preconditions otherwise it might be too strong *)
  Axiom simMapHelpValid : forall (st : St)(x : X)(c : C),
    simMapHelp st x ->
    sig.simMapHelp  (ToStSig (st,c)) (sigXcomp st x) /\
    sig5.simMapHelp (ToStSig5 (st,c)) (sig5Xcomp st x).

  Axiom simulatorZK1 : forall s w r x,
     Rel s w ->
     simMapHelp s x ->
     (P0 s r w).2 = (simulator s (simMap s w x r)).

End SigmaPlus5To5. 

Module Type SigmaPlus5to5Comp (E : GroupSig)(sig : SigmaPlus E)(sig5 : SigmaPlus5)
    (exp : SigmaPlus5To5 E sig sig5) <: SigmaPlus5.

  Definition E0 : Set := sig5.E0*E.G.
  Definition E1 : Set := sig5.E1.
  
   Definition St:Type := exp.St.
   Definition W:Type := exp.W.                
   Definition Rel :St -> W -> bool := exp.Rel.
   Definition C0 : Type := exp.C*sig5.C0*sig.C.             
   Definition C1 : Type := sig5.C1.

   Definition R0 : Type := exp.R*sig5.R0*sig.R.    
   Definition R1 : Type := sig5.R1.  
          
   Definition add0 (a b : E0) : E0 := (sig5.add0 a.1 b.1, E.Gdot a.2 b.2).                   
   Definition zero0 : E0 := (sig5.zero0,E.Gone).      
   Definition inv0 (a : E0) : E0 := (sig5.inv0 a.1, E.Ginv a.2).
   Definition bool_eq0 (a b : E0) : bool := sig5.bool_eq0 a.1 b.1 && 
                                              E.Gbool_eq a.2 b.2.
   Definition disjoint0 (a b : E0) : bool := sig5.disjoint0 a.1 b.1 &&
                                             E.Gdisjoint a.2 b.2. 

   Definition add1 : E1 -> E1 -> E1 := sig5.add1.                   
   Definition zero1 : E1 := sig5.zero1.      
   Definition inv1 : E1 -> E1 := sig5.inv1.
   Definition bool_eq1 : E1 -> E1 -> bool := sig5.bool_eq1.
   Definition disjoint1 : E1 -> E1 -> bool := sig5.disjoint1.

   Definition T : Type := sig5.T*sig.T.             
                
   Definition P0 (s : St)(r : R0)(w : W) : (St*C0) := 
      let '(r, r', r'') := r in
      let c := exp.P0 s r w in

      (s,(c.2,(sig5.P0 (exp.ToStSig5 c) r' (exp.ToWitSig5 c r w)).2,
      (sig.P0 (exp.ToStSig c) r'' (exp.ToWitSig c r w)).2)).

   Definition P1 (tran : St*C0*E0)(r : R0*R1)(w : W) : (St*C0*E0*C1) :=
    let '(s, (c, c',c''), (e,e')) := tran in
    let '(r, r', r'',r''') := r in
  
    (tran, (sig5.P1 ((exp.ToStSig5 (s,c)),c',e) (r', r''') 
      (exp.ToWitSig5 (s,c) r w)).2).        

   Definition P2 (tran : St*C0*E0*C1*E1)(r : R0*R1)(w : W) : (St*C0*E0*C1*E1*T) := 
    let '(s, (c, c', c''), (e, e'), c1, e1) := tran in
    let '(r, r', r'',r''') := r in

    (tran, ((sig5.P2 ((exp.ToStSig5 (s,c)),c',e,c1,e1) (r',r''') 
      (exp.ToWitSig5 (s,c) r w)).2,
    (sig.P1 (exp.ToStSig (s, c),c'',e') r'' 
      (exp.ToWitSig (s,c) r w)).2)). 

   Definition V2 (tran : St*C0*E0*C1*E1*T) : bool :=
      let '(s, (c, c', c''), e, c1, e1, t) := tran in
      sig5.V2 (exp.ToStSig5 (s,c),c',e.1,c1,e1,t.1) &&
      sig.V1 (exp.ToStSig (s, c),c'',e.2,t.2).           

   Definition TE0 : Type := exp.TE*sig5.TE0*sig.TE.                            
   Definition TE1 : Type := sig5.TE1. 

   Definition X  : Type := exp.X. 
   Definition simMapHelp (s : St)(x : X) : Prop := exp.simMapHelp s x.
                                           
   Definition simulator (st : St)(t : TE0*TE1)(e : E0*E1) : (St*C0*E0*C1*E1*T) :=
    let '((t,t',t''),(t''')) := t in
    let '((e,e'),e'') := e in 

    let c   := exp.simulator st t in
    let a  := sig5.simulator (exp.ToStSig5 (st,c)) (t',t''') (e,e'') in
    let b     := sig.simulator (exp.ToStSig (st,c))  t'' e' in 

    (st, (c,a.1.1.1.1.2,b.1.1.2),(e,e'),a.1.1.2,e'',(a.2,b.2)).

   Definition simMap (st : St)(w : W)(e : E0*E1)(x : X)(r : R0*R1) : (TE0*TE1) :=
    let '((e,e'),e'') := e in 
    let '(r, r', r'',r''') := r in

    (exp.simMap st w x r, (sig5.simMap (exp.ToStSig5 (exp.P0 st r w)) 
      (exp.ToWitSig5 (exp.P0 st r w) r w) (e,e'') (exp.sig5Xcomp st x) (r',r''')).1,
      sig.simMap (exp.ToStSig (exp.P0 st r w))  
        (exp.ToWitSig (exp.P0 st r w) r w) e' (exp.sigXcomp st x) r'',
    (sig5.simMap (exp.ToStSig5 (exp.P0 st r w)) 
      (exp.ToWitSig5 (exp.P0 st r w) r w) (e,e'') (exp.sig5Xcomp st x) (r',r''')).2).
          
   Definition simMapInv (st : St)(w : W)(e : E0*E1)(x : X)(t : TE0*TE1) : (R0*R1) :=
    let '((e,e'),e'') := e in 
    let '(t, t', t'',t''') := t in
    let r := exp.simMapInv st w x t in

    (r, (sig5.simMapInv (exp.ToStSig5 (st,(exp.simulator st t))) 
      (exp.ToWitSig5 (st,(exp.simulator st t)) r w) (e,e'') (exp.sig5Xcomp st x) (t',t''')).1,
      sig.simMapInv (exp.ToStSig (exp.P0 st r w))  
        (exp.ToWitSig (exp.P0 st r w) r w) e' (exp.sigXcomp st x) t'',
    (sig5.simMapInv (exp.ToStSig5 (exp.P0 st r w)) 
      (exp.ToWitSig5 (exp.P0 st r w) r w) (e,e'') (exp.sig5Xcomp st x) (t',t''')).2).

   Definition M0 : nat := max sig5.M0 sig.M.
   Definition M1 : nat := S (Nat.pred sig5.M1).

   Lemma M1_cast : S (Nat.pred sig5.M1) = sig5.M1.
   Proof.
    intros. pose exp.M1_nonzero. lia.
   Qed.
   Lemma M0_sub_1 : 0+sig5.M0 <= max sig5.M0 sig.M.
   Proof.
    intros. apply Nat.le_max_l.
   Qed.

   Lemma M0_sub_2 : 0+sig.M <= max sig5.M0 sig.M.
   Proof.
    intros. apply Nat.le_max_r.
   Qed.

   Definition extractor (t : vector (vector T M1) M0)(e : vector (E0*(vector E1 M1)) M0) : W := 
    exp.extractor (sig5.extractor (Vsub (Vmap (fun a => Vcast (UnzipLeft a) M1_cast) t) M0_sub_1)
                         (Vsub (Vmap (fun a => (a.1.1, Vcast a.2 M1_cast)) e) M0_sub_1))
     (sig.extractor (Vsub (Vmap (fun a => Vhead (UnzipRight a)) t) M0_sub_2)
                                          (Vsub (UnzipRight (UnzipLeft e)) M0_sub_2)).

   Definition fail_event (t : St)(c : C0*(vector C1 M0))(e :vector (E0*(vector E1 M1)) M0) : Prop :=
    exp.argument t c.1.1.1 \/
    sig5.fail_event (exp.ToStSig5 (t,c.1.1.1)) (c.1.1.2,Vsub c.2 M0_sub_1) 
    (Vmap (fun a => (a.1.1, Vcast a.2 M1_cast)) (Vsub e M0_sub_1)) \/
    (sig.fail_event (exp.ToStSig (t,c.1.1.1)) 
    c.1.2 (Vsub (UnzipRight (UnzipLeft e)) M0_sub_2)).
     
  Lemma e_abgrp0 : AbeGroup E0 add0 zero0 bool_eq0 disjoint0 inv0.
  Proof.
    pose sig5.e_abgrp0. pose E.module_abegrp. destruct a, a0. destruct abegrp_grp, 
    abegrp_grp0. destruct grp_mon. destruct grp_mon0.
    constructor. constructor. constructor.
    + intros. unfold add0. apply injective_projections; simpl. apply sig5.e_abgrp0.
    apply E.module_abegrp.
    + intros. unfold add0. apply injective_projections; simpl. apply sig5.e_abgrp0.
    apply E.module_abegrp.
    + intros. unfold add0. apply injective_projections; simpl. apply sig5.e_abgrp0.
    apply E.module_abegrp.
    + intros. unfold bool_eq0. destruct a, b. split; intros.
    apply andb_true_iff in H. destruct H. apply sig5.e_abgrp0 in H.
    apply E.module_abegrp in H0. simpl in *. rewrite H. rewrite H0. trivial.
    rewrite H. apply andb_true_iff. split. apply sig5.e_abgrp0; trivial.
    apply E.module_abegrp; trivial.
    + intros. unfold bool_eq0. destruct a, b. rewrite bool_eq_sym0.
    rewrite bool_eq_sym. trivial.
    + intros. unfold bool_eq0. destruct a, b. split; intros.
    apply andb_false_iff in H. destruct H. apply bool_neq_corr in H.
    unfold not in *. intros. apply H. rewrite H0. trivial.
    apply bool_neq_corr0 in H. unfold not in *. intros. apply H. rewrite H0. trivial.
    apply andb_false_iff. case_eq (sig5.bool_eq0 e e0); intros. 
    apply bool_eq_corr in H0.  case_eq (E.Gbool_eq g g0); intros.
    apply bool_eq_corr0 in H1. assert False.  apply H. rewrite H0. rewrite H1.
    trivial. contradiction. right. apply H1. left. apply H0.
    + intros. unfold disjoint0. rewrite disjoint_sym0. rewrite disjoint_sym. trivial.
    + intros. unfold disjoint0 in *. apply andb_true_iff in H. destruct H.
    apply disjoint_corr in H. apply disjoint_corr0 in H0. unfold not in *.
    intros. apply H. rewrite H1. trivial.
    + intros. unfold add0, zero0, inv0. destruct x. apply injective_projections; simpl. 
    apply inv_left. apply inv_left0.
    + intros. unfold add0. apply injective_projections; simpl. apply inv_right.
    apply inv_right0.
    + intros. unfold add0. apply injective_projections; simpl. apply comm.
    apply comm0.
  Qed.

  Lemma e_abgrp1 : AbeGroup E1 add1 zero1 bool_eq1 disjoint1 inv1.
  Proof.
    apply sig5.e_abgrp1.
  Qed. 
  
  (** We require the functions do not modifiy the previous transcript *)
  Lemma pres_p0 : forall (s : St)(r : R0)(w : W), 
      (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. unfold P0. destruct r.  destruct p. simpl. trivial.
  Qed.

  Lemma pres_p1 : forall (sce : St*C0*E0)(r : R0*R1)(w : W), 
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Proof.
    intros. unfold P1. destruct sce. destruct p. destruct c. destruct p, e, r.
    destruct r, p. simpl. trivial.
  Qed.

  Lemma pres_p2 : forall (sce : St*C0*E0*C1*E1)(r : R0*R1)(w : W), 
    (P2 sce r w) = (sce,(P2 sce r w).2).
  Proof.
    intros. unfold P2. destruct sce. destruct p, r. destruct p, r.
    destruct p, e0, p0. destruct c0, p. simpl. trivial.
  Qed.
  
  Lemma pres_sim : forall (s: St)(t : TE0*TE1)(e : E0*E1),
     s = (simulator s t e).1.1.1.1.1.
  Proof.
    intros. unfold simulator. destruct t, e. destruct t, e. destruct p. simpl. 
    trivial.
  Qed.

  Lemma chal_sim0 : forall (s: St)(t : TE0*TE1)(e : E0*E1),
    e.1 = (simulator s t e).1.1.1.2.
  Proof.
    intros. unfold simulator. destruct t, e. destruct t, e. destruct p. simpl.
    trivial.
  Qed.
  
  Lemma chal_sim1 : forall (s: St)(t : TE0*TE1)(e : E0*E1),
    e.2 = (simulator s t e).1.2. 
  Proof.
    intros. unfold simulator. destruct t, e. destruct t, e. destruct p. simpl.
    trivial.
  Qed. 

  (** Properties *)
  Lemma correctness : forall (s :St)(w:W)(r0:R0)(r1:R1)(c0: E0)(c1 : E1),
    Rel s w ->
    V2 (P2 
      ((P1 ((P0 s r0 w), c0) (r0,r1) w), c1)
   (r0,r1) w) = true.
  Proof.
    intros. unfold V2, P2, P1, P0. destruct r0. simpl. destruct p, c0. simpl.
    apply andb_true_iff. split.
    + rewrite <- exp.pres_p0. rewrite <- sig5.pres_p0. rewrite <- sig5.pres_p1. 
    rewrite <- sig5.pres_p2. rewrite sig5.correctness; auto. apply exp.ToValid; auto.
    + rewrite <- sig.pres_p1. rewrite <- exp.pres_p0. rewrite <- sig.pres_p0.  apply sig.correctness. 
     apply exp.ToValid; auto.
  Qed.

  
  Definition allDifferent (e : vector (E0*vector E1 M1) M0) :=
    PairwisePredicate disjoint0 (UnzipLeft e) /\
      bVforall (fun a => PairwisePredicate disjoint1 a.2) e.

  Definition allValid  (s : St)(c0 : C0)(c1 : vector C1 M0)
        (e : vector (E0*vector E1 M1) M0)
        (t : vector (vector T M1) M0) :=
    bVforall3 (fun c e0 t0 => 
      bVforall2 (fun e1 t1 => V2 (s, c0, e0.1, c, e1, t1)) e0.2 t0) c1 e t.
  
  Lemma special_soundness : forall (s : St)(c0 : C0)(c1 : vector C1 M0)
        (e : vector (E0*vector E1 M1) M0)
        (t : vector (vector T M1) M0),
      (* Forall e it is disjoint from all e *)
      allDifferent e ->
      allValid s c0 c1 e t ->
    Rel s (extractor t e) = true \/ fail_event s (c0,c1) e.
  Proof.
    intros. unfold fail_event, extractor. simpl.
    assert (sig.Rel (exp.ToStSig (s, c0.1.1)) (sig.extractor (Vsub
    (Vmap (fun a => Vhead (UnzipRight a)) t) M0_sub_2) 
    (Vsub (UnzipRight (UnzipLeft e)) M0_sub_2)) = true \/
    sig.fail_event (exp.ToStSig (s, c0.1.1)) c0.2
    (Vsub (UnzipRight (UnzipLeft e)) M0_sub_2)).
    + apply sig.special_soundness. destruct H. apply PairwisePredicateSplitUnzip in H.
    apply andb_true_iff in H. destruct H. apply (PairwisePredicate_sub 0 sig.M M0_sub_2) in H2. auto.
    apply E.module_abegrp. unfold allValid in H0.  unfold V2 in H0. 
    apply bVforall2_nth_intro. intros. do 2 rewrite Vnth_sub. 
    apply (bVforall3_elim_nth (Vnth_sub_aux 0 M0_sub_2 ip)) in H0.
    apply bVforall2_elim_head in H0. do 3 rewrite Vnth_map. destruct c0, p.
    apply andb_true_iff in H0. destruct H0. simpl. rewrite Vhead_map.  apply H1.
    + destruct H1. 
    ++ assert (sig5.Rel (exp.ToStSig5 (s, c0.1.1))
    (sig5.extractor (Vsub (Vmap (fun a => Vcast (UnzipLeft a) M1_cast) t) M0_sub_1)
        (Vsub (Vmap (fun a => (a.1.1, Vcast a.2 M1_cast)) e) M0_sub_1)) \/
    sig5.fail_event (exp.ToStSig5 (s, c0.1.1)) (c0.1.2, Vsub c1 M0_sub_1)
      (Vmap (fun a => (a.1.1, Vcast a.2 M1_cast)) (Vsub e M0_sub_1))).
    +++ rewrite Vsub_map. destruct H. apply sig5.special_soundness.
    ++++ apply (PairwisePredicate_sub 0 sig5.M0 M0_sub_1) in H.
         apply PairwisePredicateSplitUnzip in H. apply andb_true_iff in H. destruct H.
         split.
    apply PairwisePredicateVnth. intros. 
    assert (forall a b : sig5.E0, sig5.disjoint0 a b = sig5.disjoint0 b a).
    apply sig5.e_abgrp0. pose (PairwisePredicateVnth2 sig5.disjoint0 H5 
    (UnzipLeft (Vsub (UnzipLeft e) M0_sub_1)) H ip jp H4). do 2 rewrite Vnth_map.
    do 2 rewrite Vnth_sub.  do 2 rewrite Vnth_map. simpl.
    assert (sig5.disjoint0 (Vnth (UnzipLeft (Vsub (UnzipLeft e) M0_sub_1)) ip)
     (Vnth (UnzipLeft (Vsub (UnzipLeft e) M0_sub_1)) jp)). trivial.
    do 2 rewrite Vnth_map in H6. do 2 rewrite Vnth_sub in H6. 
    do 2 rewrite Vnth_map in H6. trivial. intros. 
    +++++ apply bVforall_nth_intro. intros. rewrite Vnth_sub.  
    apply (bVforall_elim_nth (Vnth_sub_aux 0 M0_sub_1 ip)) in H2.
    rewrite Vnth_map. simpl. apply PairwisePredicate_cast. 
    apply sig5.e_abgrp1. apply H2.
    +++++
    intros. unfold disjoint0. 
    replace (sig5.disjoint0 a.1 b.1) with (sig5.disjoint0 b.1 a.1).
    replace (E.Gdisjoint a.2 b.2) with (E.Gdisjoint b.2 a.2).
    trivial. apply E.module_abegrp. apply sig5.e_abgrp0. 
    ++++ apply bVforall3_nth_intro. intros. do 3 rewrite Vnth_sub.
    apply (bVforall3_elim_nth (Vnth_sub_aux 0 M0_sub_1 ip)) in H0. unfold V2 in H0.
    apply bVforall2_nth_intro. intros. do 2 rewrite Vnth_map. rewrite Vnth_cast.
    simpl. apply (bVforall2_elim_nth (Vnth_cast_aux M1_cast ip0)) in H0.
    destruct c0, p. apply andb_true_iff in H0. destruct H0. simpl in *.
    rewrite Vnth_cast. rewrite Vnth_map. apply H0.
    +++ destruct H2. pose (exp.special_soundness H1 H2). destruct o.    
    left; auto. right. left; auto. right. right. left. apply H2.
    ++ right. right. right. auto.
  Qed.

  Lemma honest_verifier_ZK :
    forall (s : St)(w : W)(e : E0*E1)(x : X)(r : R0*R1)(t : TE0*TE1),
      simMapHelp s x ->
      Rel s w ->
      (P2 ((P1 ((P0 s r.1 w), e.1) r w), e.2) r w =
      simulator s (simMap s w e x r) e) /\ 
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.
  Proof.
    intros. unfold V2, P2, P1, P0, simulator, simMap, simMapInv. 
    destruct r, e, r, e, p, t, t, p. simpl.
    unfold simMapHelp in H. pose (exp.simMapHelpValid (exp.P0 s r1 w).2 H).
    destruct a. rewrite <- exp.pres_p0 in H1. rewrite <- exp.pres_p0 in H2.
    pose (exp.ToValid r1 H0). destruct a. 
    pose (sig5.honest_verifier_ZK (e,e0) (r2, r0) (t2, t0) H2 H4). 
    pose (sig.honest_verifier_ZK g r t H1 H3). destruct a, a0.
    destruct H8, H6. split.
    (* The map work *)
    + intros.
    apply injective_projections; simpl. apply injective_projections; simpl. 
    apply injective_projections; simpl. apply injective_projections; simpl.
    apply injective_projections; simpl.
    ++ trivial.
    ++ rewrite exp.pres_p0. rewrite <- (exp.simulatorZK1 r1 H0 H). 
    apply injective_projections; simpl. apply injective_projections; simpl. 
    trivial. do 2 rewrite <- exp.pres_p0. rewrite <- surjective_pairing.
    rewrite <- H5. rewrite sig5.pres_p1. rewrite sig5.pres_p2. simpl. trivial.
    do 2 rewrite <- exp.pres_p0. rewrite <- H7. rewrite sig.pres_p1. simpl. trivial.
    ++ trivial.
    ++  rewrite <- (exp.simulatorZK1 r1 H0 H). rewrite <- exp.pres_p0. 
    rewrite <- surjective_pairing. rewrite <- H5. rewrite sig5.pres_p2. simpl. 
    rewrite <- sig5.pres_p0. trivial.
    ++ trivial.
    ++ rewrite <- (exp.simulatorZK1 r1 H0 H). apply injective_projections; simpl. 
    rewrite <- exp.pres_p0. rewrite <- surjective_pairing. rewrite <- H5.
    rewrite <- sig5.pres_p1. rewrite <- sig5.pres_p0. trivial.
    rewrite <- exp.pres_p0. rewrite <- H7. rewrite <- sig.pres_p0. trivial.  
    (* and it bijects *)
    + pose (exp.simMapInvValid r1 t1 H0 H). destruct a. split.
    ++ (* First direction *)
    apply injective_projections; simpl. apply injective_projections; simpl. 
    apply injective_projections; simpl. 
    +++ apply H12. 
    +++ rewrite <- (exp.simulatorZK1 r1 H0 H). rewrite <- exp.pres_p0.
    rewrite H12. rewrite <- surjective_pairing. rewrite H6. trivial.
    +++ rewrite H12. rewrite H8. trivial.
    +++ rewrite H12. rewrite <- surjective_pairing. rewrite H6. trivial.
    ++ (* Second direction *)
    clear H12 H9 H8 H7 H10 H6 H5 H1 H2 H3 H3 H4.
    pose (exp.ToValid (exp.simMapInv s w x t1) H0). destruct a.
    pose (exp.simMapHelpValid (exp.P0 s (exp.simMapInv s w x t1) w).2 H).
    destruct a. rewrite <- exp.pres_p0 in H3. rewrite <- exp.pres_p0 in H4.
    pose (sig5.honest_verifier_ZK (e,e0) (r2, r0) (t2, t0) H4 H2). 
    pose (sig.honest_verifier_ZK g r t H3 H1). destruct a, a0.
    destruct H8, H6. rewrite exp.pres_p0 in H10.
    rewrite (exp.simulatorZK1 (exp.simMapInv s w x t1) H0 H) in H10.
    rewrite H11 in H10.
    apply injective_projections; simpl. apply injective_projections; simpl.
    apply injective_projections; simpl. 
    +++ apply H11.
    +++ rewrite exp.pres_p0. rewrite (exp.simulatorZK1 (exp.simMapInv s w x t1) H0 H).
    rewrite H11. rewrite <- surjective_pairing. rewrite H10. trivial.
    +++ rewrite H9. trivial.
    +++ rewrite exp.pres_p0. rewrite (exp.simulatorZK1 (exp.simMapInv s w x t1) H0 H).
    rewrite H11. rewrite <- surjective_pairing. rewrite H10. trivial.
  Qed. 

  Lemma simulator_correct : forall (s : St)(t : TE0*TE1)(e : E0*E1),
    V2(simulator s t e) = true.
  Proof.
    intros. unfold V2, simulator. destruct t, e, t, e, p. simpl. apply andb_true_iff.
    split.
    + remember ((sig5.simulator (exp.ToStSig5 (s, exp.simulator s t1)) (t2, t0) (e, e0))) as a. 
    rewrite (sig5.pres_sim (exp.ToStSig5 (s, exp.simulator s t1)) (t2, t0) (e,e0)).
    rewrite <-Heqa. replace e with (e,e0).1. replace e0 with (e,e0).2.
    rewrite (sig5.chal_sim0 (exp.ToStSig5 (s, exp.simulator s t1)) (t2, t0) (e, e0)).
    rewrite <- Heqa. rewrite (sig5.chal_sim1 (exp.ToStSig5 (s, exp.simulator s t1)) 
    (t2, t0) (e, e0)). rewrite <- Heqa. do 5 rewrite <- surjective_pairing. 
    rewrite Heqa. apply sig5.simulator_correct. auto. auto.
    + remember (sig.simulator (exp.ToStSig (s, exp.simulator s t1)) t g) as a.
    rewrite (sig.pres_sim (exp.ToStSig (s, exp.simulator s t1)) t g).
    rewrite <- Heqa. rewrite (sig.chal_sim (exp.ToStSig (s, exp.simulator s t1)) t g).
    rewrite <- Heqa. do 3 rewrite <- surjective_pairing. rewrite Heqa.
    apply sig.simulator_correct.
  Qed.  

End SigmaPlus5to5Comp.

Module SigmaPlus5to5CompIns (E : GroupSig)(sig : SigmaPlus E)(sig5 : SigmaPlus5)
    (exp : SigmaPlus5To5 E sig sig5) <: SigmaPlus5to5Comp E sig sig5 exp.

  Definition E0 : Set := sig5.E0*E.G.
  Definition E1 : Set := sig5.E1.
  
   Definition St:Type := exp.St.
   Definition W:Type := exp.W.
   Definition Rel :St -> W -> bool := exp.Rel.
   Definition C0 : Type := exp.C*sig5.C0*sig.C.
   Definition C1 : Type := sig5.C1.

   Definition R0 : Type := exp.R*sig5.R0*sig.R.
   Definition R1 : Type := sig5.R1.
          
   Definition add0 (a b : E0) : E0 := (sig5.add0 a.1 b.1, E.Gdot a.2 b.2).
   Definition zero0 : E0 := (sig5.zero0,E.Gone).
   Definition inv0 (a : E0) : E0 := (sig5.inv0 a.1, E.Ginv a.2).
   Definition bool_eq0 (a b : E0) : bool := sig5.bool_eq0 a.1 b.1 &&
                                              E.Gbool_eq a.2 b.2.
   Definition disjoint0 (a b : E0) : bool := sig5.disjoint0 a.1 b.1 &&
                                             E.Gdisjoint a.2 b.2.

   Definition add1 : E1 -> E1 -> E1 := sig5.add1.
   Definition zero1 : E1 := sig5.zero1.
   Definition inv1 : E1 -> E1 := sig5.inv1.
   Definition bool_eq1 : E1 -> E1 -> bool := sig5.bool_eq1.
   Definition disjoint1 : E1 -> E1 -> bool := sig5.disjoint1.

   Definition T : Type := sig5.T*sig.T.
                
   Definition P0 (s : St)(r : R0)(w : W) : (St*C0) :=
      let '(r, r', r'') := r in
      let c := exp.P0 s r w in

      (s,(c.2,(sig5.P0 (exp.ToStSig5 c) r' (exp.ToWitSig5 c r w)).2,
      (sig.P0 (exp.ToStSig c) r'' (exp.ToWitSig c r w)).2)).

   Definition P1 (tran : St*C0*E0)(r : R0*R1)(w : W) : (St*C0*E0*C1) :=
    let '(s, (c, c',c''), (e,e')) := tran in
    let '(r, r', r'',r''') := r in
  
    (tran, (sig5.P1 ((exp.ToStSig5 (s,c)),c',e) (r', r''')
      (exp.ToWitSig5 (s,c) r w)).2).

   Definition P2 (tran : St*C0*E0*C1*E1)(r : R0*R1)(w : W) : (St*C0*E0*C1*E1*T) :=
    let '(s, (c, c', c''), (e, e'), c1, e1) := tran in
    let '(r, r', r'',r''') := r in

    (tran, ((sig5.P2 ((exp.ToStSig5 (s,c)),c',e,c1,e1) (r',r''')
      (exp.ToWitSig5 (s,c) r w)).2,
    (sig.P1 (exp.ToStSig (s, c),c'',e') r''
      (exp.ToWitSig (s,c) r w)).2)).

   Definition V2 (tran : St*C0*E0*C1*E1*T) : bool :=
      let '(s, (c, c', c''), e, c1, e1, t) := tran in
      sig5.V2 (exp.ToStSig5 (s,c),c',e.1,c1,e1,t.1) &&
      sig.V1 (exp.ToStSig (s, c),c'',e.2,t.2).

   Definition TE0 : Type := exp.TE*sig5.TE0*sig.TE.
   Definition TE1 : Type := sig5.TE1.

   Definition X  : Type := exp.X.
   Definition simMapHelp (s : St)(x : X) : Prop := exp.simMapHelp s x.
                                           
   Definition simulator (st : St)(t : TE0*TE1)(e : E0*E1) : (St*C0*E0*C1*E1*T) :=
    let '((t,t',t''),(t''')) := t in
    let '((e,e'),e'') := e in

    let c   := exp.simulator st t in
    let a  := sig5.simulator (exp.ToStSig5 (st,c)) (t',t''') (e,e'') in
    let b     := sig.simulator (exp.ToStSig (st,c))  t'' e' in

    (st, (c,a.1.1.1.1.2,b.1.1.2),(e,e'),a.1.1.2,e'',(a.2,b.2)).

   Definition simMap (st : St)(w : W)(e : E0*E1)(x : X)(r : R0*R1) : (TE0*TE1) :=
    let '((e,e'),e'') := e in
    let '(r, r', r'',r''') := r in

    (exp.simMap st w x r, (sig5.simMap (exp.ToStSig5 (exp.P0 st r w))
      (exp.ToWitSig5 (exp.P0 st r w) r w) (e,e'') (exp.sig5Xcomp st x) (r',r''')).1,
      sig.simMap (exp.ToStSig (exp.P0 st r w))
        (exp.ToWitSig (exp.P0 st r w) r w) e' (exp.sigXcomp st x) r'',
    (sig5.simMap (exp.ToStSig5 (exp.P0 st r w))
      (exp.ToWitSig5 (exp.P0 st r w) r w) (e,e'') (exp.sig5Xcomp st x) (r',r''')).2).
          
   Definition simMapInv (st : St)(w : W)(e : E0*E1)(x : X)(t : TE0*TE1) : (R0*R1) :=
    let '((e,e'),e'') := e in
    let '(t, t', t'',t''') := t in
    let r := exp.simMapInv st w x t in

    (r, (sig5.simMapInv (exp.ToStSig5 (st,(exp.simulator st t)))
      (exp.ToWitSig5 (st,(exp.simulator st t)) r w) (e,e'') (exp.sig5Xcomp st x) (t',t''')).1,
      sig.simMapInv (exp.ToStSig (exp.P0 st r w))
        (exp.ToWitSig (exp.P0 st r w) r w) e' (exp.sigXcomp st x) t'',
    (sig5.simMapInv (exp.ToStSig5 (exp.P0 st r w))
      (exp.ToWitSig5 (exp.P0 st r w) r w) (e,e'') (exp.sig5Xcomp st x) (t',t''')).2).

   Definition M0 : nat := max sig5.M0 sig.M.
   Definition M1 : nat := S (Nat.pred sig5.M1).

   Lemma M1_cast : S (Nat.pred sig5.M1) = sig5.M1.
   Proof.
    intros. pose exp.M1_nonzero. lia.
   Qed.
   Lemma M0_sub_1 : 0+sig5.M0 <= max sig5.M0 sig.M.
   Proof.
    intros. apply Nat.le_max_l.
   Qed.

   Lemma M0_sub_2 : 0+sig.M <= max sig5.M0 sig.M.
   Proof.
    intros. apply Nat.le_max_r.
   Qed.

   Definition extractor (t : vector (vector T M1) M0)(e : vector (E0*(vector E1 M1)) M0) : W :=
    exp.extractor (sig5.extractor (Vsub (Vmap (fun a => Vcast (UnzipLeft a) M1_cast) t) M0_sub_1)
                         (Vsub (Vmap (fun a => (a.1.1, Vcast a.2 M1_cast)) e) M0_sub_1))
     (sig.extractor (Vsub (Vmap (fun a => Vhead (UnzipRight a)) t) M0_sub_2)
                                          (Vsub (UnzipRight (UnzipLeft e)) M0_sub_2)).

   Definition fail_event (t : St)(c : C0*(vector C1 M0))(e :vector (E0*(vector E1 M1)) M0) : Prop :=
    exp.argument t c.1.1.1 \/
    sig5.fail_event (exp.ToStSig5 (t,c.1.1.1)) (c.1.1.2,Vsub c.2 M0_sub_1)
    (Vmap (fun a => (a.1.1, Vcast a.2 M1_cast)) (Vsub e M0_sub_1)) \/
    (sig.fail_event (exp.ToStSig (t,c.1.1.1))
    c.1.2 (Vsub (UnzipRight (UnzipLeft e)) M0_sub_2)).
     
  Lemma e_abgrp0 : AbeGroup E0 add0 zero0 bool_eq0 disjoint0 inv0.
  Proof.
    pose sig5.e_abgrp0. pose E.module_abegrp. destruct a, a0. destruct abegrp_grp,
    abegrp_grp0. destruct grp_mon. destruct grp_mon0.
    constructor. constructor. constructor.
    + intros. unfold add0. apply injective_projections; simpl. apply sig5.e_abgrp0.
    apply E.module_abegrp.
    + intros. unfold add0. apply injective_projections; simpl. apply sig5.e_abgrp0.
    apply E.module_abegrp.
    + intros. unfold add0. apply injective_projections; simpl. apply sig5.e_abgrp0.
    apply E.module_abegrp.
    + intros. unfold bool_eq0. destruct a, b. split; intros.
    apply andb_true_iff in H. destruct H. apply sig5.e_abgrp0 in H.
    apply E.module_abegrp in H0. simpl in *. rewrite H. rewrite H0. trivial.
    rewrite H. apply andb_true_iff. split. apply sig5.e_abgrp0; trivial.
    apply E.module_abegrp; trivial.
    + intros. unfold bool_eq0. destruct a, b. rewrite bool_eq_sym0.
    rewrite bool_eq_sym. trivial.
    + intros. unfold bool_eq0. destruct a, b. split; intros.
    apply andb_false_iff in H. destruct H. apply bool_neq_corr in H.
    unfold not in *. intros. apply H. rewrite H0. trivial.
    apply bool_neq_corr0 in H. unfold not in *. intros. apply H. rewrite H0. trivial.
    apply andb_false_iff. case_eq (sig5.bool_eq0 e e0); intros.
    apply bool_eq_corr in H0.  case_eq (E.Gbool_eq g g0); intros.
    apply bool_eq_corr0 in H1. assert False.  apply H. rewrite H0. rewrite H1.
    trivial. contradiction. right. apply H1. left. apply H0.
    + intros. unfold disjoint0. rewrite disjoint_sym0. rewrite disjoint_sym. trivial.
    + intros. unfold disjoint0 in *. apply andb_true_iff in H. destruct H.
    apply disjoint_corr in H. apply disjoint_corr0 in H0. unfold not in *.
    intros. apply H. rewrite H1. trivial.
    + intros. unfold add0, zero0, inv0. destruct x. apply injective_projections; simpl.
    apply inv_left. apply inv_left0.
    + intros. unfold add0. apply injective_projections; simpl. apply inv_right.
    apply inv_right0.
    + intros. unfold add0. apply injective_projections; simpl. apply comm.
    apply comm0.
  Qed.

  Lemma e_abgrp1 : AbeGroup E1 add1 zero1 bool_eq1 disjoint1 inv1.
  Proof.
    apply sig5.e_abgrp1.
  Qed.
  
  (** We require the functions do not modifiy the previous transcript *)
  Lemma pres_p0 : forall (s : St)(r : R0)(w : W),
      (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. unfold P0. destruct r.  destruct p. simpl. trivial.
  Qed.

  Lemma pres_p1 : forall (sce : St*C0*E0)(r : R0*R1)(w : W),
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Proof.
    intros. unfold P1. destruct sce. destruct p. destruct c. destruct p, e, r.
    destruct r, p. simpl. trivial.
  Qed.

  Lemma pres_p2 : forall (sce : St*C0*E0*C1*E1)(r : R0*R1)(w : W),
    (P2 sce r w) = (sce,(P2 sce r w).2).
  Proof.
    intros. unfold P2. destruct sce. destruct p, r. destruct p, r.
    destruct p, e0, p0. destruct c0, p. simpl. trivial.
  Qed.
  
  Lemma pres_sim : forall (s: St)(t : TE0*TE1)(e : E0*E1),
     s = (simulator s t e).1.1.1.1.1.
  Proof.
    intros. unfold simulator. destruct t, e. destruct t, e. destruct p. simpl.
    trivial.
  Qed.

  Lemma chal_sim0 : forall (s: St)(t : TE0*TE1)(e : E0*E1),
    e.1 = (simulator s t e).1.1.1.2.
  Proof.
    intros. unfold simulator. destruct t, e. destruct t, e. destruct p. simpl.
    trivial.
  Qed.
  
  Lemma chal_sim1 : forall (s: St)(t : TE0*TE1)(e : E0*E1),
    e.2 = (simulator s t e).1.2.
  Proof.
    intros. unfold simulator. destruct t, e. destruct t, e. destruct p. simpl.
    trivial.
  Qed.

  (** Properties *)
  Lemma correctness : forall (s :St)(w:W)(r0:R0)(r1:R1)(c0: E0)(c1 : E1),
    Rel s w ->
    V2 (P2
      ((P1 ((P0 s r0 w), c0) (r0,r1) w), c1)
   (r0,r1) w) = true.
  Proof.
    intros. unfold V2, P2, P1, P0. destruct r0. simpl. destruct p, c0. simpl.
    apply andb_true_iff. split.
    + rewrite <- exp.pres_p0. rewrite <- sig5.pres_p0. rewrite <- sig5.pres_p1.
    rewrite <- sig5.pres_p2. rewrite sig5.correctness; auto. apply exp.ToValid; auto.
    + rewrite <- sig.pres_p1. rewrite <- exp.pres_p0. rewrite <- sig.pres_p0.  apply sig.correctness.
     apply exp.ToValid; auto.
  Qed.

 
  Definition allDifferent (e : vector (E0*vector E1 M1) M0) :=
    PairwisePredicate disjoint0 (UnzipLeft e) /\
      bVforall (fun a => PairwisePredicate disjoint1 a.2) e.

  Definition allValid  (s : St)(c0 : C0)(c1 : vector C1 M0)
        (e : vector (E0*vector E1 M1) M0)
        (t : vector (vector T M1) M0) :=
    bVforall3 (fun c e0 t0 => 
      bVforall2 (fun e1 t1 => V2 (s, c0, e0.1, c, e1, t1)) e0.2 t0) c1 e t.
  
  Lemma special_soundness : forall (s : St)(c0 : C0)(c1 : vector C1 M0)
        (e : vector (E0*vector E1 M1) M0)
        (t : vector (vector T M1) M0),
      (* Forall e it is disjoint from all e *)
      allDifferent e ->
      allValid s c0 c1 e t ->
    Rel s (extractor t e) = true \/ fail_event s (c0,c1) e.
  Proof.
     intros. unfold fail_event, extractor. simpl.
    assert (sig.Rel (exp.ToStSig (s, c0.1.1)) (sig.extractor (Vsub
    (Vmap (fun a => Vhead (UnzipRight a)) t) M0_sub_2) 
    (Vsub (UnzipRight (UnzipLeft e)) M0_sub_2)) = true \/
    sig.fail_event (exp.ToStSig (s, c0.1.1)) c0.2
    (Vsub (UnzipRight (UnzipLeft e)) M0_sub_2)).
    + apply sig.special_soundness. destruct H. apply PairwisePredicateSplitUnzip in H.
    apply andb_true_iff in H. destruct H. apply (PairwisePredicate_sub 0 sig.M M0_sub_2) in H2. auto.
    apply E.module_abegrp. unfold allValid in H0.  unfold V2 in H0. 
    apply bVforall2_nth_intro. intros. do 2 rewrite Vnth_sub. 
    apply (bVforall3_elim_nth (Vnth_sub_aux 0 M0_sub_2 ip)) in H0.
    apply bVforall2_elim_head in H0. do 3 rewrite Vnth_map. destruct c0, p.
    apply andb_true_iff in H0. destruct H0. simpl. rewrite Vhead_map.  apply H1.
    + destruct H1. 
    ++ assert (sig5.Rel (exp.ToStSig5 (s, c0.1.1))
    (sig5.extractor (Vsub (Vmap (fun a => Vcast (UnzipLeft a) M1_cast) t) M0_sub_1)
        (Vsub (Vmap (fun a => (a.1.1, Vcast a.2 M1_cast)) e) M0_sub_1)) \/
    sig5.fail_event (exp.ToStSig5 (s, c0.1.1)) (c0.1.2, Vsub c1 M0_sub_1)
      (Vmap (fun a => (a.1.1, Vcast a.2 M1_cast)) (Vsub e M0_sub_1))).
    +++ rewrite Vsub_map. destruct H. apply sig5.special_soundness.
    ++++ apply (PairwisePredicate_sub 0 sig5.M0 M0_sub_1) in H.
         apply PairwisePredicateSplitUnzip in H. apply andb_true_iff in H. destruct H.
         split.
    apply PairwisePredicateVnth. intros. 
    assert (forall a b : sig5.E0, sig5.disjoint0 a b = sig5.disjoint0 b a).
    apply sig5.e_abgrp0. pose (PairwisePredicateVnth2 sig5.disjoint0 H5 
    (UnzipLeft (Vsub (UnzipLeft e) M0_sub_1)) H ip jp H4). do 2 rewrite Vnth_map.
    do 2 rewrite Vnth_sub.  do 2 rewrite Vnth_map. simpl.
    assert (sig5.disjoint0 (Vnth (UnzipLeft (Vsub (UnzipLeft e) M0_sub_1)) ip)
     (Vnth (UnzipLeft (Vsub (UnzipLeft e) M0_sub_1)) jp)). trivial.
    do 2 rewrite Vnth_map in H6. do 2 rewrite Vnth_sub in H6. 
    do 2 rewrite Vnth_map in H6. trivial. intros. 
    +++++ apply bVforall_nth_intro. intros. rewrite Vnth_sub.  
    apply (bVforall_elim_nth (Vnth_sub_aux 0 M0_sub_1 ip)) in H2.
    rewrite Vnth_map. simpl. apply PairwisePredicate_cast. 
    apply sig5.e_abgrp1. apply H2.
    +++++
    intros. unfold disjoint0. 
    replace (sig5.disjoint0 a.1 b.1) with (sig5.disjoint0 b.1 a.1).
    replace (E.Gdisjoint a.2 b.2) with (E.Gdisjoint b.2 a.2).
    trivial. apply E.module_abegrp. apply sig5.e_abgrp0. 
    ++++ apply bVforall3_nth_intro. intros. do 3 rewrite Vnth_sub.
    apply (bVforall3_elim_nth (Vnth_sub_aux 0 M0_sub_1 ip)) in H0. unfold V2 in H0.
    apply bVforall2_nth_intro. intros. do 2 rewrite Vnth_map. rewrite Vnth_cast.
    simpl. apply (bVforall2_elim_nth (Vnth_cast_aux M1_cast ip0)) in H0.
    destruct c0, p. apply andb_true_iff in H0. destruct H0. simpl in *.
    rewrite Vnth_cast. rewrite Vnth_map. apply H0.
    +++ destruct H2. pose (exp.special_soundness H1 H2). destruct o.    
    left; auto. right. left; auto. right. right. left. apply H2.
    ++ right. right. right. auto.
  Qed.

  Lemma honest_verifier_ZK :
    forall (s : St)(w : W)(e : E0*E1)(x : X)(r : R0*R1)(t : TE0*TE1),
      simMapHelp s x ->
      Rel s w ->
      (P2 ((P1 ((P0 s r.1 w), e.1) r w), e.2) r w =
      simulator s (simMap s w e x r) e) /\
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.
  Proof.
    intros. unfold V2, P2, P1, P0, simulator, simMap, simMapInv.
    destruct r, e, r, e, p, t, t, p. simpl.
    unfold simMapHelp in H. pose (exp.simMapHelpValid (exp.P0 s r1 w).2 H).
    destruct a. rewrite <- exp.pres_p0 in H1. rewrite <- exp.pres_p0 in H2.
    pose (exp.ToValid r1 H0). destruct a.
    pose (sig5.honest_verifier_ZK (e,e0) (r2, r0) (t2, t0) H2 H4).
    pose (sig.honest_verifier_ZK g r t H1 H3). destruct a, a0.
    destruct H8, H6. split.
    (* The map work *)
    + intros.
    apply injective_projections; simpl. apply injective_projections; simpl.
    apply injective_projections; simpl. apply injective_projections; simpl.
    apply injective_projections; simpl.
    ++ trivial.
    ++ rewrite exp.pres_p0. rewrite <- (exp.simulatorZK1 r1 H0 H).
    apply injective_projections; simpl. apply injective_projections; simpl.
    trivial. do 2 rewrite <- exp.pres_p0. rewrite <- surjective_pairing.
    rewrite <- H5. rewrite sig5.pres_p1. rewrite sig5.pres_p2. simpl. trivial.
    do 2 rewrite <- exp.pres_p0. rewrite <- H7. rewrite sig.pres_p1. simpl. trivial.
    ++ trivial.
    ++  rewrite <- (exp.simulatorZK1 r1 H0 H). rewrite <- exp.pres_p0.
    rewrite <- surjective_pairing. rewrite <- H5. rewrite sig5.pres_p2. simpl.
    rewrite <- sig5.pres_p0. trivial.
    ++ trivial.
    ++ rewrite <- (exp.simulatorZK1 r1 H0 H). apply injective_projections; simpl.
    rewrite <- exp.pres_p0. rewrite <- surjective_pairing. rewrite <- H5.
    rewrite <- sig5.pres_p1. rewrite <- sig5.pres_p0. trivial.
    rewrite <- exp.pres_p0. rewrite <- H7. rewrite <- sig.pres_p0. trivial.
    (* and it bijects *)
    + pose (exp.simMapInvValid r1 t1 H0 H). destruct a. split.
    ++ (* First direction *)
    apply injective_projections; simpl. apply injective_projections; simpl.
    apply injective_projections; simpl.
    +++ apply H12.
    +++ rewrite <- (exp.simulatorZK1 r1 H0 H). rewrite <- exp.pres_p0.
    rewrite H12. rewrite <- surjective_pairing. rewrite H6. trivial.
    +++ rewrite H12. rewrite H8. trivial.
    +++ rewrite H12. rewrite <- surjective_pairing. rewrite H6. trivial.
    ++ (* Second direction *)
    clear H12 H9 H8 H7 H10 H6 H5 H1 H2 H3 H3 H4.
    pose (exp.ToValid (exp.simMapInv s w x t1) H0). destruct a.
    pose (exp.simMapHelpValid (exp.P0 s (exp.simMapInv s w x t1) w).2 H).
    destruct a. rewrite <- exp.pres_p0 in H3. rewrite <- exp.pres_p0 in H4.
    pose (sig5.honest_verifier_ZK (e,e0) (r2, r0) (t2, t0) H4 H2).
    pose (sig.honest_verifier_ZK g r t H3 H1). destruct a, a0.
    destruct H8, H6. rewrite exp.pres_p0 in H10.
    rewrite (exp.simulatorZK1 (exp.simMapInv s w x t1) H0 H) in H10.
    rewrite H11 in H10.
    apply injective_projections; simpl. apply injective_projections; simpl.
    apply injective_projections; simpl.
    +++ apply H11.
    +++ rewrite exp.pres_p0. rewrite (exp.simulatorZK1 (exp.simMapInv s w x t1) H0 H).
    rewrite H11. rewrite <- surjective_pairing. rewrite H10. trivial.
    +++ rewrite H9. trivial.
    +++ rewrite exp.pres_p0. rewrite (exp.simulatorZK1 (exp.simMapInv s w x t1) H0 H).
    rewrite H11. rewrite <- surjective_pairing. rewrite H10. trivial.
  Qed.

  Lemma simulator_correct : forall (s : St)(t : TE0*TE1)(e : E0*E1),
    V2(simulator s t e) = true.
  Proof.
    intros. unfold V2, simulator. destruct t, e, t, e, p. simpl. apply andb_true_iff.
    split.
    + remember ((sig5.simulator (exp.ToStSig5 (s, exp.simulator s t1)) (t2, t0) (e, e0))) as a.
    rewrite (sig5.pres_sim (exp.ToStSig5 (s, exp.simulator s t1)) (t2, t0) (e,e0)).
    rewrite <-Heqa. replace e with (e,e0).1. replace e0 with (e,e0).2.
    rewrite (sig5.chal_sim0 (exp.ToStSig5 (s, exp.simulator s t1)) (t2, t0) (e, e0)).
    rewrite <- Heqa. rewrite (sig5.chal_sim1 (exp.ToStSig5 (s, exp.simulator s t1))
    (t2, t0) (e, e0)). rewrite <- Heqa. do 5 rewrite <- surjective_pairing.
    rewrite Heqa. apply sig5.simulator_correct. auto. auto.
    + remember (sig.simulator (exp.ToStSig (s, exp.simulator s t1)) t g) as a.
    rewrite (sig.pres_sim (exp.ToStSig (s, exp.simulator s t1)) t g).
    rewrite <- Heqa. rewrite (sig.chal_sim (exp.ToStSig (s, exp.simulator s t1)) t g).
    rewrite <- Heqa. do 3 rewrite <- surjective_pairing. rewrite Heqa.
    apply sig.simulator_correct.
  Qed.

End SigmaPlus5to5CompIns.
