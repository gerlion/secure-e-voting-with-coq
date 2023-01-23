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
Require Import sigmaprotocolPlus5.
Require Import Lia.
Set Implicit Arguments.

Module Type SigmaPlus9.

  Parameter E0 : Set. (* First challenge *)
  Parameter E1 : Set. (* Second challenge *)
  Parameter E2 : Set. (* Third challenge *)
  Parameter E3 : Set. (* Fourth challenge *)
  
   Parameter St:Type.                                (* The set of statements *)
   Parameter W:Type.                                (* The set of witness *)
   Parameter Rel :St -> W -> bool.                  (* The relation function *)

   Parameter C0 : Type.                             (* The first set of commitments *)
   Parameter C1 : Type.                             (* Second set of commitments *)
   Parameter C2 : Type.                             (* Third set of commitments *)
   Parameter C3 : Type.                             (* Fourth set of commitments *)

   Parameter R0 : Type.                              (* The set of random coins for the prover *)
   Parameter R1 : Type.
   Parameter R2 : Type.
   Parameter R3 : Type.

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

   Parameter add2 : E2 -> E2 -> E2.                    (* We will require the set challenges of to be a ring *)
   Parameter zero2 : E2.      
   Parameter inv2 : E2 -> E2.
   Parameter bool_eq2 : E2 -> E2 -> bool.
   Parameter disjoint2 : E2 -> E2 -> bool. 

   Parameter add3 : E3 -> E3 -> E3.                    (* We will require the set challenges of to be a ring *)
   Parameter zero3 : E3.      
   Parameter inv3 : E3 -> E3.
   Parameter bool_eq3 : E3 -> E3 -> bool.
   Parameter disjoint3 : E3 -> E3 -> bool. 

   Parameter T : Type.                              
   Parameter P0 : St -> R0 -> W ->                          (St*C0).         
   Parameter P1 : (St*C0*E0) -> R0*R1 -> W ->               (St*C0*E0*C1).            
   Parameter P2 : (St*C0*E0*C1*E1) -> R0*R1*R2 -> W ->      (St*C0*E0*C1*E1*C2). 
   Parameter P3 : (St*C0*E0*C1*E1*C2*E2) -> R0*R1*R2*R3 -> W ->  
      (St*C0*E0*C1*E1*C2*E2*C3).
   Parameter P4 : (St*C0*E0*C1*E1*C2*E2*C3*E3) -> R0*R1*R2*R3 -> W -> 
      (St*C0*E0*C1*E1*C2*E2*C3*E3*T). 
   Parameter V : (St*C0*E0*C1*E1*C2*E2*C3*E3*T) -> bool.              

   Parameter TE0 : Type.                             
   Parameter TE1 : Type. 
   Parameter TE2 : Type. 
   Parameter TE3 : Type. 
   Parameter X  : Type. 
   Parameter simMapHelp : St -> X -> Prop.    (* We allow simpMap have information no ones else has *)
                                           
   Parameter simulator : St -> (TE0*TE1*TE2*TE3) -> (E0*E1*E2*E3) -> 
      (St*C0*E0*C1*E1*C2*E2*C3*E3*T). (* The simulator *)
   Parameter simMap    : St -> W -> (E0*E1*E2*E3) -> X -> (R0*R1*R2*R3)  -> 
      (TE0*TE1*TE2*TE3).    
   Parameter simMapInv : St -> W -> (E0*E1*E2*E3) -> X -> (TE0*TE1*TE2*TE3) -> 
      (R0*R1*R2*R3).  

   Parameter M0 : nat.
   Parameter M1 : nat.
   Parameter M2 : nat.
   Parameter M3 : nat.

   Parameter extractor : vector (vector (vector (vector T M3) M2) M1) M0 -> 
      vector (E0*vector (E1*vector (E2*(vector E3 M3)) M2) M1) M0 -> (W).   (* The extractor *)

  Parameter argument : St -> C0*(vector (C1*vector (C2*vector C3 M2) M1) M0)  -> 
      vector (E0*vector (E1*vector (E2*(vector E3 M3)) M2) M1) M0 -> Prop.

  Axiom e_abgrp0 : AbeGroup E0 add0 zero0 bool_eq0 disjoint0 inv0.
  Axiom e_abgrp1 : AbeGroup E1 add1 zero1 bool_eq1 disjoint1 inv1.
  Axiom e_abgrp2 : AbeGroup E2 add2 zero2 bool_eq2 disjoint2 inv2.
  Axiom e_abgrp3 : AbeGroup E3 add3 zero3 bool_eq3 disjoint3 inv3.
  
  (** We require the functions do not modifiy the previous transcript *)
  Axiom pres_p0 : forall (s : St)(r : R0)(w : W), 
      (P0 s r w) = (s,(P0 s r w).2).
  Axiom pres_p1 : forall (sce : St*C0*E0)(r : R0*R1)(w : W), 
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Axiom pres_p2 : forall (sce : St*C0*E0*C1*E1)(r : R0*R1*R2)(w : W), 
    (P2 sce r w) = (sce,(P2 sce r w).2).
  Axiom pres_p3 : forall (sce : St*C0*E0*C1*E1*C2*E2)(r : R0*R1*R2*R3)(w : W), 
    (P3 sce r w) = (sce,(P3 sce r w).2).
  Axiom pres_p4 : forall (sce : St*C0*E0*C1*E1*C2*E2*C3*E3)(r : R0*R1*R2*R3)(w : W), 
    (P4 sce r w) = (sce,(P4 sce r w).2).

  Axiom pres_sim : forall (s: St)(t : TE0*TE1*TE2*TE3)(e : E0*E1*E2*E3),
     s = (simulator s t e).1.1.1.1.1.1.1.1.1.
  Axiom chal_sim0 : forall (s: St)(t : TE0*TE1*TE2*TE3)(e : E0*E1*E2*E3),
    e.1.1.1 = (simulator s t e).1.1.1.1.1.1.1.2.
  Axiom chal_sim1 : forall (s: St)(t : TE0*TE1*TE2*TE3)(e : E0*E1*E2*E3),
    e.1.1.2 = (simulator s t e).1.1.1.1.1.2.  
  Axiom chal_sim2 : forall (s: St)(t : TE0*TE1*TE2*TE3)(e : E0*E1*E2*E3),
    e.1.2 = (simulator s t e).1.1.1.2.  
  Axiom chal_sim3 : forall (s: St)(t : TE0*TE1*TE2*TE3)(e : E0*E1*E2*E3),
    e.2 = (simulator s t e).1.2.  

  (** Properties *)
  Axiom correctness : forall (s :St)(w:W)(r:R0*R1*R2*R3)(c0: E0)
        (c1 : E1)(c2 : E2)(c3 : E3),
    Rel s w ->
    V (P4 ((P3 ((P2 ((P1 ((P0 s r.1.1.1 w),
                       c0) r.1.1 w), c1) r.1 w), c2) r w),c3) r w) = true.


  Axiom special_soundness : forall (s : St)
        (c :C0*(vector (C1*vector (C2*vector C3 M2) M1) M0))
        (e : vector (E0*vector (E1*vector (E2*(vector E3 M3)) M2) M1) M0)
        (t : vector (vector (vector (vector T M3) M2) M1) M0),

    (* First we need to check the challenges are diffirent*)
    (* It would be possible to refactor this into a fixpoint which would 
    look clean but might be harder to work with *)
    PairwisePredicate disjoint0 (UnzipLeft e)  ->
    bVforall (fun a => PairwisePredicate disjoint1 a) 
      (Vmap (fun a => UnzipLeft a) (UnzipRight e))  ->
    bVforall (fun b =>  bVforall (fun a => PairwisePredicate disjoint2 a) b)
      (Vmap (fun a => Vmap (fun b => UnzipLeft b) (UnzipRight a)) (UnzipRight e)) ->
    bVforall (fun c => bVforall (fun b =>  bVforall (fun a => 
          PairwisePredicate disjoint3 a) b) c)
      (Vmap (fun a => 
          Vmap (fun c => 
              Vmap (fun b => b) 
          (UnzipRight c))
      (UnzipRight a)) (UnzipRight e)) ->

    (* And the proofs are valid *)
    bVforall3 (fun c1 e0 t => 
      bVforall3 (fun c2 e1 t => 
        bVforall3 (fun c3 e2 t =>
          bVforall2 (fun e3 t =>
            V (s, c.1, e0.1, c1.1, e1.1, c2.1, e2.1, c3, e3, t)
          ) e2.2 t
        ) c2.2 e1.2 t
      ) c1.2 e0.2 t
    ) c.2 e t ->

 
    Rel s (extractor t e) = true \/ argument s c e. 

  Axiom honest_verifier_ZK :
    forall (s : St)(w : W)(e : E0*E1*E2*E3)(x : X)(r : R0*R1*R2*R3)
          (t : TE0*TE1*TE2*TE3),
      simMapHelp s x ->
      Rel s w ->
      (P4 ((P3 ((P2 ((P1 ((P0 s r.1.1.1 w), e.1.1.1)
         r.1.1 w), e.1.1.2) r.1 w), e.1.2) r w),e.2) r w =
      simulator s (simMap s w e x r) e) /\ 
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.

  Axiom simulator_correct : forall (s : St)(t : TE0*TE1*TE2*TE3)(e : E0*E1*E2*E3),
    V (simulator s t e) = true.

End SigmaPlus9.

(* This combinor is used to build shuffle argument *)
Module Type SigmaPlus5plus3to9 (E : GroupSig)(sig : SigmaPlus E)(sig5 : SigmaPlus5).

  Parameter E0 : Set. (* First challenge *)
  Parameter E1 : Set. (* Second challenge *)

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

  Parameter St:Type.                                (* The set of statements *)
  Parameter W:Type.                                (* The set of witness *)
  Parameter Rel :St -> W -> bool.  

  Parameter C0 : Type.                            
  Parameter C1 : Type. 

  Parameter R0 : Type.                              
  Parameter R1 : Type.

  Parameter P0 : St -> R0 -> W ->                          (St*C0).         
  Parameter P1 : (St*C0*E0) -> R0*R1 -> W ->               (St*C0*E0*C1).  

  Axiom pres_p0 : forall (s : St)(r : R0)(w : W), 
      (P0 s r w) = (s,(P0 s r w).2).

  Axiom pres_p1 : forall (s : St*C0*E0)(r : R0*R1)(w : W), 
      (P1 s r w) = (s,(P1 s r w).2).

  Parameter ToStSig : St*C0*E0*C1*E1 -> sig.St.  
  Parameter ToWitSig : St*C0*E0*C1*E1 -> (R0*R1) -> W -> sig.W.

  Parameter ToStSig5 : St*C0*E0*C1*E1 -> sig5.St.  
  Parameter ToWitSig5 : St*C0*E0*C1*E1 -> (R0*R1) -> W -> sig5.W.

  Axiom ToValid : forall s w r e e1,
    Rel s w ->
   sig.Rel (ToStSig (P1 (P0 s r.1 w, e) r w,e1))
           (ToWitSig (P1 (P0 s r.1 w, e) r w, e1) r w) /\
   sig5.Rel (ToStSig5 (P1 (P0 s r.1 w, e) r w,e1))
           (ToWitSig5 (P1 (P0 s r.1 w, e) r w, e1) r w).

  Parameter TE0 : Type.                             
  Parameter TE1 : Type. 

  Parameter X  : Type. 
  Parameter simMapHelp : St -> X -> Prop. 

  Parameter sigXcomp : St -> X -> sig.X.
  Parameter sig5Xcomp : St -> X -> sig5.X.

  Parameter simulator : St -> (TE0*TE1) -> (E0*E1) -> (C0*C1).

  Parameter simMap : St -> W -> (E0*E1) -> X -> (R0*R1) ->  (TE0*TE1).    
  Parameter simMapInv : St -> W -> (E0*E1) -> X -> (TE0*TE1) -> (R0*R1).  

  Axiom simMapInvValid :  forall (st : St)(w : W)(e : E0*E1)(x : X)
          (r : R0*R1)(t : TE0*TE1),
     Rel st w ->
     simMapHelp st x ->
    simMap st w e x (simMapInv st w e x t) = t /\
    simMapInv st w e x (simMap st w e x r) = r.

  (* This may need more preconditions otherwise it might be too strong *)
  Axiom simMapHelpValid : forall (st : St)(x : X)(c : C0*C1)(e : E0*E1),
    simMapHelp st x ->
    sig.simMapHelp  (ToStSig (st,c.1,e.1,c.2,e.2)) (sigXcomp st x) /\
    sig5.simMapHelp (ToStSig5 (st,c.1,e.1,c.2,e.2)) (sig5Xcomp st x).

  Axiom simulatorZK1 : forall s w r x e,
     Rel s w ->
     simMapHelp s x ->
     (P0 s r.1 w).2 = (simulator s (simMap s w e x r) e).1.

  Axiom simulatorZK2 : forall s w r x e,
     Rel s w ->
     simMapHelp s x ->
     (P1 (P0 s r.1 w,e.1) r w).2 = (simulator s (simMap s w e x r) e).2.

  Axiom e_abgrp0 : AbeGroup E0 add0 zero0 bool_eq0 disjoint0 inv0.
  Axiom e_abgrp1 : AbeGroup E1 add1 zero1 bool_eq1 disjoint1 inv1.

  Parameter M0 : nat.
  Parameter M1 : nat.

  Axiom M3_nonzero : sig5.M1 > 0.

  Parameter extractor : vector (vector (sig5.W*sig.W) M1) M0 -> 
      vector (E0*vector E1 M1) M0 -> W.
  Parameter argument : St -> (C0*vector C1 M0) -> vector (E0*vector E1 M1) M0 -> Prop.

  Axiom special_soundness : forall s c0 (e : vector (E0*vector E1 M1) M0)
        (c1 : vector C1 M0)(w : vector (vector (sig5.W*sig.W) M1) M0),
    bVforall3 (fun e c1 w =>
      bVforall2 (fun e2 d =>
          sig5.Rel (ToStSig5 (s,c0,e.1,c1,e2)) d.1 &&
          sig.Rel (ToStSig (s,c0,e.1,c1,e2)) d.2 
      ) e.2 w
    ) e c1 w ->

    PairwisePredicate (fun a b => disjoint0 a b) (UnzipLeft e)  ->
    bVforall (fun a => PairwisePredicate disjoint1 a) (UnzipRight e) ->
    Rel s (extractor w e) \/ argument s (c0,c1) e.
  
End SigmaPlus5plus3to9.

Module SigmaPlus5plus3to9Comp (E : GroupSig)(sig : SigmaPlus E)(sig5 : SigmaPlus5)
    (exp : SigmaPlus5plus3to9 E sig sig5) <: SigmaPlus9.

  Definition E0 : Set := exp.E0.
  Definition E1 : Set := exp.E1.
  Definition E2 : Set := sig5.E0*E.G.
  Definition E3 : Set := sig5.E1.
  
   Definition St:Type := exp.St.                               
   Definition W:Type  := exp.W.                              
   Definition Rel := exp.Rel.          

   Definition C0 : Type := exp.C0.                         
   Definition C1 : Type := exp.C1.                         
   Definition C2 : Type := sig5.C0*sig.C.                  
   Definition C3 : Type := sig5.C1.                  

   Definition R0 : Type := exp.R0.                        
   Definition R1 : Type := exp.R1.
   Definition R2 : Type := sig5.R0*sig.R.
   Definition R3 : Type := sig5.R1.

   Definition add0 : E0 -> E0 -> E0 := exp.add0.
   Definition zero0 : E0 := exp.zero0.     
   Definition inv0 : E0 -> E0 := exp.inv0.
   Definition bool_eq0 : E0 -> E0 -> bool := exp.bool_eq0.
   Definition disjoint0 : E0 -> E0 -> bool := exp.disjoint0.

   Definition add1 : E1 -> E1 -> E1 := exp.add1.                   
   Definition zero1 : E1 := exp.zero1.      
   Definition inv1 : E1 -> E1 := exp.inv1.
   Definition bool_eq1 : E1 -> E1 -> bool := exp.bool_eq1.
   Definition disjoint1 : E1 -> E1 -> bool := exp.disjoint1. 

   Definition add2 (a b: E2) : E2 := (sig5.add0 a.1 b.1, E.Gdot a.2 b.2).                    
   Definition zero2 : E2 := (sig5.zero0, E.Gone).      
   Definition inv2 (a : E2) : E2 := (sig5.inv0 a.1, E.Ginv a.2).
   Definition bool_eq2 (a b : E2) : bool := sig5.bool_eq0 a.1 b.1 && E.Gbool_eq a.2 b.2.
   Definition disjoint2(a b : E2) : bool := 
      sig5.disjoint0 a.1 b.1 && E.Gdisjoint a.2 b.2.

   Definition add3 : E3 -> E3 -> E3 := sig5.add1.                    
   Definition zero3 : E3 := sig5.zero1.      
   Definition inv3 : E3 -> E3 := sig5.inv1.
   Definition bool_eq3 : E3 -> E3 -> bool := sig5.bool_eq1. 
   Definition disjoint3 : E3 -> E3 -> bool := sig5.disjoint1.

   Definition T : Type := sig5.T * sig.T.                             
   Definition P0 : St -> R0 -> W ->            (St*C0) := exp.P0.        
   Definition P1 : (St*C0*E0) -> R0*R1 -> W -> (St*C0*E0*C1) := exp.P1.  
          
   Definition P2 (s : St*C0*E0*C1*E1)(r : R0*R1*R2)(w : W) : (St*C0*E0*C1*E1*C2) :=
       let '(r0, r1, (r21, r22)) := r in
       (s,((sig5.P0 (exp.ToStSig5 s) r21 (exp.ToWitSig5 s r.1 w)).2, 
           (sig.P0 (exp.ToStSig s) r22 (exp.ToWitSig s r.1 w)).2)).

   Definition P3 (s : St*C0*E0*C1*E1*C2*E2)(r : R0*R1*R2*R3)(w : W) : 
      (St*C0*E0*C1*E1*C2*E2*C3) := 
      let '(r0, r1, (r21, r22), r3) := r in
      (s, (sig5.P1 (exp.ToStSig5 s.1.1,s.1.2.1,s.2.1) (r21,r3) 
        (exp.ToWitSig5 s.1.1 r.1.1 w)).2).
  
   Definition P4 (s : St*C0*E0*C1*E1*C2*E2*C3*E3)(r : R0*R1*R2*R3)(w : W) : 
      (St*C0*E0*C1*E1*C2*E2*C3*E3*T) := 
      (* let '(st,c0,e0,c1,e1,c2,e2,c3,e3) := s in *)
      let e3 := s.2 in
      let c3 := s.1.2 in
      let e2 := s.1.1.2 in
      let c2 := s.1.1.1.2 in

      let '(r0, r1, (r21, r22), r3) := r in
      (s, ((sig5.P2 (exp.ToStSig5 s.1.1.1.1,c2.1,e2.1,c3,e3) (r21,r3)
          (exp.ToWitSig5 s.1.1.1.1 r.1.1 w)).2,
          (sig.P1 (exp.ToStSig s.1.1.1.1,c2.2,e2.2) r22 
          (exp.ToWitSig s.1.1.1.1 r.1.1 w)).2)).

   Definition V (s : St*C0*E0*C1*E1*C2*E2*C3*E3*T) : bool :=
      (* let '(st,c0,e0,c1,e1,c2,e2,c3,e3,t) := s in *)
      let t := s.2 in
      let e3 := s.1.2 in
      let c3 := s.1.1.2 in
      let e2 := s.1.1.1.2 in
      let c2 := s.1.1.1.1.2 in

      sig5.V2 (exp.ToStSig5 s.1.1.1.1.1,c2.1,e2.1,c3,e3,t.1) && 
      sig.V1  (exp.ToStSig  s.1.1.1.1.1,c2.2,e2.2,t.2).
              
   Definition TE0 : Type := exp.TE0.                             
   Definition TE1 : Type := exp.TE1. 
   Definition TE2 : Type := sig5.TE0*sig.TE. 
   Definition TE3 : Type := sig5.TE1. 
   Definition X  : Type := exp.X. 
   Definition simMapHelp : St -> X -> Prop := exp.simMapHelp.
                                           
   Definition simulator (s : St)(t : TE0*TE1*TE2*TE3)(e : E0*E1*E2*E3) :
      (St*C0*E0*C1*E1*C2*E2*C3*E3*T) :=
      let '(e0, e1, (e21, e22), e3) := e in
      let '(t0, t1, (t21, t22), t3) := t in
      let c := exp.simulator s t.1.1 e.1.1 in
      (* let '(_,c21,_,c3,_,t1) *)
      let a := sig5.simulator (exp.ToStSig5 (s,c.1,e0,c.2,e1)) (t21, t3) (e21, e3) in
      (* let '(_,c22,_,t2) *)
      let b := sig.simulator (exp.ToStSig (s,c.1,e0,c.2,e1)) t22 e22 in 
      (s,c.1,e0,c.2,e1,(a.1.1.1.1.2,b.1.1.2),(e21,e22),a.1.1.2,e3,(a.2,b.2)).

   Definition simMap (s : St)(w : W)(e : E0*E1*E2*E3)(x : X)(r : R0*R1*R2*R3) :
      (TE0*TE1*TE2*TE3) := 
      
      (* let '(r0,r1,r2,r3) := r in *)
      let r0 := r.1.1.1 in
      let r1 := r.1.1.2 in
      let r2 := r.1.2 in
      let r3 := r.2 in

      let '(e0,e1,e2,e3) := e in
      let a := exp.P0 s r0 w in 
      let b := exp.P1 (a,e0) r.1.1 w in

      (exp.simMap s w e.1.1 x r.1.1, 
      ((sig5.simMap (exp.ToStSig5 (s,a.2,e0,b.2,e1)) 
          (exp.ToWitSig5 (s,a.2,e0,b.2,e1) r.1.1 w) (e2.1,e3) 
            (exp.sig5Xcomp s x) (r2.1, r3)).1,
          sig.simMap (exp.ToStSig (s,a.2,e0,b.2,e1))
            (exp.ToWitSig (s,a.2,e0,b.2,e1) r.1.1 w) e2.2 
            (exp.sigXcomp s x) r2.2),
      (sig5.simMap (exp.ToStSig5 (s,a.2,e0,b.2,e1))
          (exp.ToWitSig5 (s,a.2,e0,b.2,e1) r.1.1 w) (e2.1,e3) 
            (exp.sig5Xcomp s x) (r2.1, r3)).2).
    
   Definition simMapInv (s : St)(w : W)(e : E0*E1*E2*E3)(x : X)(t : TE0*TE1*TE2*TE3) :
      (R0*R1*R2*R3) :=  

      (*let '(t0,t1,t2,t3) *)
      let t0 := t.1.1.1 in
      let t1 := t.1.1.2 in
      let t2 := t.1.2 in
      let t3 := t.2 in

      let '(e0,e1,e2,e3) := e in
      let a := exp.simulator s t.1.1 e.1.1 in
      let b := exp.simMapInv s w e.1.1 x t.1.1 in

      (b, 
      ((sig5.simMapInv (exp.ToStSig5 (s,a.1,e0,a.2,e1)) 
          (exp.ToWitSig5 (s,a.1,e0,a.2,e1) b w) (e2.1,e3) 
            (exp.sig5Xcomp s x) (t2.1, t3)).1,
          sig.simMapInv (exp.ToStSig (s,a.1,e0,a.2,e1))
            (exp.ToWitSig (s,a.1,e0,a.2,e1) b w) e2.2 
            (exp.sigXcomp s x) t2.2),
      (sig5.simMapInv (exp.ToStSig5 (s,a.1,e0,a.2,e1))
          (exp.ToWitSig5 (s,a.1,e0,a.2,e1) b w) (e2.1,e3) 
            (exp.sig5Xcomp s x) (t2.1, t3)).2).

   Definition M0 : nat := exp.M0.
   Definition M1 : nat := exp.M1.
   Definition M2 : nat := max sig5.M0 sig.M. 
   Definition M3 : nat := S (Nat.pred sig5.M1).

   Lemma M3_cast : S (Nat.pred sig5.M1) = sig5.M1.
   Proof.
    intros. pose exp.M3_nonzero. lia.
   Qed.

   Lemma M2_sub_1 : 0+sig5.M0 <= max sig5.M0 sig.M.
   Proof.
    intros. apply Nat.le_max_l.
   Qed.

   Lemma M2_sub_2 : 0+sig.M <= max sig5.M0 sig.M.
   Proof.
    intros. apply Nat.le_max_r.
   Qed.

   Definition getSig5Resp (t : vector (vector T M3) M2) : 
          vector (vector sig5.T sig5.M1) sig5.M0 :=
       (Vmap (fun g => UnzipLeft (Vcast g M3_cast)) (Vsub t M2_sub_1)).

   Definition getSig5Chal (e : vector (E2*(vector E3 M3)) M2) :
      vector (sig5.E0*(vector sig5.E1 sig5.M1)) sig5.M0 :=
     (Vmap (fun g => (g.1.1,Vcast g.2 M3_cast)) (Vsub e M2_sub_1)).

   Definition getSigResp (t : vector (vector T M3) M2) :   
      vector sig.T sig.M :=
      (Vmap (fun g => (Vhead g).2) (Vsub t M2_sub_2)).

   Definition getSigChal (e : vector (E2*(vector E3 M3)) M2) :  
      vector E.G sig.M :=
      Vmap (fun g => (g.1.2)) (Vsub e M2_sub_2).

   Definition extractor (t : vector (vector (vector (vector T M3) M2) M1) M0) 
     (e : vector (E0*vector (E1*vector (E2*(vector E3 M3)) M2) M1) M0) : (W) :=
    
     let w0 := Vmap2 (fun t1 e1 => Vmap2 (fun t2 e3 => 
     sig5.extractor (getSig5Resp t2) (getSig5Chal e3.2)) t1 e1.2 ) t e in
     let w1 := Vmap2 (fun c d => Vmap2 (fun a b => 
     sig.extractor (getSigResp a) (getSigChal b.2)) c d.2) t e in

     exp.extractor (Vmap2 (fun a b => Zip a b) w0 w1) 
      (Vmap (fun a => (a.1, UnzipLeft a.2)) e).
   
  Definition getSig5Com (c : C2*vector C3 M2) :
    sig5.C0*vector sig5.C1 sig5.M0 :=
    (c.1.1, Vsub c.2 M2_sub_1).

  Definition getSigCom (c : C2*vector C3 M2) : sig.C := c.1.2.

  Definition argument (s : St)(c : C0*(vector (C1*vector (C2*vector C3 M2) M1) M0))  
      (e : vector (E0*vector (E1*vector (E2*(vector E3 M3)) M2) M1) M0) : Prop :=
    exp.argument s (c.1, UnzipLeft c.2) (Vmap (fun a => (a.1,UnzipLeft a.2)) e) \/

    (exists i j (ip : i < M0)(jp : j < M1),
    sig5.fail_event (exp.ToStSig5 (s, c.1, (Vnth e ip).1,(Vnth c.2 ip).1,
          (Vnth (Vnth e ip).2 jp).1))
    (getSig5Com  (Vnth (Vnth c.2 ip).2 jp))
    (getSig5Chal (Vnth (Vnth e ip).2 jp).2)) \/

    (exists i j (ip : i < M0)(jp : j < M1),
    sig.fail_event (exp.ToStSig (s, c.1, (Vnth e ip).1,(Vnth c.2 ip).1,
          (Vnth (Vnth e ip).2 jp).1))
    (getSigCom (Vnth (Vnth c.2 ip).2 jp)) (getSigChal (Vnth (Vnth e ip).2 jp).2)). 

  Lemma e_abgrp0 : AbeGroup E0 add0 zero0 bool_eq0 disjoint0 inv0. 
    apply exp.e_abgrp0. Qed.
  
  Lemma e_abgrp1 : AbeGroup E1 add1 zero1 bool_eq1 disjoint1 inv1. 
    apply exp.e_abgrp1. Qed.
  
  Lemma e_abgrp2 : AbeGroup E2 add2 zero2 bool_eq2 disjoint2 inv2.
  Proof.
    intros. destruct (sig5.e_abgrp0). destruct (E.module_abegrp).
    destruct abegrp_grp, abegrp_grp0. constructor. constructor. 
    destruct grp_mon, grp_mon0. constructor.
    + intros. unfold add2. apply injective_projections; simpl.
    apply sig5.e_abgrp0. apply E.module_abegrp.
    + intros. unfold add2. apply injective_projections; simpl.
    apply sig5.e_abgrp0. apply E.module_abegrp.
    + intros. unfold add2. apply injective_projections; simpl.
    apply sig5.e_abgrp0. apply E.module_abegrp.
    + intros. split; intros. apply andb_true_iff in H. destruct H.
    apply bool_eq_corr  in H. apply bool_eq_corr0 in H0.
    apply injective_projections; simpl; auto. apply andb_true_iff.
    rewrite H. split. apply bool_eq_corr; trivial. apply bool_eq_corr0;
    trivial.
    + intros. unfold bool_eq2. apply f_equal2. apply bool_eq_sym.
    apply bool_eq_sym0.
    + intros. split; intros. unfold not. intros. apply andb_false_iff in H.
    destruct H. apply bool_neq_corr in H. apply H. rewrite H0. trivial.
    apply bool_neq_corr0 in H. apply H. rewrite H0. trivial.
    apply andb_false_iff. case_eq (sig5.bool_eq0 a.1 b.1); intros.
    right. apply bool_eq_corr in H0. apply bool_neq_corr0. unfold not. intros.
    apply H. apply injective_projections; simpl; trivial. left. trivial.  
    + intros.  unfold disjoint2. apply f_equal2. apply disjoint_sym.
    apply disjoint_sym0.
    + intros. apply andb_true_iff in H. destruct H. apply disjoint_corr0 in H0.
    unfold not. intros. apply H0. rewrite H1. trivial.
    + intros. unfold add2. apply injective_projections; simpl.
    apply inv_left. apply inv_left0.
    + intros. unfold add2. apply injective_projections; simpl.
    apply inv_right. apply inv_right0.
    + intros. unfold add2. apply injective_projections; simpl.
    apply comm. apply comm0.
  Qed.

  Lemma e_abgrp3 : AbeGroup E3 add3 zero3 bool_eq3 disjoint3 inv3. 
    apply sig5.e_abgrp1. Qed.
  
  (** We require the functions do not modifiy the previous transcript *)
  Lemma pres_p0 : forall (s : St)(r : R0)(w : W), 
      (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. unfold P0. rewrite exp.pres_p0. simpl. trivial.
  Qed.

  Lemma pres_p1 : forall (sce : St*C0*E0)(r : R0*R1)(w : W), 
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Proof.
    intros. unfold P1. rewrite exp.pres_p1. simpl. trivial.
  Qed.

  Lemma pres_p2 : forall (sce : St*C0*E0*C1*E1)(r : R0*R1*R2)(w : W), 
    (P2 sce r w) = (sce,(P2 sce r w).2).
  Proof.
    intros. unfold P2. destruct r, r, p. rewrite sig5.pres_p0. rewrite sig.pres_p0.
    simpl. trivial. 
  Qed.

  Lemma pres_p3 : forall (sce : St*C0*E0*C1*E1*C2*E2)(r : R0*R1*R2*R3)(w : W), 
    (P3 sce r w) = (sce,(P3 sce r w).2).
  Proof.
    intros. unfold P3. destruct r, p, r0, p. rewrite sig5.pres_p1. simpl. trivial.
  Qed.

  Lemma pres_p4 : forall (sce : St*C0*E0*C1*E1*C2*E2*C3*E3)(r : R0*R1*R2*R3)(w : W), 
    (P4 sce r w) = (sce,(P4 sce r w).2).
  Proof.
    intros. unfold P4. destruct sce, r. destruct p, p0, p, p0, r0, p, p, p, p, p. 
    rewrite sig5.pres_p2. rewrite sig.pres_p1. simpl. trivial.
  Qed.

  Lemma pres_sim : forall (s: St)(t : TE0*TE1*TE2*TE3)(e : E0*E1*E2*E3),
     s = (simulator s t e).1.1.1.1.1.1.1.1.1.
  Proof.
    intros. unfold simulator. simpl. destruct e, t, p, p0, p, e0, p0, t0. simpl.
    trivial.
  Qed.

  Lemma chal_sim0 : forall (s: St)(t : TE0*TE1*TE2*TE3)(e : E0*E1*E2*E3),
    e.1.1.1 = (simulator s t e).1.1.1.1.1.1.1.2.
  Proof.
    intros. unfold simulator. simpl. destruct e, t, p, p0, p, e0, p0, t0. simpl.
    trivial.
  Qed.

  Lemma chal_sim1 : forall (s: St)(t : TE0*TE1*TE2*TE3)(e : E0*E1*E2*E3),
    e.1.1.2 = (simulator s t e).1.1.1.1.1.2.  
  Proof.
    intros. unfold simulator. simpl. destruct e, t, p, p0, p, e0, p0, t0. simpl.
    trivial.
  Qed.

  Lemma chal_sim2 : forall (s: St)(t : TE0*TE1*TE2*TE3)(e : E0*E1*E2*E3),
    e.1.2 = (simulator s t e).1.1.1.2.  
  Proof.
    intros. unfold simulator. simpl. destruct e, t, p, p0, p, e0, p0, t0. simpl.
    trivial.
  Qed.

  Lemma chal_sim3 : forall (s: St)(t : TE0*TE1*TE2*TE3)(e : E0*E1*E2*E3),
    e.2 = (simulator s t e).1.2.  
  Proof.
    intros. unfold simulator. simpl. destruct e, t, p, p0, p, e0, p0, t0. simpl.
    trivial.
  Qed.
  

  (** Properties *)
  Lemma correctness : forall (s :St)(w:W)(r:R0*R1*R2*R3)(c0: E0)
        (c1 : E1)(c2 : E2)(c3 : E3),
    Rel s w ->
    V (P4 ((P3 ((P2 ((P1 ((P0 s r.1.1.1 w),
                       c0) r.1.1 w), c1) r.1 w), c2) r w),c3) r w) = true.
  Proof.
    intros. unfold V, P4, P3, P2, P1, P0. destruct r, p, p, r0. cbn. 
    apply andb_true_iff. apply (exp.ToValid (r1, r2) c0 c1) in H. destruct H.
    split.
    + rewrite <- sig5.pres_p0. rewrite <- sig5.pres_p1. rewrite <- sig5.pres_p2. 
    apply sig5.correctness; trivial.
    + rewrite <- sig.pres_p0. rewrite <- sig.pres_p1. apply sig.correctness.
    trivial. 
  Qed.

  Lemma special_soundness : forall (s : St)
        (c :C0*(vector (C1*vector (C2*vector C3 M2) M1) M0))
        (e : vector (E0*vector (E1*vector (E2*(vector E3 M3)) M2) M1) M0)
        (t : vector (vector (vector (vector T M3) M2) M1) M0),

    PairwisePredicate disjoint0 (UnzipLeft e)  ->
    bVforall (fun a => PairwisePredicate disjoint1 a) 
      (Vmap (fun a => UnzipLeft a) (UnzipRight e))  ->
    bVforall (fun b =>  bVforall (fun a => PairwisePredicate disjoint2 a) b)
      (Vmap (fun a => Vmap (fun b => UnzipLeft b) (UnzipRight a)) (UnzipRight e)) ->
    bVforall (fun c => bVforall (fun b =>  bVforall (fun a => 
          PairwisePredicate disjoint3 a) b) c)
      (Vmap (fun a => 
          Vmap (fun c => 
              Vmap (fun b => b) 
          (UnzipRight c))
      (UnzipRight a)) (UnzipRight e)) ->

    (* And the proofs are valid *)
    bVforall3 (fun c1 e0 t => 
      bVforall3 (fun c2 e1 t => 
        bVforall3 (fun c3 e2 t =>
          bVforall2 (fun e3 t =>
            V (s, c.1, e0.1, c1.1, e1.1, c2.1, e2.1, c3, e3, t)
          ) e2.2 t
        ) c2.2 e1.2 t
      ) c1.2 e0.2 t
    ) c.2 e t ->
 
    Rel s (extractor t e) = true \/ argument s c e. 
  Proof.
    + intros. unfold extractor.
    (* We need to show that we can use all the sig 5 witness *)
    assert (Vforall3 (fun c1 e0 t => 
          Vforall3 (fun c2 e1 t => 
          sig5.Rel (exp.ToStSig5 (s, c.1, e0.1, c1.1, e1.1)) t \/
     sig5.fail_event (exp.ToStSig5 (s, c.1, e0.1, c1.1, e1.1)) 
          (getSig5Com c2) (getSig5Chal e1.2))                 
      c1.2 e0.2 t) c.2 e (Vmap2
           (fun (t1 : vector (vector (vector T M3) M2) M1)
              (e1 : E0 * vector (E1 * vector (E2 * vector E3 M3) M2) M1) =>
            Vmap2
              (fun (t2 : vector (vector T M3) M2)
                 (e3 : E1 * vector (E2 * vector E3 M3) M2) =>
               sig5.extractor (getSig5Resp t2) (getSig5Chal e3.2)) t1 e1.2) t e)).
    ++ apply Vforall3_nth_intro. intros. apply Vforall3_nth_intro. intros.
    do 2 rewrite Vnth_map2. apply sig5.special_soundness.
    +++ apply (bVforall_elim_nth ip) in H1. apply (bVforall_elim_nth ip0) in H1.
    do 3 rewrite Vnth_map in H1. trivial. apply PairwisePredicateSplitUnzip in H1.
    apply andb_true_iff in H1. destruct H1. rewrite Vnth_map in H1. unfold getSig5Chal.
    unfold sig5.allDifferent. rewrite UnzipLeftMap.
    apply (PairwisePredicate_sub 0 sig5.M0 M2_sub_1) in H1.
    assert (Vsub (UnzipLeft (UnzipLeft (Vnth (Vnth e ip).2 ip0).2)) M2_sub_1 =
    Vmap (fun a : sig5.E0 * E.G * vector E3 (S (Nat.pred sig5.M1)) => a.1.1)
     (Vsub (Vnth (Vnth e ip).2 ip0).2 M2_sub_1)). apply Veq_nth. intros. 
    rewrite Vnth_map. do 2 rewrite Vnth_sub. do 2 rewrite Vnth_map. trivial.
    rewrite H5 in H1. split. apply H1.
    ++++ apply (bVforall_elim_nth ip) in H2. apply (bVforall_elim_nth ip0) in H2.
    do 2 rewrite Vnth_map in H2. unfold getSig5Chal. rewrite UnzipRightbVforall.
    apply bVforall_nth_intro. intros. do 2 rewrite Vnth_map. rewrite Vnth_sub.
    simpl. apply (bVforall_elim_nth (Vnth_sub_aux 0 M2_sub_1 ip1)) in H2.
    do 4 rewrite Vnth_map in H2. apply PairwisePredicate_cast. intros.
    apply sig5.e_abgrp1. trivial.
    ++++ intros. apply sig5.e_abgrp0.
    +++  apply (bVforall3_elim_nth ip) in H3. apply (bVforall3_elim_nth ip0) in H3.
    apply bVforall3_nth_intro. intros. apply bVforall2_nth_intro. intros.
    apply (bVforall3_elim_nth (Vnth_sub_aux 0 M2_sub_1 ip1)) in H3.
    unfold getSig5Chal, getSig5Resp. do 2 rewrite Vnth_map. simpl in *. 
    rewrite Vnth_cast. rewrite Vnth_sub. apply (bVforall2_elim_nth 
    (Vnth_cast_aux M3_cast ip2)) in H3. unfold V in H3. apply andb_true_iff in H3.
    destruct H3. simpl in *. rewrite Vnth_map. rewrite Vnth_cast. do 2 rewrite Vnth_sub.
    apply H3.
    (* apply (bVforall3_elim_nth ip) in H3. apply (bVforall3_elim_nth ip0) in H3. *)
    ++ assert (Vforall3 (fun c1 e0 t => 
          Vforall3 (fun c2 e1 t => 
          sig.Rel (exp.ToStSig (s, c.1, e0.1, c1.1, e1.1)) t \/
     sig.fail_event (exp.ToStSig (s, c.1, e0.1, c1.1, e1.1)) 
          (getSigCom c2) (getSigChal e1.2))                 
      c1.2 e0.2 t) c.2 e (Vmap2
           (fun (t1 : vector (vector (vector T M3) M2) M1)
              (e1 : E0 * vector (E1 * vector (E2 * vector E3 M3) M2) M1) =>
            Vmap2
              (fun (t2 : vector (vector T M3) M2)
                 (e3 : E1 * vector (E2 * vector E3 M3) M2) =>
               sig.extractor (getSigResp t2) (getSigChal e3.2)) t1 e1.2) t e)).
    +++ apply Vforall3_nth_intro. intros. apply Vforall3_nth_intro. intros.
    do 2 rewrite Vnth_map2. apply sig.special_soundness.
    ++++ apply (bVforall_elim_nth ip) in H1. apply (bVforall_elim_nth ip0) in H1.
    do 2 rewrite Vnth_map in H1. apply PairwisePredicateSplitUnzip in H1.
    apply andb_true_iff in H1. destruct H1. do 2 rewrite Vnth_map in H5.  
    unfold getSigChal. apply (PairwisePredicate_sub 0 sig.M M2_sub_2) in H5.
    assert (Vsub (UnzipRight (UnzipLeft (Vnth (Vnth e ip).2 ip0).2)) M2_sub_2 = 
    getSigChal (Vnth (Vnth e ip).2 ip0).2). apply Veq_nth. intros.
    rewrite Vnth_map. do 2 rewrite Vnth_sub. do 2 rewrite Vnth_map. trivial.
    rewrite H6 in H5. apply H5. intros. apply E.module_abegrp.
    ++++ apply bVforall2_nth_intro. intros. apply (bVforall3_elim_nth ip) in H3. 
    apply (bVforall3_elim_nth ip0) in H3. do 2 rewrite Vnth_map. do 2 rewrite Vnth_sub.
    apply (bVforall3_elim_nth (Vnth_sub_aux 0 M2_sub_2 ip1)) in H3.
    apply bVforall2_elim_head in H3. unfold V in H3. apply andb_true_iff in H3.
    destruct H3. simpl in *. apply H5.
    (* Finish proving base cases - ready to start case analysis *)
    +++ (case_eq (bVforall3
       (fun (c1 : exp.C1 * vector (C2 * vector C3 M2) M1)
          (e0 : exp.E0 * vector (exp.E1 * vector (E2 * vector E3 M3) M2) M1) =>
        [eta bVforall3
               (fun (c2 : C2 * vector C3 M2)
                  (e1 : exp.E1 * vector (E2 * vector E3 M3) M2) 
                  (t1 : sig5.W) =>
                sig5.Rel (exp.ToStSig5 (s, c.1, e0.1, c1.1, e1.1)) t1) c1.2 e0.2]) c.2 e
       (Vmap2
          (fun (t1 : vector (vector (vector T M3) M2) M1)
             (e1 : E0 * vector (E1 * vector (E2 * vector E3 M3) M2) M1) =>
           Vmap2
             (fun (t2 : vector (vector T M3) M2)
                (e3 : E1 * vector (E2 * vector E3 M3) M2) =>
              sig5.extractor (getSig5Resp t2) (getSig5Chal e3.2)) t1 e1.2) t e))); intros.
    (case_eq (bVforall3
       (fun (c1 : exp.C1 * vector (C2 * vector C3 M2) M1)
          (e0 : exp.E0 * vector (exp.E1 * vector (E2 * vector E3 M3) M2) M1) =>
        [eta bVforall3
               (fun (c2 : C2 * vector C3 M2)
                  (e1 : exp.E1 * vector (E2 * vector E3 M3) M2) 
                  (t1 : sig.W) =>
                sig.Rel (exp.ToStSig (s, c.1, e0.1, c1.1, e1.1)) t1) c1.2 e0.2]) c.2 e
       (Vmap2
          (fun (t1 : vector (vector (vector T M3) M2) M1)
             (e1 : E0 * vector (E1 * vector (E2 * vector E3 M3) M2) M1) =>
           Vmap2
             (fun (t2 : vector (vector T M3) M2)
                (e3 : E1 * vector (E2 * vector E3 M3) M2) =>
              sig.extractor (getSigResp t2) (getSigChal e3.2)) t1 e1.2) t e))); intros.
    ++++ (* Should be able to prove relation here or top argument broken *)
    unfold argument. assert (exp.Rel s (exp.extractor (Vmap2 
    (fun a : vector sig5.W M1 => [eta Zip a]) (Vmap2 (fun (t1 : vector (vector 
    (vector T M3) M2) M1)(e1 : E0 * vector (E1 * vector (E2 * vector E3 M3) M2) M1) 
    => Vmap2 (fun (t2 : vector (vector T M3) M2)(e3 : E1 * vector (E2 * vector E3 M3) 
    M2) => sig5.extractor (getSig5Resp t2) (getSig5Chal e3.2)) t1 e1.2) t e)
    (Vmap2 (fun (c0 : vector (vector (vector T M3) M2) M1)(d : E0 * vector 
    (E1 * vector (E2 * vector E3 M3) M2) M1) => Vmap2 (fun (a : vector (vector T M3)
    M2)(b : E1 * vector (E2 * vector E3 M3) M2) => sig.extractor (getSigResp a) 
    (getSigChal b.2)) c0 d.2) t e)) (Vmap (fun a : E0 * vector (E1 * vector 
    (E2 * vector E3 M3) M2) M1 => (a.1, UnzipLeft a.2)) e)) \/ 
    exp.argument s (c.1, UnzipLeft c.2) (Vmap (fun a : E0 * vector (E1 * vector 
    (E2 * vector E3 M3) M2) M1 => (a.1, UnzipLeft a.2)) e)). 
    apply exp.special_soundness. 
    +++++ apply bVforall3_nth_intro. intros. apply bVforall2_nth_intro. intros. 
    do 3 rewrite Vnth_map. do 6 rewrite Vnth_map2. apply (bVforall3_elim_nth ip) in H7.
    apply (bVforall3_elim_nth ip0) in H7. apply (bVforall3_elim_nth ip) in H6.
    apply (bVforall3_elim_nth ip0) in H6. do 2 rewrite Vnth_map2 in H7.
    do 2 rewrite Vnth_map2 in H6. apply andb_true_iff. split; auto.
    +++++ rewrite UnzipLeftMap. apply H.
    +++++ rewrite UnzipRightMap. assert (Vmap [eta UnzipLeft (B:=vector (E2 * 
    vector E3 M3) M2)] (UnzipRight e) = Vmap (fun a : E0 * vector (E1 * vector (E2 * 
    vector E3 M3) M2) M1 => UnzipLeft a.2) e). apply Veq_nth. intros.
    do 3 rewrite Vnth_map. trivial. rewrite H8 in H0. apply H0.  
    +++++ destruct H8. left; trivial. right. left. trivial.
    ++++ (* Sig relation broken *)
    apply bVforall_false3 in H7. destruct H7. destruct H7. apply bVforall_false3 in H7.
    destruct H7. destruct H7. apply (Vforall3_elim_nth x0) in H5.
    apply (Vforall3_elim_nth x2) in H5. destruct H5. assert False.
    apply not_true_iff_false in H7. apply H7. trivial. contradiction.
    right. right. right. exists x. exists x1. exists x0. exists x2. trivial.
    ++++ (* Sig5 relation broken *)
    apply bVforall_false3 in H6. destruct H6. destruct H6. apply bVforall_false3 in H6.
    destruct H6. destruct H6. apply (Vforall3_elim_nth x0) in H4.
    apply (Vforall3_elim_nth x2) in H4. destruct H4. assert False.
    apply not_true_iff_false in H6. apply H6. trivial. contradiction.
    right. right. left. exists x. exists x1. exists x0. exists x2. trivial.
  Qed. 

  Lemma honest_verifier_ZK :
    forall (s : St)(w : W)(e : E0*E1*E2*E3)(x : X)(r : R0*R1*R2*R3)
          (t : TE0*TE1*TE2*TE3),
      simMapHelp s x ->
      Rel s w ->
      (P4 ((P3 ((P2 ((P1 ((P0 s r.1.1.1 w), e.1.1.1)
         r.1.1 w), e.1.1.2) r.1 w), e.1.2) r w),e.2) r w =
      simulator s (simMap s w e x r) e) /\ 
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.
  Proof.
    intros. unfold P4, P3, P2, P1, P0, simulator, simMap, simMapInv. destruct r. 
    destruct p, p, r0. simpl. destruct e, p, p, e0. simpl.
    pose (exp.simMapHelpValid ((exp.P0 s r1 w).2, 
      (exp.P1 (exp.P0 s r1 w, e1) (r1, r2) w).2) (e1, e2) H). destruct a.
    pose (exp.ToValid (r1,r2) e1 e2 H0). destruct a. simpl in *. 
    rewrite <- exp.pres_p0 in H1. rewrite <- exp.pres_p1 in H1.
    rewrite <- exp.pres_p0 in H2. rewrite <- exp.pres_p1 in H2. 
    pose (sig5.honest_verifier_ZK (e0, e) (r0, r) (t.1.2.1, t.2) H2 H4).  
    pose (sig.honest_verifier_ZK g r3 t.1.2.2 H1 H3). destruct a0.
    destruct a. simpl in *. split. 
    + (* The simulator produces valid transcript *)
    rewrite <- exp.pres_p0. rewrite <- exp.pres_p1. rewrite <- exp.simulatorZK1; auto.
    rewrite <- exp.simulatorZK2; auto. destruct (exp.simMap s w (e1, e2) x (r1, r2)).
    apply injective_projections; simpl.
    apply injective_projections; simpl. apply injective_projections; simpl.
    apply injective_projections; simpl. apply injective_projections; simpl.
    apply injective_projections; simpl. 
    ++ rewrite <- exp.pres_p0. rewrite <- exp.pres_p1. trivial.
    ++ trivial.
    ++ rewrite <- exp.pres_p0. rewrite <- exp.pres_p1. 
    rewrite <- surjective_pairing. symmetry in H7. rewrite H7. 
    apply injective_projections; simpl.
    +++ rewrite sig5.pres_p2. rewrite sig5.pres_p1. simpl. trivial.
    +++ symmetry in H5. rewrite H5. rewrite sig.pres_p1. simpl. trivial.
    ++ trivial.
    ++ rewrite <- exp.pres_p0. rewrite <- exp.pres_p1. 
    rewrite <- surjective_pairing. symmetry in H7. rewrite H7. rewrite sig5.pres_p2.
    simpl. rewrite <- sig5.pres_p0. trivial.
    ++ trivial.
    ++ apply injective_projections; simpl.
    +++ rewrite <- exp.pres_p0. rewrite <- exp.pres_p1. symmetry in H7.
    rewrite <- surjective_pairing. rewrite H7. rewrite <- sig5.pres_p0. 
    rewrite <- sig5.pres_p1. trivial. 
    +++ rewrite <- exp.pres_p0. rewrite <- exp.pres_p1. symmetry in H5.
    rewrite H5. rewrite <- sig.pres_p0.  trivial. 
    (* and the coin space are bijective *)
    + rewrite <- exp.simulatorZK1; auto.
    rewrite <- exp.simulatorZK2; auto. destruct H8. destruct H6. 
    pose (exp.simMapInvValid (e1,e2) (r1, r2) t.1.1 H0 H). destruct a. split. 
    ++ (* first one way *) 
    rewrite H12. destruct (exp.simMap s w (e1, e2) x (r1, r2)). 
    apply injective_projections; simpl. apply injective_projections; simpl.
    +++ trivial. 
    +++ rewrite <- exp.pres_p0. do 2 rewrite <- exp.pres_p1. 
    rewrite <- surjective_pairing. rewrite H8. rewrite H6. trivial.
    +++ rewrite <- exp.pres_p0. do 2 rewrite <- exp.pres_p1. 
    rewrite <- surjective_pairing. rewrite H8. trivial.
    ++ (* and then the other *)
    destruct t, p, p. simpl. rewrite H11. clear H10 H6 H5 H9 H8 H7 H1 H2 H3 H4.
    pose (exp.simMapHelpValid ((exp.P0 s (exp.simMapInv s w (e1, e2) x (t1, t2)).1 w).2, 
      (exp.P1 (exp.P0 s (exp.simMapInv s w (e1, e2) x (t1, t2)).1 w, e1) 
    (exp.simMapInv s w (e1, e2) x (t1, t2)) w).2) (e1, e2) H). destruct a.
    pose (exp.ToValid (exp.simMapInv s w (e1, e2) x (t1, t2)) e1 e2 H0). 
    destruct a. simpl in *. rewrite <- surjective_pairing.
    rewrite <- exp.pres_p0 in H1. rewrite <- exp.pres_p1 in H1.
    rewrite <- exp.pres_p0 in H2. rewrite <- exp.pres_p1 in H2. 
    pose (sig5.honest_verifier_ZK (e0, e) (r0,r) (t0.1, t) H2 H4).  
    pose (sig.honest_verifier_ZK g r3 t0.2 H1 H3). destruct a. destruct a0.
    destruct H6. destruct H8.
     apply injective_projections; simpl. apply injective_projections; simpl.
    +++ trivial.
    +++ rewrite <- exp.pres_p0. rewrite <- exp.pres_p1.
    rewrite <- H11. rewrite <- exp.simulatorZK1; auto. 
    rewrite <- exp.simulatorZK2; auto. rewrite H11.
    rewrite <- exp.pres_p0. rewrite <- exp.pres_p1. rewrite H9. rewrite H10.
    simpl. rewrite <- surjective_pairing. trivial.
    +++ rewrite <- exp.pres_p0. rewrite <- exp.pres_p1.
    rewrite <- H11. rewrite <- exp.simulatorZK1; auto. 
    rewrite <- exp.simulatorZK2; auto. rewrite H11.
    rewrite <- exp.pres_p0. rewrite <- exp.pres_p1. rewrite H9. trivial.
  Qed.

  Lemma simulator_correct : forall (s : St)(t : TE0*TE1*TE2*TE3)(e : E0*E1*E2*E3),
    V (simulator s t e) = true. 
  Proof.
    intros. unfold V, simulator. destruct e, t, p, p0, p, e0, p0, t0. simpl.
    apply andb_true_iff. split.
    ++ remember (exp.ToStSig5 (s, (exp.simulator s (t1, t2) (e1, e2)).1, e1,
         (exp.simulator s (t1, t2) (e1, e2)).2, e2))  as c.
    remember (sig5.simulator c  (t0, t) (e0, e)) as d.
    pose (sig5.chal_sim0 c (t0, t) (e0, e)).
    pose (sig5.chal_sim1 c (t0, t) (e0, e)).
    simpl in *. rewrite e4. rewrite <- Heqd. rewrite e3. rewrite <- Heqd.
    rewrite (sig5.pres_sim  c (t0, t) (e0, e)). rewrite Heqd.
    do 5 rewrite <- surjective_pairing.  apply sig5.simulator_correct. 
    ++ remember (exp.ToStSig (s, (exp.simulator s (t1, t2) (e1, e2)).1, e1,
        (exp.simulator s (t1, t2) (e1, e2)).2, e2)) as c.
     remember (sig.simulator c t3 g) as d. rewrite (sig.chal_sim c t3 g). rewrite <- Heqd.
    rewrite (sig.pres_sim c t3 g). rewrite Heqd. do 3 rewrite <- surjective_pairing.
    trivial. apply sig.simulator_correct.
  Qed. 

End SigmaPlus5plus3to9Comp.

