Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Groups.groups.
Require Import Coq.Lists.List.
Set Implicit Arguments.

Module Sigma.

Section Sigma.
Delimit Scope Sigma with F.
Open Scope Sigma.

(* This record defines the structure of a sigma protocol
including additional objects required for the proof.  *)

Variable E : Set.

Record form := mkForm {   
    S:Type;                                (* The set of statements *)
    W:Type;                                (* The set of witness *)
    Rel :S -> W -> bool;                  (* The relation function *)
    C : Type;                              (* The set of commitments *)
    R : Type;                              (* The set of random coins for the prover *)
    (*;                              (* The set of challenges *) *)
    add : E -> E -> E;                    (* We will require the set challenges of to be a abgroup *)
    zero : E;      
    inv : E -> E;
    bool_eq : E -> E -> bool;
    disjoint : E -> E -> bool;            (* disjoint is required for product groups *)
    T : Type;                              (* The set of responses  *)
    P0 : S -> R -> W -> (S*C);            (* The initial step of the prover, outputs a commit *)
    V0 : (S*C) -> E -> (S*C*E);           (* The initial step of the verifier, outputs a challenge *)
    P1 : (S*C*E) -> R -> W -> (S*C*E*T);  (* The final step of the prover, outputs a response *)
    V1 : (S*C*E*T) -> bool;               (* The final step of the verifier *)
    simulator : S -> T -> E -> (S*C*E*T); (* The simulator *)
    simMap    : S -> W -> E -> R -> T;    (* An explicit mapping between honest and simulated *)
    simMapInv : S -> W -> E -> T -> R;    (* A function we use to show simMap is a bijection 
      between R and T when fixing the other variables *)
    extractor : T -> T -> E -> E -> W   (* The extractor *)
}.

End Sigma.
End Sigma.

Section BasicSigmaDef.
Delimit Scope BasicSigmaDef with F.
Open Scope BasicSigmaDef.

(** This document contains the basic defination of a sigma protocol 
    in addition it provides methods to generate variations of 
    existing sigma protocols, namely:

      AND     - 2 commits, 1 challenge, 2 resp        
      OR      - 2 commits, 1 challenge, (2+2) resp
      EQUAL   - 2 commits, 1 challenge, 1 resp
      Parral  - 2 commits, 2 challenges, 2 resps, for two distinct sigmas
*)

Variable E : Set.

Notation "sigma .S"   := (Sigma.S sigma) (at level 0).
Notation "sigma .W"   := (Sigma.W sigma) (at level 0).
Notation "sigma .Rel" := (Sigma.Rel sigma) (at level 0).
Notation "sigma .C"   := (Sigma.C sigma) (at level 0).
Notation "sigma .R"   := (Sigma.R sigma) (at level 0).
(* Notation "sigma .E"   := (Sigma.E sigma) (at level 0). *)
Notation "sigma .add" := (Sigma.add sigma) (at level 0).
Notation "sigma .zero" := (Sigma.zero sigma) (at level 0).
Notation "sigma .bool_eq" := (Sigma.bool_eq sigma) (at level 0).
Notation "sigma .inv" := (Sigma.inv sigma) (at level 0).
Notation "sigma .disjoint" := (Sigma.disjoint sigma) (at level 0).
Notation "sigma .T" := (Sigma.T sigma) (at level 0).
Notation "sigma .P0" := (Sigma.P0 sigma) (at level 0).
Notation "sigma .V0" := (Sigma.V0 sigma) (at level 0).
Notation "sigma .P1" := (Sigma.P1 sigma) (at level 0).
Notation "sigma .V1" := (Sigma.V1 sigma) (at level 0).
Notation "sigma .simulator" := (Sigma.simulator sigma) (at level 0).
Notation "sigma .simMap" := (Sigma.simMap sigma) (at level 0).
Notation "sigma .simMapInv" := (Sigma.simMapInv sigma) (at level 0).
Notation "sigma .extractor" := (Sigma.extractor sigma) (at level 0).

(** We require the challenge space E to be a group *)
(** A sigmaProtocol for a relation Rel *)
Class SigmaProtocol (Sig : Sigma.form E) := {

  e_abgrp :> AbeGroup E Sig.add Sig.zero Sig.bool_eq Sig.disjoint Sig.inv;
  
  (** We require the functions do not modifiy the previous transcript *)
  pres_p0 : forall (s : Sig.S)(r : Sig.R)(w : Sig.W), (Sig.P0 s r w) = (s,(Sig.P0 s r w).2);
  pres_v0 : forall (sc : Sig.S*Sig.C)(e : E), (Sig.V0 sc e) = (sc,(Sig.V0 sc e).2);
  pres_p1 : forall (sce : Sig.S*Sig.C*E)(r : Sig.R)(w : Sig.W), 
    (Sig.P1 sce r w) = (sce,(Sig.P1 sce r w).2);
  pres_sim : forall (s: Sig.S)(t : Sig.T)(e : E),
      (s, (Sig.simulator s t e).1.1.2) = (Sig.simulator s t e).1.1;
  (** For composability we require that V0 maps E to E independent of S*C 
        note that when the Fiat-Shamir transfom is applied this no
        really holds but since the FSC is applied only to the highest
        level it dosn't matter *)
   comp_v0 : forall (sc : Sig.S*Sig.C)(e : E), e= (Sig.V0 (sc) e).2; (* public coin *)
   (** We also require the simulator's challenge and response to be independent of the statment *)
  chal_sim : forall (s: Sig.S)(t : Sig.T)(e : E),
    e = (Sig.simulator s t e).1.2;   
  comp_sim1: forall (s1 s2 : Sig.S)(t :Sig.T)(e: E),
          (Sig.simulator s1 t e).2 = (Sig.simulator s2 t e).2;

  (** Properties *)
  correctness : forall (s :Sig.S)(w:Sig.W)(r:Sig.R)(c: E),
    Sig.Rel s w ->
    Sig.V1 (Sig.P1 (Sig.V0 (Sig.P0 s r w) c) r w) = true;

  special_soundness : forall (s : Sig.S)(c : Sig.C)(e1 e2 : E)(t1 t2 :Sig.T),
    Sig.disjoint e1 e2 ->
    Sig.V1 (s, c, e1, t1) = true ->
    Sig.V1 (s, c, e2, t2) = true ->
    Sig.Rel s (Sig.extractor t1 t2 e1 e2) = true;

  (* Fixing s w e, the multiset of transcripts produced in the honest run can be described
     as a function of R; analgously the multiset of transcripts produced by the simulator
     can be described as a function of T.  We use the function simMap from R to T to
     show that the elements of the multisets are equal up to permutation, and hence
     drawing R at random in the honest and T at random in the simulated gives the same
     distribution.  For this we require that simMap is bijective.  To prove this we make 
     use of simMapInv and the well known result that f is bijective if g(f(x)) = x and 
      f(g(y)) = y. *)
  honest_verifier_ZK :
    forall (s : Sig.S)(w : Sig.W)(e : E)(r : Sig.R)(t : Sig.T),
      (Sig.V1 (Sig.P1(Sig.V0 (Sig.P0 s r w) e) r w) = true ->
      (Sig.P1(Sig.V0 (Sig.P0 s r w) e) r w) =
      Sig.simulator s (Sig.simMap s w e r) e) /\ 
      Sig.simMapInv s w e (Sig.simMap s w e r) = r /\
      Sig.simMap s w e (Sig.simMapInv s w e t) = t;

  simulator_correct : forall (s : Sig.S)(t : Sig.T)(e : E),
    Sig.V1(Sig.simulator s t e) = true;
}.

(* To apply the equality composition we require a few extra properties  *)
Class CompSigmaProtocol (Sig : Sigma.form E)
   := {

  sigma_comp :> SigmaProtocol Sig;

  (* The composabilty of p1 holds for an important subclass of sigmas but not all *)
  comp_p1 : forall (sc1 sc2 : Sig.S*Sig.C)(e : E)(r : Sig.R)(w : Sig.W), 
           (Sig.P1 (sc1,e) r w).2 = (Sig.P1 (sc2,e) r w).2;

  comp_simMap : forall (s1 s2 : Sig.S)(r : Sig.R)(e : E)(w : Sig.W),
    Sig.simMap s1 w e r = Sig.simMap s2 w e r;
}.

End BasicSigmaDef.

Section SigmaCompilers.
Delimit Scope SigmaCompilers with F.
Open Scope SigmaCompilers.

Variable E E' : Set.

Notation "sigma .S"   := (Sigma.S sigma) (at level 0).
Notation "sigma .W"   := (Sigma.W sigma) (at level 0).
Notation "sigma .Rel" := (Sigma.Rel sigma) (at level 0).
Notation "sigma .C"   := (Sigma.C sigma) (at level 0).
Notation "sigma .R"   := (Sigma.R sigma) (at level 0).
Notation "sigma .add" := (Sigma.add sigma) (at level 0).
Notation "sigma .zero" := (Sigma.zero sigma) (at level 0).
Notation "sigma .bool_eq" := (Sigma.bool_eq sigma) (at level 0).
Notation "sigma .inv" := (Sigma.inv sigma) (at level 0).
Notation "sigma .disjoint" := (Sigma.disjoint sigma) (at level 0).
Notation "sigma .T" := (Sigma.T sigma) (at level 0).
Notation "sigma .P0" := (Sigma.P0 sigma) (at level 0).
Notation "sigma .V0" := (Sigma.V0 sigma) (at level 0).
Notation "sigma .P1" := (Sigma.P1 sigma) (at level 0).
Notation "sigma .V1" := (Sigma.V1 sigma) (at level 0).
Notation "sigma .simulator" := (Sigma.simulator sigma) (at level 0).
Notation "sigma .simMap" := (Sigma.simMap sigma) (at level 0).
Notation "sigma .simMapInv" := (Sigma.simMapInv sigma) (at level 0).
Notation "sigma .extractor" := (Sigma.extractor sigma) (at level 0).

(* Equality of sigma is a special case that can only be applied if P1
 is indepedent of the statment which is not generally true *)
 (* Normally in evoting equality is applied directly to dLog to create the
  relationship of dh-tuples and then expanded with ands and ors *)

Definition eqSigmaProtocol (Sig : Sigma.form E) : Sigma.form E  := 
  let eqS : Type := prod Sig.S Sig.S in
  let eqC : Type := prod Sig.C Sig.C in
  
  let eq_Rel (s : eqS)(w :Sig.W) : bool := Sig.Rel s.1 w && Sig.Rel s.2 w in 

  let eq_P0 (s : eqS)(r : Sig.R)(w : Sig.W) : (eqS*eqC) :=
    let c1 := (Sig.P0 s.1 r w).2 in
    let c2 := (Sig.P0 s.2 r w).2 in
     (s,(c1,c2)) in

  let eq_V0 (p0 : eqS*eqC)(e : E) : (eqS*eqC*E) :=
    let s1 := p0.1.1 in
    let s2 := p0.1.2 in 
    let c1 := p0.2.1 in
    let c2 := p0.2.2 in
   (p0, (Sig.V0 (s1,c1),e).2) in

  let eq_P1 (v0 : eqS*eqC*E)(r : Sig.R)(w : Sig.W) : (eqS*eqC*E*Sig.T) :=
  let s1 := v0.1.1.1 in
  let s2 := v0.1.1.2 in
  let c1 := v0.1.2.1 in
  let c2 := v0.1.2.2 in 
  let e := v0.2 in 
   (v0,(Sig.P1 (s1,c1,e) r w).2) in 

 let eq_V1 (p1 : eqS*eqC*E*Sig.T) : bool :=
   let s1 := p1.1.1.1.1 in
   let s2 := p1.1.1.1.2 in
   let c1 := p1.1.1.2.1 in
   let c2 := p1.1.1.2.2 in 
   let e := p1.1.2 in 
   let r := p1.2 in
   Sig.V1 (s1,c1,e,r) && Sig.V1 (s2,c2,e,r) in

  let eq_simulator(s: eqS)(r:Sig.T)(e: E) : (eqS*eqC*E*Sig.T) :=
    let s1 := s.1 in
    let s2 := s.2 in 
    let sim1 := Sig.simulator s1 r e in
    let sim2 := Sig.simulator s2 r e in
    let c1 := sim1.1.1.2 in
    let c2 := sim2.1.1.2 in
    let e1 := sim1.1.2 in
    let r1 := sim1.2 in
    (s,(c1,c2),e1,r1) in 

  let eq_simMap (s : eqS)(w: Sig.W)(e :E)(r: Sig.R) : (Sig.T) :=
    Sig.simMap s.1 w e r in 

  let eq_simMapInv (s : eqS)(w: Sig.W)(e :E)(t : Sig.T) : (Sig.R) :=
    Sig.simMapInv s.1 w e t in 

  let eq_extractor(r1 r2 : Sig.T)(e1 e2 :E) : (Sig.W) :=
    Sig.extractor r1 r2 e1 e2 in

  Sigma.mkForm eq_Rel Sig.add Sig.zero Sig.inv Sig.bool_eq Sig.disjoint eq_P0 eq_V0
   eq_P1 eq_V1 eq_simulator eq_simMap eq_simMapInv eq_extractor.

Definition andSigmaProtocol (Sig : Sigma.form E) : Sigma.form E  := 

  let andS : Type := prod Sig.S Sig.S in
  let andW : Type := prod Sig.W Sig.W in
  let andC : Type := prod Sig.C Sig.C in
  let andR : Type := prod Sig.R Sig.R in
  let andT : Type := prod Sig.T Sig.T in
  

  let and_Rel (s : andS)(w :andW) : bool 
    := Sig.Rel s.1 w.1 && Sig.Rel s.2 w.2 in

   let and_P0 (s : andS)(r : andR)(w : andW) : (andS*andC) :=
    let c1 := (Sig.P0 s.1 r.1 w.1).2 in
    let c2 := (Sig.P0 s.2 r.2 w.2).2 in
     (s,(c1,c2)) in

  let and_V0 (p0 : andS*andC)(e : E) : (andS*andC*E) :=
    let s1 := p0.1.1 in
    let s2 := p0.1.2 in 
    let c1 := p0.2.1 in
    let c2 := p0.2.2 in
   (p0, (Sig.V0 (s1,c1) e).2) in

 let and_P1 (v0 : andS*andC*E)(r : andR)(w : andW) :
     (andS*andC*E*andT) :=
  let s1 := v0.1.1.1 in
  let s2 := v0.1.1.2 in
  let c1 := v0.1.2.1 in
  let c2 := v0.1.2.2 in 
  let e := v0.2 in 
   (v0,((Sig.P1 (s1,c1,e) r.1 w.1).2,(Sig.P1 (s2,c2,e) r.2 w.2).2)) in

 let and_V1 (p1 : andS*andC*E*andT) : bool :=
   let s1 := p1.1.1.1.1 in
   let s2 := p1.1.1.1.2 in
   let c1 := p1.1.1.2.1 in
   let c2 := p1.1.1.2.2 in 
   let e := p1.1.2 in 
   let r := p1.2 in
   Sig.V1 (s1,c1,e,r.1) && Sig.V1 (s2,c2,e,r.2) in

  let and_simulator(s: andS)(r: andT)(e: E) : (andS*andC*E*andT) :=
    let s1 := s.1 in
    let s2 := s.2 in 
    let sim1 := Sig.simulator s1 r.1 e in
    let sim2 := Sig.simulator s2 r.2 e in
    let c1 := sim1.1.1.2 in
    let c2 := sim2.1.1.2 in
    let e1 := sim1.1.2 in
    let r1 := sim1.2 in
    let r2 := sim2.2 in
    (s,(c1,c2),e1,(r1,r2)) in

  let and_simMap (s: andS)(w: andW)(e :E)(r: andR) : (andT) :=
    ((Sig.simMap s.1 w.1 e r.1 ),(Sig.simMap s.2 w.2 e r.2)) in

  let and_simMapInv (s: andS)(w: andW)(e :E)(t: andT) : (andR) :=
    ((Sig.simMapInv s.1 w.1 e t.1 ),(Sig.simMapInv s.2 w.2 e t.2)) in

  let and_extractor(r1 r2 : andT)(e1 e2 : E) : (andW) :=
    (Sig.extractor r1.1 r2.1 e1 e2, Sig.extractor r1.2 r2.2 e1 e2) in

  Sigma.mkForm and_Rel Sig.add Sig.zero Sig.inv Sig.bool_eq Sig.disjoint 
  and_P0 and_V0
  and_P1 and_V1 and_simulator and_simMap and_simMapInv and_extractor.

Definition disSigmaProtocol (Sig : Sigma.form E) : Sigma.form E  := 

  let disS : Type := prod Sig.S Sig.S in        (*new statment space*)
  let disC : Type := prod Sig.C Sig.C in           (*new commit space *)
  let disR : Type := prod (prod Sig.R Sig.T) E in       (*new random space *)
 (* the witness is needed to allow correct forking *)
  let disT : Type := prod (prod Sig.T E) Sig.T in   (*new response space*)
  
  let dis_Rel (s : disS)(w :Sig.W) : bool := Sig.Rel s.1 w || Sig.Rel s.2 w in
  
  let dis_P0 (s : disS)(rzeb : disR)(w : Sig.W) : (disS*disC) :=    
    let e := rzeb.2 in 
    let z := rzeb.1.2 in 
    let r := rzeb.1.1 in 
    let hc1 := (Sig.P0 s.1 r w).2 in
    let hc2 := (Sig.P0 s.2 r w).2 in
    let sc1 := (Sig.simulator s.1 z e).1.1.2 in 
    let sc2 := (Sig.simulator s.2 z e).1.1.2 in
    if (Sig.Rel s.1 w) then (s,(hc1,sc2))
        else (s,(sc1,hc2)) in
      
  let dis_V0 (p0 : disS*disC)(e : E) : (disS*disC*E) :=
   (p0, e) in

 let dis_P1 (v0 : disS*disC*E)(rzeb : disR)(w : Sig.W) : (disS*disC*E*disT) :=
  let s1 := v0.1.1.1 in
  let s2 := v0.1.1.2 in
  let c1 := v0.1.2.1 in
  let c2 := v0.1.2.2 in 
  let e := v0.2 in 
  let se := rzeb.2 in 
  let z := rzeb.1.2 in 
  let r := rzeb.1.1 in 
  let e1 := (Sig.V0 (s1, c1) (Sig.add e (Sig.inv se))).2 in
  let ht1 := (Sig.P1 (s1,c1,e1) r w).2 in 
  let ht2 := (Sig.P1 (s2,c2,e1) r w).2 in
  let st1 := (Sig.simulator s1 z se).2 in 
  let st2 := (Sig.simulator s2 z se).2 in 
   if (Sig.Rel s1 w) then (v0, ((ht1,e1,st2)))
      else   (v0, ((st1,se,ht2))) in 

 let dis_V1 (p1 : disS*disC*E*disT) : bool :=
   let s1 := p1.1.1.1.1 in
   let s2 := p1.1.1.1.2 in
   let c1 := p1.1.1.2.1 in
   let c2 := p1.1.1.2.2 in 
   let e  := p1.1.2 in
   let e1 := p1.2.1.2 in  
   let e2 := (Sig.add e (Sig.inv e1)) in 
   let r1 := p1.2.1.1 in
   let r2 := p1.2.2 in
   (Sig.V1 (s1,c1,e1,r1) && Sig.V1 (s2,c2,e2,r2)) in

  let dis_simulator(s: disS)(t : disT )(e: E) : (disS*disC*E*disT) :=
    let s1 := s.1 in
    let s2 := s.2 in 
    let e1 := t.1.2 in  
    let e2 := (Sig.add e (Sig.inv e1)) in 
    let r1 := t.1.1 in
    let r2 := t.2 in
    let sim1 := Sig.simulator s1 r1 e1 in
    let sim2 := Sig.simulator s2 r2 e2 in
    let c1 := sim1.1.1.2 in
    let c2 := sim2.1.1.2 in
    let sr1 := sim1.2 in
    let sr2 := sim2.2 in
    let se1 := sim1.1.2 in
    let se2 := sim2.1.2 in
      (s,(c1,c2),e,((sr1,se1), (sr2))) in

  (* disR := (R*T*E) and distT := (T*E*T) *)
  let dis_simMap (s : disS)(w: Sig.W)(e :E)(rtcb: disR) : (disT) :=
    let r := rtcb.1.1 in
    let t := rtcb.1.2 in 
    let c := rtcb.2 in 
    let h1 := Sig.simMap s.1 w (Sig.add e (Sig.inv c)) r in
    let h2 := Sig.simMap s.2 w (Sig.add e (Sig.inv c)) r in
    if (Sig.Rel s.1 w) then (h1, Sig.add e (Sig.inv c),t)
      else (t,c,h2) in

  let dis_simMapInv (s : disS)(w: Sig.W)(e :E)(tet : disT) : (disR) :=
    let t1 := tet.1.1 in 
    let c := tet.1.2 in
    let t2 := tet.2 in 
    let h1 := Sig.simMapInv s.1 w c t1 in
    let h2 := Sig.simMapInv s.2 w (Sig.add e (Sig.inv c)) t2 in
    if (Sig.Rel s.1 w) then (h1, t2, Sig.add e (Sig.inv c)) else
      (h2,t1,c) in

  let dis_extractor (r1 r2 : disT)(c1 c2 :E) : (Sig.W) :=
    let e1 := r1.1.2 in
    let e2 := (Sig.add c1 (Sig.inv e1)) in
    let e3 := r2.1.2 in
    let e4 := (Sig.add c2 (Sig.inv e3)) in
    let t1 := r1.1.1 in
    let t2 := r1.2 in
    let t3 := r2.1.1 in
    let t4 := r2.2 in
   if ~~(Sig.bool_eq e1 e3) then Sig.extractor t1 t3 e1 e3 else
    Sig.extractor t2 t4 e2 e4 in

  Sigma.mkForm dis_Rel
  Sig.add Sig.zero Sig.inv Sig.bool_eq Sig.disjoint dis_P0 dis_V0 
  dis_P1 dis_V1 dis_simulator
  dis_simMap dis_simMapInv dis_extractor. 

Definition parSigmaProtocol (Sig1 : Sigma.form E)(Sig2 : Sigma.form E') : Sigma.form (E*E') := 

  let parS : Type := prod Sig1.S Sig2.S in        
  let parW : Type := prod Sig1.W Sig2.W in
  let parC : Type := prod Sig1.C Sig2.C in          
  let parR : Type := prod Sig1.R Sig2.R in 
  let parE : Set := prod E E' in
  let parT : Type := prod Sig1.T Sig2.T in  
  
  let par_Rel (s : parS)(w :parW) : bool := Sig1.Rel s.1 w.1 && Sig2.Rel s.2 w.2 in
  
  let par_add (e1 e2 : parE) : parE :=
    (Sig1.add e1.1 e2.1, Sig2.add e1.2 e2.2) in

  let par_zero : parE  :=
    (Sig1.zero, Sig2.zero) in

  let par_bool_eq (e1 e2 : parE) : bool :=
     Sig1.bool_eq e1.1 e2.1 && Sig2.bool_eq e1.2 e2.2 in

  let par_inv (e : parE) : parE := 
    (Sig1.inv e.1, Sig2.inv e.2) in 

  let par_disjoint (e1 e2 : parE) : bool :=
     Sig1.disjoint e1.1 e2.1 && Sig2.disjoint e1.2 e2.2 in

  let par_P0 (s : parS)(r : parR)(w : parW) : (parS*parC) :=
    let c1 := (Sig1.P0 s.1 r.1 w.1).2 in
    let c2 := (Sig2.P0 s.2 r.2 w.2).2 in
     (s,(c1,c2)) in

  let par_V0 (p0 : parS*parC)(e : parE) : (parS*parC*parE) :=
    let s1 := p0.1.1 in
    let s2 := p0.1.2 in 
    let c1 := p0.2.1 in
    let c2 := p0.2.2 in
   (p0, ((Sig1.V0 (s1,c1) e.1).2,(Sig2.V0 (s2,c2) e.2).2)) in

 let par_P1 (v0 : parS*parC*parE)(r : parR)(w : parW) :
     (parS*parC*parE*parT) :=
  let s1 := v0.1.1.1 in
  let s2 := v0.1.1.2 in
  let c1 := v0.1.2.1 in
  let c2 := v0.1.2.2 in 
  let e := v0.2 in 
   (v0,((Sig1.P1 (s1,c1,e.1) r.1 w.1).2,(Sig2.P1 (s2,c2,e.2) r.2 w.2).2)) in

 let par_V1 (p1 : parS*parC*parE*parT) : bool :=
   let s1 := p1.1.1.1.1 in
   let s2 := p1.1.1.1.2 in
   let c1 := p1.1.1.2.1 in
   let c2 := p1.1.1.2.2 in 
   let e := p1.1.2 in 
   let r := p1.2 in
   Sig1.V1 (s1,c1,e.1,r.1) && Sig2.V1 (s2,c2,e.2,r.2) in

  let par_simulator(s: parS)(r: parT)(e: parE) : (parS*parC*parE*parT) :=
    let s1 := s.1 in
    let s2 := s.2 in 
    let sim1 := Sig1.simulator s1 r.1 e.1 in
    let sim2 := Sig2.simulator s2 r.2 e.2 in
    let c1 := sim1.1.1.2 in
    let c2 := sim2.1.1.2 in
    let e1 := sim1.1.2 in
    let e2 := sim2.1.2 in
    let r1 := sim1.2 in
    let r2 := sim2.2 in
    (s,(c1,c2),(e1,e2),(r1,r2)) in

  let par_simMap (s: parS)(w: parW)(e :parE)(r: parR) : (parT) :=
    ((Sig1.simMap s.1 w.1 e.1 r.1),(Sig2.simMap s.2 w.2 e.2 r.2)) in

  let par_simMapInv (s: parS)(w: parW)(e :parE)(t : parT) : (parR) :=
    ((Sig1.simMapInv s.1 w.1 e.1 t.1),(Sig2.simMapInv s.2 w.2 e.2 t.2)) in

  let par_extractor(r1 r2 : parT)(e1 e2 : parE) : (parW) :=
    (Sig1.extractor r1.1 r2.1 e1.1 e2.1, Sig2.extractor r1.2 r2.2 e1.2 e2.2) in

  Sigma.mkForm par_Rel 
  par_add par_zero par_inv par_bool_eq par_disjoint par_P0 par_V0 
  par_P1 par_V1 par_simulator
  par_simMap par_simMapInv par_extractor. 

Definition genAndSigmaProtocol (Sig1 Sig2 : Sigma.form E) : Sigma.form E := 
  let genAndS : Type := prod Sig1.S Sig2.S in        
  let genAndW : Type := prod Sig1.W Sig2.W in
  let genAndC : Type := prod Sig1.C Sig2.C in          
  let genAndR : Type := prod Sig1.R Sig2.R in 
  let genAndT : Type := prod Sig1.T Sig2.T in  
  
  let genAnd_Rel (s : genAndS)(w :genAndW) : bool := Sig1.Rel s.1 w.1 && Sig2.Rel s.2 w.2 in

  let genAnd_P0 (s : genAndS)(r : genAndR)(w : genAndW) : (genAndS*genAndC) :=
    let c1 := (Sig1.P0 s.1 r.1 w.1).2 in
    let c2 := (Sig2.P0 s.2 r.2 w.2).2 in
     (s,(c1,c2)) in

  let genAnd_V0 (p0 : genAndS*genAndC)(e : E) : (genAndS*genAndC*E) :=
    let s1 := p0.1.1 in
    let s2 := p0.1.2 in 
    let c1 := p0.2.1 in
    let c2 := p0.2.2 in
    (p0, e) in

 let genAnd_P1 (v0 : genAndS*genAndC*E)(r : genAndR)(w : genAndW) :
     (genAndS*genAndC*E*genAndT) :=
  let s1 := v0.1.1.1 in
  let s2 := v0.1.1.2 in
  let c1 := v0.1.2.1 in
  let c2 := v0.1.2.2 in 
  let e := v0.2 in 
   (v0,((Sig1.P1 (s1,c1,e) r.1 w.1).2,(Sig2.P1 (s2,c2,e) r.2 w.2).2)) in

 let genAnd_V1 (p1 : genAndS*genAndC*E*genAndT) : bool :=
   let s1 := p1.1.1.1.1 in
   let s2 := p1.1.1.1.2 in
   let c1 := p1.1.1.2.1 in
   let c2 := p1.1.1.2.2 in 
   let e := p1.1.2 in 
   let r := p1.2 in
   Sig1.V1 (s1,c1,e,r.1) && Sig2.V1 (s2,c2,e,r.2) in

  let genAnd_simulator(s: genAndS)(r: genAndT)(e: E) : (genAndS*genAndC*E*genAndT) :=
    let s1 := s.1 in
    let s2 := s.2 in 
    let sim1 := Sig1.simulator s1 r.1 e in
    let sim2 := Sig2.simulator s2 r.2 e in
    let c1 := sim1.1.1.2 in
    let c2 := sim2.1.1.2 in
    let r1 := sim1.2 in
    let r2 := sim2.2 in
    (s,(c1,c2),e,(r1,r2)) in

  let genAnd_simMap (s: genAndS)(w: genAndW)(e :E)(r: genAndR) : (genAndT) :=
    ((Sig1.simMap s.1 w.1 e r.1),(Sig2.simMap s.2 w.2 e r.2)) in

  let genAnd_simMapInv (s: genAndS)(w: genAndW)(e :E)(t: genAndT) : (genAndR) :=
    ((Sig1.simMapInv s.1 w.1 e t.1),(Sig2.simMapInv s.2 w.2 e t.2)) in

  let genAnd_extractor(r1 r2 : genAndT)(e1 e2 : E) : (genAndW) :=
    (Sig1.extractor r1.1 r2.1 e1 e2, Sig2.extractor r1.2 r2.2 e1 e2) in

  Sigma.mkForm genAnd_Rel 
  Sig1.add Sig1.zero Sig1.inv Sig1.bool_eq Sig1.disjoint 
  genAnd_P0 genAnd_V0 
  genAnd_P1 genAnd_V1 genAnd_simulator
  genAnd_simMap genAnd_simMapInv genAnd_extractor. 

End SigmaCompilers.

Section SigmaEq.
Delimit Scope SigmaEq with F.
Open Scope SigmaEq.


Variable E : Set.

Notation "sigma .S"   := (Sigma.S sigma) (at level 0).
Notation "sigma .W"   := (Sigma.W sigma) (at level 0).
Notation "sigma .Rel" := (Sigma.Rel sigma) (at level 0).
Notation "sigma .C"   := (Sigma.C sigma) (at level 0).
Notation "sigma .R"   := (Sigma.R sigma) (at level 0).
Notation "sigma .add" := (Sigma.add sigma) (at level 0).
Notation "sigma .zero" := (Sigma.zero sigma) (at level 0).
Notation "sigma .bool_eq" := (Sigma.bool_eq sigma) (at level 0).
Notation "sigma .inv" := (Sigma.inv sigma) (at level 0).
Notation "sigma .disjoint" := (Sigma.disjoint sigma) (at level 0).
Notation "sigma .T" := (Sigma.T sigma) (at level 0).
Notation "sigma .P0" := (Sigma.P0 sigma) (at level 0).
Notation "sigma .V0" := (Sigma.V0 sigma) (at level 0).
Notation "sigma .P1" := (Sigma.P1 sigma) (at level 0).
Notation "sigma .V1" := (Sigma.V1 sigma) (at level 0).
Notation "sigma .simulator" := (Sigma.simulator sigma) (at level 0).
Notation "sigma .simMap" := (Sigma.simMap sigma) (at level 0).
Notation "sigma .extractor" := (Sigma.extractor sigma) (at level 0).
(**We now turn to proving the correctness of the compilers *)

Generalizable Variables sigma.

Context `{sigma : Sigma.form E}.

Lemma comp_sim2 :
   forall (s1 s2 : sigma.S)(t :sigma.T)(e: E),
      SigmaProtocol sigma ->
          (sigma.simulator s1 t e).1.2 = (sigma.simulator s2 t e).1.2.
Proof.
  intros.  rewrite <- chal_sim. rewrite <- chal_sim. trivial.
  auto. auto.
Qed.

Theorem eqCorr :
   CompSigmaProtocol sigma ->
     CompSigmaProtocol (eqSigmaProtocol sigma).
Proof.
  (* inital conditions *)
  intros. assert (SigmaProtocol sigma). apply H.
  constructor. constructor. unfold eqSigmaProtocol. simpl.
  apply e_abgrp. apply H.
  unfold eqSigmaProtocol. simpl in *. intros. auto.
  unfold eqSigmaProtocol. simpl in *. intros. auto.
  unfold eqSigmaProtocol. simpl in *. intros. auto.
  unfold eqSigmaProtocol. simpl in *. intros. auto.
  unfold eqSigmaProtocol. simpl in *. intros. trivial.  
  intros. unfold eqSigmaProtocol. simpl.
  rewrite <- chal_sim with (e:=e). auto. apply H.
  intros. unfold eqSigmaProtocol. simpl in *. apply sigma_comp. 
  apply H.

  (* Proving correctness *)
  unfold eqSigmaProtocol. simpl in *. intros.
  apply andb_true_iff in H1. destruct H1. apply andb_true_iff. split.
  (* Inital setup for correctness complete *)
  rewrite <- pres_p0; auto. replace c with (sigma.V0(sigma.P0 s.1 r w) c).2.
  remember ((sigma) .P0 s.1 r w) as sc.
  rewrite <- pres_p1; auto. 
  replace (sc, ((sigma) .V0 sc c).2) with ((sigma) .V0 sc c).
  rewrite Heqsc. apply correctness; auto. apply H. symmetry. apply comp_v0; auto.
  (* First half correctness complete *)
  rewrite <- pres_p0; auto. rewrite <- pres_p0; auto. replace c with (sigma.V0(sigma.P0 s.2 r w) c).2.
  remember ((sigma) .P0 s.1 r w) as sc.
  rewrite pres_v0; auto. rewrite <- comp_v0; auto. rewrite <- comp_p1 with (sc1:= sigma.P0 s.2 r w); auto.
  replace c with (sigma.V0 (sigma.P0 s.2 r w) c).2.
  rewrite <- pres_p1; auto. rewrite <- pres_v0; auto. rewrite <- pres_v0; auto. 
  apply correctness; auto. symmetry. apply comp_v0; auto.
  symmetry. apply comp_v0; auto.

  (** special_soundness *)
  unfold eqSigmaProtocol. simpl in *. intros. apply andb_true_iff.
  apply andb_true_iff in H2. apply andb_true_iff in H3.
  destruct H2. destruct H3.  split.
  apply special_soundness with (c := c.1); auto. 
  apply special_soundness with (c := c.2); auto.

  (** eq honest verifier_ZK *)
  unfold eqSigmaProtocol. simpl in *. intros.
  pose (honest_verifier_ZK s.1 w e r t). pose (honest_verifier_ZK s.2 w e r t).
  destruct a. destruct a0. split. intros valid.
  simpl. apply andb_true_iff in valid. destruct valid.
  rewrite <- pres_p0 in H5; auto. rewrite <- pres_p1 in H5; auto. 
  rewrite (comp_v0 ((sigma) .P0 s.1 r w) e) in H5; auto. rewrite <- pres_v0 in H5; auto.
  apply H1 in H5. 
  rewrite (comp_p1 (s.1, ((sigma) .P0 s.1 r w).2) 
  (s.2, ((sigma) .P0 s.2 r w).2) e r w) in H6; auto.
  rewrite <- pres_p0 in H6;  auto.
  rewrite (comp_v0 ((sigma) .P0 s.2 r w) e) in H6; auto. 
  rewrite <- pres_p1 in H6; auto. rewrite <- pres_v0 in H6; auto.
   apply H3 in H6.

  (*Cleanup front *)
  rewrite <- pres_p0; auto. rewrite <- H5. rewrite (comp_simMap s.1 s.2). rewrite <- H6.
  (* rewrite <- H2.  rewrite <- H4.*)
  remember (((sigma) .P0 s.1 r w).2, ((sigma) .P0 s.2 r w).2) as c.  
  remember (((sigma) .P1 ((sigma) .P0 s.1 r w, e) r w).2) as f.
  
  (*Simple top*)
  rewrite pres_p1; auto. simpl. (*1B*) rewrite pres_v0; auto. simpl. rewrite pres_p1; auto.
  simpl. rewrite pres_v0; auto. simpl. (*2B*) rewrite <- comp_v0; auto. rewrite Heqc.
  rewrite Heqf. trivial. auto.
  
  (* Simulator always correct *)
  unfold eqSigmaProtocol. simpl in *. intros.
  rewrite pres_sim. rewrite pres_sim. 
  rewrite <- surjective_pairing. rewrite <- surjective_pairing. rewrite simulator_correct.  
  replace ((sigma.simulator s.1 t e).1.2) with ((sigma.simulator s.2 t e).1.2).
  replace ((sigma.simulator s.1 t e).2) with ((sigma.simulator s.2 t e).2).
  rewrite <- surjective_pairing. rewrite <- surjective_pairing. rewrite simulator_correct.  trivial.
  apply comp_sim1. apply H. apply comp_sim2. apply H.

  unfold eqSigmaProtocol. simpl in *. intros.
   apply comp_p1.  apply H. 

  unfold eqSigmaProtocol. simpl in *. intros.  apply comp_simMap.  apply H.
Qed.

End SigmaEq.

Section SigmaAnd.
Delimit Scope SigmaAnd with F.
Open Scope SigmaAnd.


Variable E : Set.

Generalizable Variables sigma.

Context `{sigma : Sigma.form E}.

Theorem andCorr :
    SigmaProtocol sigma ->
     SigmaProtocol (andSigmaProtocol sigma).
Proof.
  constructor. unfold andSigmaProtocol. simpl. apply e_abgrp.
  apply H.
  unfold andSigmaProtocol. simpl. intros. auto.
  unfold andSigmaProtocol. simpl. intros. auto.
  unfold andSigmaProtocol. simpl. intros. auto.
  unfold andSigmaProtocol. simpl. intros. auto.
  unfold andSigmaProtocol. simpl. intros.
  remember (sc.1.1, sc.2.1) as sc1.
  rewrite <- comp_v0. trivial. apply H.
  unfold andSigmaProtocol. simpl. intros. 
  replace (Sigma.simulator sigma s.1 t.1 e).1.2 with e. auto.
  apply chal_sim. apply H.
  unfold andSigmaProtocol. simpl. intros. 
  replace ((Sigma.simulator sigma s1.1 t.1 e).2) with ((Sigma.simulator sigma s2.1 t.1 e).2) by (apply comp_sim1; apply H). 
  replace ((Sigma.simulator sigma s1.2 t.2 e).2) with ((Sigma.simulator sigma s2.2 t.2 e).2) by (apply comp_sim1; apply H).
  trivial. 
  unfold andSigmaProtocol. simpl. intros. 

  (** correctness *)
  unfold andSigmaProtocol. simpl. intros. 
  apply andb_true_iff in H0. destruct H0.
  rewrite <- pres_p0. rewrite <- pres_v0. rewrite <- pres_p1.
  apply andb_true_iff. split. apply correctness. apply H. apply H0.
  rewrite <- comp_v0. rewrite <- pres_p0.
  rewrite (comp_v0 (Sigma.P0 sigma s.2 r.2 w.2) c).
  rewrite <- pres_v0. rewrite <- pres_p1. apply correctness. apply H.
  apply H1. apply H. apply H. apply H. apply H. apply H. apply H. apply H.

  (** special soundness *)
  unfold andSigmaProtocol. simpl. intros. 
  apply andb_true_iff. apply andb_true_iff in H1. apply andb_true_iff in H2.
  destruct H1. destruct H2. split. 
  apply special_soundness with (c:=c.1). apply H. apply H0. apply H1.
  apply H2. apply special_soundness with (c:=c.2). apply H. apply H0.
  apply H3. apply H4.

  (** Honest verifer zero knowledge *)
  unfold andSigmaProtocol. simpl. intros. 
   pose (honest_verifier_ZK s.1 w.1 e r.1 t.1). pose (honest_verifier_ZK s.2 w.2 e r.2 t.2).
  destruct a. destruct a0.  split. intros.
  apply andb_true_iff in H4. destruct H4. 
  rewrite pres_p0; auto. simpl. rewrite <- pres_p0; auto. rewrite <- pres_p0; auto.
  rewrite <- pres_v0; auto. 
  replace (Sigma.V0 sigma (Sigma.P0 sigma s.1 r.1 w.1) e).2 with (Sigma.V0 sigma (Sigma.P0 sigma s.2 r.2 w.2) e).2.
  rewrite <- pres_v0; auto. rewrite <- pres_p0 in H4; auto. 
  rewrite <- pres_p1 in H4; auto. rewrite <- pres_v0 in H4; auto.
  do 2 rewrite <- pres_p0 in H5; auto. 
  rewrite <- pres_p1 in H5; auto.   
  replace (Sigma.V0 sigma (Sigma.P0 sigma s.1 r.1 w.1) e).2 with (Sigma.V0 sigma (Sigma.P0 sigma s.2 r.2 w.2) e).2 in H5.
rewrite <- pres_v0 in H5; auto.
  apply H0 in H4.
 apply H2 in H5.
  rewrite <- H4. rewrite <- H5. apply injective_projections; auto.
  (* Second position *)
  apply injective_projections; auto. simpl. rewrite pres_p1; auto. rewrite pres_v0; auto. 
  simpl. rewrite pres_p1; auto. rewrite pres_v0; auto. 
  (* Third position *)
  simpl. rewrite pres_p1; auto. simpl. rewrite <- comp_v0; auto.
  rewrite <- comp_v0; auto. trivial.  rewrite <- comp_v0; auto.
  rewrite <- comp_v0; auto. trivial.  rewrite <- comp_v0; auto.
  rewrite <- comp_v0; auto. trivial. destruct H1. destruct H3.  
  rewrite H1. rewrite H3. rewrite H5. rewrite H4. do 2 rewrite <- surjective_pairing;
  auto.

  (* Simulator always correct *)
  unfold andSigmaProtocol. simpl. intros. 
  apply andb_true_iff. split. rewrite pres_sim.
  rewrite <- surjective_pairing. rewrite <- surjective_pairing.
  apply simulator_correct. apply H.  rewrite pres_sim.
  replace ((Sigma.simulator sigma s.1 t.1 e).1.2) with ((Sigma.simulator sigma s.2 t.2 e).1.2).
  rewrite <- surjective_pairing. rewrite <- surjective_pairing.
  apply simulator_correct. apply H. rewrite <- chal_sim. rewrite <- chal_sim.
  trivial. apply H. apply H.
Qed.

End SigmaAnd.



Section SigmaDis.
Delimit Scope SigmaDis with F.
Open Scope SigmaDis.

Generalizable Variables sigma.

Variable E : Set.

Context `{sigma : Sigma.form E}.
Infix "+" := (Sigma.add sigma).
Notation "0" := (Sigma.zero sigma).

Notation "- x" :=  ((Sigma.inv sigma) x).

Lemma andb_true_iff_three:
  forall b1 b2 b3 :bool, b1 && b2 && b3 = true <-> b1 = true /\ b2 = true /\ b3 = true.
Proof.
  intros. rewrite <- andb_true_iff. rewrite <- andb_true_iff. rewrite andb_assoc.
  apply iff_refl.
Qed.

Theorem disCorr :
    SigmaProtocol sigma ->
    (forall (a b : E), 
        Sigma.disjoint sigma a b <-> Sigma.bool_eq sigma a b = false) ->
     SigmaProtocol (disSigmaProtocol sigma).
Proof.
 constructor.
 (* inital conditions *)
 unfold disSigmaProtocol. simpl. apply e_abgrp. apply H.

  unfold disSigmaProtocol. simpl. intros. case (Sigma.Rel sigma s.1 w). auto. auto.
  unfold disSigmaProtocol. simpl. auto.
  unfold disSigmaProtocol. simpl. intros. case (Sigma.Rel sigma sce.1.1.1 w). auto. auto.
  unfold disSigmaProtocol. simpl. auto.
  unfold disSigmaProtocol. simpl.  
 trivial.
   unfold disSigmaProtocol. simpl. trivial.
   unfold disSigmaProtocol. simpl. intros.
  replace ((Sigma.simulator sigma s2.1 t.1.1 t.1.2).2) with ((Sigma.simulator sigma s1.1 t.1.1 t.1.2).2) by (apply comp_sim1; apply H).
  replace ((Sigma.simulator sigma s2.1 t.1.1 t.1.2).1.2) with ((Sigma.simulator sigma s1.1 t.1.1 t.1.2).1.2).
  replace ((Sigma.simulator sigma s2.2 t.2 (e + - t.1.2)).2) with ((Sigma.simulator sigma s1.2 t.2 (e + - t.1.2)).2) by (apply comp_sim1; apply H).  
  trivial. apply comp_sim2. apply H.
  unfold disSigmaProtocol. simpl. intros. trivial.

  (*correcntess *)
  unfold disSigmaProtocol. simpl. intros.
   apply andb_true_iff. split.  
  (* Case 1 of V1 *)
  case_eq (Sigma.Rel sigma s.1 w).
  (* Case 1.1 *)
  intros. rewrite H2. simpl. rewrite <- pres_p0.
  rewrite <- pres_v0. rewrite <- pres_p1.
  apply correctness. apply H. apply H2. apply H. apply H. apply H.
  (* Case 1.2 *)
  intros. rewrite H2. simpl. rewrite pres_sim.
  remember (Sigma.simulator sigma s.1 r.1.2 r.2).1.1 as sc.
  remember (Sigma.simulator sigma s.1 r.1.2 r.2).2 as resp.
  replace (r.2) with (Sigma.simulator sigma s.1 r.1.2 r.2).1.2.
  rewrite Heqsc. rewrite Heqresp. rewrite <- surjective_pairing.
  rewrite <- surjective_pairing. apply simulator_correct. apply H.
  symmetry. apply chal_sim. apply H.

  (* Case 2 *)
  case_eq (Sigma.Rel sigma s.1 w). simpl.
  (* Case 2.1 *)
  intros. rewrite H2. simpl. simpl. rewrite pres_sim.
  remember (Sigma.simulator sigma s.2 r.1.2 r.2).1.1 as sc.
  remember (Sigma.simulator sigma s.2 r.1.2 r.2).2 as resp.
  rewrite <- comp_v0. replace (c + - (c + - r.2)) with r.2.
  replace (r.2) with (Sigma.simulator sigma s.2 r.1.2 r.2).1.2.
  rewrite Heqsc. rewrite Heqresp. rewrite <- surjective_pairing.
  rewrite <- surjective_pairing. apply simulator_correct. apply H.
  symmetry. apply chal_sim. apply H. symmetry. apply double_chall. apply H.
  (* Case 2.2 *)
  intros. rewrite H2. simpl. rewrite <- pres_p0.
  rewrite <- comp_v0. replace (c + - r.2) with (Sigma.V0 sigma (Sigma.P0 sigma s.2 r.1.1 w) (c + - r.2)).2.
  rewrite <- pres_v0. rewrite <- pres_p1. 
  apply correctness. apply H. rewrite H2 in H1. simpl in *.  apply H1. apply H. apply H.
  symmetry. apply comp_v0. apply H. apply H. apply H.

  (* Special Soundness *)
  (* Setup *)
  unfold disSigmaProtocol. simpl. intros.
  apply andb_true_iff in H2.
  apply andb_true_iff in H3. destruct H2. destruct H3.
  assert (Sigma.bool_eq sigma t1.1.2 t2.1.2 = false \/ 
    Sigma.bool_eq sigma (e1 + - t1.1.2) (e2 + - t2.1.2) = false).
  apply chall_dist with (c1:= e1)(c2:= e2).
  rewrite bool_neq_corr. rewrite <- bool_neq_corr.
  apply H0. apply H1. 
  replace (e1 + - t1.1.2) with (- t1.1.2 + e1) by apply comm.
  rewrite dot_assoc. rewrite <- inv_right. rewrite one_left. 
  trivial.  replace (e2 + - t2.1.2) with (- t2.1.2 + e2) by apply comm.
  rewrite dot_assoc. rewrite <- inv_right. rewrite one_left. 
  trivial. 

  (* Case two*)
  intros. induction H6. rewrite H6.
  apply orb_true_iff. left. 
  apply special_soundness with (c:=c.1). apply H.
  apply H0. apply H6. apply H2. apply H3.

  intros.  apply orb_true_iff. 
  case_eq (Sigma.bool_eq sigma t1.1.2 t2.1.2). right. intros. simpl.
  apply special_soundness with (c:=c.2). apply H.
  apply H0. apply H6. apply H4. apply H5.

   intros. left.
  apply special_soundness with (c:=c.1).  apply H.
  apply H0.  apply H7. apply H2. apply H3.

  (* Zero knowledge *)
  (* part one *)
  unfold disSigmaProtocol. simpl. intros.
  pose (honest_verifier_ZK s.1 w (e + - r.2) r.1.1 t.1.1). destruct a.
  pose (honest_verifier_ZK s.1 w t.1.2 r.1.1 t.1.1). destruct a.
  case_eq (Sigma.Rel sigma s.1 w). intros. 
  split. intros. rewrite H5. simpl. 
  replace (e + - (e + - r.2)) with r.2. 
  rewrite <- chal_sim with (e:= (e + - r.2)); auto.
  rewrite <- pres_p0; auto. rewrite <- pres_v0; auto. rewrite H5 in H6. simpl in *.
  apply andb_true_iff in H6. destruct H6. 
  rewrite <- pres_p0 in H6; auto. rewrite <- pres_p1 in H6; auto. 
  rewrite <- pres_v0 in H6; auto. 
   apply H1 in H6. rewrite <- H6.
  apply injective_projections; auto. simpl. rewrite pres_p1; auto. 
  rewrite pres_v0; auto. apply injective_projections; auto. 
  simpl. apply injective_projections; auto. simpl. rewrite <- comp_v0; auto.
  symmetry. apply double_chall. destruct H2. rewrite H2. split. simpl. 
  replace (e + - (e + - r.2)) with r.2. do 2 rewrite <- surjective_pairing. trivial. 
  symmetry. apply double_chall. simpl. replace (e + - (e + - t.1.2)) with 
   t.1.2. destruct H4. rewrite H7. auto. do 2 rewrite <- surjective_pairing. trivial. 
  symmetry. apply double_chall.

  (* part two *)
  intros. rewrite H5. simpl. split. intros. 
  apply andb_true_iff in H6. destruct H6. 
  rewrite <- comp_v0 in H7; auto. rewrite (comp_v0 (s.2, (Sigma.P0 sigma s.2 r.1.1 w).2) (e + - r.2)) in H7; auto.
  rewrite <- pres_p0 in H7; auto. rewrite <- pres_p1 in H7; auto. 
  rewrite <- pres_v0 in H7; auto. simpl.  
  pose (honest_verifier_ZK s.2 w (e + - r.2) r.1.1 t.2). destruct a.
  apply H8 in H7. rewrite <- H7.
  apply injective_projections; auto. simpl. rewrite pres_p1; auto. 
  rewrite pres_v0; auto. apply injective_projections; auto. 
  simpl. apply injective_projections; auto. simpl. rewrite <- chal_sim; auto.
  simpl. rewrite <- comp_v0; auto. rewrite <- pres_p0; auto. apply f_equal.
  apply f_equal3; auto. rewrite pres_v0; auto. rewrite <- comp_v0; auto.
  split. destruct (honest_verifier_ZK s.2 w (e + - r.2) r.1.1 t.2).
   destruct H7. rewrite H7. do 2 rewrite <- surjective_pairing. trivial. 
  destruct (honest_verifier_ZK s.2 w (e + - t.1.2) r.1.1 t.2). destruct H7.
    rewrite H8.  do 2 rewrite <- surjective_pairing. trivial. 

  (* simulator correcntess *)
  unfold andSigmaProtocol. simpl. intros.
  apply andb_true_iff.
  split. rewrite pres_sim. rewrite <- surjective_pairing. 
  rewrite <- surjective_pairing. apply simulator_correct. apply H.
  rewrite pres_sim. rewrite <- chal_sim. 
  remember ((Sigma.simulator sigma s.2 t.2 (e + - t.1.2)).1.1) as a.
  remember ((Sigma.simulator sigma s.2 t.2 (e + - t.1.2)).2) as b.
  rewrite (chal_sim s.2 t.2 (e + - t.1.2)).
  rewrite Heqa. rewrite Heqb.
  rewrite <- surjective_pairing. 
  rewrite <- surjective_pairing. apply simulator_correct.
  apply H. apply H.
Qed.


End SigmaDis.


Section SigmaPar.
Delimit Scope SigmaPar with F.
Open Scope SigmaPar.

Generalizable Variables sigOne sigTwo.

Variable E E' : Set.

Context `{sigOne : Sigma.form E}.
Context `{sigTwo : Sigma.form E'}.

Theorem parCorr :
    SigmaProtocol sigOne ->
    SigmaProtocol sigTwo -> 
     SigmaProtocol (parSigmaProtocol sigOne sigTwo).
Proof.
  intros. constructor. unfold parSigmaProtocol. simpl.

  (** We need to prove the correctnes of the extended group*)
  constructor. constructor. constructor. intros.
  simpl. rewrite dot_assoc. rewrite dot_assoc. trivial.
  intros. simpl. rewrite one_left. rewrite one_left.
  rewrite <- surjective_pairing. trivial.
  intros. simpl. rewrite one_right. rewrite one_right.
  rewrite <- surjective_pairing. trivial.
  (*bool_eq_corr*)
  intros. refine (conj _ _). destruct a. destruct b. 
  simpl in *. intros. apply andb_true_iff in H1. destruct H1. 
  assert (e = e1). apply bool_eq_corr. apply H1.
  assert (e0 = e2). apply bool_eq_corr. apply H2.
  rewrite H3. rewrite H4. trivial.
  intro. apply andb_true_iff. split. apply bool_eq_corr.
  rewrite H1. trivial. apply bool_eq_corr. rewrite H1. 
  trivial.
  (* bool_eq_sym *)
  intros. rewrite bool_eq_sym. rewrite (bool_eq_sym a.2). trivial.
  (*bool_neq_corr*)
  intros.  refine (conj _ _).  intros. 
  apply andb_false_iff in H1.
  case_eq (Sigma.bool_eq sigOne a.1 b.1). 
  intros. rewrite H2 in H1. destruct H1. auto.
  apply bool_neq_corr in H1. unfold not. intro.
  rewrite H3 in H1. apply H1. trivial.
  intros.
  apply bool_neq_corr in H2. unfold not. intros.
  rewrite H3 in H2. apply H2. trivial.
  (*Fist part bool_neq_corr complete *)
  intro. unfold not in H1. unfold negb. 
  case_eq (Sigma.bool_eq sigOne a.1 b.1 &&
 Sigma.bool_eq sigTwo a.2 b.2). intro. apply andb_true_iff in H2.
  destruct H2. assert (a.2 = b.2).
  apply bool_eq_corr. apply H3. 
  assert (a.1 = b.1). apply bool_eq_corr. apply H2.
  destruct a. destruct b. simpl in *. rewrite H4 in H1. 
  rewrite H5 in H1. assert False. apply H1. trivial. contradiction. intro. trivial.
  (* disjoint sym *)
  intros. rewrite disjoint_sym. rewrite (disjoint_sym a.2). trivial.
  (* disjoint corr *)
  intros. apply andb_true_iff in H1. destruct H1. apply disjoint_corr in H1.
  unfold not in *. intros. apply H1. rewrite H3. trivial. 

  (* inv_left *)
  intros. simpl. rewrite <- inv_left. rewrite <- inv_left.
  trivial. intros. simpl.  rewrite <- inv_right.
  rewrite <- inv_right. trivial.

  (* comm *)
  intros. rewrite comm. remember (Sigma.add sigOne b.1 a.1) as one.
  rewrite comm. trivial.

  (* final proving sigma *)
  unfold parSigmaProtocol. simpl. intros. trivial.
  unfold parSigmaProtocol. simpl. intros. trivial.
  unfold parSigmaProtocol. simpl. intros. trivial.
  unfold parSigmaProtocol. simpl. intros. trivial.
  unfold parSigmaProtocol. simpl. intros. rewrite <- comp_v0.
  rewrite <- comp_v0. rewrite <- surjective_pairing. trivial.
  apply H0. apply H.
  unfold parSigmaProtocol. simpl. intros. rewrite <- chal_sim. 
  rewrite <- chal_sim.  rewrite <- surjective_pairing. trivial.
  apply H0. apply H.
  unfold parSigmaProtocol. simpl. intros. rewrite <- comp_sim1 with (s1:=s1.1)(s2:=s2.1).
  rewrite <- comp_sim1 with (s1:=s1.2)(s2:=s2.2). trivial.
  apply H0. apply H.
  unfold parSigmaProtocol. simpl. intros. 
  
  (* correcntess *)
  unfold parSigmaProtocol. simpl. intros. rewrite <- pres_p0.
  rewrite <- pres_p0. rewrite <- pres_v0. rewrite <- pres_v0. 
  rewrite <- pres_p1. rewrite <- pres_p1.
  apply andb_true_iff in H1. destruct H1.
  rewrite correctness.  apply H1. rewrite correctness.
  apply H2. trivial. apply H0. apply H. apply H0. apply H.
  apply H0. apply H.
  
  (* special soundness*)
  unfold parSigmaProtocol. simpl. intros. apply andb_true_iff.
  apply andb_true_iff in H1. destruct H1.
  apply andb_true_iff in H2. destruct H2.
  apply andb_true_iff in H3. destruct H3.
  split.

  apply special_soundness with (c:=c.1). apply H.
  apply H1. apply H2. apply H3.
  apply special_soundness with (c:=c.2). apply H0.
  apply H4. apply H5. apply H6.

  (* Zero knowledge *)
  unfold parSigmaProtocol. simpl. intros. 
  pose (honest_verifier_ZK s.1 w.1 e.1 r.1 t.1). destruct a.
  pose (honest_verifier_ZK s.2 w.2 e.2 r.2 t.2). destruct a.
  split. intros. apply andb_true_iff in H5. destruct H5. 
  rewrite <- pres_p0 in H5; auto. rewrite <- pres_v0 in H5; auto. 
  rewrite <- pres_p1 in H5; auto.
  rewrite <- pres_p0 in H6; auto. rewrite <- pres_v0 in H6; auto. 
  rewrite <- pres_p1 in H6; auto.
   apply H1 in H5.
   apply H3 in H6.
  rewrite <- H5. rewrite <- H6. apply injective_projections; auto.
  apply injective_projections; auto. apply injective_projections; auto.
  simpl. rewrite pres_p1; auto. simpl. rewrite pres_p1; auto. simpl.
  rewrite pres_v0; auto. simpl. rewrite pres_v0; auto. simpl.
  rewrite pres_p1; auto. simpl. rewrite pres_p1; auto. simpl.
  rewrite <- comp_v0; auto. rewrite <- comp_v0; auto.
  rewrite <- comp_v0; auto. rewrite <- comp_v0; auto. simpl.
  rewrite <- pres_p0; auto. rewrite <- pres_p0; auto.
  rewrite <- pres_v0; auto. rewrite <- pres_v0; auto. destruct H2.
  destruct H4. rewrite H2. rewrite H4. rewrite H5. rewrite H6.
  do 2 rewrite <- surjective_pairing; auto.

  (* Simulator correctness *)
  unfold parSigmaProtocol. simpl. intros. 
  apply andb_true_iff. split. rewrite pres_sim.
  rewrite <- surjective_pairing. rewrite <- surjective_pairing.
  apply simulator_correct. apply H.  rewrite pres_sim.
  rewrite <- surjective_pairing. rewrite <- surjective_pairing.
  apply simulator_correct. apply H0. 
Qed.

(* We now prove several helpful sublemmas about
  parralel that we use in Helios *)
Lemma ParVerLeft :
  forall (sig1 : Sigma.form E)(sig2 : Sigma.form E'),
    SigmaProtocol sig1 ->
    SigmaProtocol sig2 ->
  let sig3 := parSigmaProtocol sig1 sig2 in
  forall (s : Sigma.S  sig3)(c : Sigma.C sig3)(e : (E*E'))(t : Sigma.T sig3),
    (Sigma.V1 sig3 (s, c, e, t) = true) ->
   Sigma.V1 sig1 (s.1, c.1, e.1, t.1).
Proof.
  intros. unfold sig3 in *. unfold parSigmaProtocol in *. simpl in *.
  apply andb_true_iff in H1. destruct H1. apply H1.
Qed.

Lemma ParDisLeft :
  forall (sig1 : Sigma.form E)(sig2 : Sigma.form E'),
    SigmaProtocol sig1 ->
    SigmaProtocol sig2 ->
  let sig3 := parSigmaProtocol sig1 sig2 in
  forall (e1 e2 : (E*E')),
    (Sigma.disjoint sig3 e1 e2 = true) ->
   Sigma.disjoint sig1 e1.1 e2.1 = true.
Proof.
  intros. unfold sig3 in *. unfold parSigmaProtocol in *. simpl in *.
  apply andb_true_iff in H1. destruct H1. apply H1.
Qed.

Lemma ParExtLeft :
  forall (sig1 : Sigma.form E)(sig2 : Sigma.form E'),
    SigmaProtocol sig1 ->
    SigmaProtocol sig2 ->
  let sig3 := parSigmaProtocol sig1 sig2 in
  forall (s : Sigma.S sig3)(c : Sigma.C sig3)(e1 e2 : (E*E'))(t1 t2 : Sigma.T sig3),
    Sigma.Rel sig3 s (Sigma.extractor sig3 t1 t2 e1 e2) = true ->
   Sigma.Rel sig1 s.1 (Sigma.extractor sig1 t1.1 t2.1 e1.1 e2.1) = true.
Proof.
  intros. unfold sig3 in *. unfold parSigmaProtocol in *. simpl in *.
  apply andb_true_iff in H1. destruct H1. apply H1.
Qed.


Lemma ParStatment :
  forall (sig1 : Sigma.form E)(sig2 : Sigma.form E'),
  let sig3 := parSigmaProtocol sig1 sig2 in
    Sigma.S sig3 = prod (Sigma.S sig1) (Sigma.S sig2).
Proof.
  intros. unfold sig3 in *. unfold parSigmaProtocol in *. trivial.
Qed.

End SigmaPar.

Section SigmaAndGen.
Delimit Scope SigmaAndGen with F.
Open Scope SigmaAndGen.

Generalizable Variables sigOne sigTwo.

Variable E : Set.

Context `{sigOne : Sigma.form E}.
Context `{sigTwo : Sigma.form E}.



Theorem andGenCorr :
    SigmaProtocol sigOne ->
    SigmaProtocol sigTwo ->  
    (Sigma.disjoint sigOne = Sigma.disjoint sigTwo) ->
     SigmaProtocol (genAndSigmaProtocol sigOne sigTwo).
Proof.
  constructor; unfold genAndSigmaProtocol; simpl. apply e_abgrp;
  apply H. intros; unfold genAndSigmaProtocol; simpl; auto.
  intros; unfold genAndSigmaProtocol; simpl; auto.
  intros; unfold genAndSigmaProtocol; simpl; auto.
  intros; unfold genAndSigmaProtocol; simpl; auto.
  intros; unfold genAndSigmaProtocol; simpl; auto.
  intros; unfold genAndSigmaProtocol; simpl; auto.
  intros; unfold genAndSigmaProtocol; simpl; auto.
  replace ((Sigma.simulator sigOne s1.1 t.1 e).2) with ((Sigma.simulator sigOne s2.1 t.1 e).2) by (apply comp_sim1; apply H). 
  replace ((Sigma.simulator sigTwo s1.2 t.2 e).2) with ((Sigma.simulator sigTwo s2.2 t.2 e).2) by (apply comp_sim1; apply H0).
  trivial. 

  (** correctness *)
  unfold andSigmaProtocol. simpl. intros. 
  apply andb_true_iff in H2. destruct H2.
  rewrite <- pres_p0. rewrite <- pres_p1. 
  apply andb_true_iff. split.
  rewrite (comp_v0 (Sigma.P0 sigOne s.1 r.1 w.1) c).
  rewrite <- pres_v0. apply correctness. apply H. 
  apply H2. apply H. simpl.
  rewrite <- pres_p0. rewrite <- pres_p1. rewrite (comp_v0 (Sigma.P0 sigTwo s.2 r.2 w.2) c).
  rewrite <- pres_v0. apply correctness. apply H0.
  apply H3. apply H0. apply H0. apply H0. apply H. apply H. 

  (** special soundness *)
  unfold andSigmaProtocol. simpl. intros. 
  apply andb_true_iff. apply andb_true_iff in H3. apply andb_true_iff in H4.
  destruct H3. destruct H4. split. 
  apply special_soundness with (c:=c.1). apply H. apply H2. apply H3.
  apply H4. apply special_soundness with (c:=c.2). apply H0. rewrite <- H1. apply H2.
  apply H5. apply H6.

  (** Honest verifer zero knowledge *)
  simpl. intros. pose (honest_verifier_ZK s.1 w.1 e r.1 t.1).
  pose (honest_verifier_ZK s.2 w.2 e r.2 t.2). destruct a. destruct a0.
  split. intros. apply andb_true_iff in H6. destruct H6.
  rewrite <- pres_p0 in H6; auto. rewrite <- pres_p1 in H6; auto.
  rewrite (comp_v0 (Sigma.P0 sigOne s.1 r.1 w.1) e) in H6; auto.
  rewrite <- pres_v0 in H6; auto.
  rewrite <- pres_p0 in H7; auto. rewrite <- pres_p1 in H7; auto.
  rewrite (comp_v0 (Sigma.P0 sigTwo s.2 r.2 w.2) e) in H7; auto.
  rewrite <- pres_v0 in H7; auto.
  apply H2 in H6. apply H4 in H7. 
  (*Part 1*) 
  rewrite <- H6. rewrite <- H7. apply injective_projections; auto.
  apply injective_projections; auto. apply injective_projections; auto.
  simpl. do 2 (rewrite pres_p1; auto; simpl). 
  do 2 (rewrite pres_v0; auto; simpl). simpl. do 2 (rewrite <- pres_p0; auto).
  do 2 (rewrite pres_v0; rewrite <- comp_v0; simpl; auto). destruct H3; destruct H5.
  rewrite H3. rewrite H5. rewrite H6. rewrite H7. do 2 rewrite <- surjective_pairing;
  auto. 

  (* The simulator is always sound *)
  unfold andSigmaProtocol. simpl. intros. 
  apply andb_true_iff. do 2 rewrite pres_sim. 
  remember ((Sigma.simulator sigOne s.1 t.1 e).1.1) as b.
  remember ((Sigma.simulator sigOne s.1 t.1 e).2) as c. split.
  rewrite (chal_sim s.1 t.1 e). rewrite Heqb. rewrite Heqc.
  rewrite <- surjective_pairing. rewrite <- surjective_pairing.
  apply simulator_correct. apply H. 
  remember ((Sigma.simulator sigTwo s.2 t.2 e).1.1) as d.
  remember ((Sigma.simulator sigTwo s.2 t.2 e).2) as f.
  rewrite (chal_sim s.2 t.2 e). rewrite Heqd. rewrite Heqf.
  rewrite <- surjective_pairing. rewrite <- surjective_pairing.
  apply simulator_correct. apply H0.
Qed. 

End SigmaAndGen.
