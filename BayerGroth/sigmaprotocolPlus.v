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
Require Import Lia.
Set Implicit Arguments.

(* We pass in the challenge group as a parameter to make compilers easier 
    see below *)
Module Type SigmaPlus (E : GroupSig).

  Import E.

  Parameter St : Type.                                (* The set of statements *)
  Parameter W : Type.                                (* The set of witness *)
  Parameter Rel : St -> W -> bool.                 (* The relation function *)
  Parameter  C : Type.                              (* The set of commitments *)
  Parameter  R : Type.                              (* The set of random coins for the prover *)
    (*;                                   (* The set of challenges *) *)
  
  Parameter T : Type.                              (* The set of responses  *)
  Parameter P0 : St -> R -> W -> (St*C).            (* The initial step of the prover, outputs a commit *)
  Parameter P1 : (St*C*G) -> R -> W -> (St*C*G*T).  (* The final step of the prover, outputs a response *)
  Parameter V1 : (St*C*G*T) -> bool.              (* The final step of the verifier *)

   Parameter TE : Type.                             (* The output produced by simulator maper *)
   Parameter X  : Type. 
   Parameter simMapHelp : St -> X -> Prop.    (* We allow simpMap have information no ones else has *)
                                           
   Parameter simulator : St -> TE -> G -> (St*C*G*T). (* The simulator *)
   Parameter simMap    : St -> W -> G -> X -> R  ->  TE.    (* An explicit mapping between honest and simulated *)
   Parameter simMapInv : St -> W -> G -> X -> TE -> R.    (* A function we use to show simMap is a bijection 
      between R and T when fixing the other variables *)

   Parameter M : nat.
   Parameter extractor : (vector T M) -> (vector G M) -> (W).   (* The extractor *)
   Parameter fail_event : St -> C -> (vector G M) -> Prop. (* allows contructing an argument rather
    than a proof of inserting extra conditions *)
  
  (** We require the functions do not modifiy the previous transcript *)
  Axiom pres_p0 : forall (s : St)(r : R)(w : W), (P0 s r w) = (s,(P0 s r w).2).
  Axiom pres_p1 : forall (sce : St*C*G)(r : R)(w : W), 
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Axiom pres_sim : forall (s: St)(t : TE)(e : G),
      s = (simulator s t e).1.1.1.
  (** For composability we require that V0 maps E to E independent of S*C 
        note that when the Fiat-Shamir transfom is applied this no
        really holds but since the FSC is applied only to the highest
        level it dosn't matter *)
   (** We also require the simulator's challenge and response to be independent of the statment *)
  Axiom chal_sim : forall (s: St)(t : TE)(e : G),
    e = (simulator s t e).1.2.  

  (** Properties *)
  Axiom correctness : forall (s :St)(w:W)(r:R)(c: G),
    Rel s w ->
    V1 (P1 ((P0 s r w), c) r w) = true.

  Definition allDifferent (e : vector G M) := PairwisePredicate Gdisjoint e.

  Axiom special_soundness : forall (s : St)(c : C)(e : vector G M)(t : vector T M),
    (* Forall e it is disjoint from all e *)
    allDifferent e ->
    bVforall2 (fun e1 t1 => V1 (s, c, e1, t1)) e t -> 
    Rel s (extractor t e) = true \/ fail_event s c e.

  (* The concept here is that we want to show a bijection between 
    the transcripts produced honestly choosing r at random and the 
    transcripts produced by the simulator choosting t at random.  We used 
    to this by using a simulator map to produce the response and then 
    caculating the commitmnets (along with a checkthat the simMap was bijective
    using  the well known result that f is bijective if g(f(x)) = x and 
      f(g(y)) = y. *)

  (*In more complicated proofs this bijection still exists but it is no 
    longer between the response space and the randomness space, rather 
    it is between the response space and a slight enlarged version of the 
    response space.  Both simMap and simMapInv do not need to run in
    polynomial time *)

  Axiom honest_verifier_ZK :
    forall (s : St)(w : W)(e : G)(x : X)(r : R)(t : TE),
      simMapHelp s x ->
      Rel s w ->
      ((P1((P0 s r w), e) r w) =
      simulator s (simMap s w e x r) e) /\ 
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.

  Axiom simulator_correct : forall (s : St)(t : TE)(e : G),
    V1(simulator s t e) = true.

End SigmaPlus.

Module genAndSigmaProtocol (E : GroupSig)(S1 S2 : SigmaPlus E) <: SigmaPlus E.

  Import E.

  Definition St := prod S1.St S2.St.
  Definition W := prod S1.W S2.W.                            
  Definition Rel (st : St)(w : W) : bool := S1.Rel st.1 w.1 && S2.Rel st.2 w.2.                
  Definition  C : Type := prod S1.C S2.C.                         
  Definition  R : Type := prod S1.R S2.R.         
    
  Definition T : Type := prod S1.T S2.T.                     
  Definition P0 (st : St)(r : R)(w : W) : (St*C) := 
    (st, ((S1.P0 st.1 r.1 w.1).2, (S2.P0 st.2 r.2 w.2).2)).
  Definition P1 (sce : St*C*G)(r : R)(w : W) : (St*C*G*T) :=
    (sce, ((S1.P1 (sce.1.1.1, sce.1.2.1, sce.2) r.1 w.1).2, 
    (S2.P1 (sce.1.1.2, sce.1.2.2, sce.2) r.2 w.2).2)).
  Definition V1 (scet : St*C*G*T) : bool :=
    let s := scet.1.1.1 in
    let c := scet.1.1.2 in
    let e := scet.1.2 in
    let t := scet.2 in

    S1.V1 (s.1,c.1,e,t.1) && S2.V1 (s.2,c.2,e,t.2).

   Definition TE := prod S1.TE S2.TE.                           
   Definition X  : Type := prod S1.X S2.X. 
   Definition simMapHelp (st : St)(x : X) :=    
    S1.simMapHelp st.1 x.1 /\ S2.simMapHelp st.2 x.2.
                                           
   Definition simulator (st : St)(t : TE)(e : G) : (St*C*G*T) :=
    (st, ((S1.simulator st.1 t.1 e).1.1.2,(S2.simulator st.2 t.2 e).1.1.2),
     e, ((S1.simulator st.1 t.1 e).2,(S2.simulator st.2 t.2 e).2)).
  
   Definition simMap    (st : St)(w : W)(e : G)(x : X)(r : R) : TE :=
     (S1.simMap st.1 w.1 e x.1 r.1, S2.simMap st.2 w.2 e x.2 r.2).

   Definition simMapInv (st : St)(w : W)(e : G)(x : X)(t : TE) : R :=
      (S1.simMapInv st.1 w.1 e x.1 t.1, S2.simMapInv st.2 w.2 e x.2 t.2).

   Definition M : nat := max S1.M S2.M.
   Lemma sub1 : 0+S1.M <= M. 
   Proof.
    intros. unfold M. lia.
   Qed.
   Lemma sub2 : 0+S2.M <= M.
   Proof.
    intros. unfold M. lia.
   Qed.

   Definition extractor (t : vector T M)(e : vector G M) : W :=
    (S1.extractor (UnzipLeft (Vsub t sub1)) (Vsub e sub1), 
    S2.extractor (UnzipRight (Vsub t sub2)) (Vsub e sub2)).

   Definition fail_event (st : St)(c : C)(e : vector G M) : Prop :=
    S1.fail_event st.1 c.1 (Vsub e sub1) \/ S2.fail_event st.2 c.2 (Vsub e sub2). 
  
  (** We require the functions do not modifiy the previous transcript *)
  Lemma pres_p0 : forall (s : St)(r : R)(w : W), (P0 s r w) = (s,(P0 s r w).2).
  Proof.
    intros. trivial.
  Qed.

  Lemma pres_p1 : forall (sce : St*C*G)(r : R)(w : W), 
    (P1 sce r w) = (sce,(P1 sce r w).2).
  Proof.
    intros. trivial.
  Qed.

  Lemma pres_sim : forall (s: St)(t : TE)(e : G),
      s = (simulator s t e).1.1.1.
  Proof.
    intros. trivial.
  Qed.

  Lemma chal_sim : forall (s: St)(t : TE)(e : G),
    e = (simulator s t e).1.2.  
  Proof.
    intros. trivial.
  Qed.

  (** Properties *)
  Lemma correctness : forall (s :St)(w:W)(r:R)(c: G),
    Rel s w ->
    V1 (P1 ((P0 s r w), c) r w) = true.
  Proof.
    intros. unfold Rel, V1, P1, P0 in *. simpl. apply andb_true_iff in H. destruct H.
    apply andb_true_iff. split. pose S1.pres_p0. symmetry in e. rewrite e.
    pose S1.pres_p1. symmetry in e0. rewrite e0. apply S1.correctness; trivial.
    pose S2.pres_p0. symmetry in e. rewrite e.
    pose S2.pres_p1. symmetry in e0. rewrite e0. apply S2.correctness; trivial.
  Qed.

   Definition allDifferent (e : vector G M) := PairwisePredicate Gdisjoint e.

  Lemma special_soundness : forall (s : St)(c : C)(e : vector G M)(t : vector T M),
    (* Forall e it is disjoint from all e *)
    PairwisePredicate Gdisjoint e  ->
    bVforall2 (fun e1 t1 => V1 (s, c, e1, t1)) e t -> 
    Rel s (extractor t e) = true \/ fail_event s c e.
  Proof.
    pose module_abegrp. intros. unfold V1 in H0. assert (PairwisePredicate Gdisjoint e).
    trivial.  apply bVforall2Split in H0.
    destruct H0. apply (bVforall2_sub 0 S1.M sub1) in H0. 
    apply (bVforall2_sub 0 S2.M sub2) in H2. 
    apply (PairwisePredicate_sub 0 S1.M sub1) in H.
    apply (PairwisePredicate_sub 0 S2.M sub2) in H1. simpl in H0. simpl in H2.
    (* Lets get the underlying soundness out *)
    assert (bVforall2 (fun a' b' => S1.V1 (s.1, c.1, a', b')) (Vsub e sub1) 
    (UnzipLeft (Vsub t sub1))). apply (bVforall2_follows (fun a => a.1) 
    (fun a' b' => S1.V1 (s.1, c.1, a', b')) (fun a' b' => S1.V1 (s.1, c.1, a', b'.1)) 
    (Vsub e sub1) (Vsub t sub1) H0). intros. apply H3. 
    pose (S1.special_soundness s.1 c.1 (Vsub e sub1) 
    (UnzipLeft (Vsub t sub1)) H H3) as H5.
    assert (bVforall2 (fun a' b' => S2.V1 (s.2, c.2, a', b')) (Vsub e sub2) 
    (UnzipRight (Vsub t sub2))). apply (bVforall2_follows (fun a => a.2) 
    (fun a' b' => S2.V1 (s.2, c.2, a', b')) (fun a' b' => S2.V1 (s.2, c.2, a', b'.2)) 
    (Vsub e sub2) (Vsub t sub2) H2). intros. apply H4. 
    pose (S2.special_soundness s.2 c.2 (Vsub e sub2) 
    (UnzipRight (Vsub t sub2)) H1 H4) as H6.
    (* Now the main line *)
    unfold fail_event, Rel, extractor. destruct H5. destruct H6. left.
    apply andb_true_iff.  split; trivial.
    right. right. trivial. right. left. trivial. apply disjoint_sym.
    apply disjoint_sym.
  Qed.

  Lemma honest_verifier_ZK :
    forall (s : St)(w : W)(e : G)(x : X)(r : R)(t : TE),
      simMapHelp s x ->
      Rel s w ->
      ((P1((P0 s r w), e) r w) =
      simulator s (simMap s w e x r) e) /\ 
      simMapInv s w e x (simMap s w e x r) = r /\
      simMap s w e x (simMapInv s w e x t) = t.
  Proof.
    intros. destruct H. apply andb_true_iff in H0. destruct H0.
    unfold P1, P0, simulator, simMap, simMapInv in *.
    pose (S1.honest_verifier_ZK e r.1 t.1 H H0). 
    pose (S2.honest_verifier_ZK e r.2 t.2 H1 H2). 
    destruct a. destruct a0.
    split; simpl. rewrite <- H3. rewrite <- H5. apply injective_projections;
    simpl. apply injective_projections; simpl. apply injective_projections; simpl.
    trivial. apply injective_projections; simpl. rewrite S1.pres_p1. simpl.
    trivial. rewrite S2.pres_p1. simpl. trivial. trivial.
    rewrite <- S1.pres_p0. rewrite <- S2.pres_p0. trivial.
    destruct H4. destruct H6. split; apply injective_projections; simpl. 
    apply H4. apply H6. apply H7. apply H8.
  Qed.

  Lemma simulator_correct : forall (s : St)(t : TE)(e : G),
    V1(simulator s t e) = true.
  Proof.
    intros. unfold V1, simulator. apply andb_true_iff; split; simpl.
    remember (S1.simulator s.1 t.1 e). rewrite (S1.pres_sim s.1 t.1 e). 
    rewrite <- Heqp. rewrite (S1.chal_sim s.1 t.1 e). rewrite <- Heqp. auto.
    do 3 rewrite <- surjective_pairing. rewrite Heqp. apply S1.simulator_correct.
    remember (S2.simulator s.2 t.2 e). rewrite (S2.pres_sim s.2 t.2 e). 
    rewrite <- Heqp. rewrite (S2.chal_sim s.2 t.2 e). rewrite <- Heqp. auto.
    do 3 rewrite <- surjective_pairing. rewrite Heqp. apply S2.simulator_correct.
  Qed.

End genAndSigmaProtocol.
