Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import groups.
Require Import sigmaprotocol.
Require Import Coq.Lists.List.
Require Import Quote.
Require Import Ring.
Require Import Field. 
Require Import Field_theory.
Require Import HeliosIACR2018.
Require Import cryptoprim.
Require Import matrices.


Infix "+" := Fadd.
Infix "*" := Fmul.
Notation "x / y" := (Fmul x (FmulInv y)). 
Notation "0" := Fzero.
Notation "1" := Fone.
Notation "- x" :=  (Finv x).
Notation "x - y" := (x + (- y)).

Infix "o" := Gdot (at level 50) .
Notation "\ x" := (Ginv x) (at level 50) .

Infix "^" := op.

(** Begin Sigma Proper *)
(* We pass why to allow branching in disjunction *)
Definition valid_P0 (ggtox : G*G)(r : F)(w : F) : (G*G*G) :=
  let g := ggtox.1 in 
  (ggtox, g^r).

Definition valid_V0 (ggtoxgtor: G*G*G) (c: F): (G*G*G*F)
  := (ggtoxgtor, c).

Definition valid_P1 (ggtoxgtorc: G*G*G*F) (r x: F) : G*G*G*F*F :=
  let c    :=  snd (ggtoxgtorc) in
  let s:= (r + c*x) in (ggtoxgtorc, s).

Definition valid_V1 (ggtoxgtorcs : G*G*G*F*F) :=
  let g    :=  fst (fst (fst (fst ggtoxgtorcs))) in
  let gtox :=  snd (fst (fst (fst ggtoxgtorcs))) in
  let gtor :=  snd (fst (fst ggtoxgtorcs)) in
  let c    :=  snd (fst ggtoxgtorcs) in
  let s    :=  snd ggtoxgtorcs in
  Gbool_eq (g^s) ((gtox^c) o gtor).

Definition simulator_mapper (s : G*G)(r c x :F):=
  (r+x*c).

Definition simulator (ggtox :G*G)(z e : F) :=
let g := fst ggtox in
let gtox := snd ggtox in
  (ggtox, g^(z) o \ gtox^e, e, z).

Definition extractor (s1 s2 c1 c2 : F) :=
  (s1 - s2) / (c1 - c2).

Definition disjoint (c1 c2 : F) :=
  negb (Fbool_eq c1 c2).

Definition dLogForm : Sigma.form F := Sigma.mkForm F (prod G G) F dLog G F
  Fadd Fzero Finv Fbool_eq disjoint F valid_P0 valid_V0 valid_P1 valid_V1
 simulator simulator_mapper extractor.

Theorem dLogSigma
  :CompSigmaProtocol F dLogForm. 
Proof.
  pose HeliosIACR2018.
  assert (AbeGroup F Fadd 0 Fbool_eq Finv).  apply (field_additive_abegrp (F)(Fadd)(Fzero)
  (Fbool_eq) (Fsub)(Finv)(Fmul) (Fone)(FmulInv)(Fdiv)). apply v. apply v. apply v.
  destruct v. destruct vs_field. destruct F_R.   pose HeliosIACR2018.
   constructor. constructor. constructor.  unfold dLogForm. cbn in *. apply H.
  + intros. trivial.
(* Comp and prev prop *)
  + intros. unfold valid_P0. trivial.
  + intros. unfold valid_V0.  trivial.
  + intros. unfold valid_P1. trivial.
  + intros. unfold valid_V0. trivial.
  + intros. unfold valid_P1. trivial. 
  + intros. unfold simulator. trivial.
  + intros. unfold dLogForm. simpl. trivial.

(* Correctness *)
+ intros. cbn in *.
  unfold valid_V1, valid_P1, valid_V0, valid_P0.
  cbn.  unfold dLog in H0. assert (s.2 = (s.1 ^ w)). rewrite <- bool_eq_corr.
  apply H0. rewrite H1.
  rewrite <- mod_dist_Fmul, <- mod_dist_Fadd, comm, bool_eq_corr. 
  trivial.
 
(* Special soundness *)
+ cbn. intros.  unfold extractor. unfold dLog. rewrite bool_eq_corr. 
  rewrite Radd_comm. rewrite mod_dist_Fmul.  assert ((e1 - e2) <> 0). 
  apply (zero2 (dot:=Fadd)(Aone:=Fzero)(bool_equal:=Fbool_eq)(Ainv:=Finv)).  
  rewrite <- bool_neq_corr. cbn in H0. unfold dLogForm in H0. simpl in H0. unfold disjoint in H0. 
  apply negb_false_iff in H0. rewrite negb_involutive in H0. apply H0. cbn in *.
  apply op_cancel with (x:= (e1 - e2)).  apply H3.
  do 2 rewrite <- mod_dist_Fmul. rewrite Rmul_comm.
  rewrite Rmul_assoc. rewrite Finv_l. apply H3. rewrite Rmul_1_l. 
  (** We have now proved g^(s1 - s2) = gtox ^ (c1 - c2) *)
  rewrite mod_dist_Fadd. rewrite <- neg_eq. unfold dLogForm in H1. unfold dLogForm in H2.
  unfold valid_V1 in H1.  unfold valid_V1 in H2. simpl in *.  rewrite mod_dist_Fadd.
  apply bool_eq_corr in H1. apply bool_eq_corr in H2. symmetry. rewrite <- neg_eq. symmetry.
  rewrite H1. rewrite H2.  remember (s.2^e1) as a. remember (s.2^e2) as b.
  symmetry. rewrite comm. rewrite <- dot_assoc. apply left_cancel.
  assert (\(b o c) = (\b o \c)). symmetry. apply inv_dist. rewrite H4. rewrite comm.
  rewrite <- dot_assoc. rewrite <- inv_left. rewrite one_right. rewrite <- one_right.
  symmetry. rewrite <- one_right. apply left_cancel. intuition. (* Again, I am surprised that auto,
  trivial is not working. This project is literally testing the Coq internals *)

(* honest verifier ZK *)
  + intros. cbn in *. unfold dLogForm. simpl.
  split. unfold simulator_mapper. unfold simulator.  unfold valid_P1. unfold valid_V0. unfold valid_P0.
  simpl. unfold dLog in H0. replace (s.2) with (s.1 ^ w). 
  rewrite neg_eq. rewrite <- mod_dist_Fmul.
  rewrite <- mod_dist_Fadd. rewrite <- dot_assoc. 
  replace (w * e) with (e * w) by apply Rmul_comm.
  replace (e * w + (Finv e * w)) with Fzero.
  rewrite one_right. trivial. Add Field vs_field : Ffield. ring; auto.  
  unfold dLogForm in H0. unfold dLog in H0. cbn in H0. symmetry. rewrite <- bool_eq_corr. apply H0.
  (** Part one completed *)
  intros. exists (t + Finv (w * e)). unfold simulator_mapper.
  rewrite <- dot_assoc.
  rewrite <- inv_left. rewrite one_right. trivial.
  
  + intros. cbn in *. unfold dLogForm. simpl. unfold valid_V1. cbn. unfold simulator. simpl. 
  replace (s.1 ^ t o \ s.2 ^ e) with (\ s.2 ^ e o s.1 ^ t) by apply comm.
  rewrite dot_assoc. rewrite <- inv_right. rewrite one_left. 
  rewrite bool_eq_corr. trivial.

  + intros. unfold valid_P1. trivial.
  
  + intros. unfold simulator_mapper. trivial.
Qed. 

(* We have now defined and proved the sigma protocol for discrete log *)

(*We now define an empty sigma form though with real types for some reason
  we need this to define the later generaters nicely*)
Definition emptyRel (s : G)(w : F): bool := 
  true.

Definition empty_P0 (g : G)(r : F)(w : F) : (G*G) :=
  (g,g).
  
Definition empty_V0 (g: G*G) (c: F): (G*G*F):=
   (g, c).

Definition empty_P1 (g: G*G*F) (r x: F) : G*G*F*F :=
  (g, g.2).

Definition empty_V1 (g : G*G*F*F) :=
  true.

Definition empty_simulator_mapper (s : G)(r c x :F):=
  (r).

Definition empty_simulator (g :G)(z e : F) :=
  (g, g, e, e).

Definition empty_mapper (s1 s2 c1 c2 : F) :=
  (s1 - s2) / (c1 - c2).

Definition emptyForm : Sigma.form F := Sigma.mkForm F G F emptyRel G F
  Fadd Fzero Finv Fbool_eq disjoint F empty_P0 empty_V0 empty_P1 empty_V1
 empty_simulator empty_simulator_mapper empty_mapper.

Theorem emptySigma
  :CompSigmaProtocol F emptyForm.
Proof.
  pose HeliosIACR2018.
  assert (AbeGroup F Fadd 0 Fbool_eq Finv). apply (field_additive_abegrp (F)(Fadd)(Fzero)
  (Fbool_eq) (Fsub)(Finv)(Fmul) (Fone)(FmulInv)(Fdiv)). apply v. apply v. apply v.
  destruct v. destruct vs_field. destruct F_R.   pose HeliosIACR2018.
   constructor. constructor. constructor.  unfold emptyForm. cbn in *. apply H. trivial.
  (*Begining main lemmas *)
  + intros. trivial.
  + intros. trivial.
  + intros. trivial.
  + intros. trivial.
  + intros. trivial.
  + intros. trivial.
  + intros. trivial.
  + intros. trivial.
  + intros. trivial.  
  + intros. unfold emptyForm. cbn. split. trivial.
    intros. exists t. trivial.
  + intros. trivial. 
  + intros. trivial. 
  + intros. trivial.
Qed. 

Lemma ExtractorHelper :
  forall(a b :G)(e1 e2 : F),
  e1 - e2 <> 0 ->
  b = ((a o b^e1) o \ (a o b^e2))^(FmulInv (e1 - e2)).
Proof.
  pose HeliosIACR2018.
  intros. remember (b ^ e1) as c. remember (b ^ e2) as d.
  replace (a o c) with (c o a). rewrite <- dot_assoc. 
  replace (\ (a o d)) with (\a o \d). replace (a o ((\ a) o (\ d)))
  with (\d). rewrite Heqc. rewrite Heqd. rewrite neg_eq.
  rewrite <- mod_dist_Fadd. rewrite <- mod_dist_Fmul.
  replace (FmulInv (e1 - e2) * (e1 - e2)) with 1. symmetry. apply mod_id.
  field; auto. rewrite dot_assoc. rewrite <- inv_right.
  rewrite one_left. trivial. apply inv_dist. apply comm.
Qed.

Lemma ExtractorHelper2 :
  forall(a b :G)(e1 e2 : F),
  e1 - e2 <> 0 ->
  b = ((b^e1 o a) o \ (b^e2 o a))^(FmulInv (e1 - e2)).
Proof.
  pose HeliosIACR2018. intros. replace (b^e1 o a) with (a o b^e1).
  replace (b ^ e2 o a) with (a o b^e2). apply ExtractorHelper.
  apply H. apply comm. apply comm. 
Qed.

Definition dLog2 (s :G*G*G)(w : F*F) := 
  let g     := s.1.1 in
  let h     := s.1.2 in
  let gtox  := s.2 in 
  Gbool_eq gtox (PC g h w.1 w.2).


(** Begin Sigma Proper *)
(* We pass why to allow branching in disjunction *)
Definition dLog2_P0 (ggtox : G*G*G)(r : F*F)(w : F*F) : (G*G*G*G) :=
  let g := ggtox.1.1 in 
  let h := ggtox.1.2 in 
  (ggtox, PC g h r.1 r.2).

Definition dLog2_V0 (ggtoxgtor: G*G*G*G) (c: F): (G*G*G*G*F)
  := (ggtoxgtor, c).

Definition dLog2_P1 (ggtoxgtorc: G*G*G*G*F) (r x: F*F) : G*G*G*G*F*(F*F) :=
  let c    :=  snd (ggtoxgtorc) in
  let s1  := (r.1 + x.1*c) in 
  let s2  := (r.2 + x.2*c) in 
  (ggtoxgtorc, (s1, s2)).

Definition dLog2_V1 (ggtoxgtorcs :  G*G*G*G*F*(F*F)) :=
  let g    :=  ggtoxgtorcs.1.1.1.1.1 in
  let h    :=  ggtoxgtorcs.1.1.1.1.2 in
  let gtox :=  ggtoxgtorcs.1.1.1.2 in
  let gtor :=  ggtoxgtorcs.1.1.2 in
  let c    :=  ggtoxgtorcs.1.2 in
  let s1   :=  ggtoxgtorcs.2.1 in
  let s2   :=  ggtoxgtorcs.2.2 in
  Gbool_eq (PC g h s1 s2) ((gtox^c) o gtor).

Definition dLog2_simulator_mapper (s : G*G*G)(r : F*F)(c :F)( x :F*F):=
  ((r.1+x.1*c),(r.2+x.2*c)).

Definition dLog2_simulator (ggtox :G*G*G)(z : F*F)(e : F) :=
let g :=  ggtox.1.1 in
let h :=  ggtox.1.2 in
let gtox := snd ggtox in
  (ggtox, PC g h z.1 z.2 o \ gtox^e, e, z).

Definition dLog2_extractor (s1 s2 :F*F)(c1 c2 : F) :=
  ((s1.1 - s2.1) / (c1 - c2),(s1.2 - s2.2) / (c1 - c2)).

Definition dLog2Form : Sigma.form F := Sigma.mkForm F (G*G*G) (F*F) dLog2 G (F*F)
  Fadd Fzero Finv Fbool_eq disjoint (F*F) dLog2_P0 dLog2_V0 dLog2_P1
  dLog2_V1 dLog2_simulator dLog2_simulator_mapper dLog2_extractor.

(* Some random PC lemmas that belong elsewhere *)
Lemma PCExp : forall (g h : G)(m r c : F),
  PC g h m r ^ c = PC g h (m*c) (r*c).
Proof.
  pose HeliosIACR2018.
  intros. unfold PC. rewrite mod_dist_Gdot. do 2 rewrite <- mod_dist_FMul2.
  trivial.
Qed.

Lemma PCMult : forall (g h : G)(m1 m2 r1 r2 : F),
  PC g h m1 r1 o PC g h m2 r2 = PC g h (m1+m2) (r1+r2).
Proof.
  pose HeliosIACR2018.
  intros. unfold PC. do 2 rewrite mod_dist_Fadd. do 2 rewrite dot_assoc.
  apply right_cancel. do 2 rewrite <- dot_assoc. apply left_cancel.
  apply comm.
Qed.

Lemma PCneg : forall (g h : G)(m r : F),
  \ PC g h m r = PC g h (Finv m) (Finv r).
Proof.
  pose HeliosIACR2018.
  intros. unfold PC.  rewrite <- neg_eq. rewrite <- neg_eq.
  remember (g^r) as a. remember (h^m) as b.   destruct v.
  symmetry.  
  apply (@inv_dist G Gdot Gone Gbool_eq Ginv module_abegrp a b).
Qed.

Theorem EPCExp :
   forall(h : G)(hs : V2G),
   forall v : V2F, 
   forall a r : F, 
   EPC h hs (V2F_scale v a) (r*a) = (EPC h hs v r) ^ a.
Proof.
  pose HeliosIACR2018. intros. unfold V2F_scale. unfold EPC.
  rewrite mod_dist_Gdot. rewrite mod_dist_FMul2. apply left_cancel.
  unfold V2G_Pexp. unfold V2G_prod. simpl. rewrite mod_dist_Gdot.
  do 2 rewrite mod_dist_FMul2. trivial.
Qed.


Lemma EPCMult : forall (g : G)(hs : V2G),
                forall (m1 m2 : V2F)(r1 r2 : F), 
  EPC g hs m1 r1 o EPC g hs m2 r2 = EPC g hs (V2F_add m1 m2) (r1+r2).
Proof.
  pose HeliosIACR2018.
  intros. unfold EPC. rewrite <- dot_assoc. rewrite mod_dist_Fadd.
  symmetry. rewrite <- dot_assoc. apply left_cancel. symmetry.
  rewrite comm. rewrite <- dot_assoc. apply left_cancel.
  apply V2F_add_product.
Qed.

Lemma EPCneg : forall (g : G)(hs : V2G)(m : V2F)(r : F),
  \ EPC g hs m r = EPC g hs (V2F_neg m) (Finv r).
Proof.
  pose HeliosIACR2018.
  intros. unfold EPC. rewrite <- neg_eq. rewrite V2F_neg_inv.
  remember (g^r) as a. remember (V2G_prod (V2G_Pexp hs m)) as b. 
  symmetry. apply (@inv_dist G Gdot Gone Gbool_eq Ginv module_abegrp a b).
Qed.

Theorem dLogSigma2
  :CompSigmaProtocol F dLog2Form. 
Proof.
  pose HeliosIACR2018.  unfold dLog2Form in *. simpl in *.
  assert (AbeGroup F Fadd 0 Fbool_eq Finv).  apply (field_additive_abegrp (F)(Fadd)(Fzero)
  (Fbool_eq) (Fsub)(Finv)(Fmul) (Fone)(FmulInv)(Fdiv)). apply v. apply v. apply v.
  destruct v. destruct vs_field. destruct F_R.   
   constructor. constructor. constructor. cbn in *. apply H.
  + intros. trivial.
(* Comp and prev prop *)
  + intros. unfold valid_P0. trivial.
  + intros. unfold valid_V0.  trivial.
  + intros. unfold valid_P1. trivial.
  + intros. unfold valid_V0. trivial.
  + intros. unfold valid_P1. trivial. 
  + intros. unfold simulator. trivial.
  + intros. unfold dLogForm. simpl. trivial.

(* Correctness *)
+ intros. unfold dLog2Form in *. simpl in *.
  unfold dLog2_V1, dLog2_P1, dLog2_V0, dLog2_P0. simpl.
  unfold dLog2 in H0. assert (s.2 = PC s.1.1 s.1.2 w.1 w.2). 
  rewrite <- bool_eq_corr. apply H0. rewrite H1.
  rewrite bool_eq_corr. rewrite PCExp. symmetry. rewrite comm. 
  rewrite PCMult. intuition.
  
(* Special soundness *)
+ intros. pose HeliosIACR2018.
  unfold dLog2_V1 in *. simpl in *. unfold dLog2_extractor.
  unfold dLog2. simpl. rewrite bool_eq_corr. apply bool_eq_corr in H1.
  apply bool_eq_corr in H2. rewrite <- PCExp. rewrite <- PCMult.
  rewrite <- PCneg. rewrite H1. rewrite H2. apply ExtractorHelper2.
  unfold disjoint in H0. apply negb_false_iff in H0. rewrite negb_involutive in H0.
  apply F_bool_neq_corr in H0.  unfold not in *. intros. 
  apply shift in H3. rewrite H3 in H0. apply H0. trivial.

(* honest verifier ZK *)
  + intros. cbn in *. unfold dLog2Form. simpl.
  split. unfold dLog2_simulator_mapper. unfold dLog2_simulator.
  unfold dLog2_P1. unfold dLog2_V0. unfold dLog2_P0.
  simpl. unfold dLog2 in H0. apply bool_eq_corr in H0.
  rewrite H0. symmetry. rewrite PCExp. rewrite PCneg.
  rewrite PCMult. replace (r.1 + w.1 * e - w.1 * e) with r.1.
  replace (r.2 + w.2 * e - w.2 * e) with r.2. trivial.
  field; auto. field; auto.   
  (** Part one completed *)
  intros. exists (t.1 + Finv (w.1 * e), t.2 + Finv (w.2 * e)). 
  unfold dLog2_simulator_mapper. simpl. 
  replace (t.1 - w.1 * e + w.1 * e) with t.1. 
  replace (t.2 - w.2 * e + w.2 * e) with t.2. apply surjective_pairing.
  field; auto. field; auto. 
  
  + intros. simpl in *. unfold dLog2_V1. simpl. rewrite bool_eq_corr.
   rewrite comm.  rewrite <- dot_assoc. rewrite <- inv_left.
    rewrite one_right. trivial.

  + intros. unfold valid_P1. trivial.
  
  + intros. unfold simulator_mapper. trivial.
Qed. 

Definition dLog3 (s :G*V2G*G)(w : V2F*F) := 
  let g     := s.1.1 in
  let hs     := s.1.2 in
  let gtox  := s.2 in 
  Gbool_eq gtox (EPC g hs w.1 w.2).

Definition dLog3_P0 (ggtox : G*V2G*G)(r : V2F*F)(w : V2F*F) : (G*V2G*G*G) :=
  let g := ggtox.1.1 in 
  let hs := ggtox.1.2 in 
  (ggtox, EPC g hs r.1 r.2).

Definition dLog3_V0 (ggtoxgtor: G*V2G*G*G) (c: F): (G*V2G*G*G*F)
  := (ggtoxgtor, c).

Definition dLog3_P1 (ggtoxgtorc: G*V2G*G*G*F) (r x: V2F*F) : G*V2G*G*G*F*(V2F*F) :=
  let c    :=  snd (ggtoxgtorc) in
  let s1  := V2F_add r.1 (V2F_scale x.1 c) in 
  let s2  := (r.2 + x.2*c) in 
  (ggtoxgtorc, (s1, s2)).

Definition dLog3_V1 (ggtoxgtorcs : G*V2G*G*G*F*(V2F*F)) :=
  let g    :=  ggtoxgtorcs.1.1.1.1.1 in
  let hs   :=  ggtoxgtorcs.1.1.1.1.2 in
  let gtox :=  ggtoxgtorcs.1.1.1.2 in
  let gtor :=  ggtoxgtorcs.1.1.2 in
  let c    :=  ggtoxgtorcs.1.2 in
  let s1   :=  ggtoxgtorcs.2.1 in
  let s2   :=  ggtoxgtorcs.2.2 in
  Gbool_eq (EPC g hs s1 s2) ((gtox^c) o gtor).

Definition dLog3_simulator_mapper (s : G*V2G*G)(r : V2F*F)(c :F)( x :V2F*F):=
  ((V2F_add r.1 (V2F_scale x.1 c)),(r.2+x.2*c)).

Definition dLog3_simulator (ggtox :G*V2G*G)(z : V2F*F)(e : F) :=
let g :=  ggtox.1.1 in
let hs :=  ggtox.1.2 in
let gtox := snd ggtox in
  (ggtox, EPC g hs z.1 z.2 o \ gtox^e, e, z).

Definition dLog3_extractor (s1 s2 :V2F*F)(c1 c2 : F) :=
  (V2F_scale (V2F_add s1.1 (V2F_neg s2.1)) (FmulInv (c1 - c2)),(s1.2 - s2.2) / (c1 - c2)).

Definition dLog3Form : Sigma.form F := Sigma.mkForm F (G*V2G*G) (V2F*F) dLog3 G (V2F*F)
  Fadd Fzero Finv Fbool_eq disjoint (V2F*F) dLog3_P0 dLog3_V0 dLog3_P1
  dLog3_V1 dLog3_simulator dLog3_simulator_mapper dLog3_extractor.

Theorem dLogSigma3
  :CompSigmaProtocol F dLog3Form. 
Proof.
  pose HeliosIACR2018.  unfold dLog3Form in *. simpl in *.
  assert (AbeGroup F Fadd 0 Fbool_eq Finv).  apply (field_additive_abegrp (F)(Fadd)(Fzero)
  (Fbool_eq) (Fsub)(Finv)(Fmul) (Fone)(FmulInv)(Fdiv)). apply v. apply v. apply v.
  destruct v. destruct vs_field. destruct F_R.   
   constructor. constructor. constructor. cbn in *. apply H.
  + intros. trivial.
(* Comp and prev prop *)
  + intros. unfold valid_P0. trivial.
  + intros. unfold valid_V0.  trivial.
  + intros. unfold valid_P1. trivial.
  + intros. unfold valid_V0. trivial.
  + intros. unfold valid_P1. trivial. 
  + intros. unfold simulator. trivial.
  + intros. unfold dLogForm. simpl. trivial.

(* Correctness *)
+ intros. unfold dLog3Form in *. simpl in *.
  unfold dLog3_V1, dLog3_P1, dLog3_V0, dLog3_P0. simpl.
  unfold dLog3 in H0. assert (s.2 = EPC s.1.1 s.1.2 w.1 w.2). 
  rewrite <- bool_eq_corr. apply H0. rewrite H1.
  rewrite bool_eq_corr. rewrite <- EPCExp. symmetry. rewrite comm. 
  rewrite EPCMult. intuition.
  
(* Special soundness *)
+ intros. pose HeliosIACR2018.
  unfold dLog3_V1 in *. simpl in *. unfold dLog3_extractor.
  unfold dLog3. simpl. rewrite bool_eq_corr. apply bool_eq_corr in H1.
  apply bool_eq_corr in H2. rewrite EPCExp.  rewrite <- EPCMult.
  rewrite <- EPCneg.  rewrite H1. rewrite H2. apply ExtractorHelper2.
  unfold disjoint in H0. apply negb_false_iff in H0. rewrite negb_involutive in H0.
  apply F_bool_neq_corr in H0. unfold not in *. intros. 
  apply shift in H3. rewrite H3 in H0. apply H0. trivial.

(* honest verifier ZK *)
  + intros. cbn in *. unfold dLog3Form. simpl.
  split. unfold dLog3_simulator_mapper. unfold dLog3_simulator.
  unfold dLog3_P1. unfold dLog3_V0. unfold dLog3_P0.
  simpl. unfold dLog3 in H0. apply bool_eq_corr in H0.
  rewrite H0. symmetry. rewrite <- EPCExp. rewrite EPCneg.
  rewrite EPCMult.  replace (r.2 + w.2 * e - w.2 * e) with r.2. 
  rewrite V2F_add_neg. trivial.
  field; auto. 
  (** Part one completed *)
  intros. exists (V2F_add t.1 (V2F_neg (V2F_scale w.1 e)), t.2 + Finv (w.2 * e)). 
  unfold dLog3_simulator_mapper. simpl. remember (V2F_scale w.1 e) as a.
  replace (t.2 - w.2 * e + w.2 * e) with t.2. rewrite V2F_add_ass.
  replace (V2F_add (V2F_neg a) a) with (V2F_add a (V2F_neg a)). 
  rewrite <- V2F_add_ass. rewrite V2F_add_neg. apply surjective_pairing.
  apply V2F_comm. field; auto. 
  
  + intros. simpl in *. unfold dLog3_V1. simpl. rewrite bool_eq_corr.
   rewrite comm.  rewrite <- dot_assoc. rewrite <- inv_left.
    rewrite one_right. trivial.

  + intros. unfold valid_P1. trivial.
  
  + intros. unfold simulator_mapper. trivial.
Qed. 

(* This last sigma would preferable be generated by using composition
  but at present the compilers don't support this *)

Definition u'_Rel (s : (G*G*G*V2G*(V2G*V2G))*(G*V2G*V2G))(w : V2F*F*F*V2F) := 
  let parm := s.1 in
  let g := parm.1.1.1.1 in
  let pk := parm.1.1.1.2 in
  let h := parm.1.1.2 in
  let hs := parm.1.2 in
  let e' := parm.2 in

  let stat := s.2 in
  let a := stat.1.1 in
  let b := stat.1.2 in
  let cHat := stat.2 in

  let u' := w.1.1.1 in
  let rTil := w.1.1.2 in
  let rStar := w.1.2 in
  let rHat := w.2 in

  Gbool_eq a (EPC h hs u' rTil) && 
  V2G_eq b (V2G_mult (V2G_Tprod (ciphExp e' u')) (Enc g pk rStar Gone)) &&
  Gbool_eq (m1 cHat) (PC h (m1 hs) (r1 u') (r1 rHat)) && 
  Gbool_eq (m2 cHat) (PC h (m1 cHat) (r2 u') (r2 rHat)).


(** Begin Sigma Proper *)
(* We pass why to allow branching in disjunction *)
Definition u'_P0 (s : (G*G*G*V2G*(V2G*V2G))*(G*V2G*V2G))
    (r w : V2F*F*F*V2F) : (G*G*G*V2G*(V2G*V2G))*(G*V2G*V2G)*(G*V2G*V2G) :=
  let parm := s.1 in
  let g := parm.1.1.1.1 in
  let pk := parm.1.1.1.2 in
  let h := parm.1.1.2 in
  let hs := parm.1.2 in
  let e' := parm.2 in

  let stat := s.2 in
  let a := stat.1.1 in
  let b := stat.1.2 in
  let cHat := stat.2 in

  let u' := w.1.1.1 in
  let rTil := w.1.1.2 in
  let rStar := w.1.2 in
  let rHat := w.2 in

  let w' := r.1.1.1 in 
  let w3 := r.1.1.2 in
  let w4 := r.1.2 in 
  let wHat := r.2 in

  let t3 := EPC h hs w' w3 in 
  let t4 := V2G_mult (V2G_Tprod (ciphExp e' w')) (Enc g pk w4 Gone) in
  let tHat1 := PC h (m1 hs) (r1 w') (r1 wHat) in
  let tHat2 := PC h (m1 cHat) (r2 w') (r2 wHat) in

  (s, (t3, t4, Build_V2G tHat1 tHat2)).

Definition u'_V0 (ggtoxgtor: (G*G*G*V2G*(V2G*V2G))*(G*V2G*V2G)*(G*V2G*V2G)) 
    (c: F): ((G*G*G*V2G*(V2G*V2G))*(G*V2G*V2G)*(G*V2G*V2G)*F)
  := (ggtoxgtor, c).

Definition u'_P1 (ggtoxgtorc: (G*G*G*V2G*(V2G*V2G))*(G*V2G*V2G)*(G*V2G*V2G)*F) 
    (r w: V2F*F*F*V2F) : (G*G*G*V2G*(V2G*V2G))*(G*V2G*V2G)*(G*V2G*V2G)*F*(V2F*F*F*V2F) :=
  let c    :=  snd (ggtoxgtorc) in

  let u' := w.1.1.1 in
  let rTil := w.1.1.2 in
  let rStar := w.1.2 in
  let rHat := w.2 in

  let w' := r.1.1.1 in 
  let w3 := r.1.1.2 in
  let w4 := r.1.2 in 
  let wHat := r.2 in

  let s3  := w3+rTil*c in
  let s4  := w4+rStar*c in
  let sHat := V2F_add wHat (V2F_scale rHat c) in
  let s' := V2F_add w' (V2F_scale u' c) in
  
  (ggtoxgtorc, (s', s3, s4, sHat)).

Definition u'_V1 (transcript :  
  (G*G*G*V2G*(V2G*V2G))*(G*V2G*V2G)*(G*V2G*V2G)*F*(V2F*F*F*V2F)) :=
  
  let s := transcript.1.1.1 in
  let c := transcript.1.1.2 in
  let e := transcript.1.2 in
  let t := transcript.2 in

  let parm := s.1 in
  let g := parm.1.1.1.1 in
  let pk := parm.1.1.1.2 in
  let h := parm.1.1.2 in
  let hs := parm.1.2 in
  let e' := parm.2 in

  let stat := s.2 in
  let a := stat.1.1 in
  let b := stat.1.2 in
  let cHat := stat.2 in

  let t3 := c.1.1 in
  let t4 := c.1.2 in
  let tHat :=  c.2 in

  let s3  := t.1.1.2 in 
  let s4  := t.1.2 in 
  let sHat := t.2 in 
  let s' := t.1.1.1 in

  Gbool_eq (t3 o a^e) (EPC h hs s' s3) && 
  V2G_eq (V2G_mult t4 (V2G_Sexp b e)) 
    (V2G_mult (V2G_Tprod (ciphExp e' s')) (Enc g pk s4 Gone)) &&
  Gbool_eq (m1 (V2G_mult tHat (V2G_Sexp cHat e))) (PC h (m1 hs) (r1 s') (r1 sHat)) && 
  Gbool_eq (m2 (V2G_mult tHat (V2G_Sexp cHat e))) (PC h (m1 cHat) (r2 s') (r2 sHat)).

Definition u'_simulator_mapper (s : (G*G*G*V2G*(V2G*V2G))*(G*V2G*V2G))
  (r  :  V2F*F*F*V2F)(c :F)(w : V2F*F*F*V2F):=

  let u' := w.1.1.1 in
  let rTil := w.1.1.2 in
  let rStar := w.1.2 in
  let rHat := w.2 in

  let w' := r.1.1.1 in 
  let w3 := r.1.1.2 in
  let w4 := r.1.2 in 
  let wHat := r.2 in

  let s3  := w3+rTil*c in
  let s4  := w4+rStar*c in
  let sHat := V2F_add wHat (V2F_scale rHat c) in
  let s' := V2F_add w' (V2F_scale u' c) in
  
  (s', s3, s4, sHat).

Definition u'_simulator (s :(G*G*G*V2G*(V2G*V2G))*(G*V2G*V2G))(z :  V2F*F*F*V2F)(e : F) :
  ((G*G*G*V2G*(V2G*V2G))*(G*V2G*V2G)*(G*V2G*V2G)*F*(V2F*F*F*V2F)) :=
  let parm := s.1 in
  let g := parm.1.1.1.1 in
  let pk := parm.1.1.1.2 in
  let h := parm.1.1.2 in
  let hs := parm.1.2 in
  let e' := parm.2 in

  let stat := s.2 in
  let a := stat.1.1 in
  let b := stat.1.2 in
  let cHat := stat.2 in

  let s3  := z.1.1.2 in 
  let s4  := z.1.2 in 
  let sHat := z.2 in 
  let s' := z.1.1.1 in

  let t3 := EPC h hs s' s3 o \ a^e in 
  let t4 := V2G_mult (V2G_mult (V2G_Tprod (ciphExp e' s')) (Enc g pk s4 Gone)) 
    (V2G_inv (V2G_Sexp b e)) in
  let tHat1 := PC h (m1 hs) (r1 s') (r1 sHat) o \ m1 (V2G_Sexp cHat e) in
  let tHat2 := PC h (m1 cHat) (r2 s') (r2 sHat) o \ m2 (V2G_Sexp cHat e) in

  (s, (t3, t4, Build_V2G tHat1 tHat2), e, z).

Definition u'_extractor (s1 s2 :V2F*F*F*V2F)(c1 c2 : F) :=
  
  let s3_1  := s1.1.1.2 in 
  let s4_1  := s1.1.2 in 
  let sHat_1 := s1.2 in 
  let s'_1 := s1.1.1.1 in

  let s3_2  := s2.1.1.2 in 
  let s4_2  := s2.1.2 in 
  let sHat_2 := s2.2 in 
  let s'_2 := s2.1.1.1 in

 (V2F_scale (V2F_add s'_1 (V2F_neg s'_2)) (FmulInv (c1 - c2)),
  (s3_1 - s3_2) / (c1 - c2),(s4_1- s4_2) / (c1 - c2),
  V2F_scale (V2F_add sHat_1 (V2F_neg sHat_2)) (FmulInv (c1 - c2))).

Definition u'Form : Sigma.form F := Sigma.mkForm F
  ((G*G*G*V2G*(V2G*V2G))*(G*V2G*V2G)) (V2F*F*F*V2F) u'_Rel 
  (G*V2G*V2G) (V2F*F*F*V2F) Fadd Fzero Finv Fbool_eq 
  disjoint (V2F*F*F*V2F) u'_P0 u'_V0 u'_P1
  u'_V1 u'_simulator u'_simulator_mapper u'_extractor.

Theorem u'Sigma
  :CompSigmaProtocol F u'Form. 
Proof.
  pose HeliosIACR2018.  unfold u'Form in *. simpl in *.
  assert (AbeGroup F Fadd 0 Fbool_eq Finv).  apply (field_additive_abegrp (F)(Fadd)(Fzero)
  (Fbool_eq) (Fsub)(Finv)(Fmul) (Fone)(FmulInv)(Fdiv)). apply v. apply v. apply v.
  destruct v. destruct vs_field. destruct F_R.   
   constructor. constructor. constructor. cbn in *. apply H.
  + intros. trivial.
(* Comp and prev prop *)
  + intros. trivial.
  + intros. trivial.
  + intros. trivial.
  + intros. trivial.
  + intros. trivial. 
  + intros. trivial.
  + intros. simpl. trivial.

  (* correctness *)
  + intros. simpl in *. unfold u'_P0. unfold u'_V0. unfold u'_Rel in H0. unfold u'_P1.
  unfold u'_V1. simpl in *. apply andb_true_iff in H0. destruct H0.
  apply andb_true_iff in H0. destruct H0. apply andb_true_iff in H0. destruct H0.
  apply andb_true_iff. split. apply andb_true_iff. split. apply andb_true_iff. split.
  apply bool_eq_corr. apply bool_eq_corr in H0. rewrite H0. rewrite <- EPCMult.
  rewrite <- EPCExp. intuition. 
  (* part 2 *)  
  apply V2Geq in H3. apply V2Geq.
  rewrite H3. rewrite V2G_Sexp_dis_dot. rewrite EncOfOneRasiedToB.
  replace (Gone) with (Gone o Gone). rewrite <- EncIsHomomorphic.
  replace (Gone o Gone) with Gone. do 2 rewrite <- V2G_Assoc.
  apply V2G_right_cancel. rewrite V2G_Comm. rewrite <- V2G_Assoc.
  apply V2G_right_cancel. rewrite Sexp_dist. rewrite V2G_Comm. 
  rewrite V2G_mult_Tprod_ciphExp. intuition. rewrite one_right. trivial.
   rewrite one_right. trivial.
  (* part 3 *)
  apply bool_eq_corr. apply bool_eq_corr in H2. rewrite H2. rewrite <- PCMult.
  rewrite <- PCExp. intuition. 
  (* part 4 *)
  apply bool_eq_corr. apply bool_eq_corr in H2. apply bool_eq_corr in H1.
  rewrite H1. rewrite <- PCMult. rewrite <- PCExp.
   apply right_cancel. rewrite H2. intuition.

  (* Special soundness *)
  + intros. simpl in *. unfold u'_Rel. unfold u'_extractor. simpl.
  unfold u'_V1 in *. apply andb_true_iff in H1. destruct H1.
  apply andb_true_iff in H1. destruct H1. apply andb_true_iff in H1. 
  destruct H1. apply andb_true_iff in H2. destruct H2. simpl in *.
  apply andb_true_iff in H2. destruct H2. apply andb_true_iff in H2. 
  destruct H2. apply bool_eq_corr in H1. apply bool_eq_corr in H6.
  apply bool_eq_corr in H7. apply bool_eq_corr in H2. 
  apply bool_eq_corr in H3. apply bool_eq_corr in H4. 
  apply V2Geq in H8. apply V2Geq in H5. unfold disjoint in H0. 
  apply negb_false_iff in H0. rewrite negb_involutive in H0.
  apply F_bool_neq_corr in H0. apply andb_true_iff. split.
   apply andb_true_iff. split. apply andb_true_iff. split. 
  (* part 1 *)
  apply bool_eq_corr. rewrite EPCExp. rewrite <- EPCMult. 
  rewrite <- EPCneg. rewrite <- H1. rewrite <- H2. apply ExtractorHelper.
  unfold not in *. intros.  pose HeliosIACR2018. apply shift in H9.
  rewrite H9 in H0. apply H0. trivial. 
  (* part 2 *) 
  apply V2Geq. rewrite <- Sexp_dist. rewrite <- V2G_mult_Tprod_ciphExp.
  rewrite <- EncOfOneRasiedToB. rewrite <- V2G_Sexp_dis_dot. 
  assert (Gone = (Gone o Gone)). rewrite one_right. intuition.
  rewrite H9. rewrite <- EncIsHomomorphic. rewrite V2G_commHack.
  rewrite <- H5. rewrite ciphExp_neg. rewrite EncInv. 
  remember (V2G_Tprod (ciphExp s.1.2 t2.1.1.1)) as a. 
  remember (Enc s.1.1.1.1.1 s.1.1.1.1.2 t2.1.2 Gone) as b.
  rewrite V2G_inv_dist. rewrite <- H8. rewrite V2G_inv_dist2.
  rewrite V2G_commHack. rewrite V2G_InvCorr. rewrite V2G_Comm.
  rewrite V2G_One. rewrite V2G_Sexp_inv. rewrite <- V2G_Sexp_dis_add.
   rewrite <- V2G_Sexp_dis_mul. replace ((e1 - e2) / (e1 - e2)) with 1.
  rewrite V2G_Sexp_id. trivial. field; auto. unfold not in *. intros. 
  pose HeliosIACR2018. apply shift in H10. rewrite H10 in H0. apply H0.
   trivial. 
  (* part 3 *)
  apply bool_eq_corr. rewrite <- PCExp. rewrite <- PCMult. 
  rewrite <- PCneg. rewrite <- H4. rewrite <- H7. apply ExtractorHelper.
  unfold not in *. intros.  pose HeliosIACR2018. apply shift in H9.
  rewrite H9 in H0. apply H0. trivial. 
  (* part 4 *)
  apply bool_eq_corr. rewrite <- PCExp. rewrite <- PCMult. 
  rewrite <- PCneg. rewrite <- H6. rewrite <- H3. apply ExtractorHelper.
  unfold not in *. intros.  pose HeliosIACR2018. apply shift in H9.
  rewrite H9 in H0. apply H0. trivial.

  (* honest verifier ZK *)
  + intros. simpl in *. split. unfold u'_simulator_mapper. 
  unfold u'_simulator. unfold u'_P0. unfold u'_V0. unfold u'_P1.
  simpl in *. unfold u'_Rel in H0. apply andb_true_iff in H0.
  destruct H0. apply andb_true_iff in H0. destruct H0. 
  apply andb_true_iff in H0. destruct H0. apply bool_eq_corr in H0. 
  apply bool_eq_corr in H1. apply bool_eq_corr in H2. apply V2Geq in H3.
  simpl in *. rewrite H0. apply injective_projections. simpl.
  apply injective_projections. simpl. apply injective_projections. simpl.
  trivial. simpl. apply injective_projections. simpl.
  (* part 1.1 *)
  apply injective_projections. simpl. rewrite <- EPCExp.
  rewrite EPCneg. rewrite EPCMult. replace (r.1.1.2 + w.1.1.2 * 
  e - w.1.1.2 * e) with r.1.1.2. rewrite V2F_add_neg. intuition.
  (* part 1.2 *)
  field; auto. simpl. rewrite H3. rewrite V2G_Sexp_inv.
  rewrite V2G_Sexp_dis_dot. rewrite V2G_commHack. apply V2G_Mul.
  split. rewrite Sexp_dist. rewrite V2G_mult_Tprod_ciphExp.
  rewrite V2F_scale_neg. rewrite V2F_add_neg. intuition.
  rewrite EncOfOneRasiedToB. rewrite EncIsHomomorphic.
  rewrite one_right. replace (r.1.2 + w.1.2 * e + w.1.2 * - e) with r.1.2.
  intuition. field; auto.
  (* part 1.3 *)
  simpl. rewrite H2. rewrite H1. apply V2G_eqBreakDown. simpl. split.
  rewrite PCExp. rewrite PCneg. rewrite PCMult. 
  replace (r1 r.1.1.1 + r1 w.1.1.1 * e - r1 w.1.1.1 * e) with (r1 r.1.1.1).
  replace (r1 r.2 + r1 w.2 * e - r1 w.2 * e) with (r1 r.2). intuition.
  field; auto. field; auto. remember ((PC s.1.1.1.2 (m1 s.1.1.2) (r1 w.1.1.1) (r1 w.2))) as b.
  rewrite PCExp. rewrite PCneg. rewrite H2. rewrite PCMult.
  replace (r2 r.1.1.1 + r2 w.1.1.1 * e - r2 w.1.1.1 * e) with (r2 r.1.1.1).
  replace (r2 r.2 + r2 w.2 * e - r2 w.2 * e) with (r2 r.2).
  intuition. field; auto. field; auto.
  (* part 1.4 *)
  simpl. trivial. simpl. trivial.
  (* part 2 *)
  intros. exists (V2F_add t.1.1.1 (V2F_neg (V2F_scale w.1.1.1 e)),
   t.1.1.2 - w.1.1.2*e,  t.1.2 - w.1.2*e, 
   V2F_add t.2 (V2F_neg (V2F_scale w.2 e))). 
  unfold u'_simulator_mapper. apply injective_projections. simpl.
  apply injective_projections. simpl. apply injective_projections. simpl.
  rewrite V2F_add_neg2. intuition. simpl. field; auto. simpl. field; auto.
  simpl. rewrite V2F_add_neg2. intuition.
  
  + intros. simpl in *. unfold u'_V1. unfold u'_simulator. simpl.
    apply andb_true_iff. split. apply andb_true_iff. split. 
    apply andb_true_iff. split.  
    (* part 1 *)
    rewrite bool_eq_corr. rewrite <- dot_assoc. rewrite <- inv_left.
    rewrite one_right. trivial.
    (* part 2 *)
    apply V2Geq. rewrite V2G_Assoc. rewrite V2G_InvCorr2.
    rewrite V2G_One. trivial.
    (* part 3 *)
    rewrite bool_eq_corr. rewrite <- dot_assoc. rewrite <- inv_left.
    rewrite one_right. trivial.
    (* part 4 *)  
    rewrite bool_eq_corr. rewrite <- dot_assoc. rewrite <- inv_left.
    rewrite one_right. trivial.

  + intros. unfold u'_P1. trivial.
  
  + intros. trivial.
Qed.
  

