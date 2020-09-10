Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import groups.
Require Import sigmaprotocol.
Require Import Coq.Lists.List.
Require Import Ring.
Require Import Field. 
Require Import Field_theory.
Require Import HeliosIACR2018.
Require Import cryptoprim.
Require Import matrices.
Require Import basicSigmas.
From Groups Require Import groups module vectorspace dualvectorspaces modulevectorspace.

Set implicit arguments.

Import HeliosIACR2018VS.
Import HeliosIACR2018G.
Module BS := BasicSigmas HeliosIACR2018G HeliosIACR2018F HeliosIACR2018VS.
Import BS. 
Module DG := DualGroupIns HeliosIACR2018G.
Module DVS := DualVectorSpaceIns HeliosIACR2018G DG HeliosIACR2018F HeliosIACR2018VS.
Module MVS := VectorSpaceModuleSameGroupInsIns DG HeliosIACR2018F DVS.
Module ES := BasicElGamal HeliosIACR2018G HeliosIACR2018F HeliosIACR2018VS 
    DG DVS MVS.
Module ALES := EncryptionSchemeProp HeliosIACR2018G DG HeliosIACR2018F HeliosIACR2018F 
    DVS MVS ES.
Import ALES.

(*Begining main compiles *)

(* This is the sigma protocol for correct decryption *)
Definition DHTForm : Sigma.form F
  := eqSigmaProtocol dLogForm.

Theorem DHTSigma : 
  CompSigmaProtocol DHTForm.
Proof.
  apply eqCorr. unfold DHTForm. 
  apply dLogSigma.
Qed.

(** The proof of (Diffie Hellmen tuple discjunction) (DHTD) can be 
    used to prove that one of two ElGamal ciphertext is 
    an encryption of zero and hence that a given ciphertext
     contains one of two messages *)

Definition DHTDisForm : Sigma.form F
  := disSigmaProtocol DHTForm.

Theorem DHTDisSigma : 
  SigmaProtocol DHTDisForm.
Proof.
  unfold DHTDisForm. apply disCorr.
  apply DHTSigma. 
  (* We also need to prove that the extra requirments are met *)
  unfold DHTForm.
  unfold eqSigmaProtocol. simpl. unfold disjoint. intros. 
  refine (conj _ _). intros. apply negb_false_iff in H. rewrite negb_involutive in H.
  apply H. intros. apply negb_false_iff. rewrite negb_involutive. apply H.
Qed.

(** The sigma protocols are too general and we need 
    to restrict it *)

(** Maps a generator g, public key h, and ciphertext (gtox,htox)
 into the statement for the sigma protocol *)
Definition oneOrZero (s : (Sigma.S DHTForm)) : Sigma.S DHTDisForm := 
  let g     := s.1.1 in
  let h     := s.1.2 in 
  let gtox  := s.2.1 in 
  let htox  := s.2.2 in 
  (((g, gtox),(h, htox)), ((g, gtox), (h, (htox o - g)))).

(** Maps a generator g, public key h, and ciphertext c
 into the statement for the sigma protocol  *)
Definition oneOrZeroCipher(pk : ES.PK)(c : DG.G) : Sigma.S DHTDisForm  :=
  oneOrZero(pk,c).

(** Maps a generator g, public key h, ciphertext c, decryption factor d *)
Definition decFactorStatment(pk : ES.PK)(c : DG.G)(d : G) : Sigma.S DHTForm :=
  (pk,(c.1,d)).

(* The definition of encryption correctness for 1 of n*)  
Definition HeliosCorrectEncr  (pk :ES.PK)(prodCiph : DG.G)(cs : list DG.G): Prop := 
    let zero := Gone in
    let one := pk.1 in
    decryptsToOneOrZero pk pk.1 (prodCiph) /\
    Forall (decryptsToOneOrZero pk pk.1) cs.

(* The definition of encryption correctness for n of n*)  
Definition HeliosCorrectEncrApproval  (pk :ES.PK)(cs : list DG.G): Prop := 
    let zero := Gone in
    let one := pk.1 in
    Forall (decryptsToOneOrZero pk pk.1) cs.
(**
  **
**)

Fixpoint recChalType (c : list (G*G)) : Set :=
  match c with
    | nil => F
    | a :: b => ((recChalType b)*F)
  end.

(* The 1 of n sigma protocol, produced from a list of length n *)
Fixpoint OneOfNSigma (c : list (G*G)) : Sigma.form (recChalType c) :=
  match c with
    | nil => DHTDisForm
    | a :: b => parSigmaProtocol (OneOfNSigma b) DHTDisForm
  end.

(* The OneOfNSigma is a sigma protocol *)
Theorem OneOfNSigmaCorrect :
  forall (c : list (G*G)),
  SigmaProtocol (OneOfNSigma c).
Proof.
  intros. unfold OneOfNSigma. induction c. apply DHTDisSigma.
  apply parCorr. apply IHc. apply DHTDisSigma.
Qed.

(* The n of n sigma protocol, produced from a list of length n *)
Fixpoint ApprovalSigma (c : list (G*G)) : Sigma.form (recChalType c) :=
  match c with
    | nil => emptyForm
    | a :: b => parSigmaProtocol (ApprovalSigma b) DHTDisForm
  end.

(* The ApprovalSigma is a sigma protocol *)
Theorem ApprovalSigmaCorrect :
  forall (c : list (G*G)),
  SigmaProtocol (ApprovalSigma c).
Proof.
  intros. unfold ApprovalSigma. induction c. apply emptySigma.
  apply parCorr. apply IHc. apply DHTDisSigma.
Qed.

(* The decryption sigma *)
Definition DecryptionSigma :=
  parSigmaProtocol (parSigmaProtocol(parSigmaProtocol 
    DHTForm DHTForm) DHTForm) DHTForm.

(* The DecryptionSigma is correct *)
Theorem DecryptionSigmaCorrect :
  SigmaProtocol DecryptionSigma.
Proof.
  intros. unfold DecryptionSigma. apply parCorr. apply parCorr. apply parCorr. 
  apply DHTSigma. apply DHTSigma. apply DHTSigma.  apply DHTSigma. 
Qed.

(* Generates the OneOfN statement from ciphertexts *)
Fixpoint OneOfNStatment (pk : ES.PK)(cProd : DG.G)(c : list (DG.G)) : Sigma.S (OneOfNSigma c):=
 match c with
  | nil  => (oneOrZeroCipher pk cProd)
  | a :: b => (OneOfNStatment pk cProd b, (oneOrZeroCipher pk a))
 end.

(* Generates the Approval statement from ciphertexts *)
Fixpoint ApprovalSigmaStatment (pk : ES.PK)(c : list (DG.G)) : Sigma.S (ApprovalSigma c):=
 match c with
  | nil  => (pk.1)
  | a :: b => (ApprovalSigmaStatment pk b, (oneOrZeroCipher pk a))
 end.

(* Generates the decryption statement from generator g, ciphertext c,
  authority public keys y, and decryption factors d *)
Definition DecryptionSigmaStatment (c : G*G)
  (y :(ES.PK*ES.PK*ES.PK*ES.PK)) (d :(G*G*G*G)): Sigma.S DecryptionSigma :=

  ((decFactorStatment y.1.1.1 c d.1.1.1),(decFactorStatment y.1.1.2 c d.1.1.2),
    (decFactorStatment y.1.2 c d.1.2),(decFactorStatment y.2 c d.2)).

(* Proposition that correct encryption for a list of ciphertexts follows from the 
  special soundness of the sigma protocol verifier *)
Definition HeliosCorrectEncrApprovalList  (pk : ES.PK)
      (cs : list (list DG.G)): Prop := 
 forall x : list(G*G),
  In x cs -> (*Technical our proof generates a new sigma protocol for each voter *)

  let Sig := ApprovalSigma x in
  let s := (ApprovalSigmaStatment pk x) in

  forall (c : Sigma.C Sig)(e1 e2 : (recChalType x))
    (t1 t2 : Sigma.T Sig),
  Sigma.V1 Sig (s,c,e1,t1) ->
  Sigma.V1 Sig (s,c,e2,t2) ->
  Sigma.disjoint Sig e1 e2 ->
  HeliosCorrectEncrApproval pk x.

(* Given a pair containing a ciphertext and message, as well generator g
  and public key h.  The ciphertext decrypts to the message  *)
Definition decryptionConsistent (pk : ES.PK)(pair: DG.G*G) :=
  decryptsTo2 pk pair.1 pair.2.

(* Given a generator g, public key h, authority public keys y,
  list of decryption factors df, and a list of decryption tuples dt
  assert that if the relation between df and dt is basicly consitstent see below
  then the acceptence of the verify implies the claimed decryption is correct *)
Definition HeliosCorrectDecrList (y: (ES.PK*ES.PK*ES.PK*ES.PK))
  (df : list(G*G*G*G))
  (dt : list ((DG.G)*ES.M)) : Prop :=
  
  let d := combine dt df in 

    let pk := (y.1.1.1.1,
                y.1.1.1.2 o y.1.1.2.2 o y.1.2.2 o y.2.2) in

  forall x : ((G*G)*G*(G*G*G*G)),
  In x d -> (*For all values to check the decrytion of *)

   (*Basic consistence, the sum of decryption factors is equal to second element 
    of the ciphertext divided by the claimed message *)
  x.2.1.1.1 o x.2.1.1.2 o x.2.1.2 o x.2.2 = x.1.1.2 o - x.1.2 ->

  let Sig := DecryptionSigma in
  let s := DecryptionSigmaStatment x.1.1 y x.2 in

  forall (c : Sigma.C Sig)(e1 e2 : (F*F*F*F))(t1 t2 : Sigma.T Sig),
  Sigma.V1 Sig (s,c,e1,t1) ->
  Sigma.V1 Sig (s,c,e2,t2) ->
  Sigma.disjoint Sig e1 e2 ->
  decryptionConsistent pk x.1.

(* Basic lemma about how OneOfNStatment behaves under induction *)
Definition OneOfNStatmentLeft (pk : ES.PK)(prodCiph a : (G*G))(l : list(G*G)) : 
  let s := OneOfNStatment pk prodCiph (a :: l) in
   s.1 = (OneOfNStatment pk prodCiph l).
Proof.
  intros. trivial. 
Qed.

(* This theorem says that if the adversary can answer for more than one challenge
then the product ciphertexts is an encryption of zero or one. The step of reasoning that getting
the right challenge occurs with negliable probability in the random oracle model
is not modelled *) 
Lemma OneOfNCorrectProd :
  forall (pk : ES.PK)(cs : list (G*G))(prodCiph : (G*G)),
  let zero := Gone in
  let one := pk.1 in
  let Sig := OneOfNSigma cs in
  let s := (OneOfNStatment pk prodCiph cs) in

  forall (c : Sigma.C Sig)(e1 e2 : (recChalType cs))
    (t1 t2 : Sigma.T Sig),
  Sigma.V1 Sig (s,c,e1,t1) ->
  Sigma.V1 Sig (s,c,e2,t2) ->
  Sigma.disjoint Sig e1 e2 ->
  (exists r : F, (pk.1 ^ r, pk.2 ^ r o Gone) = prodCiph) \/
  (exists r : F, (pk.1 ^ r, pk.2 ^ r o pk.1) = prodCiph).
Proof.
  pose module_abegrp.
  + intros. assert (Sigma.Rel Sig s (Sigma.extractor Sig t1 t2 e1 e2)).
  eapply special_soundness with (c:=c). apply OneOfNSigmaCorrect. apply H1. apply H. apply H0.
  induction (cs).  
  (*Base case (decryption of product equal to 1 or 0) *)
  remember (Sigma.extractor Sig t1 t2 e1 e2) as w.
  case_eq (Gbool_eq (prodCiph).1 (pk.1 ^ w) && Gbool_eq ((prodCiph).2) (pk.2 ^ w)).
  intros. apply andb_true_iff in H3. destruct H3. left. exists w. 
  apply bool_eq_corr in H3. rewrite <- H3.
  apply bool_eq_corr in H4. rewrite <- H4. rewrite one_right.
  symmetry. apply surjective_pairing.  (* or 1 *)
  intros. right. unfold Sig in H2. simpl in H2. exists w. unfold HardProb.dLog in H2. rewrite H3 in H2. simpl in H2.
  apply andb_true_iff in H2. destruct H2. apply bool_eq_corr in H2.
  rewrite <- H2.  apply bool_eq_corr in H4. rewrite <- H4. rewrite <- dot_assoc.
  rewrite <- inv_left. rewrite one_right. symmetry. apply surjective_pairing. 
  (*Inductive case for (decryption of product equal to 1 or 0) *)
  apply (IHl c.1 e1.1 e2.1 t1.1 t2.1). apply ParVerLeft in H. apply H. 
  apply OneOfNSigmaCorrect. apply DHTDisSigma. apply ParVerLeft in H0. apply H0. 
  apply OneOfNSigmaCorrect.  apply DHTDisSigma. apply ParDisLeft in H1.
  apply H1. apply OneOfNSigmaCorrect. apply DHTDisSigma.
  apply ParExtLeft in H2. apply H2. apply OneOfNSigmaCorrect. apply DHTDisSigma.
  trivial.
Qed.

(* This theorem says that if the adversary can answer for more than one challenge
then all ciphertexts are an encryption of zero or one. The step of reasoning that getting
the right challenge occurs with negliable probability in the random oracle model
is not modelled *) 
Lemma OneOfNAllDecryptToOneOrZero :
  forall (pk : ES.PK)(cs : list (G*G))(prodCiph : (G*G)),
  let zero := Gone in
  let one := pk.1 in
  let Sig := OneOfNSigma cs in
  let s := (OneOfNStatment pk prodCiph cs) in

  forall (c : Sigma.C Sig)(e1 e2 : (recChalType cs))(t1 t2 : Sigma.T Sig),
  Sigma.V1 Sig (s,c,e1,t1) ->
  Sigma.V1 Sig (s,c,e2,t2) ->
  Sigma.disjoint Sig e1 e2 ->
  Forall (decryptsToOneOrZero pk one) cs.
Proof.
  pose module_abegrp.
  intros. (*Begining part two*)
  assert (Sigma.Rel Sig s (Sigma.extractor Sig t1 t2 e1 e2)).
  eapply special_soundness with (c:=c). apply OneOfNSigmaCorrect. apply H1. apply H. apply H0.
  unfold decryptsToOneOrZero. unfold decryptsTo. unfold ES.enc in *.
  (*Base case for second part of thorem*)
  induction cs.  exact. 
  (*Inductive case *)
  remember (Sigma.extractor Sig t1 t2 e1 e2) as w. apply Forall_cons.
  case_eq (Gbool_eq (a0).1 (pk.1 ^ w.2) && Gbool_eq ((a0).2) (pk.2 ^ w.2)).
  intros. apply andb_true_iff in H3. destruct H3. left. exists w.2. 
  apply bool_eq_corr in H3. rewrite <- H3.
  apply bool_eq_corr in H4. rewrite <- H4. rewrite one_right. 
  symmetry. apply surjective_pairing. (*Or one *) 
  intros. right. unfold Sig in H2. simpl in H2. exists w.2. unfold HardProb.dLog in H3.
   rewrite H3 in H2. simpl in H2.
  apply andb_true_iff in H2. destruct H2. 
  apply andb_true_iff in H4. destruct H4. unfold HardProb.dLog in H4. unfold HardProb.dLog in H5.
  apply bool_eq_corr in H4. rewrite (surjective_pairing a0).
  simpl in H4. rewrite H4. apply bool_eq_corr in H5. simpl in H5.
   symmetry in H5. apply b_equal in H5.
   rewrite <- H5. unfold Ginv. replace (- - pk.1) with pk.1 by apply dob_neg. trivial. 
    (*Inductive case for (decryption of product equal to 1 or 0) *)
  apply (IHcs c.1 e1.1 e2.1 t1.1 t2.1).  apply ParVerLeft in H. apply H.
   apply OneOfNSigmaCorrect. apply DHTDisSigma.  apply ParVerLeft in H0. apply H0.
   apply OneOfNSigmaCorrect. apply DHTDisSigma. apply ParDisLeft in H1.
  apply H1. apply OneOfNSigmaCorrect. apply DHTDisSigma. rewrite Heqw in H2.
  apply ParExtLeft in H2. apply H2. apply OneOfNSigmaCorrect. apply DHTDisSigma.
  trivial.
Qed.

(* Given a list of ciphertexts produce the product *)
Definition Prod (cs : list (G*G)) : (G*G) :=
  let zero := Gone in
  fold_left DG.Gdot cs (zero,zero). 
  
(* We now use two precious lemmas to show that the sigma accepting implies that 
   each ciphertext is the encryption of zero or one and that the product is the 
  encryption of zero or one. *)
Theorem HeliosCorrextEncrImpliedBySigma :
  forall (pk :ES.PK)(cs : list (G*G)),
  let zero := Gone in
  let one := pk.1 in
  let Sig := OneOfNSigma cs in
  let s := (OneOfNStatment pk (Prod cs)  cs) in

  forall (c : Sigma.C Sig)(e1 e2 : recChalType cs)
    (t1 t2 : Sigma.T Sig),
  Sigma.V1 Sig (s,c,e1,t1) ->
  Sigma.V1 Sig (s,c,e2,t2) ->
  Sigma.disjoint Sig  e1 e2 ->
   HeliosCorrectEncr pk (Prod cs) cs.
  (* Proof of honest key generation *)
  (* Proof of correct decryption *)
Proof.
  intros. unfold HeliosCorrectEncr. split.  
   apply (OneOfNCorrectProd pk cs (Prod cs) c e1 e2 t1 t2).
  apply H. apply H0. apply H1.

  (*Begining part two*)
  apply (OneOfNAllDecryptToOneOrZero pk cs (Prod cs) c e1 e2 t1 t2).
  apply H. apply H0. apply H1. 
Qed.

(* We now show that the accepentence of ApprovalSigma implies that all 
  ciphertexts are the encryption of zero or one *)
Theorem HeliosCorrectEncrApprovalImpliedBySigma :
  forall (pk : ES.PK)(cs : list (G*G)),
  let zero := Gone in
  let one := pk.1 in
  let Sig := ApprovalSigma cs in
  let s := (ApprovalSigmaStatment pk cs) in

  forall (c : Sigma.C Sig)(e1 e2 : (recChalType cs))
    (t1 t2 : Sigma.T Sig),
  Sigma.V1 Sig (s,c,e1,t1) ->
  Sigma.V1 Sig (s,c,e2,t2) ->
  Sigma.disjoint Sig e1 e2 ->
  HeliosCorrectEncrApproval pk cs.
Proof.
  pose module_abegrp.
  intros. unfold HeliosCorrectEncrApproval.
  intros. (*Begining part two*)
  assert (Sigma.Rel Sig s (Sigma.extractor Sig t1 t2 e1 e2)).
  eapply special_soundness with (c:=c). apply ApprovalSigmaCorrect. apply H1. apply H. apply H0.
  unfold decryptsToOneOrZero. unfold decryptsTo. unfold ES.enc in *.
  (*Base case for second part of thorem*)
  induction cs.  exact. 
  (*Inductive case *)
  remember (Sigma.extractor Sig t1 t2 e1 e2) as w. apply Forall_cons.
  case_eq (Gbool_eq (a0).1 (pk.1 ^ w.2) && Gbool_eq ((a0).2) (pk.2 ^ w.2)).
  intros. apply andb_true_iff in H3. destruct H3. left. exists w.2. 
  apply bool_eq_corr in H3. rewrite <- H3.
  apply bool_eq_corr in H4. rewrite <- H4. rewrite one_right.
  symmetry. apply surjective_pairing. (*Or one *) 
  intros. right. unfold Sig in H2. simpl in H2. exists w.2. 
  unfold HardProb.dLog in H3. rewrite H3 in H2. simpl in H2.
  apply andb_true_iff in H2. destruct H2. 
  apply andb_true_iff in H4. destruct H4. unfold HardProb.dLog in H4. 
  unfold HardProb.dLog in H5.
  apply bool_eq_corr in H4. rewrite (surjective_pairing a0).
  simpl in H4. rewrite H4. apply bool_eq_corr in H5. simpl in H5.
   symmetry in H5. apply b_equal in H5.
   rewrite <- H5. unfold Ginv. replace (- - pk.1) with pk.1 by apply dob_neg. trivial.
    (*Inductive case for (decryption of product equal to 1 or 0) *)
  apply (IHcs c.1 e1.1 e2.1 t1.1 t2.1).  apply ParVerLeft in H. apply H.
   apply ApprovalSigmaCorrect. apply DHTDisSigma.  apply ParVerLeft in H0. apply H0.
   apply ApprovalSigmaCorrect. apply DHTDisSigma. apply ParDisLeft in H1.
  apply H1. apply ApprovalSigmaCorrect. apply DHTDisSigma. rewrite Heqw in H2.
  apply ParExtLeft in H2. apply H2. apply ApprovalSigmaCorrect. apply DHTDisSigma.
  trivial.
Qed.

Definition lenEqualToN (n : nat)(l : list (G*G)) :=    (*These functions are surely unnecessary *)
  n = length l.

Definition lenEqualToN2 (n : nat)(l : list (G)) := 
  n = length l.

Definition mapToGroup (g : G)(m : F) :=
  g^m.


Theorem HeliosCorrectDecrListImplied :
  (*Group generator, public key, authority sub keys, list of ciphertexts, messages,
  and claimed decryption factors for the messages *)
  forall (y: (ES.PK*ES.PK*ES.PK*ES.PK)),
  forall (df :list (G*G*G*G)),
  forall(dt : list ((G*G)*G)),
  let d := combine dt df in 

  let pk := (y.1.1.1.1,
                y.1.1.1.2 o y.1.1.2.2 o y.1.2.2 o y.2.2) in
  (* We require each key to be in relation to the same generator *)
   y.1.1.1.1 = y.1.1.2.1 ->
   y.1.1.1.1 = y.1.2.1 ->
   y.1.1.1.1 = y.2.1 ->


  forall x : ((G*G)*G*(G*G*G*G)),
  In x d -> (*For all values to check the decrytion of *)

  x.2.1.1.1 o x.2.1.1.2 o x.2.1.2 o x.2.2 = x.1.1.2 o - x.1.2 ->

  let Sig := DecryptionSigma in
  let s := DecryptionSigmaStatment x.1.1 y x.2 in

  forall (c : Sigma.C Sig)(e1 e2 : (F*F*F*F))
    (t1 t2 : Sigma.T Sig),
  Sigma.V1 Sig (s,c,e1,t1) ->
  Sigma.V1 Sig (s,c,e2,t2) ->
  Sigma.disjoint Sig e1 e2 ->
  decryptionConsistent pk x.1.
Proof.
  pose module_abegrp.  
  intros y df dt d pk g1 g2 g3 x key xd.
  intros. assert (Sigma.Rel Sig s (Sigma.extractor Sig t1 t2 e1 e2)).
  eapply special_soundness with (c:=c). apply DecryptionSigmaCorrect. apply H1. 
  apply H. apply H0. remember (Sigma.extractor Sig t1 t2 e1 e2) as w.
  unfold decryptionConsistent. unfold decryptsTo2.
  exists (w.1.1.1 + w.1.1.2 + w.1.2 + w.2). simpl in H2.
  unfold HardProb.dLog in H2.  apply andb_true_iff in H2. destruct H2.  
  apply andb_true_iff in H2. destruct H2. 
  apply andb_true_iff in H2. destruct H2.
  apply andb_true_iff in H2. destruct H2. 
  apply andb_true_iff in H4. destruct H4.
  apply andb_true_iff in H5. destruct H5. 
  apply andb_true_iff in H3. destruct H3.
  unfold d. unfold ES.keymatch.  simpl in *.  apply bool_eq_corr in H3.
  apply bool_eq_corr in H4. apply bool_eq_corr in H5.
  apply bool_eq_corr in H6. apply bool_eq_corr in H7.
  apply bool_eq_corr in H8. apply bool_eq_corr in H9.
  apply bool_eq_corr in H2. split. do 3 rewrite mod_dist_Fadd.
  rewrite <- H2. rewrite <- g1 in H5. rewrite <- g2 in H4. 
  rewrite <- g3 in H3.
  rewrite <- H3. rewrite <- H4.  rewrite <- H5. apply bool_eq_corr.
  intuition. unfold ES.dec. do 3 rewrite mod_dist_Fadd.
  symmetry in H6. rewrite H6. symmetry in H8. rewrite H8. 
  symmetry in H9. rewrite H9. symmetry in H7. rewrite H7.
  rewrite xd. pose inv_dist. symmetry in e. rewrite e. rewrite dot_assoc.
  pose (inv_right x.1.1.2). symmetry in e0. rewrite e0. rewrite one_left.
  rewrite <- dob_neg. trivial.
Qed.

Theorem HeliosCorrectResultApproval :
  (*The outer list contains each voter and inner list contains there ciphertext on each option *)
  forall numOpts numVoter : nat,
  forall (cs : list (list (G*G))),
  forall (y : (ES.PK*ES.PK*ES.PK*ES.PK)),(*Authoritity keys *)
  forall (df : list (G*G*G*G)),(* Decryption Factors, each authority each option *)
  forall (r : list F),(* Results *)

  let pk := (y.1.1.1.1,
                y.1.1.1.2 o y.1.1.2.2 o y.1.2.2 o y.2.2) in
  (* We require each key to be in relation to the same generator *)
   y.1.1.1.1 = y.1.1.2.1 ->
   y.1.1.1.1 = y.1.2.1 ->
   y.1.1.1.1 = y.2.1 ->


  length cs = numVoter -> (*Basic data length consistency *)
  Forall (lenEqualToN numOpts) cs ->
  length df = numOpts ->
  length r = numOpts ->
  
  let summation := map Prod cs in
  let resultInGroup := map (mapToGroup pk.1) r in
  let dt := combine summation resultInGroup in

  (*All ballots are correctly formed AND the annonced result is correct *)
  HeliosCorrectEncrApprovalList pk cs /\ 
    HeliosCorrectDecrList y df dt.
Proof.
  intros numOpts numVoter cs y df r pk g1 g2 g3 lenCiph1 lenCiph2
 lenD lenR summation resultInGroup dt. split.
  unfold HeliosCorrectEncrApprovalList. intros x inx. 
  apply (HeliosCorrectEncrApprovalImpliedBySigma).

  unfold HeliosCorrectDecrList. apply HeliosCorrectDecrListImplied; auto.
Qed.
 




