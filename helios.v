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
Require Import basicSigmas.


(** This section contains a number of standard sigma
 protocols compilied out of the dLog Sigma *)

(** we turn our attention to proving the sigma protocol
 for knowledge of discrete log *)

Infix "+" := Fadd.
Infix "*" := Fmul.
Notation "x / y" := (Fmul x (FmulInv y)). 
Notation "0" := Fzero.
Notation "1" := Fone.
Notation "- x" :=  (Finv x).
Notation "x - y" := (x + (- y)).

Infix "o" := Gdot (at level 50) .
Notation "- x" := (Ginv x).

Infix "^" := op.


(*Begining main compiles *)

(* This is the sigma protocol for correct decryption *)
Definition DHTForm : Sigma.form F
  := eqSigmaProtocol F dLogForm.

Theorem DHTSigma : 
  CompSigmaProtocol F DHTForm.
Proof.
  apply eqCorr. unfold DHTForm. 
  apply dLogSigma.
Qed.

(** The proof of (Diffie Hellmen tuple discjunction) (DHTD) can be 
    used to prove that one of two ElGamal ciphertext is 
    an encryption of zero and hence that a given ciphertext
     contains one of two messages *)

Definition DHTDisForm : Sigma.form F
  := disSigmaProtocol F DHTForm.

Theorem DHTDisSigma : 
  SigmaProtocol F DHTDisForm.
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
Definition oneOrZero (s : (Sigma.S F DHTForm)) : Sigma.S F DHTDisForm := 
  let g     := s.1.1 in
  let h     := s.1.2 in 
  let gtox  := s.2.1 in 
  let htox  := s.2.2 in 
  (((g, gtox),(h, htox)), ((g, gtox), (h, (htox o - g)))).

(** Maps a generator g, public key h, and ciphertext c
 into the statement for the sigma protocol  *)
Definition oneOrZeroCipher(g h : G)(c : G*G) : Sigma.S F DHTDisForm  :=
  oneOrZero((g,h),c).

(** Maps a generator g, public key h, ciphertext c, decryption factor d *)
Definition decFactorStatment(g h : G)(c : G*G)(d : G) : Sigma.S F DHTForm :=
  ((g,h),(c.1,d)).

(* The definition of encryption correctness for 1 of n*)  
Definition HeliosCorrectEncr  (g h :G)(prodCiph : (G*G))(cs : list (G*G)): Prop := 
    let zero := Gone in
    let one := g in
    decryptsToOneOrZero g h (prodCiph) /\
    Forall (decryptsToOneOrZero g h) cs.

(* The definition of encryption correctness for n of n*)  
Definition HeliosCorrectEncrApproval  (g h :G)(cs : list (G*G)): Prop := 
    let zero := Gone in
    let one := g in
    Forall (decryptsToOneOrZero g h) cs.
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
    | a :: b => parSigmaProtocol (recChalType b) F (OneOfNSigma b) DHTDisForm
  end.

(* The OneOfNSigma is a sigma protocol *)
Theorem OneOfNSigmaCorrect :
  forall (c : list (G*G)),
  SigmaProtocol (recChalType c) (OneOfNSigma c).
Proof.
  intros. unfold OneOfNSigma. induction c. apply DHTDisSigma.
  apply parCorr. apply IHc. apply DHTDisSigma.
Qed.

(* The n of n sigma protocol, produced from a list of length n *)
Fixpoint ApprovalSigma (c : list (G*G)) : Sigma.form (recChalType c) :=
  match c with
    | nil => emptyForm
    | a :: b => parSigmaProtocol (recChalType b) F (ApprovalSigma b) DHTDisForm
  end.

(* The ApprovalSigma is a sigma protocol *)
Theorem ApprovalSigmaCorrect :
  forall (c : list (G*G)),
  SigmaProtocol (recChalType c) (ApprovalSigma c).
Proof.
  intros. unfold ApprovalSigma. induction c. apply emptySigma.
  apply parCorr. apply IHc. apply DHTDisSigma.
Qed.

(* The decryption sigma *)
Definition DecryptionSigma :=
  parSigmaProtocol (F*F*F) F (parSigmaProtocol (F*F) F
    (parSigmaProtocol F F DHTForm DHTForm) DHTForm) DHTForm.

(* The DecryptionSigma is correct *)
Theorem DecryptionSigmaCorrect :
  SigmaProtocol (F*F*F*F) DecryptionSigma.
Proof.
  intros. unfold DecryptionSigma. apply parCorr. apply parCorr. apply parCorr. 
  apply DHTSigma. apply DHTSigma. apply DHTSigma.  apply DHTSigma. 
Qed.

(* Generates the OneOfN statement from ciphertexts *)
Fixpoint OneOfNStatment (g h : G)(cProd : G*G)(c : list (G*G)) : Sigma.S (recChalType c) (OneOfNSigma c):=
 match c with
  | nil  => (oneOrZeroCipher g h cProd)
  | a :: b => (OneOfNStatment g h cProd b, (oneOrZeroCipher g h a))
 end.

(* Generates the Approval statement from ciphertexts *)
Fixpoint ApprovalSigmaStatment (g h : G)(c : list (G*G)) : Sigma.S (recChalType c) (ApprovalSigma c):=
 match c with
  | nil  => (g)
  | a :: b => (ApprovalSigmaStatment g h b, (oneOrZeroCipher g h a))
 end.

(* Generates the decryption statement from generator g, ciphertext c,
  authority public keys y, and decryption factors d *)
Definition DecryptionSigmaStatment (g : G)(c : G*G)
  (y :(G*G*G*G)) (d :(G*G*G*G)): Sigma.S (F*F*F*F) DecryptionSigma :=

  ((decFactorStatment g y.1.1.1 c d.1.1.1),(decFactorStatment g y.1.1.2 c d.1.1.2),
    (decFactorStatment g y.1.2 c d.1.2),(decFactorStatment g y.2 c d.2)).

(* Proposition that correct encryption for a list of ciphertexts follows from the 
  special soundness of the sigma protocol verifier *)
Definition HeliosCorrectEncrApprovalList  (g h :G)(cs : list (list (G*G))): Prop := 
 forall x : list(G*G),
  In x cs -> (*Technical our proof generates a new sigma protocol for each voter *)

  let Sig := ApprovalSigma x in
  let s := (ApprovalSigmaStatment g h x) in

  forall (c : Sigma.C (recChalType x) Sig)(e1 e2 : (recChalType x))
    (t1 t2 : Sigma.T (recChalType x) Sig),
  Sigma.V1 (recChalType x) Sig (s,c,e1,t1) ->
  Sigma.V1 (recChalType x) Sig (s,c,e2,t2) ->
  Sigma.disjoint (recChalType x) Sig e1 e2 ->
  HeliosCorrectEncrApproval g h x.

(* Given a pair containing a ciphertext and message, as well generator g
  and public key h.  The ciphertext decrypts to the message  *)
Definition decryptionConsistent (g h : G)(pair: (G*G)*G) :=
  decryptsTo2 g h pair.1 pair.2.

(* Given a generator g, public key h, authority public keys y,
  list of decryption factors df, and a list of decryption tuples dt
  assert that if the relation between df and dt is basicly consitstent see below
  then the acceptence of the verify implies the claimed decryption is correct *)
Definition HeliosCorrectDecrList  (g h :G)(y: (G*G*G*G))
  (df : list(G*G*G*G))
  (dt : list ((G*G)*G)) : Prop :=
  
  let d := combine dt df in 

  forall x : ((G*G)*G*(G*G*G*G)),
  In x d -> (*For all values to check the decrytion of *)

   (*Basic consistence, the sum of decryption factors is equal to second element 
    of the ciphertext divided by the claimed message *)
  x.2.1.1.1 o x.2.1.1.2 o x.2.1.2 o x.2.2 = x.1.1.2 o - x.1.2 ->

  let Sig := DecryptionSigma in
  let s := DecryptionSigmaStatment g x.1.1 y x.2 in

  forall (c : Sigma.C (F*F*F*F) Sig)(e1 e2 : (F*F*F*F))(t1 t2 : Sigma.T (F*F*F*F) Sig),
  Sigma.V1 (F*F*F*F) Sig (s,c,e1,t1) ->
  Sigma.V1 (F*F*F*F) Sig (s,c,e2,t2) ->
  Sigma.disjoint (F*F*F*F) Sig e1 e2 ->
  decryptionConsistent g h x.1.

(* Basic lemma about how OneOfNStatment behaves under induction *)
Definition OneOfNStatmentLeft (g h : G)(prodCiph a : (G*G))(l : list(G*G)) : 
  let s := OneOfNStatment g h prodCiph (a :: l) in
   s.1 = (OneOfNStatment g h prodCiph l).
Proof.
  intros. trivial. 
Qed.

(* This theorem says that if the adversary can answer for more than one challenge
then the product ciphertexts is an encryption of zero or one. The step of reasoning that getting
the right challenge occurs with negliable probability in the random oracle model
is not modelled *) 
Lemma OneOfNCorrectProd :
  forall (g h :G)(cs : list (G*G))(prodCiph : (G*G)),
  let zero := Gone in
  let one := g in
  let Sig := OneOfNSigma cs in
  let s := (OneOfNStatment g h prodCiph cs) in

  forall (c : Sigma.C (recChalType cs) Sig)(e1 e2 : (recChalType cs))
    (t1 t2 : Sigma.T (recChalType cs) Sig),
  Sigma.V1 (recChalType cs) Sig (s,c,e1,t1) ->
  Sigma.V1 (recChalType cs) Sig (s,c,e2,t2) ->
  Sigma.disjoint (recChalType cs) Sig e1 e2 ->
  (exists r : F, (g ^ r, h ^ r o Gone) = prodCiph) \/
  (exists r : F, (g ^ r, h ^ r o g) = prodCiph).
Proof.
  pose HeliosIACR2018.
  + intros. assert (Sigma.Rel (recChalType cs) Sig s (Sigma.extractor (recChalType cs) Sig t1 t2 e1 e2)).
  eapply special_soundness with (c:=c). apply OneOfNSigmaCorrect. apply H1. apply H. apply H0.
 
  induction (cs).  
  (*Base case (decryption of product equal to 1 or 0) *)
  remember (Sigma.extractor (recChalType nil) Sig t1 t2 e1 e2) as w.
  case_eq (Gbool_eq (prodCiph).1 (g ^ w) && Gbool_eq ((prodCiph).2) (h ^ w)).
  intros. apply andb_true_iff in H3. destruct H3. left. exists w. 
  apply bool_eq_corr in H3. rewrite <- H3.
  apply bool_eq_corr in H4. rewrite <- H4. rewrite one_right.
  symmetry. apply surjective_pairing.  (* or 1 *)
  intros. right. unfold Sig in H2. simpl in H2. exists w. unfold dLog in H2. rewrite H3 in H2. simpl in H2.
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
  forall (g h :G)(cs : list (G*G))(prodCiph : (G*G)),
  let zero := Gone in
  let one := g in
  let Sig := OneOfNSigma cs in
  let s := (OneOfNStatment g h prodCiph cs) in

  forall (c : Sigma.C (recChalType cs) Sig)(e1 e2 : (recChalType cs))(t1 t2 : Sigma.T (recChalType cs) Sig),
  Sigma.V1 (recChalType cs) Sig (s,c,e1,t1) ->
  Sigma.V1 (recChalType cs) Sig (s,c,e2,t2) ->
  Sigma.disjoint (recChalType cs) Sig e1 e2 ->
  Forall (decryptsToOneOrZero g h) cs.
Proof.
  pose HeliosIACR2018.
  intros. (*Begining part two*)
  assert (Sigma.Rel (recChalType cs) Sig s (Sigma.extractor (recChalType cs) Sig t1 t2 e1 e2)).
  eapply special_soundness with (c:=c). apply OneOfNSigmaCorrect. apply H1. apply H. apply H0.
  unfold decryptsToOneOrZero. unfold decryptsTo.  unfold enc in *.
  (*Base case for second part of thorem*)
  induction cs.  exact. 
  (*Inductive case *)
  remember (Sigma.extractor (recChalType (a :: cs)) Sig t1 t2 e1 e2) as w. apply Forall_cons.
  case_eq (Gbool_eq (a).1 (g ^ w.2) && Gbool_eq ((a).2) (h ^ w.2)).
  intros. apply andb_true_iff in H3. destruct H3. left. exists w.2. 
  apply bool_eq_corr in H3. rewrite <- H3.
  apply bool_eq_corr in H4. rewrite <- H4. rewrite one_right. 
  symmetry. apply surjective_pairing. (*Or one *) 
  intros. right. unfold Sig in H2. simpl in H2. exists w.2. unfold dLog in H3.
   rewrite H3 in H2. simpl in H2.
  apply andb_true_iff in H2. destruct H2. 
  apply andb_true_iff in H4. destruct H4. unfold dLog in H4. unfold dLog in H5.
  apply bool_eq_corr in H4. rewrite (surjective_pairing a).
  simpl in H4. rewrite H4. apply bool_eq_corr in H5. simpl in H5.
   symmetry in H5. apply b_equal in H5.
   rewrite <- H5. replace (- - g) with g by apply dob_neg. trivial. 
    (*Inductive case for (decryption of product equal to 1 or 0) *)
  apply (IHcs c.1 e1.1 e2.1 t1.1 t2.1).  apply ParVerLeft in H. apply H.
   apply OneOfNSigmaCorrect. apply DHTDisSigma.  apply ParVerLeft in H0. apply H0.
   apply OneOfNSigmaCorrect. apply DHTDisSigma. apply ParDisLeft in H1.
  apply H1. apply OneOfNSigmaCorrect. apply DHTDisSigma. rewrite Heqw in H2.
  apply ParExtLeft in H2. apply H2. apply OneOfNSigmaCorrect. apply DHTDisSigma.
  trivial.
Qed.
  
(* We now use two precious lemmas to show that the sigma accepting implies that 
   each ciphertext is the encryption of zero or one and that the product is the 
  encryption of zero or one. *)
Theorem HeliosCorrextEncrImpliedBySigma :
  forall (g h :G)(cs : list (G*G)),
  let zero := Gone in
  let one := g in
  let Sig := OneOfNSigma cs in
  let s := (OneOfNStatment g h (Prod cs)  cs) in

  forall (c : Sigma.C (recChalType cs) Sig)(e1 e2 : recChalType cs)
    (t1 t2 : Sigma.T (recChalType cs) Sig),
  Sigma.V1 (recChalType cs) Sig (s,c,e1,t1) ->
  Sigma.V1 (recChalType cs) Sig (s,c,e2,t2) ->
  Sigma.disjoint (recChalType cs) Sig  e1 e2 ->
   HeliosCorrectEncr g h (Prod cs) cs.
  (* Proof of honest key generation *)
  (* Proof of correct decryption *)
Proof.
  intros. unfold HeliosCorrectEncr. split.  
   apply (OneOfNCorrectProd g h cs (Prod cs) c e1 e2 t1 t2).
  apply H. apply H0. apply H1.

  (*Begining part two*)
  apply (OneOfNAllDecryptToOneOrZero g h cs (Prod cs) c e1 e2 t1 t2).
  apply H. apply H0. apply H1. 
Qed.

(* We now show that the accepentence of ApprovalSigma implies that all 
  ciphertexts are the encryption of zero or one *)
Theorem HeliosCorrectEncrApprovalImpliedBySigma :
  forall (g h :G)(cs : list (G*G)),
  let zero := Gone in
  let one := g in
  let Sig := ApprovalSigma cs in
  let s := (ApprovalSigmaStatment g h cs) in

  forall (c : Sigma.C (recChalType cs) Sig)(e1 e2 : (recChalType cs))
    (t1 t2 : Sigma.T (recChalType cs) Sig),
  Sigma.V1 (recChalType cs) Sig (s,c,e1,t1) ->
  Sigma.V1 (recChalType cs) Sig (s,c,e2,t2) ->
  Sigma.disjoint (recChalType cs) Sig e1 e2 ->
  HeliosCorrectEncrApproval g h cs.
Proof.
  intros. unfold HeliosCorrectEncrApproval.
  pose HeliosIACR2018.
  intros. (*Begining part two*)
  assert (Sigma.Rel (recChalType cs) Sig s (Sigma.extractor (recChalType cs) Sig t1 t2 e1 e2)).
  eapply special_soundness with (c:=c). apply ApprovalSigmaCorrect. apply H1. apply H. apply H0.
  unfold decryptsToOneOrZero. unfold decryptsTo.  unfold enc in *.
  (*Base case for second part of thorem*)
  induction cs.  exact. 
  (*Inductive case *)
  remember (Sigma.extractor (recChalType (a :: cs)) Sig t1 t2 e1 e2) as w. apply Forall_cons.
  case_eq (Gbool_eq (a).1 (g ^ w.2) && Gbool_eq ((a).2) (h ^ w.2)).
  intros. apply andb_true_iff in H3. destruct H3. left. exists w.2. 
  apply bool_eq_corr in H3. rewrite <- H3.
  apply bool_eq_corr in H4. rewrite <- H4. rewrite one_right.
  symmetry. apply surjective_pairing. (*Or one *) 
  intros. right. unfold Sig in H2. simpl in H2. exists w.2. unfold dLog in H3.
   rewrite H3 in H2. simpl in H2.
  apply andb_true_iff in H2. destruct H2. 
  apply andb_true_iff in H4. destruct H4. unfold dLog in H4. unfold dLog in H5.
  apply bool_eq_corr in H4. rewrite (surjective_pairing a).
  simpl in H4. rewrite H4. apply bool_eq_corr in H5. simpl in H5.
   symmetry in H5. apply b_equal in H5.
   rewrite <- H5. replace (- - g) with g by apply dob_neg. trivial.
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
  forall (g h :G),
  forall (y: (G*G*G*G)),
  forall (df :list (G*G*G*G)),
  forall(dt : list ((G*G)*G)),
  let d := combine dt df in 
  ((y.1.1.1 o y.1.1.2) o y.1.2) o y.2 = h ->

  forall x : ((G*G)*G*(G*G*G*G)),
  In x d -> (*For all values to check the decrytion of *)

  x.2.1.1.1 o x.2.1.1.2 o x.2.1.2 o x.2.2 = x.1.1.2 o - x.1.2 ->

  let Sig := DecryptionSigma in
  let s := DecryptionSigmaStatment g x.1.1 y x.2 in

  forall (c : Sigma.C (F*F*F*F) Sig)(e1 e2 : (F*F*F*F))
    (t1 t2 : Sigma.T (F*F*F*F) Sig),
  Sigma.V1 (F*F*F*F) Sig (s,c,e1,t1) ->
  Sigma.V1 (F*F*F*F) Sig (s,c,e2,t2) ->
  Sigma.disjoint (F*F*F*F) Sig e1 e2 ->
  decryptionConsistent g h x.1.
Proof.
  pose HeliosIACR2018.  
  intros g h y df dt d key x xd.
  intros. assert (Sigma.Rel (F*F*F*F) Sig s (Sigma.extractor (F*F*F*F) Sig t1 t2 e1 e2)).
  eapply special_soundness with (c:=c). apply DecryptionSigmaCorrect. apply H2. apply H0. apply H1.
  remember (Sigma.extractor (F*F*F*F) Sig t1 t2 e1 e2) as w.
  unfold decryptionConsistent. unfold decryptsTo2.
  exists (w.1.1.1 + w.1.1.2 + w.1.2 + w.2). simpl in H3.
  unfold dLog in H3.  apply andb_true_iff in H3. destruct H3.  
  apply andb_true_iff in H3. destruct H3. 
  apply andb_true_iff in H3. destruct H3.
  apply andb_true_iff in H3. destruct H3. 
  apply andb_true_iff in H4. destruct H4.
  apply andb_true_iff in H5. destruct H5. 
  apply andb_true_iff in H6. destruct H6.
  simpl in *.  apply bool_eq_corr in H3.
  apply bool_eq_corr in H4. apply bool_eq_corr in H5.
  apply bool_eq_corr in H6. apply bool_eq_corr in H7.
  apply bool_eq_corr in H8. apply bool_eq_corr in H9.
  apply bool_eq_corr in H10. split. do 3 rewrite mod_dist_Fadd.
  rewrite <- H3. rewrite <- H5. rewrite <- H6.  rewrite <- H4.
  apply key. do 3 rewrite mod_dist_Fadd.
  rewrite <- H7. rewrite <- H8. rewrite <- H9.  rewrite <- H10.
  rewrite <- H. intuition.
Qed.

Theorem HeliosCorrectResultApproval :
  (*The outer list contains each voter and inner list contains there ciphertext on each option *)
  forall numOpts numVoter : nat,
  forall (g h :G)(cs : list (list (G*G))),
  forall (y : (G*G*G*G)),(*Authoritity keys *)
  forall (df : list (G*G*G*G)),(* Decryption Factors, each authority each option *)
  forall (r : list F),(* Results *)

  length cs = numVoter -> (*Basic data length consistency *)
  Forall (lenEqualToN numOpts) cs ->
  length df = numOpts ->
  length r = numOpts ->

  (*Data consistence*)
  y.1.1.1 o y.1.1.2 o y.1.2 o y.2 = h -> (*The authority decryption keys 
      combine to give the h*)
  
  let summation := map Prod cs in
  let resultInGroup := map (mapToGroup g) r in
  let dt := combine summation resultInGroup in

  (*All ballots are correctly formed AND the annonced result is correct *)
  HeliosCorrectEncrApprovalList g h cs /\ 
    HeliosCorrectDecrList g h y df dt.
Proof.
  intros numOpts numVoter g h cs y df r lenCiph1 lenCiph2
 lenD lenR keyCorrect summation resultInGroup dt. split.
  unfold HeliosCorrectEncrApprovalList. intros x inx. 
  apply (HeliosCorrectEncrApprovalImpliedBySigma).

  unfold HeliosCorrectDecrList. apply HeliosCorrectDecrListImplied.
  apply keyCorrect.
Qed.
 




