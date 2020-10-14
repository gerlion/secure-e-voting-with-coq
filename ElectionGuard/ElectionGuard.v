Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import groups.
Require Import vectorspace.
Require Import dualvectorspaces.
Require Import sigmaprotocol.
Require Import Coq.Lists.List.
Require Import Ring.
Require Import Field. 
Require Import Field_theory.
Require Import cryptoprim.
Require Import matrices.
Require Import matricesF.
Require Import basicSigmas.
Require Import modulevectorspace.
Require Import Vector.
From CoLoR Require Import VecUtil VecArith Matrix.
Require Import VectorUtil.
Require Import Recdef.

(** This section contains a number of standard sigma
 protocols compilied out of the dLog Sigma *)

(** we turn our attention to proving the sigma protocol
 for knowledge of discrete log *)

Set Implicit Arguments.

Module ElectionGuard (ElectionGuardG : GroupSig)(ElectionGuardF : FieldSig)
   (ElectionGuardVS : VectorSpaceSig ElectionGuardG ElectionGuardF).
Import ElectionGuardVS.
Module BS := BasicSigmas ElectionGuardG ElectionGuardF ElectionGuardVS.
Import BS.
Module DG := DualGroupIns ElectionGuardG.
Module DVS := DualVectorSpaceIns ElectionGuardG DG ElectionGuardF ElectionGuardVS.
Module MVS := VectorSpaceModuleSameGroupInsIns DG ElectionGuardF DVS.
Module ES := BasicElGamal ElectionGuardG ElectionGuardF ElectionGuardVS DG DVS MVS.
Module ALES := EncryptionSchemeProp ElectionGuardG DG ElectionGuardF ElectionGuardF 
    DVS MVS ES.
Import ALES.
Module MatrixF := MatricesFIns ElectionGuardF .
Import MatrixF.
Module Matrix := MatricesG ElectionGuardG ElectionGuardF ElectionGuardVS MatrixF.
Import Matrix.
Module MoC := MatricesG DG ElectionGuardF DVS MatrixF.
Import ElectionGuardG.

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

Definition DHTDisForm 
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
Definition ElectionGuardCorrectEncr (n : nat)(pk :ES.PK)
  (prodCiph : DG.G)(cs : vector DG.G n): Prop := 
    let zero := Gone in
    let one := pk.1 in
    decryptsTo pk (prodCiph) pk.1 /\
    Vforall (decryptsToOneOrZero pk pk.1) cs.

Fixpoint recChalType (n : nat) : Set :=
  match n with
    | 0%nat => F
    | S a => ((recChalType a)*F)
  end.

Fixpoint recChalTypeSelDec (n m : nat) : Set :=
  match n with
    | 0%nat => F
    | S a => ((recChalTypeSelDec a m)*(recChalType m))
  end.

(* The 1 of n sigma protocol, produced from a list of length n *)
Fixpoint OneOfNSigma (n : nat) : Sigma.form (recChalType n) :=
  match n with
    | 0%nat => DHTForm
    | S a => parSigmaProtocol (OneOfNSigma a) DHTDisForm
  end.

(* The OneOfNSigma is a sigma protocol *)
Theorem OneOfNSigmaCorrect :
  forall (n : nat),
  SigmaProtocol (OneOfNSigma n).
Proof.
  intros. unfold OneOfNSigma. induction n. apply DHTSigma.
  apply parCorr. apply IHn. apply DHTDisSigma.
Qed.

(* The decryption sigma *)
Fixpoint DecryptionSigma (n : nat) : Sigma.form (recChalType n) :=
  match n with
    | 0%nat => emptyForm 
    | S a => parSigmaProtocol (DecryptionSigma a) DHTForm
  end.

(* The DecryptionSigma is correct *)
Theorem DecryptionSigmaCorrect :
  forall (n : nat),
  SigmaProtocol (DecryptionSigma n).
Proof.
  intros. induction n. apply emptySigma.
  apply parCorr. apply IHn. apply DHTSigma.
Qed.

Fixpoint BallotDecSigma (numSel numAuth : nat) :
       Sigma.form (recChalTypeSelDec numSel numAuth) :=
  match numSel with
    | 0%nat => emptyForm 
    | S a => parSigmaProtocol 
       (BallotDecSigma a numAuth) (DecryptionSigma numAuth)
  end.

Theorem BallotDecSigmaCorrect :
  forall (n m : nat),
  SigmaProtocol (BallotDecSigma n m).
Proof.
  intros. induction n. apply emptySigma.
  apply parCorr. apply IHn. apply DecryptionSigmaCorrect.
Qed.

(* Generates the OneOfN statement from ciphertexts *)
Fixpoint OneOfNStatment (n : nat)(pk : ES.PK)(cProd : DG.G)
  (c : vector DG.G n) : Sigma.S (OneOfNSigma n):=
 match c with
  | nil  => ((pk.1,cProd.1),(pk.2,cProd.2 o - pk.1))
  | Vcons a b => (OneOfNStatment pk cProd b, (oneOrZeroCipher pk a))
 end.

(* Generates the decryption statement from generator g, ciphertext c,
  authority public keys y, and decryption factors d *)
Function DecryptionSigmaStatment (n : nat)(c : G*G)(g : G) :
    vector G n -> vector G n -> Sigma.S (DecryptionSigma n) :=
 match n with
   | 0%nat => fun v v1 => Gone
   | S a   => fun v v1 => (DecryptionSigmaStatment c g (Vtail v) (Vtail v1),
     (decFactorStatment (g,(Vhead v)) c (Vhead v1)))
  end.

Function BallotDecSigmaStatment (numSel numAuth : nat)(g : G)(pk : vector G numAuth) :
      vector DG.G numSel -> vector (vector G numAuth) numSel ->
      Sigma.S (BallotDecSigma numSel numAuth) :=
 match numSel with
   | 0%nat => fun v v1 => Gone
   | S a => fun v v1 => (BallotDecSigmaStatment g pk (Vtail v) (Vtail v1),
     (DecryptionSigmaStatment (Vhead v) g pk (Vhead v1)))
  end.

(* Given a pair containing a ciphertext and message, as well generator g
  and public key h.  The ciphertext decrypts to the message  *)
Definition decryptionConsistent (pk : ES.PK)(pair: DG.G*G) :=
  decryptsTo2 pk pair.1 pair.2.

(* This theorem says that if the adversary can answer for more than one challenge
then the product ciphertexts is an encryption of zero or one. The step of reasoning that getting
the right challenge occurs with negliable probability in the random oracle model
is not modelled *) 
Lemma OneOfNCorrectProd :
  forall (pk : ES.PK)(n : nat)(cs : vector (G*G) n)(prodCiph : (G*G)),
  let zero := Gone in
  let one := pk.1 in
  let Sig := OneOfNSigma n in
  let s := (OneOfNStatment pk prodCiph cs) in

  forall (c : Sigma.C Sig)(e1 e2 : (recChalType n))
    (t1 t2 : Sigma.T Sig),
  Sigma.V1 Sig (s,c,e1,t1) ->
  Sigma.V1 Sig (s,c,e2,t2) ->
  Sigma.disjoint Sig e1 e2 ->
  (exists r : F, (pk.1 ^ r, pk.2 ^ r o pk.1) = prodCiph).
Proof.
  pose ElectionGuardG.module_abegrp.
  + intros. assert (Sigma.Rel Sig s (Sigma.extractor Sig t1 t2 e1 e2)).
  eapply special_soundness with (c:=c). apply OneOfNSigmaCorrect. apply H1. apply H. apply H0.
  induction (cs).  
  (*Base case (decryption of product equal to 1 or 0) *)
  remember (Sigma.extractor Sig t1 t2 e1 e2) as w.
  intros. unfold Sig in H2. simpl in H2. exists w. unfold HardProb.dLog in H2.  simpl in H2.
  apply andb_true_iff in H2. destruct H2. apply bool_eq_corr in H2.
  rewrite <- H2.  apply bool_eq_corr in H3. rewrite <- H3. rewrite <- dot_assoc.
  rewrite <- inv_left. rewrite one_right. symmetry. apply surjective_pairing.
  (*Inductive case for (decryption of product equal to 1 or 0) *)
  apply (IHt (Vtail cs) c.1 e1.1 e2.1 t1.1 t2.1). apply ParVerLeft in H. apply H. 
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
  forall (pk : ES.PK)(n : nat)(cs : vector (G*G) n)(prodCiph : (G*G)),
  let zero := Gone in
  let one := pk.1 in
  let Sig := OneOfNSigma n in
  let s := (OneOfNStatment pk prodCiph cs) in

  forall (c : Sigma.C Sig)(e1 e2 : (recChalType n))
  (t1 t2 : Sigma.T Sig),
  Sigma.V1 Sig (s,c,e1,t1) ->
  Sigma.V1 Sig (s,c,e2,t2) ->
  Sigma.disjoint Sig e1 e2 ->
  Vforall (decryptsToOneOrZero pk one) cs.
Proof.
  pose ElectionGuardG.module_abegrp.
  intros. (*Begining part two*)
  assert (Sigma.Rel Sig s (Sigma.extractor Sig t1 t2 e1 e2)).
  eapply special_soundness with (c:=c). apply OneOfNSigmaCorrect. apply H1. apply H. apply H0.
  unfold decryptsToOneOrZero. unfold decryptsTo. unfold ES.enc in *.
  (*Base case for second part of thorem*)
  induction cs. exact. 
  (*Inductive case *)
  remember (Sigma.extractor Sig t1 t2 e1 e2) as w. simpl. split. 
  case_eq (Gbool_eq h.1 (pk.1 ^ w.2) && Gbool_eq h.2 (pk.2 ^ w.2)).
  intros. apply andb_true_iff in H3. destruct H3. left. exists w.2. 
  apply bool_eq_corr in H3. rewrite <- H3.
  apply bool_eq_corr in H4. rewrite <- H4. rewrite one_right. 
  symmetry. apply surjective_pairing. (*Or one *) 
  intros. right. unfold Sig in H2. simpl in H2. exists w.2. unfold HardProb.dLog in H3.
   rewrite H3 in H2. simpl in H2.
  apply andb_true_iff in H2. destruct H2. 
  apply andb_true_iff in H4. destruct H4. unfold HardProb.dLog in H4. unfold HardProb.dLog in H5.
  apply bool_eq_corr in H4. rewrite (surjective_pairing h).
  simpl in H4. rewrite H4. apply bool_eq_corr in H5. simpl in H5.
   symmetry in H5. apply b_equal in H5.
   rewrite <- H5. destruct pk. simpl. pose (dob_neg g).
  symmetry in e. unfold abegop. rewrite e. trivial. 
    (*Inductive case for (decryption of product equal to 1 or 0) *)
  apply (IHcs c.1 e1.1 e2.1 t1.1 t2.1).  apply ParVerLeft in H. apply H.
   apply OneOfNSigmaCorrect. apply DHTDisSigma.  apply ParVerLeft in H0. apply H0.
   apply OneOfNSigmaCorrect. apply DHTDisSigma. apply ParDisLeft in H1.
  apply H1. apply OneOfNSigmaCorrect. apply DHTDisSigma. rewrite Heqw in H2.
  apply ParExtLeft in H2. apply H2. apply OneOfNSigmaCorrect. apply DHTDisSigma.
  trivial.
Qed. 

Definition mapToGroup (g : G)(m : F) :=
  g^m.

Lemma DecryptionSigmaMeans : forall (numAuth : nat)
  (g : G)(pks df : VG numAuth)(b : DG.G)(result : F)
  (w : Sigma.W (DecryptionSigma numAuth)),
  let pk := (g, VG_prod pks) in
  Sigma.Rel
       (DecryptionSigma numAuth)
       (DecryptionSigmaStatment b g pks df) w = true -> 
  mapToGroup g result =
     b.2 o - VG_prod df ->
 decryptsTo2 pk b
  (mapToGroup g result).
Proof.
  pose ElectionGuardG.module_abegrp.
  intros. rewrite H0. unfold decryptsTo2.
  clear H0. unfold ES.keymatch, ES.dec. induction numAuth. 
  (* Base case *)
  exists 0. split. apply bool_eq_corr. unfold pk. 
  rewrite (Vector_0_is_nil pks). cbn. apply mod_ann. 
  rewrite (Vector_0_is_nil df). rewrite mod_ann. cbn. trivial.
  (* Inductive case *)
  simpl in H. apply andb_true_iff in H. destruct H.
  apply IHnumAuth in H. destruct H. exists (x + w.2).
  destruct H. apply bool_eq_corr in H. simpl in H.
  apply andb_true_iff in H0. destruct H0. unfold HardProb.dLog in H0.
  unfold HardProb.dLog in H2. apply bool_eq_corr in H0.
  apply bool_eq_corr in H2. simpl in *.
  split. apply bool_eq_corr. rewrite mod_dist_Fadd.
  simpl. rewrite (VSn_eq pks). rewrite VG_prod_Vcons.
  apply eqImplProd. split; auto. rewrite mod_dist_Fadd.
  rewrite (VSn_eq df). rewrite VG_prod_Vcons. rewrite H2.
  pose inv_dist. symmetry in e. do 2 rewrite e.
  do 2 rewrite dot_assoc. rewrite H1. intuition.
Qed. 

Definition ProofTranscript (A : Set)(sigma : Sigma.form A) : Type :=
  prod (prod (Sigma.C sigma) A) (Sigma.T sigma).

Fixpoint ProofTranDecAuthComm (n numAuth : nat) :
  Sigma.C
    (BallotDecSigma n (S numAuth)) ->
  Sigma.C 
    (BallotDecSigma n numAuth) :=
  match n with
    | 0%nat => fun a => a
    | S a   => fun b => (ProofTranDecAuthComm a numAuth b.1,
                           b.2.1)
  end.

Fixpoint ProofTranDecAuthChal (n numAuth : nat) :
  recChalTypeSelDec n (S numAuth) ->
  recChalTypeSelDec n numAuth :=
  match n with
    | 0%nat => fun a => a
    | S a   => fun b => (ProofTranDecAuthChal a numAuth b.1,
                           b.2.1)
  end.

Fixpoint ProofTranDecAuthResp (n numAuth : nat) :
  Sigma.T
    (BallotDecSigma n (S numAuth)) ->
  Sigma.T 
    (BallotDecSigma n numAuth) :=
  match n with
    | 0%nat => fun a => a
    | S a   => fun b => (ProofTranDecAuthResp a numAuth b.1,
                           b.2.1)
  end.

Definition ProofTranDecAuth (n numAuth : nat)
  (proof : ProofTranscript (BallotDecSigma n (S numAuth))) :
  ProofTranscript (BallotDecSigma n numAuth) :=
  (ProofTranDecAuthComm n numAuth proof.1.1,
     ProofTranDecAuthChal n numAuth proof.1.2,
       ProofTranDecAuthResp n numAuth proof.2).

Definition TransComp (A : Set)(sigma : Sigma.form A)
  (s : Sigma.S sigma)(proofs : ProofTranscript sigma) :=  
  (s,proofs.1.1,proofs.1.2,proofs.2).

(***********************************************)
(*                                             *)
(*                  Correct Encryption         *)
(*                                             *)
(***********************************************)

(* A prooduct of vectors, with an element corresponding
   to each contest *)
Fixpoint tally (numContests : nat) :
    vector nat numContests -> Set :=
  match numContests with
  | 0%nat => fun _ => Empty_set
  | _     => fun v => prod (VF (Vhead v)) (tally (Vtail v))
  end.

Fixpoint ballot (numContests : nat) :
    vector nat numContests -> Set :=
  match numContests with
  | 0%nat => fun _ => G
  | _     => fun v => prod (vector DG.G (Vhead v)) (ballot (Vtail v))
  end.

Fixpoint ballotProof (numContests : nat) :
    vector nat numContests -> Type :=
  match numContests with
    | 0%nat => fun _ => Empty_set
    | S n'  => fun v1 => prod (ProofTranscript (OneOfNSigma (Vhead v1)))
        (ballotProof (Vtail v1))
  end.

Fixpoint ballotProofDis (numContests : nat)(numSel : vector nat numContests) :
  ballotProof numSel -> ballotProof numSel -> Prop :=
  match numSel with
    | nil      => fun v1 v2 => True
    | cons h t => fun v1 v2 => (Sigma.disjoint (OneOfNSigma h) v1.1.1.2 v2.1.1.2) /\
        (ballotProofDis t v1.2 v2.2)
  end.

Fixpoint ballotProofComEq (numContests : nat)(numSel : vector nat numContests) :
  ballotProof numSel -> ballotProof numSel -> Prop :=
  match numSel with
    | nil      => fun v1 v2 => True
    | cons h t => fun v1 v2 =>  v1.1.1.1 = v2.1.1.1 /\
        (ballotProofComEq t v1.2 v2.2)
  end.

Definition SelectionVerifier (pk : ES.PK)(numSel : nat)
    (selections : vector DG.G numSel)
    (proof : ProofTranscript (OneOfNSigma numSel)) : bool :=
  let prod := MoC.VG_prod selections in 
  let statment := OneOfNStatment pk prod selections in 
  Sigma.V1 (OneOfNSigma numSel) (TransComp statment proof).

Function BallotVerifier (pk : ES.PK)(numContests : nat)
  (numSel : vector nat numContests) : ballot numSel -> ballotProof numSel -> bool :=
  match numSel with
    | nil => fun v1 v2 => true
    | cons h t => fun v1 v2 => 
      SelectionVerifier pk v1.1 v2.1
      && BallotVerifier pk t v1.2 v2.2
  end.

Fixpoint BallotCorrectlyFormed (pk : DG.G)(one : G)
  (numContests : nat)(numSel : vector nat numContests) :
  ballot numSel -> Prop :=
  match numSel with
    | nil => fun v => True
    | cons h t => fun v => 
      let prod := MoC.VG_prod v.1 in
      Vforall (decryptsToOneOrZero pk one) v.1 /\
      decryptsTo pk prod one /\
       BallotCorrectlyFormed pk one t v.2
  end. 

Lemma BallotVerifierCorrect : forall(pk : ES.PK)(numContests : nat)
  (numSel : vector nat numContests)(b : ballot numSel)
  (p p' : ballotProof numSel),
  BallotVerifier pk numSel b p ->
  BallotVerifier pk numSel b p'->
  ballotProofDis numSel p p' ->
  ballotProofComEq numSel p p' ->
  BallotCorrectlyFormed pk pk.1 numSel b.
Proof.
  intros. induction numSel. cbn. trivial.
  cbn. simpl in H. simpl in H0. apply andb_true_iff in H0.
  apply andb_true_iff in H. destruct H. destruct H0. simpl in H1.
  destruct H1. simpl in H2. destruct H2. split.
  pose (OneOfNAllDecryptToOneOrZero pk b.1 (MoC.VG_prod b.1) 
    p.1.1.1 p.1.1.2 p'.1.1.2 p.1.2 p'.1.2 ).
  apply v; simpl; auto. rewrite H2. auto. split.
  pose (OneOfNCorrectProd pk b.1 (MoC.VG_prod b.1) p.1.1.1 
    p.1.1.2 p'.1.1.2 p.1.2 p'.1.2).
  apply e; simpl; auto. rewrite H2. auto.
  apply (IHnumSel b.2 p.2 p'.2); auto. 
Qed.

(***********************************************)
(*                                             *)
(*                  Correct Decryption         *)
(*                                             *)
(***********************************************)

Fixpoint decryptionFactors (numContests numAuth : nat) :
  vector nat numContests -> Set :=
  match numContests with
    | 0%nat => fun _ => Empty_set
    | S n'  => fun v1 => 
        prod (vector (vector G numAuth) (Vhead v1))
        (decryptionFactors numAuth (Vtail v1))
  end.

Fixpoint decrytionProof (numContests numAuth : nat) :
    vector nat numContests -> Type :=
  match numContests with
    | 0%nat => fun _ => Empty_set
    | S n'  => fun v1 => prod (ProofTranscript (BallotDecSigma (Vhead v1) numAuth))
        (decrytionProof numAuth (Vtail v1))
  end.

Fixpoint decryptionProofDis (numContests numAuth : nat)
  (numSel : vector nat numContests) :
  decrytionProof numAuth numSel -> decrytionProof numAuth numSel -> Prop :=
  match numSel with
    | nil      => fun v1 v2 => True
    | cons h t => fun v1 v2 => 
        (Sigma.disjoint 
          (BallotDecSigma h numAuth) v1.1.1.2 v2.1.1.2) /\
        (decryptionProofDis numAuth t v1.2 v2.2)
  end.

Fixpoint decryptionProofComEq (numContests numAuth : nat)
  (numSel : vector nat numContests) :
  decrytionProof numAuth numSel -> decrytionProof numAuth numSel -> Prop :=
  match numSel with
    | nil      => fun v1 v2 => True
    | cons h t => fun v1 v2 =>  v1.1.1.1 = v2.1.1.1 /\
        (decryptionProofComEq numAuth t v1.2 v2.2)
  end.

Definition SelectionDecVerifier  (numSel numAuth : nat)(g : G)(pks : vector G numAuth)
    (selections : vector DG.G numSel)(decFactors : vector (vector G numAuth) numSel)
    (proof : ProofTranscript (BallotDecSigma numSel numAuth)) : bool :=
  let statment := BallotDecSigmaStatment g pks selections decFactors in 
  Sigma.V1 (BallotDecSigma numSel numAuth) 
    (TransComp statment proof).

Function DecryptionVerifier (numContests numAuth : nat)(g : G)(pks : vector G numAuth)
  (numSel : vector nat numContests) : ballot numSel ->
   decryptionFactors numAuth numSel -> decrytionProof numAuth numSel -> bool :=
   match numSel with
    | nil => fun v1 v2 v3 => true
    | cons h t => fun v1 v2 v3 => 
      SelectionDecVerifier g pks v1.1 v2.1 v3.1
      && DecryptionVerifier g pks t v1.2 v2.2 v3.2
  end.

Lemma DecryptionVerifierInd : forall (numContests numAuth h : nat)
  (g : G)(pks : vector G numAuth)(numSel : vector nat numContests)
  (b : ballot (Vcons h numSel))
  (decFactors : decryptionFactors numAuth (Vcons h numSel))
  (decProofs : decrytionProof numAuth  (Vcons h numSel)),
  DecryptionVerifier g pks (Vcons h numSel) b decFactors decProofs ->
    DecryptionVerifier g pks numSel
    b.2 decFactors.2 decProofs.2.
Proof.
  intros. simpl in H. destruct b. destruct decProofs. destruct decFactors.
  apply andb_true_iff in H. apply H.
Qed.

Fixpoint BallotCorrectlyDecrypted (pk : DG.G)
  (numContests : nat)(numSel : vector nat numContests) :
  ballot numSel -> tally numSel -> Prop :=
  match numSel with
    | nil => fun v1 v2 => True
    | cons h t => fun v1 v2 => 
      Vforall2 (decryptsTo2 pk) v1.1 (Vmap (mapToGroup pk.1) v2.1)
         /\ BallotCorrectlyDecrypted pk t v1.2 v2.2
  end.

Fixpoint ResultDecFactorsConsistentSub (numAuth numSel : nat)(g : G) :
  vector DG.G numSel -> vector (vector G numAuth) numSel ->
  vector F numSel -> Prop :=
  match numSel with 
    | 0%nat => fun _ _ _ => True
    | S a   => fun v1 v2 v3 => 
      mapToGroup g (Vhead v3) = 
        (Vhead v1).2 o - VG_prod (Vhead v2) /\
      ResultDecFactorsConsistentSub g (Vtail v1)
        (Vtail v2) (Vtail v3)
  end.

Fixpoint ResultDecFactorsConsistent (numContests numAuth : nat)(g : G)
  (numSel : vector nat numContests) :
  ballot numSel -> tally numSel -> decryptionFactors numAuth numSel -> Prop :=
  match numSel with
    | nil => fun v1 v2 v3 => True
    | cons h t => fun v1 v2 v3 => 
      ResultDecFactorsConsistentSub g v1.1 v3.1 v2.1 /\
        ResultDecFactorsConsistent numAuth g t v1.2 v2.2 v3.2
  end.
Lemma ResultDecFactorsConsistentInd : forall (numContests numAuth h : nat)
  (g : G)(numSel : vector nat numContests)
  (b : ballot (Vcons h numSel))
  (decFactors : decryptionFactors numAuth (Vcons h numSel))
  (result : tally (Vcons h numSel)),
  ResultDecFactorsConsistent numAuth g (Vcons h numSel) b result decFactors ->
    ResultDecFactorsConsistent numAuth g numSel
    b.2 result.2 decFactors.2.
Proof.
  intros. simpl in H. destruct b. destruct result. destruct decFactors.
  apply H.
Qed.

Fixpoint SumOfProd (numAuth : nat) :
  Sigma.W (DecryptionSigma numAuth) -> F :=
  match numAuth with
    | 0%nat => fun _ => 0
    | S a   => fun w => w.2 + (SumOfProd a w.1)
  end.

Lemma DecryptionVerifierCorrect : forall (numContests numAuth : nat)
  (g : G)(pks : vector G numAuth)(numSel : vector nat numContests)
  (b : ballot numSel)
  (decFactors : decryptionFactors numAuth numSel)
  (p p' : decrytionProof numAuth numSel)
  (result : tally numSel),
  DecryptionVerifier g pks numSel b decFactors p  ->
  DecryptionVerifier g pks numSel b decFactors p' ->
  decryptionProofDis numAuth numSel p p' ->
  decryptionProofComEq numAuth numSel p p' ->
  ResultDecFactorsConsistent numAuth g numSel b result decFactors ->
  let pk := (g, VG_prod pks) in
  BallotCorrectlyDecrypted pk numSel b result.
Proof.
  pose module_abegrp.
  intros. induction numSel. cbn. trivial.
  simpl in *. apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H0. destruct H0. destruct H1. destruct H2.
  destruct H3. pose BallotDecSigmaCorrect as correct. split. clear IHnumSel. 
  unfold SelectionDecVerifier, TransComp in H. 
  unfold SelectionDecVerifier, TransComp in H0.
  pose (BallotDecSigmaStatment g pks b.1 decFactors.1) as s.
  assert (Sigma.Rel 
    (BallotDecSigma h numAuth) s (Sigma.extractor 
    (BallotDecSigma h numAuth) p.1.2 p'.1.2 p.1.1.2 p'.1.1.2)). unfold s.
  apply special_soundness with (c:=p.1.1.1); auto.
  rewrite H2. auto. induction h. rewrite (Vector_0_is_nil b.1).
  rewrite (Vector_0_is_nil result.1). cbn. trivial.
  rewrite (VSn_eq b.1). rewrite (VSn_eq result.1). cbn.
  split.
  (* Non-inductive part *)
  clear IHh. simpl in H9. apply andb_true_iff in H9. destruct H9.
  simpl in H3. destruct H3.
  apply (DecryptionSigmaMeans pks (Vhead decFactors.1) (Vhead b.1)
  (Sigma.extractor (DecryptionSigma numAuth) p.1.2.2 p'.1.2.2
  p.1.1.2.2 p'.1.1.2.2) H10 H3).
  (* End inner induction *)
  simpl in H1, H0, H, H3, H9. apply andb_true_iff in H1. 
  apply andb_true_iff in H0. apply andb_true_iff in H.
  apply andb_true_iff in H9. destruct H1, H0, H, H3, H9.
  pose (IHh (Vtail b.1,b.2) (Vtail decFactors.1,decFactors.2)
  ((p.1.1.1.1,p.1.1.2.1,p.1.2.1) ,p.2) ((p'.1.1.1.1,p'.1.1.2.1,p'.1.2.1) ,p'.2) 
  (Vtail result.1,result.2)).
  unfold Vforall2 in v. apply v; auto. rewrite H2. auto. 
  (* Inductive hyp *)
  apply (IHnumSel b.2 decFactors.2 p.2 p'.2); auto.
Qed.


(***********************************************)
(*                                             *)
(*                  Main Verifier              *)
(*                                             *)
(***********************************************)

Fixpoint multBallots (numContests : nat)(numSel : vector nat numContests) :
  ballot numSel -> ballot numSel -> ballot numSel :=
  match numSel return ballot numSel -> ballot numSel -> ballot numSel with
    | Vnil => fun _ => fun _ => Gone
    | cons h t => fun b1 => fun b2 =>
      (MoC.VG_mult b1.1 b2.1, multBallots t b1.2 b2.2)
  end.

Lemma multBallotsVcons : forall (a numContests : nat)(numSel : vector nat numContests)
  (b1 b2 : ballot (Vcons a numSel)),
  multBallots (Vcons a numSel) b1 b2 =
    (MoC.VG_mult b1.1 b2.1, multBallots numSel b1.2 b2.2).
Proof.
  intros. auto.
Qed.

Lemma multBallotAssoc : forall (numContests : nat)
  (numSel : vector nat numContests)
  (b1 b2 b3 : ballot numSel),
  multBallots numSel (multBallots numSel b1 b2) b3 =
    multBallots numSel b1 (multBallots numSel b2 b3).
Proof.
  intros. induction numSel. cbn. trivial.
  simpl. rewrite IHnumSel. rewrite MoC.VG_assoc.
  trivial.
Qed. 

Lemma multBallotComm : forall (numContests : nat)
  (numSel : vector nat numContests)
  (b1 b2 : ballot numSel),
  multBallots numSel b1 b2 = multBallots numSel b2 b1.
Proof.
  intros. induction numSel. cbn. trivial.
  simpl. rewrite IHnumSel. rewrite MoC.VG_comm.
  trivial.
Qed.

Lemma rightCancelMultBallot : forall (numContests : nat)
  (numSel : vector nat numContests)
  (b1 b2 b3 : ballot numSel),
  b1 = b2 ->
  multBallots numSel b1 b3 = multBallots numSel b2 b3.
Proof.
  intros. rewrite H. trivial.
Qed.

Fixpoint zeroBallot (numContests : nat)
      (numSel : vector nat numContests) : 
    ballot numSel  :=
  match numSel with
  | nil => Gone
  | cons h t => (MoC.VG_id h, zeroBallot t)
  end. 

(* We can give the second it does not matter *)
Lemma multBallotsInd : forall (numContests numCast h : nat) 
  (numSel : vector nat numContests)
  (castBallots : vector  (ballot (Vcons h numSel)) numCast),
  (Vfold_left (multBallots (Vcons h numSel))
    (zeroBallot (Vcons h numSel)) castBallots).2 =
  Vfold_left (multBallots numSel)
    (zeroBallot numSel)
    (Vmap [eta snd] castBallots).
Proof.
  intros. rewrite Vfold_left_zip. rewrite Prod_right_replace. auto.
Qed.

Definition Verifier
  (* Parameters *)
  (numTrustees numCast numContests : nat)
  (numSel : vector nat numContests) 
  (g : G)(pks : vector G numTrustees)
  (* Cast ballots *)
  (castBallots : vector  (ballot numSel) numCast)
  (* Proofs of correct encryption *)
  (ballotProofs : vector (ballotProof numSel) numCast)
  (decFactors : decryptionFactors numTrustees numSel)
  (decProofs : decrytionProof numTrustees numSel) : bool := 
  let pk := (g, VG_prod pks) in
  let tally := Vfold_left (multBallots numSel) 
     (zeroBallot numSel) castBallots in
  (* Check proof of correct encryption *)
  (bVforall2 (BallotVerifier pk numSel)) numCast castBallots ballotProofs
  (* Checks proof of correct decryption *) && 
  DecryptionVerifier g pks numSel tally decFactors decProofs.

(***********************************************)
(*                                             *)
(*                  Main Theorem               *)
(*                                             *)
(***********************************************)

Theorem VerifierCorrect : forall 
  (numTrustees numCast numContests : nat)
  (numSel : vector nat numContests) 
  (g : G)(pks : vector G numTrustees)
  (* Cast ballots *)
  (castBallots : vector  (ballot numSel) numCast)
  (* Proofs of correct encryption *)
  (balProf1 balProf2 : vector (ballotProof numSel) numCast)
  (decFactors : decryptionFactors numTrustees numSel)
  (decProf1 decProf2 : decrytionProof numTrustees numSel)
  (result : tally numSel),

  let pk := (g, VG_prod pks) in
  let summation := Vfold_left (multBallots numSel) 
     (zeroBallot numSel) castBallots in
  
  (* The tally and the decryption factors are consistent *)
  ResultDecFactorsConsistent numTrustees g numSel summation result decFactors ->
  Verifier numSel g pks castBallots balProf1 decFactors decProf1 ->

  (* Conditions for special soundness *)
  Verifier numSel g pks castBallots balProf2 decFactors decProf2 ->
  Vforall2 (ballotProofDis numSel) balProf1 balProf2 ->
  Vforall2 (ballotProofComEq numSel) balProf1 balProf2 ->
  decryptionProofDis numTrustees numSel decProf1 decProf2 ->
  decryptionProofComEq numTrustees numSel decProf1 decProf2 ->

    Vforall (BallotCorrectlyFormed pk g numSel) castBallots /\
    BallotCorrectlyDecrypted pk numSel summation result.
  Proof.
    intros. unfold Verifier in H0. unfold Verifier in H1.
    apply andb_true_iff in H0. apply andb_true_iff in H1.
    destruct H0. destruct H1. split. clear H4. clear H5.
    clear H6. clear H7. clear H. induction castBallots.
    (* All correctly encryted *)
    cbn. trivial. simpl. simpl in H0. simpl in H1.
    rewrite (VSn_eq balProf1) in H0. cbn in H0.
    rewrite (VSn_eq balProf2) in H1. cbn in H1.
    rewrite (VSn_eq balProf1) in H2.
    rewrite (VSn_eq balProf2) in H2. cbn in H2.
    rewrite (VSn_eq balProf1) in H3.
    rewrite (VSn_eq balProf2) in H3. cbn in H3.
    apply andb_true_iff in H0. apply andb_true_iff in H1.
    destruct H0. destruct H1. destruct H2. destruct H3. split.
    apply (BallotVerifierCorrect pk numSel h (Vhead balProf1) 
      (Vhead balProf2)); auto.
    apply (IHcastBallots (Vtail balProf1) (Vtail balProf2)); auto.
    (* Correctly decrypted *)
    clear H0. clear H1. 
    apply (DecryptionVerifierCorrect g pks numSel summation 
      decFactors decProf1 decProf2); auto.
  Qed.
End ElectionGuard.
