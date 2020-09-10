From Coq Require Extraction.
Require Import basicSigmas.
Require Import helios.
Require Import Coq.extraction.ExtrOcamlZBigInt.
Extraction Language OCaml.
 
Extraction "lib.ml"
  ALES ApprovalSigma ApprovalSigmaStatment DecryptionSigma DecryptionSigmaStatment.



(*
    choices = ciphertexts from voter.json  (v1003.json)
    (c,e1,t1) = individualProof from voter.json
    public key from product of authority public key
    subpublic key and decryptionfactors from authority.json
   ApprovalSigma expects a list (M*M) and returns a sigma protocol
  ApprovalSigmaStatment expects M M list (M*M) and returns a statmentfor
    ApprovalSigma
    ApprovalSigma.C = (M * M * (M * M)) repeated n times
    ApprovalSigma.E = R repated n times
    ApprovalSigma.T = R*R*R
    Structure of decryption factors
    s := M*
    
    c := M*(M*M)*(M*M)*(M*M)*(M*M)*(M*M)*(M*M)*(M*M)
    e1 := R*R*R*R*R*R*R*R
    t1 := R*(R*R)*(R*R)*(R*R)*(R*R)*(R*R)*(R*R)*(R*R)
     
      the inital values for c, e1 and t1 are for the empty
    sigma protocol, it will accept on all values
    1. For each voter take list of their ciphertexts
          sig = OverallFormApproval ciphertexts
          s = StatmentFormApproval g h ciphertexts
          sig.v1(s,c,e1,t1)
    2. Sum all the ciphertexts
    3. Check for each option that decryption is correct
        sig = DecryptionForm
        s := StatmentDcryptionForm
*)
