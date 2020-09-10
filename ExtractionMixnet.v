From Coq Require Extraction.
Require Import basicSigmas.
Require Import cryptoprim.
Require Import mixnetTest.
Require Import Coq.extraction.ExtrOcamlZBigInt.
Extraction Language OCaml.

Extraction "lib.ml" ElGamalWikstrom Nat.pred.
 
(*Extraction "lib.ml" 
  ApprovalSigma ApprovalSigmaStatment DecryptionSigma DecryptionSigmaStatment
  ALES.decryptsToExt. *)

