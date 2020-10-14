From Coq Require Extraction.
Require Import basicSigmas.
Require Import cryptoprim.
Require Import ElectionGuard.
Require Import EGmodules.
Require Import Coq.extraction.ExtrOcamlZBigInt.
Extraction Language OCaml.

Module EG := ElectionGuard ElectionGuardG ElectionGuardF ElectionGuardVS.

Extraction "lib.ml" 
  EG.OneOfNSigma EG.OneOfNStatment EG.DecryptionSigma EG.DecryptionSigmaStatment.

