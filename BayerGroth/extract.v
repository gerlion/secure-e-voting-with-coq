From Coq Require Extraction.
Require Import Coq.extraction.ExtrOcamlZBigInt. 
Require Import BayerGrothSupport BGZero BGHadProduct sigmaprotocolPlus5 BGShuffleArg BGSingleProd BGProdArg BGMultiexpArg sigmaprotocolPlus9.
Require Import HeliosIACR2018.
From Groups Require Import dualvectorspaces modulevectorspace groupfromring nthvectorspaces.
Require Import cryptoprim.
Extraction Language OCaml.

Module Ciphertext := DualGroupIns HeliosIACR2018G.
Module DVS := DualVectorSpaceIns HeliosIACR2018G Ciphertext HeliosIACR2018F HeliosIACR2018VS.
Module MVS := VectorSpaceModuleSameGroupInsIns Ciphertext HeliosIACR2018F DVS.
Module Chal := GroupFromRingIns HeliosIACR2018F.

(* This plus 1 *)
Module L <: Nat.
  Definition N:= 1.
End L.

Module NGroupM := GroupNthIns HeliosIACR2018G L.
Module NGroupC := GroupNthIns Ciphertext L.
Module Nthring := NthRingIns L HeliosIACR2018F.
Module Nthvs := NthVectorSpaceIns L Ciphertext HeliosIACR2018F NGroupC DVS.
Module NthvsM :=  NthVectorSpaceIns L HeliosIACR2018G HeliosIACR2018F NGroupM HeliosIACR2018VS.
Module NthMVS := VectorSpaceModuleSameGroupNthStackIns L Ciphertext HeliosIACR2018F HeliosIACR2018F DVS NGroupC Nthring Nthvs MVS.
Module Enc := ExtendedElGamal L HeliosIACR2018G HeliosIACR2018F HeliosIACR2018VS NGroupM Ciphertext DVS NGroupC Nthring Nthvs NthvsM NthMVS.

(* This makes the n parameter of BayerGroth 8 *) 
Module  N <: Nat.
  Definition  N := 5.
End N.

(* This makes the m paramater of BayerGroth 8 *)
Module M <: Nat.
  Definition N := 6.
End M.

Module Support := BGSupportIns NGroupM NGroupC HeliosIACR2018G Nthring HeliosIACR2018F HeliosIACR2018VS Nthvs NthMVS NthvsM N M Enc.

Module BGZeroarg := BGZeroArgIns NGroupM NGroupC HeliosIACR2018G Nthring HeliosIACR2018F HeliosIACR2018VS Nthvs Chal NthMVS NthvsM N M Enc Support.

Module BGHadprodbase := BGHadProdIns NGroupM NGroupC HeliosIACR2018G Nthring HeliosIACR2018F HeliosIACR2018VS Nthvs Chal NthMVS NthvsM N M Enc Support BGZeroarg.

Module BGHadprod := SigmaPlusTo5simTofullIns Chal BGZeroarg BGHadprodbase.

Module sig5 := SigmaPlus5CompIns Chal BGZeroarg BGHadprod.

Module sig := BGSingleProdIns HeliosIACR2018G HeliosIACR2018F HeliosIACR2018VS Chal N.

Module prodarg := ProdArgIns NGroupM NGroupC HeliosIACR2018G Nthring HeliosIACR2018F HeliosIACR2018VS Nthvs Chal NthMVS NthvsM N M Enc Support BGZeroarg BGHadprodbase BGHadprod sig5 sig.

Module prodarg2 := SigmaPlus5to5CompIns Chal sig sig5 prodarg.

Module BGMultiarg := BGMultiArgIns  NGroupM NGroupC HeliosIACR2018G Nthring HeliosIACR2018F HeliosIACR2018VS Nthvs Chal NthMVS NthvsM N M Enc Support.
                
Module SH := ShuffleArg  NGroupM NGroupC HeliosIACR2018G Nthring HeliosIACR2018F HeliosIACR2018VS Nthvs Chal NthMVS NthvsM N M Enc Support BGZeroarg BGHadprodbase BGHadprod sig5 sig prodarg prodarg2 BGMultiarg.

Module ShuffleSigma := SigmaPlus5plus3to9Comp Chal BGMultiarg prodarg2 SH.

Print ShuffleSigma.

Extraction "lib.ml" ShuffleSigma.V.
