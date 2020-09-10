Require Import groups.
Require Import cryptoprim.
Require Import basicSigmas.
Require Import wikstromMatrix.
Require Import HeliosIACR2018.
Require Import dualvectorspaces.
Require Import modulevectorspace.
Require Import nthvectorspaces.
Require Import CoLoR.Util.Vector.VecUtil.

(* Basic ElGamal *)
Module DualGroup := DualGroupIns HeliosIACR2018G.

Module DVS := DualVectorSpaceIns HeliosIACR2018G DualGroup
                        HeliosIACR2018F HeliosIACR2018VS.

Module MVS := VectorSpaceModuleSameGroupInsIns DualGroup HeliosIACR2018F DVS.

Module ES := BasicElGamal HeliosIACR2018G  HeliosIACR2018F
 HeliosIACR2018VS DualGroup DVS MVS.

Module M <: Nat.
  Definition N := 1%nat.
End M.

Module ElGamalWikstrom := WikstromMixnet HeliosIACR2018G DualGroup  
  HeliosIACR2018G HeliosIACR2018F HeliosIACR2018F HeliosIACR2018VS DVS 
  MVS ES M.

Print ElGamalWikstrom.