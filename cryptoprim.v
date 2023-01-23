Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
From Groups Require Import groups module vectorspace dualvectorspaces
    nthvectorspaces modulevectorspace groupfromring genprodvectorspaces.
Require Import Coq.Lists.List.
Require Import Ring.
Require Import Field. 
Require Import Field_theory.
Require Import matrices matricesF.
From CoLoR Require Import VecUtil VecArith Matrix.
Require Import VectorUtil.
Require Import Lia.
Set Implicit Arguments.

(***********************************************************)
(*                                                         *)
(*       Mixable                                           *)
(*                                                         *)
(***********************************************************)

(* This is supposed to be a submodule of encryption schmes that also 
  covers Pedersen commitments, there are things that are mixable in 
  TW's mixnet which are less structured then this but I don't think
  anyone cares. *)
Module Type Mixable (Message Ciphertext : GroupSig)
  (Ring: RingSig)(Field : FieldSig)(VS : VectorSpaceSig Ciphertext Field)
    (MVS :  VectorSpaceModuleSameGroup Ciphertext Ring Field VS).
  Import MVS.
  Parameter KGR : Type.                 (* randomness for keygen *)
  Parameter PK : Type.                  (* public key space *)

  Definition M := Message.G.             (* message space    *)
  Definition Mop := Message.Gdot.  (* message space is an ablelian group *)
  Definition Mzero := Message.Gone.
  Definition Mone := Message.Ggen.
  Definition Minv := Message.Ginv.
  Definition Mbool_eq := Message.Gbool_eq.

  Parameter keygenMix : KGR -> PK.    (* key generation   *)
  Parameter enc : PK -> M -> Ring.F -> G. (* or commit *)

  Definition M_abgrp := Message.module_abegrp.

  Axiom homomorphism : forall (pk : PK)(m m' : M)(r r' : Ring.F),
                Ciphertext.Gdot (enc pk m' r')(enc pk m r) = 
                  enc pk (Mop m m') (Ring.Fadd r r'). 

  Axiom encOfOnePrec : forall (pk : PK)(a : Ring.F)(b :F),
          VS.op (enc pk Mzero a) b = enc pk Mzero (op3 a b).
End Mixable.

Module ParallelMixable (Hack : Nat)(Message Ciphertext : GroupSig)
  (Ring: RingSig)(Field : FieldSig)(VS : VectorSpaceSig Ciphertext Field)
  (MVS :  VectorSpaceModuleSameGroup Ciphertext Ring Field VS)
  (Mix : Mixable Message Ciphertext Ring Field VS MVS) (NthMessage : 
  GroupNthSig Message Hack)(NthCiphertext : GroupNthSig Ciphertext Hack)
  (NthRing : NthRingSig Hack Ring)(NthVS : NthVectorSpaceSig Hack Ciphertext
  Field NthCiphertext VS)(NthMVS : VectorSpaceModuleSameGroupNthStack Hack  
   Ciphertext Field Ring VS NthCiphertext NthRing NthVS MVS)
  <: Mixable NthMessage NthCiphertext NthRing Field NthVS NthMVS.
  Import NthMVS.
  Import Hack.

  (* We choose to use different keys for each position.
      We can obvisouly set them to be all the same  *) 
  Definition KGR := vector Mix.KGR (S N).       (* randomness for keygen *)
  Definition PK := vector Mix.PK (S N).         (* public key space *)

  Definition M := NthMessage.G.             (* message space    *)
  Definition Mop := NthMessage.Gdot.  (* message space is an ablelian group *)
  Definition Mzero := NthMessage.Gone.
  Definition Mone := Vconst Mix.Mone (S N).
  Definition Minv := NthMessage.Ginv.
  Definition Mbool_eq := NthMessage.Gbool_eq.

  Definition keygenMix (a : KGR) := Vmap Mix.keygenMix a.    (* key generation   *)
  Definition enc (pk : PK)(a : NthMessage.G) (b : NthRing.F) := 
      Vmap2 (fun a b => a b) (Vmap2 Mix.enc pk a) b. (* or commit *)

  Definition M_abgrp := NthMessage.module_abegrp.

  Lemma homomorphism : forall (pk : PK)(m m' : M)(r r' : NthRing.F),
                NthCiphertext.Gdot (enc pk m' r')(enc pk m r) = 
                  enc pk (Mop m m') (NthRing.Fadd r r'). 
  Proof.
    intros. apply Veq_nth. intros. do 7 rewrite Vnth_map2.
    rewrite Mix.homomorphism. do 2 rewrite Vnth_map2. trivial.
  Qed.

  Lemma encOfOnePrec : forall (pk : PK)(a : NthRing.F)(b : Field.F),
          NthVS.op (enc pk Mzero a) b = enc pk Mzero (op3 a b).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map.
    do 4 rewrite Vnth_map2. rewrite Vnth_const. rewrite Mix.encOfOnePrec.
    rewrite Vnth_map. trivial.
  Qed.

End ParallelMixable.

(* Given two mixables which share a field the product of the two
   mixables is also a mixables *)
Module ProductMixable (M1M M2M M1C M2C : GroupSig)
  (M1Ring M2Ring : RingSig)(Field : FieldSig)(VS1 : VectorSpaceSig M1C Field)
  (VS2 : VectorSpaceSig M2C Field)
  (MVS1 :  VectorSpaceModuleSameGroup M1C M1Ring Field VS1)
  (MVS2 :  VectorSpaceModuleSameGroup M2C M2Ring Field VS2)
  (Mix1 : Mixable M1M M1C M1Ring Field VS1 MVS1) 
  (Mix2 : Mixable M2M M2C M2Ring Field VS2 MVS2) 
  (* End input *)
  (Message : ProdGroupSig M1M M2M)(Ciphertext : ProdGroupSig M1C M2C)
  (Ring : ProdRingSig M1Ring M2Ring)
  (VS : ProdVectorSpaceSig M1C M2C Ciphertext Field VS1 VS2)
  (MVS : ProdVectorSpaceModuleSameGroup M1C M2C M1Ring M2Ring Field
    VS1 VS2 MVS1 MVS2 Ciphertext Ring VS)
  <: Mixable Message Ciphertext Ring Field VS MVS.

  Definition KGR := prod Mix1.KGR Mix2.KGR.       (* randomness for keygen *)
  Definition PK := prod Mix1.PK Mix2.PK.         (* public key space *)

  Definition M := Message.G.             (* message space    *)
  Definition Mop := Message.Gdot.  (* message space is an ablelian group *)
  Definition Mzero := Message.Gone.
  Definition Mone := (Mix1.Mone, Mix2.Mone).
  Definition Minv := Message.Ginv.
  Definition Mbool_eq := Message.Gbool_eq.

  Definition keygenMix (a : KGR) := 
    (Mix1.keygenMix a.1, Mix2.keygenMix a.2).    (* key generation *)
  Definition enc (pk : PK)(a : Message.G) (b : Ring.F) := 
      (Mix1.enc pk.1 a.1 b.1, Mix2.enc pk.2 a.2 b.2). (* or commit *)

  Definition M_abgrp := Message.module_abegrp.

  Lemma homomorphism : forall (pk : PK)(m m' : M)(r r' : Ring.F),
                Ciphertext.Gdot (enc pk m' r')(enc pk m r) = 
                  enc pk (Mop m m') (Ring.Fadd r r'). 
  Proof.
    intros. unfold enc. cbn. rewrite <- Mix1.homomorphism.
    rewrite <- Mix2.homomorphism. trivial.
  Qed.

  Lemma encOfOnePrec : forall (pk : PK)(a : Ring.F)(b : Field.F),
          VS.op (enc pk Mzero a) b = enc pk Mzero (MVS.op3 a b).
  Proof.
    intros. unfold enc. cbn. rewrite <- Mix1.encOfOnePrec.
    rewrite <- Mix2.encOfOnePrec. trivial.
  Qed.

End ProductMixable.

(***********************************************************)
(*                                                         *)
(*       Encryption Scheme                                 *)
(*                                                         *)
(***********************************************************)

(* This wants to be switched to work for near vector spaces *)
Module Type EncryptionScheme (Message Ciphertext : GroupSig)
    (Ring: RingSig)(Field : FieldSig)(VS : VectorSpaceSig Ciphertext Field)
    (MVS :  VectorSpaceModuleSameGroup Ciphertext Ring Field VS)
      <: Mixable Message Ciphertext Ring Field VS MVS.
  Import MVS.
    Parameter KGR : Type.                 (* randomness for keygen *)
    Parameter PK : Type.                  (* public key space *)
    Parameter SK : Type.                  (* secret key space *)
    Definition M := Message.G.             (* message space    *)
    Definition Mop := Message.Gdot.  (* message space is an ablelian group *)
    Definition Mzero := Message.Gone.
    Definition  Mone := Message.Ggen.
    Definition Minv := Message.Ginv.
    Definition Mbool_eq := Message.Gbool_eq.

    Parameter keygen : KGR -> (PK*SK).    (* key generation   *)
    Definition keygenMix kgr := (keygen kgr).1. 
    Parameter enc : PK -> M -> Ring.F -> G.    (* encryption       *)
    Parameter dec : SK -> G -> M.         (* decryption       *)
    Parameter keymatch : PK -> SK -> bool. (* checks key consistence *)
     (* reencryption is defined in EncryptionSchemeProp   *)

    Axiom correct : forall (kgr : KGR)(m : M)(r : Ring.F),
                dec (keygen kgr).2 (enc (keygen kgr).1 m r) = m.

    Definition M_abgrp := Message.module_abegrp.

    Axiom homomorphism : forall (pk : PK)(m m' : M)(r r' : Ring.F),
                Ciphertext.Gdot (enc pk m' r')(enc pk m r) = 
                  enc pk (Mop m m') (Ring.Fadd r r'). 

    Axiom encOfOnePrec : forall (pk : PK)(a : Ring.F)(b :F),
          VS.op (enc pk Mzero a) b = enc pk Mzero (op3 a b).

  Axiom encZero : forall (pk : PK),
      enc pk Mzero Ring.Fzero = Gone.
  
End EncryptionScheme.

Module ProductEncryptionScheme (M1M M2M M1C M2C : GroupSig)
  (M1Ring M2Ring : RingSig)(Field : FieldSig)(VS1 : VectorSpaceSig M1C Field)
  (VS2 : VectorSpaceSig M2C Field)
  (MVS1 :  VectorSpaceModuleSameGroup M1C M1Ring Field VS1)
  (MVS2 :  VectorSpaceModuleSameGroup M2C M2Ring Field VS2)
  (ES1 : EncryptionScheme M1M M1C M1Ring Field VS1 MVS1) 
  (ES2 : EncryptionScheme M2M M2C M2Ring Field VS2 MVS2) 
  (* End input *)
  (Message : ProdGroupSig M1M M2M)(Ciphertext : ProdGroupSig M1C M2C)
  (Ring : ProdRingSig M1Ring M2Ring)
  (VS : ProdVectorSpaceSig M1C M2C Ciphertext Field VS1 VS2)
  (MVS : ProdVectorSpaceModuleSameGroup M1C M2C M1Ring M2Ring Field
    VS1 VS2 MVS1 MVS2 Ciphertext Ring VS)
  <: EncryptionScheme Message Ciphertext Ring Field VS MVS.

  Definition KGR := prod ES1.KGR ES2.KGR.       (* randomness for keygen *)
  Definition PK := prod ES1.PK ES2.PK.         (* public key space *)
  Definition SK := prod ES1.SK ES2.SK.         (* public key space *)

  Definition M := Message.G.             (* message space    *)
  Definition Mop := Message.Gdot.  (* message space is an ablelian group *)
  Definition Mzero := Message.Gone.
  Definition Mone := (ES1.Mone, ES2.Mone).
  Definition Minv := Message.Ginv.
  Definition Mbool_eq := Message.Gbool_eq.

  Definition keygen (a : KGR) :=
    (((ES1.keygen a.1).1, (ES2.keygen a.2).1), 
      ((ES1.keygen a.1).2, (ES2.keygen a.2).2)). 
  Definition keygenMix kgr := (keygen kgr).1.
  Definition enc (pk : PK)(a : Message.G) (b : Ring.F) := 
      (ES1.enc pk.1 a.1 b.1, ES2.enc pk.2 a.2 b.2). 
  Definition dec sk m := (ES1.dec sk.1 m.1, ES2.dec sk.2 m.2).      
  Definition keymatch pk sk := ES1.keymatch pk.1 sk.1 &&
          ES2.keymatch pk.2 sk.2.

  Lemma correct : forall (kgr : KGR)(m : M)(r : Ring.F),
                dec (keygen kgr).2 (enc (keygen kgr).1 m r) = m.
  Proof.
    intros. unfold dec. cbn. rewrite ES1.correct.
    rewrite ES2.correct. apply injective_projections; auto.
  Qed.

  Definition M_abgrp := Message.module_abegrp.

  Lemma homomorphism : forall (pk : PK)(m m' : M)(r r' : Ring.F),
                Ciphertext.Gdot (enc pk m' r')(enc pk m r) = 
                  enc pk (Mop m m') (Ring.Fadd r r'). 
  Proof.
    intros. unfold enc. cbn. rewrite <- ES1.homomorphism.
    rewrite <- ES2.homomorphism. trivial.
  Qed.

  Lemma encOfOnePrec : forall (pk : PK)(a : Ring.F)(b : Field.F),
          VS.op (enc pk Mzero a) b = enc pk Mzero (MVS.op3 a b).
  Proof.
    intros. unfold enc. cbn. rewrite <- ES1.encOfOnePrec.
    rewrite <- ES2.encOfOnePrec. trivial.
  Qed.

  Lemma encZero : forall (pk : PK),
      enc pk Mzero Ring.Fzero = Ciphertext.Gone.
  Proof.
    intros. unfold enc. rewrite ES1.encZero. rewrite ES2.encZero.
    trivial.
  Qed.

End ProductEncryptionScheme.


(***********************************************************)
(*                                                         *)
(*       Encryption Scheme Plus                            *)
(*                                                         *)
(***********************************************************)

Module Type EncryptionSchemePlus (Message Ciphertext : GroupSig)
    (Ring: RingSig)(Field : FieldSig)(VS : VectorSpaceSig Ciphertext Field)
    (VSM : VectorSpaceSig Message Field)
    (MVS :  VectorSpaceModuleSameGroup Ciphertext Ring Field VS)
      <: EncryptionScheme Message Ciphertext Ring Field VS MVS.
  Import MVS.
    Parameter KGR : Type.                 (* randomness for keygen *)
    Parameter PK : Type.                  (* public key space *)
    Parameter SK : Type.                  (* secret key space *)
    Definition M := Message.G.             (* message space    *)
    Definition Mop := Message.Gdot.  (* message space is an ablelian group *)
    Definition Mzero := Message.Gone.
    Definition Mone := Message.Ggen.
    Definition Minv := Message.Ginv.
    Definition Mbool_eq := Message.Gbool_eq.

    Parameter keygen : KGR -> (PK*SK).    (* key generation   *)
    Definition keygenMix kgr := (keygen kgr).1. 
    Parameter enc : PK -> M -> Ring.F -> G.    (* encryption       *)
    Parameter dec : SK -> G -> M.         (* decryption       *)
    Parameter keymatch : PK -> SK -> bool. (* checks key consistence *)
     (* reencryption is defined in EncryptionSchemeProp   *)

    Axiom correct : forall (kgr : KGR)(m : M)(r : Ring.F),
                dec (keygen kgr).2 (enc (keygen kgr).1 m r) = m.

    Definition M_abgrp := Message.module_abegrp.

    Axiom homomorphism : forall (pk : PK)(m m' : M)(r r' : Ring.F),
                Ciphertext.Gdot (enc pk m' r')(enc pk m r) = 
                  enc pk (Mop m m') (Ring.Fadd r r'). 

    Axiom encOfOnePrec : forall (pk : PK)(a : Ring.F)(b :F),
          VS.op (enc pk Mzero a) b = enc pk Mzero (op3 a b).

    Axiom encDis : forall (pk : PK)(g : M)(a : Ring.F)(b b' : F),
          VS.op (enc pk (VSM.op g b) a) b' = 
            enc pk (VSM.op g (b*b')) (op3 a b').

    Axiom encZero : forall (pk : PK),
      enc pk Mzero Ring.Fzero = Gone.

End EncryptionSchemePlus.


Module ParallelEncryptionSchemePlus (Hack : Nat)(Message Ciphertext : GroupSig)
  (Ring: RingSig)(Field : FieldSig)(VS : VectorSpaceSig Ciphertext Field)
  (VSM : VectorSpaceSig Message Field)
  (MVS :  VectorSpaceModuleSameGroup Ciphertext Ring Field VS)
  (ES : EncryptionSchemePlus Message Ciphertext Ring Field VS VSM MVS) 
  (NthMessage :  GroupNthSig Message Hack)(NthCiphertext : GroupNthSig Ciphertext Hack)
  (NthRing : NthRingSig Hack Ring)(NthVS : NthVectorSpaceSig Hack Ciphertext
  Field NthCiphertext VS)(NthVSM : NthVectorSpaceSig Hack Message
  Field NthMessage VSM)(NthMVS : VectorSpaceModuleSameGroupNthStack Hack  
   Ciphertext Field Ring VS NthCiphertext NthRing NthVS MVS)
  <: EncryptionSchemePlus NthMessage NthCiphertext NthRing Field NthVS NthVSM
     NthMVS.
  Import NthMVS.
  Import Hack.

  (* We choose to use different keys for each position.
      We can obvisouly set them to be all the same  *) 
  Definition KGR := vector ES.KGR (S N).       (* randomness for keygen *)
  Definition PK := vector ES.PK (S N).         (* public key space *)
  Definition SK := vector ES.SK (S N). 
  Definition M := NthMessage.G.             (* message space    *)
  Definition Mop := NthMessage.Gdot.  (* message space is an ablelian group *)
  Definition Mzero := NthMessage.Gone.
  Definition Mone := Vconst ES.Mone (S N).
  Definition Minv := NthMessage.Ginv.
  Definition Mbool_eq := NthMessage.Gbool_eq.

  Definition keygen (a : KGR) := Unzip (Vmap ES.keygen a).    (* key generation   *)
  Definition keygenMix (a : KGR) := (keygen a).1.    (* key generation   *)
  Definition enc (pk : PK)(a : NthMessage.G) (b : NthRing.F) := 
      Vmap2 (fun a b => a b) (Vmap2 ES.enc pk a) b. (* or commit *)
  (* decryption *)
  Definition dec (sk : SK)(c : NthCiphertext.G) := Vmap2 ES.dec sk c. 
  (* checks key consistence *) 
  Definition keymatch (pk : PK)(sk : SK) := bVforall (fun x =>
    ES.keymatch x.1 x.2) (Zip pk sk) . 
     (* reencryption is defined in EncryptionSchemeProp   *)

  Lemma correct : forall (kgr : KGR)(m : M)(r : NthRing.F),
                dec (keygen kgr).2 (enc (keygen kgr).1 m r) = m.
  Proof.
    intros. apply Veq_nth. intros. do 3 rewrite Vnth_map2. 
    do 4 rewrite Vnth_map. pose (ES.correct (Vnth kgr ip)
    (Vnth m ip) (Vnth r ip)). apply e.
  Qed.

  Definition M_abgrp := NthMessage.module_abegrp.

  Lemma homomorphism : forall (pk : PK)(m m' : M)(r r' : NthRing.F),
                NthCiphertext.Gdot (enc pk m' r')(enc pk m r) = 
                  enc pk (Mop m m') (NthRing.Fadd r r'). 
  Proof.
    intros. apply Veq_nth. intros. do 7 rewrite Vnth_map2.
    rewrite ES.homomorphism. do 2 rewrite Vnth_map2. trivial.
  Qed.

  Lemma encOfOnePrec : forall (pk : PK)(a : NthRing.F)(b : Field.F),
          NthVS.op (enc pk Mzero a) b = enc pk Mzero (op3 a b).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map.
    do 4 rewrite Vnth_map2. rewrite Vnth_const. rewrite ES.encOfOnePrec.
    rewrite Vnth_map. trivial.
  Qed.

  Lemma encDis : forall (pk : PK)(g : M)(a : NthRing.F)(b b' : Field.F),
          NthVS.op (enc pk (NthVSM.op g b) a) b' = 
            enc pk (NthVSM.op g (Field.Fmul b b')) (op3 a b').
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. do 4 rewrite Vnth_map2.
    do 3 rewrite Vnth_map.  rewrite ES.encDis. trivial.
  Qed.

  Lemma encZero : forall (pk : PK),
    enc pk Mzero NthRing.Fzero = NthCiphertext.Gone.
  Proof.
    intros. apply Veq_nth. intros. do 2 rewrite Vnth_map2.
    do 3 rewrite Vnth_const. rewrite ES.encZero. trivial.
  Qed.

End ParallelEncryptionSchemePlus.

Module Type MixableProp  (Message Ciphertext : GroupSig)(Ring: RingSig)
    (Field : FieldSig)(VS : VectorSpaceSig Ciphertext Field)
    (MVS :  VectorSpaceModuleSameGroup Ciphertext Ring Field VS)
    (Mix : Mixable Message Ciphertext Ring Field VS MVS).
  Import Mix.
  Import MVS.
  Module AddVSLemmas := VectorSpaceAddationalLemmas Ciphertext Field VS.
  Import AddVSLemmas.

  Module Mat := MatricesFIns Field.
  Module MatG := MatricesG Ciphertext Field VS Mat.

  Definition reenc (pk : PK)(c: G)(r : Ring.F) : G :=
    Ciphertext.Gdot (enc pk Mzero r) c.

  Lemma EncInv : 
  forall (pk : PK)(a : Ring.F),
    enc pk Mzero (Ring.Finv a) = Ginv (enc pk Mzero a).
  Proof.
    intros. replace (Ring.Finv a) with (op3 a (Finv Fone)). rewrite <- encOfOnePrec.
    rewrite <- neg_eq. rewrite VS.mod_id. trivial. apply RopInv.
  Qed. 

  Lemma EncEq : 
  forall (pk : PK)(m1 m2  : M)(r1 r2 : Ring.F),
    m1 = m2 -> r1 = r2 -> enc pk m1 r1 = enc pk m2 r2.
  Proof.
    intros. rewrite H. rewrite H0. auto.
  Qed.

  Definition IsReEnc (pk : PK)(c1 c2 : G)(r : Ring.F) : Prop :=
    c2 = reenc pk c1 r.

  Definition bIsReEnc (pk : PK)(c1 c2 : G)(r : Ring.F) : bool :=
    Gbool_eq c2 (reenc pk c1 r).

  Lemma EncZeroZeroIsOne : forall (pk : PK),
      enc pk Mzero Ring.Fzero = Gone.
  Proof.
    intros. replace Ring.Fzero with (op3 Ring.Fzero Fzero).
    rewrite <- encOfOnePrec. rewrite VS.mod_ann.
    trivial. apply RopRZero.
  Qed.

  (* Given a generator g, public key h, ciphertext c,
  and message m *)
  Definition decryptsTo (pk :PK)(c : G)(m : M) :=
    exists (r : Ring.F), enc pk m r = c.

  Definition decryptsToExt (pk :PK)(c : G)(m : M)(r : Ring.F) :=
    let c' := (enc pk m r) in
    Gbool_eq c' c.

  (* Given a generator g, public key h, ciphertext c,
    c is an encryption of zero or one *)
  Definition decryptsToOneOrZero (pk :PK)(one : M)(c : G) : Prop  :=
    let zero := Mzero in
    decryptsTo pk c zero \/ decryptsTo pk c one.

  Lemma comHomomorphism : forall l (pk :PK)(m : vector M l)(r : vector Ring.F l),
    enc pk (Vfold_left Mop Mzero m) (Vfold_left Ring.Fadd Ring.Fzero r) =
    Vfold_left Ciphertext.Gdot (enc pk Mzero Ring.Fzero) (Vmap2 (enc pk) m r).
  Proof.
    pose Message.module_abegrp. destruct Ring.module_ring.
    intros. induction l. rewrite (Vector_0_is_nil m). rewrite (Vector_0_is_nil r). 
    cbn. trivial. simpl. rewrite <-  MatG.Vfold_Gdot_const. rewrite <- IHl.
    rewrite homomorphism. apply f_equal2. rewrite Vfold_left_induction.
    intros. rewrite dot_assoc. trivial. intros. apply comm. trivial.
    rewrite Vfold_left_induction. intros. symmetry. apply Radd_assoc.
    intros. apply Radd_comm. trivial.
  Qed.

  Lemma encOfOnePrec_build : forall pk n (gen :  forall i, i < n -> Ring.F)
      (a : vector F n),
    Vmap2 VS.op (Vbuild (fun j (jp : j < n) => enc pk Mzero (gen j jp))) a = 
      Vbuild (fun j (jp : j < n) => enc pk Mzero (op3 (gen j jp) (Vnth a jp))).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vbuild_nth. 
    apply encOfOnePrec.
  Qed.

  Lemma encOfOnePrec_map : forall pk n (b : vector Ring.F n)
      (a : vector F n),
    Vmap2 VS.op (Vmap (fun x => enc pk Mzero x) b) a =
     Vmap (fun x => enc pk Mzero x) (Vmap2 op3 b a).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vnth_map. 
    rewrite Vnth_map2. apply encOfOnePrec.
  Qed.

End MixableProp.

Module MixablePropIns  (Message Ciphertext : GroupSig)(Ring: RingSig)
    (Field : FieldSig)(VS : VectorSpaceSig Ciphertext Field)
    (MVS :  VectorSpaceModuleSameGroup Ciphertext Ring Field VS)
    (Mix : Mixable Message Ciphertext Ring Field VS MVS)
    <: MixableProp Message Ciphertext Ring Field VS MVS Mix.
  Import Mix.
  Import MVS.
  Module AddVSLemmas := VectorSpaceAddationalLemmas Ciphertext Field VS.
  Import AddVSLemmas.

  Module Mat := MatricesFIns Field.
  Module MatG := MatricesG Ciphertext Field VS Mat.

  Definition reenc (pk : PK)(c: G)(r : Ring.F) : G :=
    Ciphertext.Gdot (enc pk Mzero r) c.

  Lemma EncInv : 
  forall (pk : PK)(a : Ring.F),
    enc pk Mzero (Ring.Finv a) = Ginv (enc pk Mzero a).
  Proof.
    intros. replace (Ring.Finv a) with (op3 a (Finv Fone)). rewrite <- encOfOnePrec.
    rewrite <- neg_eq. rewrite VS.mod_id. trivial. apply RopInv.
  Qed. 

  Lemma EncEq : 
  forall (pk : PK)(m1 m2  : M)(r1 r2 : Ring.F),
    m1 = m2 -> r1 = r2 -> enc pk m1 r1 = enc pk m2 r2.
  Proof.
    intros. rewrite H. rewrite H0. auto.
  Qed.

  Definition IsReEnc (pk : PK)(c1 c2 : G)(r : Ring.F) : Prop :=
    c2 = reenc pk c1 r.

  Definition bIsReEnc (pk : PK)(c1 c2 : G)(r : Ring.F) : bool :=
    Gbool_eq c2 (reenc pk c1 r).

  Lemma EncZeroZeroIsOne : forall (pk : PK),
      enc pk Mzero Ring.Fzero = Gone.
  Proof.
    intros. replace Ring.Fzero with (op3 Ring.Fzero Fzero).
    rewrite <- encOfOnePrec. rewrite VS.mod_ann.
    trivial. apply RopRZero.
  Qed.

  (* Given a generator g, public key h, ciphertext c,
  and message m *)
  Definition decryptsTo (pk :PK)(c : G)(m : M) :=
    exists (r : Ring.F), enc pk m r = c.

  Definition decryptsToExt (pk :PK)(c : G)(m : M)(r : Ring.F) :=
    let c' := (enc pk m r) in
    Gbool_eq c' c.

  (* Given a generator g, public key h, ciphertext c,
    c is an encryption of zero or one *)
  Definition decryptsToOneOrZero (pk :PK)(one : M)(c : G) : Prop  :=
    let zero := Mzero in
    decryptsTo pk c zero \/ decryptsTo pk c one.

  Lemma comHomomorphism : forall l (pk :PK)(m : vector M l)(r : vector Ring.F l),
    enc pk (Vfold_left Mop Mzero m) (Vfold_left Ring.Fadd Ring.Fzero r) =
    Vfold_left Ciphertext.Gdot (enc pk Mzero Ring.Fzero) (Vmap2 (enc pk) m r).
  Proof.
    pose Message.module_abegrp. destruct Ring.module_ring.
    intros. induction l. rewrite (Vector_0_is_nil m). rewrite (Vector_0_is_nil r). 
    cbn. trivial. simpl. rewrite <-  MatG.Vfold_Gdot_const. rewrite <- IHl.
    rewrite homomorphism. apply f_equal2. rewrite Vfold_left_induction.
    intros. rewrite dot_assoc. trivial. intros. apply comm. trivial.
    rewrite Vfold_left_induction. intros. symmetry. apply Radd_assoc.
    intros. apply Radd_comm. trivial.
  Qed.

  Lemma encOfOnePrec_build : forall pk n (gen :  forall i, i < n -> Ring.F)
      (a : vector F n),
    Vmap2 VS.op (Vbuild (fun j (jp : j < n) => enc pk Mzero (gen j jp))) a = 
      Vbuild (fun j (jp : j < n) => enc pk Mzero (op3 (gen j jp) (Vnth a jp))).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vbuild_nth. 
    apply encOfOnePrec.
  Qed.

  Lemma encOfOnePrec_map : forall pk n (b : vector Ring.F n)
      (a : vector F n),
    Vmap2 VS.op (Vmap (fun x => enc pk Mzero x) b) a =
     Vmap (fun x => enc pk Mzero x) (Vmap2 op3 b a).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vnth_map. 
    rewrite Vnth_map2. apply encOfOnePrec.
  Qed.

End MixablePropIns.


Module EncryptionSchemeProp (Message Ciphertext : GroupSig)(Ring: RingSig)
    (Field : FieldSig)(VS : VectorSpaceSig Ciphertext Field)
    (MVS :  VectorSpaceModuleSameGroup Ciphertext Ring Field VS)
    (Enc : EncryptionScheme Message Ciphertext Ring Field VS MVS)
    <: MixableProp Message Ciphertext Ring Field VS MVS Enc.
  Import Enc.
  Import MVS.
  Module AddVSLemmas := VectorSpaceAddationalLemmas Ciphertext Field VS.
  Import AddVSLemmas.

  Module Mat := MatricesFIns Field.
  Module MatG := MatricesG Ciphertext Field VS Mat.

 Definition reenc (pk : PK)(c: G)(r : Ring.F) : G :=
    Ciphertext.Gdot (enc pk Mzero r) c.

  Lemma EncInv : 
  forall (pk : PK)(a : Ring.F),
    enc pk Mzero (Ring.Finv a) = Ginv (enc pk Mzero a).
  Proof.
    intros. replace (Ring.Finv a) with (op3 a (Finv Fone)). rewrite <- encOfOnePrec.
    rewrite <- neg_eq. rewrite VS.mod_id. trivial. apply RopInv.
  Qed. 

  Lemma EncEq : 
  forall (pk : PK)(m1 m2  : M)(r1 r2 : Ring.F),
    m1 = m2 -> r1 = r2 -> enc pk m1 r1 = enc pk m2 r2.
  Proof.
    intros. rewrite H. rewrite H0. auto.
  Qed.

  Definition IsReEnc (pk : PK)(c1 c2 : G)(r : Ring.F) : Prop :=
    c2 = reenc pk c1 r.

  Definition bIsReEnc (pk : PK)(c1 c2 : G)(r : Ring.F) : bool :=
    Gbool_eq c2 (reenc pk c1 r).

  Lemma EncZeroZeroIsOne : forall (pk : PK),
      enc pk Mzero Ring.Fzero = Gone.
  Proof.
    intros. replace Ring.Fzero with (op3 Ring.Fzero Fzero).
    rewrite <- encOfOnePrec. rewrite VS.mod_ann.
    trivial. apply RopRZero.
  Qed.

  (* Given a generator g, public key h, ciphertext c,
  and message m *)
  Definition decryptsTo (pk :PK)(c : G)(m : M) :=
    exists (r : Ring.F), enc pk m r = c.

  Definition decryptsToExt (pk :PK)(c : G)(m : M)(r : Ring.F) :=
    let c' := (enc pk m r) in
    Gbool_eq c' c.

  (* Given a generator g, public key h, ciphertext c,
    c is an encryption of zero or one *)
  Definition decryptsToOneOrZero (pk :PK)(one : M)(c : G) : Prop  :=
    let zero := Mzero in
    decryptsTo pk c zero \/ decryptsTo pk c one.

  (* Given a generator g, public key h, ciphertext c,
    and message m *)
  Definition decryptsTo2 (pk :PK)(c : G)(m : M) :=
    exists (x : SK), keymatch pk x /\ dec x c = m.

  Lemma comHomomorphism : forall l (pk :PK)(m : vector M l)(r : vector Ring.F l),
    enc pk (Vfold_left Mop Mzero m) (Vfold_left Ring.Fadd Ring.Fzero r) =
    Vfold_left Ciphertext.Gdot (enc pk Mzero Ring.Fzero) (Vmap2 (enc pk) m r).
  Proof.
    pose Message.module_abegrp. destruct Ring.module_ring.
    intros. induction l. rewrite (Vector_0_is_nil m). rewrite (Vector_0_is_nil r). 
    cbn. trivial. simpl. rewrite <-  MatG.Vfold_Gdot_const. rewrite <- IHl.
    rewrite homomorphism. apply f_equal2. rewrite Vfold_left_induction.
    intros. rewrite dot_assoc. trivial. intros. apply comm. trivial.
    rewrite Vfold_left_induction. intros. symmetry. apply Radd_assoc.
    intros. apply Radd_comm. trivial.
  Qed.

  Lemma encOfOnePrec_build : forall pk n (gen :  forall i, i < n -> Ring.F)
      (a : vector F n),
    Vmap2 VS.op (Vbuild (fun j (jp : j < n) => enc pk Mzero (gen j jp))) a = 
      Vbuild (fun j (jp : j < n) => enc pk Mzero (op3 (gen j jp) (Vnth a jp))).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vbuild_nth. 
    apply encOfOnePrec.
  Qed.

  Lemma encOfOnePrec_map : forall pk n (b : vector Ring.F n)
      (a : vector F n),
    Vmap2 VS.op (Vmap (fun x => enc pk Mzero x) b) a =
     Vmap (fun x => enc pk Mzero x) (Vmap2 op3 b a).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vnth_map. 
    rewrite Vnth_map2. apply encOfOnePrec.
  Qed.

  Lemma foldZero : forall l (pk :PK)(r : vector Ring.F l),
    Vfold_left Ciphertext.Gdot Gone (Vmap [eta enc pk Mzero] r) =
    enc pk Mzero (Vfold_left Ring.Fadd Ring.Fzero r).
  Proof.
    pose Message.module_abegrp. pose Ring.module_ring.
    intros. induction l. rewrite (Vector_0_is_nil r0). cbn. trivial. rewrite encZero.
    trivial. rewrite (VSn_eq r0). simpl.  rewrite <-  MatG.Vfold_Gdot_const. 
    rewrite IHl. rewrite homomorphism. rewrite one_right. apply f_equal.
    simpl. rewrite Vfold_left_const; destruct r; intros. rewrite Radd_assoc.
    trivial. rewrite Radd_comm. trivial. rewrite Radd_comm. trivial.
  Qed. 

  Lemma comHomomorphism_build : forall n (pk :PK)(gen1 : forall i, i < n -> M)
      (gen2 :  forall i, i < n -> Ring.F),
    enc pk (Vfold_left Mop Mzero (Vbuild (fun j (jp : j < n) => gen1 j jp)))
       (Vfold_left Ring.Fadd Ring.Fzero (Vbuild (fun j (jp : j < n) => gen2 j jp))) =
    Vfold_left Ciphertext.Gdot Ciphertext.Gone (Vbuild (fun j (jp : j < n) => 
     enc pk (gen1 j jp) (gen2 j jp))).
  Proof.
    pose Message.module_abegrp. destruct Ring.module_ring.
    intros. induction n. do 3 rewrite Vbuild_0. cbn. apply encZero. 
    rewrite (VSn_eq (Vbuild (fun (j : nat) (jp : j < S n) => 
      enc pk (gen1 j jp) (gen2 j jp)))). rewrite MatG.Vfold_left_Vcons.
    rewrite Vbuild_tail. rewrite <- IHn. rewrite Vbuild_head.
    rewrite homomorphism. apply f_equal2.
    + rewrite Vfold_left_induction; intros. rewrite dot_assoc. trivial. apply comm.
    rewrite Vbuild_head. rewrite Vbuild_tail. trivial.
    + rewrite Vfold_left_induction. intros. symmetry. apply Radd_assoc.
    intros. apply Radd_comm. rewrite Vbuild_head. rewrite Vbuild_tail. trivial.
  Qed.

  Lemma comHomomorphism_map : forall n (pk :PK)(a : vector Ring.F n),
    enc pk Mzero
       (Vfold_left Ring.Fadd Ring.Fzero a) =
    Vfold_left Ciphertext.Gdot Ciphertext.Gone (Vmap (fun x => enc pk Mzero x) a).
  Proof.
    pose Message.module_abegrp. destruct Ring.module_ring.
    intros. induction n. rewrite (Vector_0_is_nil a0). cbn. apply encZero.  
    rewrite (VSn_eq a0). simpl. rewrite <- MatG.Vfold_Gdot_const. rewrite <- IHn.
    rewrite homomorphism. rewrite one_right. rewrite <- Vfold_left_induction; intros.
    rewrite Vfold_left_const; intros. rewrite Radd_assoc. trivial.
    apply Radd_comm. rewrite Radd_comm. rewrite <- Vfold_left_induction; intros.
    trivial. rewrite Radd_assoc. trivial. apply Radd_comm. rewrite Radd_assoc. 
    trivial. apply Radd_comm. 
  Qed.


End EncryptionSchemeProp. 


Module BasicElGamal (Group : GroupSig)(Field : FieldSig)(VS : VectorSpaceSig Group Field)
      (DualGroup : DualGroupSig Group)(DVS : DualVectorSpaceSig Group DualGroup Field VS)
      (MVS : VectorSpaceModuleSameGroupIns DualGroup Field DVS) 
      <: EncryptionSchemePlus Group DualGroup Field Field DVS VS MVS.
    Module AddVSLemmas := VectorSpaceAddationalLemmas Group Field VS.
    Import AddVSLemmas.
    Module AddDVSLemmas := VectorSpaceAddationalLemmas DualGroup Field DVS.

    Import MVS.
    Import Field.
    
    Definition KGR := prod Group.G F.           (* randomness for keygen *)
    Definition PK := DualGroup.G.                  (* public key space *)
    Definition SK := F.                  (* secret key space *)
    Definition M := Group.G.                   (* message space    *)
    Definition Mop := Group.Gdot.  (* message space is an ablelian group *)
    Definition Mzero := Group.Gone.
    Definition Mone := Group.Ggen.
    Definition Minv := Group.Ginv.
    Definition Mbool_eq := Group.Gbool_eq.

    Definition keygen (kgr : KGR) : (PK*SK) := 
      ((kgr.1,VS.op kgr.1 kgr.2),kgr.2). 

    Definition keygenMix (kgr : KGR) : (PK) :=
      (keygen kgr).1.

    Definition enc (pk : PK)(m : Group.G)(r : F) : G :=
      (VS.op pk.1 r, Group.Gdot (VS.op pk.2 r) m).

    Definition dec (sk : F)(C : G) : M :=
      Group.Gdot C.2 (Group.Ginv (VS.op C.1 sk)).

    Definition keymatch (pk : PK)(sk : SK) : bool :=
      Group.Gbool_eq (VS.op pk.1 sk) pk.2.
     
    Definition M_abgrp := Group.module_abegrp.

    Lemma correct : forall (kgr : KGR)(m : M)(r : F),
                let (pk,sk) := keygen kgr in
                dec sk (enc pk m r) = m.
    Proof.
      pose M_abgrp. intros. cbn. 
      unfold dec, enc. simpl. rewrite comm.
      rewrite dot_assoc. pose VS.mod_dist_Fmul. do 2 rewrite <- e.
      replace (Fmul kgr.2 r) with (Fmul r kgr.2). rewrite <- inv_left.
      rewrite one_left. trivial. field; auto.
    Qed.

    Lemma homomorphism : forall (pk : PK)(m m' : M)(r r' : F),
                Gdot (enc pk m' r')(enc pk m r) = 
                  enc pk (Mop m m') (Fadd r r').
    Proof.
      pose M_abgrp. intros. simpl. unfold Gdot, enc. simpl.
      rewrite VS.mod_dist_Fadd. apply injective_projections.
      simpl. rewrite comm. trivial. simpl. rewrite comm. do 2 rewrite dot_assoc.
      apply right_cancel. rewrite VS.mod_dist_Fadd. do 2 rewrite <- dot_assoc. 
      apply left_cancel. apply comm.
    Qed.

    Lemma encOfOnePrec : forall (pk : PK)(a b : F),
          (DVS.op (enc pk Mzero a) b) = enc pk Mzero (Fmul a b).
    Proof.
      pose Group.module_abegrp. destruct a, abegrp_grp, grp_mon. 
      intros. unfold enc. unfold DVS.op. apply injective_projections.
      simpl. symmetry. apply mod_dist_FMul2.
      simpl. do 2 rewrite one_right. symmetry. apply mod_dist_FMul2.
    Qed.

    Lemma encDis : forall (pk : PK)(g : M)(a : F)(b b' : F),
          DVS.op (enc pk (VS.op g b) a) b' = 
            enc pk (VS.op g (b*b')) (op3 a b').
    Proof.
      intros. unfold enc, op3, op. simpl. 
      rewrite VS.mod_dist_Gdot. do 3 rewrite <- mod_dist_FMul2. trivial.
    Qed.

    Lemma encZero : forall (pk : PK),
      enc pk Mzero Fzero = Gone.
    Proof.
      intros. replace Mzero with (VS.op Mzero 0).
      replace 0 with (0*0). rewrite <- encDis.
       rewrite mod_ann. trivial.  
      field; auto. rewrite VS.mod_ann. trivial.
    Qed.

    Lemma invert : forall  (pk : PK)(g : M)(a : F),
      DualGroup.Ginv (enc pk g a) = enc pk (Group.Ginv g) (-a).
    Proof.
      intros. unfold Ginv, enc. simpl. apply injective_projections;
      simpl. rewrite neg_eq. trivial. rewrite <- neg_eq.
      symmetry. pose Group.module_abegrp. apply inv_dist.
    Qed.

End BasicElGamal.

Module Type Nat.
  Parameter N : nat.
End Nat.



Module ExtendedElGamal (Hack : Nat)(Group : GroupSig)(Field: FieldSig)
    (VS : VectorSpaceSig Group Field)(NthGroupM : GroupNthSig Group Hack)
    (DualGroup : DualGroupSig Group)(DVS : DualVectorSpaceSig Group DualGroup Field VS)
    (NthGroup : GroupNthSig DualGroup Hack)(NthRing : NthRingSig Hack Field) 
    (NthVS : NthVectorSpaceSig Hack DualGroup Field NthGroup DVS)
    (NthMVS : NthVectorSpaceSig Hack Group Field NthGroupM VS)
    (MVS : VectorSpaceModuleSameGroupNthSig Hack DualGroup Field Field 
    DVS NthGroup NthRing NthVS)
    <: EncryptionSchemePlus NthGroupM NthGroup NthRing Field NthVS NthMVS MVS.
  Import Hack.
  Module Mo := MatricesFIns Field.
  Module MoM := MatricesG Group Field VS Mo.
  Module AddVSLemmas := VectorSpaceAddationalLemmas Group Field VS.
    Import AddVSLemmas.
    Import MVS.
    Import Field.
    
    Definition KGR := prod (MoM.VG (S N))(Mo.VF (S N)). (* randomness for keygen *)
    Definition PK := NthGroup.G.                  (* public key space *)
    Definition SK := Mo.VF (S N).                  (* secret key space *)
    Definition M := NthGroupM.G.                   (* message space    *)
    Definition Mop := NthGroupM.Gdot.  (* message space is an ablelian group *)
    Definition Mzero := NthGroupM.Gone.
    Definition Mone := NthGroupM.Ggen.
    Definition Minv := NthGroupM.Ginv.
    Definition Mbool_eq := NthGroupM.Gbool_eq.

    (* F is the randomness space and G is the message space *)
    Definition keygen (kgr : KGR) : (PK*SK) := 
      (Vmap2 (fun x y => (x, VS.op x y)) kgr.1 kgr.2, kgr.2). 

    Definition keygenMix (kgr : KGR) : (PK) :=
      (keygen kgr).1.

    Definition enc (Pk : PK)(m : M)(r : Mo.VF (S N)) : NthGroup.G :=
      let mr := Vmap2 (fun x y => (x,y)) m r  in
      Vmap2 (fun (pk :DualGroup.G)(mr : (Group.G*F)) => (VS.op pk.1 mr.2, 
          Group.Gdot (VS.op pk.2 mr.2) mr.1)) Pk mr.

    Definition dec (Sk : SK)(C : NthGroup.G) : M :=
      Vmap2 (fun sk c => Group.Gdot c.2 (Group.Ginv (VS.op c.1 sk))) Sk C.

    Definition keymatch (Pk : PK)(Sk : SK) : bool :=
      MoM.VG_eq (Vmap2 (fun pk sk => VS.op pk.1 sk) Pk Sk) 
          (Vmap (fun x => x.1) Pk).

    Definition M_abgrp := NthGroupM.module_abegrp.

    Lemma correct : forall (kgr : KGR)(m : M)(r : Mo.VF (S N)),
                let (pk,sk) := keygen kgr in
                dec sk (enc pk m r) = m.
    Proof.
      pose Group.module_abegrp. intros. simpl. pose Vcons_map2. symmetry in e.
      rewrite e. do 2 rewrite <- VSn_eq.
      unfold dec, enc. apply Veq_nth. intros. do 4 rewrite Vnth_map2. simpl.
      rewrite <- mod_dist_FMul2. rewrite <- VS.mod_dist_Fmul.
      rewrite comm. rewrite dot_assoc. rewrite <- inv_left.
      apply one_left.
    Qed.

    Lemma homomorphism : forall (pk : PK)(m m' : M)(r r' : Mo.VF (S N)),
                NthGroup.Gdot (enc pk m' r')(enc pk m r) = 
                  enc pk (Mop m m') (Mo.VF_add r r').
    Proof.
      pose Group.module_abegrp.
      intros. simpl. apply Veq_nth. intros. do 9 rewrite Vnth_map2.
      simpl. apply injective_projections. simpl. rewrite comm.
      rewrite VS.mod_dist_Fadd. trivial. simpl. rewrite comm. 
      do 2 rewrite dot_assoc. apply right_cancel. rewrite comm.
      rewrite dot_assoc. apply right_cancel. rewrite comm. 
      rewrite VS.mod_dist_Fadd. trivial.
    Qed.

    Lemma encOfOnePrec : forall (pk : PK)(a : Mo.VF (S N))(b : F),
          (NthVS.op (enc pk Mzero a) b) = enc pk Mzero (Mo.VF_scale a b).
    Proof.
      pose Group.module_abegrp.
      intros. apply Veq_nth. intros. rewrite Vnth_map. do 4 rewrite Vnth_map2.
      do 2 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
      rewrite Vnth_map. unfold DVS.op. apply injective_projections_simp.
      symmetry. apply mod_dist_FMul2. rewrite Vnth_const.
      do 2 rewrite one_right. symmetry. apply mod_dist_FMul2.
    Qed.

    Lemma encDis : forall (pk : PK)(g : M)(a : Mo.VF (S N))(b b' : F),
          NthVS.op (enc pk (NthMVS.op g b) a) b' = 
            enc pk (NthMVS.op g (b*b')) (op3 a b').
    Proof.
      intros. unfold enc, op3, NthVS.op. 
      apply Veq_nth. intros. rewrite Vnth_map. do 4 rewrite Vnth_map2. 
      do 2 rewrite Prod_left_replace. do 2 rewrite Prod_right_replace.
       do 3 rewrite Vnth_map. unfold DVS.op. rewrite Prod_left_replace.
      rewrite Prod_right_replace.
       rewrite VS.mod_dist_Gdot. do 3 rewrite <- mod_dist_FMul2. trivial.
    Qed.

    Lemma encZero : forall (pk : PK),
      enc pk Mzero NthRing.Fzero = NthGroup.Gone.
    Proof.
      intros. replace Mzero with (NthMVS.op Mzero 0).
      replace 0 with (0*0). replace NthRing.Fzero with
      (op3 NthRing.Fzero 0). rewrite <- encDis.
       rewrite NthVS.mod_ann. trivial.  rewrite RopRZero. trivial.
      field; auto. rewrite NthMVS.mod_ann. trivial.
    Qed.

End ExtendedElGamal.

Module BasicComScheme (Group : GroupSig)(Ring : RingSig)
  (M : ModuleSig Group Ring)(Mo : MatricesF Ring) .
  Import M.
  Module AddMLemmas := ModuleAddationalLemmas Group Ring M.
  Import AddMLemmas.

  Module MoM := MatricesG Group Ring M Mo.
  Import Mo.
  Import MoM.

  Definition PC (h: G)(h1 : G)(m : F)(r: F) : G :=
    h^r o h1^m.

  Lemma PCExp : forall (g h : G)(m r c : F),
    PC g h m r ^ c = PC g h (m*c) (r*c).
  Proof.
    intros. unfold PC. rewrite mod_dist_Gdot. do 2 rewrite <- mod_dist_FMul2.
    trivial.
  Qed.

  Lemma PCExp2 : forall (g h : G)(m r c : F),
    PC g h m r ^ c = PC g h (c*m) (c*r).
  Proof.
    intros. replace (c * m) with (m * c).
    replace (c*r) with (r*c). apply PCExp. ring; auto. ring; auto.
  Qed.

  Lemma PCMult : forall (g h : G)(m1 m2 r1 r2 : F),
    PC g h m1 r1 o PC g h m2 r2 = PC g h (m1+m2) (r1+r2).
  Proof.
    pose module_abegrp. intros. unfold PC. do 2 rewrite mod_dist_Fadd. 
    do 2 rewrite dot_assoc. apply right_cancel. do 2 rewrite <- dot_assoc. 
    apply left_cancel. apply comm.
  Qed.

  Lemma PCneg : forall (g h : G)(m r : F),
    - PC g h m r = PC g h (Finv m) (Finv r).
  Proof.
    pose module_abegrp.
    intros. unfold PC.  rewrite <- neg_eq. rewrite <- neg_eq.
    remember (g^r) as b. remember (h^m) as c. symmetry. apply inv_dist.
  Qed.

  Lemma PC_m_r_eq : forall h h1 m m' r r',
  m = m' -> r = r' -> PC h h1 m r = PC h h1 m' r'.
  Proof.
    intros. rewrite H. rewrite H0. trivial.
  Qed.

  Lemma PC_up0 : forall(h: G)(h1 : G)(a b c d :F),
  PC h (PC h h1 a b) c d = PC h h1 (a*c) (d+b*c).
  Proof.
        pose module_abegrp.
    intros. unfold PC. rewrite mod_dist_Fadd. rewrite <- dot_assoc.
    apply left_cancel. rewrite mod_dist_Gdot.
    do 2 rewrite <- mod_dist_Fmul. replace (c*b) with (b*c).
    replace (a0*c) with (c*a0). trivial. ring; auto.
    ring; auto. 
  Qed.

  Lemma PC_h1_eq : forall h h1 h1' m r,
    h1 = h1' -> PC h h1 m r = PC h h1' m r.
  Proof.
    intros. rewrite H. trivial.
  Qed.


  Lemma PC_h1_m_r_eq : forall h h1 h1' m m' r r',
    h1 = h1' -> m = m' -> r = r' -> 
      PC h h1 m r = PC h h1' m' r'.
  Proof.
    intros. rewrite H. rewrite H0. rewrite H1. trivial.
  Qed.

  Lemma PC_zero : forall h h1,
      PC h h1 0 0  = Gone.
  Proof.
    pose module_abegrp.
    intros. unfold PC. do 2 rewrite mod_ann. apply one_right.
  Qed.

  Definition comPC (N : nat)(h h1 :G)(m : VF N)(r : VF N) : VG N :=
    Vmap2 (PC h h1) m r.

  Lemma comPCfromOp : forall (h h1 :G)(x: F),
    h1 = op h x ->
    forall (N : nat)(m : VF N)(r : VF N),
  comPC h h1 m r = Vmap [eta op h] (VF_add r (VF_scale m x)).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
    rewrite Vnth_map. unfold PC, FSemiRingT.Aplus. rewrite mod_dist_Fadd.
    rewrite mod_dist_Fmul. rewrite <- H. trivial.
  Qed.

  Lemma  comPCVcons : forall (n : nat)(h hs : G)
      (m0 : F)(r0 : F)(m1 : VF n)(r1 : VF n),
    (Vcons (PC h hs m0 r0) (comPC h hs m1 r1)) =
      comPC h hs (Vcons m0 m1) (Vcons r0 r1).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. trivial.
  Qed.

  Lemma comPCVcast : forall (n n' : nat)(h hs : G)
      (m : VF n)(r : VF n)(H : n = n'),
      Vcast (comPC h hs m r) H = 
        comPC h hs (Vcast m H) (Vcast r H).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_cast.
    do 2 rewrite Vnth_map2. do 2 rewrite Vnth_cast. trivial.
  Qed.

  Lemma comPCVapp : forall (n m : nat)(h hs : G)
     (m0 : VF n)(r0 : VF n)(m1 : VF m)(r1 : VF m),
  Vapp (comPC h hs m0 r0) (comPC h hs m1 r1) =
    comPC h hs (Vapp m0 m1) (Vapp r0 r1).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. 
    do 3 rewrite Vnth_app. destruct (le_gt_dec n i).
    rewrite Vnth_map2. trivial. rewrite Vnth_map2. trivial.
  Qed.

  Lemma comPCDis : forall (N : nat)(h h1 :G)
      (m : VF N)(r r' : VF N),
    Vmap2 op (comPC h h1 m r) r' =
      comPC h h1 (Vmap2 Fmul m r') (Vmap2 Fmul r r').
    Proof.
      intros. apply Veq_nth. intros. do 5 rewrite Vnth_map2.
      unfold PC. rewrite mod_dist_Gdot. do 2 rewrite mod_dist_FMul2.
      trivial.
    Qed.

  Lemma PCMultExt : forall (n : nat)(g h : G)(m r : vector F n),
    PC g h (Vfold_left Fadd Fzero m) (Vfold_left Fadd Fzero r) 
      = Vfold_left Gdot Gone (comPC g h m r).
  Proof.
    pose module_abegrp. intros. unfold PC. induction n. 
    rewrite (Vector_0_is_nil r). rewrite (Vector_0_is_nil m). cbn.
    do 2 rewrite mod_ann. rewrite one_right. trivial. symmetry.
    rewrite (VSn_eq m). rewrite (VSn_eq r). unfold comPC. rewrite Vcons_map2.
    pose VG_prod_Vcons. unfold VG_prod in e. rewrite e.
    unfold comPC in IHn. rewrite <- IHn.  unfold PC.
    pose VF_sum_vcons. unfold VF_sum in e0. do 2 rewrite e0. do 2 rewrite mod_dist_Fadd.
    do 2 rewrite <- dot_assoc. rewrite left_cancel.  do 2 rewrite dot_assoc. 
    rewrite right_cancel. apply comm. 
  Qed. 

  Definition relComPC (h :G)(h1 : G)(c : G) (*Stament*)
                (m1 m2 : F)(r1 r2 : F) :=  (*Witness *)
    m1 <> m2 /\
    c = (PC h h1 m1 r1) /\ c = (PC h h1 m2 r2).

    Lemma trapdoorPC : forall (h h1 : G)(x : F),
    h1 = h ^ x ->
    forall (m r : F),
    PC h h1 m r =
    PC h h1 0 (r + x * m).
  Proof.
    pose module_abegrp.
    intros. unfold PC. rewrite H. rewrite mod_dist_Fadd. rewrite <- dot_assoc.
    apply f_equal. rewrite mod_ann. rewrite one_right. rewrite mod_dist_FMul2.
    trivial.
  Qed. 

End BasicComScheme.

Module BasicComSchemeMixable (Group : GroupSig)
    (Field : FieldSig)(VS : VectorSpaceSig Group Field)
    (Message : GroupFromRing Field) 
    (MVS :  VectorSpaceModuleSameGroupIns Group Field VS) 
      <: Mixable Message Group Field Field VS MVS.

  Import Group.
  Import Field.

  Import MVS.

  Module Mo := MatricesFIns Field.

  Module PC := BasicComScheme Group Field VS Mo.
  Import PC.

  Definition KGR := (prod G F).               (* randomness for keygen *)
  Definition PK := (prod G G).                  (* public key space *)

  Definition M := Message.G.             (* message space    *)
  Definition Mop := Message.Gdot.  (* message space is an ablelian group *)
  Definition Mzero := Message.Gone.
  Definition Mone := Message.Ggen.
  Definition Minv := Message.Ginv.
  Definition Mbool_eq := Message.Gbool_eq.

  Definition keygenMix kgr := (kgr.1, kgr.1^kgr.2).    (* key generation   *)
  Definition enc pk m r := PC pk.1 pk.2 m r. (* or commit *)

  Definition M_abgrp := Message.module_abegrp.

  Lemma homomorphism : forall (pk : PK)(m m' : M)(r r' : F),
                Group.Gdot (enc pk m' r')(enc pk m r) = 
                  enc pk (Mop m m') (Fadd r r'). 
    Proof.
      pose module_abegrp.
      intros. unfold enc. rewrite <- PCMult. apply comm.
    Qed.

  Lemma encOfOnePrec : forall (pk : PK)(a : F)(b :F),
          VS.op (enc pk Mzero a) b = enc pk Mzero (op3 a b).
    Proof.
      pose vs_field.
      intros. unfold enc. rewrite PCExp2. apply PC_m_r_eq.
      unfold Mzero, Message.Gone. field; auto.
      unfold op3. field; auto.
    Qed.

  
End BasicComSchemeMixable.


Module ExtendComScheme (Group : GroupSig)(Ring : RingSig)
  (M : ModuleSig Group Ring)(Mo : MatricesF Ring).
  Import M.
  
  Module MoM := MatricesG Group Ring M Mo.
  Import Mo.
  Import MoM.

  Definition EPC  (N :nat)(h :G)(hs : VG N)(m : VF N)(r : F) : G :=
    h^r o VG_prod (VG_Pexp hs m).

  Lemma EPC_m_eq : forall N h (hs : VG N) m m' r,
    m = m' -> EPC h hs m r = EPC h hs m' r.
  Proof.
    intros. rewrite H. trivial.
  Qed.

  Lemma EPC_m_r_eq : forall N h (hs : VG N) m m' r r',
    m = m' -> r = r' ->
         EPC h hs m r = EPC h hs m' r'.
  Proof.
    intros. rewrite H. rewrite H0. trivial.
  Qed.

  Lemma EPC_vcons : forall (N :nat)(h : G)(hs : VG (1+N))(r w c d : F)(r' w' : VF N),
    EPC h hs (Vcons (r + w * c) (VF_add r' (VF_scale w' c))) d =
        EPC h hs (VF_add (Vapp [r] r') (VF_scale (Vapp [w] w') c)) d.
  Proof.
    intros. apply EPC_m_eq. apply VF_scale_vcons.
  Qed.

  Lemma EPC_vcons2 : forall (N :nat)(h : G)(hs : VG (1+N))(r w c d : F)(r' w' : VF N),
    EPC h hs (Vcons ((r + w) * c) (VF_scale (VF_add r' w') c)) d =
        EPC h hs (VF_scale (VF_add (Vapp [r] r') (Vapp [w] w')) c) d.
  Proof.
    intros. apply EPC_m_eq. apply VF_scale_vcons2.
  Qed.

  Theorem EPCExp :
     forall N,
     forall(h : G)(hs : VG N),
     forall v : VF N, 
     forall a r : F,
     EPC h hs (VF_scale v a) (r*a) = (EPC h hs v r) ^ a.
  Proof.
    pose module_abegrp. intros. unfold VF_scale. unfold EPC.
    rewrite mod_dist_Gdot. rewrite mod_dist_FMul2. apply left_cancel.
    unfold VG_Pexp. unfold VG_prod. simpl. remember (Vfold_left Gdot Gone
    (Vmap2 op hs v) ^ a0) as b. replace (Gone) with (Gone ^ a0).
    rewrite Heqb. rewrite VG_mod_dist. apply Vfold_left_eq.
    apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2. rewrite Vnth_map.
    replace (Vnth v ip * a0) with (a0 * Vnth v ip). rewrite mod_dist_Fmul.
    trivial. ring; auto. apply mod_mone.
  Qed.

  Lemma EPCMult :  forall N, forall (g : G)(hs : VG N),
                  forall (m1 m2 : VF N)(r1 r2 : F), 
    EPC g hs m1 r1 o EPC g hs m2 r2 = EPC g hs (VF_add m1 m2) (r1+r2).
  Proof.
    pose module_abegrp. 
    intros. unfold EPC. rewrite <- dot_assoc. rewrite mod_dist_Fadd.
    symmetry. rewrite <- dot_assoc. apply left_cancel. symmetry.
    rewrite comm. rewrite <- dot_assoc. apply left_cancel.
    apply VF_add_product.
  Qed.

  Lemma EPCneg : forall N, forall (g : G)(hs : VG N)(m : VF N)(r : F),
    - EPC g hs m r = EPC g hs (VF_neg m) (Finv r).
  Proof.
    pose module_abegrp.
    intros. unfold EPC. rewrite <- neg_eq. rewrite VF_neg_inv.
    remember (g^r) as b. remember (VG_prod (VG_Pexp hs m)) as c. 
    symmetry. apply inv_dist.
  Qed.

  Lemma EPCfall : forall N, forall (g : G)(hs : VG N)(r : F),
    EPC g hs (VF_zero N) r = g^r.
  Proof.
    pose module_abegrp.
    intros. unfold EPC. rewrite VG_Zero_exp. rewrite VG_Zero_prod.
    rewrite one_right. trivial.
  Qed. 

  Definition comEPC (N N' : nat)(h :G)(hs : (VG N))
      (m : vector (VF N) N')(r : VF N') : VG N' :=
    Vmap2 (EPC h hs) m r.

  Definition comEPCvec (N N' : nat)(h :G)(hs : (VG N))
      (m : VF (N*N'))(r : VF N') : VG N' :=
    comEPC h hs (VecToMat N N' m) r.

  Lemma comEPC_build : forall N N' (h :G)(hs : (VG N))(m : vector (VF N) N')
        (r : VF N'),
    comEPC h hs m r  = 
      Vbuild (fun (j : nat) (jp : j < N') => EPC h hs (Vnth m jp) (Vnth r jp)).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vbuild_nth. rewrite Vnth_map2. trivial.
  Qed.

  Lemma comEPCrev : forall (N N' : nat)(h :G)(hs : (VG N))
      (m : vector (VF N) N')(r : VF N')(c : VG N'),
    c = comEPC h hs m r -> rev c = comEPC h hs (rev m) (rev r).
  Proof.  
    intros. rewrite H. apply Veq_nth. intros. rewrite Vbuild_nth. 
    do 2 rewrite Vnth_map2. do 2 rewrite Vbuild_nth. trivial.
  Qed.

  Lemma  comEPCVcons : forall (n m : nat)(h : G)(hs : VG n)
      (m0 : VF n)(r0 : F)(m1 : vector (VF n) m)(r1 : VF m),
    (Vcons (EPC h hs m0 r0) (comEPC h hs m1 r1)) =
      comEPC h hs (Vcons m0 m1) (Vcons r0 r1).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. trivial.
  Qed.

  Lemma  comEPCVadd : forall (n m : nat)(h : G)(hs : VG n)
      (m0 : VF n)(r0 : F)(m1 : vector (VF n) m)(r1 : VF m),
    (Vadd (comEPC h hs m1 r1) (EPC h hs m0 r0)) =
      comEPC h hs (Vadd m1 m0) (Vadd r1 r0).
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_add.
    destruct (Nat.eq_dec i m). trivial. rewrite Vnth_map2. trivial.
  Qed.

  Lemma comEPCDis : forall (N N' : nat)(h :G)(hs : (VG N))
      (m : vector (VF N) N')(r r' : VF N'),
    Vmap2 op (comEPC h hs m r) r' =
      comEPC h hs 
        (Vmap2 (VF_scale (n:=N)) m r') (Vmap2 Fmul r r').
    Proof.
      intros. apply Veq_nth. intros. do 5 rewrite Vnth_map2.
      unfold EPC. rewrite mod_dist_Gdot. rewrite mod_dist_FMul2.
      rewrite VG_prod_VG_Pexp_scale. trivial.
    Qed.

  Lemma comEPCDis2 : forall (N N' : nat)(h :G)(hs : (VG N))
      (m : vector (VF N) N')(r : VF N') r',
  VG_Sexp (comEPC h hs m r) r' = comEPC h hs 
  (Vmap (fun a => VF_scale a r') m) (VF_scale r r').
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map. do 2 rewrite Vnth_map2.
    do 2 rewrite Vnth_map. rewrite EPCExp. trivial.
  Qed.

  Lemma comEPCmult : forall  (N N' : nat)(h :G)(hs : (VG N))
        (m m' : vector (VF N) N')(r r' : VF N'),
    VG_mult (comEPC h hs m r) (comEPC h hs m' r') = 
    comEPC h hs (Vmap2 (@VF_add N) m m') (VF_add r r').
  Proof.
    intros. apply Veq_nth. intros. do 6 rewrite Vnth_map2. apply EPCMult.
  Qed.

  Lemma EPCMultExt : forall (n n' : nat)(g : G)(hs : VG n)
      (m : vector (VF n) n' )(r : vector F n'),
    EPC g hs (Vfold_left (VF_add (n:=n)) (VF_zero n) m) 
      (Vfold_left Fadd Fzero r) 
      = Vfold_left Gdot Gone (comEPC g hs m r).
  Proof.
    pose module_abegrp. intros. unfold EPC. induction n'. 
    rewrite (Vector_0_is_nil r). rewrite (Vector_0_is_nil m). cbn.
    rewrite mod_ann. rewrite VG_Zero_exp.  rewrite VG_Zero_prod.
    rewrite one_right. trivial. symmetry.
    rewrite (VSn_eq m). rewrite (VSn_eq r). unfold comEPC. rewrite Vcons_map2.
    pose VG_prod_Vcons. unfold VG_prod in e. rewrite e.
    unfold comEPC in IHn'. rewrite <- IHn'.  unfold EPC.
    pose VF_sum_vcons. unfold VF_sum in e0. rewrite e0. rewrite mod_dist_Fadd.
    do 2 rewrite <- dot_assoc. rewrite left_cancel.  rewrite dot_assoc. 
    rewrite comm. symmetry. rewrite comm. rewrite dot_assoc. 
    rewrite right_cancel. rewrite Vfold_left_Vcons_VFadd.
    rewrite VF_add_product. trivial.
  Qed. 

  Lemma comEPCDis_build : forall (N N' : nat)(h :G)(hs : (VG N))
      (r : VF N')(gen1 : forall i, i < N' -> VF N)(gen2: forall i, i < N' -> F),
    Vmap2 op (Vbuild (fun j (jp : j < N') => EPC h hs (gen1 j jp) (gen2 j jp))) r =
      Vbuild (fun j (jp : j < N') => EPC h hs 
        (VF_scale (gen1 j jp) (Vnth r jp)) (Fmul (gen2 j jp) (Vnth r jp))).
    Proof.
      intros. apply Veq_nth. intros. rewrite Vnth_map2. do 2 rewrite Vbuild_nth.
      unfold EPC. rewrite mod_dist_Gdot. rewrite mod_dist_FMul2.
      rewrite VG_prod_VG_Pexp_scale. trivial.
    Qed.

  Lemma EPCMultExt_build : forall (n n' : nat)(g : G)(hs : VG n)
      (gen1 : forall i, i < n' -> VF n)(gen2: forall i, i < n' -> F),
    EPC g hs 
      (Vfold_left (VF_add (n:=n)) (VF_zero n) (Vbuild (fun j (jp : j < n') => gen1 j jp))) 
      (Vfold_left Fadd Fzero (Vbuild (fun j (jp : j < n') => gen2 j jp))) 
      = Vfold_left Gdot Gone (Vbuild (fun j (jp : j < n') =>
         EPC g hs (gen1 j jp) (gen2 j jp))).
  Proof.
    pose module_abegrp. intros. unfold EPC. induction n'. 
    do 3 rewrite Vbuild_0. cbn. rewrite mod_ann. rewrite VG_Zero_exp.  
    rewrite VG_Zero_prod. rewrite one_right. trivial. symmetry.
    rewrite (VSn_eq (Vbuild (fun (j : nat) (jp : j < S n') =>
      g ^ gen2 j jp o VG_prod (VG_Pexp hs (gen1 j jp))))). 
    pose VG_prod_Vcons. unfold VG_prod in e. rewrite e. rewrite Vbuild_tail.
    rewrite <- IHn'. rewrite Vbuild_head. pose (commHack (A:=G)(dot:=Gdot)).
    unfold abegop in e0. rewrite e0. apply f_equal2.
    + rewrite <- Vbuild_tail. rewrite <- mod_dist_Fadd.
    pose VF_sum_vcons. unfold VF_sum in e1. rewrite <- e1. rewrite <- Vbuild_head.
    rewrite <- VSn_eq. trivial.
    + rewrite VF_add_product. rewrite VF_comm. rewrite <- Vfold_left_Vcons_VFadd.
    apply f_equal. apply f_equal. rewrite <- Vbuild_head. rewrite <- Vbuild_tail.
    rewrite <- VSn_eq. trivial.
  Qed. 

  Lemma comEPCApp : forall (N N' N'' : nat)(h :G)(hs : (VG N))
      (m : vector (VF N) N')(r : VF N')(m' : vector (VF N) N'')(r' : VF N''),
    comEPC h hs (Vapp m m') (Vapp r r') = 
    Vapp (comEPC h hs m r) (comEPC h hs m' r').
  Proof.
    intros. apply Veq_nth. intros. rewrite Vnth_map2. do 3 rewrite Vnth_app.
    destruct (le_gt_dec N' i); rewrite Vnth_map2; trivial.
  Qed.

  (*the definiation of a commitment commitment to a matrix *) 
  Definition com (N : nat)(h :G)(hs : (VG N))(m : MF N)(r : VF N) : VG N :=
    comEPC h hs m r.

  Lemma EPC_add : forall (N : nat)(h : G)(hs: VG N),
  forall (m m' : VF N)(r r' : F),
    EPC h hs (VF_add m m') (r + r') =
    (EPC h hs m r) o (EPC h hs m' r').
  Proof.
    pose module_abegrp.
    intros. unfold EPC. assert (forall a b c d, 
      (a o b) o (c o d) = (a o c) o (b o d)).
    intros.  rewrite dot_assoc. 
    replace ((a0 o b) o c) with (a0 o (b o c)) by apply dot_assoc. 
    replace (b o c) with (c o b) by apply comm.
    do 2 rewrite dot_assoc. trivial. 
    rewrite H. rewrite mod_dist_Fadd.
    rewrite VF_add_product. rewrite VF_comm. trivial.
  Qed.

  Definition relComEPC (N : nat)(h :G)(hs : VG N)(c : G) (*Stament*)
                (m1 m2 : VF N)(r1 r2 : F) :=  (*Witness *)
    m1 <> m2 /\
    c = (EPC h hs m1 r1) /\ c = (EPC h hs m2 r2).

  Lemma trapdoorEPC : forall (N : nat)(h : G)(hs : VG N)(x : VF N),
    hs = Vmap (op h) x ->
    forall (m : VF N)(r : F),
    EPC h hs m r =
    EPC h hs (VF_zero N) (r + (VF_inProd x m)).
  Proof.
    pose module_abegrp.
    intros. unfold EPC. rewrite H. rewrite mod_dist_Fadd. rewrite <- dot_assoc.
    apply f_equal. rewrite VG_Zero_exp. rewrite VG_Zero_prod. rewrite one_right.
    rewrite VG_Pexp_inProd. rewrite <- VF_sum_op. rewrite InProd_Sum. trivial.
  Qed. 

End ExtendComScheme.


Module ExtendComSchemeMixable (Group : GroupSig)
    (Field : FieldSig)(VS : VectorSpaceSig Group Field)
    (Hack : Nat)(NthRing : NthRingSig Hack Field) 
    (Message : GroupFromRing NthRing) 
    (MVS :  VectorSpaceModuleSameGroupIns Group Field VS) 
      <: Mixable Message Group Field Field VS MVS.

  Import VS.
  
  Module Mo := MatricesFIns Field.
  Module MoM := MatricesG Group Field VS Mo.
  Import Mo.
  Import MoM.

  Import Group.
  Import Field.

  Import MVS.

  Module EPC := ExtendComScheme Group Field VS Mo.
  Import EPC.

  Import Hack.

  Definition KGR := (prod G (VF (S N))).               (* randomness for keygen *)
  Definition PK := (prod G (VG (S N))).                  (* public key space *)

  Definition M := Message.G.             (* message space    *)
  Definition Mop := Message.Gdot.  (* message space is an ablelian group *)
  Definition Mzero := Message.Gone.
  Definition Mone := Message.Ggen.
  Definition Minv := Message.Ginv.
  Definition Mbool_eq := Message.Gbool_eq.

  Definition keygenMix (kgr : KGR) : PK := 
     (kgr.1, Vmap (fun x => kgr.1^x) kgr.2).    (* key generation   *)
  Definition enc (pk : PK) (m : M) (r : F) := 
    EPC pk.1 pk.2 m r. (* or commit *)

  Definition M_abgrp := Message.module_abegrp.

  Lemma homomorphism : forall (pk : PK)(m m' : M)(r r' : F),
                Group.Gdot (enc pk m' r')(enc pk m r) = 
                  enc pk (Mop m m') (Fadd r r'). 
    Proof.
      pose module_abegrp.
      intros. unfold enc. rewrite <- EPCMult. apply comm.
    Qed.

  Lemma encOfOnePrec : forall (pk : PK)(a : F)(b :F),
          VS.op (enc pk Mzero a) b = enc pk Mzero (op3 a b).
    Proof.
      pose vs_field.
      intros. unfold enc. rewrite <- EPCExp. apply EPC_m_r_eq.
      apply Veq_nth. intros. rewrite Vnth_map. rewrite Vnth_const. 
      field; auto. unfold op3. field; auto.
    Qed.

  
End ExtendComSchemeMixable.


Module HardProblems (Group : GroupSig)(Ring : RingSig)(M : ModuleSig Group Ring).
   Import M.

  Definition dLog (s :G*G)(w : F) := 
    let g     := s.1 in
    let gtox  := s.2 in 
    Gbool_eq gtox (g^w).

  
End HardProblems.
