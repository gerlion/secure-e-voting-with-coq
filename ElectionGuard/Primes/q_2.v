From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_one2:
  prime  851192406808771314425127174946283943890399979859867192819->
  prime  19598705166771959514638553203145974516359947008250982025673031.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      19598705166771959514638553203145974516359947008250982025673031
      23025
      ((851192406808771314425127174946283943890399979859867192819,1)::nil)
      0
      163840
      96
      1024)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
