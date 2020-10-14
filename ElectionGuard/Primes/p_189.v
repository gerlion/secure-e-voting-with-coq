From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_two189:
  prime  2510105968821263210445433849931953->
  prime  43627452910095569517664827243948775340537489.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      43627452910095569517664827243948775340537489
      17380721552
      ((2510105968821263210445433849931953,1)::nil)
      100
      0
      20
      100)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
