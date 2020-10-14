From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_two191:
  prime  2169465729771251->
  prime  1904572046176155084118090201.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1904572046176155084118090201
      877899115916
      ((2169465729771251,1)::nil)
      1904572046176155084117754061
      92236816
      0
      9604)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
