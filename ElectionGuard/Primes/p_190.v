From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_two190:
  prime  1904572046176155084118090201->
  prime  2510105968821263210445433849931953.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2510105968821263210445433849931953
      1317937
      ((1904572046176155084118090201,1)::nil)
      0
      99144
      18
      324)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
