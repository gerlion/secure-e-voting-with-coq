From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_two192:
  prime  3379229979443->
  prime  2169465729771251.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2169465729771251
      642
      ((3379229979443,1)::nil)
      2169465729677171
      9834496
      0
      3136)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
