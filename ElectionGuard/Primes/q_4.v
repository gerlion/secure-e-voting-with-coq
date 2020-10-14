From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_one4:
  prime  22618303394524571143790659120906899035736103->
  prime  1599985727084156606062269125791503366494591139841169917.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1599985727084156606062269125791503366494591139841169917
      70738538571
      ((22618303394524571143790659120906899035736103,1)::nil)
      0
      199794688
      1392
      53824)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
