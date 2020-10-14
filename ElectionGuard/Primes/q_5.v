From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_one5:
  prime  1833074268135551596059806535438812872591->
  prime  22618303394524571143790659120906899035736103.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      22618303394524571143790659120906899035736103
      12339
      ((1833074268135551596059806535438812872591,1)::nil)
      0
      78608
      17
      289)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
