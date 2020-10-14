From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_one6:
  prime  3267768359970392679605575209221863->
  prime  1833074268135551596059806535438812872591.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1833074268135551596059806535438812872591
      560956
      ((3267768359970392679605575209221863,1)::nil)
      0
      192
      4
      16)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
