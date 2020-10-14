From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_one10:
  prime  2056984558309->
  prime  224061157912888249.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      224061157912888249
      108927
      ((2056984558309,1)::nil)
      0
      221184
      48
      576)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
