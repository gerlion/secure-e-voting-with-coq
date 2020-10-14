From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_one8:
  prime  276939591147492220081->
  prime  5484259094177836171154485091.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      5484259094177836171154485091
      19803088
      ((276939591147492220081,1)::nil)
      5484259094177836171154341731
      25690112
      64
      4096)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
