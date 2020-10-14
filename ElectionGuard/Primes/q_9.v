From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_one9:
  prime  224061157912888249->
  prime  276939591147492220081.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      276939591147492220081
      1236
      ((224061157912888249,1)::nil)
      0
      3584
      8
      64)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
