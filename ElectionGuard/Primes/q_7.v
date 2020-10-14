From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_one7:
  prime  5484259094177836171154485091->
  prime  3267768359970392679605575209221863.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      3267768359970392679605575209221863
      595845
      ((5484259094177836171154485091,1)::nil)
      3267768359970392679605575196172815
      18161012554
      879
      85849)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
