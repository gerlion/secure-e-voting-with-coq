From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_two188:
  prime  43627452910095569517664827243948775340537489->
  prime  3671860946725283512884739339215946595430128633857.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      3671860946725283512884739339215946595430128633857
      84164
      ((43627452910095569517664827243948775340537489,1)::nil)
      16900
      0
      26
      676)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
