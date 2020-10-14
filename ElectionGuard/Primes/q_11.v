From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma jack_one11 : prime 2056984558309.
Proof.
 apply (Pocklington_refl
         (Pock_certif 2056984558309 2 ((24571, 1)::(2,2)::nil) 92778)
        ((Proof_certif 24571 prime24571) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

