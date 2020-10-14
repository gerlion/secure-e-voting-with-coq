From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma jack_two193 : prime 3379229979443.
Proof.
 apply (Pocklington_refl
         (Pock_certif 3379229979443 2 ((1689614989721, 1)::(2,1)::nil) 1)
        ((Pock_certif 1689614989721 3 ((6034339249, 1)::(2,3)::nil) 1) ::
         (Pock_certif 6034339249 17 ((23, 1)::(7, 1)::(2,4)::nil) 3514) ::
         (Proof_certif 23 prime23) ::
         (Proof_certif 7 prime7) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

