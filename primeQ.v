Require Import Coqprime.examples.PocklingtonRefl.
Local Open Scope positive_scope.

Lemma myPrime : prime 61329566248342901292543872769978950870633559608669337131139375508370458778917.
Proof.
 apply (Pocklington_refl
         (Pock_certif 61329566248342901292543872769978950870633559608669337131139375508370458778917 5 ((6350820103, 1)::(4223919769, 1)::(97, 1)::(23, 1)::(7, 1)::(3, 3)::(2,2)::nil) 23858495663773412360561306)
        ((Pock_certif 6350820103 3 ((32074849, 1)::(2,1)::nil) 1) ::
         (Pock_certif 4223919769 7 ((139, 1)::(2,3)::nil) 2117) ::
         (Pock_certif 32074849 17 ((3, 2)::(2,5)::nil) 199) ::
         (Proof_certif 139 prime139) ::
         (Proof_certif 97 prime97) ::
         (Proof_certif 23 prime23) ::
         (Proof_certif 7 prime7) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

