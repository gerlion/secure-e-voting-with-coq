Require Import Field_theory 
  Ring_theory List NArith 
  Ring Field Utf8 Lia Coq.Arith.PeanoNat. 
Import ListNotations.

Section Computation.

  


  Variable 
    (R : Type)
    (rO rI:R)
    (radd rmul rsub : R -> R -> R)
    (ropp : R -> R)
    (rdiv : R -> R -> R)
    (rinv : R -> R).


  Variable RRing : 
    ring_theory rO rI radd rmul rsub ropp eq.
  Variable Rfield : 
    field_theory rO rI radd rmul rsub ropp rdiv rinv eq.

  Add Field cField : Rfield.
  Add Ring cRing : RRing.

  (* power theory *)  
  Variable Cpow : Type.
  Variable Cp_phi : N -> Cpow.
  Variable rpow : R -> Cpow -> R.
  Variable pow_th : power_theory rI rmul eq Cp_phi rpow.

  (* Field notations *)
  Local Notation "0" := rO : R_scope.
  Local Notation "1" := rI : R_scope.
  Local Infix "+" := radd : R_scope.
  Local Infix "-" := rsub : R_scope.
  Local Infix "*" := rmul : R_scope.
  Local Infix "/" := rdiv : R_scope.
  Notation "- x" := (ropp x) : R_scope.
  Notation "/ x" := (rinv x) : R_scope.

  Local Open Scope R_scope.

  (* closed form of polynomial *)
  Fixpoint mul_closed_poly (l : list R) (x : R) : R :=
    match l with
    | [] => 1
    | h :: t => (h - x) * mul_closed_poly t x 
    end.

  (* generate k combinations of list l *)
  Fixpoint gen_comb (l : list R) (k : nat) : list (list R) :=
    match k with 
    | O => [[]]
    | S k' => match l with 
      | [] => []
      | h :: t => List.map (fun u => h :: u) (gen_comb t k') ++
        gen_comb t k
    end
    end.

  Definition add_rlist (l : list R) :=
    List.fold_left (λ a b, a + b) l 0.

  Definition mul_rlist (l : list R) :=
    List.fold_left (λ a b, a * b) l 1.
    

  Fixpoint compute_poly_simp (l : list R) 
    (x : R) (k : nat) : R :=
    match k with
    | O => pow_N 1 rmul (-x) (N.of_nat (List.length l)) 
    | S k' => (pow_N 1 rmul (-x) (N.of_nat (Nat.sub (List.length l) k))) *
      (add_rlist (List.map mul_rlist (gen_comb l k))) + 
      compute_poly_simp l x k'
    end.
    
    
  Variable u x₁ x₂ x₃ x₄ : R.
  Eval compute in mul_closed_poly [x₁; x₂] u.



  Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
    match n with 
    | O => []
    | S n' => match l with 
      | [] => []
      | h :: t => h :: (take n' t)
    end 
    end.

 
  Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
    match n with 
    | O => l
    | S n' => match l with 
      | [] => []
      | h :: t => drop n' t
    end
    end.

  Fixpoint zip_with {A B C : Type} (f : A -> B -> C) (l₁ : list A) 
    (l₂ : list B) : list C :=
    match l₁, l₂ with
    | h₁ :: t₁, h₂ :: t₂ =>  (f h₁ h₂) :: (zip_with f t₁ t₂)
    | _, _ => []
    end.

  Lemma take_nt :
    forall n (t : list R), 
      n ≤ length t -> 
      n ≤ length (take n t).
  Proof.
    induction n. 
    + intros ? Hn.
      simpl.
      nia.
    + intros ? Hn.
      simpl.
      destruct t.
      - (* impossible *)   
        simpl in Hn.
        nia.
      - (* inductive case *) 
        simpl in Hn.
        simpl.
        apply Le.le_n_S.
        eapply IHn;
        try nia.
  Qed.


  (* Not in Coq library! *)
  (* If two lists have the same length and they pointwise equal, 
  then they are same list*)
  Lemma nth_ext_error {A : Type} : 
    forall (l l' : list A), 
    length l = length l' ->
    (forall n, n < length l -> nth_error l n = nth_error l' n) -> l = l'.
  Proof.
    induction l.
    + destruct l'.
      simpl; 
      intros Hl Hn.
      reflexivity.
      simpl; 
      intros Hl Hn.
      nia.
    + destruct l'.
      simpl; 
      intros Hl Hn.
      nia.
      simpl; 
      intros Hl Hn.
      assert (Ht : O < S (length l)) by 
      nia.
      pose proof (Hn O Ht) as Hp.
      simpl in Hp.
      f_equal. 
      inversion Hp.
      reflexivity.
      apply IHl.
      nia.
      intros ? Hnn.
      assert (Hv : S n < S (length l)) by 
      nia.
      pose proof (Hn _  Hv).
      simpl in H.
      exact H.
  Qed.


  Lemma take_drop_inv {A : Type} : 
    forall (n : nat) (l : list A), 
    (take n l ++ drop n l = l).
  Proof.
    induction n.
    - simpl; intros ?; reflexivity.
    - simpl; intros ?.
      destruct l.
      + reflexivity.
      + simpl. rewrite IHn.
        reflexivity.
  Qed.

  Lemma take_all : 
    forall l : list R, (take (length l) l)  = l.
  Proof.
    induction l. 
    simpl; reflexivity.
    simpl; rewrite IHl; 
    reflexivity.
  Qed. 

  Lemma drop_all : 
    forall l : list R, (drop (length l) l)  = [].
  Proof.
    induction l. 
    simpl; reflexivity.
    simpl; rewrite IHl; 
    reflexivity.
  Qed. 

  Fixpoint list_upto (n : nat) : list nat :=
    match n with 
    | O => [O]
    | S n' => n :: list_upto n'
    end.

  

  Lemma test_inv : 
    let l := [x₁; x₂; x₃; x₄] in 
    let n := 2%nat in 
    compute_poly_simp (take n l) u n * 
    mul_closed_poly (drop n l) u = mul_closed_poly l u.
  Proof.
    compute.
    ring_simplify.
    ring.
  Qed.

  Lemma test_inv_2 : 
    let t := [x₂; x₃; x₄] in 
    let n := 2%nat in
    let h := x₁ in
    let y := u in
    compute_poly_simp (take (S n) (h :: t)) y (S n) =
    compute_poly_simp (take n t) y n * (h - y).
  Proof.
    simpl.
    ring_simplify.
    unfold add_rlist, mul_rlist.
    simpl.
    ring_simplify.
    ring.
  Qed.




  Definition populate_poly_terms (l : list R) 
    (x : R) (k : nat) : list (nat * nat * R * R) := 
    List.map (fun w => 
      (Nat.sub (List.length l) w, w, 
      pow_N 1 rmul (-x) (N.of_nat (Nat.sub (List.length l) w)), 
      add_rlist (List.map mul_rlist (gen_comb l w))))
      (list_upto k).


  Definition eval_populate_poly  (l : list R) 
    (x : R) (k : nat) : R :=
    List.fold_left (fun a '(_, _, u, v) => a + u * v)
      (populate_poly_terms l x k) 0.

  Fact tmp_3 : eval_populate_poly [x₂; x₃] u 2 = 
    compute_poly_simp [x₂; x₃] u 2.
  Proof.
    simpl.
    unfold eval_populate_poly.
    simpl.
    unfold add_rlist,
    mul_rlist.
    simpl.
    ring_simplify.
    ring.
  Qed.

  Lemma populate_poly_term_rewrite :
    forall h t x n,
    populate_poly_terms (h :: t) x (S n) = 
      [(Nat.sub (List.length (h :: t)) (S n), S n,
      pow_N 1 rmul (-x) (N.of_nat (Nat.sub (List.length (h :: t)) (S n))),
      add_rlist (List.map mul_rlist (gen_comb (h :: t) (S n))))] ++
      (populate_poly_terms (h :: t) x n).
  Proof.
    intros *.
    simpl; reflexivity.
  Qed. 

  Lemma fold_left_acc : 
    forall (l : list (nat * nat * R * R)) (a : R), 
    fold_left (fun a '(_, _, u, v) => a + u * v) l a =
    a + fold_left (fun a '(_, _, u, v) => a + u * v) l 0.
  Proof.
    induction l. 
    + intros ?.
      simpl;
      ring.
    + intros ?;
      simpl.
      rewrite IHl.
      destruct a as [[[an bn] cn] dn]. 
      rewrite <-Radd_assoc.
      f_equal.
      rewrite <-IHl.
      assert (Ha : 0 + cn * dn = cn * dn).
      ring.
      rewrite Ha.
      reflexivity.
      exact RRing.
  Qed.

  Lemma populate_poly_term_compute_poly :
    forall n l x, 
    n <= List.length l ->
    eval_populate_poly l x n = compute_poly_simp l x n.
  Proof.
    induction n.
    + intros ? ? Hl.
      simpl.
      unfold eval_populate_poly.
      simpl.
      ring_simplify.
      assert (Ht: (gen_comb l 0) = [[]]).
      unfold gen_comb.
      (* weird! not simplifying *)
      destruct l.
      reflexivity.
      reflexivity.
      rewrite Ht;
      clear Ht.
      simpl.
      unfold add_rlist,
      mul_rlist.
      simpl.
      ring_simplify.
      assert (Ht: ((length l - 0) = length l)%nat).
      nia.
      rewrite Ht; clear Ht.
      reflexivity.
    + intros ? ? Hl.
      destruct l as [|h t].
      simpl in Hl;
      nia.
      simpl in Hl.
      simpl.
      assert (Hnt : n <= List.length (h :: t)).
      simpl; nia.
      specialize (IHn _ x Hnt).
      rewrite <-IHn.
      unfold eval_populate_poly.
      rewrite populate_poly_term_rewrite.
      rewrite List.fold_left_app.
      simpl.
      remember ((
      pow_N 1 rmul (- x) (N.of_nat (length t - n)) *
      add_rlist (map mul_rlist (map (λ u0 : list R, h :: u0) 
      (gen_comb t n) ++ gen_comb t (S n))))) as a.
      ring_simplify.
      remember ((populate_poly_terms (h :: t) x n)) as pl.
      rewrite fold_left_acc.
      ring.
  Qed.




  
  Definition mul_polyterm_populate_terms (l : list R) 
    (x : R) (k : nat) (y : R) : list (nat * nat * R * R) := 
    List.map (fun '(a, b, u, t) => (a, S b, u, y * t))
    (populate_poly_terms l x k).

  

  Lemma fold_nested_map_first :
    forall (l : list (nat * nat * R * R)) (y : R), 
    List.fold_left (fun a '(_, _, u, v) => a + u * v)
      (List.map (fun '(a, b, u, t) => (a, S b, u, y * t)) l) 0 =
    y * List.fold_left (fun a '(_, _, u, v) => a + u * v) l 0.
  Proof.
    induction l as [|(((au, bu), cu), du) l].
    + intros ?; 
      simpl;
      ring.
    + intros ?.
      simpl.
      rewrite fold_left_acc.
      rewrite IHl.
      remember (fold_left
      (λ (a : R) '(y0, v), let '(y1, u0) := y0 in let '(_, _) := y1 in a + u0 * v)
      l 0) as fl.
      rewrite fold_left_acc;
      subst.
      ring.
  Qed.


  Lemma connect_mul_polyterm_with_poly_term :
    forall l x k y, 
    List.fold_left (fun a '(_, _, u, v) => a + u * v) 
    (mul_polyterm_populate_terms l x k y) 0 = 
    y * List.fold_left (fun a '(_, _, u, v) => a + u * v) 
    (populate_poly_terms l x k) 0.
  Proof.
    intros *.
    unfold mul_polyterm_populate_terms.
    eapply fold_nested_map_first.
  Qed.


  Lemma connect_mul_polyterm_with_evalpoly :
    forall l x k y, 
    List.fold_left (fun a '(_, _, u, v) => a + u * v) 
    (mul_polyterm_populate_terms l x k y) 0 = 
    y * eval_populate_poly l x k.
  Proof.
    intros *.
    unfold eval_populate_poly.
    unfold mul_polyterm_populate_terms.
    eapply fold_nested_map_first.
  Qed.



  
  (* multiply every term *)
  Definition mul_polypow_populate_terms (l : list R) 
    (x : R) (k : nat) (y : R) : list (nat * nat * R * R) := 
    List.map (fun '(a, b, u, t) => (S a, b, y * u, t))
      (populate_poly_terms l x k).

  
  Lemma fold_nested_map_second :
    forall (l : list (nat * nat * R * R)) (y : R), 
    List.fold_left (fun a '(_, _, u, v) => a + u * v)
      (List.map (fun '(a, b, u, t) => (S a, b, y * u, t)) l) 0 =
    y * List.fold_left (fun a '(_, _, u, v) => a + u * v) l 0.
  Proof.
    induction l as [|(((au, bu), cu), du) l].
    + intros ?; 
      simpl;
      ring.
    + intros ?.
      simpl.
      rewrite fold_left_acc.
      rewrite IHl.
      remember (fold_left
      (λ (a : R) '(y0, v), let '(y1, u0) := y0 in let '(_, _) := y1 in a + u0 * v)
      l 0) as fl.
      rewrite fold_left_acc;
      subst.
      ring.
  Qed.    
  


  Lemma connect_mul_polypow_with_poly_term:
    forall l x k y, 
    List.fold_left (fun a '(_, _, u, v) => a + u * v) 
    (mul_polypow_populate_terms l x k y) 0 = 
    y * List.fold_left (fun a '(_, _, u, v) => a + u * v) 
    (populate_poly_terms l x k) 0.
  Proof.
    intros *.
    unfold mul_polypow_populate_terms.
    eapply fold_nested_map_second.
  Qed.



  Lemma connect_mul_polypow_with_evalpoly :
    forall l x k y, 
    List.fold_left (fun a '(_, _, u, v) => a + u * v) 
    (mul_polypow_populate_terms l x k y) 0 = 
    y * eval_populate_poly l x k.
  Proof.
    intros *.
    unfold mul_polyterm_populate_terms.
    eapply fold_nested_map_second.
  Qed.




  
  


 
    
  
  (*
  compute_poly_simp u y n * (h - y) = compute_poly_simp (h :: u) y (S n)
  *)  
  Eval compute in populate_poly_terms [x₂; x₃] u 2.
  (*
    [(0, 2, 1, 0 + 1 * x₂ * x₃); 
    (1, 1, - u, 0 + 1 * x₂ + 1 * x₃);
    (2, 0, - u * - u, 0 + 1)]
  *)


  Eval compute in mul_polyterm_populate_terms [x₂; x₃] u 2 x₁. 
  (*
    [(0, 3, 1, x₁ * (0 + 1 * x₂ * x₃));
    (1, 2, - u, x₁ * (0 + 1 * x₂ + 1 * x₃));
    (2, 1, - u * - u, x₁ * (0 + 1))]
  *)

  (* align the two polynomials *)
  Definition append_mul_polyterm_populate_terms (l : list R)
    (x : R) (n : nat) (y : R) :=
    mul_polyterm_populate_terms l x n y ++ 
    [(S n, O, pow_N 1 rmul (-x) (N.of_nat (S n)), 0)].


  
  Eval compute in append_mul_polyterm_populate_terms [x₂; x₃] u 2 x₁.
  (*
   [(0, 3, 1, x₁ * (0 + 1 * x₂ * x₃));
    (1, 2, - u, x₁ * (0 + 1 * x₂ + 1 * x₃));
    (2, 1, - u * - u, x₁ * (0 + 1)); 
    (3, 0, - u * (- u * - u), 0)] (* This one is newly added term *)
  *)


  Eval compute in mul_polypow_populate_terms [x₂; x₃] u 2 (-u).
  (*
    [(1, 2, - u * 1, 0 + 1 * x₂ * x₃);
    (2, 1, - u * - u, 0 + 1 * x₂ + 1 * x₃);
    (3, 0, - u * (- u * - u), 0 + 1)]
  *) 

  Definition append_mul_polypow_populate_terms (l : list R)
    (x : R) (n : nat) (y : R) :=
    [(O, S n, 1, 0)] ++
    mul_polypow_populate_terms l x n y.
  

  Eval compute in append_mul_polypow_populate_terms [x₂; x₃] u 2 (-u).
  (*
    [(0, 3, 1, 0); 
    (1, 2, - u * 1, 0 + 1 * x₂ * x₃);
    (2, 1, - u * - u, 0 + 1 * x₂ + 1 * x₃);
    (3, 0, - u * (- u * - u), 0 + 1)]
  *)



  (* If I add the polynomials 
    (i) append_mul_polyterm_populate_terms [x₂; x₃] x 2 x₁ and 
    (ii) append_mul_polypow_populate_terms [x₂; x₃] x 2 (-x),
    then I will get (iii) populate_poly_terms [x₁; x₂; x₃] x 3.
  *)

  Definition add_polynomials (l : list R)
    (x : R) (n : nat) (y : R) :=
    zip_with 
    (fun '(a, b, u, v) '(_, _, _, w) => (a, b, u, v + w))
    (append_mul_polyterm_populate_terms l x n y)
    (append_mul_polypow_populate_terms l x n (-x)).
  

  Eval compute in add_polynomials [x₂; x₃] u 2 x₁.
  (*
  [(0, 3, 1, x₁ * (0 + 1 * x₂ * x₃) + 0);
  (1, 2, - u, x₁ * (0 + 1 * x₂ + 1 * x₃) + (0 + 1 * x₂ * x₃));
  (2, 1, - u * - u, x₁ * (0 + 1) + (0 + 1 * x₂ + 1 * x₃));
  (3, 0, - u * (- u * - u), 0 + (0 + 1))]
  *)



  Eval compute in populate_poly_terms [x₁; x₂; x₃] u 3.
  (*
  [(0, 3, 1, 0 + 1 * x₁ * x₂ * x₃);
  (1, 2, - u, 0 + 1 * x₁ * x₂ + 1 * x₁ * x₃ + 1 * x₂ * x₃);
  (2, 1, - u * - u, 0 + 1 * x₁ + 1 * x₂ + 1 * x₃);
  (3, 0, - u * (- u * - u), 0 + 1)]
  *)

  (*
    In order to show to that 
      add_polynomials l x n y is equal to
      populate_poly_terms (y :: l) x (S n), 
    I need to show that:
    (i) their lenghts are equal, and
    (ii) they are pointwise equal.   
    

    nth_ext_error {A : Type} : 
    forall (l l' : list A), 
    length l = length l' ->
    (forall n, n < length l -> 
      nth_error l n = nth_error l' n) -> l = l'.

  *)

  Lemma list_upto_length : forall n : nat, 
    List.length (list_upto n) = S n.
  Proof.
    induction n.
    - simpl; reflexivity.
    - simpl; rewrite IHn;
      reflexivity.
  Qed.


  Lemma populate_poly_terms_length : 
    forall n l y, 
    List.length (populate_poly_terms l y n) = S n. 
  Proof.
    intros ? ? ?.
    unfold populate_poly_terms.
    rewrite map_length.
    apply list_upto_length.
  Qed.

  Lemma zip_length_min : forall {X Y Z : Type}
    (f : X -> Y -> Z) l l', 
    length (zip_with f l l') = min (length l) (length l').
  Proof.
    induction l; 
    destruct l'; 
    simpl; eauto.
  Qed.

  Lemma zip_length : forall {X Y Z : Type} (f : X -> Y -> Z) 
    l l', length l = length l' -> length (zip_with f l l') = length l.
  Proof.
    intros * H. 
    rewrite zip_length_min.
    rewrite H. 
    rewrite Min.min_idempotent.
    eauto.
  Qed.


  Lemma add_polynomials_length : 
    forall n l x y,
    List.length 
    (add_polynomials l x n y) = S (S n).
  Proof.
    intros ? ? ? ?. 
    unfold add_polynomials.
    rewrite zip_length.
    unfold append_mul_polyterm_populate_terms.
    unfold mul_polyterm_populate_terms,
    populate_poly_terms.
    rewrite map_map.
    rewrite app_length.
    rewrite map_length.
    simpl.
    rewrite list_upto_length.
    nia.
    unfold append_mul_polypow_populate_terms, 
    append_mul_polyterm_populate_terms,
    mul_polypow_populate_terms,
    mul_polyterm_populate_terms,
    populate_poly_terms.
    repeat rewrite map_map.
    rewrite app_length.
    simpl.
    repeat rewrite map_length.
    nia.
  Qed.


  Lemma add_polynomials_populate_poly_terms_same_length :
    forall n l x y,  
    List.length (add_polynomials l x n y) =
    List.length (populate_poly_terms (y :: l) x (S n)).
  Proof.
    intros ? ? ? ?.
    rewrite add_polynomials_length.
    rewrite populate_poly_terms_length.
    reflexivity.
  Qed.


  Lemma zip_list_index_some {A B C : Type} 
    (f : A -> B -> C) : 
    forall (l₁ : list A) (l₂ : list B) 
    k t w, 
    List.length l₁ = List.length l₂ -> 
    (k < List.length l₁)%nat -> 
    Some t = List.nth_error l₁ k ->
    Some w = List.nth_error l₂ k ->
    List.nth_error (zip_with f l₁ l₂) k = Some (f t w).
  Proof.
    induction l₁.
    - simpl; intros ? ? ? ? ? Hl Hk Hw.
      lia.
    - simpl; intros ? ? ? ? Hl Hk Hw Hv.
      destruct l₂.
      simpl in Hl.
      lia.
      simpl in Hl.
      inversion Hl as [Hlt]; clear Hl.
      destruct k.
      simpl. simpl in Hw.
      simpl in Hv.
      inversion Hw; inversion Hv; subst.
      reflexivity.
      simpl.
      assert (Hwt : (k < List.length l₁)%nat) by lia.
      clear Hk.
      apply IHl₁; assumption.
  Qed.

  
  
  Lemma list_elem_nth : forall n k : nat,
    (k < List.length (list_upto n))%nat -> 
    (List.nth_error (list_upto n) k = Some (n - k))%nat.
  Proof.
    induction n;simpl.
    + intros [|]; intro H; simpl.
      reflexivity. lia.
    + intros ? Hk.
      destruct k.
      - simpl. reflexivity.
      - simpl. apply IHn.
        lia.
  Qed.


  Lemma nth_append_polyterms : 
    forall n l x y k,
    k < S (S n) ->
    (n <= List.length l) ->
    nth_error (append_mul_polyterm_populate_terms l x n y) k = 
    if k <? S n then 
    Some ((length l - n + k)%nat, 
      Nat.sub (S n) k, 
      pow_N 1 rmul (- x) (N.of_nat (length l - n + k)),
      y * add_rlist (map mul_rlist (gen_comb l (Nat.sub n k))))
    else
    Some (S n, O, pow_N 1 rmul (- x) (N.of_nat (S n)), 0).
  Proof.
    intros * Hk Hn.
    assert (Htt: k < S n  \/  k = S n).
    nia.
    unfold append_mul_polyterm_populate_terms,
    mul_polyterm_populate_terms,
    populate_poly_terms.
    rewrite map_map.
    destruct Htt as [Htt | Htt].
    apply Nat.ltb_lt in Htt.
    rewrite Htt.
    rewrite nth_error_app1.
    erewrite map_nth_error.
    f_equal.
    f_equal.
    f_equal.
    f_equal.
    assert (Hkt: k <= length l).
    eapply Nat.ltb_lt in Htt.
    nia.
    assert (Hkw : k <= n).
    apply Nat.ltb_lt in Htt.
    nia.
    nia.
    assert (Hkt: k <= length l).
    eapply Nat.ltb_lt in Htt.
    nia.
    assert (Hkw : k <= n).
    apply Nat.ltb_lt in Htt.
    nia.
    nia.
    assert (Hkt: k <= length l).
    eapply Nat.ltb_lt in Htt.
    nia.
    assert (Hwt : k <= n).
    apply Nat.ltb_lt in Htt.
    nia.
    f_equal.
    nia.
    erewrite list_elem_nth.
    reflexivity.
    rewrite list_upto_length.
    eapply Nat.ltb_lt in Htt.
    nia.
    rewrite map_length.
    eapply Nat.ltb_lt in Htt.
    rewrite list_upto_length.
    nia.
    rewrite Htt, Nat.ltb_irrefl.
    rewrite nth_error_app2.
    rewrite map_length.
    rewrite list_upto_length.
    assert (Hnt : (S n - S n = O)%nat).
    nia.
    rewrite Hnt.
    simpl.
    reflexivity.
    rewrite map_length, 
    list_upto_length.
    nia.
  Qed.


  Lemma nth_append_polyterms_expanded : 
    forall n l x y k,
    k < S (S n) ->
    (n <= List.length l) ->
    nth_error (append_mul_polyterm_populate_terms l x n y) k =
    if k =? O then 
      Some ((length l - n)%nat, 
        Nat.sub (S n) 0, 
        pow_N 1 rmul (- x) (N.of_nat (length l - n )),
        y * add_rlist (map mul_rlist (gen_comb l n)))
    else if k <? S n then 
      Some ((length l - n + k)%nat, 
        Nat.sub (S n) k, 
        pow_N 1 rmul (- x) (N.of_nat (length l - n + k)),
        y * add_rlist (map mul_rlist (gen_comb l (Nat.sub n k))))
    else
      Some (S n, O, pow_N 1 rmul (- x) (N.of_nat (S n)), 0).
  Proof.
    intros * Hk Hn.
    pose proof nth_append_polyterms n l x y k Hk Hn as Hp.
    assert (Hkt : k = O ∨ 1 <= k <= n ∨ k = S n).
    nia.
    destruct Hkt as [Hkt | [Hkt | Hkt]].
    rewrite Hkt.  
    rewrite Hkt in Hp.
    assert (Htt : 0 =? 0 = true).
    apply Nat.eqb_refl.
    rewrite Htt;
    clear Htt.
    assert (Htt: 0 <? S n = true).
    apply Nat.ltb_lt;
    try nia.
    rewrite Htt in Hp.
    rewrite Nat.add_0_r in Hp.
    repeat rewrite Nat.sub_0_r in Hp.
    exact Hp.
    assert (Htt : k =? 0 = false).
    apply Nat.eqb_neq.
    nia.
    rewrite Htt; clear Htt.
    assert (Htt: k <? S n = true).
    apply Nat.ltb_lt;
    try nia.
    rewrite Htt in Hp.
    rewrite Htt.
    exact Hp.
    assert (Htt : k =? 0 = false).
    apply Nat.eqb_neq.
    nia.
    rewrite Htt; clear Htt.
    assert (Hsn : k <? S n = false).
    rewrite Hkt.
    apply Nat.ltb_irrefl.
    rewrite Hsn in Hp.
    rewrite Hsn.
    exact Hp.
  Qed.



  


  Lemma nth_append_polypow : 
    forall n l x k,
    k < S (S n) -> 
    n <= List.length l ->
    nth_error (append_mul_polypow_populate_terms l x n (-x)) k = 
    if k =? O then 
    Some (O, S n, 1, 0)
    else 
    Some (S (length l - (n - (k - 1))), 
      (n - (k - 1))%nat, 
      -x * pow_N 1 rmul (- x) (N.of_nat (length l - (n - (k - 1)))),
      add_rlist (map mul_rlist (gen_comb l (n - (k - 1))))).
  Proof.
    intros * Hk Hn.
    assert (Htt: k = O  \/  S O <= k).
    nia.
    unfold append_mul_polypow_populate_terms, 
    mul_polypow_populate_terms, 
    populate_poly_terms.
    rewrite map_map.
    destruct Htt as [Htt | Htt].
    rewrite Htt.
    rewrite Nat.eqb_refl.
    rewrite nth_error_app1.
    simpl.
    reflexivity.
    simpl; nia.
    assert (Hz: k =? O = false).
    rewrite Nat.eqb_neq.
    nia.
    rewrite Hz; clear Hz.
    rewrite nth_error_app2.
    simpl.
    erewrite map_nth_error.
    f_equal.
    erewrite list_elem_nth.
    reflexivity.
    rewrite list_upto_length.
    nia.
    simpl.
    nia.
  Qed.


  Lemma nth_append_polypow_expanded : 
    forall n l x k,
    k < S (S n) -> 
    n <= List.length l ->
    nth_error (append_mul_polypow_populate_terms l x n (-x)) k = 
    if k =? O then 
      Some (O, S n, 1, 0)
    else if k <? S n then  
      Some (S (length l - (n - (k - 1))), 
        (n - (k - 1))%nat, 
        -x * pow_N 1 rmul (- x) (N.of_nat (length l - (n - (k - 1)))),
        add_rlist (map mul_rlist (gen_comb l (n - (k - 1)))))
    else (* k = S n *) 
      Some ((length l - n + S n)%nat, O, 
        -x * pow_N 1 rmul (- x) (N.of_nat (length l)), 1).
  Proof.
    intros * Hk Hn.
    pose proof nth_append_polypow n l x k Hk Hn as Hp.
    assert (Hkt : k = O ∨ 1 <= k <= n ∨ k = S n).
    nia.
    destruct Hkt as [Hkt | [Hkt | Hkt]].
    rewrite Hkt.  
    rewrite Hkt in Hp.
    assert (Htt : 0 =? 0 = true).
    apply Nat.eqb_refl.
    rewrite Htt;
    rewrite Htt in Hp;
    clear Htt.
    exact Hp.   
    assert (Htt : k =? 0 = false).
    apply Nat.eqb_neq.
    nia.
    rewrite Htt; 
    rewrite Htt in Hp;
    clear Htt.
    assert (Htt: k <? S n = true).
    apply Nat.ltb_lt;
    try nia.
    rewrite Htt. 
    exact Hp.
    assert (Htt : k =? 0 = false).
    apply Nat.eqb_neq.
    nia.
    rewrite Htt; 
    rewrite Htt in Hp;
    clear Htt.
    assert (Hsn : k <? S n = false).
    rewrite Hkt.
    apply Nat.ltb_irrefl.
    rewrite Hsn.
    rewrite Hkt in Hp.
    rewrite Hkt.
    rewrite Hp.
    repeat f_equal.
    nia.
    nia.
    nia.
    simpl.
    rewrite Nat.sub_0_r.
    rewrite Nat.sub_diag.
    unfold add_rlist,
    mul_rlist.
    destruct l;
    simpl; ring.
  Qed.


  Lemma gen_comb_emp : 
    forall l n, 
    List.length l <= n -> 
    gen_comb l (S n) = [].
  Proof.
    induction l.
    + intros ? Hn.
      simpl;
      reflexivity.
    + intros ? Hn.
      simpl.
      destruct n.
      simpl in Hn.
      nia.
      simpl in Hn.
      assert (Hln₁ : length l <= n).
      nia.
      assert (Hln₂ : length l <= S n).
      nia.
      specialize (IHl _ Hln₁) as Ha.
      specialize (IHl _ Hln₂) as Hb.
      rewrite Ha, Hb.
      reflexivity.
  Qed.  
          
  
  Lemma gen_comb_equal : 
    forall l n, 
    n = List.length l ->
    gen_comb l n = [l].
  Proof.
    induction l.
    + intros ? Hn.
      simpl in Hn;
      rewrite Hn;
      simpl;
      reflexivity.
    + intros ? Hn.
      simpl in Hn.
      destruct n.
      nia.
      simpl.
      rewrite gen_comb_emp.
      rewrite List.app_nil_r.
      inversion Hn as (Hni).
      specialize (IHl _ Hni).
      rewrite <-Hni.
      rewrite IHl.
      simpl.
      reflexivity.
      nia.
  Qed.

  Lemma fold_left_gen_mul : 
    forall l y v, 
    y * fold_left (λ a b : R, a * b) l v = 
    fold_left (λ a b : R, a * b) l (v * y).
  Proof.
    induction l.
    + intros ? ?.
      simpl; ring.
    + intros ? ?.
      simpl.
      rewrite IHl.
      f_equal.
      ring.
  Qed.


  Lemma gen_comb_rewrite :
    forall n l y, 
    n = length l -> 
    y * add_rlist (map mul_rlist (gen_comb l n)) =
    add_rlist (map mul_rlist (gen_comb (y :: l) (S n))).
  Proof.
    intros * Hn.
    simpl.
    rewrite gen_comb_emp,
    List.app_nil_r.
    rewrite gen_comb_equal.
    simpl.
    unfold add_rlist,
    mul_rlist.
    simpl.
    ring_simplify.
    rewrite fold_left_gen_mul.
    reflexivity.
    nia.
    nia.
  Qed.
   


  Lemma tmp_4 : 
    let l := [x₂; x₃; x₄] in 
    let n := 3%nat in
    let y := x₁ in
    y * add_rlist (map mul_rlist (gen_comb l n)) =
    add_rlist (map mul_rlist (gen_comb (y :: l) (S n))).
  Proof.
    simpl.
    unfold add_rlist, mul_rlist.
    simpl.
    ring.
  Qed.


  Lemma sum_rlist_acc : 
    forall (l : list R) (a : R), 
    fold_left (fun acc u => acc + u) l a =
    a + fold_left (fun acc u => acc + u) l 0.
  Proof.
    induction l. 
    + intros ?.
      simpl;
      ring.
    + intros ?;
      simpl.
      rewrite IHl. 
      rewrite <-Radd_assoc.
      f_equal.
      rewrite <-IHl.
      assert (Ha : 0 + a = a).
      ring.
      rewrite Ha.
      reflexivity.
      exact RRing.
  Qed.

  Lemma add_rlist_dist : 
    forall l₁ l₂, 
    add_rlist (l₁ ++ l₂) = add_rlist l₁ + add_rlist l₂.
  Proof.
    induction l₁.
    + intros *.
      simpl.
      unfold add_rlist.
      simpl.
      ring.
    + intros *.
      unfold add_rlist in * |- *.
      simpl.
      rewrite sum_rlist_acc.
      remember (fold_left (λ acc u0 : R, acc + u0) (l₁ ++ l₂) 0) as fl.
      rewrite sum_rlist_acc.
      subst.
      rewrite IHl₁.
      ring.
  Qed. 

  Lemma add_rlist_dist_cons : 
    forall (l : list R) (a : R), 
    add_rlist (a :: l) = add_rlist [a] + add_rlist l.
  Proof.
    intros l a.
    unfold add_rlist.
    simpl.
    assert (Ha : (0 + a = a)).
    ring.
    rewrite sum_rlist_acc.
    ring.
  Qed.


  Lemma fold_left_map : 
    forall gl y, 
    y * add_rlist (map mul_rlist gl) =
    add_rlist (map mul_rlist (map (λ u : list R, y :: u) gl)).
  Proof.
    induction gl.
    + intros ?.
      simpl.
      unfold add_rlist.
      simpl. 
      ring.
    + intros ?.
      simpl.
      rewrite add_rlist_dist_cons.
      ring_simplify.
      rewrite IHgl.
      remember (y * add_rlist [mul_rlist a]) as ya.
      rewrite add_rlist_dist_cons.
      subst.
      f_equal.
      unfold add_rlist, 
      mul_rlist.
      simpl.
      ring_simplify.
      rewrite fold_left_gen_mul.
      ring.
  Qed.


  (* I don't know how to prove this one yet! *)
  Lemma thomas_has_proof_for_this : 
    forall k n l y,
    k <= n ->
    n = length l -> 
    y * add_rlist (map mul_rlist (gen_comb l (n - k))) +
    add_rlist (map mul_rlist (gen_comb l (S n - k))) =
    add_rlist (map mul_rlist (gen_comb (y :: l) (S n - k))).
  Proof.
    induction k.
    + intros * Hk Hn.
      simpl.
      rewrite Nat.sub_0_r.
      rewrite gen_comb_emp,
      List.app_nil_r.
      rewrite gen_comb_equal.
      simpl.
      unfold add_rlist,
      mul_rlist.
      simpl.
      ring_simplify.
      rewrite fold_left_gen_mul.
      reflexivity.
      nia.
      nia.
    + intros * Hk Hn.
      destruct n.
      - nia.
      - repeat rewrite Nat.sub_succ.
        assert (Hkt : k <= n).
        nia.
        destruct l.
        simpl in Hn.
        nia.
        simpl in Hn.
        rewrite <-Minus.minus_Sn_m.
        remember (r :: l) as rl.
      assert (Htt : 
        gen_comb (y :: rl) (S (n - k)) = 
        List.map (fun u => y :: u) (gen_comb rl (n - k)) ++  gen_comb rl (S (n - k))).
      reflexivity.
      rewrite Htt.
      rewrite map_app.
      rewrite add_rlist_dist.
      f_equal.
      apply fold_left_map.
      nia.
  Qed.
      


  Lemma tmp_5 : 
    let l := [x₂; x₃; x₄] in 
    let n := 3%nat in
    let k := 1%nat in (* 1 <= k <= n *)
    let y := x₁ in
    y * add_rlist (map mul_rlist (gen_comb l (n - k))) +
    add_rlist (map mul_rlist (gen_comb l (n - (k - 1)))) =
    add_rlist (map mul_rlist (gen_comb (y :: l) (S n - k))).
  Proof.
    simpl.
    unfold add_rlist,
    mul_rlist.
    simpl.
    ring.
  Qed.


  Lemma pow_N_rewrite : 
    forall k x, 
    1 <= k ->
    pow_N 1 rmul (- x) (N.of_nat k) =
    - x * pow_N 1 rmul (- x) (N.of_nat (k - 1)).
  Proof.
    induction k. 
    + intros * Hk.
      nia.
    + intros * Hk.
      destruct k.
      simpl.
      ring.
      assert (Hkt : 1 <= S k).
      nia.
      specialize (IHk x Hkt).
      simpl in *.
      rewrite pow_pos_succ.
      reflexivity.
      constructor;
      try eauto.
      intros xt yt zt Ha Hb.
      rewrite Ha; 
      exact Hb.
      intros xt yt Ha.
      unfold Morphisms.respectful.
      intros xa ya Hx.
      rewrite Ha, Hx.
      reflexivity.
      intros xa ya za.
      ring.
  Qed.
  
  Lemma nth_error_nil : forall {t} i,
    @nth_error t nil i = None.
  Proof.
    induction i; auto.
  Qed.

  Lemma nth_error_length : forall {t} l n x,
    @nth_error t l n = Some x -> n < length l.
  Proof.
    intros.
    generalize dependent x.
    generalize dependent l.
    induction n.
    induction l.
    - intros.
      inversion H.
    - intros.
      simpl.
      apply PeanoNat.Nat.lt_0_succ.
    - intros.
      destruct l.
      rewrite nth_error_nil in H.
      inversion H.
      inversion H.
      apply IHn in H1.
      simpl.
      apply Lt.lt_n_S.
      assumption.
  Qed.


 
 
  Lemma append_mul_polyterm_populate_terms_length:
    forall n l x y, 
    length (append_mul_polyterm_populate_terms l x n y) = S (S n).
  Proof.
    intros *.
    unfold append_mul_polyterm_populate_terms.
    rewrite app_length.
    simpl.
    unfold mul_polyterm_populate_terms.
    rewrite map_length.
    unfold populate_poly_terms.
    rewrite map_length.
    rewrite list_upto_length.
    nia.
  Qed.

  Lemma append_mul_polyterm_polypow_first_three_term_same : 
    forall n k l x y a₁ b₁ u₁ v₁ a₂ b₂ u₂ v₂,
    n = List.length l ->
    Some (a₁, b₁, u₁, v₁) = 
      List.nth_error (append_mul_polyterm_populate_terms l x n y) k ->
    Some (a₂, b₂, u₂, v₂) = 
      List.nth_error (append_mul_polypow_populate_terms l x n (-x)) k ->
    a₁ = a₂ ∧ b₁ = b₂ ∧ u₁ = u₂ ∧ 
    (v₁ + v₂ = add_rlist (List.map mul_rlist (gen_comb (y :: l) b₁))).
  Proof.
    intros * Hn Ha Hb.
    symmetry in Ha.
    symmetry in Hb.
    pose proof @nth_error_length _ ((append_mul_polyterm_populate_terms l x n y)) k
    (a₁, b₁, u₁, v₁) Ha as Hnel.
    rewrite append_mul_polyterm_populate_terms_length in Hnel.
    rewrite nth_append_polyterms in Ha.
    rewrite nth_append_polypow in Hb.
    assert (Hkt : k = O ∨ 1 <= k <= n ∨ k = S n).
    
    nia.
    destruct Hkt as [Hkt | [Hkt | Hkt]].
    rewrite Hkt in Ha, Hb.
    assert (Htt : 0 =? 0 = true).
    apply Nat.eqb_refl.
    rewrite Htt in Hb; 
    clear Htt.
    assert (Htt : 0 <? S n = true).
    apply Nat.ltb_lt;
    nia.
    rewrite Htt in Ha.
    inversion Ha; 
    inversion Hb;
    subst.
    repeat split; 
    try nia.
    rewrite Nat.sub_diag.
    simpl; reflexivity. 
    rewrite Nat.sub_0_r.
    rewrite gen_comb_rewrite.
    ring.
    reflexivity.
    assert (Hsn : k <? S n = true).
    apply Nat.ltb_lt.
    nia.
    rewrite Hsn in Ha; clear Hsn.
    assert (Hwt : k =? 0 = false).
    apply Nat.eqb_neq.
    nia.
    rewrite Hwt in Hb.
    clear Hwt.
    inversion Ha; 
    inversion Hb; 
    subst.
    repeat split.
    try nia.
    destruct k;
    simpl in Hkt; 
    try nia.
    rewrite Nat.sub_diag.
    assert (Htt : (length l - (length l - (k - 1)) = k - 1)%nat).
    nia.
    rewrite Htt; clear Htt.
    apply pow_N_rewrite.
    nia.
    assert (Htt : ((length l - (k - 1)) = S (length l) - k)%nat).
    nia.
    rewrite Htt; clear Htt.
    apply thomas_has_proof_for_this;
    try nia.
    assert (Hwt : k =? 0 = false).
    apply Nat.eqb_neq.
    nia.
    rewrite Hwt in Hb.
    assert (Hsn : k <? S n = false).
    rewrite Hkt.
    apply Nat.ltb_irrefl.
    rewrite Hsn in Ha; clear Hsn.
    assert (Htt : (k - 1 = n)%nat).
    nia.
    rewrite Htt in Hb.
    rewrite Nat.sub_diag in Hb.
    rewrite Nat.sub_0_r in Hb.
    rewrite <-Hn in Hb.
    split.
    assert (Ha₁ : a₁ = S n).
    inversion Ha; subst; reflexivity.
    assert (Ha₂ : a₂ = S n).
    inversion Hb; subst; reflexivity.
    subst; reflexivity.
    split.
    inversion Ha; inversion Hb;
    subst; reflexivity.
    split.
    assert (u₁ = pow_N 1 rmul (- x) (N.of_nat (S n))).
    inversion Ha; subst;
    reflexivity.
    assert (u₂ = - x * pow_N 1 rmul (- x) (N.of_nat n)).
    inversion Hb; subst;
    reflexivity.
    subst. 
    pose proof (pow_N_rewrite (S (length l)) x).
    assert (1 <= S (length l))%nat.
    nia.
    specialize (H H0).
    assert ( S (length l) - 1 = length l)%nat.
    nia.
    rewrite H1 in H.
    exact H.
    assert (Hbb : b₁ = O).
    inversion Ha;
    subst;
    reflexivity.
    rewrite Hbb.
    simpl.
    inversion Ha; 
    inversion Hb; 
    subst.
    simpl.
    destruct l. 
    simpl.
    ring.
    simpl.
    ring.
    nia.
    nia.
    nia.
    nia.
  Qed.


  Lemma append_mul_polypow_populate_terms_lenght:
    forall n l x, 
    length (append_mul_polypow_populate_terms l x n (- x)) = S (S n).
  Proof.
    intros *.
    unfold append_mul_polypow_populate_terms,
    mul_polypow_populate_terms,
    populate_poly_terms.
    simpl.
    rewrite map_map, 
    map_length, 
    list_upto_length.
    nia.
  Qed.


  

  Lemma  populate_poly_terms_nth_terms : 
    forall k n l x, 
    k < S n -> 
    n <= length l -> 
    nth_error (populate_poly_terms l x n) k = 
    Some ((length l - n + k)%nat, 
      Nat.sub n k, 
      pow_N 1 rmul (-x) (N.of_nat (length l - n + k)),
    add_rlist (List.map mul_rlist (gen_comb l (Nat.sub n k)))).
  Proof.
    intros * Hk Hn.
    unfold populate_poly_terms.
    erewrite map_nth_error.
    f_equal.
    instantiate (1 := Nat.sub n k).
    f_equal.
    f_equal.
    f_equal.
    nia.
    assert (Hkt : k <= n).
    nia.
    f_equal.
    nia.
    rewrite list_elem_nth.
    f_equal.
    rewrite list_upto_length.
    nia.
  Qed.
  
  

  Lemma add_polynomials_populate_poly_terms_pointwise_same : 
    forall k n l x y,
    k < S (S n) ->
    (n = List.length l) ->
    nth_error (add_polynomials l x n y) k = 
    nth_error (populate_poly_terms (y :: l) x (S n)) k.
  Proof.
    intros * Hk Hn.
    assert (Hnn: n <= length l).
    nia.
    assert(Hnpt : 
    length (append_mul_polyterm_populate_terms l x n y) = S (S n)).
    erewrite append_mul_polyterm_populate_terms_length;
    reflexivity.
    assert(Hnpp: 
    length (append_mul_polypow_populate_terms l x n (- x)) = S (S n)).
    erewrite append_mul_polypow_populate_terms_lenght;
    reflexivity.
    assert (Hkt : k = O ∨ 1 <= k <= n ∨ k = S n).
    nia.
    destruct Hkt as [Hkt | [Hkt | Hkt]].
    rewrite Hkt.
    assert (Ha: nth_error (append_mul_polyterm_populate_terms l x n y) k = 
      Some ((length l - n + k)%nat, 
      Nat.sub (S n) k, 
      pow_N 1 rmul (- x) (N.of_nat (length l - n + k)),
      y * add_rlist (map mul_rlist (gen_comb l (Nat.sub n k))))).
    rewrite Hkt.
    erewrite nth_append_polyterms.
    assert (Hsn : 0 <? S n = true).
    apply Nat.ltb_lt.
    nia.
    rewrite Hsn; clear Hsn.
    repeat f_equal.
    nia.
    nia.
    assert (Hb : nth_error (append_mul_polypow_populate_terms l x n (- x)) k = 
      Some (O, S n, 1, 0)).
    rewrite Hkt.
    rewrite nth_append_polypow.
    assert (Hsn : 0 =? 0 = true).
    apply Nat.eqb_refl.
    rewrite Hsn; clear Hsn.
    reflexivity.
    nia.
    nia.
    symmetry in Ha;
    symmetry in Hb.
    pose proof @zip_list_index_some _ _ _ 
    (fun '(a, b, u, v) '(_, _, _, w) => (a, b, u, v + w))
    (append_mul_polyterm_populate_terms l x n y)
    (append_mul_polypow_populate_terms l x n (- x))
    k as Hz.
    rewrite Hnpt, Hnpp in Hz.
    specialize (Hz _ _ eq_refl Hk Ha Hb).
    unfold add_polynomials.
    rewrite Hkt in Hz.
    rewrite Hz.
    rewrite populate_poly_terms_nth_terms.
    repeat f_equal.
    repeat rewrite Nat.sub_0_r.
    ring_simplify.
    eapply gen_comb_rewrite;
    exact Hn.
    nia.
    simpl; nia.
    destruct Hkt as [Hktl Hktr].

    assert (Ha: nth_error (append_mul_polyterm_populate_terms l x n y) k = 
      Some ((length l - n + k)%nat, 
      Nat.sub (S n) k, 
      pow_N 1 rmul (- x) (N.of_nat (length l - n + k)),
      y * add_rlist (map mul_rlist (gen_comb l (Nat.sub n k))))).
    rewrite nth_append_polyterms.
    assert (Hsn : k <? S n = true).
    apply Nat.ltb_lt.
    nia.
    rewrite Hsn; clear Hsn.
    repeat f_equal.
    nia.
    nia.
    assert (Hb : nth_error (append_mul_polypow_populate_terms l x n (- x)) k = 
    Some (S (length l - (n - (k - 1))), 
    (n - (k - 1))%nat, 
    -x * pow_N 1 rmul (- x) (N.of_nat (length l - (n - (k - 1)))),
    add_rlist (map mul_rlist (gen_comb l (n - (k - 1)))))).
    rewrite nth_append_polypow.
    assert (Hkt : k =? 0 = false).
    apply Nat.eqb_neq.
    nia.
    rewrite Hkt; clear Hkt.
    f_equal.
    nia.
    nia.
    symmetry in Ha.
    symmetry in Hb.
    pose proof @zip_list_index_some _ _ _ 
    (fun '(a, b, u, v) '(_, _, _, w) => (a, b, u, v + w))
    (append_mul_polyterm_populate_terms l x n y)
    (append_mul_polypow_populate_terms l x n (- x))
    k as Hz.
    rewrite Hnpt, Hnpp in Hz.
    specialize (Hz _ _ eq_refl Hk Ha Hb).
    unfold add_polynomials.
    rewrite Hz.
    rewrite populate_poly_terms_nth_terms.
    repeat f_equal.
    assert (Htt : ((n - (k - 1)) = S n - k)%nat).
    nia.
    rewrite Htt; clear Htt.
    eapply thomas_has_proof_for_this.
    nia.
    nia.
    nia.
    simpl; nia.
    rewrite Hkt.
    assert (Ha: nth_error (append_mul_polyterm_populate_terms l x n y) k = 
    Some (S n, O, pow_N 1 rmul (- x) (N.of_nat (S n)), 0)).
    rewrite nth_append_polyterms.
    assert (Hsn : k <? S n = false).
    rewrite Hkt.
    apply Nat.ltb_irrefl.
    rewrite Hsn; clear Hsn.
    repeat f_equal.
    nia.
    nia.
    assert (Hb : nth_error (append_mul_polypow_populate_terms l x n (- x)) k = 
    Some (S (length l - (n - (k - 1))), 
    (n - (k - 1))%nat, 
    -x * pow_N 1 rmul (- x) (N.of_nat (length l - (n - (k - 1)))),
    add_rlist (map mul_rlist (gen_comb l (n - (k - 1)))))).
    rewrite nth_append_polypow.
    assert (Hwt : k =? 0 = false).
    apply Nat.eqb_neq.
    nia.
    rewrite Hwt; clear Hwt.
    f_equal.
    nia.
    nia.
    symmetry in Ha.
    symmetry in Hb.
    pose proof @zip_list_index_some _ _ _ 
    (fun '(a, b, u, v) '(_, _, _, w) => (a, b, u, v + w))
    (append_mul_polyterm_populate_terms l x n y)
    (append_mul_polypow_populate_terms l x n (- x))
    k as Hz.
    rewrite Hnpt, Hnpp in Hz.
    specialize (Hz _ _ eq_refl Hk Ha Hb).
    unfold add_polynomials.
    rewrite Hkt in Hz.
    rewrite Hz.
    rewrite populate_poly_terms_nth_terms.
    repeat f_equal.
    simpl.
    rewrite <-Hn.
    nia.
    nia.
    simpl.
    rewrite <-Hn.
    nia.
    assert (Hsnt : ((n - (S n - 1)) = O)%nat).
    nia.
    rewrite Hsnt; clear Hsnt.
    rewrite Nat.sub_diag.
    simpl.
    destruct l.
    simpl.
    ring_simplify.
    reflexivity.
    simpl.
    ring_simplify.
    reflexivity.
    nia.
    simpl; nia.
  Qed.


 

  Lemma add_polynomials_populate_poly_terms_same :
    forall n l x y, 
    n = length l -> 
    add_polynomials l x n y = populate_poly_terms (y :: l) x (S n).
  Proof.
    intros ? ? ? ? Hn.
    eapply @nth_ext_error.
    apply add_polynomials_populate_poly_terms_same_length.
    intros nt Hnt.
    eapply add_polynomials_populate_poly_terms_pointwise_same.
    rewrite add_polynomials_length in Hnt.
    nia.
    nia.
  Qed.

  

  Lemma take_nt_rewrite {A : Type} :
    forall n (t : list A), 
    n ≤ length t ->
    n = length (take n t).
  Proof.
    induction n. 
    + intros ? Hn.
      simpl.
      reflexivity.
    + intros ? Hn.
      simpl.
      destruct t.
      simpl in Hn; nia.
      simpl in Hn.
      simpl.
      f_equal.
      apply IHn.
      nia.
  Qed.  


  Fact tmp_6 : 
    let nt := [x₂; x₃; x₄] in 
    let n := 3%nat in
    let y := x₁ in
    let h := u in 
    fold_left
    (λ (a : R) '(y0, v), let '(y1, u0) := y0 in let '(_, _) := y1 in a + u0 * v)
    (populate_poly_terms nt y n) 0 * (h - y) =
    fold_left
    (λ (a : R) '(y0, v), let '(y1, u0) := y0 in let '(_, _) := y1 in a + u0 * v)
    (populate_poly_terms (h :: nt) y (S n)) 0.
  Proof.
    simpl.
    compute.
    ring_simplify.
    ring.
  Qed.



  Fact tmp_7 :
    let nt := [x₂; x₃] in 
    let n := 2%nat in
    let y := x₁ in
    let h := u in 
    fold_left (λ (a : R) '(y0, v), let '(y1, u0) := y0 in let '(_, _) := y1 in a + u0 * v)
    (populate_poly_terms nt y n) 0 * (h - y) =
    fold_left (λ (a : R) '(y0, v), let '(y1, u0) := y0 in let '(_, _) := y1 in a + u0 * v)
    (zip_with
      (λ '(y0, v),
          let
          '(y1, u0) := y0 in
          let
          '(a, b) := y1 in
            λ '(y2, w), let '(y3, _) := y2 in let '(_, _) := y3 in (a, b, u0, v + w))
      (append_mul_polyterm_populate_terms nt y n h)
      (append_mul_polypow_populate_terms nt y n (- y))) 0.
  Proof.
    simpl.
    unfold add_rlist, 
    mul_rlist.
    simpl.
    ring_simplify.
    ring.
  Qed.


  Lemma nth_error_and_map :
    forall (l₁ l₂ : list (nat * nat * R * R)),
    List.length l₁ = List.length l₂ ->
    (forall k (ul₁ ul₂ vl₁ vl₂ : R) i₁ i₂ j₁ j₂,
      Some (i₁, j₁, ul₁, vl₁) = List.nth_error l₁ k ->
      Some (i₂, j₂, ul₂, vl₂) = List.nth_error l₂ k ->
      ul₁ = ul₂) ->
    List.map (fun '(_, _, x, _) => x) l₁ = 
    List.map (fun '(_, _, y, _) => y) l₂.  
  Proof.
    induction l₁ as [|(((au, bu), cu), du) l₁].
    + intros * Ha Hf.
      destruct l₂.
      reflexivity.
      simpl in Ha.
      nia.
    + intros * Ha Hf.
      destruct l₂ as [|(((av, bv), cv), dv) l₂].
      simpl in Ha.
      nia.
      simpl.
      f_equal.
      exact (Hf O cu cv du dv au av bu bv eq_refl eq_refl).
      apply IHl₁.
      simpl in Ha.
      nia.
      intros * Hc Hd.
      exact (Hf (S k) ul₁ ul₂ vl₁ vl₂ i₁ i₂ j₁ j₂ Hc Hd).
  Qed.



  Lemma fold_left_zip_reduce : 
    forall (l₁ l₂ : list (nat * nat * R * R)),
    List.length l₁ = List.length l₂ ->
    (List.map (fun '(_, _, x, _) => x) l₁ = 
     List.map (fun '(_, _, y, _) => y) l₂) -> 
    fold_left (fun acc '(_, _, u, v) => acc + u * v)
    (zip_with (fun '(a, b, u₁, v₁) '(_, _, _, v₂) =>
      (a, b, u₁, v₁ + v₂)) l₁ l₂) 0 =
    fold_left (fun accl '(al, bl, ul, vl) => accl + ul * vl) 
    l₁ 0 + 
    fold_left (fun accr '(ar, br, ur, vr) => accr + ur * vr)
    l₂ 0.
  Proof.
    induction l₁ as [|(((au, bu), cu), du) l₁].
    + intros * Ha Hb.
      simpl in Ha.
      destruct l₂.
      simpl in Ha.
      simpl.
      ring. 
      simpl in Ha.
      nia.
    + intros * Ha Hb.
      destruct l₂ as [|(((av, bv), cv), dv) l₂].
      simpl in Ha.
      nia.
      simpl in Ha.
      simpl.
      simpl in Hb.
      inversion Hb.
      rewrite fold_left_acc.
      remember (fold_left
      (λ (a : R) '(y, v), let '(y0, u0) := y in let '(_, _) := y0 in a + u0 * v)
      (zip_with
        (λ '(y, v₁),
        let
        '(y0, u₁) := y in
         let
         '(a, b) := y0 in
          λ '(y1, v₂),
            let '(y2, _) := y1 in let '(_, _) := y2 in (a, b, u₁, v₁ + v₂))
        l₁ l₂) 0) as fl₁.
      rewrite fold_left_acc.
      remember (fold_left
      (λ (a : R) '(y, v), let '(y0, u0) := y in let '(_, _) := y0 in a + u0 * v)
      l₁ 0 ) as fl₂.
      rewrite fold_left_acc.
      subst.
      rewrite IHl₁.
      ring_simplify.
      ring.
      nia.
      assumption.
  Qed.



  Lemma equal_terms_map :
    forall n nt y h, 
    n = List.length nt -> 
    map (λ '(y0, _), let '(y1, x) := y0 in let '(_, _) := y1 in x)
    (append_mul_polyterm_populate_terms nt y n h) =
    map (λ '(y0, _), let '(y2, y1) := y0 in let '(_, _) := y2 in y1)
    (append_mul_polypow_populate_terms nt y n (- y)).
  Proof.
    intros * Hn.
    eapply nth_error_and_map.
    rewrite append_mul_polyterm_populate_terms_length.
    rewrite append_mul_polypow_populate_terms_lenght.
    reflexivity.
    intros * Ha Hb.
    destruct (append_mul_polyterm_polypow_first_three_term_same 
    _ _ _ _ _ _ _ _ _ _ _ _ _ Hn Ha Hb) as (_ & _ & Hc & _).
    exact Hc.
  Qed.





  Lemma comp_gen_ind_rewrite :
    forall n h t y, 
    (n = length t)%nat ->
    compute_poly_simp (take n t) y n * (h - y) = 
    compute_poly_simp (take (S n) (h :: t)) y (S n).
  Proof.
    intros ? ? ? ? Hn.
    assert (Hnt : n <= length t).
    nia.
    pose proof take_nt _ _ Hnt.
    assert(Htt: take (S n) (h :: t) = h :: take n t).
    reflexivity.
    rewrite Htt; 
    clear Htt.
    remember (take n t) as nt.
    rewrite <-populate_poly_term_compute_poly.
    rewrite <-populate_poly_term_compute_poly.
    unfold eval_populate_poly.
    assert (Hwt : n = length nt).
    rewrite Heqnt.
    apply take_nt_rewrite;
    try assumption.
    pose proof add_polynomials_populate_poly_terms_same 
    n nt y h Hwt as Hp.
    rewrite <-Hp.
    unfold add_polynomials.
    rewrite fold_left_zip_reduce.
    unfold append_mul_polyterm_populate_terms,
    append_mul_polypow_populate_terms.
    rewrite fold_left_app.
    simpl.
    rewrite connect_mul_polyterm_with_evalpoly.
    assert (Htt: 0 + 1 * 0 = 0).
    ring.
    rewrite Htt; clear Htt.
    rewrite connect_mul_polypow_with_evalpoly.
    unfold eval_populate_poly.
    ring.
    rewrite append_mul_polypow_populate_terms_lenght.
    rewrite append_mul_polyterm_populate_terms_length.
    reflexivity.
    eapply equal_terms_map;
    try assumption.
    simpl; nia.
    nia.
  Qed.
    
    




  Lemma compute_simp_gen : 
    forall n l y,
    (n = List.length l)%nat ->
    compute_poly_simp (take n l) y n * 
    mul_closed_poly (drop n l) y = mul_closed_poly l y.
  Proof.
    induction n. 
    + simpl.
      intros ? ? Ha.
      ring_simplify.
      reflexivity.
    + intros ? ? Ha.
      assert (Hwt : S n <= length l).
      nia.
      assert (Ht : exists h t, l = h :: t). (* S n <= lenght l*)
      destruct l. 
      simpl in Ha.
      nia.
      exists r, l. 
      reflexivity.
      destruct Ht as (h & t & Hl).
      rewrite Hl.
      rewrite Hl in Ha, Hwt.
      simpl in Ha, Hwt.
      apply Nat.succ_le_mono in Hwt.
      rewrite <-comp_gen_ind_rewrite.
      simpl.
      inversion Ha as [Hb]. 
      specialize (IHn t y Hb).
      rewrite drop_all.
      simpl.
      rewrite <-IHn.
      rewrite Hb.
      rewrite drop_all.
      simpl.
      ring.
      nia.
  Qed.
  

  


  Lemma compute_simp : 
    forall l y,
    compute_poly_simp l y (List.length l) = mul_closed_poly l y.
  Proof.
    intros ? ?.
    assert(Ht: length l = length l).
    nia.
    pose proof compute_simp_gen (List.length l)
      l y Ht as Hr.
    rewrite take_all, drop_all in Hr.
    simpl in Hr.
    ring [Hr].
  Qed.

  


    