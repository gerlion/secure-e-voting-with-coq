
type __ = Obj.t

type bool =
| True
| False

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p0 -> XO (succ p0)
  | XO p0 -> XI p0
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q -> XO (add_carry p0 q)
       | XO q -> XI (add p0 q)
       | XH -> XO (succ p0))
    | XO p0 ->
      (match y with
       | XI q -> XI (add p0 q)
       | XO q -> XO (add p0 q)
       | XH -> XI p0)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q -> XI (add_carry p0 q)
       | XO q -> XO (add_carry p0 q)
       | XH -> XI (succ p0))
    | XO p0 ->
      (match y with
       | XI q -> XO (add_carry p0 q)
       | XO q -> XI (add p0 q)
       | XH -> XO (succ p0))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p0 -> XI (XO p0)
  | XO p0 -> XI (pred_double p0)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p0 -> IsPos (XI p0)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p0 -> IsPos (XO p0)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p0 -> IsPos (XO (XO p0))
  | XO p0 -> IsPos (XO (pred_double p0))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q -> double_mask (sub_mask p0 q)
       | XO q -> succ_double_mask (sub_mask p0 q)
       | XH -> IsPos (XO p0))
    | XO p0 ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p0 q)
       | XO q -> double_mask (sub_mask p0 q)
       | XH -> IsPos (pred_double p0))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p0 q)
       | XO q -> double_mask (sub_mask p0 q)
       | XH -> IsPos (pred_double p0))
    | XO p0 ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p0 q)
       | XO q -> succ_double_mask (sub_mask_carry p0 q)
       | XH -> double_pred_mask p0)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p0 -> add y (XO (mul p0 y))
    | XO p0 -> XO (mul p0 y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q -> compare_cont r p0 q
       | XO q -> compare_cont Gt p0 q
       | XH -> Gt)
    | XO p0 ->
      (match y with
       | XI q -> compare_cont Lt p0 q
       | XO q -> compare_cont r p0 q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p0 -> Zpos (XO p0)
  | Zneg p0 -> Zneg (XO p0)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p0 -> Zpos (XI p0)
  | Zneg p0 -> Zneg (Coq_Pos.pred_double p0)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p0 -> Zpos (Coq_Pos.pred_double p0)
  | Zneg p0 -> Zneg (XI p0)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q -> double (pos_sub p0 q)
       | XO q -> succ_double (pos_sub p0 q)
       | XH -> Zpos (XO p0))
    | XO p0 ->
      (match y with
       | XI q -> pred_double (pos_sub p0 q)
       | XO q -> double (pos_sub p0 q)
       | XH -> Zpos (Coq_Pos.pred_double p0))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Coq_Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m0 n0 =
    add m0 (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p0 -> Zpos p0

  (** val pos_div_eucl : positive -> z -> (z, z) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b)))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b)))
    | XH ->
      (match leb (Zpos (XO XH)) b with
       | True -> Pair (Z0, (Zpos XH))
       | False -> Pair ((Zpos XH), Z0))

  (** val div_eucl : z -> z -> (z, z) prod **)

  let div_eucl a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> Pair (Z0, Z0)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> Pair (Z0, Z0)
       | Zpos _ ->
         let Pair (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in Pair (q, (opp r)))

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let Pair (_, r) = div_eucl a b in r
 end

module Sigma =
 struct
  type coq_S = __
 end

(** val pminusN : positive -> positive -> n **)

let pminusN x y =
  match Coq_Pos.sub_mask x y with
  | Coq_Pos.IsPos k -> Npos k
  | _ -> N0

(** val is_lt : positive -> positive -> bool **)

let is_lt n0 m0 =
  match Coq_Pos.compare n0 m0 with
  | Lt -> True
  | _ -> False

(** val div_eucl0 : positive -> positive -> (n, n) prod **)

let rec div_eucl0 a b =
  match a with
  | XI a' ->
    let Pair (q, r) = div_eucl0 a' b in
    (match q with
     | N0 ->
       (match r with
        | N0 -> Pair (N0, N0)
        | Npos r0 ->
          (match is_lt (XI r0) b with
           | True -> Pair (N0, (Npos (XI r0)))
           | False -> Pair ((Npos XH), (pminusN (XI r0) b))))
     | Npos q0 ->
       (match r with
        | N0 ->
          (match is_lt XH b with
           | True -> Pair ((Npos (XO q0)), (Npos XH))
           | False -> Pair ((Npos (XI q0)), N0))
        | Npos r0 ->
          (match is_lt (XI r0) b with
           | True -> Pair ((Npos (XO q0)), (Npos (XI r0)))
           | False -> Pair ((Npos (XI q0)), (pminusN (XI r0) b)))))
  | XO a' ->
    let Pair (q, r) = div_eucl0 a' b in
    (match q with
     | N0 ->
       (match r with
        | N0 -> Pair (N0, N0)
        | Npos r0 ->
          (match is_lt (XO r0) b with
           | True -> Pair (N0, (Npos (XO r0)))
           | False -> Pair ((Npos XH), (pminusN (XO r0) b))))
     | Npos q0 ->
       (match r with
        | N0 -> Pair ((Npos (XO q0)), N0)
        | Npos r0 ->
          (match is_lt (XO r0) b with
           | True -> Pair ((Npos (XO q0)), (Npos (XO r0)))
           | False -> Pair ((Npos (XI q0)), (pminusN (XO r0) b)))))
  | XH ->
    (match is_lt XH b with
     | True -> Pair (N0, (Npos XH))
     | False -> Pair ((Npos XH), N0))

(** val egcd_log2 :
    positive -> positive -> positive -> ((z, z) prod, positive) prod option **)

let rec egcd_log2 a b c =
  let Pair (q, n0) = div_eucl0 a b in
  (match n0 with
   | N0 -> Some (Pair ((Pair (Z0, (Zpos XH))), b))
   | Npos r ->
     let Pair (q', n1) = div_eucl0 b r in
     (match n1 with
      | N0 -> Some (Pair ((Pair ((Zpos XH), (Z.opp (Z.of_N q)))), r))
      | Npos r' ->
        (match c with
         | XI c' ->
           (match egcd_log2 r r' c' with
            | Some p0 ->
              let Pair (p1, w') = p0 in
              let Pair (u', v') = p1 in
              let u = Z.sub u' (Z.mul v' (Z.of_N q')) in
              Some (Pair ((Pair (u, (Z.sub v' (Z.mul (Z.of_N q) u)))), w'))
            | None -> None)
         | XO c' ->
           (match egcd_log2 r r' c' with
            | Some p0 ->
              let Pair (p1, w') = p0 in
              let Pair (u', v') = p1 in
              let u = Z.sub u' (Z.mul v' (Z.of_N q')) in
              Some (Pair ((Pair (u, (Z.sub v' (Z.mul (Z.of_N q) u)))), w'))
            | None -> None)
         | XH -> None)))

(** val egcd : positive -> positive -> ((z, z) prod, positive) prod **)

let egcd a b =
  match egcd_log2 a b (XO b) with
  | Some p0 -> p0
  | None -> Pair ((Pair ((Zpos XH), (Zpos XH))), XH)

(** val zegcd : z -> z -> ((z, z) prod, z) prod **)

let zegcd a b =
  match a with
  | Z0 ->
    (match b with
     | Z0 -> Pair ((Pair (Z0, Z0)), Z0)
     | Zpos _ -> Pair ((Pair (Z0, (Zpos XH))), b)
     | Zneg _ -> Pair ((Pair (Z0, (Zneg XH))), (Z.opp b)))
  | Zpos a0 ->
    (match b with
     | Z0 -> Pair ((Pair ((Zpos XH), Z0)), a)
     | Zpos b0 -> let Pair (p0, w) = egcd a0 b0 in Pair (p0, (Zpos w))
     | Zneg b0 ->
       let Pair (p0, w) = egcd a0 b0 in
       let Pair (u, v) = p0 in Pair ((Pair (u, (Z.opp v))), (Zpos w)))
  | Zneg a0 ->
    (match b with
     | Z0 -> Pair ((Pair ((Zneg XH), Z0)), (Z.opp a))
     | Zpos b0 ->
       let Pair (p0, w) = egcd a0 b0 in
       let Pair (u, v) = p0 in Pair ((Pair ((Z.opp u), v)), (Zpos w))
     | Zneg b0 ->
       let Pair (p0, w) = egcd a0 b0 in
       let Pair (u, v) = p0 in Pair ((Pair ((Z.opp u), (Z.opp v))), (Zpos w)))

type znz = z
  (* singleton inductive, whose constructor was mkznz *)

(** val val0 : z -> znz -> z **)

let val0 _ z0 =
  z0

(** val mul0 : z -> znz -> znz -> znz **)

let mul0 n0 v1 v2 =
  Z.modulo (Z.mul (val0 n0 v1) (val0 n0 v2)) n0

(** val inv : z -> znz -> znz **)

let inv p0 v =
  Z.modulo (fst (fst (zegcd (val0 p0 v) p0))) p0

(** val p : z **)

let p =
  Zpos (XI (XI (XI (XO (XI (XO (XI (XI (XO (XO (XI (XO (XO (XI (XO (XO (XO
    (XO (XO (XO (XI (XI (XO (XO (XO (XI (XI (XI (XI (XI (XO (XO (XI (XI (XI
    (XI (XI (XI (XI (XO (XO (XO (XO (XO (XO (XI (XI (XO (XI (XI (XI (XO (XI
    (XO (XO (XO (XI (XO (XO (XI (XI (XO (XI (XI (XO (XO (XI (XI (XO (XI (XO
    (XI (XI (XO (XO (XI (XI (XO (XO (XI (XI (XO (XI (XO (XO (XO (XO (XI (XI
    (XI (XI (XO (XI (XI (XI (XO (XI (XI (XI (XI (XI (XO (XO (XO (XO (XI (XO
    (XO (XO (XI (XO (XO (XO (XO (XO (XO (XO (XI (XO (XI (XI (XO (XO (XI (XI
    (XO (XO (XI (XO (XO (XO (XO (XI (XI (XI (XO (XI (XO (XI (XO (XI (XI (XO
    (XO (XO (XO (XO (XI (XO (XI (XO (XI (XI (XI (XO (XI (XO (XO (XO (XI (XI
    (XO (XO (XO (XI (XI (XI (XO (XI (XO (XO (XI (XO (XO (XI (XI (XI (XI (XO
    (XI (XI (XO (XO (XO (XO (XI (XO (XO (XO (XO (XI (XO (XO (XI (XI (XI (XO
    (XO (XI (XI (XI (XI (XI (XO (XO (XO (XI (XO (XO (XO (XI (XI (XO (XO (XO
    (XI (XO (XI (XI (XO (XI (XO (XO (XO (XO (XO (XI (XI (XO (XI (XO (XI (XI
    (XO (XI (XO (XO (XO (XI (XI (XO (XO (XO (XO (XO (XI (XI (XI (XI (XI (XI
    (XO (XI (XI (XO (XO (XO (XO (XO (XO (XO (XI (XO (XI (XO (XO (XI (XO (XO
    (XI (XI (XO (XO (XI (XO (XI (XO (XI (XI (XI (XI (XI (XO (XO (XO (XO (XI
    (XO (XI (XI (XO (XI (XO (XI (XI (XI (XI (XO (XI (XI (XO (XI (XO (XI (XO
    (XO (XO (XO (XI (XI (XO (XI (XO (XO (XO (XI (XI (XI (XI (XI (XI (XO (XO
    (XO (XI (XI (XO (XO (XI (XI (XO (XO (XI (XI (XO (XO (XO (XI (XO (XO (XI
    (XO (XO (XO (XO (XI (XO (XI (XO (XI (XI (XI (XO (XO (XI (XO (XI (XI (XO
    (XO (XI (XI (XO (XO (XO (XO (XI (XI (XI (XO (XO (XO (XO (XO (XI (XO (XI
    (XI (XI (XI (XI (XO (XI (XI (XO (XO (XO (XO (XO (XO (XO (XI (XI (XO (XI
    (XO (XO (XO (XO (XO (XO (XI (XI (XO (XI (XO (XI (XI (XI (XI (XO (XO (XO
    (XI (XO (XI (XI (XI (XO (XI (XO (XI (XI (XI (XI (XO (XI (XI (XI (XO (XI
    (XO (XI (XI (XO (XI (XO (XI (XI (XO (XI (XI (XI (XI (XO (XI (XI (XO (XO
    (XI (XO (XO (XI (XO (XI (XI (XO (XI (XI (XO (XI (XI (XI (XI (XO (XI (XO
    (XI (XI (XI (XI (XO (XI (XI (XO (XO (XO (XI (XI (XO (XO (XO (XI (XI (XI
    (XO (XO (XI (XO (XO (XI (XI (XI (XI (XI (XI (XO (XI (XO (XO (XO (XI (XO
    (XI (XI (XO (XI (XO (XI (XI (XI (XI (XI (XO (XI (XO (XO (XO (XO (XI (XO
    (XI (XI (XI (XO (XO (XO (XI (XO (XI (XO (XO (XO (XO (XI (XI (XI (XI (XI
    (XO (XI (XI (XO (XO (XI (XO (XO (XO (XI (XO (XO (XO (XI (XO (XO (XI (XO
    (XO (XO (XI (XO (XI (XI (XO (XO (XO (XI (XO (XO (XI (XO (XI (XI (XO (XO
    (XI (XI (XO (XO (XI (XO (XO (XO (XI (XO (XI (XI (XI (XI (XO (XO (XI (XI
    (XI (XI (XO (XO (XI (XO (XO (XO (XI (XO (XI (XI (XI (XI (XI (XI (XI (XI
    (XI (XO (XO (XI (XI (XO (XO (XO (XI (XO (XI (XI (XI (XI (XO (XO (XO (XI
    (XO (XO (XO (XO (XI (XO (XI (XO (XO (XI (XI (XI (XI (XO (XO (XO (XI (XO
    (XO (XO (XO (XI (XI (XO (XI (XI (XI (XI (XI (XO (XI (XO (XO (XI (XO (XI
    (XI (XI (XI (XI (XI (XI (XI (XI (XI (XO (XO (XI (XO (XO (XI (XO (XO (XO
    (XI (XO (XO (XO (XO (XO (XO (XI (XO (XO (XO (XO (XO (XI (XO (XI (XO (XO
    (XO (XO (XO (XI (XO (XO (XO (XO (XO (XI (XO (XO (XI (XI (XO (XI (XI (XI
    (XI (XO (XO (XI (XI (XI (XI (XI (XI (XI (XI (XO (XO (XI (XO (XO (XI (XO
    (XI (XO (XI (XI (XO (XI (XI (XO (XO (XI (XO (XO (XI (XO (XI (XO (XI (XI
    (XI (XI (XO (XO (XO (XO (XI (XO (XI (XO (XO (XO (XO (XO (XI (XI (XI (XO
    (XI (XI (XI (XI (XO (XO (XO (XI (XI (XI (XO (XI (XO (XO (XI (XO (XI (XO
    (XI (XO (XI (XO (XO (XO (XO (XO (XO (XI (XI (XI (XO (XO (XO (XI (XO (XI
    (XO (XI (XO (XO (XI (XO (XI (XI (XO (XI (XO (XI (XO (XI (XI (XO (XO (XO
    (XI (XO (XO (XO (XI (XO (XO (XI (XO (XI (XI (XO (XO (XO (XI (XO (XI (XI
    (XO (XO (XI (XO (XI (XO (XO (XO (XI (XO (XI (XO (XO (XI (XO (XO (XO (XI
    (XI (XI (XI (XO (XI (XO (XI (XI (XI (XI (XO (XO (XO (XI (XI (XO (XO (XO
    (XI (XI (XI (XO (XI (XI (XI (XI (XO (XI (XO (XO (XO (XI (XO (XI (XI (XO
    (XO (XI (XI (XI (XO (XO (XO (XO (XO (XO (XO (XI (XO (XI (XI (XO (XO (XI
    (XO (XI (XO (XI (XO (XI (XO (XO (XI (XO (XI (XI (XO (XO (XO (XO (XO (XI
    (XI (XI (XO (XI (XO (XI (XI (XO (XO (XO (XO (XI (XI (XI (XO (XO (XO (XI
    (XO (XI (XO (XI (XO (XO (XI (XI (XO (XO (XI (XI (XO (XI (XI (XO (XO (XI
    (XO (XI (XI (XI (XO (XI (XO (XO (XI (XO (XO (XI (XI (XO (XO (XI (XO (XO
    (XI (XI (XO (XO (XO (XI (XO (XO (XI (XO (XI (XI (XO (XI (XI (XO (XO (XO
    (XO (XO (XO (XO (XI (XO (XO (XO (XO (XI (XO (XI (XI (XO (XO (XO (XO (XI
    (XI (XI (XO (XO (XO (XO (XO (XO (XO (XI (XI (XO (XO (XO (XI (XI (XI (XI
    (XO (XO (XO (XO (XI (XO (XI (XO (XO (XO (XO (XO (XO (XO (XI (XI (XO (XI
    (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XI (XO (XI (XO (XO (XI (XI (XO
    (XI (XI (XI (XO (XO (XO (XO (XO (XI (XI (XI (XO (XI (XO (XO (XI (XI (XO
    (XI (XI (XI (XI (XI (XI (XO (XO (XO (XI (XO (XO (XO (XI (XO (XI (XI (XI
    (XO (XI (XO (XO (XO (XO (XI (XI (XO (XI (XI (XO (XO (XO (XO (XO (XO (XI
    (XO (XI (XO (XO (XI (XO (XI (XO (XI (XI (XI (XI (XO (XO (XI (XO (XO (XI
    (XO (XO (XO (XI (XO (XI (XO (XO (XO (XO (XO (XI (XO (XI (XI (XO (XO (XI
    (XI (XO (XO (XI (XO (XO (XI (XO (XI (XI (XI (XO (XO (XO (XO (XI (XI (XI
    (XO (XO (XI (XO (XO (XI (XI (XO (XI (XO (XO (XI (XO (XI (XO (XO (XI (XO
    (XO (XI (XI (XI (XO (XI (XI (XO (XO (XI (XO (XI (XI (XO (XO (XI (XO (XO
    (XO (XI (XO (XO (XO (XO (XI (XI (XI (XO (XO (XI (XO (XO (XO (XO (XO (XO
    (XI (XI (XI (XI (XI (XI (XO (XI (XO (XI (XO (XO (XO (XO (XI (XI (XO (XO
    (XI (XI (XI (XI (XI (XI (XO (XI (XO (XO (XI (XI (XO (XO (XI (XI (XO (XI
    (XI (XO (XO (XI (XI (XI (XI (XI (XO (XO (XI (XI (XI (XI (XI (XO (XO (XO
    (XO (XI (XO (XI (XI (XO (XI (XI (XO (XO (XO (XI (XI (XI (XO (XI (XO (XI
    (XI (XI (XI (XO (XI (XO (XI (XO (XO (XO (XI (XI (XO (XI (XI (XO (XO (XO
    (XI (XO (XI (XI (XI (XO (XI (XO (XI (XI (XO (XI (XI (XI (XO (XO (XI (XI
    (XO (XI (XO (XI (XO (XI (XI (XI (XO (XO (XO (XI (XO (XO (XO (XO (XI (XI
    (XO (XI (XO (XO (XI (XO (XI (XI (XO (XO (XO (XI (XO (XO (XO (XO (XO (XI
    (XO (XI (XO (XO (XI (XO (XO (XI (XI (XI (XO (XO (XO (XI (XI (XO (XO (XI
    (XI (XO (XO (XI (XO (XO (XI (XO (XI (XI (XI (XI (XO (XO (XI (XI (XI (XI
    (XO (XI (XI (XO (XO (XO (XI (XI (XO (XI (XI (XO (XI (XO (XI (XI (XO (XO
    (XI (XO (XO (XO (XO (XO (XO (XO (XI (XO (XI (XI (XO (XO (XO (XI (XO (XI
    (XI (XO (XI (XO (XO (XO (XI (XO (XO (XI (XO (XO (XI (XO (XO (XO (XO (XO
    (XO (XO (XO (XO (XI (XO (XI (XO (XI (XI (XI (XO (XO (XO (XI (XI (XI (XI
    (XO (XO (XO (XI (XI (XI (XO (XO (XI (XI (XO (XI (XI (XO (XI (XO (XI (XI
    (XO (XI (XO (XI (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XI (XI (XO (XI
    (XO (XI (XO (XO (XI (XI (XO (XI (XI (XI (XI (XO (XO (XO (XI (XI (XI (XO
    (XO (XO (XI (XO (XI (XO (XO (XI (XO (XI (XI (XO (XO (XO (XO (XO (XO (XI
    (XI (XO (XI (XI (XO (XO (XI (XI (XI (XO (XO (XO (XO (XI (XO (XO (XO (XO
    (XI (XO (XO (XI (XO (XI (XO (XI (XI (XI (XI (XI (XI (XO (XI (XO (XI (XO
    (XI (XO (XI (XO (XO (XI (XI (XO (XI (XI (XO (XO (XI (XI (XO (XO (XI (XO
    (XO (XO (XI (XI (XO (XI (XO (XO (XO (XO (XO (XO (XO (XI (XO (XI (XI (XI
    (XO (XI (XO (XI (XI (XO (XI (XO (XO (XO (XI (XI (XO (XO (XO (XO (XI (XI
    (XO (XI (XO (XO (XO (XI (XI (XI (XO (XO (XI (XI (XI (XO (XI (XI (XI (XO
    (XO (XO (XO (XI (XI (XI (XI (XI (XI (XO (XO (XO (XO (XI (XI (XI (XI (XO
    (XI (XI (XO (XO (XI (XI (XI (XO (XO (XO (XI (XO (XO (XI (XI (XO (XO (XI
    (XI (XI (XI (XI (XO (XI (XI (XI (XI (XO (XI (XO (XO (XI (XI (XO (XI (XO
    (XI (XI (XI (XI (XI (XI (XO (XO (XO (XO (XI (XI (XO (XI (XO (XI (XO (XI
    (XI (XI (XI (XO (XO (XI (XI (XI (XO (XO (XO (XO (XI (XI (XI (XI (XO (XO
    (XO (XO (XI (XO (XI (XI (XO (XI (XO (XO (XO (XI (XO (XI (XI (XO (XO (XO
    (XO (XI (XO (XI (XI (XI (XO (XI (XI (XI (XI (XO (XI (XI (XO (XO (XO (XI
    (XO (XO (XO (XI (XI (XO (XI (XO (XI (XO (XI (XO (XO (XO (XO (XO (XI (XO
    (XO (XO (XO (XO (XO (XO (XI (XI (XO (XI (XI (XI (XI (XO (XO (XO (XO (XO
    (XI (XI (XO (XI (XO (XO (XI (XO (XO (XO (XI (XO (XI (XI (XO (XO (XO (XI
    (XI (XO (XO (XI (XI (XO (XO (XI (XI (XI (XI (XI (XO (XI (XI (XO (XI (XO
    (XI (XO (XO (XO (XO (XI (XO (XO (XI (XI (XI (XI (XI (XI (XO (XO (XI (XI
    (XI (XI (XI (XO (XO (XO (XI (XI (XI (XI (XI (XO (XI (XI (XI (XO (XI (XO
    (XI (XO (XO (XO (XI (XO (XO (XI (XI (XO (XI (XO (XO (XO (XI (XO (XO (XI
    (XI (XO (XO (XO (XI (XI (XI (XI (XO (XO (XO (XI (XO (XI (XO (XI (XI (XO
    (XO (XI (XI (XI (XO (XI (XO (XO (XO (XO (XI (XI (XO (XO (XO (XI (XI (XO
    (XO (XO (XI (XO (XO (XO (XI (XO (XO (XI (XO (XI (XO (XI (XI (XI (XI (XO
    (XI (XO (XO (XO (XO (XO (XI (XO (XI (XO (XI (XI (XO (XI (XO (XI (XI (XO
    (XI (XI (XI (XO (XO (XI (XI (XI (XI (XO (XO (XI (XO (XI (XI (XO (XI (XI
    (XO (XO (XI (XO (XI (XO (XI (XO (XI (XI (XO (XO (XO (XO (XO (XO (XO (XI
    (XO (XO (XI (XI (XO (XI (XO (XI (XO (XO (XO (XO (XO (XO
    XH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

type fp = znz

type m = fp

(** val mdot : m -> m -> m **)

let mdot a b =
  mul0 p a b

(** val minv : m -> m **)

let minv a =
  inv p a

(** val oneOrZero : Sigma.coq_S -> Sigma.coq_S **)

let oneOrZero s =
  let g = fst (fst (Obj.magic s)) in
  let h = snd (fst (Obj.magic s)) in
  let gtox = fst (snd (Obj.magic s)) in
  let htox = snd (snd (Obj.magic s)) in
  Obj.magic (Pair ((Pair ((Pair (g, gtox)), (Pair (h, htox)))), (Pair ((Pair
    (g, gtox)), (Pair (h, (mdot htox (minv g))))))))

(** val oneOrZeroCipher : m -> m -> (m, m) prod -> Sigma.coq_S **)

let oneOrZeroCipher g h c =
  oneOrZero (Obj.magic (Pair ((Pair (g, h)), c)))

(** val statmentFormApproval : m -> m -> (m, m) prod list -> Sigma.coq_S **)

let rec statmentFormApproval g h = function
| Nil -> Obj.magic g
| Cons (a, b) ->
  Obj.magic (Pair ((statmentFormApproval g h b), (oneOrZeroCipher g h a)))
