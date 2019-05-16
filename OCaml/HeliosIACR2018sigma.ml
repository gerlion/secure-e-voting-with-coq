
type __ = Obj.t

type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

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

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)
 let rec add n0 m0 =
   match n0 with
   | O -> m0
   | S p0 -> S (add p0 m0)
end
include Coq__1

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
       | XI q0 -> XO (add_carry p0 q0)
       | XO q0 -> XI (add p0 q0)
       | XH -> XO (succ p0))
    | XO p0 ->
      (match y with
       | XI q0 -> XI (add p0 q0)
       | XO q0 -> XO (add p0 q0)
       | XH -> XI p0)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q0 -> XI (add_carry p0 q0)
       | XO q0 -> XO (add_carry p0 q0)
       | XH -> XI (succ p0))
    | XO p0 ->
      (match y with
       | XI q0 -> XO (add_carry p0 q0)
       | XO q0 -> XI (add p0 q0)
       | XH -> XO (succ p0))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
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
       | XI q0 -> double_mask (sub_mask p0 q0)
       | XO q0 -> succ_double_mask (sub_mask p0 q0)
       | XH -> IsPos (XO p0))
    | XO p0 ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p0 q0)
       | XO q0 -> double_mask (sub_mask p0 q0)
       | XH -> IsPos (pred_double p0))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p0 q0)
       | XO q0 -> double_mask (sub_mask p0 q0)
       | XH -> IsPos (pred_double p0))
    | XO p0 ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p0 q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p0 q0)
       | XH -> double_pred_mask p0)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p0 -> add y (XO (mul p0 y))
    | XO p0 -> XO (mul p0 y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r0 x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q0 -> compare_cont r0 p0 q0
       | XO q0 -> compare_cont Gt p0 q0
       | XH -> Gt)
    | XO p0 ->
      (match y with
       | XI q0 -> compare_cont Lt p0 q0
       | XO q0 -> compare_cont r0 p0 q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r0
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p0 q0 =
    match p0 with
    | XI p1 -> (match q0 with
                | XI q1 -> eqb p1 q1
                | _ -> False)
    | XO p1 -> (match q0 with
                | XO q1 -> eqb p1 q1
                | _ -> False)
    | XH -> (match q0 with
             | XH -> True
             | _ -> False)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op0 p0 a =
    match p0 with
    | XI p1 -> op0 a (iter_op op0 p1 (op0 a a))
    | XO p1 -> iter_op op0 p1 (op0 a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)
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
       | XI q0 -> double (pos_sub p0 q0)
       | XO q0 -> succ_double (pos_sub p0 q0)
       | XH -> Zpos (XO p0))
    | XO p0 ->
      (match y with
       | XI q0 -> pred_double (pos_sub p0 q0)
       | XO q0 -> double (pos_sub p0 q0)
       | XH -> Zpos (Coq_Pos.pred_double p0))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Coq_Pos.pred_double q0)
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

  (** val eqb : z -> z -> bool **)

  let rec eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> True
             | _ -> False)
    | Zpos p0 -> (match y with
                  | Zpos q0 -> Coq_Pos.eqb p0 q0
                  | _ -> False)
    | Zneg p0 -> (match y with
                  | Zneg q0 -> Coq_Pos.eqb p0 q0
                  | _ -> False)

  (** val to_nat : z -> nat **)

  let to_nat = function
  | Zpos p0 -> Coq_Pos.to_nat p0
  | _ -> O

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p0 -> Zpos p0

  (** val pos_div_eucl : positive -> z -> (z, z) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q0, r0) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r0) (Zpos XH) in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q0), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b)))
    | XO a' ->
      let Pair (q0, r0) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r0 in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q0), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b)))
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
         let Pair (q0, r0) = pos_div_eucl a' (Zpos b') in
         (match r0 with
          | Z0 -> Pair ((opp q0), Z0)
          | _ -> Pair ((opp (add q0 (Zpos XH))), (add b r0))))
    | Zneg a' ->
      (match b with
       | Z0 -> Pair (Z0, Z0)
       | Zpos _ ->
         let Pair (q0, r0) = pos_div_eucl a' b in
         (match r0 with
          | Z0 -> Pair ((opp q0), Z0)
          | _ -> Pair ((opp (add q0 (Zpos XH))), (sub b r0)))
       | Zneg b' ->
         let Pair (q0, r0) = pos_div_eucl a' (Zpos b') in Pair (q0, (opp r0)))

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let Pair (_, r0) = div_eucl a b in r0
 end

module Sigma =
 struct
  type form = { coq_Rel : (__ -> __ -> bool); add : (__ -> __ -> __);
                zero : __; inv : (__ -> __); bool_eq : (__ -> __ -> bool);
                disjoint : (__ -> __ -> bool);
                coq_P0 : (__ -> __ -> __ -> (__, __) prod);
                coq_V0 : ((__, __) prod -> __ -> ((__, __) prod, __) prod);
                coq_P1 : (((__, __) prod, __) prod -> __ -> __ -> (((__, __)
                         prod, __) prod, __) prod);
                coq_V1 : ((((__, __) prod, __) prod, __) prod -> bool);
                simulator : (__ -> __ -> __ -> (((__, __) prod, __) prod, __)
                            prod); simMap : (__ -> __ -> __ -> __ -> __);
                extractor : (__ -> __ -> __ -> __ -> __) }

  type coq_S = __

  type coq_W = __

  (** val coq_Rel : form -> coq_S -> coq_W -> bool **)

  let coq_Rel x = x.coq_Rel

  type coq_C = __

  type coq_R = __

  type coq_E = __

  (** val add : form -> coq_E -> coq_E -> coq_E **)

  let add x = x.add

  (** val zero : form -> coq_E **)

  let zero x = x.zero

  (** val inv : form -> coq_E -> coq_E **)

  let inv x = x.inv

  (** val bool_eq : form -> coq_E -> coq_E -> bool **)

  let bool_eq x = x.bool_eq

  (** val disjoint : form -> coq_E -> coq_E -> bool **)

  let disjoint x = x.disjoint

  type coq_T = __

  (** val coq_P0 : form -> coq_S -> coq_R -> coq_W -> (coq_S, coq_C) prod **)

  let coq_P0 x = x.coq_P0

  (** val coq_V0 :
      form -> (coq_S, coq_C) prod -> coq_E -> ((coq_S, coq_C) prod, coq_E)
      prod **)

  let coq_V0 x = x.coq_V0

  (** val coq_P1 :
      form -> ((coq_S, coq_C) prod, coq_E) prod -> coq_R -> coq_W ->
      (((coq_S, coq_C) prod, coq_E) prod, coq_T) prod **)

  let coq_P1 x = x.coq_P1

  (** val coq_V1 :
      form -> (((coq_S, coq_C) prod, coq_E) prod, coq_T) prod -> bool **)

  let coq_V1 x = x.coq_V1

  (** val simulator :
      form -> coq_S -> coq_T -> coq_E -> (((coq_S, coq_C) prod, coq_E) prod,
      coq_T) prod **)

  let simulator x = x.simulator

  (** val simMap : form -> coq_S -> coq_R -> coq_E -> coq_W -> coq_T **)

  let simMap x = x.simMap

  (** val extractor : form -> coq_T -> coq_T -> coq_E -> coq_E -> coq_W **)

  let extractor x = x.extractor
 end

(** val eqSigmaProtocol : Sigma.form -> Sigma.form **)

let eqSigmaProtocol sig1 =
  let eq_Rel = fun s w ->
    match sig1.Sigma.coq_Rel (fst s) w with
    | True -> sig1.Sigma.coq_Rel (snd s) w
    | False -> False
  in
  let eq_P0 = fun s r0 w ->
    let c1 = snd (sig1.Sigma.coq_P0 (fst s) r0 w) in
    let c2 = snd (sig1.Sigma.coq_P0 (snd s) r0 w) in Pair (s, (Pair (c1, c2)))
  in
  let eq_V0 = fun p0 e ->
    let s1 = fst (fst p0) in
    let c1 = fst (snd p0) in
    Pair (p0, (snd (Pair ((sig1.Sigma.coq_V0 (Pair (s1, c1))), e))))
  in
  let eq_P1 = fun v0 r0 w ->
    let s1 = fst (fst (fst v0)) in
    let c1 = fst (snd (fst v0)) in
    let e = snd v0 in
    Pair (v0, (snd (sig1.Sigma.coq_P1 (Pair ((Pair (s1, c1)), e)) r0 w)))
  in
  let eq_V1 = fun p1 ->
    let s1 = fst (fst (fst (fst p1))) in
    let s2 = snd (fst (fst (fst p1))) in
    let c1 = fst (snd (fst (fst p1))) in
    let c2 = snd (snd (fst (fst p1))) in
    let e = snd (fst p1) in
    let r0 = snd p1 in
    (match sig1.Sigma.coq_V1 (Pair ((Pair ((Pair (s1, c1)), e)), r0)) with
     | True -> sig1.Sigma.coq_V1 (Pair ((Pair ((Pair (s2, c2)), e)), r0))
     | False -> False)
  in
  let eq_simulator = fun s r0 e ->
    let s1 = fst s in
    let s2 = snd s in
    let sim1 = sig1.Sigma.simulator s1 r0 e in
    let sim2 = sig1.Sigma.simulator s2 r0 e in
    let c1 = snd (fst (fst sim1)) in
    let c2 = snd (fst (fst sim2)) in
    let e1 = snd (fst sim1) in
    let r1 = snd sim1 in Pair ((Pair ((Pair (s, (Pair (c1, c2)))), e1)), r1)
  in
  let eq_simMap = fun s r0 e w -> sig1.Sigma.simMap (fst s) r0 e w in
  let eq_extractor = fun r1 r2 e1 e2 -> sig1.Sigma.extractor r1 r2 e1 e2 in
  { Sigma.coq_Rel = (Obj.magic eq_Rel); Sigma.add = sig1.Sigma.add;
  Sigma.zero = sig1.Sigma.zero; Sigma.inv = sig1.Sigma.inv; Sigma.bool_eq =
  sig1.Sigma.bool_eq; Sigma.disjoint = sig1.Sigma.disjoint; Sigma.coq_P0 =
  (Obj.magic eq_P0); Sigma.coq_V0 = (Obj.magic eq_V0); Sigma.coq_P1 =
  (Obj.magic eq_P1); Sigma.coq_V1 = (Obj.magic eq_V1); Sigma.simulator =
  (Obj.magic eq_simulator); Sigma.simMap = (Obj.magic eq_simMap);
  Sigma.extractor = eq_extractor }

(** val disSigmaProtocol : Sigma.form -> Sigma.form **)

let disSigmaProtocol sig1 =
  let dis_Rel = fun s w ->
    match sig1.Sigma.coq_Rel (fst s) w with
    | True -> True
    | False -> sig1.Sigma.coq_Rel (snd s) w
  in
  let dis_P0 = fun s rzeb w ->
    let e = snd rzeb in
    let z0 = snd (fst rzeb) in
    let r0 = fst (fst rzeb) in
    let hc1 = snd (sig1.Sigma.coq_P0 (fst s) r0 w) in
    let hc2 = snd (sig1.Sigma.coq_P0 (snd s) r0 w) in
    let sc1 = snd (fst (fst (sig1.Sigma.simulator (fst s) z0 e))) in
    let sc2 = snd (fst (fst (sig1.Sigma.simulator (snd s) z0 e))) in
    (match sig1.Sigma.coq_Rel (fst s) w with
     | True -> Pair (s, (Pair (hc1, sc2)))
     | False -> Pair (s, (Pair (sc1, hc2))))
  in
  let dis_V0 = fun p0 e -> Pair (p0, e) in
  let dis_P1 = fun v0 rzeb w ->
    let s1 = fst (fst (fst v0)) in
    let s2 = snd (fst (fst v0)) in
    let c1 = fst (snd (fst v0)) in
    let c2 = snd (snd (fst v0)) in
    let e = snd v0 in
    let se = snd rzeb in
    let z0 = snd (fst rzeb) in
    let r0 = fst (fst rzeb) in
    let e1 =
      snd
        (sig1.Sigma.coq_V0 (Pair (s1, c1))
          (sig1.Sigma.add e (sig1.Sigma.inv se)))
    in
    let ht1 = snd (sig1.Sigma.coq_P1 (Pair ((Pair (s1, c1)), e1)) r0 w) in
    let ht2 = snd (sig1.Sigma.coq_P1 (Pair ((Pair (s2, c2)), e1)) r0 w) in
    let st1 = snd (sig1.Sigma.simulator s1 z0 se) in
    let st2 = snd (sig1.Sigma.simulator s2 z0 se) in
    (match sig1.Sigma.coq_Rel s1 w with
     | True -> Pair (v0, (Pair ((Pair (ht1, e1)), st2)))
     | False -> Pair (v0, (Pair ((Pair (st1, se)), ht2))))
  in
  let dis_V1 = fun p1 ->
    let s1 = fst (fst (fst (fst p1))) in
    let s2 = snd (fst (fst (fst p1))) in
    let c1 = fst (snd (fst (fst p1))) in
    let c2 = snd (snd (fst (fst p1))) in
    let e = snd (fst p1) in
    let e1 = snd (fst (snd p1)) in
    let e2 = sig1.Sigma.add e (sig1.Sigma.inv e1) in
    let r1 = fst (fst (snd p1)) in
    let r2 = snd (snd p1) in
    (match sig1.Sigma.coq_V1 (Pair ((Pair ((Pair (s1, c1)), e1)), r1)) with
     | True -> sig1.Sigma.coq_V1 (Pair ((Pair ((Pair (s2, c2)), e2)), r2))
     | False -> False)
  in
  let dis_simulator = fun s t e ->
    let s1 = fst s in
    let s2 = snd s in
    let e1 = snd (fst t) in
    let e2 = sig1.Sigma.add e (sig1.Sigma.inv e1) in
    let r1 = fst (fst t) in
    let r2 = snd t in
    let sim1 = sig1.Sigma.simulator s1 r1 e1 in
    let sim2 = sig1.Sigma.simulator s2 r2 e2 in
    let c1 = snd (fst (fst sim1)) in
    let c2 = snd (fst (fst sim2)) in
    let sr1 = snd sim1 in
    let sr2 = snd sim2 in
    let se1 = snd (fst sim1) in
    Pair ((Pair ((Pair (s, (Pair (c1, c2)))), e)), (Pair ((Pair (sr1, se1)),
    sr2)))
  in
  let dis_simMap = fun s rtcb e w ->
    let r0 = fst (fst rtcb) in
    let t = snd (fst rtcb) in
    let c = snd rtcb in
    let h1 =
      sig1.Sigma.simMap (fst s) r0 (sig1.Sigma.add e (sig1.Sigma.inv c)) w
    in
    let h2 =
      sig1.Sigma.simMap (snd s) r0 (sig1.Sigma.add e (sig1.Sigma.inv c)) w
    in
    (match sig1.Sigma.coq_Rel (fst s) w with
     | True -> Pair ((Pair (h1, (sig1.Sigma.add e (sig1.Sigma.inv c)))), t)
     | False -> Pair ((Pair (t, c)), h2))
  in
  let dis_extractor = fun r1 r2 c1 c2 ->
    let e1 = snd (fst r1) in
    let e2 = sig1.Sigma.add c1 (sig1.Sigma.inv e1) in
    let e3 = snd (fst r2) in
    let e4 = sig1.Sigma.add c2 (sig1.Sigma.inv e3) in
    let t1 = fst (fst r1) in
    let t2 = snd r1 in
    let t3 = fst (fst r2) in
    let t4 = snd r2 in
    (match negb (sig1.Sigma.bool_eq e1 e3) with
     | True -> sig1.Sigma.extractor t1 t3 e1 e3
     | False -> sig1.Sigma.extractor t2 t4 e2 e4)
  in
  { Sigma.coq_Rel = (Obj.magic dis_Rel); Sigma.add = sig1.Sigma.add;
  Sigma.zero = sig1.Sigma.zero; Sigma.inv = sig1.Sigma.inv; Sigma.bool_eq =
  sig1.Sigma.bool_eq; Sigma.disjoint = sig1.Sigma.disjoint; Sigma.coq_P0 =
  (Obj.magic dis_P0); Sigma.coq_V0 = dis_V0; Sigma.coq_P1 =
  (Obj.magic dis_P1); Sigma.coq_V1 = (Obj.magic dis_V1); Sigma.simulator =
  (Obj.magic dis_simulator); Sigma.simMap = (Obj.magic dis_simMap);
  Sigma.extractor = (Obj.magic dis_extractor) }

(** val parSigmaProtocol : Sigma.form -> Sigma.form -> Sigma.form **)

let parSigmaProtocol sig1 sig2 =
  let par_Rel = fun s w ->
    match sig1.Sigma.coq_Rel (fst s) (fst w) with
    | True -> sig2.Sigma.coq_Rel (snd s) (snd w)
    | False -> False
  in
  let par_add = fun e1 e2 -> Pair ((sig1.Sigma.add (fst e1) (fst e2)),
    (sig2.Sigma.add (snd e1) (snd e2)))
  in
  let par_zero = Pair (sig1.Sigma.zero, sig2.Sigma.zero) in
  let par_bool_eq = fun e1 e2 ->
    match sig1.Sigma.bool_eq (fst e1) (fst e2) with
    | True -> sig2.Sigma.bool_eq (snd e1) (snd e2)
    | False -> False
  in
  let par_inv = fun e -> Pair ((sig1.Sigma.inv (fst e)),
    (sig2.Sigma.inv (snd e)))
  in
  let par_disjoint = fun e1 e2 ->
    match sig1.Sigma.disjoint (fst e1) (fst e2) with
    | True -> sig2.Sigma.disjoint (snd e1) (snd e2)
    | False -> False
  in
  let par_P0 = fun s r0 w ->
    let c1 = snd (sig1.Sigma.coq_P0 (fst s) (fst r0) (fst w)) in
    let c2 = snd (sig2.Sigma.coq_P0 (snd s) (snd r0) (snd w)) in
    Pair (s, (Pair (c1, c2)))
  in
  let par_V0 = fun p0 e ->
    let s1 = fst (fst p0) in
    let s2 = snd (fst p0) in
    let c1 = fst (snd p0) in
    let c2 = snd (snd p0) in
    Pair (p0, (Pair ((snd (sig1.Sigma.coq_V0 (Pair (s1, c1)) (fst e))),
    (snd (sig2.Sigma.coq_V0 (Pair (s2, c2)) (snd e))))))
  in
  let par_P1 = fun v0 r0 w ->
    let s1 = fst (fst (fst v0)) in
    let s2 = snd (fst (fst v0)) in
    let c1 = fst (snd (fst v0)) in
    let c2 = snd (snd (fst v0)) in
    let e = snd v0 in
    Pair (v0, (Pair
    ((snd
       (sig1.Sigma.coq_P1 (Pair ((Pair (s1, c1)), (fst e))) (fst r0) (fst w))),
    (snd
      (sig2.Sigma.coq_P1 (Pair ((Pair (s2, c2)), (snd e))) (snd r0) (snd w))))))
  in
  let par_V1 = fun p1 ->
    let s1 = fst (fst (fst (fst p1))) in
    let s2 = snd (fst (fst (fst p1))) in
    let c1 = fst (snd (fst (fst p1))) in
    let c2 = snd (snd (fst (fst p1))) in
    let e = snd (fst p1) in
    let r0 = snd p1 in
    (match sig1.Sigma.coq_V1 (Pair ((Pair ((Pair (s1, c1)), (fst e))),
             (fst r0))) with
     | True ->
       sig2.Sigma.coq_V1 (Pair ((Pair ((Pair (s2, c2)), (snd e))), (snd r0)))
     | False -> False)
  in
  let par_simulator = fun s r0 e ->
    let s1 = fst s in
    let s2 = snd s in
    let sim1 = sig1.Sigma.simulator s1 (fst r0) (fst e) in
    let sim2 = sig2.Sigma.simulator s2 (snd r0) (snd e) in
    let c1 = snd (fst (fst sim1)) in
    let c2 = snd (fst (fst sim2)) in
    let e1 = snd (fst sim1) in
    let e2 = snd (fst sim2) in
    let r1 = snd sim1 in
    let r2 = snd sim2 in
    Pair ((Pair ((Pair (s, (Pair (c1, c2)))), (Pair (e1, e2)))), (Pair (r1,
    r2)))
  in
  let par_simMap = fun s r0 e w -> Pair
    ((sig1.Sigma.simMap (fst s) (fst r0) (fst e) (fst w)),
    (sig2.Sigma.simMap (snd s) (snd r0) (snd e) (snd w)))
  in
  let par_extractor = fun r1 r2 e1 e2 -> Pair
    ((sig1.Sigma.extractor (fst r1) (fst r2) (fst e1) (fst e2)),
    (sig2.Sigma.extractor (snd r1) (snd r2) (snd e1) (snd e2)))
  in
  { Sigma.coq_Rel = (Obj.magic par_Rel); Sigma.add = (Obj.magic par_add);
  Sigma.zero = (Obj.magic par_zero); Sigma.inv = (Obj.magic par_inv);
  Sigma.bool_eq = (Obj.magic par_bool_eq); Sigma.disjoint =
  (Obj.magic par_disjoint); Sigma.coq_P0 = (Obj.magic par_P0); Sigma.coq_V0 =
  (Obj.magic par_V0); Sigma.coq_P1 = (Obj.magic par_P1); Sigma.coq_V1 =
  (Obj.magic par_V1); Sigma.simulator = (Obj.magic par_simulator);
  Sigma.simMap = (Obj.magic par_simMap); Sigma.extractor =
  (Obj.magic par_extractor) }

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
    let Pair (q0, r0) = div_eucl0 a' b in
    (match q0 with
     | N0 ->
       (match r0 with
        | N0 -> Pair (N0, N0)
        | Npos r1 ->
          (match is_lt (XI r1) b with
           | True -> Pair (N0, (Npos (XI r1)))
           | False -> Pair ((Npos XH), (pminusN (XI r1) b))))
     | Npos q1 ->
       (match r0 with
        | N0 ->
          (match is_lt XH b with
           | True -> Pair ((Npos (XO q1)), (Npos XH))
           | False -> Pair ((Npos (XI q1)), N0))
        | Npos r1 ->
          (match is_lt (XI r1) b with
           | True -> Pair ((Npos (XO q1)), (Npos (XI r1)))
           | False -> Pair ((Npos (XI q1)), (pminusN (XI r1) b)))))
  | XO a' ->
    let Pair (q0, r0) = div_eucl0 a' b in
    (match q0 with
     | N0 ->
       (match r0 with
        | N0 -> Pair (N0, N0)
        | Npos r1 ->
          (match is_lt (XO r1) b with
           | True -> Pair (N0, (Npos (XO r1)))
           | False -> Pair ((Npos XH), (pminusN (XO r1) b))))
     | Npos q1 ->
       (match r0 with
        | N0 -> Pair ((Npos (XO q1)), N0)
        | Npos r1 ->
          (match is_lt (XO r1) b with
           | True -> Pair ((Npos (XO q1)), (Npos (XO r1)))
           | False -> Pair ((Npos (XI q1)), (pminusN (XO r1) b)))))
  | XH ->
    (match is_lt XH b with
     | True -> Pair (N0, (Npos XH))
     | False -> Pair ((Npos XH), N0))

(** val egcd_log2 :
    positive -> positive -> positive -> ((z, z) prod, positive) prod option **)

let rec egcd_log2 a b c =
  let Pair (q0, n0) = div_eucl0 a b in
  (match n0 with
   | N0 -> Some (Pair ((Pair (Z0, (Zpos XH))), b))
   | Npos r0 ->
     let Pair (q', n1) = div_eucl0 b r0 in
     (match n1 with
      | N0 -> Some (Pair ((Pair ((Zpos XH), (Z.opp (Z.of_N q0)))), r0))
      | Npos r' ->
        (match c with
         | XI c' ->
           (match egcd_log2 r0 r' c' with
            | Some p0 ->
              let Pair (p1, w') = p0 in
              let Pair (u', v') = p1 in
              let u = Z.sub u' (Z.mul v' (Z.of_N q')) in
              Some (Pair ((Pair (u, (Z.sub v' (Z.mul (Z.of_N q0) u)))), w'))
            | None -> None)
         | XO c' ->
           (match egcd_log2 r0 r' c' with
            | Some p0 ->
              let Pair (p1, w') = p0 in
              let Pair (u', v') = p1 in
              let u = Z.sub u' (Z.mul v' (Z.of_N q')) in
              Some (Pair ((Pair (u, (Z.sub v' (Z.mul (Z.of_N q0) u)))), w'))
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

(** val zero0 : z -> znz **)

let zero0 n0 =
  Z.modulo Z0 n0

(** val one : z -> znz **)

let one n0 =
  Z.modulo (Zpos XH) n0

(** val add0 : z -> znz -> znz -> znz **)

let add0 n0 v1 v2 =
  Z.modulo (Z.add (val0 n0 v1) (val0 n0 v2)) n0

(** val mul0 : z -> znz -> znz -> znz **)

let mul0 n0 v1 v2 =
  Z.modulo (Z.mul (val0 n0 v1) (val0 n0 v2)) n0

(** val opp0 : z -> znz -> znz **)

let opp0 n0 v =
  Z.modulo (Z.opp (val0 n0 v)) n0

(** val inv0 : z -> znz -> znz **)

let inv0 p0 v =
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

(** val q : z **)

let q =
  Zpos (XI (XO (XI (XO (XO (XI (XO (XO (XI (XO (XI (XI (XI (XO (XO (XI (XI
    (XO (XI (XI (XO (XO (XO (XI (XI (XI (XI (XI (XI (XO (XO (XI (XI (XO (XI
    (XO (XO (XI (XI (XO (XI (XI (XO (XI (XO (XO (XO (XI (XI (XI (XI (XI (XO
    (XI (XI (XI (XO (XI (XO (XO (XO (XO (XO (XI (XO (XI (XO (XI (XI (XO (XO
    (XO (XI (XO (XO (XO (XO (XI (XO (XO (XO (XO (XI (XI (XI (XO (XI (XI (XO
    (XI (XO (XI (XI (XO (XI (XO (XI (XO (XO (XI (XI (XI (XO (XI (XO (XI (XO
    (XO (XO (XI (XO (XI (XI (XO (XI (XO (XO (XO (XO (XI (XI (XI (XO (XI (XO
    (XI (XI (XO (XO (XO (XO (XO (XO (XO (XO (XI (XO (XO (XO (XO (XO (XO (XI
    (XI (XO (XI (XO (XI (XO (XI (XI (XO (XO (XO (XO (XO (XI (XO (XO (XI (XI
    (XO (XI (XI (XO (XO (XO (XO (XO (XO (XI (XO (XI (XO (XI (XO (XI (XO (XO
    (XO (XI (XO (XO (XI (XO (XO (XO (XI (XI (XI (XO (XO (XO (XI (XI (XI (XO
    (XO (XI (XI (XI (XO (XO (XO (XO (XI (XO (XO (XO (XO (XI (XO (XI (XI (XO
    (XO (XI (XO (XO (XI (XI (XI (XI (XO (XI (XI (XO (XI (XO (XI (XI (XI (XI
    (XO (XI (XI (XO (XO (XI (XO (XI (XI (XI (XO (XI (XO (XO (XI (XI (XI (XI
    (XO (XO (XO (XO
    XH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

type fp = znz

(** val fpMul : fp -> fp -> fp **)

let fpMul =
  mul0 p

(** val fpOne : fp **)

let fpOne =
  one p

type r = znz

(** val radd : r -> r -> r **)

let radd =
  add0 q

(** val rzero : r **)

let rzero =
  zero0 q

(** val rbool_eq : r -> r -> bool **)

let rbool_eq a b =
  Z.eqb (val0 q a) (val0 q b)

(** val rinv : r -> r **)

let rinv =
  opp0 q

(** val rmul : r -> r -> r **)

let rmul =
  mul0 q

(** val rmulInv : r -> r **)

let rmulInv =
  inv0 q

(** val naive_power : fp -> nat -> fp **)

let rec naive_power a = function
| O -> fpOne
| S p0 -> fpMul a (naive_power a p0)

type m = fp

(** val mdot : m -> m -> m **)

let mdot a b =
  mul0 p a b

(** val mbool_eq : m -> m -> bool **)

let mbool_eq a b =
  Z.eqb (val0 p a) (val0 p b)

(** val minv : m -> m **)

let minv a =
  inv0 p a

(** val op : m -> r -> m **)

let op a b =
  naive_power a (Z.to_nat (val0 q b))

(** val dLog : (m, m) prod -> r -> bool **)

let dLog s w =
  let g = fst s in let gtox = snd s in mbool_eq gtox (op g w)

(** val valid_P0 : (m, m) prod -> r -> r -> ((m, m) prod, m) prod **)

let valid_P0 ggtox r0 _ =
  let g = fst ggtox in Pair (ggtox, (op g r0))

(** val valid_V0 :
    ((m, m) prod, m) prod -> r -> (((m, m) prod, m) prod, r) prod **)

let valid_V0 ggtoxgtor c =
  Pair (ggtoxgtor, c)

(** val valid_P1 :
    (((m, m) prod, m) prod, r) prod -> r -> r -> ((((m, m) prod, m) prod, r)
    prod, r) prod **)

let valid_P1 ggtoxgtorc r0 x =
  let c = snd ggtoxgtorc in let s = radd r0 (rmul c x) in Pair (ggtoxgtorc, s)

(** val valid_V1 : ((((m, m) prod, m) prod, r) prod, r) prod -> bool **)

let valid_V1 ggtoxgtorcs =
  let g = fst (fst (fst (fst ggtoxgtorcs))) in
  let gtox = snd (fst (fst (fst ggtoxgtorcs))) in
  let gtor = snd (fst (fst ggtoxgtorcs)) in
  let c = snd (fst ggtoxgtorcs) in
  let s = snd ggtoxgtorcs in mbool_eq (op g s) (mdot (op gtox c) gtor)

(** val simulator_mapper : (m, m) prod -> r -> r -> r -> r **)

let simulator_mapper _ r0 c x =
  radd r0 (rmul x c)

(** val simulator0 :
    (m, m) prod -> r -> r -> ((((m, m) prod, m) prod, r) prod, r) prod **)

let simulator0 ggtox z0 e =
  let g = fst ggtox in
  let gtox = snd ggtox in
  Pair ((Pair ((Pair (ggtox, (mdot (op g z0) (minv (op gtox e))))), e)), z0)

(** val extractor0 : r -> r -> r -> r -> r **)

let extractor0 s1 s2 c1 c2 =
  rmul (radd s1 (rinv s2)) (rmulInv (radd c1 (rinv c2)))

(** val disjoint0 : r -> r -> bool **)

let disjoint0 c1 c2 =
  negb (rbool_eq c1 c2)

(** val dLogForm : Sigma.form **)

let dLogForm =
  { Sigma.coq_Rel = (Obj.magic dLog); Sigma.add = (Obj.magic radd);
    Sigma.zero = (Obj.magic rzero); Sigma.inv = (Obj.magic rinv);
    Sigma.bool_eq = (Obj.magic rbool_eq); Sigma.disjoint =
    (Obj.magic disjoint0); Sigma.coq_P0 = (Obj.magic valid_P0);
    Sigma.coq_V0 = (Obj.magic valid_V0); Sigma.coq_P1 = (Obj.magic valid_P1);
    Sigma.coq_V1 = (Obj.magic valid_V1); Sigma.simulator =
    (Obj.magic simulator0); Sigma.simMap = (Obj.magic simulator_mapper);
    Sigma.extractor = (Obj.magic extractor0) }

(** val emptyRel : m -> r -> bool **)

let emptyRel _ _ =
  True

(** val empty_P0 : m -> r -> r -> (m, m) prod **)

let empty_P0 g _ _ =
  Pair (g, g)

(** val empty_V0 : (m, m) prod -> r -> ((m, m) prod, r) prod **)

let empty_V0 g c =
  Pair (g, c)

(** val empty_P1 :
    ((m, m) prod, r) prod -> r -> r -> (((m, m) prod, r) prod, r) prod **)

let empty_P1 g _ _ =
  Pair (g, (snd g))

(** val empty_V1 : (((m, m) prod, r) prod, r) prod -> bool **)

let empty_V1 _ =
  True

(** val empty_simulator_mapper : m -> r -> r -> r -> r **)

let empty_simulator_mapper _ r0 _ _ =
  r0

(** val empty_simulator : m -> r -> r -> (((m, m) prod, r) prod, r) prod **)

let empty_simulator g _ e =
  Pair ((Pair ((Pair (g, g)), e)), e)

(** val empty_mapper : r -> r -> r -> r -> r **)

let empty_mapper s1 s2 c1 c2 =
  rmul (radd s1 (rinv s2)) (rmulInv (radd c1 (rinv c2)))

(** val emptyForm : Sigma.form **)

let emptyForm =
  { Sigma.coq_Rel = (Obj.magic emptyRel); Sigma.add = (Obj.magic radd);
    Sigma.zero = (Obj.magic rzero); Sigma.inv = (Obj.magic rinv);
    Sigma.bool_eq = (Obj.magic rbool_eq); Sigma.disjoint =
    (Obj.magic disjoint0); Sigma.coq_P0 = (Obj.magic empty_P0);
    Sigma.coq_V0 = (Obj.magic empty_V0); Sigma.coq_P1 = (Obj.magic empty_P1);
    Sigma.coq_V1 = (Obj.magic empty_V1); Sigma.simulator =
    (Obj.magic empty_simulator); Sigma.simMap =
    (Obj.magic empty_simulator_mapper); Sigma.extractor =
    (Obj.magic empty_mapper) }

(** val dHTForm : Sigma.form **)

let dHTForm =
  eqSigmaProtocol dLogForm

(** val dHTDisForm : Sigma.form **)

let dHTDisForm =
  disSigmaProtocol dHTForm

(** val overallFormApproval : (m, m) prod list -> Sigma.form **)

let rec overallFormApproval = function
| Nil -> emptyForm
| Cons (_, b) -> parSigmaProtocol (overallFormApproval b) dHTDisForm
