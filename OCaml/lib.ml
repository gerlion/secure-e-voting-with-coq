
type __ = Obj.t

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

type comparison =
| Eq
| Lt
| Gt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : Big.big_int -> Big.big_int **)

  let rec succ = Big.succ

  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)

  let rec add = Big.add

  (** val add_carry : Big.big_int -> Big.big_int -> Big.big_int **)

  and add_carry x y =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 -> Big.doubleplusone (add_carry p0 q0))
        (fun q0 -> Big.double (add_carry p0 q0))
        (fun _ -> Big.doubleplusone (succ p0))
        y)
      (fun p0 ->
      Big.positive_case
        (fun q0 -> Big.double (add_carry p0 q0))
        (fun q0 -> Big.doubleplusone (add p0 q0))
        (fun _ -> Big.double (succ p0))
        y)
      (fun _ ->
      Big.positive_case
        (fun q0 -> Big.doubleplusone (succ q0))
        (fun q0 -> Big.double (succ q0))
        (fun _ -> Big.doubleplusone Big.one)
        y)
      x

  (** val pred_double : Big.big_int -> Big.big_int **)

  let rec pred_double x =
    Big.positive_case
      (fun p0 -> Big.doubleplusone (Big.double p0))
      (fun p0 -> Big.doubleplusone (pred_double p0))
      (fun _ -> Big.one)
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos Big.one
  | IsPos p0 -> IsPos (Big.doubleplusone p0)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p0 -> IsPos (Big.double p0)
  | x0 -> x0

  (** val double_pred_mask : Big.big_int -> mask **)

  let double_pred_mask x =
    Big.positive_case
      (fun p0 -> IsPos (Big.double (Big.double p0)))
      (fun p0 -> IsPos (Big.double (pred_double p0)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : Big.big_int -> Big.big_int -> mask **)

  let rec sub_mask x y =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 -> double_mask (sub_mask p0 q0))
        (fun q0 -> succ_double_mask (sub_mask p0 q0))
        (fun _ -> IsPos (Big.double p0))
        y)
      (fun p0 ->
      Big.positive_case
        (fun q0 -> succ_double_mask (sub_mask_carry p0 q0))
        (fun q0 -> double_mask (sub_mask p0 q0))
        (fun _ -> IsPos (pred_double p0))
        y)
      (fun _ ->
      Big.positive_case
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : Big.big_int -> Big.big_int -> mask **)

  and sub_mask_carry x y =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 -> succ_double_mask (sub_mask_carry p0 q0))
        (fun q0 -> double_mask (sub_mask p0 q0))
        (fun _ -> IsPos (pred_double p0))
        y)
      (fun p0 ->
      Big.positive_case
        (fun q0 -> double_mask (sub_mask_carry p0 q0))
        (fun q0 -> succ_double_mask (sub_mask_carry p0 q0))
        (fun _ -> double_pred_mask p0)
        y)
      (fun _ -> IsNeg)
      x

  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)

  let rec mul = Big.mult

  (** val compare_cont :
      comparison -> Big.big_int -> Big.big_int -> comparison **)

  let rec compare_cont = fun c x y -> Big.compare_case c Lt Gt x y

  (** val compare : Big.big_int -> Big.big_int -> comparison **)

  let compare = fun x y -> Big.compare_case Eq Lt Gt x y

  (** val eqb : Big.big_int -> Big.big_int -> bool **)

  let rec eqb p0 q0 =
    Big.positive_case
      (fun p1 ->
      Big.positive_case
        (fun q1 -> eqb p1 q1)
        (fun _ -> false)
        (fun _ -> false)
        q0)
      (fun p1 ->
      Big.positive_case
        (fun _ -> false)
        (fun q1 -> eqb p1 q1)
        (fun _ -> false)
        q0)
      (fun _ ->
      Big.positive_case
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q0)
      p0
 end

module Z =
 struct
  (** val double : Big.big_int -> Big.big_int **)

  let double x =
    Big.z_case
      (fun _ -> Big.zero)
      (fun p0 -> (Big.double p0))
      (fun p0 -> Big.opp (Big.double p0))
      x

  (** val succ_double : Big.big_int -> Big.big_int **)

  let succ_double x =
    Big.z_case
      (fun _ -> Big.one)
      (fun p0 -> (Big.doubleplusone p0))
      (fun p0 -> Big.opp (Coq_Pos.pred_double p0))
      x

  (** val pred_double : Big.big_int -> Big.big_int **)

  let pred_double x =
    Big.z_case
      (fun _ -> Big.opp Big.one)
      (fun p0 -> (Coq_Pos.pred_double p0))
      (fun p0 -> Big.opp (Big.doubleplusone p0))
      x

  (** val pos_sub : Big.big_int -> Big.big_int -> Big.big_int **)

  let rec pos_sub x y =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 -> double (pos_sub p0 q0))
        (fun q0 -> succ_double (pos_sub p0 q0))
        (fun _ -> (Big.double p0))
        y)
      (fun p0 ->
      Big.positive_case
        (fun q0 -> pred_double (pos_sub p0 q0))
        (fun q0 -> double (pos_sub p0 q0))
        (fun _ -> (Coq_Pos.pred_double p0))
        y)
      (fun _ ->
      Big.positive_case
        (fun q0 -> Big.opp (Big.double q0))
        (fun q0 -> Big.opp (Coq_Pos.pred_double q0))
        (fun _ -> Big.zero)
        y)
      x

  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)

  let add = Big.add

  (** val opp : Big.big_int -> Big.big_int **)

  let opp = Big.opp

  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)

  let sub = Big.sub

  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)

  let mul = Big.mult

  (** val compare : Big.big_int -> Big.big_int -> comparison **)

  let compare = Big.compare_case Eq Lt Gt

  (** val leb : Big.big_int -> Big.big_int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : Big.big_int -> Big.big_int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : Big.big_int -> Big.big_int -> bool **)

  let rec eqb x y =
    Big.z_case
      (fun _ ->
      Big.z_case
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p0 ->
      Big.z_case
        (fun _ -> false)
        (fun q0 -> Coq_Pos.eqb p0 q0)
        (fun _ -> false)
        y)
      (fun p0 ->
      Big.z_case
        (fun _ -> false)
        (fun _ -> false)
        (fun q0 -> Coq_Pos.eqb p0 q0)
        y)
      x

  (** val of_N : Big.big_int -> Big.big_int **)

  let of_N = fun p -> p

  (** val pos_div_eucl :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)

  let rec pos_div_eucl a b =
    Big.positive_case
      (fun a' ->
      let (q0, r0) = pos_div_eucl a' b in
      let r' = add (mul (Big.double Big.one) r0) Big.one in
      if ltb r' b
      then ((mul (Big.double Big.one) q0), r')
      else ((add (mul (Big.double Big.one) q0) Big.one), (sub r' b)))
      (fun a' ->
      let (q0, r0) = pos_div_eucl a' b in
      let r' = mul (Big.double Big.one) r0 in
      if ltb r' b
      then ((mul (Big.double Big.one) q0), r')
      else ((add (mul (Big.double Big.one) q0) Big.one), (sub r' b)))
      (fun _ ->
      if leb (Big.double Big.one) b
      then (Big.zero, Big.one)
      else (Big.one, Big.zero))
      a

  (** val div_eucl :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)

  let div_eucl a b =
    Big.z_case
      (fun _ -> (Big.zero, Big.zero))
      (fun a' ->
      Big.z_case
        (fun _ -> (Big.zero, Big.zero))
        (fun _ -> pos_div_eucl a' b)
        (fun b' ->
        let (q0, r0) = pos_div_eucl a' b' in
        (Big.z_case
           (fun _ -> ((opp q0), Big.zero))
           (fun _ -> ((opp (add q0 Big.one)), (add b r0)))
           (fun _ -> ((opp (add q0 Big.one)), (add b r0)))
           r0))
        b)
      (fun a' ->
      Big.z_case
        (fun _ -> (Big.zero, Big.zero))
        (fun _ ->
        let (q0, r0) = pos_div_eucl a' b in
        (Big.z_case
           (fun _ -> ((opp q0), Big.zero))
           (fun _ -> ((opp (add q0 Big.one)), (sub b r0)))
           (fun _ -> ((opp (add q0 Big.one)), (sub b r0)))
           r0))
        (fun b' -> let (q0, r0) = pos_div_eucl a' b' in (q0, (opp r0)))
        b)
      a

  (** val modulo : Big.big_int -> Big.big_int -> Big.big_int **)

  let modulo a b =
    Big_int.mod_big_int a b
 end

module Sigma =
 struct
  type 'e form = { coq_Rel : (__ -> __ -> bool); add : ('e -> 'e -> 'e);
                   zero : 'e; inv : ('e -> 'e); bool_eq : ('e -> 'e -> bool);
                   disjoint : ('e -> 'e -> bool);
                   coq_P0 : (__ -> __ -> __ -> __ * __);
                   coq_V0 : ((__ * __) -> 'e -> (__ * __) * 'e);
                   coq_P1 : (((__ * __) * 'e) -> __ -> __ ->
                            ((__ * __) * 'e) * __);
                   coq_V1 : ((((__ * __) * 'e) * __) -> bool);
                   simulator : (__ -> __ -> 'e -> ((__ * __) * 'e) * __);
                   simMap : (__ -> __ -> 'e -> __ -> __);
                   extractor : (__ -> __ -> 'e -> 'e -> __) }

  type 'e coq_S = __

  type 'e coq_W = __

  (** val coq_Rel : 'a1 form -> 'a1 coq_S -> 'a1 coq_W -> bool **)

  let coq_Rel x = x.coq_Rel

  type 'e coq_C = __

  type 'e coq_R = __

  (** val add : 'a1 form -> 'a1 -> 'a1 -> 'a1 **)

  let add x = x.add

  (** val zero : 'a1 form -> 'a1 **)

  let zero x = x.zero

  (** val inv : 'a1 form -> 'a1 -> 'a1 **)

  let inv x = x.inv

  (** val bool_eq : 'a1 form -> 'a1 -> 'a1 -> bool **)

  let bool_eq x = x.bool_eq

  (** val disjoint : 'a1 form -> 'a1 -> 'a1 -> bool **)

  let disjoint x = x.disjoint

  type 'e coq_T = __

  (** val coq_P0 :
      'a1 form -> 'a1 coq_S -> 'a1 coq_R -> 'a1 coq_W -> 'a1 coq_S * 'a1 coq_C **)

  let coq_P0 x = x.coq_P0

  (** val coq_V0 :
      'a1 form -> ('a1 coq_S * 'a1 coq_C) -> 'a1 -> ('a1 coq_S * 'a1
      coq_C) * 'a1 **)

  let coq_V0 x = x.coq_V0

  (** val coq_P1 :
      'a1 form -> (('a1 coq_S * 'a1 coq_C) * 'a1) -> 'a1 coq_R -> 'a1 coq_W
      -> (('a1 coq_S * 'a1 coq_C) * 'a1) * 'a1 coq_T **)

  let coq_P1 x = x.coq_P1

  (** val coq_V1 :
      'a1 form -> ((('a1 coq_S * 'a1 coq_C) * 'a1) * 'a1 coq_T) -> bool **)

  let coq_V1 x = x.coq_V1

  (** val simulator :
      'a1 form -> 'a1 coq_S -> 'a1 coq_T -> 'a1 -> (('a1 coq_S * 'a1
      coq_C) * 'a1) * 'a1 coq_T **)

  let simulator x = x.simulator

  (** val simMap :
      'a1 form -> 'a1 coq_S -> 'a1 coq_R -> 'a1 -> 'a1 coq_W -> 'a1 coq_T **)

  let simMap x = x.simMap

  (** val extractor :
      'a1 form -> 'a1 coq_T -> 'a1 coq_T -> 'a1 -> 'a1 -> 'a1 coq_W **)

  let extractor x = x.extractor
 end

(** val eqSigmaProtocol : 'a1 Sigma.form -> 'a1 Sigma.form **)

let eqSigmaProtocol sig1 =
  let eq_Rel = fun s w ->
    (&&) (sig1.Sigma.coq_Rel (fst s) w) (sig1.Sigma.coq_Rel (snd s) w)
  in
  let eq_P0 = fun s r0 w ->
    let c1 = snd (sig1.Sigma.coq_P0 (fst s) r0 w) in
    let c2 = snd (sig1.Sigma.coq_P0 (snd s) r0 w) in (s, (c1, c2))
  in
  let eq_V0 = fun p0 e ->
    let s1 = fst (fst p0) in
    let c1 = fst (snd p0) in (p0, (snd ((sig1.Sigma.coq_V0 (s1, c1)), e)))
  in
  let eq_P1 = fun v0 r0 w ->
    let s1 = fst (fst (fst v0)) in
    let c1 = fst (snd (fst v0)) in
    let e = snd v0 in (v0, (snd (sig1.Sigma.coq_P1 ((s1, c1), e) r0 w)))
  in
  let eq_V1 = fun p1 ->
    let s1 = fst (fst (fst (fst p1))) in
    let s2 = snd (fst (fst (fst p1))) in
    let c1 = fst (snd (fst (fst p1))) in
    let c2 = snd (snd (fst (fst p1))) in
    let e = snd (fst p1) in
    let r0 = snd p1 in
    (&&) (sig1.Sigma.coq_V1 (((s1, c1), e), r0))
      (sig1.Sigma.coq_V1 (((s2, c2), e), r0))
  in
  let eq_simulator = fun s r0 e ->
    let s1 = fst s in
    let s2 = snd s in
    let sim1 = sig1.Sigma.simulator s1 r0 e in
    let sim2 = sig1.Sigma.simulator s2 r0 e in
    let c1 = snd (fst (fst sim1)) in
    let c2 = snd (fst (fst sim2)) in
    let e1 = snd (fst sim1) in let r1 = snd sim1 in (((s, (c1, c2)), e1), r1)
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

(** val disSigmaProtocol : 'a1 Sigma.form -> 'a1 Sigma.form **)

let disSigmaProtocol sig1 =
  let dis_Rel = fun s w ->
    (||) (sig1.Sigma.coq_Rel (fst s) w) (sig1.Sigma.coq_Rel (snd s) w)
  in
  let dis_P0 = fun s rzeb w ->
    let e = snd rzeb in
    let z = snd (fst rzeb) in
    let r0 = fst (fst rzeb) in
    let hc1 = snd (sig1.Sigma.coq_P0 (fst s) r0 w) in
    let hc2 = snd (sig1.Sigma.coq_P0 (snd s) r0 w) in
    let sc1 = snd (fst (fst (sig1.Sigma.simulator (fst s) z e))) in
    let sc2 = snd (fst (fst (sig1.Sigma.simulator (snd s) z e))) in
    if sig1.Sigma.coq_Rel (fst s) w then (s, (hc1, sc2)) else (s, (sc1, hc2))
  in
  let dis_V0 = fun p0 e -> (p0, e) in
  let dis_P1 = fun v0 rzeb w ->
    let s1 = fst (fst (fst v0)) in
    let s2 = snd (fst (fst v0)) in
    let c1 = fst (snd (fst v0)) in
    let c2 = snd (snd (fst v0)) in
    let e = snd v0 in
    let se = snd rzeb in
    let z = snd (fst rzeb) in
    let r0 = fst (fst rzeb) in
    let e1 =
      snd (sig1.Sigma.coq_V0 (s1, c1) (sig1.Sigma.add e (sig1.Sigma.inv se)))
    in
    let ht1 = snd (sig1.Sigma.coq_P1 ((s1, c1), e1) r0 w) in
    let ht2 = snd (sig1.Sigma.coq_P1 ((s2, c2), e1) r0 w) in
    let st1 = snd (sig1.Sigma.simulator s1 z se) in
    let st2 = snd (sig1.Sigma.simulator s2 z se) in
    if sig1.Sigma.coq_Rel s1 w
    then (v0, ((ht1, e1), st2))
    else (v0, ((st1, se), ht2))
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
    (&&) (sig1.Sigma.coq_V1 (((s1, c1), e1), r1))
      (sig1.Sigma.coq_V1 (((s2, c2), e2), r2))
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
    let se1 = snd (fst sim1) in (((s, (c1, c2)), e), ((sr1, se1), sr2))
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
    if sig1.Sigma.coq_Rel (fst s) w
    then ((h1, (sig1.Sigma.add e (sig1.Sigma.inv c))), t)
    else ((t, c), h2)
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
    if negb (sig1.Sigma.bool_eq e1 e3)
    then sig1.Sigma.extractor t1 t3 e1 e3
    else sig1.Sigma.extractor t2 t4 e2 e4
  in
  { Sigma.coq_Rel = (Obj.magic dis_Rel); Sigma.add = sig1.Sigma.add;
  Sigma.zero = sig1.Sigma.zero; Sigma.inv = sig1.Sigma.inv; Sigma.bool_eq =
  sig1.Sigma.bool_eq; Sigma.disjoint = sig1.Sigma.disjoint; Sigma.coq_P0 =
  (Obj.magic dis_P0); Sigma.coq_V0 = dis_V0; Sigma.coq_P1 =
  (Obj.magic dis_P1); Sigma.coq_V1 = (Obj.magic dis_V1); Sigma.simulator =
  (Obj.magic dis_simulator); Sigma.simMap = (Obj.magic dis_simMap);
  Sigma.extractor = (Obj.magic dis_extractor) }

(** val parSigmaProtocol :
    'a1 Sigma.form -> 'a2 Sigma.form -> ('a1 * 'a2) Sigma.form **)

let parSigmaProtocol sig1 sig2 =
  let par_Rel = fun s w ->
    (&&) (sig1.Sigma.coq_Rel (fst s) (fst w))
      (sig2.Sigma.coq_Rel (snd s) (snd w))
  in
  let par_add = fun e1 e2 -> ((sig1.Sigma.add (fst e1) (fst e2)),
    (sig2.Sigma.add (snd e1) (snd e2)))
  in
  let par_zero = (sig1.Sigma.zero, sig2.Sigma.zero) in
  let par_bool_eq = fun e1 e2 ->
    (&&) (sig1.Sigma.bool_eq (fst e1) (fst e2))
      (sig2.Sigma.bool_eq (snd e1) (snd e2))
  in
  let par_inv = fun e -> ((sig1.Sigma.inv (fst e)), (sig2.Sigma.inv (snd e)))
  in
  let par_disjoint = fun e1 e2 ->
    (&&) (sig1.Sigma.disjoint (fst e1) (fst e2))
      (sig2.Sigma.disjoint (snd e1) (snd e2))
  in
  let par_P0 = fun s r0 w ->
    let c1 = snd (sig1.Sigma.coq_P0 (fst s) (fst r0) (fst w)) in
    let c2 = snd (sig2.Sigma.coq_P0 (snd s) (snd r0) (snd w)) in (s, (c1, c2))
  in
  let par_V0 = fun p0 e ->
    let s1 = fst (fst p0) in
    let s2 = snd (fst p0) in
    let c1 = fst (snd p0) in
    let c2 = snd (snd p0) in
    (p0, ((snd (sig1.Sigma.coq_V0 (s1, c1) (fst e))),
    (snd (sig2.Sigma.coq_V0 (s2, c2) (snd e)))))
  in
  let par_P1 = fun v0 r0 w ->
    let s1 = fst (fst (fst v0)) in
    let s2 = snd (fst (fst v0)) in
    let c1 = fst (snd (fst v0)) in
    let c2 = snd (snd (fst v0)) in
    let e = snd v0 in
    (v0, ((snd (sig1.Sigma.coq_P1 ((s1, c1), (fst e)) (fst r0) (fst w))),
    (snd (sig2.Sigma.coq_P1 ((s2, c2), (snd e)) (snd r0) (snd w)))))
  in
  let par_V1 = fun p1 ->
    let s1 = fst (fst (fst (fst p1))) in
    let s2 = snd (fst (fst (fst p1))) in
    let c1 = fst (snd (fst (fst p1))) in
    let c2 = snd (snd (fst (fst p1))) in
    let e = snd (fst p1) in
    let r0 = snd p1 in
    (&&) (sig1.Sigma.coq_V1 (((s1, c1), (fst e)), (fst r0)))
      (sig2.Sigma.coq_V1 (((s2, c2), (snd e)), (snd r0)))
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
    let r2 = snd sim2 in (((s, (c1, c2)), (e1, e2)), (r1, r2))
  in
  let par_simMap = fun s r0 e w ->
    ((sig1.Sigma.simMap (fst s) (fst r0) (fst e) (fst w)),
    (sig2.Sigma.simMap (snd s) (snd r0) (snd e) (snd w)))
  in
  let par_extractor = fun r1 r2 e1 e2 ->
    ((sig1.Sigma.extractor (fst r1) (fst r2) (fst e1) (fst e2)),
    (sig2.Sigma.extractor (snd r1) (snd r2) (snd e1) (snd e2)))
  in
  { Sigma.coq_Rel = (Obj.magic par_Rel); Sigma.add = par_add; Sigma.zero =
  par_zero; Sigma.inv = par_inv; Sigma.bool_eq = par_bool_eq;
  Sigma.disjoint = par_disjoint; Sigma.coq_P0 = (Obj.magic par_P0);
  Sigma.coq_V0 = (Obj.magic par_V0); Sigma.coq_P1 = (Obj.magic par_P1);
  Sigma.coq_V1 = (Obj.magic par_V1); Sigma.simulator =
  (Obj.magic par_simulator); Sigma.simMap = (Obj.magic par_simMap);
  Sigma.extractor = (Obj.magic par_extractor) }

(** val pminusN : Big.big_int -> Big.big_int -> Big.big_int **)

let pminusN x y =
  match Coq_Pos.sub_mask x y with
  | Coq_Pos.IsPos k -> k
  | _ -> Big.zero

(** val is_lt : Big.big_int -> Big.big_int -> bool **)

let is_lt n m0 =
  match Coq_Pos.compare n m0 with
  | Lt -> true
  | _ -> false

(** val div_eucl0 :
    Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)

let rec div_eucl0 a b =
  Big.positive_case
    (fun a' ->
    let (q0, r0) = div_eucl0 a' b in
    (Big.n_case
       (fun _ ->
       Big.n_case
         (fun _ -> (Big.zero, Big.zero))
         (fun r1 ->
         if is_lt (Big.doubleplusone r1) b
         then (Big.zero, (Big.doubleplusone r1))
         else (Big.one, (pminusN (Big.doubleplusone r1) b)))
         r0)
       (fun q1 ->
       Big.n_case
         (fun _ ->
         if is_lt Big.one b
         then ((Big.double q1), Big.one)
         else ((Big.doubleplusone q1), Big.zero))
         (fun r1 ->
         if is_lt (Big.doubleplusone r1) b
         then ((Big.double q1), (Big.doubleplusone r1))
         else ((Big.doubleplusone q1), (pminusN (Big.doubleplusone r1) b)))
         r0)
       q0))
    (fun a' ->
    let (q0, r0) = div_eucl0 a' b in
    (Big.n_case
       (fun _ ->
       Big.n_case
         (fun _ -> (Big.zero, Big.zero))
         (fun r1 ->
         if is_lt (Big.double r1) b
         then (Big.zero, (Big.double r1))
         else (Big.one, (pminusN (Big.double r1) b)))
         r0)
       (fun q1 ->
       Big.n_case
         (fun _ -> ((Big.double q1), Big.zero))
         (fun r1 ->
         if is_lt (Big.double r1) b
         then ((Big.double q1), (Big.double r1))
         else ((Big.doubleplusone q1), (pminusN (Big.double r1) b)))
         r0)
       q0))
    (fun _ ->
    if is_lt Big.one b then (Big.zero, Big.one) else (Big.one, Big.zero))
    a

(** val egcd_log2 :
    Big.big_int -> Big.big_int -> Big.big_int ->
    ((Big.big_int * Big.big_int) * Big.big_int) option **)

let rec egcd_log2 a b c =
  let (q0, n) = div_eucl0 a b in
  (Big.n_case
     (fun _ -> Some ((Big.zero, Big.one), b))
     (fun r0 ->
     let (q', n0) = div_eucl0 b r0 in
     (Big.n_case
        (fun _ -> Some ((Big.one, (Z.opp (Z.of_N q0))), r0))
        (fun r' ->
        Big.positive_case
          (fun c' ->
          match egcd_log2 r0 r' c' with
          | Some p0 ->
            let (p1, w') = p0 in
            let (u', v') = p1 in
            let u = Z.sub u' (Z.mul v' (Z.of_N q')) in
            Some ((u, (Z.sub v' (Z.mul (Z.of_N q0) u))), w')
          | None -> None)
          (fun c' ->
          match egcd_log2 r0 r' c' with
          | Some p0 ->
            let (p1, w') = p0 in
            let (u', v') = p1 in
            let u = Z.sub u' (Z.mul v' (Z.of_N q')) in
            Some ((u, (Z.sub v' (Z.mul (Z.of_N q0) u))), w')
          | None -> None)
          (fun _ -> None)
          c)
        n0))
     n)

(** val egcd :
    Big.big_int -> Big.big_int -> (Big.big_int * Big.big_int) * Big.big_int **)

let egcd a b =
  match egcd_log2 a b (Big.double b) with
  | Some p0 -> p0
  | None -> ((Big.one, Big.one), Big.one)

(** val zegcd :
    Big.big_int -> Big.big_int -> (Big.big_int * Big.big_int) * Big.big_int **)

let zegcd a b =
  Big.z_case
    (fun _ ->
    Big.z_case
      (fun _ -> ((Big.zero, Big.zero), Big.zero))
      (fun _ -> ((Big.zero, Big.one), b))
      (fun _ -> ((Big.zero, (Big.opp Big.one)), (Z.opp b)))
      b)
    (fun a0 ->
    Big.z_case
      (fun _ -> ((Big.one, Big.zero), a))
      (fun b0 -> let (p0, w) = egcd a0 b0 in (p0, w))
      (fun b0 ->
      let (p0, w) = egcd a0 b0 in let (u, v) = p0 in ((u, (Z.opp v)), w))
      b)
    (fun a0 ->
    Big.z_case
      (fun _ -> (((Big.opp Big.one), Big.zero), (Z.opp a)))
      (fun b0 ->
      let (p0, w) = egcd a0 b0 in let (u, v) = p0 in (((Z.opp u), v), w))
      (fun b0 ->
      let (p0, w) = egcd a0 b0 in
      let (u, v) = p0 in (((Z.opp u), (Z.opp v)), w))
      b)
    a

type znz = Big.big_int
  (* singleton inductive, whose constructor was mkznz *)

(** val val0 : Big.big_int -> znz -> Big.big_int **)

let val0 _ z =
  z

(** val zero0 : Big.big_int -> znz **)

let zero0 n =
  Big.zero

(** val one : Big.big_int -> znz **)

let one n =
  Big.one

(** val add0 : Big.big_int -> znz -> znz -> znz **)

let add0 n v1 v2 =
  Z.modulo (Z.add (val0 n v1) (val0 n v2)) n

(** val mul0 : Big.big_int -> znz -> znz -> znz **)

let mul0 n v1 v2 =
  Z.modulo (Z.mul (val0 n v1) (val0 n v2)) n

(** val opp0 : Big.big_int -> znz -> znz **)

let opp0 n v =
  Z.modulo (Z.opp (val0 n v)) n

let rec pow_mult x e n acc =
    Big.positive_case
    (fun w -> pow_mult (mul0 n x x) w n (mul0 n acc x))
    (fun w -> pow_mult (mul0 n x x) w n acc)
    (fun _ -> (mul0 n x acc))
    e

let pow x s n =
    let e = val0 n s in
    (Big.z_case
    (fun _ -> Big.one)
    (fun p0 -> pow_mult x p0 n Big.one)
    (fun _ -> Big.one)
    e)

let twoBigInt = Big_int.big_int_of_string "2"

(* We use the Fermat's little thorem *)
let mul_inv n a = pow a (Big_int.sub_big_int n twoBigInt) n

let inv0 p0 v =
 mul_inv p0 v

(* let inv0 p0 v =
  Z.modulo (fst (fst (zegcd (val0 p0 v) p0))) p0 *)

(** val p : Big.big_int **)

let p =
  (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.double
    Big.one)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val q : Big.big_int **)

let q =
  (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double
    Big.one)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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

(** val binary_power_mult2 : fp -> Big.big_int -> fp -> fp **)

let rec binary_power_mult2 x n acc =
  Big.positive_case
    (fun w -> binary_power_mult2 (fpMul x x) w (fpMul acc x))
    (fun w -> binary_power_mult2 (fpMul x x) w acc)
    (fun _ -> fpMul x acc)
    n

(** val binary_power2 : fp -> r -> fp **)

let binary_power2 x n =
  let e = val0 q n in
  (Big.z_case
     (fun _ -> fpOne)
     (fun p0 -> binary_power_mult2 x p0 fpOne)
     (fun _ -> fpOne)
     e)

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

let op =
  binary_power2

(** val dLog : (m * m) -> r -> bool **)

let dLog s w =
  let g = fst s in let gtox = snd s in mbool_eq gtox (op g w)

(** val valid_P0 : (m * m) -> r -> r -> (m * m) * m **)

let valid_P0 ggtox r0 _ =
  let g = fst ggtox in (ggtox, (op g r0))

(** val valid_V0 : ((m * m) * m) -> r -> ((m * m) * m) * r **)

let valid_V0 ggtoxgtor c =
  (ggtoxgtor, c)

(** val valid_P1 :
    (((m * m) * m) * r) -> r -> r -> (((m * m) * m) * r) * r **)

let valid_P1 ggtoxgtorc r0 x =
  let c = snd ggtoxgtorc in let s = radd r0 (rmul c x) in (ggtoxgtorc, s)

(** val valid_V1 : ((((m * m) * m) * r) * r) -> bool **)

let valid_V1 ggtoxgtorcs =
  let g = fst (fst (fst (fst ggtoxgtorcs))) in
  let gtox = snd (fst (fst (fst ggtoxgtorcs))) in
  let gtor = snd (fst (fst ggtoxgtorcs)) in
  let c = snd (fst ggtoxgtorcs) in
  let s = snd ggtoxgtorcs in mbool_eq (op g s) (mdot (op gtox c) gtor)

(** val simulator_mapper : (m * m) -> r -> r -> r -> r **)

let simulator_mapper _ r0 c x =
  radd r0 (rmul x c)

(** val simulator0 : (m * m) -> r -> r -> (((m * m) * m) * r) * r **)

let simulator0 ggtox z e =
  let g = fst ggtox in
  let gtox = snd ggtox in
  (((ggtox, (mdot (op g z) (minv (op gtox e)))), e), z)

(** val extractor0 : r -> r -> r -> r -> r **)

let extractor0 s1 s2 c1 c2 =
  rmul (radd s1 (rinv s2)) (rmulInv (radd c1 (rinv c2)))

(** val disjoint0 : r -> r -> bool **)

let disjoint0 c1 c2 =
  negb (rbool_eq c1 c2)

(** val dLogForm : r Sigma.form **)

let dLogForm =
  { Sigma.coq_Rel = (Obj.magic dLog); Sigma.add = radd; Sigma.zero = rzero;
    Sigma.inv = rinv; Sigma.bool_eq = rbool_eq; Sigma.disjoint = disjoint0;
    Sigma.coq_P0 = (Obj.magic valid_P0); Sigma.coq_V0 = (Obj.magic valid_V0);
    Sigma.coq_P1 = (Obj.magic valid_P1); Sigma.coq_V1 = (Obj.magic valid_V1);
    Sigma.simulator = (Obj.magic simulator0); Sigma.simMap =
    (Obj.magic simulator_mapper); Sigma.extractor = (Obj.magic extractor0) }

(** val emptyRel : m -> r -> bool **)

let emptyRel _ _ =
  true

(** val empty_P0 : m -> r -> r -> m * m **)

let empty_P0 g _ _ =
  (g, g)

(** val empty_V0 : (m * m) -> r -> (m * m) * r **)

let empty_V0 g c =
  (g, c)

(** val empty_P1 : ((m * m) * r) -> r -> r -> ((m * m) * r) * r **)

let empty_P1 g _ _ =
  (g, (snd g))

(** val empty_V1 : (((m * m) * r) * r) -> bool **)

let empty_V1 _ =
  true

(** val empty_simulator_mapper : m -> r -> r -> r -> r **)

let empty_simulator_mapper _ r0 _ _ =
  r0

(** val empty_simulator : m -> r -> r -> ((m * m) * r) * r **)

let empty_simulator g _ e =
  (((g, g), e), e)

(** val empty_mapper : r -> r -> r -> r -> r **)

let empty_mapper s1 s2 c1 c2 =
  rmul (radd s1 (rinv s2)) (rmulInv (radd c1 (rinv c2)))

(** val emptyForm : r Sigma.form **)

let emptyForm =
  { Sigma.coq_Rel = (Obj.magic emptyRel); Sigma.add = radd; Sigma.zero =
    rzero; Sigma.inv = rinv; Sigma.bool_eq = rbool_eq; Sigma.disjoint =
    disjoint0; Sigma.coq_P0 = (Obj.magic empty_P0); Sigma.coq_V0 =
    (Obj.magic empty_V0); Sigma.coq_P1 = (Obj.magic empty_P1); Sigma.coq_V1 =
    (Obj.magic empty_V1); Sigma.simulator = (Obj.magic empty_simulator);
    Sigma.simMap = (Obj.magic empty_simulator_mapper); Sigma.extractor =
    (Obj.magic empty_mapper) }

(** val dHTForm : r Sigma.form **)

let dHTForm =
  eqSigmaProtocol dLogForm

(** val dHTDisForm : r Sigma.form **)

let dHTDisForm =
  disSigmaProtocol dHTForm

(** val oneOrZero : r Sigma.coq_S -> r Sigma.coq_S **)

let oneOrZero s =
  let g = fst (fst (Obj.magic s)) in
  let h = snd (fst (Obj.magic s)) in
  let gtox = fst (snd (Obj.magic s)) in
  let htox = snd (snd (Obj.magic s)) in
  Obj.magic (((g, gtox), (h, htox)), ((g, gtox), (h, (mdot htox (minv g)))))

(** val oneOrZeroCipher : m -> m -> (m * m) -> r Sigma.coq_S **)

let oneOrZeroCipher g h c =
  oneOrZero (Obj.magic ((g, h), c))

(** val decFactorStatment : m -> m -> (m * m) -> m -> r Sigma.coq_S **)

let decFactorStatment g h c d =
  Obj.magic ((g, h), ((fst c), d))

type recChalType = __

(** val approvalSigma : (m * m) list -> recChalType Sigma.form **)

let rec approvalSigma = function
| [] -> Obj.magic emptyForm
| _ :: b -> Obj.magic parSigmaProtocol (approvalSigma b) dHTDisForm

(** val decryptionSigma : (((r * r) * r) * r) Sigma.form **)

let decryptionSigma =
  parSigmaProtocol
    (parSigmaProtocol (parSigmaProtocol dHTForm dHTForm) dHTForm) dHTForm

(** val approvalSigmaStatment :
    m -> m -> (m * m) list -> recChalType Sigma.coq_S **)

let rec approvalSigmaStatment g h = function
| [] -> Obj.magic g
| a :: b -> Obj.magic ((approvalSigmaStatment g h b), (oneOrZeroCipher g h a))

(** val decryptionSigmaStatment :
    m -> (m * m) -> (((m * m) * m) * m) -> (((m * m) * m) * m) ->
    (((r * r) * r) * r) Sigma.coq_S **)

let decryptionSigmaStatment g c y d =
  Obj.magic
    ((((decFactorStatment g (fst (fst (fst y))) c (fst (fst (fst d)))),
    (decFactorStatment g (snd (fst (fst y))) c (snd (fst (fst d))))),
    (decFactorStatment g (snd (fst y)) c (snd (fst d)))),
    (decFactorStatment g (snd y) c (snd d)))
