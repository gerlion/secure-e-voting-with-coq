
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

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
      let (q0, r) = pos_div_eucl a' b in
      let r' = add (mul (Big.double Big.one) r) Big.one in
      if ltb r' b
      then ((mul (Big.double Big.one) q0), r')
      else ((add (mul (Big.double Big.one) q0) Big.one), (sub r' b)))
      (fun a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = mul (Big.double Big.one) r in
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
        let (q0, r) = pos_div_eucl a' b' in
        (Big.z_case
           (fun _ -> ((opp q0), Big.zero))
           (fun _ -> ((opp (add q0 Big.one)), (add b r)))
           (fun _ -> ((opp (add q0 Big.one)), (add b r)))
           r))
        b)
      (fun a' ->
      Big.z_case
        (fun _ -> (Big.zero, Big.zero))
        (fun _ ->
        let (q0, r) = pos_div_eucl a' b in
        (Big.z_case
           (fun _ -> ((opp q0), Big.zero))
           (fun _ -> ((opp (add q0 Big.one)), (sub b r)))
           (fun _ -> ((opp (add q0 Big.one)), (sub b r)))
           r))
        (fun b' -> let (q0, r) = pos_div_eucl a' b' in (q0, (opp r)))
        b)
      a

  (** val modulo : Big.big_int -> Big.big_int -> Big.big_int **)

  let modulo a b =
    let (_, r) = div_eucl a b in r
 end

module type GroupSig =
 sig
  type coq_G

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : coq_G

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Ginv : coq_G -> coq_G
 end

module type RingSig =
 sig
  type coq_F

  val coq_Fadd : coq_F -> coq_F -> coq_F

  val coq_Fzero : coq_F

  val coq_Fbool_eq : coq_F -> coq_F -> bool

  val coq_Fsub : coq_F -> coq_F -> coq_F

  val coq_Finv : coq_F -> coq_F

  val coq_Fmul : coq_F -> coq_F -> coq_F

  val coq_Fone : coq_F
 end

module ModuleAddationalLemmas =
 functor (Group:GroupSig) ->
 functor (Ring:RingSig) ->
 functor (M:sig
  val op : Group.coq_G -> Ring.coq_F -> Group.coq_G
 end) ->
 struct
 end

module type FieldSig =
 sig
  type coq_F

  val coq_Fadd : coq_F -> coq_F -> coq_F

  val coq_Fzero : coq_F

  val coq_Fbool_eq : coq_F -> coq_F -> bool

  val coq_Fsub : coq_F -> coq_F -> coq_F

  val coq_Finv : coq_F -> coq_F

  val coq_Fmul : coq_F -> coq_F -> coq_F

  val coq_Fone : coq_F

  val coq_FmulInv : coq_F -> coq_F

  val coq_Fdiv : coq_F -> coq_F -> coq_F
 end

module VectorSpaceAddationalLemmas =
 functor (Group:GroupSig) ->
 functor (Field:FieldSig) ->
 functor (VS:sig
  val op : Group.coq_G -> Field.coq_F -> Group.coq_G
 end) ->
 struct
 end

module DualGroupIns =
 functor (Group:GroupSig) ->
 struct
  type coq_G = Group.coq_G * Group.coq_G

  (** val coq_Gdot : coq_G -> coq_G -> coq_G **)

  let coq_Gdot a b =
    ((Group.coq_Gdot (fst a) (fst b)), (Group.coq_Gdot (snd a) (snd b)))

  (** val coq_Gone : Group.coq_G * Group.coq_G **)

  let coq_Gone =
    (Group.coq_Gone, Group.coq_Gone)

  (** val coq_Gbool_eq : coq_G -> coq_G -> bool **)

  let coq_Gbool_eq a b =
    (&&) (Group.coq_Gbool_eq (fst a) (fst b))
      (Group.coq_Gbool_eq (snd a) (snd b))

  (** val coq_Ginv :
      (Group.coq_G * Group.coq_G) -> Group.coq_G * Group.coq_G **)

  let coq_Ginv a =
    ((Group.coq_Ginv (fst a)), (Group.coq_Ginv (snd a)))
 end

module DualVectorSpaceIns =
 functor (Group:GroupSig) ->
 functor (DualGroup:sig
  type coq_G = Group.coq_G * Group.coq_G

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : Group.coq_G * Group.coq_G

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Ginv : (Group.coq_G * Group.coq_G) -> Group.coq_G * Group.coq_G
 end) ->
 functor (Field:FieldSig) ->
 functor (VS:sig
  val op : Group.coq_G -> Field.coq_F -> Group.coq_G
 end) ->
 struct
  (** val op : DualGroup.coq_G -> Field.coq_F -> Group.coq_G * Group.coq_G **)

  let op a b =
    ((VS.op (fst a) b), (VS.op (snd a) b))
 end

module VectorSpaceModuleSameGroupInsIns =
 functor (Group:GroupSig) ->
 functor (Field:FieldSig) ->
 functor (VS:sig
  val op : Group.coq_G -> Field.coq_F -> Group.coq_G
 end) ->
 struct
  (** val op3 : Field.coq_F -> Field.coq_F -> Field.coq_F **)

  let op3 =
    Field.coq_Fmul
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
                   simMapInv : (__ -> __ -> 'e -> __ -> __);
                   extractor : (__ -> __ -> 'e -> 'e -> __) }

  type 'e coq_S = __

  type 'e coq_W = __

  (** val coq_Rel : 'a1 form -> 'a1 coq_S -> 'a1 coq_W -> bool **)

  let coq_Rel f0 =
    f0.coq_Rel

  type 'e coq_C = __

  type 'e coq_R = __

  (** val add : 'a1 form -> 'a1 -> 'a1 -> 'a1 **)

  let add f0 =
    f0.add

  (** val zero : 'a1 form -> 'a1 **)

  let zero f0 =
    f0.zero

  (** val inv : 'a1 form -> 'a1 -> 'a1 **)

  let inv f0 =
    f0.inv

  (** val bool_eq : 'a1 form -> 'a1 -> 'a1 -> bool **)

  let bool_eq f0 =
    f0.bool_eq

  (** val disjoint : 'a1 form -> 'a1 -> 'a1 -> bool **)

  let disjoint f0 =
    f0.disjoint

  type 'e coq_T = __

  (** val coq_P0 :
      'a1 form -> 'a1 coq_S -> 'a1 coq_R -> 'a1 coq_W -> 'a1 coq_S * 'a1 coq_C **)

  let coq_P0 f0 =
    f0.coq_P0

  (** val coq_V0 :
      'a1 form -> ('a1 coq_S * 'a1 coq_C) -> 'a1 -> ('a1 coq_S * 'a1
      coq_C) * 'a1 **)

  let coq_V0 f0 =
    f0.coq_V0

  (** val coq_P1 :
      'a1 form -> (('a1 coq_S * 'a1 coq_C) * 'a1) -> 'a1 coq_R -> 'a1 coq_W
      -> (('a1 coq_S * 'a1 coq_C) * 'a1) * 'a1 coq_T **)

  let coq_P1 f0 =
    f0.coq_P1

  (** val coq_V1 :
      'a1 form -> ((('a1 coq_S * 'a1 coq_C) * 'a1) * 'a1 coq_T) -> bool **)

  let coq_V1 f0 =
    f0.coq_V1

  (** val simulator :
      'a1 form -> 'a1 coq_S -> 'a1 coq_T -> 'a1 -> (('a1 coq_S * 'a1
      coq_C) * 'a1) * 'a1 coq_T **)

  let simulator f0 =
    f0.simulator

  (** val simMap :
      'a1 form -> 'a1 coq_S -> 'a1 coq_W -> 'a1 -> 'a1 coq_R -> 'a1 coq_T **)

  let simMap f0 =
    f0.simMap

  (** val simMapInv :
      'a1 form -> 'a1 coq_S -> 'a1 coq_W -> 'a1 -> 'a1 coq_T -> 'a1 coq_R **)

  let simMapInv f0 =
    f0.simMapInv

  (** val extractor :
      'a1 form -> 'a1 coq_T -> 'a1 coq_T -> 'a1 -> 'a1 -> 'a1 coq_W **)

  let extractor f0 =
    f0.extractor
 end

(** val eqSigmaProtocol : 'a1 Sigma.form -> 'a1 Sigma.form **)

let eqSigmaProtocol sig1 =
  let eq_Rel = fun s w ->
    (&&) (sig1.Sigma.coq_Rel (fst s) w) (sig1.Sigma.coq_Rel (snd s) w)
  in
  let eq_P0 = fun s r w ->
    let c1 = snd (sig1.Sigma.coq_P0 (fst s) r w) in
    let c2 = snd (sig1.Sigma.coq_P0 (snd s) r w) in (s, (c1, c2))
  in
  let eq_V0 = fun p0 e ->
    let s1 = fst (fst p0) in
    let c1 = fst (snd p0) in (p0, (snd ((sig1.Sigma.coq_V0 (s1, c1)), e)))
  in
  let eq_P1 = fun v0 r w ->
    let s1 = fst (fst (fst v0)) in
    let c1 = fst (snd (fst v0)) in
    let e = snd v0 in (v0, (snd (sig1.Sigma.coq_P1 ((s1, c1), e) r w)))
  in
  let eq_V1 = fun p1 ->
    let s1 = fst (fst (fst (fst p1))) in
    let s2 = snd (fst (fst (fst p1))) in
    let c1 = fst (snd (fst (fst p1))) in
    let c2 = snd (snd (fst (fst p1))) in
    let e = snd (fst p1) in
    let r = snd p1 in
    (&&) (sig1.Sigma.coq_V1 (((s1, c1), e), r))
      (sig1.Sigma.coq_V1 (((s2, c2), e), r))
  in
  let eq_simulator = fun s r e ->
    let s1 = fst s in
    let s2 = snd s in
    let sim1 = sig1.Sigma.simulator s1 r e in
    let sim2 = sig1.Sigma.simulator s2 r e in
    let c1 = snd (fst (fst sim1)) in
    let c2 = snd (fst (fst sim2)) in
    let e1 = snd (fst sim1) in let r1 = snd sim1 in (((s, (c1, c2)), e1), r1)
  in
  let eq_simMap = fun s w e r -> sig1.Sigma.simMap (fst s) w e r in
  let eq_simMapInv = fun s w e t0 -> sig1.Sigma.simMapInv (fst s) w e t0 in
  let eq_extractor = fun r1 r2 e1 e2 -> sig1.Sigma.extractor r1 r2 e1 e2 in
  { Sigma.coq_Rel = (Obj.magic eq_Rel); Sigma.add = sig1.Sigma.add;
  Sigma.zero = sig1.Sigma.zero; Sigma.inv = sig1.Sigma.inv; Sigma.bool_eq =
  sig1.Sigma.bool_eq; Sigma.disjoint = sig1.Sigma.disjoint; Sigma.coq_P0 =
  (Obj.magic eq_P0); Sigma.coq_V0 = (Obj.magic eq_V0); Sigma.coq_P1 =
  (Obj.magic eq_P1); Sigma.coq_V1 = (Obj.magic eq_V1); Sigma.simulator =
  (Obj.magic eq_simulator); Sigma.simMap = (Obj.magic eq_simMap);
  Sigma.simMapInv = (Obj.magic eq_simMapInv); Sigma.extractor = eq_extractor }

(** val disSigmaProtocol : 'a1 Sigma.form -> 'a1 Sigma.form **)

let disSigmaProtocol sig1 =
  let dis_Rel = fun s w ->
    (||) (sig1.Sigma.coq_Rel (fst s) w) (sig1.Sigma.coq_Rel (snd s) w)
  in
  let dis_P0 = fun s rzeb w ->
    let e = snd rzeb in
    let z = snd (fst rzeb) in
    let r = fst (fst rzeb) in
    let hc1 = snd (sig1.Sigma.coq_P0 (fst s) r w) in
    let hc2 = snd (sig1.Sigma.coq_P0 (snd s) r w) in
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
    let r = fst (fst rzeb) in
    let e1 =
      snd (sig1.Sigma.coq_V0 (s1, c1) (sig1.Sigma.add e (sig1.Sigma.inv se)))
    in
    let ht1 = snd (sig1.Sigma.coq_P1 ((s1, c1), e1) r w) in
    let ht2 = snd (sig1.Sigma.coq_P1 ((s2, c2), e1) r w) in
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
  let dis_simulator = fun s t0 e ->
    let s1 = fst s in
    let s2 = snd s in
    let e1 = snd (fst t0) in
    let e2 = sig1.Sigma.add e (sig1.Sigma.inv e1) in
    let r1 = fst (fst t0) in
    let r2 = snd t0 in
    let sim1 = sig1.Sigma.simulator s1 r1 e1 in
    let sim2 = sig1.Sigma.simulator s2 r2 e2 in
    let c1 = snd (fst (fst sim1)) in
    let c2 = snd (fst (fst sim2)) in
    let sr1 = snd sim1 in
    let sr2 = snd sim2 in
    let se1 = snd (fst sim1) in (((s, (c1, c2)), e), ((sr1, se1), sr2))
  in
  let dis_simMap = fun s w e rtcb ->
    let r = fst (fst rtcb) in
    let t0 = snd (fst rtcb) in
    let c = snd rtcb in
    let h1 =
      sig1.Sigma.simMap (fst s) w (sig1.Sigma.add e (sig1.Sigma.inv c)) r
    in
    let h2 =
      sig1.Sigma.simMap (snd s) w (sig1.Sigma.add e (sig1.Sigma.inv c)) r
    in
    if sig1.Sigma.coq_Rel (fst s) w
    then ((h1, (sig1.Sigma.add e (sig1.Sigma.inv c))), t0)
    else ((t0, c), h2)
  in
  let dis_simMapInv = fun s w e tet ->
    let t1 = fst (fst tet) in
    let c = snd (fst tet) in
    let t2 = snd tet in
    let h1 = sig1.Sigma.simMapInv (fst s) w c t1 in
    let h2 =
      sig1.Sigma.simMapInv (snd s) w (sig1.Sigma.add e (sig1.Sigma.inv c)) t2
    in
    if sig1.Sigma.coq_Rel (fst s) w
    then ((h1, t2), (sig1.Sigma.add e (sig1.Sigma.inv c)))
    else ((h2, t1), c)
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
  Sigma.simMapInv = (Obj.magic dis_simMapInv); Sigma.extractor =
  (Obj.magic dis_extractor) }

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
  let par_P0 = fun s r w ->
    let c1 = snd (sig1.Sigma.coq_P0 (fst s) (fst r) (fst w)) in
    let c2 = snd (sig2.Sigma.coq_P0 (snd s) (snd r) (snd w)) in (s, (c1, c2))
  in
  let par_V0 = fun p0 e ->
    let s1 = fst (fst p0) in
    let s2 = snd (fst p0) in
    let c1 = fst (snd p0) in
    let c2 = snd (snd p0) in
    (p0, ((snd (sig1.Sigma.coq_V0 (s1, c1) (fst e))),
    (snd (sig2.Sigma.coq_V0 (s2, c2) (snd e)))))
  in
  let par_P1 = fun v0 r w ->
    let s1 = fst (fst (fst v0)) in
    let s2 = snd (fst (fst v0)) in
    let c1 = fst (snd (fst v0)) in
    let c2 = snd (snd (fst v0)) in
    let e = snd v0 in
    (v0, ((snd (sig1.Sigma.coq_P1 ((s1, c1), (fst e)) (fst r) (fst w))),
    (snd (sig2.Sigma.coq_P1 ((s2, c2), (snd e)) (snd r) (snd w)))))
  in
  let par_V1 = fun p1 ->
    let s1 = fst (fst (fst (fst p1))) in
    let s2 = snd (fst (fst (fst p1))) in
    let c1 = fst (snd (fst (fst p1))) in
    let c2 = snd (snd (fst (fst p1))) in
    let e = snd (fst p1) in
    let r = snd p1 in
    (&&) (sig1.Sigma.coq_V1 (((s1, c1), (fst e)), (fst r)))
      (sig2.Sigma.coq_V1 (((s2, c2), (snd e)), (snd r)))
  in
  let par_simulator = fun s r e ->
    let s1 = fst s in
    let s2 = snd s in
    let sim1 = sig1.Sigma.simulator s1 (fst r) (fst e) in
    let sim2 = sig2.Sigma.simulator s2 (snd r) (snd e) in
    let c1 = snd (fst (fst sim1)) in
    let c2 = snd (fst (fst sim2)) in
    let e1 = snd (fst sim1) in
    let e2 = snd (fst sim2) in
    let r1 = snd sim1 in
    let r2 = snd sim2 in (((s, (c1, c2)), (e1, e2)), (r1, r2))
  in
  let par_simMap = fun s w e r ->
    ((sig1.Sigma.simMap (fst s) (fst w) (fst e) (fst r)),
    (sig2.Sigma.simMap (snd s) (snd w) (snd e) (snd r)))
  in
  let par_simMapInv = fun s w e t0 ->
    ((sig1.Sigma.simMapInv (fst s) (fst w) (fst e) (fst t0)),
    (sig2.Sigma.simMapInv (snd s) (snd w) (snd e) (snd t0)))
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
  Sigma.simMapInv = (Obj.magic par_simMapInv); Sigma.extractor =
  (Obj.magic par_extractor) }

type 'a rel_dec = 'a -> 'a -> bool

(** val dec_beq : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool **)

let dec_beq beq x y =
  let b = beq x y in if b then true else false

type 'a t =
| Nil
| Cons of 'a * nat * 'a t

(** val caseS : ('a1 -> nat -> 'a1 t -> 'a2) -> nat -> 'a1 t -> 'a2 **)

let caseS h _ = function
| Nil -> Obj.magic __
| Cons (h0, n0, t0) -> h h0 n0 t0

(** val hd : nat -> 'a1 t -> 'a1 **)

let hd n =
  caseS (fun h _ _ -> h) n

(** val const : 'a1 -> nat -> 'a1 t **)

let rec const a = function
| O -> Nil
| S n0 -> Cons (a, n0, (const a n0))

(** val tl : nat -> 'a1 t -> 'a1 t **)

let tl n =
  caseS (fun _ _ t0 -> t0) n

module type SetA =
 sig
  type coq_A
 end

module type Eqset =
 sig
  type coq_A
 end

module type Eqset_dec =
 sig
  module Eq :
   Eqset

  val eqA_dec : Eq.coq_A -> Eq.coq_A -> bool
 end

module Eqset_def =
 functor (A:SetA) ->
 struct
  type coq_A = A.coq_A
 end

(** val vnth : nat -> 'a1 t -> nat -> 'a1 **)

let rec vnth _ v i =
  match v with
  | Nil -> assert false (* absurd case *)
  | Cons (x, wildcard', v') ->
    (match i with
     | O -> x
     | S j -> vnth wildcard' v' j)

(** val vreplace : nat -> 'a1 t -> nat -> 'a1 -> 'a1 t **)

let rec vreplace _ v i a =
  match v with
  | Nil -> assert false (* absurd case *)
  | Cons (h, wildcard', v') ->
    (match i with
     | O -> Cons (a, wildcard', v')
     | S i' -> Cons (h, wildcard', (vreplace wildcard' v' i' a)))

(** val vmap : ('a1 -> 'a2) -> nat -> 'a1 t -> 'a2 t **)

let rec vmap f0 _ = function
| Nil -> Nil
| Cons (a, n0, v') -> Cons ((f0 a), n0, (vmap f0 n0 v'))

(** val bVforall : ('a1 -> bool) -> nat -> 'a1 t -> bool **)

let rec bVforall f0 _ = function
| Nil -> true
| Cons (a, n0, w) -> (&&) (f0 a) (bVforall f0 n0 w)

(** val vforall2_aux_dec :
    ('a1 -> 'a2 -> bool) -> nat -> 'a1 t -> nat -> 'a2 t -> bool **)

let rec vforall2_aux_dec r_dec _ v1 _ v2 =
  match v1 with
  | Nil -> (match v2 with
            | Nil -> true
            | Cons (_, _, _) -> false)
  | Cons (h, n, t0) ->
    (match v2 with
     | Nil -> false
     | Cons (h0, n0, v3) ->
       let s = vforall2_aux_dec r_dec n t0 n0 v3 in
       if s then r_dec h h0 else false)

(** val vforall2_dec :
    ('a1 -> 'a2 -> bool) -> nat -> 'a1 t -> 'a2 t -> bool **)

let vforall2_dec r_dec n v w =
  vforall2_aux_dec r_dec n v n w

(** val bVforall2_aux :
    ('a1 -> 'a2 -> bool) -> nat -> nat -> 'a1 t -> 'a2 t -> bool **)

let rec bVforall2_aux f0 _ _ v1 v2 =
  match v1 with
  | Nil -> (match v2 with
            | Nil -> true
            | Cons (_, _, _) -> false)
  | Cons (x, n, xs) ->
    (match v2 with
     | Nil -> false
     | Cons (y, n0, ys) -> (&&) (f0 x y) (bVforall2_aux f0 n n0 xs ys))

(** val bVforall2 : ('a1 -> 'a2 -> bool) -> nat -> 'a1 t -> 'a2 t -> bool **)

let bVforall2 f0 n v1 v2 =
  bVforall2_aux f0 n n v1 v2

(** val vbuild_spec : nat -> (nat -> __ -> 'a1) -> 'a1 t **)

let rec vbuild_spec n gen =
  match n with
  | O -> Nil
  | S p0 ->
    let gen' = fun i -> gen (S i) __ in
    Cons ((gen O __), p0, (vbuild_spec p0 (fun i _ -> gen' i)))

(** val vbuild : nat -> (nat -> __ -> 'a1) -> 'a1 t **)

let vbuild =
  vbuild_spec

(** val vfold_left : ('a1 -> 'a2 -> 'a1) -> nat -> 'a1 -> 'a2 t -> 'a1 **)

let rec vfold_left f0 _ a = function
| Nil -> a
| Cons (b, n0, w) -> vfold_left f0 n0 (f0 a b) w

(** val vfold_left_rev : ('a1 -> 'a2 -> 'a1) -> nat -> 'a1 -> 'a2 t -> 'a1 **)

let rec vfold_left_rev f0 _ a = function
| Nil -> a
| Cons (b, n0, w) -> f0 (vfold_left_rev f0 n0 a w) b

(** val vmap2 : ('a1 -> 'a2 -> 'a3) -> nat -> 'a1 t -> 'a2 t -> 'a3 t **)

let rec vmap2 f0 n x x0 =
  match n with
  | O -> Nil
  | S n0 ->
    Cons ((f0 (hd n0 x) (hd n0 x0)), n0, (vmap2 f0 n0 (tl n0 x) (tl n0 x0)))

module type SemiRingType =
 sig
  module ES :
   Eqset_dec

  val coq_A0 : ES.Eq.coq_A

  val coq_A1 : ES.Eq.coq_A

  val coq_Aplus : ES.Eq.coq_A -> ES.Eq.coq_A -> ES.Eq.coq_A

  val coq_Amult : ES.Eq.coq_A -> ES.Eq.coq_A -> ES.Eq.coq_A
 end

module SemiRing =
 functor (SR:SemiRingType) ->
 struct
 end

module VectorArith =
 functor (SRT:SemiRingType) ->
 struct
  module SR = SemiRing(SRT)

  (** val zero_vec : nat -> SRT.ES.Eq.coq_A t **)

  let zero_vec =
    const SRT.coq_A0

  (** val id_vec : nat -> nat -> SRT.ES.Eq.coq_A t **)

  let id_vec n i =
    vreplace n (zero_vec n) i SRT.coq_A1

  (** val vector_plus :
      nat -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A t **)

  let vector_plus n v1 v2 =
    vmap2 SRT.coq_Aplus n v1 v2

  (** val add_vectors :
      nat -> nat -> SRT.ES.Eq.coq_A t t -> SRT.ES.Eq.coq_A t **)

  let add_vectors n k v =
    vfold_left_rev (vector_plus n) k (zero_vec n) v

  (** val dot_product :
      nat -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A **)

  let dot_product n l r =
    vfold_left_rev SRT.coq_Aplus n SRT.coq_A0 (vmap2 SRT.coq_Amult n l r)
 end

module Matrix =
 functor (SRT:SemiRingType) ->
 struct
  module SR = SemiRing(SRT)

  module VA = VectorArith(SRT)

  type matrix = SRT.ES.Eq.coq_A t t

  (** val get_row : nat -> nat -> matrix -> nat -> SRT.ES.Eq.coq_A t **)

  let get_row m _ m0 i =
    vnth m m0 i

  (** val get_col : nat -> nat -> matrix -> nat -> SRT.ES.Eq.coq_A t **)

  let get_col m n m0 i =
    vmap (fun v -> vnth n v i) m m0

  (** val get_elem : nat -> nat -> matrix -> nat -> nat -> SRT.ES.Eq.coq_A **)

  let get_elem m n m0 i j =
    vnth n (get_row m n m0 i) j

  (** val mat_build_spec :
      nat -> nat -> (nat -> nat -> __ -> __ -> SRT.ES.Eq.coq_A) -> matrix **)

  let rec mat_build_spec n n0 gen =
    match n with
    | O -> Nil
    | S n1 ->
      let gen_1 = fun j -> gen O j __ in
      let gen' = fun i j -> gen (S i) j __ in
      let s = mat_build_spec n1 n0 (fun i j _ -> gen' i j) in
      let s0 = vbuild_spec n0 gen_1 in Cons (s0, n1, s)

  (** val mat_build :
      nat -> nat -> (nat -> nat -> __ -> __ -> SRT.ES.Eq.coq_A) -> matrix **)

  let mat_build =
    mat_build_spec

  (** val zero_matrix : nat -> nat -> matrix **)

  let zero_matrix m n =
    mat_build m n (fun _ _ _ _ -> SRT.coq_A0)

  (** val id_matrix : nat -> matrix **)

  let id_matrix n =
    vbuild n (fun i _ -> VA.id_vec n i)

  (** val inverse_matrix :
      (SRT.ES.Eq.coq_A -> SRT.ES.Eq.coq_A) -> nat -> nat -> matrix -> matrix **)

  let inverse_matrix inv1 m n m0 =
    mat_build m n (fun i j _ _ -> inv1 (get_elem m n m0 i j))

  type row_mat = matrix

  type col_mat = matrix

  (** val vec_to_row_mat : nat -> SRT.ES.Eq.coq_A t -> row_mat **)

  let vec_to_row_mat _ v =
    Cons (v, O, Nil)

  (** val vec_to_col_mat : nat -> SRT.ES.Eq.coq_A t -> col_mat **)

  let vec_to_col_mat n v =
    vmap (fun i -> Cons (i, O, Nil)) n v

  (** val row_mat_to_vec : nat -> row_mat -> SRT.ES.Eq.coq_A t **)

  let row_mat_to_vec n m =
    get_row (S O) n m O

  (** val col_mat_to_vec : nat -> col_mat -> SRT.ES.Eq.coq_A t **)

  let col_mat_to_vec n m =
    get_col n (S O) m O

  (** val mat_transpose : nat -> nat -> matrix -> matrix **)

  let mat_transpose m n m0 =
    mat_build n m (fun i j _ _ -> get_elem m n m0 j i)

  (** val vec_plus :
      nat -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A t **)

  let vec_plus n l r =
    vmap2 SRT.coq_Aplus n l r

  (** val mat_plus : nat -> nat -> matrix -> matrix -> SRT.ES.Eq.coq_A t t **)

  let mat_plus m n l r =
    vmap2 (vec_plus n) m l r

  (** val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix **)

  let mat_mult m n p0 l r =
    mat_build m p0 (fun i j _ _ ->
      VA.dot_product n (get_row m n l i) (get_col n p0 r j))

  (** val mat_vec_prod :
      nat -> nat -> matrix -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A t **)

  let mat_vec_prod m n m0 v =
    col_mat_to_vec m (mat_mult m n (S O) m0 (vec_to_col_mat n v))

  (** val mat_forall2'_dec :
      nat -> nat -> SRT.ES.Eq.coq_A rel_dec -> matrix rel_dec **)

  let mat_forall2'_dec m n p_dec m0 n0 =
    vforall2_dec (vforall2_dec p_dec n) m m0 n0

  (** val mat_forall2_dec :
      nat -> nat -> SRT.ES.Eq.coq_A rel_dec -> matrix rel_dec **)

  let mat_forall2_dec =
    mat_forall2'_dec
 end

module MatricesFIns =
 functor (Ring:RingSig) ->
 struct
  module F =
   struct
    type coq_A = Ring.coq_F
   end

  module F_Eqset = Eqset_def(F)

  module F_Eqset_dec =
   struct
    module Eq = F_Eqset

    (** val eqA_dec : Ring.coq_F -> Ring.coq_F -> bool **)

    let eqA_dec =
      dec_beq Ring.coq_Fbool_eq
   end

  module FSemiRingT =
   struct
    module ES = F_Eqset_dec

    (** val coq_A0 : Ring.coq_F **)

    let coq_A0 =
      Ring.coq_Fzero

    (** val coq_A1 : Ring.coq_F **)

    let coq_A1 =
      Ring.coq_Fone

    (** val coq_Aplus : Ring.coq_F -> Ring.coq_F -> Ring.coq_F **)

    let coq_Aplus =
      Ring.coq_Fadd

    (** val coq_Amult : Ring.coq_F -> Ring.coq_F -> Ring.coq_F **)

    let coq_Amult =
      Ring.coq_Fmul
   end

  module FMatrix = Matrix(FSemiRingT)

  type coq_VF = Ring.coq_F t

  (** val coq_VF_zero : nat -> Ring.coq_F t **)

  let coq_VF_zero =
    const Ring.coq_Fzero

  (** val coq_VF_one : nat -> Ring.coq_F t **)

  let coq_VF_one =
    const Ring.coq_Fone

  (** val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t **)

  let coq_VF_n_id n n0 =
    FMatrix.VA.id_vec n0 n

  (** val coq_VF_prod : nat -> coq_VF -> Ring.coq_F **)

  let coq_VF_prod n v =
    vfold_left Ring.coq_Fmul n Ring.coq_Fone v

  (** val coq_VF_sum : nat -> coq_VF -> Ring.coq_F **)

  let coq_VF_sum n v =
    vfold_left Ring.coq_Fadd n Ring.coq_Fzero v

  (** val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF **)

  let coq_VF_add =
    FMatrix.VA.vector_plus

  (** val coq_VF_neg : nat -> coq_VF -> coq_VF **)

  let coq_VF_neg n v1 =
    vmap Ring.coq_Finv n v1

  (** val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF **)

  let coq_VF_sub n v1 v2 =
    coq_VF_add n v1 (coq_VF_neg n v2)

  (** val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF **)

  let coq_VF_mult n v1 v2 =
    vmap2 Ring.coq_Fmul n v1 v2

  (** val coq_VF_scale : nat -> coq_VF -> Ring.coq_F -> coq_VF **)

  let coq_VF_scale n v s =
    vmap (fun x -> Ring.coq_Fmul x s) n v

  (** val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Ring.coq_F **)

  let coq_VF_inProd =
    FMatrix.VA.dot_product

  (** val coq_VF_beq : nat -> coq_VF -> coq_VF -> bool **)

  let coq_VF_beq n r r' =
    bVforall2 Ring.coq_Fbool_eq n r r'

  (** val coq_VF_an_id : nat -> coq_VF -> bool **)

  let coq_VF_an_id n v =
    vfold_left (&&) n false
      (vbuild n (fun i _ -> coq_VF_beq n v (FMatrix.VA.id_vec n i)))

  type coq_MF = FMatrix.matrix

  (** val coq_MF_id : nat -> coq_MF **)

  let coq_MF_id =
    FMatrix.id_matrix

  (** val coq_MF_col : nat -> coq_MF -> nat -> coq_VF **)

  let coq_MF_col n m i =
    FMatrix.get_col n n m i

  (** val coq_MF_row : nat -> coq_MF -> nat -> coq_VF **)

  let coq_MF_row n m i =
    FMatrix.get_row n n m i

  (** val coq_MF_mult : nat -> coq_MF -> coq_MF -> coq_MF **)

  let coq_MF_mult n m m' =
    FMatrix.mat_mult n n n m m'

  (** val coq_MF_trans : nat -> coq_MF -> coq_MF **)

  let coq_MF_trans n m =
    FMatrix.mat_transpose n n m

  (** val coq_MF_CVmult : nat -> coq_MF -> coq_VF -> coq_VF **)

  let coq_MF_CVmult n m v =
    FMatrix.mat_vec_prod n n m v

  (** val coq_MF_VCmult : nat -> coq_VF -> coq_MF -> coq_VF **)

  let coq_MF_VCmult n v m =
    FMatrix.row_mat_to_vec n
      (FMatrix.mat_mult (S O) n n (FMatrix.vec_to_row_mat n v) m)

  (** val coq_MF_Fscal : nat -> coq_MF -> coq_VF -> coq_MF **)

  let coq_MF_Fscal n m v =
    FMatrix.mat_build n n (fun i j _ _ ->
      vnth n (coq_VF_mult n (FMatrix.get_row n n m i) v) j)

  (** val coq_MF_scal : nat -> coq_MF -> Ring.coq_F -> coq_MF **)

  let coq_MF_scal n m a =
    FMatrix.mat_build n n (fun i j _ _ ->
      Ring.coq_Fmul (FMatrix.get_elem n n m i j) a)

  (** val coq_MFisPermutation : nat -> coq_MF -> bool **)

  let coq_MFisPermutation n m =
    (&&) (bVforall (coq_VF_an_id n) n m)
      (bVforall (coq_VF_an_id n) n (FMatrix.mat_transpose n n m))
 end

module MatricesG =
 functor (Group:GroupSig) ->
 functor (Ring:RingSig) ->
 functor (M:sig
  val op : Group.coq_G -> Ring.coq_F -> Group.coq_G
 end) ->
 functor (MatF:sig
  module F :
   sig
    type coq_A = Ring.coq_F
   end

  module F_Eqset :
   sig
    type coq_A = F.coq_A
   end

  module F_Eqset_dec :
   sig
    module Eq :
     sig
      type coq_A = F.coq_A
     end

    val eqA_dec : Ring.coq_F -> Ring.coq_F -> bool
   end

  module FSemiRingT :
   sig
    module ES :
     sig
      module Eq :
       sig
        type coq_A = F.coq_A
       end

      val eqA_dec : Ring.coq_F -> Ring.coq_F -> bool
     end

    val coq_A0 : Ring.coq_F

    val coq_A1 : Ring.coq_F

    val coq_Aplus : Ring.coq_F -> Ring.coq_F -> Ring.coq_F

    val coq_Amult : Ring.coq_F -> Ring.coq_F -> Ring.coq_F
   end

  module FMatrix :
   sig
    module SR :
     sig
     end

    module VA :
     sig
      module SR :
       sig
       end

      val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t

      val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t

      val vector_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t -> FSemiRingT.ES.Eq.coq_A t ->
        FSemiRingT.ES.Eq.coq_A t

      val add_vectors :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A t t -> FSemiRingT.ES.Eq.coq_A t

      val dot_product :
        nat -> FSemiRingT.ES.Eq.coq_A t -> FSemiRingT.ES.Eq.coq_A t ->
        FSemiRingT.ES.Eq.coq_A
     end

    type matrix = FSemiRingT.ES.Eq.coq_A t t

    val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t

    val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t

    val get_elem :
      nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

    val mat_build_spec :
      nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) ->
      matrix

    val mat_build :
      nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) ->
      matrix

    val zero_matrix : nat -> nat -> matrix

    val id_matrix : nat -> matrix

    val inverse_matrix :
      (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat ->
      matrix -> matrix

    type row_mat = matrix

    type col_mat = matrix

    val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t -> row_mat

    val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t -> col_mat

    val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t

    val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t

    val mat_transpose : nat -> nat -> matrix -> matrix

    val vec_plus :
      nat -> FSemiRingT.ES.Eq.coq_A t -> FSemiRingT.ES.Eq.coq_A t ->
      FSemiRingT.ES.Eq.coq_A t

    val mat_plus :
      nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t t

    val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

    val mat_vec_prod :
      nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t ->
      FSemiRingT.ES.Eq.coq_A t

    val mat_forall2'_dec :
      nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

    val mat_forall2_dec :
      nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
   end

  type coq_VF = Ring.coq_F t

  val coq_VF_zero : nat -> Ring.coq_F t

  val coq_VF_one : nat -> Ring.coq_F t

  val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t

  val coq_VF_prod : nat -> coq_VF -> Ring.coq_F

  val coq_VF_sum : nat -> coq_VF -> Ring.coq_F

  val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

  val coq_VF_neg : nat -> coq_VF -> coq_VF

  val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

  val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

  val coq_VF_scale : nat -> coq_VF -> Ring.coq_F -> coq_VF

  val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Ring.coq_F

  val coq_VF_beq : nat -> coq_VF -> coq_VF -> bool

  val coq_VF_an_id : nat -> coq_VF -> bool

  type coq_MF = FMatrix.matrix

  val coq_MF_id : nat -> coq_MF

  val coq_MF_col : nat -> coq_MF -> nat -> coq_VF

  val coq_MF_row : nat -> coq_MF -> nat -> coq_VF

  val coq_MF_mult : nat -> coq_MF -> coq_MF -> coq_MF

  val coq_MF_trans : nat -> coq_MF -> coq_MF

  val coq_MF_CVmult : nat -> coq_MF -> coq_VF -> coq_VF

  val coq_MF_VCmult : nat -> coq_VF -> coq_MF -> coq_VF

  val coq_MF_Fscal : nat -> coq_MF -> coq_VF -> coq_MF

  val coq_MF_scal : nat -> coq_MF -> Ring.coq_F -> coq_MF

  val coq_MFisPermutation : nat -> coq_MF -> bool
 end) ->
 struct
  module AddMLemmas = ModuleAddationalLemmas(Group)(Ring)(M)

  type coq_VG = Group.coq_G t

  (** val coq_VG_id : nat -> Group.coq_G t **)

  let coq_VG_id =
    const Group.coq_Gone

  (** val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG **)

  let coq_VG_mult n v v' =
    vmap2 Group.coq_Gdot n v v'

  (** val coq_VG_inv : nat -> coq_VG -> coq_VG **)

  let coq_VG_inv n v =
    vmap Group.coq_Ginv n v

  (** val coq_VG_prod : nat -> coq_VG -> Group.coq_G **)

  let coq_VG_prod n v =
    vfold_left Group.coq_Gdot n Group.coq_Gone v

  (** val coq_VG_Pexp : nat -> coq_VG -> MatF.coq_VF -> coq_VG **)

  let coq_VG_Pexp n v v' =
    vmap2 M.op n v v'

  (** val coq_VG_Sexp : nat -> coq_VG -> Ring.coq_F -> coq_VG **)

  let coq_VG_Sexp n v e =
    vmap (fun x -> M.op x e) n v

  (** val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool **)

  let coq_VG_eq n m m' =
    bVforall2 Group.coq_Gbool_eq n m m'

  (** val coq_VG_MF_exp_coll : nat -> coq_VG -> MatF.coq_MF -> coq_VG **)

  let coq_VG_MF_exp_coll n c b =
    vbuild n (fun i _ ->
      coq_VG_prod n (coq_VG_Pexp n c (MatF.coq_MF_col n b i)))

  (** val coq_VG_MF_exp_row : nat -> coq_VG -> MatF.coq_MF -> coq_VG **)

  let coq_VG_MF_exp_row n c b =
    vbuild n (fun i _ -> coq_VG_prod n (coq_VG_Pexp n c (vnth n b i)))

  (** val coq_PexpMatrix : nat -> coq_VG -> MatF.coq_MF -> coq_VG **)

  let coq_PexpMatrix n c e =
    vmap (fun row -> coq_VG_prod n (coq_VG_Pexp n c row)) n e

  (** val coq_VG_scale_sum :
      nat -> nat -> nat -> MatF.coq_VF t t -> MatF.coq_VF t **)

  let coq_VG_scale_sum n j m b =
    vfold_left (fun x y -> vmap2 (MatF.coq_VF_add n) j x y) m
      (const (MatF.coq_VF_zero n) j) b
 end

module EncryptionSchemeProp =
 functor (Message:GroupSig) ->
 functor (Ciphertext:GroupSig) ->
 functor (Ring:RingSig) ->
 functor (Field:FieldSig) ->
 functor (VS:sig
  val op : Ciphertext.coq_G -> Field.coq_F -> Ciphertext.coq_G
 end) ->
 functor (MVS:sig
  val op3 : Ring.coq_F -> Field.coq_F -> Ring.coq_F
 end) ->
 functor (Enc:sig
  type coq_KGR

  type coq_PK

  type coq_SK

  type coq_M = Message.coq_G

  val coq_Mop : Message.coq_G -> Message.coq_G -> Message.coq_G

  val coq_Mzero : Message.coq_G

  val coq_Minv : Message.coq_G -> Message.coq_G

  val coq_Mbool_eq : Message.coq_G -> Message.coq_G -> bool

  val keygen : coq_KGR -> coq_PK * coq_SK

  val keygenMix : coq_KGR -> coq_PK

  val enc : coq_PK -> coq_M -> Ring.coq_F -> Ciphertext.coq_G

  val dec : coq_SK -> Ciphertext.coq_G -> coq_M

  val keymatch : coq_PK -> coq_SK -> bool
 end) ->
 struct
  module AddVSLemmas = VectorSpaceAddationalLemmas(Ciphertext)(Field)(VS)

  (** val reenc :
      Enc.coq_PK -> Ciphertext.coq_G -> Ring.coq_F -> Ciphertext.coq_G **)

  let reenc pk c r =
    Ciphertext.coq_Gdot (Enc.enc pk Enc.coq_Mzero r) c

  (** val decryptsToExt :
      Enc.coq_PK -> Ciphertext.coq_G -> Enc.coq_M -> Ring.coq_F -> bool **)

  let decryptsToExt pk c m r =
    let c' = Enc.enc pk m r in Ciphertext.coq_Gbool_eq c' c
 end

module BasicElGamal =
 functor (Group:GroupSig) ->
 functor (Field:FieldSig) ->
 functor (VS:sig
  val op : Group.coq_G -> Field.coq_F -> Group.coq_G
 end) ->
 functor (DualGroup:sig
  type coq_G = Group.coq_G * Group.coq_G

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : Group.coq_G * Group.coq_G

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Ginv : (Group.coq_G * Group.coq_G) -> Group.coq_G * Group.coq_G
 end) ->
 functor (DVS:sig
  val op : DualGroup.coq_G -> Field.coq_F -> Group.coq_G * Group.coq_G
 end) ->
 functor (MVS:sig
  val op3 : Field.coq_F -> Field.coq_F -> Field.coq_F
 end) ->
 struct
  module AddVSLemmas = VectorSpaceAddationalLemmas(Group)(Field)(VS)

  module AddDVSLemmas = VectorSpaceAddationalLemmas(DualGroup)(Field)(DVS)

  type coq_KGR = Group.coq_G * Field.coq_F

  type coq_PK = DualGroup.coq_G

  type coq_SK = Field.coq_F

  type coq_M = Group.coq_G

  (** val coq_Mop : Group.coq_G -> Group.coq_G -> Group.coq_G **)

  let coq_Mop =
    Group.coq_Gdot

  (** val coq_Mzero : Group.coq_G **)

  let coq_Mzero =
    Group.coq_Gone

  (** val coq_Minv : Group.coq_G -> Group.coq_G **)

  let coq_Minv =
    Group.coq_Ginv

  (** val coq_Mbool_eq : Group.coq_G -> Group.coq_G -> bool **)

  let coq_Mbool_eq =
    Group.coq_Gbool_eq

  (** val keygen : coq_KGR -> coq_PK * coq_SK **)

  let keygen kgr =
    (((fst kgr), (VS.op (fst kgr) (snd kgr))), (snd kgr))

  (** val keygenMix : coq_KGR -> coq_PK **)

  let keygenMix kgr =
    fst (keygen kgr)

  (** val enc : coq_PK -> Group.coq_G -> Field.coq_F -> DualGroup.coq_G **)

  let enc pk m r =
    ((VS.op (fst pk) r), (Group.coq_Gdot (VS.op (snd pk) r) m))

  (** val dec : Field.coq_F -> DualGroup.coq_G -> coq_M **)

  let dec sk c =
    Group.coq_Gdot (snd c) (Group.coq_Ginv (VS.op (fst c) sk))

  (** val keymatch : coq_PK -> coq_SK -> bool **)

  let keymatch pk sk =
    Group.coq_Gbool_eq (VS.op (fst pk) sk) (snd pk)
 end

module BasicComScheme =
 functor (Group:GroupSig) ->
 functor (Ring:RingSig) ->
 functor (M:sig
  val op : Group.coq_G -> Ring.coq_F -> Group.coq_G
 end) ->
 functor (Mo:sig
  module F :
   sig
    type coq_A = Ring.coq_F
   end

  module F_Eqset :
   sig
    type coq_A = F.coq_A
   end

  module F_Eqset_dec :
   sig
    module Eq :
     sig
      type coq_A = F.coq_A
     end

    val eqA_dec : Ring.coq_F -> Ring.coq_F -> bool
   end

  module FSemiRingT :
   sig
    module ES :
     sig
      module Eq :
       sig
        type coq_A = F.coq_A
       end

      val eqA_dec : Ring.coq_F -> Ring.coq_F -> bool
     end

    val coq_A0 : Ring.coq_F

    val coq_A1 : Ring.coq_F

    val coq_Aplus : Ring.coq_F -> Ring.coq_F -> Ring.coq_F

    val coq_Amult : Ring.coq_F -> Ring.coq_F -> Ring.coq_F
   end

  module FMatrix :
   sig
    module SR :
     sig
     end

    module VA :
     sig
      module SR :
       sig
       end

      val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t

      val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t

      val vector_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t -> FSemiRingT.ES.Eq.coq_A t ->
        FSemiRingT.ES.Eq.coq_A t

      val add_vectors :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A t t -> FSemiRingT.ES.Eq.coq_A t

      val dot_product :
        nat -> FSemiRingT.ES.Eq.coq_A t -> FSemiRingT.ES.Eq.coq_A t ->
        FSemiRingT.ES.Eq.coq_A
     end

    type matrix = FSemiRingT.ES.Eq.coq_A t t

    val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t

    val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t

    val get_elem :
      nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

    val mat_build_spec :
      nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) ->
      matrix

    val mat_build :
      nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) ->
      matrix

    val zero_matrix : nat -> nat -> matrix

    val id_matrix : nat -> matrix

    val inverse_matrix :
      (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat ->
      matrix -> matrix

    type row_mat = matrix

    type col_mat = matrix

    val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t -> row_mat

    val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t -> col_mat

    val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t

    val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t

    val mat_transpose : nat -> nat -> matrix -> matrix

    val vec_plus :
      nat -> FSemiRingT.ES.Eq.coq_A t -> FSemiRingT.ES.Eq.coq_A t ->
      FSemiRingT.ES.Eq.coq_A t

    val mat_plus :
      nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t t

    val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

    val mat_vec_prod :
      nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t ->
      FSemiRingT.ES.Eq.coq_A t

    val mat_forall2'_dec :
      nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

    val mat_forall2_dec :
      nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
   end

  type coq_VF = Ring.coq_F t

  val coq_VF_zero : nat -> Ring.coq_F t

  val coq_VF_one : nat -> Ring.coq_F t

  val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t

  val coq_VF_prod : nat -> coq_VF -> Ring.coq_F

  val coq_VF_sum : nat -> coq_VF -> Ring.coq_F

  val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

  val coq_VF_neg : nat -> coq_VF -> coq_VF

  val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

  val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

  val coq_VF_scale : nat -> coq_VF -> Ring.coq_F -> coq_VF

  val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Ring.coq_F

  val coq_VF_beq : nat -> coq_VF -> coq_VF -> bool

  val coq_VF_an_id : nat -> coq_VF -> bool

  type coq_MF = FMatrix.matrix

  val coq_MF_id : nat -> coq_MF

  val coq_MF_col : nat -> coq_MF -> nat -> coq_VF

  val coq_MF_row : nat -> coq_MF -> nat -> coq_VF

  val coq_MF_mult : nat -> coq_MF -> coq_MF -> coq_MF

  val coq_MF_trans : nat -> coq_MF -> coq_MF

  val coq_MF_CVmult : nat -> coq_MF -> coq_VF -> coq_VF

  val coq_MF_VCmult : nat -> coq_VF -> coq_MF -> coq_VF

  val coq_MF_Fscal : nat -> coq_MF -> coq_VF -> coq_MF

  val coq_MF_scal : nat -> coq_MF -> Ring.coq_F -> coq_MF

  val coq_MFisPermutation : nat -> coq_MF -> bool
 end) ->
 struct
  module AddMLemmas = ModuleAddationalLemmas(Group)(Ring)(M)

  module MoM = MatricesG(Group)(Ring)(M)(Mo)

  (** val coq_PC :
      Group.coq_G -> Group.coq_G -> Ring.coq_F -> Ring.coq_F -> Group.coq_G **)

  let coq_PC h h1 m r =
    Group.coq_Gdot (M.op h r) (M.op h1 m)

  (** val comPC :
      nat -> Group.coq_G -> Group.coq_G -> Mo.coq_VF -> Mo.coq_VF ->
      MoM.coq_VG **)

  let comPC n h h1 m r =
    vmap2 (coq_PC h h1) n m r
 end

module HardProblems =
 functor (Group:GroupSig) ->
 functor (Ring:RingSig) ->
 functor (M:sig
  val op : Group.coq_G -> Ring.coq_F -> Group.coq_G
 end) ->
 struct
  (** val dLog : (Group.coq_G * Group.coq_G) -> Ring.coq_F -> bool **)

  let dLog s w =
    let g0 = fst s in let gtox = snd s in Group.coq_Gbool_eq gtox (M.op g0 w)
 end

module BasicSigmas =
 functor (Group:GroupSig) ->
 functor (Field:FieldSig) ->
 functor (VS:sig
  val op : Group.coq_G -> Field.coq_F -> Group.coq_G
 end) ->
 struct
  module HardProb = HardProblems(Group)(Field)(VS)

  module Mo = MatricesFIns(Field)

  module PC = BasicComScheme(Group)(Field)(VS)(Mo)

  module AddVSLemmas = VectorSpaceAddationalLemmas(Group)(Field)(VS)

  (** val valid_P0 :
      (Group.coq_G * Group.coq_G) -> Field.coq_F -> Field.coq_F ->
      (Group.coq_G * Group.coq_G) * Group.coq_G **)

  let valid_P0 ggtox r _ =
    let g0 = fst ggtox in (ggtox, (VS.op g0 r))

  (** val valid_V0 :
      ((Group.coq_G * Group.coq_G) * Group.coq_G) -> Field.coq_F ->
      ((Group.coq_G * Group.coq_G) * Group.coq_G) * Field.coq_F **)

  let valid_V0 ggtoxgtor c =
    (ggtoxgtor, c)

  (** val valid_P1 :
      (((Group.coq_G * Group.coq_G) * Group.coq_G) * Field.coq_F) ->
      Field.coq_F -> Field.coq_F ->
      (((Group.coq_G * Group.coq_G) * Group.coq_G) * Field.coq_F) * Field.coq_F **)

  let valid_P1 ggtoxgtorc r x =
    let c = snd ggtoxgtorc in
    let s = Field.coq_Fadd r (Field.coq_Fmul c x) in (ggtoxgtorc, s)

  (** val valid_V1 :
      ((((Group.coq_G * Group.coq_G) * Group.coq_G) * Field.coq_F) * Field.coq_F)
      -> bool **)

  let valid_V1 ggtoxgtorcs =
    let g0 = fst (fst (fst (fst ggtoxgtorcs))) in
    let gtox = snd (fst (fst (fst ggtoxgtorcs))) in
    let gtor = snd (fst (fst ggtoxgtorcs)) in
    let c = snd (fst ggtoxgtorcs) in
    let s = snd ggtoxgtorcs in
    Group.coq_Gbool_eq (VS.op g0 s) (Group.coq_Gdot (VS.op gtox c) gtor)

  (** val simulator_mapper :
      (Group.coq_G * Group.coq_G) -> Field.coq_F -> Field.coq_F ->
      Field.coq_F -> Field.coq_F **)

  let simulator_mapper _ x c r =
    Field.coq_Fadd r (Field.coq_Fmul x c)

  (** val simulator_mapper_inv :
      (Group.coq_G * Group.coq_G) -> Field.coq_F -> Field.coq_F ->
      Field.coq_F -> Field.coq_F **)

  let simulator_mapper_inv _ x c t0 =
    Field.coq_Fadd t0 (Field.coq_Finv (Field.coq_Fmul x c))

  (** val simulator :
      (Group.coq_G * Group.coq_G) -> Field.coq_F -> Field.coq_F ->
      (((Group.coq_G * Group.coq_G) * Group.coq_G) * Field.coq_F) * Field.coq_F **)

  let simulator ggtox z e =
    let g0 = fst ggtox in
    let gtox = snd ggtox in
    (((ggtox, (Group.coq_Gdot (VS.op g0 z) (Group.coq_Ginv (VS.op gtox e)))),
    e), z)

  (** val extractor :
      Field.coq_F -> Field.coq_F -> Field.coq_F -> Field.coq_F -> Field.coq_F **)

  let extractor s1 s2 c1 c2 =
    Field.coq_Fmul (Field.coq_Fadd s1 (Field.coq_Finv s2))
      (Field.coq_FmulInv (Field.coq_Fadd c1 (Field.coq_Finv c2)))

  (** val disjoint : Field.coq_F -> Field.coq_F -> bool **)

  let disjoint c1 c2 =
    negb (Field.coq_Fbool_eq c1 c2)

  (** val dLogForm : Field.coq_F Sigma.form **)

  let dLogForm =
    { Sigma.coq_Rel = (Obj.magic HardProb.dLog); Sigma.add = Field.coq_Fadd;
      Sigma.zero = Field.coq_Fzero; Sigma.inv = Field.coq_Finv;
      Sigma.bool_eq = Field.coq_Fbool_eq; Sigma.disjoint = disjoint;
      Sigma.coq_P0 = (Obj.magic valid_P0); Sigma.coq_V0 =
      (Obj.magic valid_V0); Sigma.coq_P1 = (Obj.magic valid_P1);
      Sigma.coq_V1 = (Obj.magic valid_V1); Sigma.simulator =
      (Obj.magic simulator); Sigma.simMap = (Obj.magic simulator_mapper);
      Sigma.simMapInv = (Obj.magic simulator_mapper_inv); Sigma.extractor =
      (Obj.magic extractor) }

  (** val emptyRel : Group.coq_G -> Field.coq_F -> bool **)

  let emptyRel _ _ =
    true

  (** val empty_P0 :
      Group.coq_G -> Field.coq_F -> Field.coq_F -> Group.coq_G * Group.coq_G **)

  let empty_P0 g0 _ _ =
    (g0, g0)

  (** val empty_V0 :
      (Group.coq_G * Group.coq_G) -> Field.coq_F ->
      (Group.coq_G * Group.coq_G) * Field.coq_F **)

  let empty_V0 g0 c =
    (g0, c)

  (** val empty_P1 :
      ((Group.coq_G * Group.coq_G) * Field.coq_F) -> Field.coq_F ->
      Field.coq_F -> ((Group.coq_G * Group.coq_G) * Field.coq_F) * Field.coq_F **)

  let empty_P1 g0 _ _ =
    (g0, (snd g0))

  (** val empty_V1 :
      (((Group.coq_G * Group.coq_G) * Field.coq_F) * Field.coq_F) -> bool **)

  let empty_V1 _ =
    true

  (** val empty_simulator_mapper :
      Group.coq_G -> Field.coq_F -> Field.coq_F -> Field.coq_F -> Field.coq_F **)

  let empty_simulator_mapper _ _ _ r =
    r

  (** val empty_simulator_mapper_inv :
      Group.coq_G -> Field.coq_F -> Field.coq_F -> Field.coq_F -> Field.coq_F **)

  let empty_simulator_mapper_inv _ _ _ t0 =
    t0

  (** val empty_simulator :
      Group.coq_G -> Field.coq_F -> Field.coq_F ->
      ((Group.coq_G * Group.coq_G) * Field.coq_F) * Field.coq_F **)

  let empty_simulator g0 _ e =
    (((g0, g0), e), e)

  (** val empty_mapper :
      Field.coq_F -> Field.coq_F -> Field.coq_F -> Field.coq_F -> Field.coq_F **)

  let empty_mapper s1 s2 c1 c2 =
    Field.coq_Fmul (Field.coq_Fadd s1 (Field.coq_Finv s2))
      (Field.coq_FmulInv (Field.coq_Fadd c1 (Field.coq_Finv c2)))

  (** val emptyForm : Field.coq_F Sigma.form **)

  let emptyForm =
    { Sigma.coq_Rel = (Obj.magic emptyRel); Sigma.add = Field.coq_Fadd;
      Sigma.zero = Field.coq_Fzero; Sigma.inv = Field.coq_Finv;
      Sigma.bool_eq = Field.coq_Fbool_eq; Sigma.disjoint = disjoint;
      Sigma.coq_P0 = (Obj.magic empty_P0); Sigma.coq_V0 =
      (Obj.magic empty_V0); Sigma.coq_P1 = (Obj.magic empty_P1);
      Sigma.coq_V1 = (Obj.magic empty_V1); Sigma.simulator =
      (Obj.magic empty_simulator); Sigma.simMap =
      (Obj.magic empty_simulator_mapper); Sigma.simMapInv =
      (Obj.magic empty_simulator_mapper_inv); Sigma.extractor =
      (Obj.magic empty_mapper) }

  (** val dLog2 :
      ((Group.coq_G * Group.coq_G) * Group.coq_G) ->
      (Field.coq_F * Field.coq_F) -> bool **)

  let dLog2 s w =
    let g0 = fst (fst s) in
    let h = snd (fst s) in
    let gtox = snd s in
    Group.coq_Gbool_eq gtox (PC.coq_PC g0 h (fst w) (snd w))

  (** val dLog2_P0 :
      ((Group.coq_G * Group.coq_G) * Group.coq_G) ->
      (Field.coq_F * Field.coq_F) -> (Field.coq_F * Field.coq_F) ->
      ((Group.coq_G * Group.coq_G) * Group.coq_G) * Group.coq_G **)

  let dLog2_P0 ggtox r _ =
    let g0 = fst (fst ggtox) in
    let h = snd (fst ggtox) in (ggtox, (PC.coq_PC g0 h (fst r) (snd r)))

  (** val dLog2_V0 :
      (((Group.coq_G * Group.coq_G) * Group.coq_G) * Group.coq_G) ->
      Field.coq_F ->
      (((Group.coq_G * Group.coq_G) * Group.coq_G) * Group.coq_G) * Field.coq_F **)

  let dLog2_V0 ggtoxgtor c =
    (ggtoxgtor, c)

  (** val dLog2_P1 :
      ((((Group.coq_G * Group.coq_G) * Group.coq_G) * Group.coq_G) * Field.coq_F)
      -> (Field.coq_F * Field.coq_F) -> (Field.coq_F * Field.coq_F) ->
      ((((Group.coq_G * Group.coq_G) * Group.coq_G) * Group.coq_G) * Field.coq_F) * (Field.coq_F * Field.coq_F) **)

  let dLog2_P1 ggtoxgtorc r x =
    let c = snd ggtoxgtorc in
    let s1 = Field.coq_Fadd (fst r) (Field.coq_Fmul (fst x) c) in
    let s2 = Field.coq_Fadd (snd r) (Field.coq_Fmul (snd x) c) in
    (ggtoxgtorc, (s1, s2))

  (** val dLog2_V1 :
      (((((Group.coq_G * Group.coq_G) * Group.coq_G) * Group.coq_G) * Field.coq_F) * (Field.coq_F * Field.coq_F))
      -> bool **)

  let dLog2_V1 ggtoxgtorcs =
    let g0 = fst (fst (fst (fst (fst ggtoxgtorcs)))) in
    let h = snd (fst (fst (fst (fst ggtoxgtorcs)))) in
    let gtox = snd (fst (fst (fst ggtoxgtorcs))) in
    let gtor = snd (fst (fst ggtoxgtorcs)) in
    let c = snd (fst ggtoxgtorcs) in
    let s1 = fst (snd ggtoxgtorcs) in
    let s2 = snd (snd ggtoxgtorcs) in
    Group.coq_Gbool_eq (PC.coq_PC g0 h s1 s2)
      (Group.coq_Gdot (VS.op gtox c) gtor)

  (** val dLog2_simulator_mapper :
      ((Group.coq_G * Group.coq_G) * Group.coq_G) ->
      (Field.coq_F * Field.coq_F) -> Field.coq_F ->
      (Field.coq_F * Field.coq_F) -> Field.coq_F * Field.coq_F **)

  let dLog2_simulator_mapper _ x c r =
    ((Field.coq_Fadd (fst r) (Field.coq_Fmul (fst x) c)),
      (Field.coq_Fadd (snd r) (Field.coq_Fmul (snd x) c)))

  (** val dLog2_simulator_mapper_inv :
      ((Group.coq_G * Group.coq_G) * Group.coq_G) ->
      (Field.coq_F * Field.coq_F) -> Field.coq_F ->
      (Field.coq_F * Field.coq_F) -> Field.coq_F * Field.coq_F **)

  let dLog2_simulator_mapper_inv _ x c t0 =
    ((Field.coq_Fadd (fst t0) (Field.coq_Finv (Field.coq_Fmul (fst x) c))),
      (Field.coq_Fadd (snd t0) (Field.coq_Finv (Field.coq_Fmul (snd x) c))))

  (** val dLog2_simulator :
      ((Group.coq_G * Group.coq_G) * Group.coq_G) ->
      (Field.coq_F * Field.coq_F) -> Field.coq_F ->
      ((((Group.coq_G * Group.coq_G) * Group.coq_G) * Group.coq_G) * Field.coq_F) * (Field.coq_F * Field.coq_F) **)

  let dLog2_simulator ggtox z e =
    let g0 = fst (fst ggtox) in
    let h = snd (fst ggtox) in
    let gtox = snd ggtox in
    (((ggtox,
    (Group.coq_Gdot (PC.coq_PC g0 h (fst z) (snd z))
      (Group.coq_Ginv (VS.op gtox e)))), e), z)

  (** val dLog2_extractor :
      (Field.coq_F * Field.coq_F) -> (Field.coq_F * Field.coq_F) ->
      Field.coq_F -> Field.coq_F -> Field.coq_F * Field.coq_F **)

  let dLog2_extractor s1 s2 c1 c2 =
    ((Field.coq_Fmul (Field.coq_Fadd (fst s1) (Field.coq_Finv (fst s2)))
       (Field.coq_FmulInv (Field.coq_Fadd c1 (Field.coq_Finv c2)))),
      (Field.coq_Fmul (Field.coq_Fadd (snd s1) (Field.coq_Finv (snd s2)))
        (Field.coq_FmulInv (Field.coq_Fadd c1 (Field.coq_Finv c2)))))

  (** val dLog2Form : Field.coq_F Sigma.form **)

  let dLog2Form =
    { Sigma.coq_Rel = (Obj.magic dLog2); Sigma.add = Field.coq_Fadd;
      Sigma.zero = Field.coq_Fzero; Sigma.inv = Field.coq_Finv;
      Sigma.bool_eq = Field.coq_Fbool_eq; Sigma.disjoint = disjoint;
      Sigma.coq_P0 = (Obj.magic dLog2_P0); Sigma.coq_V0 =
      (Obj.magic dLog2_V0); Sigma.coq_P1 = (Obj.magic dLog2_P1);
      Sigma.coq_V1 = (Obj.magic dLog2_V1); Sigma.simulator =
      (Obj.magic dLog2_simulator); Sigma.simMap =
      (Obj.magic dLog2_simulator_mapper); Sigma.simMapInv =
      (Obj.magic dLog2_simulator_mapper_inv); Sigma.extractor =
      (Obj.magic dLog2_extractor) }
 end

module ElectionGuard =
 functor (ElectionGuardG:GroupSig) ->
 functor (ElectionGuardF:FieldSig) ->
 functor (ElectionGuardVS:sig
  val op :
    ElectionGuardG.coq_G -> ElectionGuardF.coq_F -> ElectionGuardG.coq_G
 end) ->
 struct
  module BS = BasicSigmas(ElectionGuardG)(ElectionGuardF)(ElectionGuardVS)

  module DG = DualGroupIns(ElectionGuardG)

  module DVS =
   DualVectorSpaceIns(ElectionGuardG)(DG)(ElectionGuardF)(ElectionGuardVS)

  module MVS = VectorSpaceModuleSameGroupInsIns(DG)(ElectionGuardF)(DVS)

  module ES =
   BasicElGamal(ElectionGuardG)(ElectionGuardF)(ElectionGuardVS)(DG)(DVS)(MVS)

  module ALES =
   EncryptionSchemeProp(ElectionGuardG)(DG)(ElectionGuardF)(ElectionGuardF)(DVS)(MVS)(ES)

  module MatrixF = MatricesFIns(ElectionGuardF)

  module Matrix =
   MatricesG(ElectionGuardG)(ElectionGuardF)(ElectionGuardVS)(MatrixF)

  module MoC = MatricesG(DG)(ElectionGuardF)(DVS)(MatrixF)

  (** val coq_DHTForm : ElectionGuardF.coq_F Sigma.form **)

  let coq_DHTForm =
    eqSigmaProtocol BS.dLogForm

  (** val coq_DHTDisForm : ElectionGuardF.coq_F Sigma.form **)

  let coq_DHTDisForm =
    disSigmaProtocol coq_DHTForm

  (** val oneOrZero :
      ElectionGuardF.coq_F Sigma.coq_S -> ElectionGuardF.coq_F Sigma.coq_S **)

  let oneOrZero s =
    let g0 = fst (fst (Obj.magic s)) in
    let h = snd (fst (Obj.magic s)) in
    let gtox = fst (snd (Obj.magic s)) in
    let htox = snd (snd (Obj.magic s)) in
    Obj.magic (((g0, gtox), (h, htox)), ((g0, gtox), (h,
      (ElectionGuardG.coq_Gdot htox (ElectionGuardG.coq_Ginv g0)))))

  (** val oneOrZeroCipher :
      ES.coq_PK -> DG.coq_G -> ElectionGuardF.coq_F Sigma.coq_S **)

  let oneOrZeroCipher pk c =
    oneOrZero (Obj.magic (pk, c))

  (** val decFactorStatment :
      ES.coq_PK -> DG.coq_G -> ElectionGuardG.coq_G -> ElectionGuardF.coq_F
      Sigma.coq_S **)

  let decFactorStatment pk c d =
    Obj.magic (pk, ((fst c), d))

  type recChalType = __

  type recChalTypeSelDec = __

  (** val coq_OneOfNSigma : nat -> recChalType Sigma.form **)

  let rec coq_OneOfNSigma = function
  | O -> Obj.magic coq_DHTForm
  | S a -> Obj.magic parSigmaProtocol (coq_OneOfNSigma a) coq_DHTDisForm

  (** val coq_DecryptionSigma : nat -> recChalType Sigma.form **)

  let rec coq_DecryptionSigma = function
  | O -> Obj.magic BS.emptyForm
  | S a -> Obj.magic parSigmaProtocol (coq_DecryptionSigma a) coq_DHTForm

  (** val coq_BallotDecSigma : nat -> nat -> recChalTypeSelDec Sigma.form **)

  let rec coq_BallotDecSigma numSel numAuth =
    match numSel with
    | O -> Obj.magic BS.emptyForm
    | S a ->
      Obj.magic parSigmaProtocol (coq_BallotDecSigma a numAuth)
        (coq_DecryptionSigma numAuth)

  (** val coq_OneOfNStatment :
      nat -> ES.coq_PK -> DG.coq_G -> DG.coq_G t -> recChalType Sigma.coq_S **)

  let rec coq_OneOfNStatment _ pk cProd = function
  | Nil ->
    Obj.magic (((fst pk), (fst cProd)), ((snd pk),
      (ElectionGuardG.coq_Gdot (snd cProd) (ElectionGuardG.coq_Ginv (fst pk)))))
  | Cons (a, n0, b) ->
    Obj.magic ((coq_OneOfNStatment n0 pk cProd b), (oneOrZeroCipher pk a))

  (** val coq_DecryptionSigmaStatment :
      nat -> (ElectionGuardG.coq_G * ElectionGuardG.coq_G) ->
      ElectionGuardG.coq_G -> ElectionGuardG.coq_G t -> ElectionGuardG.coq_G
      t -> recChalType Sigma.coq_S **)

  let rec coq_DecryptionSigmaStatment n c g0 v v1 =
    match n with
    | O -> Obj.magic ElectionGuardG.coq_Gone
    | S a ->
      Obj.magic ((coq_DecryptionSigmaStatment a c g0 (tl a v) (tl a v1)),
        (decFactorStatment (g0, (hd a v)) c (hd a v1)))

  (** val coq_BallotDecSigmaStatment :
      nat -> nat -> ElectionGuardG.coq_G -> ElectionGuardG.coq_G t ->
      DG.coq_G t -> ElectionGuardG.coq_G t t -> recChalTypeSelDec Sigma.coq_S **)

  let rec coq_BallotDecSigmaStatment numSel numAuth g0 pk v v1 =
    match numSel with
    | O -> Obj.magic ElectionGuardG.coq_Gone
    | S a ->
      Obj.magic
        ((coq_BallotDecSigmaStatment a numAuth g0 pk (tl a v) (tl a v1)),
        (coq_DecryptionSigmaStatment numAuth (hd a v) g0 pk (hd a v1)))

  (** val mapToGroup :
      ElectionGuardG.coq_G -> ElectionGuardF.coq_F -> ElectionGuardG.coq_G **)

  let mapToGroup =
    ElectionGuardVS.op

  type 'a coq_ProofTranscript = ('a Sigma.coq_C * 'a) * 'a Sigma.coq_T

  (** val coq_ProofTranDecAuthComm :
      nat -> nat -> recChalTypeSelDec Sigma.coq_C -> recChalTypeSelDec
      Sigma.coq_C **)

  let rec coq_ProofTranDecAuthComm n numAuth a =
    match n with
    | O -> a
    | S a0 ->
      Obj.magic ((coq_ProofTranDecAuthComm a0 numAuth (fst (Obj.magic a))),
        (fst (snd (Obj.magic a))))

  (** val coq_ProofTranDecAuthChal :
      nat -> nat -> recChalTypeSelDec -> recChalTypeSelDec **)

  let rec coq_ProofTranDecAuthChal n numAuth a =
    match n with
    | O -> a
    | S a0 ->
      Obj.magic ((coq_ProofTranDecAuthChal a0 numAuth (fst (Obj.magic a))),
        (fst (snd (Obj.magic a))))

  (** val coq_ProofTranDecAuthResp :
      nat -> nat -> recChalTypeSelDec Sigma.coq_T -> recChalTypeSelDec
      Sigma.coq_T **)

  let rec coq_ProofTranDecAuthResp n numAuth a =
    match n with
    | O -> a
    | S a0 ->
      Obj.magic ((coq_ProofTranDecAuthResp a0 numAuth (fst (Obj.magic a))),
        (fst (snd (Obj.magic a))))

  (** val coq_ProofTranDecAuth :
      nat -> nat -> recChalTypeSelDec coq_ProofTranscript ->
      recChalTypeSelDec coq_ProofTranscript **)

  let coq_ProofTranDecAuth n numAuth proof =
    (((coq_ProofTranDecAuthComm n numAuth (fst (fst proof))),
      (coq_ProofTranDecAuthChal n numAuth (snd (fst proof)))),
      (coq_ProofTranDecAuthResp n numAuth (snd proof)))

  (** val coq_TransComp :
      'a1 Sigma.form -> 'a1 Sigma.coq_S -> 'a1 coq_ProofTranscript -> (('a1
      Sigma.coq_S * 'a1 Sigma.coq_C) * 'a1) * 'a1 Sigma.coq_T **)

  let coq_TransComp _ s proofs =
    (((s, (fst (fst proofs))), (snd (fst proofs))), (snd proofs))

  type tally = __

  type ballot = __

  type ballotProof = __

  (** val coq_SelectionVerifier :
      ES.coq_PK -> nat -> DG.coq_G t -> recChalType coq_ProofTranscript ->
      bool **)

  let coq_SelectionVerifier pk numSel selections proof =
    let prod = MoC.coq_VG_prod numSel selections in
    let statment = coq_OneOfNStatment numSel pk prod selections in
    (coq_OneOfNSigma numSel).Sigma.coq_V1
      (coq_TransComp (coq_OneOfNSigma numSel) statment proof)

  (** val coq_BallotVerifier :
      ES.coq_PK -> nat -> nat t -> ballot -> ballotProof -> bool **)

  let rec coq_BallotVerifier pk _ numSel v1 v2 =
    match numSel with
    | Nil -> true
    | Cons (h, n, t0) ->
      (&&)
        (coq_SelectionVerifier pk (hd n (Cons (h, n, t0)))
          (fst (Obj.magic v1)) (fst (Obj.magic v2)))
        (coq_BallotVerifier pk n t0 (snd (Obj.magic v1)) (snd (Obj.magic v2)))

  type decryptionFactors = __

  type decrytionProof = __

  (** val coq_SelectionDecVerifier :
      nat -> nat -> ElectionGuardG.coq_G -> ElectionGuardG.coq_G t ->
      DG.coq_G t -> ElectionGuardG.coq_G t t -> recChalTypeSelDec
      coq_ProofTranscript -> bool **)

  let coq_SelectionDecVerifier numSel numAuth g0 pks selections decFactors proof =
    let statment =
      coq_BallotDecSigmaStatment numSel numAuth g0 pks selections decFactors
    in
    (coq_BallotDecSigma numSel numAuth).Sigma.coq_V1
      (coq_TransComp (coq_BallotDecSigma numSel numAuth) statment proof)

  (** val coq_DecryptionVerifier :
      nat -> nat -> ElectionGuardG.coq_G -> ElectionGuardG.coq_G t -> nat t
      -> ballot -> decryptionFactors -> decrytionProof -> bool **)

  let rec coq_DecryptionVerifier _ numAuth g0 pks numSel v1 v2 v3 =
    match numSel with
    | Nil -> true
    | Cons (h, n, t0) ->
      (&&)
        (coq_SelectionDecVerifier (hd n (Cons (h, n, t0))) numAuth g0 pks
          (fst (Obj.magic v1)) (fst (Obj.magic v2)) (fst (Obj.magic v3)))
        (coq_DecryptionVerifier n numAuth g0 pks t0 (snd (Obj.magic v1))
          (snd (Obj.magic v2)) (snd (Obj.magic v3)))

  (** val coq_SumOfProd :
      nat -> recChalType Sigma.coq_W -> ElectionGuardF.coq_F **)

  let rec coq_SumOfProd numAuth x =
    match numAuth with
    | O -> ElectionGuardF.coq_Fzero
    | S a ->
      ElectionGuardF.coq_Fadd (snd (Obj.magic x))
        (coq_SumOfProd a (fst (Obj.magic x)))

  (** val multBallots : nat -> nat t -> ballot -> ballot -> ballot **)

  let rec multBallots _ numSel x x0 =
    match numSel with
    | Nil -> Obj.magic ElectionGuardG.coq_Gone
    | Cons (h, n, t0) ->
      Obj.magic
        ((MoC.coq_VG_mult (hd n (Cons (h, n, t0))) (fst (Obj.magic x))
           (fst (Obj.magic x0))),
        (multBallots n t0 (snd (Obj.magic x)) (snd (Obj.magic x0))))

  (** val zeroBallot : nat -> nat t -> ballot **)

  let rec zeroBallot _ = function
  | Nil -> Obj.magic ElectionGuardG.coq_Gone
  | Cons (h, n, t0) -> Obj.magic ((MoC.coq_VG_id h), (zeroBallot n t0))

  (** val coq_Verifier :
      nat -> nat -> nat -> nat t -> ElectionGuardG.coq_G ->
      ElectionGuardG.coq_G t -> ballot t -> ballotProof t ->
      decryptionFactors -> decrytionProof -> bool **)

  let coq_Verifier numTrustees numCast numContests numSel g0 pks castBallots ballotProofs decFactors decProofs =
    let pk = (g0, (Matrix.coq_VG_prod numTrustees pks)) in
    let tally0 =
      vfold_left (multBallots numContests numSel) numCast
        (zeroBallot numContests numSel) castBallots
    in
    (&&)
      (bVforall2 (coq_BallotVerifier pk numContests numSel) numCast
        castBallots ballotProofs)
      (coq_DecryptionVerifier numContests numTrustees g0 pks numSel tally0
        decFactors decProofs)
 end

(** val pminusN : Big.big_int -> Big.big_int -> Big.big_int **)

let pminusN x y =
  match Coq_Pos.sub_mask x y with
  | Coq_Pos.IsPos k -> k
  | _ -> Big.zero

(** val is_lt : Big.big_int -> Big.big_int -> bool **)

let is_lt n m =
  match Coq_Pos.compare n m with
  | Lt -> true
  | _ -> false

(** val div_eucl0 :
    Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)

let rec div_eucl0 a b =
  Big.positive_case
    (fun a' ->
    let (q0, r) = div_eucl0 a' b in
    (Big.n_case
       (fun _ ->
       Big.n_case
         (fun _ -> (Big.zero, Big.zero))
         (fun r0 ->
         if is_lt (Big.doubleplusone r0) b
         then (Big.zero, (Big.doubleplusone r0))
         else (Big.one, (pminusN (Big.doubleplusone r0) b)))
         r)
       (fun q1 ->
       Big.n_case
         (fun _ ->
         if is_lt Big.one b
         then ((Big.double q1), Big.one)
         else ((Big.doubleplusone q1), Big.zero))
         (fun r0 ->
         if is_lt (Big.doubleplusone r0) b
         then ((Big.double q1), (Big.doubleplusone r0))
         else ((Big.doubleplusone q1), (pminusN (Big.doubleplusone r0) b)))
         r)
       q0))
    (fun a' ->
    let (q0, r) = div_eucl0 a' b in
    (Big.n_case
       (fun _ ->
       Big.n_case
         (fun _ -> (Big.zero, Big.zero))
         (fun r0 ->
         if is_lt (Big.double r0) b
         then (Big.zero, (Big.double r0))
         else (Big.one, (pminusN (Big.double r0) b)))
         r)
       (fun q1 ->
       Big.n_case
         (fun _ -> ((Big.double q1), Big.zero))
         (fun r0 ->
         if is_lt (Big.double r0) b
         then ((Big.double q1), (Big.double r0))
         else ((Big.doubleplusone q1), (pminusN (Big.double r0) b)))
         r)
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
     (fun r ->
     let (q', n0) = div_eucl0 b r in
     (Big.n_case
        (fun _ -> Some ((Big.one, (Z.opp (Z.of_N q0))), r))
        (fun r' ->
        Big.positive_case
          (fun c' ->
          match egcd_log2 r r' c' with
          | Some p0 ->
            let (p1, w') = p0 in
            let (u', v') = p1 in
            let u = Z.sub u' (Z.mul v' (Z.of_N q')) in
            Some ((u, (Z.sub v' (Z.mul (Z.of_N q0) u))), w')
          | None -> None)
          (fun c' ->
          match egcd_log2 r r' c' with
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
  Z.modulo Big.zero n

(** val one : Big.big_int -> znz **)

let one n =
  Z.modulo Big.one n

(** val add0 : Big.big_int -> znz -> znz -> znz **)

let add0 n v1 v2 =
  Z.modulo (Z.add (val0 n v1) (val0 n v2)) n

(** val sub0 : Big.big_int -> znz -> znz -> znz **)

let sub0 n v1 v2 =
  Z.modulo (Z.sub (val0 n v1) (val0 n v2)) n

(** val mul0 : Big.big_int -> znz -> znz -> znz **)

let mul0 n v1 v2 =
  Z.modulo (Z.mul (val0 n v1) (val0 n v2)) n

(** val opp0 : Big.big_int -> znz -> znz **)

let opp0 n v =
  Z.modulo (Z.opp (val0 n v)) n

(** val inv0 : Big.big_int -> znz -> znz **)

let inv0 p0 v =
  Z.modulo (fst (fst (zegcd (val0 p0 v) p0))) p0

(** val div : Big.big_int -> znz -> znz -> znz **)

let div p0 v1 v2 =
  mul0 p0 v1 (inv0 p0 v2)

(** val p : Big.big_int **)

let p =
  (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.double (Big.double (Big.double (Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone
    Big.one)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val q : Big.big_int **)

let q =
  (Big.doubleplusone (Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    Big.one)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

type fp = znz

(** val fpMul : fp -> fp -> fp **)

let fpMul =
  mul0 p

(** val fpOne : fp **)

let fpOne =
  one p

type f = znz

(** val fadd : f -> f -> f **)

let fadd =
  add0 q

(** val fzero : f **)

let fzero =
  zero0 q

(** val fbool_eq_init : f -> f -> bool **)

let fbool_eq_init a b =
  Z.eqb (val0 q a) (val0 q b)

(** val fsub : f -> f -> f **)

let fsub =
  sub0 q

(** val finv : f -> f **)

let finv =
  opp0 q

(** val fmul : f -> f -> f **)

let fmul =
  mul0 q

(** val fone : f **)

let fone =
  one q

(** val fmulInv : f -> f **)

let fmulInv =
  inv0 q

(** val fdiv : f -> f -> f **)

let fdiv =
  div q

(** val binary_power_mult2 : fp -> Big.big_int -> fp -> fp **)

let rec binary_power_mult2 x n acc =
  Big.positive_case
    (fun w -> binary_power_mult2 (fpMul x x) w (fpMul acc x))
    (fun w -> binary_power_mult2 (fpMul x x) w acc)
    (fun _ -> fpMul x acc)
    n

(** val binary_power2 : fp -> f -> fp **)

let binary_power2 x n =
  let e = val0 q n in
  (Big.z_case
     (fun _ -> fpOne)
     (fun p0 -> binary_power_mult2 x p0 fpOne)
     (fun _ -> fpOne)
     e)

type g = fp

(** val gdot : g -> g -> g **)

let gdot a b =
  mul0 p a b

(** val gone : g **)

let gone =
  one p

(** val gbool_eq_init : g -> g -> bool **)

let gbool_eq_init a b =
  Z.eqb (val0 p a) (val0 p b)

(** val ginv : g -> g **)

let ginv a =
  inv0 p a

(** val op0 : g -> f -> g **)

let op0 =
  binary_power2

module ElectionGuardG =
 struct
  type coq_G = g

  (** val coq_Gdot : g -> g -> g **)

  let coq_Gdot =
    gdot

  (** val coq_Gone : g **)

  let coq_Gone =
    gone

  (** val coq_Gbool_eq : g -> g -> bool **)

  let coq_Gbool_eq =
    gbool_eq_init

  (** val coq_Ginv : g -> g **)

  let coq_Ginv =
    ginv
 end

module ElectionGuardF =
 struct
  type coq_F = f

  (** val coq_Fadd : f -> f -> f **)

  let coq_Fadd =
    fadd

  (** val coq_Fzero : f **)

  let coq_Fzero =
    fzero

  (** val coq_Fbool_eq : f -> f -> bool **)

  let coq_Fbool_eq =
    fbool_eq_init

  (** val coq_Fsub : f -> f -> f **)

  let coq_Fsub =
    fsub

  (** val coq_Finv : f -> f **)

  let coq_Finv =
    finv

  (** val coq_Fmul : f -> f -> f **)

  let coq_Fmul =
    fmul

  (** val coq_Fone : f **)

  let coq_Fone =
    fone

  (** val coq_FmulInv : f -> f **)

  let coq_FmulInv =
    fmulInv

  (** val coq_Fdiv : f -> f -> f **)

  let coq_Fdiv =
    fdiv
 end

module ElectionGuardVS =
 struct
  (** val op : g -> f -> g **)

  let op =
    op0
 end

module EG = ElectionGuard(ElectionGuardG)(ElectionGuardF)(ElectionGuardVS)
