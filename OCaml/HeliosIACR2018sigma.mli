
type __ = Obj.t

type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

val add : nat -> nat -> nat

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

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val eqb : z -> z -> bool

  val to_nat : z -> nat

  val of_N : n -> z

  val pos_div_eucl : positive -> z -> (z, z) prod

  val div_eucl : z -> z -> (z, z) prod

  val modulo : z -> z -> z
 end

module Sigma :
 sig
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

  val coq_Rel : form -> coq_S -> coq_W -> bool

  type coq_C = __

  type coq_R = __

  type coq_E = __

  val add : form -> coq_E -> coq_E -> coq_E

  val zero : form -> coq_E

  val inv : form -> coq_E -> coq_E

  val bool_eq : form -> coq_E -> coq_E -> bool

  val disjoint : form -> coq_E -> coq_E -> bool

  type coq_T = __

  val coq_P0 : form -> coq_S -> coq_R -> coq_W -> (coq_S, coq_C) prod

  val coq_V0 :
    form -> (coq_S, coq_C) prod -> coq_E -> ((coq_S, coq_C) prod, coq_E) prod

  val coq_P1 :
    form -> ((coq_S, coq_C) prod, coq_E) prod -> coq_R -> coq_W -> (((coq_S,
    coq_C) prod, coq_E) prod, coq_T) prod

  val coq_V1 : form -> (((coq_S, coq_C) prod, coq_E) prod, coq_T) prod -> bool

  val simulator :
    form -> coq_S -> coq_T -> coq_E -> (((coq_S, coq_C) prod, coq_E) prod,
    coq_T) prod

  val simMap : form -> coq_S -> coq_R -> coq_E -> coq_W -> coq_T

  val extractor : form -> coq_T -> coq_T -> coq_E -> coq_E -> coq_W
 end

val eqSigmaProtocol : Sigma.form -> Sigma.form

val disSigmaProtocol : Sigma.form -> Sigma.form

val parSigmaProtocol : Sigma.form -> Sigma.form -> Sigma.form

val pminusN : positive -> positive -> n

val is_lt : positive -> positive -> bool

val div_eucl0 : positive -> positive -> (n, n) prod

val egcd_log2 :
  positive -> positive -> positive -> ((z, z) prod, positive) prod option

val egcd : positive -> positive -> ((z, z) prod, positive) prod

val zegcd : z -> z -> ((z, z) prod, z) prod

type znz = z
  (* singleton inductive, whose constructor was mkznz *)

val val0 : z -> znz -> z

val zero0 : z -> znz

val one : z -> znz

val add0 : z -> znz -> znz -> znz

val mul0 : z -> znz -> znz -> znz

val opp0 : z -> znz -> znz

val inv0 : z -> znz -> znz

val p : z

val q : z

type fp = znz

val fpMul : fp -> fp -> fp

val fpOne : fp

type r = znz

val radd : r -> r -> r

val rzero : r

val rbool_eq : r -> r -> bool

val rinv : r -> r

val rmul : r -> r -> r

val rmulInv : r -> r

val naive_power : fp -> nat -> fp

type m = fp

val mdot : m -> m -> m

val mbool_eq : m -> m -> bool

val minv : m -> m

val op : m -> r -> m

val dLog : (m, m) prod -> r -> bool

val valid_P0 : (m, m) prod -> r -> r -> ((m, m) prod, m) prod

val valid_V0 : ((m, m) prod, m) prod -> r -> (((m, m) prod, m) prod, r) prod

val valid_P1 :
  (((m, m) prod, m) prod, r) prod -> r -> r -> ((((m, m) prod, m) prod, r)
  prod, r) prod

val valid_V1 : ((((m, m) prod, m) prod, r) prod, r) prod -> bool

val simulator_mapper : (m, m) prod -> r -> r -> r -> r

val simulator0 :
  (m, m) prod -> r -> r -> ((((m, m) prod, m) prod, r) prod, r) prod

val extractor0 : r -> r -> r -> r -> r

val disjoint0 : r -> r -> bool

val dLogForm : Sigma.form

val emptyRel : m -> r -> bool

val empty_P0 : m -> r -> r -> (m, m) prod

val empty_V0 : (m, m) prod -> r -> ((m, m) prod, r) prod

val empty_P1 :
  ((m, m) prod, r) prod -> r -> r -> (((m, m) prod, r) prod, r) prod

val empty_V1 : (((m, m) prod, r) prod, r) prod -> bool

val empty_simulator_mapper : m -> r -> r -> r -> r

val empty_simulator : m -> r -> r -> (((m, m) prod, r) prod, r) prod

val empty_mapper : r -> r -> r -> r -> r

val emptyForm : Sigma.form

val dHTForm : Sigma.form

val dHTDisForm : Sigma.form

val overallFormApproval : (m, m) prod list -> Sigma.form
