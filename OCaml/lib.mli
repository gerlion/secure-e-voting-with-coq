
type __ = Obj.t

val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

type comparison =
| Eq
| Lt
| Gt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : Big.big_int -> Big.big_int

  val add : Big.big_int -> Big.big_int -> Big.big_int

  val add_carry : Big.big_int -> Big.big_int -> Big.big_int

  val pred_double : Big.big_int -> Big.big_int

  type mask = Pos.mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : Big.big_int -> mask

  val sub_mask : Big.big_int -> Big.big_int -> mask

  val sub_mask_carry : Big.big_int -> Big.big_int -> mask

  val mul : Big.big_int -> Big.big_int -> Big.big_int

  val compare_cont : comparison -> Big.big_int -> Big.big_int -> comparison

  val compare : Big.big_int -> Big.big_int -> comparison

  val eqb : Big.big_int -> Big.big_int -> bool
 end

module Z :
 sig
  val double : Big.big_int -> Big.big_int

  val succ_double : Big.big_int -> Big.big_int

  val pred_double : Big.big_int -> Big.big_int

  val pos_sub : Big.big_int -> Big.big_int -> Big.big_int

  val add : Big.big_int -> Big.big_int -> Big.big_int

  val opp : Big.big_int -> Big.big_int

  val sub : Big.big_int -> Big.big_int -> Big.big_int

  val mul : Big.big_int -> Big.big_int -> Big.big_int

  val compare : Big.big_int -> Big.big_int -> comparison

  val leb : Big.big_int -> Big.big_int -> bool

  val ltb : Big.big_int -> Big.big_int -> bool

  val eqb : Big.big_int -> Big.big_int -> bool

  val of_N : Big.big_int -> Big.big_int

  val pos_div_eucl : Big.big_int -> Big.big_int -> Big.big_int * Big.big_int

  val div_eucl : Big.big_int -> Big.big_int -> Big.big_int * Big.big_int

  val modulo : Big.big_int -> Big.big_int -> Big.big_int
 end

module Sigma :
 sig
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

  val coq_Rel : 'a1 form -> 'a1 coq_S -> 'a1 coq_W -> bool

  type 'e coq_C = __

  type 'e coq_R = __

  val add : 'a1 form -> 'a1 -> 'a1 -> 'a1

  val zero : 'a1 form -> 'a1

  val inv : 'a1 form -> 'a1 -> 'a1

  val bool_eq : 'a1 form -> 'a1 -> 'a1 -> bool

  val disjoint : 'a1 form -> 'a1 -> 'a1 -> bool

  type 'e coq_T = __

  val coq_P0 :
    'a1 form -> 'a1 coq_S -> 'a1 coq_R -> 'a1 coq_W -> 'a1 coq_S * 'a1 coq_C

  val coq_V0 :
    'a1 form -> ('a1 coq_S * 'a1 coq_C) -> 'a1 -> ('a1 coq_S * 'a1
    coq_C) * 'a1

  val coq_P1 :
    'a1 form -> (('a1 coq_S * 'a1 coq_C) * 'a1) -> 'a1 coq_R -> 'a1 coq_W ->
    (('a1 coq_S * 'a1 coq_C) * 'a1) * 'a1 coq_T

  val coq_V1 :
    'a1 form -> ((('a1 coq_S * 'a1 coq_C) * 'a1) * 'a1 coq_T) -> bool

  val simulator :
    'a1 form -> 'a1 coq_S -> 'a1 coq_T -> 'a1 -> (('a1 coq_S * 'a1
    coq_C) * 'a1) * 'a1 coq_T

  val simMap :
    'a1 form -> 'a1 coq_S -> 'a1 coq_R -> 'a1 -> 'a1 coq_W -> 'a1 coq_T

  val extractor :
    'a1 form -> 'a1 coq_T -> 'a1 coq_T -> 'a1 -> 'a1 -> 'a1 coq_W
 end

val eqSigmaProtocol : 'a1 Sigma.form -> 'a1 Sigma.form

val disSigmaProtocol : 'a1 Sigma.form -> 'a1 Sigma.form

val parSigmaProtocol :
  'a1 Sigma.form -> 'a2 Sigma.form -> ('a1 * 'a2) Sigma.form

val pminusN : Big.big_int -> Big.big_int -> Big.big_int

val is_lt : Big.big_int -> Big.big_int -> bool

val div_eucl0 : Big.big_int -> Big.big_int -> Big.big_int * Big.big_int

val egcd_log2 :
  Big.big_int -> Big.big_int -> Big.big_int ->
  ((Big.big_int * Big.big_int) * Big.big_int) option

val egcd :
  Big.big_int -> Big.big_int -> (Big.big_int * Big.big_int) * Big.big_int

val zegcd :
  Big.big_int -> Big.big_int -> (Big.big_int * Big.big_int) * Big.big_int

type znz = Big.big_int
  (* singleton inductive, whose constructor was mkznz *)

val val0 : Big.big_int -> znz -> Big.big_int

val zero0 : Big.big_int -> znz

val one : Big.big_int -> znz

val add0 : Big.big_int -> znz -> znz -> znz

val mul0 : Big.big_int -> znz -> znz -> znz

val opp0 : Big.big_int -> znz -> znz

val inv0 : Big.big_int -> znz -> znz

val p : Big.big_int

val q : Big.big_int

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

val binary_power_mult2 : fp -> Big.big_int -> fp -> fp

val binary_power2 : fp -> r -> fp

type m = fp

val mdot : m -> m -> m

val mbool_eq : m -> m -> bool

val minv : m -> m

val op : m -> r -> m

val dLog : (m * m) -> r -> bool

val valid_P0 : (m * m) -> r -> r -> (m * m) * m

val valid_V0 : ((m * m) * m) -> r -> ((m * m) * m) * r

val valid_P1 : (((m * m) * m) * r) -> r -> r -> (((m * m) * m) * r) * r

val valid_V1 : ((((m * m) * m) * r) * r) -> bool

val simulator_mapper : (m * m) -> r -> r -> r -> r

val simulator0 : (m * m) -> r -> r -> (((m * m) * m) * r) * r

val extractor0 : r -> r -> r -> r -> r

val disjoint0 : r -> r -> bool

val dLogForm : r Sigma.form

val emptyRel : m -> r -> bool

val empty_P0 : m -> r -> r -> m * m

val empty_V0 : (m * m) -> r -> (m * m) * r

val empty_P1 : ((m * m) * r) -> r -> r -> ((m * m) * r) * r

val empty_V1 : (((m * m) * r) * r) -> bool

val empty_simulator_mapper : m -> r -> r -> r -> r

val empty_simulator : m -> r -> r -> ((m * m) * r) * r

val empty_mapper : r -> r -> r -> r -> r

val emptyForm : r Sigma.form

val dHTForm : r Sigma.form

val dHTDisForm : r Sigma.form

val oneOrZero : r Sigma.coq_S -> r Sigma.coq_S

val oneOrZeroCipher : m -> m -> (m * m) -> r Sigma.coq_S

val decFactorStatment : m -> m -> (m * m) -> m -> r Sigma.coq_S

type recChalType = __

val approvalSigma : (m * m) list -> recChalType Sigma.form

val decryptionSigma : (((r * r) * r) * r) Sigma.form

val approvalSigmaStatment : m -> m -> (m * m) list -> recChalType Sigma.coq_S

val decryptionSigmaStatment :
  m -> (m * m) -> (((m * m) * m) * m) -> (((m * m) * m) * m) ->
  (((r * r) * r) * r) Sigma.coq_S
