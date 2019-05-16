
type __ = Obj.t

type bool =
| True
| False

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

  val of_N : n -> z

  val pos_div_eucl : positive -> z -> (z, z) prod

  val div_eucl : z -> z -> (z, z) prod

  val modulo : z -> z -> z
 end

module Sigma :
 sig
  type coq_S = __
 end

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

val mul0 : z -> znz -> znz -> znz

val inv : z -> znz -> znz

val p : z

type fp = znz

type m = fp

val mdot : m -> m -> m

val minv : m -> m

val oneOrZero : Sigma.coq_S -> Sigma.coq_S

val oneOrZeroCipher : m -> m -> (m, m) prod -> Sigma.coq_S

val statmentFormApproval : m -> m -> (m, m) prod list -> Sigma.coq_S
