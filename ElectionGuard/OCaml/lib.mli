
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

module ModuleAddationalLemmas :
 functor (Group:GroupSig) ->
 functor (Ring:RingSig) ->
 functor (M:sig
  val op : Group.coq_G -> Ring.coq_F -> Group.coq_G
 end) ->
 sig
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

module VectorSpaceAddationalLemmas :
 functor (Group:GroupSig) ->
 functor (Field:FieldSig) ->
 functor (VS:sig
  val op : Group.coq_G -> Field.coq_F -> Group.coq_G
 end) ->
 sig
 end

module DualGroupIns :
 functor (Group:GroupSig) ->
 sig
  type coq_G = Group.coq_G * Group.coq_G

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : Group.coq_G * Group.coq_G

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Ginv : (Group.coq_G * Group.coq_G) -> Group.coq_G * Group.coq_G
 end

module DualVectorSpaceIns :
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
 sig
  val op : DualGroup.coq_G -> Field.coq_F -> Group.coq_G * Group.coq_G
 end

module VectorSpaceModuleSameGroupInsIns :
 functor (Group:GroupSig) ->
 functor (Field:FieldSig) ->
 functor (VS:sig
  val op : Group.coq_G -> Field.coq_F -> Group.coq_G
 end) ->
 sig
  val op3 : Field.coq_F -> Field.coq_F -> Field.coq_F
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

module BasicElGamal :
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
 sig
  module AddVSLemmas :
   sig
   end

  module AddDVSLemmas :
   sig
   end

  type coq_KGR = Group.coq_G * Field.coq_F

  type coq_PK = DualGroup.coq_G

  type coq_SK = Field.coq_F

  type coq_M = Group.coq_G

  val coq_Mop : Group.coq_G -> Group.coq_G -> Group.coq_G

  val coq_Mzero : Group.coq_G

  val coq_Minv : Group.coq_G -> Group.coq_G

  val coq_Mbool_eq : Group.coq_G -> Group.coq_G -> bool

  val keygen : coq_KGR -> coq_PK * coq_SK

  val enc : coq_PK -> Group.coq_G -> Field.coq_F -> DualGroup.coq_G

  val dec : Field.coq_F -> DualGroup.coq_G -> coq_M

  val keymatch : coq_PK -> coq_SK -> bool
 end

module BasicComScheme :
 functor (Group:GroupSig) ->
 functor (Ring:RingSig) ->
 functor (M:sig
  val op : Group.coq_G -> Ring.coq_F -> Group.coq_G
 end) ->
 sig
  module AddMLemmas :
   sig
   end

  val coq_PC :
    Group.coq_G -> Group.coq_G -> Ring.coq_F -> Ring.coq_F -> Group.coq_G
 end

module HardProblems :
 functor (Group:GroupSig) ->
 functor (Ring:RingSig) ->
 functor (M:sig
  val op : Group.coq_G -> Ring.coq_F -> Group.coq_G
 end) ->
 sig
  val dLog : (Group.coq_G * Group.coq_G) -> Ring.coq_F -> bool
 end

module BasicSigmas :
 functor (Group:GroupSig) ->
 functor (Field:FieldSig) ->
 functor (VS:sig
  val op : Group.coq_G -> Field.coq_F -> Group.coq_G
 end) ->
 sig
  module HardProb :
   sig
    val dLog : (Group.coq_G * Group.coq_G) -> Field.coq_F -> bool
   end

  module PC :
   sig
    module AddMLemmas :
     sig
     end

    val coq_PC :
      Group.coq_G -> Group.coq_G -> Field.coq_F -> Field.coq_F -> Group.coq_G
   end

  module AddVSLemmas :
   sig
   end

  val valid_P0 :
    (Group.coq_G * Group.coq_G) -> Field.coq_F -> Field.coq_F ->
    (Group.coq_G * Group.coq_G) * Group.coq_G

  val valid_V0 :
    ((Group.coq_G * Group.coq_G) * Group.coq_G) -> Field.coq_F ->
    ((Group.coq_G * Group.coq_G) * Group.coq_G) * Field.coq_F

  val valid_P1 :
    (((Group.coq_G * Group.coq_G) * Group.coq_G) * Field.coq_F) ->
    Field.coq_F -> Field.coq_F ->
    (((Group.coq_G * Group.coq_G) * Group.coq_G) * Field.coq_F) * Field.coq_F

  val valid_V1 :
    ((((Group.coq_G * Group.coq_G) * Group.coq_G) * Field.coq_F) * Field.coq_F)
    -> bool

  val simulator_mapper :
    (Group.coq_G * Group.coq_G) -> Field.coq_F -> Field.coq_F -> Field.coq_F
    -> Field.coq_F

  val simulator :
    (Group.coq_G * Group.coq_G) -> Field.coq_F -> Field.coq_F ->
    (((Group.coq_G * Group.coq_G) * Group.coq_G) * Field.coq_F) * Field.coq_F

  val extractor :
    Field.coq_F -> Field.coq_F -> Field.coq_F -> Field.coq_F -> Field.coq_F

  val disjoint : Field.coq_F -> Field.coq_F -> bool

  val dLogForm : Field.coq_F Sigma.form

  val emptyRel : Group.coq_G -> Field.coq_F -> bool

  val empty_P0 :
    Group.coq_G -> Field.coq_F -> Field.coq_F -> Group.coq_G * Group.coq_G

  val empty_V0 :
    (Group.coq_G * Group.coq_G) -> Field.coq_F ->
    (Group.coq_G * Group.coq_G) * Field.coq_F

  val empty_P1 :
    ((Group.coq_G * Group.coq_G) * Field.coq_F) -> Field.coq_F -> Field.coq_F
    -> ((Group.coq_G * Group.coq_G) * Field.coq_F) * Field.coq_F

  val empty_V1 :
    (((Group.coq_G * Group.coq_G) * Field.coq_F) * Field.coq_F) -> bool

  val empty_simulator_mapper :
    Group.coq_G -> Field.coq_F -> Field.coq_F -> Field.coq_F -> Field.coq_F

  val empty_simulator :
    Group.coq_G -> Field.coq_F -> Field.coq_F ->
    ((Group.coq_G * Group.coq_G) * Field.coq_F) * Field.coq_F

  val empty_mapper :
    Field.coq_F -> Field.coq_F -> Field.coq_F -> Field.coq_F -> Field.coq_F

  val emptyForm : Field.coq_F Sigma.form

  val dLog2 :
    ((Group.coq_G * Group.coq_G) * Group.coq_G) ->
    (Field.coq_F * Field.coq_F) -> bool

  val dLog2_P0 :
    ((Group.coq_G * Group.coq_G) * Group.coq_G) ->
    (Field.coq_F * Field.coq_F) -> (Field.coq_F * Field.coq_F) ->
    ((Group.coq_G * Group.coq_G) * Group.coq_G) * Group.coq_G

  val dLog2_V0 :
    (((Group.coq_G * Group.coq_G) * Group.coq_G) * Group.coq_G) ->
    Field.coq_F ->
    (((Group.coq_G * Group.coq_G) * Group.coq_G) * Group.coq_G) * Field.coq_F

  val dLog2_P1 :
    ((((Group.coq_G * Group.coq_G) * Group.coq_G) * Group.coq_G) * Field.coq_F)
    -> (Field.coq_F * Field.coq_F) -> (Field.coq_F * Field.coq_F) ->
    ((((Group.coq_G * Group.coq_G) * Group.coq_G) * Group.coq_G) * Field.coq_F) * (Field.coq_F * Field.coq_F)

  val dLog2_V1 :
    (((((Group.coq_G * Group.coq_G) * Group.coq_G) * Group.coq_G) * Field.coq_F) * (Field.coq_F * Field.coq_F))
    -> bool

  val dLog2_simulator_mapper :
    ((Group.coq_G * Group.coq_G) * Group.coq_G) ->
    (Field.coq_F * Field.coq_F) -> Field.coq_F -> (Field.coq_F * Field.coq_F)
    -> Field.coq_F * Field.coq_F

  val dLog2_simulator :
    ((Group.coq_G * Group.coq_G) * Group.coq_G) ->
    (Field.coq_F * Field.coq_F) -> Field.coq_F ->
    ((((Group.coq_G * Group.coq_G) * Group.coq_G) * Group.coq_G) * Field.coq_F) * (Field.coq_F * Field.coq_F)

  val dLog2_extractor :
    (Field.coq_F * Field.coq_F) -> (Field.coq_F * Field.coq_F) -> Field.coq_F
    -> Field.coq_F -> Field.coq_F * Field.coq_F

  val dLog2Form : Field.coq_F Sigma.form
 end

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

val sub0 : Big.big_int -> znz -> znz -> znz

val mul0 : Big.big_int -> znz -> znz -> znz

val opp0 : Big.big_int -> znz -> znz

val inv0 : Big.big_int -> znz -> znz

val div : Big.big_int -> znz -> znz -> znz

val p : Big.big_int

val q : Big.big_int

type fp = znz

val fpMul : fp -> fp -> fp

val fpOne : fp

type f = znz

val fadd : f -> f -> f

val fzero : f

val fbool_eq_init : f -> f -> bool

val fsub : f -> f -> f

val finv : f -> f

val fmul : f -> f -> f

val fone : f

val fmulInv : f -> f

val fdiv : f -> f -> f

val binary_power_mult2 : fp -> Big.big_int -> fp -> fp

val binary_power2 : fp -> f -> fp

type g = fp

val gdot : g -> g -> g

val gone : g

val gbool_eq_init : g -> g -> bool

val ginv : g -> g

val op0 : g -> f -> g

module ElectionGuardG :
 sig
  type coq_G = g

  val coq_Gdot : g -> g -> g

  val coq_Gone : g

  val coq_Gbool_eq : g -> g -> bool

  val coq_Ginv : g -> g
 end

module ElectionGuardF :
 sig
  type coq_F = f

  val coq_Fadd : f -> f -> f

  val coq_Fzero : f

  val coq_Fbool_eq : f -> f -> bool

  val coq_Fsub : f -> f -> f

  val coq_Finv : f -> f

  val coq_Fmul : f -> f -> f

  val coq_Fone : f

  val coq_FmulInv : f -> f

  val coq_Fdiv : f -> f -> f
 end

module ElectionGuardVS :
 sig
  val op : g -> f -> g
 end

module BS :
 sig
  module HardProb :
   sig
    val dLog :
      (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F
      -> bool
   end

  module PC :
   sig
    module AddMLemmas :
     sig
     end

    val coq_PC :
      ElectionGuardG.coq_G -> ElectionGuardG.coq_G -> ElectionGuardF.coq_F ->
      ElectionGuardF.coq_F -> ElectionGuardG.coq_G
   end

  module AddVSLemmas :
   sig
   end

  val valid_P0 :
    (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F ->
    ElectionGuardF.coq_F ->
    (ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G

  val valid_V0 :
    ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) ->
    ElectionGuardF.coq_F ->
    ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F

  val valid_P1 :
    (((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F)
    -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F ->
    (((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * ElectionGuardF.coq_F

  val valid_V1 :
    ((((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * ElectionGuardF.coq_F)
    -> bool

  val simulator_mapper :
    (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F ->
    ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F

  val simulator :
    (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F ->
    ElectionGuardF.coq_F ->
    (((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * ElectionGuardF.coq_F

  val extractor :
    ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F ->
    ElectionGuardF.coq_F -> ElectionGuardF.coq_F

  val disjoint : ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> bool

  val dLogForm : ElectionGuardF.coq_F Sigma.form

  val emptyRel : ElectionGuardG.coq_G -> ElectionGuardF.coq_F -> bool

  val empty_P0 :
    ElectionGuardG.coq_G -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F ->
    ElectionGuardG.coq_G * ElectionGuardG.coq_G

  val empty_V0 :
    (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F ->
    (ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardF.coq_F

  val empty_P1 :
    ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) ->
    ElectionGuardF.coq_F -> ElectionGuardF.coq_F ->
    ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * ElectionGuardF.coq_F

  val empty_V1 :
    (((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * ElectionGuardF.coq_F)
    -> bool

  val empty_simulator_mapper :
    ElectionGuardG.coq_G -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F ->
    ElectionGuardF.coq_F -> ElectionGuardF.coq_F

  val empty_simulator :
    ElectionGuardG.coq_G -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F ->
    ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * ElectionGuardF.coq_F

  val empty_mapper :
    ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F ->
    ElectionGuardF.coq_F -> ElectionGuardF.coq_F

  val emptyForm : ElectionGuardF.coq_F Sigma.form

  val dLog2 :
    ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) ->
    (ElectionGuardF.coq_F * ElectionGuardF.coq_F) -> bool

  val dLog2_P0 :
    ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) ->
    (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
    (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
    ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardG.coq_G

  val dLog2_V0 :
    (((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardG.coq_G)
    -> ElectionGuardF.coq_F ->
    (((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F

  val dLog2_P1 :
    ((((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F)
    -> (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
    (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
    ((((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * (ElectionGuardF.coq_F * ElectionGuardF.coq_F)

  val dLog2_V1 :
    (((((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * (ElectionGuardF.coq_F * ElectionGuardF.coq_F))
    -> bool

  val dLog2_simulator_mapper :
    ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) ->
    (ElectionGuardF.coq_F * ElectionGuardF.coq_F) -> ElectionGuardF.coq_F ->
    (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
    ElectionGuardF.coq_F * ElectionGuardF.coq_F

  val dLog2_simulator :
    ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) ->
    (ElectionGuardF.coq_F * ElectionGuardF.coq_F) -> ElectionGuardF.coq_F ->
    ((((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * (ElectionGuardF.coq_F * ElectionGuardF.coq_F)

  val dLog2_extractor :
    (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
    (ElectionGuardF.coq_F * ElectionGuardF.coq_F) -> ElectionGuardF.coq_F ->
    ElectionGuardF.coq_F -> ElectionGuardF.coq_F * ElectionGuardF.coq_F

  val dLog2Form : ElectionGuardF.coq_F Sigma.form
 end

module DG :
 sig
  type coq_G = ElectionGuardG.coq_G * ElectionGuardG.coq_G

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : ElectionGuardG.coq_G * ElectionGuardG.coq_G

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Ginv :
    (ElectionGuardG.coq_G * ElectionGuardG.coq_G) ->
    ElectionGuardG.coq_G * ElectionGuardG.coq_G
 end

module DVS :
 sig
  val op :
    DG.coq_G -> ElectionGuardF.coq_F ->
    ElectionGuardG.coq_G * ElectionGuardG.coq_G
 end

module MVS :
 sig
  val op3 :
    ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F
 end

module ES :
 sig
  module AddVSLemmas :
   sig
   end

  module AddDVSLemmas :
   sig
   end

  type coq_KGR = ElectionGuardG.coq_G * ElectionGuardF.coq_F

  type coq_PK = DG.coq_G

  type coq_SK = ElectionGuardF.coq_F

  type coq_M = ElectionGuardG.coq_G

  val coq_Mop :
    ElectionGuardG.coq_G -> ElectionGuardG.coq_G -> ElectionGuardG.coq_G

  val coq_Mzero : ElectionGuardG.coq_G

  val coq_Minv : ElectionGuardG.coq_G -> ElectionGuardG.coq_G

  val coq_Mbool_eq : ElectionGuardG.coq_G -> ElectionGuardG.coq_G -> bool

  val keygen : coq_KGR -> coq_PK * coq_SK

  val enc : coq_PK -> ElectionGuardG.coq_G -> ElectionGuardF.coq_F -> DG.coq_G

  val dec : ElectionGuardF.coq_F -> DG.coq_G -> coq_M

  val keymatch : coq_PK -> coq_SK -> bool
 end

val dHTForm : f Sigma.form

val dHTDisForm : f Sigma.form

val oneOrZero : f Sigma.coq_S -> f Sigma.coq_S

val oneOrZeroCipher : ES.coq_PK -> DG.coq_G -> f Sigma.coq_S

val decFactorStatment :
  ES.coq_PK -> DG.coq_G -> ElectionGuardG.coq_G -> f Sigma.coq_S

type recChalType = __

val oneOfNSigma :
  (ElectionGuardG.coq_G * ElectionGuardG.coq_G) list -> recChalType Sigma.form

val decryptionSigma : (((f * f) * f) * f) Sigma.form

val oneOfNStatment :
  ES.coq_PK -> DG.coq_G -> DG.coq_G list -> recChalType Sigma.coq_S

val decryptionSigmaStatment :
  (ElectionGuardG.coq_G * ElectionGuardG.coq_G) ->
  (((ES.coq_PK * ES.coq_PK) * ES.coq_PK) * ES.coq_PK) ->
  (((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardG.coq_G)
  -> (((f * f) * f) * f) Sigma.coq_S
