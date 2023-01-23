
type __ = Obj.t

val negb : bool -> bool

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

val prod_curry_subdef : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

type comparison =
| Eq
| Lt
| Gt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type 'a sig2 = 'a
  (* singleton inductive, whose constructor was exist2 *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2



val pred : nat -> nat

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

val max : nat -> nat -> nat

type reflect =
| ReflectT
| ReflectF

module Nat :
 sig
  val pred : nat -> nat

  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val divmod : nat -> nat -> nat -> nat -> nat * nat

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat
 end

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of Big_int_Z.big_int
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : Big_int_Z.big_int -> Big_int_Z.big_int

  val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val add_carry : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int

  type mask = Pos.mask =
  | IsNul
  | IsPos of Big_int_Z.big_int
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : Big_int_Z.big_int -> mask

  val sub_mask : Big_int_Z.big_int -> Big_int_Z.big_int -> mask

  val sub_mask_carry : Big_int_Z.big_int -> Big_int_Z.big_int -> mask

  val mul : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val compare_cont :
    comparison -> Big_int_Z.big_int -> Big_int_Z.big_int -> comparison

  val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison

  val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool
 end

module Z :
 sig
  val double : Big_int_Z.big_int -> Big_int_Z.big_int

  val succ_double : Big_int_Z.big_int -> Big_int_Z.big_int

  val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int

  val pos_sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val opp : Big_int_Z.big_int -> Big_int_Z.big_int

  val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val mul : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison

  val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val of_N : Big_int_Z.big_int -> Big_int_Z.big_int

  val pos_div_eucl :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int

  val div_eucl :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int

  val modulo : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
 end

type t =
| F1 of nat
| FS of nat * t

val to_nat : nat -> t -> nat

val of_nat_lt : nat -> nat -> t

type 'a t0 =
| Nil
| Cons of 'a * nat * 'a t0

val caseS : ('a1 -> nat -> 'a1 t0 -> 'a2) -> nat -> 'a1 t0 -> 'a2

val hd : nat -> 'a1 t0 -> 'a1

val const : 'a1 -> nat -> 'a1 t0

val tl : nat -> 'a1 t0 -> 'a1 t0

val locked_with : unit -> 'a1 -> 'a1

val ssr_have : 'a1 -> ('a1 -> 'a2) -> 'a2

module Option :
 sig
  val apply : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

  val default : 'a1 -> 'a1 option -> 'a1

  val bind : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option

  val map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option
 end

type ('aT, 'rT) simpl_fun =
  'aT -> 'rT
  (* singleton inductive, whose constructor was SimplFun *)

val fun_of_simpl : ('a1, 'a2) simpl_fun -> 'a1 -> 'a2

val comp : ('a2 -> 'a1) -> ('a3 -> 'a2) -> 'a3 -> 'a1

val pcomp : ('a2 -> 'a1 option) -> ('a3 -> 'a2 option) -> 'a3 -> 'a1 option

val tag : ('a1, 'a2) sigT -> 'a1

val tagged : ('a1, 'a2) sigT -> 'a2

val tagged0 : 'a1 -> 'a2 -> ('a1, 'a2) sigT

val addb : bool -> bool -> bool

val isSome : 'a1 option -> bool

val introP : bool -> reflect

val iffP : bool -> reflect -> reflect

val idP : bool -> reflect

val andP : bool -> bool -> reflect

type 't pred0 = 't -> bool

type 't predType =
  __ -> 't pred0
  (* singleton inductive, whose constructor was PredType *)

type 't pred_sort = __

val predPredType : 'a1 predType

type 't simpl_pred = ('t, bool) simpl_fun

val simplPred : 'a1 pred0 -> 'a1 simpl_pred

val predT : 'a1 simpl_pred

val predD : 'a1 pred0 -> 'a1 pred0 -> 'a1 simpl_pred

module PredOfSimpl :
 sig
  val coerce : 'a1 simpl_pred -> 'a1 pred0
 end

val simplPredType : 'a1 predType

val pred_of_argType : 'a1 simpl_pred

type 't rel = 't -> 't pred0

type 't mem_pred = 't pred0
  (* singleton inductive, whose constructor was Mem *)

val pred_of_mem : 'a1 mem_pred -> 'a1 pred_sort

val in_mem : 'a1 -> 'a1 mem_pred -> bool

val simpl_of_mem : 'a1 mem_pred -> 'a1 simpl_pred

val mem : 'a1 predType -> 'a1 pred_sort -> 'a1 mem_pred

type 't qualifier =
  't pred_sort
  (* singleton inductive, whose constructor was Qualifier *)

val has_quality : nat -> 'a1 qualifier -> 'a1 pred_sort

module type GroupSig =
 sig
  type coq_G

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : coq_G

  val coq_Ggen : coq_G

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Gdisjoint : coq_G -> coq_G -> bool

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

module RingAddationalLemmas :
 functor (Ring:RingSig) ->
 sig
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

module FieldAddationalLemmas :
 functor (Field:FieldSig) ->
 sig
  module AL :
   sig
   end
 end

module VectorSpaceAddationalLemmas :
 functor (Group:GroupSig) ->
 functor (Field:FieldSig) ->
 functor (VS:sig
  val op : Group.coq_G -> Field.coq_F -> Group.coq_G
 end) ->
 sig
  module AL :
   sig
   end
 end

module DualGroupIns :
 functor (Group:GroupSig) ->
 sig
  type coq_G = Group.coq_G * Group.coq_G

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : Group.coq_G * Group.coq_G

  val coq_Ggen : Group.coq_G * Group.coq_G

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Gdisjoint : coq_G -> coq_G -> bool

  val coq_Ginv : (Group.coq_G * Group.coq_G) -> Group.coq_G * Group.coq_G
 end

module DualVectorSpaceIns :
 functor (Group:GroupSig) ->
 functor (DualGroup:sig
  type coq_G = Group.coq_G * Group.coq_G

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : Group.coq_G * Group.coq_G

  val coq_Ggen : Group.coq_G * Group.coq_G

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Gdisjoint : coq_G -> coq_G -> bool

  val coq_Ginv : (Group.coq_G * Group.coq_G) -> Group.coq_G * Group.coq_G
 end) ->
 functor (Field:FieldSig) ->
 functor (VS:sig
  val op : Group.coq_G -> Field.coq_F -> Group.coq_G
 end) ->
 sig
  val op : DualGroup.coq_G -> Field.coq_F -> Group.coq_G * Group.coq_G
 end

type 'a rel_dec = 'a -> 'a -> bool

val dec_beq : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool

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

module Eqset_def :
 functor (A:SetA) ->
 sig
  type coq_A = A.coq_A
 end

val vcast : nat -> 'a1 t0 -> nat -> 'a1 t0

val vnth : nat -> 'a1 t0 -> nat -> 'a1

val vadd : nat -> 'a1 t0 -> 'a1 -> 'a1 t0

val vreplace : nat -> 'a1 t0 -> nat -> 'a1 -> 'a1 t0

val vapp : nat -> nat -> 'a1 t0 -> 'a1 t0 -> 'a1 t0

val vbreak : nat -> nat -> 'a1 t0 -> 'a1 t0 * 'a1 t0

val vsub : nat -> 'a1 t0 -> nat -> nat -> 'a1 t0

val vremove_last : nat -> 'a1 t0 -> 'a1 t0

val vlast : 'a1 -> nat -> 'a1 t0 -> 'a1

val vmap : ('a1 -> 'a2) -> nat -> 'a1 t0 -> 'a2 t0

val bVforall : ('a1 -> bool) -> nat -> 'a1 t0 -> bool

val vforall2_aux_dec : ('a1 -> 'a2 -> bool) -> nat -> 'a1 t0 -> nat -> 'a2 t0 -> bool

val vforall2_dec : ('a1 -> 'a2 -> bool) -> nat -> 'a1 t0 -> 'a2 t0 -> bool

val bVforall2_aux : ('a1 -> 'a2 -> bool) -> nat -> nat -> 'a1 t0 -> 'a2 t0 -> bool

val bVforall2 : ('a1 -> 'a2 -> bool) -> nat -> 'a1 t0 -> 'a2 t0 -> bool

val bVexists : ('a1 -> bool) -> nat -> 'a1 t0 -> bool

val vbuild : nat -> (nat -> __ -> 'a1) -> 'a1 t0

val vfold_left : ('a1 -> 'a2 -> 'a1) -> nat -> 'a1 -> 'a2 t0 -> 'a1

val vfold_left_rev : ('a1 -> 'a2 -> 'a1) -> nat -> 'a1 -> 'a2 t0 -> 'a1

val vmap2 : ('a1 -> 'a2 -> 'a3) -> nat -> 'a1 t0 -> 'a2 t0 -> 'a3 t0

module type SemiRingType =
 sig
  module ES :
   Eqset_dec

  val coq_A0 : ES.Eq.coq_A

  val coq_A1 : ES.Eq.coq_A

  val coq_Aplus : ES.Eq.coq_A -> ES.Eq.coq_A -> ES.Eq.coq_A

  val coq_Amult : ES.Eq.coq_A -> ES.Eq.coq_A -> ES.Eq.coq_A
 end

module SemiRing :
 functor (SR:SemiRingType) ->
 sig
 end

module VectorArith :
 functor (SRT:SemiRingType) ->
 sig
  module SR :
   sig
   end

  val zero_vec : nat -> SRT.ES.Eq.coq_A t0

  val id_vec : nat -> nat -> SRT.ES.Eq.coq_A t0

  val vector_plus :
    nat -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A t0

  val add_vectors : nat -> nat -> SRT.ES.Eq.coq_A t0 t0 -> SRT.ES.Eq.coq_A t0

  val dot_product :
    nat -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A
 end

module Matrix :
 functor (SRT:SemiRingType) ->
 sig
  module SR :
   sig
   end

  module VA :
   sig
    module SR :
     sig
     end

    val zero_vec : nat -> SRT.ES.Eq.coq_A t0

    val id_vec : nat -> nat -> SRT.ES.Eq.coq_A t0

    val vector_plus :
      nat -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A t0

    val add_vectors : nat -> nat -> SRT.ES.Eq.coq_A t0 t0 -> SRT.ES.Eq.coq_A t0

    val dot_product :
      nat -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A
   end

  type matrix = SRT.ES.Eq.coq_A t0 t0

  val get_row : nat -> nat -> matrix -> nat -> SRT.ES.Eq.coq_A t0

  val get_col : nat -> nat -> matrix -> nat -> SRT.ES.Eq.coq_A t0

  val get_elem : nat -> nat -> matrix -> nat -> nat -> SRT.ES.Eq.coq_A

  val mat_build_spec :
    nat -> nat -> (nat -> nat -> __ -> __ -> SRT.ES.Eq.coq_A) -> matrix

  val mat_build : nat -> nat -> (nat -> nat -> __ -> __ -> SRT.ES.Eq.coq_A) -> matrix

  val zero_matrix : nat -> nat -> matrix

  val id_matrix : nat -> matrix

  val inverse_matrix :
    (SRT.ES.Eq.coq_A -> SRT.ES.Eq.coq_A) -> nat -> nat -> matrix -> matrix

  type row_mat = matrix

  type col_mat = matrix

  val vec_to_row_mat : nat -> SRT.ES.Eq.coq_A t0 -> row_mat

  val vec_to_col_mat : nat -> SRT.ES.Eq.coq_A t0 -> col_mat

  val row_mat_to_vec : nat -> row_mat -> SRT.ES.Eq.coq_A t0

  val col_mat_to_vec : nat -> col_mat -> SRT.ES.Eq.coq_A t0

  val mat_transpose : nat -> nat -> matrix -> matrix

  val vec_plus :
    nat -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A t0

  val mat_plus : nat -> nat -> matrix -> matrix -> SRT.ES.Eq.coq_A t0 t0

  val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

  val mat_vec_prod : nat -> nat -> matrix -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A t0

  val mat_forall2'_dec : nat -> nat -> SRT.ES.Eq.coq_A rel_dec -> matrix rel_dec

  val mat_forall2_dec : nat -> nat -> SRT.ES.Eq.coq_A rel_dec -> matrix rel_dec
 end

val vlastS : nat -> 'a1 t0 -> 'a1

val rev : nat -> 'a1 t0 -> 'a1 t0

val zip : nat -> 'a1 t0 -> 'a2 t0 -> ('a1 * 'a2) t0

val unzipLeft : nat -> ('a1 * 'a2) t0 -> 'a1 t0

val unzipRight : nat -> ('a1 * 'a2) t0 -> 'a2 t0

val pairwisePredicate : nat -> ('a1 -> 'a1 -> bool) -> 'a1 t0 -> bool

val bVforall3 :
  nat -> ('a1 -> 'a2 -> 'a3 -> bool) -> 'a1 t0 -> 'a2 t0 -> 'a3 t0 -> bool

type index = nat

val makeIndex : nat -> nat -> index

val makeIndexSucc : nat -> index -> index

val vremove : nat -> 'a1 t0 -> nat -> 'a1 t0

val vecToMat : nat -> nat -> 'a1 t0 -> 'a1 t0 t0

val matToVec : nat -> nat -> 'a1 t0 t0 -> 'a1 t0

module MatricesFIns :
 functor (Ring:RingSig) ->
 sig
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

      val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

      val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val vector_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val add_vectors :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

      val dot_product :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A
     end

    type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

    val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

    val mat_build_spec :
      nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

    val mat_build :
      nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

    val zero_matrix : nat -> nat -> matrix

    val id_matrix : nat -> matrix

    val inverse_matrix :
      (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix ->
      matrix

    type row_mat = matrix

    type col_mat = matrix

    val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

    val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

    val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

    val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

    val mat_transpose : nat -> nat -> matrix -> matrix

    val vec_plus :
      nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
      FSemiRingT.ES.Eq.coq_A t0

    val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

    val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

    val mat_vec_prod :
      nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0

    val mat_forall2'_dec :
      nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

    val mat_forall2_dec :
      nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
   end

  module ALR :
   sig
   end

  type coq_VF = Ring.coq_F t0

  val coq_VF_zero : nat -> Ring.coq_F t0

  val coq_VF_one : nat -> Ring.coq_F t0

  val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

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

  val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

  val coq_MF_perm_last : nat -> coq_MF -> index

  val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

  val matRecover_sub : nat -> Ring.coq_F -> nat

  val matRecover : nat -> coq_VF -> coq_MF
 end

module MatricesG :
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

      val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

      val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val vector_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val add_vectors :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

      val dot_product :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A
     end

    type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

    val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

    val mat_build_spec :
      nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

    val mat_build :
      nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

    val zero_matrix : nat -> nat -> matrix

    val id_matrix : nat -> matrix

    val inverse_matrix :
      (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix ->
      matrix

    type row_mat = matrix

    type col_mat = matrix

    val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

    val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

    val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

    val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

    val mat_transpose : nat -> nat -> matrix -> matrix

    val vec_plus :
      nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
      FSemiRingT.ES.Eq.coq_A t0

    val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

    val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

    val mat_vec_prod :
      nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0

    val mat_forall2'_dec :
      nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

    val mat_forall2_dec :
      nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
   end

  module ALR :
   sig
   end

  type coq_VF = Ring.coq_F t0

  val coq_VF_zero : nat -> Ring.coq_F t0

  val coq_VF_one : nat -> Ring.coq_F t0

  val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

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

  val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

  val coq_MF_perm_last : nat -> coq_MF -> index

  val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

  val matRecover_sub : nat -> Ring.coq_F -> nat

  val matRecover : nat -> coq_VF -> coq_MF
 end) ->
 sig
  module AddMLemmas :
   sig
   end

  type coq_VG = Group.coq_G t0

  val coq_VG_id : nat -> Group.coq_G t0

  val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

  val coq_VG_inv : nat -> coq_VG -> coq_VG

  val coq_VG_prod : nat -> coq_VG -> Group.coq_G

  val coq_VG_Pexp : nat -> coq_VG -> MatF.coq_VF -> coq_VG

  val coq_VG_Sexp : nat -> coq_VG -> Ring.coq_F -> coq_VG

  val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

  val coq_VG_MF_exp_coll : nat -> coq_VG -> MatF.coq_MF -> coq_VG

  val coq_VG_MF_exp_row : nat -> coq_VG -> MatF.coq_MF -> coq_VG

  val coq_PexpMatrix : nat -> coq_VG -> MatF.coq_MF -> coq_VG

  val coq_VG_scale_sum : nat -> nat -> nat -> MatF.coq_VF t0 t0 -> MatF.coq_VF t0
 end

val predType0 : ('a2 -> 'a1 pred0) -> 'a1 predType

module Equality :
 sig
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  val op : 'a1 mixin_of -> 'a1 rel

  type coq_type = __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort mixin_of
 end

val eq_op : Equality.coq_type -> Equality.sort rel

val eqP : Equality.coq_type -> Equality.sort Equality.axiom

val eqb0 : bool -> bool -> bool

val eqbP : bool Equality.axiom

val bool_eqMixin : bool Equality.mixin_of

val bool_eqType : Equality.coq_type

val pred1 : Equality.coq_type -> Equality.sort -> Equality.sort simpl_pred

type 't subType = { val0 : (__ -> 't); sub0 : ('t -> __ -> __);
                    subType__2 : (__ -> ('t -> __ -> __) -> __ -> __) }

type 't sub_sort = __

val sub0 : 'a1 pred0 -> 'a1 subType -> 'a1 -> 'a1 sub_sort

val insub : 'a1 pred0 -> 'a1 subType -> 'a1 -> 'a1 sub_sort option

val insubd : 'a1 pred0 -> 'a1 subType -> 'a1 sub_sort -> 'a1 -> 'a1 sub_sort

val s2val : 'a1 sig2 -> 'a1

val inj_eqAxiom : Equality.coq_type -> ('a1 -> Equality.sort) -> 'a1 Equality.axiom

val injEqMixin : Equality.coq_type -> ('a1 -> Equality.sort) -> 'a1 Equality.mixin_of

val pcanEqMixin :
  Equality.coq_type -> ('a1 -> Equality.sort) -> (Equality.sort -> 'a1 option) ->
  'a1 Equality.mixin_of

val val_eqP :
  Equality.coq_type -> Equality.sort pred0 -> Equality.sort subType -> Equality.sort
  sub_sort Equality.axiom

val sub_eqMixin :
  Equality.coq_type -> Equality.sort pred0 -> Equality.sort subType -> Equality.sort
  sub_sort Equality.mixin_of

val pair_eq :
  Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort) rel

val pair_eqP :
  Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
  Equality.axiom

val prod_eqMixin :
  Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
  Equality.mixin_of

val prod_eqType : Equality.coq_type -> Equality.coq_type -> Equality.coq_type

val tagged_as :
  Equality.coq_type -> (Equality.sort, 'a1) sigT -> (Equality.sort, 'a1) sigT -> 'a1

val tag_eq :
  Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> (Equality.sort,
  Equality.sort) sigT -> (Equality.sort, Equality.sort) sigT -> bool

val tag_eqP :
  Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> (Equality.sort,
  Equality.sort) sigT Equality.axiom

val tag_eqMixin :
  Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> (Equality.sort,
  Equality.sort) sigT Equality.mixin_of

val tag_eqType :
  Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> Equality.coq_type

val eqn : nat -> nat -> bool

val eqnP : nat Equality.axiom

val nat_eqMixin : nat Equality.mixin_of

val nat_eqType : Equality.coq_type

val addn_rec : nat -> nat -> nat

val addn : nat -> nat -> nat

val subn_rec : nat -> nat -> nat

val subn : nat -> nat -> nat

val leq : nat -> nat -> bool

val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

val iteri : nat -> (nat -> 'a1 -> 'a1) -> 'a1 -> 'a1

val iterop : nat -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

val muln_rec : nat -> nat -> nat

val muln : nat -> nat -> nat

val expn_rec : nat -> nat -> nat

val expn : nat -> nat -> nat

val nat_of_bool : bool -> nat

val odd : nat -> bool

val double_rec : nat -> nat

val double0 : nat -> nat

val size : 'a1 list -> nat

val cat : 'a1 list -> 'a1 list -> 'a1 list

val nth : 'a1 -> 'a1 list -> nat -> 'a1

val find : 'a1 pred0 -> 'a1 list -> nat

val filter : 'a1 pred0 -> 'a1 list -> 'a1 list

val eqseq : Equality.coq_type -> Equality.sort list -> Equality.sort list -> bool

val eqseqP : Equality.coq_type -> Equality.sort list Equality.axiom

val seq_eqMixin : Equality.coq_type -> Equality.sort list Equality.mixin_of

val seq_eqType : Equality.coq_type -> Equality.coq_type

val mem_seq : Equality.coq_type -> Equality.sort list -> Equality.sort -> bool

type seq_eqclass = Equality.sort list

val pred_of_seq : Equality.coq_type -> seq_eqclass -> Equality.sort pred_sort

val seq_predType : Equality.coq_type -> Equality.sort predType

val uniq : Equality.coq_type -> Equality.sort list -> bool

val undup : Equality.coq_type -> Equality.sort list -> Equality.sort list

val index0 : Equality.coq_type -> Equality.sort -> Equality.sort list -> nat

val map0 : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val pmap : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list

val iota : nat -> nat -> nat list

val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val flatten : 'a1 list list -> 'a1 list

module CodeSeq :
 sig
  val code : nat list -> nat

  val decode_rec : nat -> nat -> nat -> nat list

  val decode : nat -> nat list
 end

val tag_of_pair : ('a1 * 'a2) -> ('a1, 'a2) sigT

val pair_of_tag : ('a1, 'a2) sigT -> 'a1 * 'a2

module Choice :
 sig
  type 't mixin_of =
    't pred0 -> nat -> 't option
    (* singleton inductive, whose constructor was Mixin *)

  val find : 'a1 mixin_of -> 'a1 pred0 -> nat -> 'a1 option

  type 't class_of = { base : 't Equality.mixin_of; mixin : 't mixin_of }

  val base : 'a1 class_of -> 'a1 Equality.mixin_of

  val mixin : 'a1 class_of -> 'a1 mixin_of

  type coq_type = __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort class_of

  val pack : 'a1 mixin_of -> 'a1 Equality.mixin_of -> Equality.coq_type -> coq_type

  val eqType : coq_type -> Equality.coq_type

  module InternalTheory :
   sig
    val find : coq_type -> sort pred0 -> nat -> sort option
   end
 end

val pcanChoiceMixin :
  Choice.coq_type -> ('a1 -> Choice.sort) -> (Choice.sort -> 'a1 option) -> 'a1
  Choice.mixin_of

val canChoiceMixin :
  Choice.coq_type -> ('a1 -> Choice.sort) -> (Choice.sort -> 'a1) -> 'a1
  Choice.mixin_of

val sub_choiceMixin :
  Choice.coq_type -> Choice.sort pred0 -> Choice.sort subType -> Choice.sort
  sub_sort Choice.mixin_of

val sub_choiceClass :
  Choice.coq_type -> Choice.sort pred0 -> Choice.sort subType -> Choice.sort
  sub_sort Choice.class_of

val sub_choiceType :
  Choice.coq_type -> Choice.sort pred0 -> Choice.sort subType -> Choice.coq_type

val seq_choiceMixin : Choice.coq_type -> Choice.sort list Choice.mixin_of

val seq_choiceType : Choice.coq_type -> Choice.coq_type

val tagged_choiceMixin :
  Choice.coq_type -> (Choice.sort -> Choice.coq_type) -> (Choice.sort, Choice.sort)
  sigT Choice.mixin_of

val tagged_choiceType :
  Choice.coq_type -> (Choice.sort -> Choice.coq_type) -> Choice.coq_type

val nat_choiceMixin : nat Choice.mixin_of

val nat_choiceType : Choice.coq_type

val bool_choiceMixin : bool Choice.mixin_of

val bool_choiceType : Choice.coq_type

val prod_choiceMixin :
  Choice.coq_type -> Choice.coq_type -> (Choice.sort * Choice.sort) Choice.mixin_of

val prod_choiceType : Choice.coq_type -> Choice.coq_type -> Choice.coq_type

module Countable :
 sig
  type 't mixin_of = { pickle : ('t -> nat); unpickle : (nat -> 't option) }

  val pickle : 'a1 mixin_of -> 'a1 -> nat

  val unpickle : 'a1 mixin_of -> nat -> 'a1 option

  type 't class_of = { base : 't Choice.class_of; mixin : 't mixin_of }

  val base : 'a1 class_of -> 'a1 Choice.class_of

  val mixin : 'a1 class_of -> 'a1 mixin_of

  type coq_type = __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort class_of

  val pack : 'a1 mixin_of -> Choice.coq_type -> 'a1 Choice.class_of -> coq_type

  val eqType : coq_type -> Equality.coq_type

  val choiceType : coq_type -> Choice.coq_type
 end

val unpickle0 : Countable.coq_type -> nat -> Countable.sort option

val pickle0 : Countable.coq_type -> Countable.sort -> nat

val pcanCountMixin :
  Countable.coq_type -> ('a1 -> Countable.sort) -> (Countable.sort -> 'a1 option) ->
  'a1 Countable.mixin_of

val canCountMixin :
  Countable.coq_type -> ('a1 -> Countable.sort) -> (Countable.sort -> 'a1) -> 'a1
  Countable.mixin_of

val sub_countMixin :
  Countable.coq_type -> Countable.sort pred0 -> Countable.sort subType ->
  Countable.sort sub_sort Countable.mixin_of

val pickle_seq : Countable.coq_type -> Countable.sort list -> nat

val unpickle_seq : Countable.coq_type -> nat -> Countable.sort list option

val seq_countMixin : Countable.coq_type -> Countable.sort list Countable.mixin_of

val seq_countType : Countable.coq_type -> Countable.coq_type

type subCountType = { subCount_sort : Choice.sort subType;
                      subCountType__1 : Choice.sort sub_sort Countable.mixin_of }

val sub_countType :
  Choice.coq_type -> Choice.sort pred0 -> subCountType -> Countable.coq_type

val pickle_tagged :
  Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> (Countable.sort,
  Countable.sort) sigT -> nat

val unpickle_tagged :
  Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> nat ->
  (Countable.sort, Countable.sort) sigT option

val tag_countMixin :
  Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> (Countable.sort,
  Countable.sort) sigT Countable.mixin_of

val tag_countType :
  Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> Countable.coq_type

val nat_countMixin : nat Countable.mixin_of

val nat_countType : Countable.coq_type

val bool_countMixin : bool Countable.mixin_of

val bool_countType : Countable.coq_type

val prod_countMixin :
  Countable.coq_type -> Countable.coq_type -> (Countable.sort * Countable.sort)
  Countable.mixin_of

module Finite :
 sig
  type mixin_of = { mixin_base : Equality.sort Countable.mixin_of;
                    mixin_enum : Equality.sort list }

  val mixin_base : Equality.coq_type -> mixin_of -> Equality.sort Countable.mixin_of

  val mixin_enum : Equality.coq_type -> mixin_of -> Equality.sort list

  val coq_EnumMixin : Countable.coq_type -> Countable.sort list -> mixin_of

  val coq_UniqMixin : Countable.coq_type -> Countable.sort list -> mixin_of

  type 't class_of = { base : 't Choice.class_of; mixin : mixin_of }

  val base : 'a1 class_of -> 'a1 Choice.class_of

  val mixin : 'a1 class_of -> mixin_of

  val base2 : 'a1 class_of -> 'a1 Countable.class_of

  type coq_type = __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort class_of

  val pack :
    'a1 Equality.mixin_of -> mixin_of -> Choice.coq_type -> 'a1 Choice.class_of ->
    mixin_of -> coq_type

  val eqType : coq_type -> Equality.coq_type

  val choiceType : coq_type -> Choice.coq_type

  val countType : coq_type -> Countable.coq_type

  module type EnumSig =
   sig
    val enum : coq_type -> sort list
   end

  module EnumDef :
   EnumSig
 end

type fin_pred_sort = Finite.sort pred_sort

val enum_mem : Finite.coq_type -> Finite.sort mem_pred -> Finite.sort list

module type CardDefSig =
 sig
  val card : Finite.coq_type -> Finite.sort mem_pred -> nat
 end

module CardDef :
 CardDefSig

val pred0b : Finite.coq_type -> Finite.sort pred0 -> bool

module FiniteQuant :
 sig
  type quantified = bool
    (* singleton inductive, whose constructor was Quantified *)

  val all : Finite.coq_type -> quantified -> Finite.sort -> Finite.sort -> quantified
 end

module type SubsetDefSig =
 sig
  val subset :
    Finite.coq_type -> Finite.sort mem_pred -> Finite.sort mem_pred -> bool
 end

module SubsetDef :
 SubsetDefSig

type pick_spec =
| Pick of Finite.sort
| Nopick

val pickP : Finite.coq_type -> Finite.sort pred0 -> pick_spec

val pred0P : Finite.coq_type -> Finite.sort pred0 -> reflect

val forallPP :
  Finite.coq_type -> Finite.sort pred0 -> (Finite.sort -> reflect) -> reflect

val eqfunP :
  Finite.coq_type -> (Finite.sort -> Equality.coq_type) -> (Finite.sort ->
  Equality.sort) -> (Finite.sort -> Equality.sort) -> reflect

val dinjectiveb :
  Finite.coq_type -> Equality.coq_type -> (Finite.sort -> Equality.sort) ->
  Finite.sort pred_sort -> bool

val injectiveb :
  Finite.coq_type -> Equality.coq_type -> (Finite.sort -> Equality.sort) -> bool

val image_mem :
  Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort mem_pred -> 'a1 list

val codom : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 list

val iinv_proof :
  Finite.coq_type -> Equality.coq_type -> (Finite.sort -> Equality.sort) ->
  Finite.sort pred_sort -> Equality.sort -> Finite.sort sig2

val iinv :
  Finite.coq_type -> Equality.coq_type -> (Finite.sort -> Equality.sort) ->
  Finite.sort pred_sort -> Equality.sort -> Finite.sort

val bool_finMixin : Finite.mixin_of

val bool_finType : Finite.coq_type

val pcanFinMixin :
  Countable.coq_type -> Finite.coq_type -> (Countable.sort -> Finite.sort) ->
  (Finite.sort -> Countable.sort option) -> Finite.mixin_of

val sub_enum :
  Finite.coq_type -> Finite.sort pred0 -> subCountType -> Choice.sort sub_sort list

val subFinMixin :
  Finite.coq_type -> Finite.sort pred0 -> subCountType -> Finite.mixin_of

val subFinMixin_for :
  Finite.coq_type -> Finite.sort pred0 -> subCountType -> Equality.coq_type ->
  Finite.mixin_of

type ordinal = nat
  (* singleton inductive, whose constructor was Ordinal *)

val nat_of_ord : nat -> ordinal -> nat

val ordinal_subType : nat -> nat subType

val ordinal_eqMixin : nat -> ordinal Equality.mixin_of

val ordinal_eqType : nat -> Equality.coq_type

val ordinal_choiceMixin : nat -> ordinal Choice.mixin_of

val ordinal_choiceType : nat -> Choice.coq_type

val ordinal_countMixin : nat -> ordinal Countable.mixin_of

val ord_enum : nat -> ordinal list

val ordinal_finMixin : nat -> Finite.mixin_of

val ordinal_finType : nat -> Finite.coq_type

val enum_rank_in :
  Finite.coq_type -> Finite.sort -> Finite.sort pred_sort -> Equality.sort -> nat
  sub_sort

val enum_rank : Finite.coq_type -> Finite.sort -> nat sub_sort

val bump : nat -> nat -> nat

val lift : nat -> ordinal -> ordinal -> ordinal

val prod_enum :
  Finite.coq_type -> Finite.coq_type -> (Finite.sort * Finite.sort) list

val prod_finMixin : Finite.coq_type -> Finite.coq_type -> Finite.mixin_of

val prod_finType : Finite.coq_type -> Finite.coq_type -> Finite.coq_type

val tag_enum :
  Finite.coq_type -> (Finite.sort -> Finite.coq_type) -> (Finite.sort, Finite.sort)
  sigT list

val tag_finMixin :
  Finite.coq_type -> (Finite.sort -> Finite.coq_type) -> Finite.mixin_of

val tag_finType :
  Finite.coq_type -> (Finite.sort -> Finite.coq_type) -> Finite.coq_type

type 't tuple_of = 't list
  (* singleton inductive, whose constructor was Tuple *)

val tval : nat -> 'a1 tuple_of -> 'a1 list

val tuple_subType : nat -> 'a1 list subType

val tnth_default : nat -> 'a1 tuple_of -> ordinal -> 'a1

val tnth : nat -> 'a1 tuple_of -> ordinal -> 'a1

val tuple : nat -> 'a1 tuple_of -> (__ -> 'a1 tuple_of) -> 'a1 tuple_of

val map_tuple : nat -> ('a1 -> 'a2) -> 'a1 tuple_of -> 'a2 tuple_of

val tuple_eqMixin :
  nat -> Equality.coq_type -> Equality.sort tuple_of Equality.mixin_of

val tuple_eqType : nat -> Equality.coq_type -> Equality.coq_type

val tuple_choiceMixin :
  nat -> Choice.coq_type -> Choice.sort tuple_of Choice.mixin_of

val tuple_choiceType : nat -> Choice.coq_type -> Choice.coq_type

val tuple_countMixin :
  nat -> Countable.coq_type -> Countable.sort tuple_of Countable.mixin_of

val tuple_countType : nat -> Countable.coq_type -> Countable.coq_type

module type FinTupleSig =
 sig
  val enum : nat -> Finite.coq_type -> Finite.sort tuple_of list
 end

module FinTuple :
 FinTupleSig

val tuple_finMixin : nat -> Finite.coq_type -> Finite.mixin_of

val tuple_finType : nat -> Finite.coq_type -> Finite.coq_type

val enum_tuple : Finite.coq_type -> Finite.sort pred_sort -> Finite.sort tuple_of

val codom_tuple : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 tuple_of

type 'rT finfun_on =
| Finfun_nil
| Finfun_cons of Finite.sort * Finite.sort list * 'rT * 'rT finfun_on

val finfun_rec :
  Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort list -> 'a1 finfun_on

val fun_of_fin_rec :
  Finite.coq_type -> Equality.sort -> Finite.sort list -> 'a1 finfun_on -> 'a1

type 'rT finfun_of =
  'rT finfun_on
  (* singleton inductive, whose constructor was FinfunOf *)

type 'rT dfinfun_of = 'rT finfun_of

val fun_of_fin : Finite.coq_type -> 'a1 finfun_of -> Equality.sort -> 'a1

module type FinfunDefSig =
 sig
  val finfun : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 finfun_of
 end

module FinfunDef :
 FinfunDefSig

val total_fun :
  Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort -> (Finite.sort, 'a1) sigT

val tfgraph : Finite.coq_type -> 'a1 finfun_of -> (Finite.sort, 'a1) sigT tuple_of

val tfgraph_inv :
  Finite.coq_type -> (Finite.sort, 'a1) sigT tuple_of -> 'a1 finfun_of option

val eqMixin :
  Finite.coq_type -> (Finite.sort -> Equality.coq_type) -> Equality.sort dfinfun_of
  Equality.mixin_of

val finfun_eqType : Finite.coq_type -> Equality.coq_type -> Equality.coq_type

val dfinfun_eqType :
  Finite.coq_type -> (Finite.sort -> Equality.coq_type) -> Equality.coq_type

val choiceMixin :
  Finite.coq_type -> (Finite.sort -> Choice.coq_type) -> Choice.sort dfinfun_of
  Choice.mixin_of

val finfun_choiceType : Finite.coq_type -> Choice.coq_type -> Choice.coq_type

val dfinfun_choiceType :
  Finite.coq_type -> (Finite.sort -> Choice.coq_type) -> Choice.coq_type

val countMixin :
  Finite.coq_type -> (Finite.sort -> Countable.coq_type) -> Countable.sort
  dfinfun_of Countable.mixin_of

val finfun_countType : Finite.coq_type -> Countable.coq_type -> Countable.coq_type

val dfinfun_countType :
  Finite.coq_type -> (Finite.sort -> Countable.coq_type) -> Countable.coq_type

val finMixin : Finite.coq_type -> (Finite.sort -> Finite.coq_type) -> Finite.mixin_of

val finfun_finType : Finite.coq_type -> Finite.coq_type -> Finite.coq_type

module Monoid :
 sig
  type 't law = 't -> 't -> 't
    (* singleton inductive, whose constructor was Law *)

  type 't com_law = 't law
    (* singleton inductive, whose constructor was ComLaw *)

  type 't mul_law =
    't -> 't -> 't
    (* singleton inductive, whose constructor was MulLaw *)

  type 't add_law = 't com_law
    (* singleton inductive, whose constructor was AddLaw *)
 end

type ('r, 'i) bigbody =
| BigBody of 'i * ('r -> 'r -> 'r) * bool * 'r

val applybig : ('a1, 'a2) bigbody -> 'a1 -> 'a1

val reducebig : 'a1 -> 'a2 list -> ('a2 -> ('a1, 'a2) bigbody) -> 'a1

module type BigOpSig =
 sig
  val bigop : 'a1 -> 'a2 list -> ('a2 -> ('a1, 'a2) bigbody) -> 'a1
 end

module BigOp :
 BigOpSig

val index_enum_key : unit

val index_enum : Finite.coq_type -> Finite.sort list

type set_type = bool finfun_of
  (* singleton inductive, whose constructor was FinSet *)

val finfun_of_set : Finite.coq_type -> set_type -> bool finfun_of

type set_of = set_type

val set_subType : Finite.coq_type -> bool finfun_of subType

val set_eqMixin : Finite.coq_type -> set_type Equality.mixin_of

val set_eqType : Finite.coq_type -> Equality.coq_type

val set_choiceMixin : Finite.coq_type -> set_type Choice.mixin_of

val set_choiceType : Finite.coq_type -> Choice.coq_type

val set_countMixin : Finite.coq_type -> set_type Countable.mixin_of

val set_countType : Finite.coq_type -> Countable.coq_type

val set_subCountType : Finite.coq_type -> subCountType

val set_finMixin : Finite.coq_type -> Finite.mixin_of

val set_finType : Finite.coq_type -> Finite.coq_type

module type SetDefSig =
 sig
  val finset : Finite.coq_type -> Finite.sort pred0 -> set_of

  val pred_of_set : Finite.coq_type -> set_type -> fin_pred_sort
 end

module SetDef :
 SetDefSig

val set_of_choiceType : Finite.coq_type -> Choice.coq_type

val set_of_countType : Finite.coq_type -> Countable.coq_type

val set_of_finType : Finite.coq_type -> Finite.coq_type

val setTfor : Finite.coq_type -> set_of

val set1 : Finite.coq_type -> Finite.sort -> set_of

val setI : Finite.coq_type -> set_of -> set_of -> set_of

module type ImsetSig =
 sig
  val imset :
    Finite.coq_type -> Finite.coq_type -> (Finite.sort -> Finite.sort) ->
    Finite.sort mem_pred -> set_of

  val imset2 :
    Finite.coq_type -> Finite.coq_type -> Finite.coq_type -> (Finite.sort ->
    Finite.sort -> Finite.sort) -> Finite.sort mem_pred -> (Finite.sort ->
    Finite.sort mem_pred) -> set_of
 end

module Imset :
 ImsetSig

val preimset : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 mem_pred -> set_of

module FinGroup :
 sig
  type 't mixin_of = { mul : ('t -> 't -> 't); one : 't; inv : ('t -> 't) }

  val mul : 'a1 mixin_of -> 'a1 -> 'a1 -> 'a1

  val one : 'a1 mixin_of -> 'a1

  val inv : 'a1 mixin_of -> 'a1 -> 'a1

  type base_type = { base_type__0 : __ mixin_of; base_type__1 : __ Finite.class_of }

  type sort = __

  type arg_sort = sort

  val mixin : base_type -> sort mixin_of

  val finClass : base_type -> sort Finite.class_of

  type coq_type = base_type
    (* singleton inductive, whose constructor was Pack *)

  val base : coq_type -> base_type

  val coq_Mixin : 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> 'a1 mixin_of

  val finType : base_type -> Finite.coq_type

  val arg_finType : base_type -> Finite.coq_type
 end

val oneg : FinGroup.base_type -> FinGroup.sort

val mulg :
  FinGroup.base_type -> FinGroup.arg_sort -> FinGroup.arg_sort -> FinGroup.sort

val invg : FinGroup.base_type -> FinGroup.arg_sort -> FinGroup.sort

val set_mulg : FinGroup.base_type -> set_of -> set_of -> set_of

val set_invg : FinGroup.base_type -> set_of -> set_of

val group_set_baseGroupMixin : FinGroup.base_type -> set_type FinGroup.mixin_of

val group_set_of_baseGroupType : FinGroup.base_type -> FinGroup.base_type

module GroupSet :
 sig
  type sort = set_of
 end

val group_set_eqType : FinGroup.base_type -> Equality.coq_type

val group_set_choiceType : FinGroup.base_type -> Choice.coq_type

val group_set_countType : FinGroup.base_type -> Countable.coq_type

val group_set_finType : FinGroup.base_type -> Finite.coq_type

val group_set : FinGroup.coq_type -> set_of -> bool

type group_type = GroupSet.sort
  (* singleton inductive, whose constructor was Group *)

val gval : FinGroup.coq_type -> group_type -> GroupSet.sort

val group_subType : FinGroup.coq_type -> GroupSet.sort subType

val group_eqMixin : FinGroup.coq_type -> group_type Equality.mixin_of

val group_eqType : FinGroup.coq_type -> Equality.coq_type

val group_choiceMixin : FinGroup.coq_type -> group_type Choice.mixin_of

val group_choiceType : FinGroup.coq_type -> Choice.coq_type

val group_countMixin : FinGroup.coq_type -> group_type Countable.mixin_of

val group_subCountType : FinGroup.coq_type -> subCountType

val group_finMixin : FinGroup.coq_type -> Finite.mixin_of

val group_finType : FinGroup.coq_type -> Finite.coq_type

val group_of_finType : FinGroup.coq_type -> Finite.coq_type

val generated : FinGroup.coq_type -> set_of -> set_of

val cycle : FinGroup.coq_type -> FinGroup.arg_sort -> set_of

type perm_type =
  Finite.sort finfun_of
  (* singleton inductive, whose constructor was Perm *)

val pval : Finite.coq_type -> perm_type -> Finite.sort finfun_of

type perm_of = perm_type

val perm_subType : Finite.coq_type -> Finite.sort finfun_of subType

val perm_eqMixin : Finite.coq_type -> perm_type Equality.mixin_of

val perm_eqType : Finite.coq_type -> Equality.coq_type

val perm_choiceMixin : Finite.coq_type -> perm_type Choice.mixin_of

val perm_choiceType : Finite.coq_type -> Choice.coq_type

val perm_countMixin : Finite.coq_type -> perm_type Countable.mixin_of

val perm_subCountType : Finite.coq_type -> subCountType

val perm_finMixin : Finite.coq_type -> Finite.mixin_of

val perm_finType : Finite.coq_type -> Finite.coq_type

val perm_for_finType : Finite.coq_type -> Finite.coq_type

module type PermDefSig =
 sig
  val fun_of_perm : Finite.coq_type -> perm_type -> Finite.sort -> Finite.sort

  val perm : Finite.coq_type -> (Finite.sort -> Finite.sort) -> perm_of
 end

module PermDef :
 PermDefSig

val perm_one : Finite.coq_type -> perm_of

val perm_inv : Finite.coq_type -> perm_of -> perm_of

val perm_mul : Finite.coq_type -> perm_of -> perm_of -> perm_of

val perm_of_baseFinGroupMixin : Finite.coq_type -> perm_type FinGroup.mixin_of

val perm_of_baseFinGroupType : Finite.coq_type -> FinGroup.base_type

val perm_of_finGroupType : Finite.coq_type -> FinGroup.coq_type

val aperm : Finite.coq_type -> Finite.sort -> perm_of -> Finite.sort

val porbit : Finite.coq_type -> perm_of -> Finite.sort -> set_of

val porbits : Finite.coq_type -> perm_of -> set_of

val odd_perm : Finite.coq_type -> perm_type -> bool

module GRing :
 sig
  module Zmodule :
   sig
    type 'v mixin_of = { zero : 'v; opp : ('v -> 'v); add : ('v -> 'v -> 'v) }

    val zero : 'a1 mixin_of -> 'a1

    val opp : 'a1 mixin_of -> 'a1 -> 'a1

    val add : 'a1 mixin_of -> 'a1 -> 'a1 -> 'a1

    type 't class_of = { base : 't Choice.class_of; mixin : 't mixin_of }

    val base : 'a1 class_of -> 'a1 Choice.class_of

    val mixin : 'a1 class_of -> 'a1 mixin_of

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    val coq_class : coq_type -> sort class_of

    val pack : 'a1 mixin_of -> Choice.coq_type -> 'a1 Choice.class_of -> coq_type

    val choiceType : coq_type -> Choice.coq_type
   end

  val zero : Zmodule.coq_type -> Zmodule.sort

  val opp : Zmodule.coq_type -> Zmodule.sort -> Zmodule.sort

  val add : Zmodule.coq_type -> Zmodule.sort -> Zmodule.sort -> Zmodule.sort

  module Ring :
   sig
    type mixin_of = { one : Zmodule.sort;
                      mul : (Zmodule.sort -> Zmodule.sort -> Zmodule.sort) }

    val one : Zmodule.coq_type -> mixin_of -> Zmodule.sort

    val mul :
      Zmodule.coq_type -> mixin_of -> Zmodule.sort -> Zmodule.sort -> Zmodule.sort

    val coq_EtaMixin :
      Zmodule.coq_type -> Zmodule.sort -> (Zmodule.sort -> Zmodule.sort ->
      Zmodule.sort) -> mixin_of

    type 'r class_of = { base : 'r Zmodule.class_of; mixin : mixin_of }

    val base : 'a1 class_of -> 'a1 Zmodule.class_of

    val mixin : 'a1 class_of -> mixin_of

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    val coq_class : coq_type -> sort class_of

    val pack :
      'a1 Zmodule.class_of -> mixin_of -> Zmodule.coq_type -> 'a1 Zmodule.class_of
      -> mixin_of -> coq_type

    val zmodType : coq_type -> Zmodule.coq_type
   end

  val one : Ring.coq_type -> Ring.sort

  val mul : Ring.coq_type -> Ring.sort -> Ring.sort -> Ring.sort

  val exp : Ring.coq_type -> Ring.sort -> nat -> Ring.sort

  module Lmodule :
   sig
    type mixin_of =
      Ring.sort -> Zmodule.sort -> Zmodule.sort
      (* singleton inductive, whose constructor was Mixin *)

    val scale :
      Ring.coq_type -> Zmodule.coq_type -> mixin_of -> Ring.sort -> Zmodule.sort ->
      Zmodule.sort

    type 'v class_of = { base : 'v Zmodule.class_of; mixin : mixin_of }

    val base : Ring.coq_type -> 'a1 class_of -> 'a1 Zmodule.class_of

    val mixin : Ring.coq_type -> 'a1 class_of -> mixin_of

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    val coq_class : Ring.coq_type -> coq_type -> sort class_of
   end

  val scale :
    Ring.coq_type -> Lmodule.coq_type -> Ring.sort -> Lmodule.sort -> Lmodule.sort

  module ComRing :
   sig
    val coq_RingMixin :
      Zmodule.coq_type -> Zmodule.sort -> (Zmodule.sort -> Zmodule.sort ->
      Zmodule.sort) -> Ring.mixin_of

    type 'r class_of =
      'r Ring.class_of
      (* singleton inductive, whose constructor was Class *)

    val base : 'a1 class_of -> 'a1 Ring.class_of

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    val coq_class : coq_type -> sort class_of

    val pack : ('a1 -> 'a1 -> 'a1) -> Ring.coq_type -> 'a1 Ring.class_of -> coq_type
   end

  module UnitRing :
   sig
    type mixin_of = { coq_unit : Ring.sort pred0; inv : (Ring.sort -> Ring.sort) }

    val coq_unit : Ring.coq_type -> mixin_of -> Ring.sort pred0

    val inv : Ring.coq_type -> mixin_of -> Ring.sort -> Ring.sort

    val coq_EtaMixin :
      Ring.coq_type -> Ring.sort pred0 -> (Ring.sort -> Ring.sort) -> mixin_of

    type 'r class_of = { base : 'r Ring.class_of; mixin : mixin_of }

    val base : 'a1 class_of -> 'a1 Ring.class_of

    val mixin : 'a1 class_of -> mixin_of

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    val coq_class : coq_type -> sort class_of

    val ringType : coq_type -> Ring.coq_type
   end

  val coq_unit : UnitRing.coq_type -> UnitRing.sort qualifier

  val inv : UnitRing.coq_type -> UnitRing.sort -> UnitRing.sort

  module ComUnitRing :
   sig
    type 'r class_of = { base : 'r ComRing.class_of; mixin : UnitRing.mixin_of }

    val base : 'a1 class_of -> 'a1 ComRing.class_of

    val mixin : 'a1 class_of -> UnitRing.mixin_of

    val base2 : 'a1 class_of -> 'a1 UnitRing.class_of

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    val coq_class : coq_type -> sort class_of

    val ringType : coq_type -> Ring.coq_type

    val unitRingType : coq_type -> UnitRing.coq_type
   end

  module IntegralDomain :
   sig
    type 'r class_of =
      'r ComUnitRing.class_of
      (* singleton inductive, whose constructor was Class *)

    val base : 'a1 class_of -> 'a1 ComUnitRing.class_of

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    val coq_class : coq_type -> sort class_of
   end

  module Field :
   sig
    type 'f class_of =
      'f IntegralDomain.class_of
      (* singleton inductive, whose constructor was Class *)

    val base : 'a1 class_of -> 'a1 IntegralDomain.class_of

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    val coq_class : coq_type -> sort class_of

    val pack :
      'a1 UnitRing.class_of -> IntegralDomain.coq_type -> 'a1
      IntegralDomain.class_of -> coq_type

    val comUnitRingType : coq_type -> ComUnitRing.coq_type
   end
 end

type 'r matrix0 = 'r finfun_of
  (* singleton inductive, whose constructor was Matrix *)

val mx_val : nat -> nat -> 'a1 matrix0 -> 'a1 finfun_of

val matrix_subType : nat -> nat -> 'a1 finfun_of subType

val matrix_key : unit

val matrix_of_fun_def :
  nat -> nat -> (Finite.sort -> Finite.sort -> 'a1) -> 'a1 matrix0

val matrix_of_fun :
  nat -> nat -> unit -> (Finite.sort -> Finite.sort -> 'a1) -> 'a1 matrix0

val fun_of_matrix : nat -> nat -> 'a1 matrix0 -> ordinal -> ordinal -> 'a1

val matrix_eqMixin :
  Equality.coq_type -> nat -> nat -> Equality.sort matrix0 Equality.mixin_of

val matrix_eqType : Equality.coq_type -> nat -> nat -> Equality.coq_type

val matrix_choiceMixin :
  Choice.coq_type -> nat -> nat -> Choice.sort matrix0 Choice.mixin_of

val matrix_choiceType : Choice.coq_type -> nat -> nat -> Choice.coq_type

val const_mx_key : unit

val const_mx : nat -> nat -> 'a1 -> 'a1 matrix0

val row' : nat -> nat -> ordinal -> 'a1 matrix0 -> 'a1 matrix0

val col' : nat -> nat -> ordinal -> 'a1 matrix0 -> 'a1 matrix0

val oppmx_key : unit

val addmx_key : unit

val oppmx :
  GRing.Zmodule.coq_type -> nat -> nat -> GRing.Zmodule.sort matrix0 ->
  GRing.Zmodule.sort matrix0

val addmx :
  GRing.Zmodule.coq_type -> nat -> nat -> GRing.Zmodule.sort matrix0 ->
  GRing.Zmodule.sort matrix0 -> GRing.Zmodule.sort matrix0

val matrix_zmodMixin :
  GRing.Zmodule.coq_type -> nat -> nat -> GRing.Zmodule.sort matrix0
  GRing.Zmodule.mixin_of

val matrix_zmodType : GRing.Zmodule.coq_type -> nat -> nat -> GRing.Zmodule.coq_type

val scalemx_key : unit

val scalemx :
  GRing.Ring.coq_type -> nat -> nat -> GRing.Ring.sort -> GRing.Ring.sort matrix0 ->
  GRing.Ring.sort matrix0

val matrix_lmodMixin : GRing.Ring.coq_type -> nat -> nat -> GRing.Lmodule.mixin_of

val matrix_lmodType : GRing.Ring.coq_type -> nat -> nat -> GRing.Lmodule.coq_type

val determinant :
  GRing.Ring.coq_type -> nat -> GRing.Ring.sort matrix0 -> GRing.Ring.sort

val cofactor :
  GRing.Ring.coq_type -> nat -> GRing.Ring.sort matrix0 -> ordinal -> ordinal ->
  GRing.Ring.sort

val adjugate_key : unit

val adjugate :
  GRing.Ring.coq_type -> nat -> GRing.Ring.sort matrix0 -> GRing.Ring.sort matrix0

val unitmx :
  GRing.ComUnitRing.coq_type -> nat -> GRing.ComUnitRing.sort matrix0 pred0

val invmx :
  GRing.ComUnitRing.coq_type -> nat -> GRing.ComUnitRing.sort matrix0 ->
  GRing.Lmodule.sort

val epsilon_statement : __ -> 'a1

val epsilon : __ -> 'a1

module Coq_makeField :
 functor (Coq_f:FieldSig) ->
 sig
  module AL :
   sig
   end

  type coq_R = Coq_f.coq_F

  val eqr : coq_R -> coq_R -> bool

  val eqrP : coq_R Equality.axiom

  val coq_R_eqMixin : coq_R Equality.mixin_of

  val coq_R_eqType : Equality.coq_type

  val pickR : coq_R pred0 -> nat -> coq_R option

  val coq_R_choiceMixin : coq_R Choice.mixin_of

  val coq_R_choiceType : Choice.coq_type

  val coq_R_zmodmixin : Coq_f.coq_F GRing.Zmodule.mixin_of

  val coq_R_zmodtype : GRing.Zmodule.coq_type

  val coq_R_comringmixin : GRing.Ring.mixin_of

  val coq_R_ring : GRing.Ring.coq_type

  val coq_R_comring : GRing.ComRing.coq_type

  val coq_Radd_monoid : Coq_f.coq_F Monoid.law

  val coq_Radd_comoid : Coq_f.coq_F Monoid.com_law

  val coq_Rmul_monoid : GRing.Zmodule.sort Monoid.law

  val coq_Rmul_comoid : Coq_f.coq_F Monoid.com_law

  val coq_Rmul_mul_law : Coq_f.coq_F Monoid.mul_law

  val coq_Radd_add_law : Coq_f.coq_F Monoid.add_law

  val coq_Rinvx : coq_R -> Coq_f.coq_F

  val unit_R : coq_R -> bool

  val coq_R_unitRingMixin : GRing.UnitRing.mixin_of

  val coq_R_unitRing : GRing.UnitRing.coq_type

  val coq_R_comUnitRingType : GRing.ComUnitRing.coq_type

  val coq_R_idomainType : GRing.IntegralDomain.coq_type

  val coq_R_field : GRing.Field.coq_type
 end

val vector_inv_S : nat -> 'a1 t0 -> ('a1, 'a1 t0) sigT

val fin_inv_S : nat -> t -> (__, t) sum

val vector_to_finite_fun : nat -> 'a1 t0 -> t -> 'a1

val finite_fun_to_vector : nat -> (t -> 'a1) -> 'a1 t0

type 'r matrix1 = 'r t0 t0

val finite_fun_to_matrix : nat -> nat -> (t -> t -> 'a1) -> 'a1 matrix1

val matrix_to_finite_fun : nat -> nat -> 'a1 matrix1 -> t -> t -> 'a1

val finite_to_ord : nat -> t -> ordinal

val ord_to_finite : nat -> ordinal -> t

val matrix_to_matrix : nat -> nat -> 'a1 matrix1 -> 'a1 matrix0

val matrix_to_Matrix : nat -> nat -> 'a1 matrix0 -> 'a1 matrix1

val matrix_inv :
  GRing.Field.coq_type -> nat -> GRing.Field.sort matrix1 -> GRing.Field.sort matrix1

module MatricesFieldIns :
 functor (Field:FieldSig) ->
 sig
  module Coq_mat :
   sig
    module F :
     sig
      type coq_A = Field.coq_F
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

      val eqA_dec : Field.coq_F -> Field.coq_F -> bool
     end

    module FSemiRingT :
     sig
      module ES :
       sig
        module Eq :
         sig
          type coq_A = F.coq_A
         end

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      val coq_A0 : Field.coq_F

      val coq_A1 : Field.coq_F

      val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

      val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = Field.coq_F t0

    val coq_VF_zero : nat -> Field.coq_F t0

    val coq_VF_one : nat -> Field.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val coq_VF_prod : nat -> coq_VF -> Field.coq_F

    val coq_VF_sum : nat -> coq_VF -> Field.coq_F

    val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_neg : nat -> coq_VF -> coq_VF

    val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

    val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

    val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

    val coq_MFisPermutation : nat -> coq_MF -> bool

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> Field.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module AL :
   sig
   end

  module FAL :
   sig
    module AL :
     sig
     end
   end

  val coq_VandermondeCol : nat -> Field.coq_F -> Field.coq_F t0

  val coq_VandermondeColGen : nat -> Field.coq_F -> nat -> Field.coq_F t0

  val coq_Vandermonde : nat -> Coq_mat.coq_VF -> Field.coq_F t0 t0

  module SSRfield :
   sig
    module AL :
     sig
     end

    type coq_R = Field.coq_F

    val eqr : coq_R -> coq_R -> bool

    val eqrP : coq_R Equality.axiom

    val coq_R_eqMixin : coq_R Equality.mixin_of

    val coq_R_eqType : Equality.coq_type

    val pickR : coq_R pred0 -> nat -> coq_R option

    val coq_R_choiceMixin : coq_R Choice.mixin_of

    val coq_R_choiceType : Choice.coq_type

    val coq_R_zmodmixin : Field.coq_F GRing.Zmodule.mixin_of

    val coq_R_zmodtype : GRing.Zmodule.coq_type

    val coq_R_comringmixin : GRing.Ring.mixin_of

    val coq_R_ring : GRing.Ring.coq_type

    val coq_R_comring : GRing.ComRing.coq_type

    val coq_Radd_monoid : Field.coq_F Monoid.law

    val coq_Radd_comoid : Field.coq_F Monoid.com_law

    val coq_Rmul_monoid : GRing.Zmodule.sort Monoid.law

    val coq_Rmul_comoid : Field.coq_F Monoid.com_law

    val coq_Rmul_mul_law : Field.coq_F Monoid.mul_law

    val coq_Radd_add_law : Field.coq_F Monoid.add_law

    val coq_Rinvx : coq_R -> Field.coq_F

    val unit_R : coq_R -> bool

    val coq_R_unitRingMixin : GRing.UnitRing.mixin_of

    val coq_R_unitRing : GRing.UnitRing.coq_type

    val coq_R_comUnitRingType : GRing.ComUnitRing.coq_type

    val coq_R_idomainType : GRing.IntegralDomain.coq_type

    val coq_R_field : GRing.Field.coq_type
   end

  val coq_VandermondeInv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_MF

  val nat_to_ord : nat -> nat -> ordinal

  val coq_VF_inv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_VF
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

module type Coq_Nat =
 sig
  val coq_N : nat
 end

module GroupNthIns :
 functor (Group:GroupSig) ->
 functor (Hack:Coq_Nat) ->
 sig
  type coq_G = Group.coq_G t0

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : Group.coq_G t0

  val coq_Ggen : Group.coq_G t0

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Gdisjoint : coq_G -> coq_G -> bool

  val coq_Ginv : coq_G -> Group.coq_G t0
 end

module NthRingIns :
 functor (Hack:Coq_Nat) ->
 functor (Ring:RingSig) ->
 sig
  type coq_F = Ring.coq_F t0

  val coq_Fadd : coq_F -> coq_F -> Ring.coq_F t0

  val coq_Fzero : Ring.coq_F t0

  val coq_Fbool_eq : coq_F -> coq_F -> bool

  val coq_Fsub : coq_F -> coq_F -> Ring.coq_F t0

  val coq_Finv : coq_F -> Ring.coq_F t0

  val coq_Fmul : coq_F -> coq_F -> Ring.coq_F t0

  val coq_Fone : Ring.coq_F t0
 end

module NthVectorSpaceIns :
 functor (Hack:Coq_Nat) ->
 functor (Group:GroupSig) ->
 functor (Field:FieldSig) ->
 functor (NthGroup:sig
  type coq_G = Group.coq_G t0

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : Group.coq_G t0

  val coq_Ggen : Group.coq_G t0

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Gdisjoint : coq_G -> coq_G -> bool

  val coq_Ginv : coq_G -> Group.coq_G t0
 end) ->
 functor (VS:sig
  val op : Group.coq_G -> Field.coq_F -> Group.coq_G
 end) ->
 sig
  module MatF :
   sig
    module F :
     sig
      type coq_A = Field.coq_F
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

      val eqA_dec : Field.coq_F -> Field.coq_F -> bool
     end

    module FSemiRingT :
     sig
      module ES :
       sig
        module Eq :
         sig
          type coq_A = F.coq_A
         end

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      val coq_A0 : Field.coq_F

      val coq_A1 : Field.coq_F

      val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

      val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = Field.coq_F t0

    val coq_VF_zero : nat -> Field.coq_F t0

    val coq_VF_one : nat -> Field.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val coq_VF_prod : nat -> coq_VF -> Field.coq_F

    val coq_VF_sum : nat -> coq_VF -> Field.coq_F

    val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_neg : nat -> coq_VF -> coq_VF

    val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

    val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

    val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

    val coq_MFisPermutation : nat -> coq_MF -> bool

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> Field.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module Mat :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Group.coq_G t0

    val coq_VG_id : nat -> Group.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Group.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> MatF.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_VG_scale_sum : nat -> nat -> nat -> MatF.coq_VF t0 t0 -> MatF.coq_VF t0
   end

  val op : NthGroup.coq_G -> Field.coq_F -> Mat.coq_VG
 end

module VectorSpaceModuleSameGroupNthStackIns :
 functor (Hack:Coq_Nat) ->
 functor (Group:GroupSig) ->
 functor (Field:FieldSig) ->
 functor (Ring:RingSig) ->
 functor (VS:sig
  val op : Group.coq_G -> Field.coq_F -> Group.coq_G
 end) ->
 functor (NthGroup:sig
  type coq_G = Group.coq_G t0

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : Group.coq_G t0

  val coq_Ggen : Group.coq_G t0

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Gdisjoint : coq_G -> coq_G -> bool

  val coq_Ginv : coq_G -> Group.coq_G t0
 end) ->
 functor (NthRing:sig
  type coq_F = Ring.coq_F t0

  val coq_Fadd : coq_F -> coq_F -> Ring.coq_F t0

  val coq_Fzero : Ring.coq_F t0

  val coq_Fbool_eq : coq_F -> coq_F -> bool

  val coq_Fsub : coq_F -> coq_F -> Ring.coq_F t0

  val coq_Finv : coq_F -> Ring.coq_F t0

  val coq_Fmul : coq_F -> coq_F -> Ring.coq_F t0

  val coq_Fone : Ring.coq_F t0
 end) ->
 functor (NthVectorSpace:sig
  module MatF :
   sig
    module F :
     sig
      type coq_A = Field.coq_F
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

      val eqA_dec : Field.coq_F -> Field.coq_F -> bool
     end

    module FSemiRingT :
     sig
      module ES :
       sig
        module Eq :
         sig
          type coq_A = F.coq_A
         end

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      val coq_A0 : Field.coq_F

      val coq_A1 : Field.coq_F

      val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

      val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = Field.coq_F t0

    val coq_VF_zero : nat -> Field.coq_F t0

    val coq_VF_one : nat -> Field.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val coq_VF_prod : nat -> coq_VF -> Field.coq_F

    val coq_VF_sum : nat -> coq_VF -> Field.coq_F

    val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_neg : nat -> coq_VF -> coq_VF

    val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

    val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

    val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

    val coq_MFisPermutation : nat -> coq_MF -> bool

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> Field.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module Mat :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Group.coq_G t0

    val coq_VG_id : nat -> Group.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Group.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> MatF.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_VG_scale_sum : nat -> nat -> nat -> MatF.coq_VF t0 t0 -> MatF.coq_VF t0
   end

  val op : NthGroup.coq_G -> Field.coq_F -> Mat.coq_VG
 end) ->
 functor (MVS:sig
  val op3 : Ring.coq_F -> Field.coq_F -> Ring.coq_F
 end) ->
 sig
  val op3 : NthRing.coq_F -> Field.coq_F -> Ring.coq_F t0
 end

module GroupFromRingIns :
 functor (Ring:RingSig) ->
 sig
  type coq_G = Ring.coq_F

  val coq_Gdot : Ring.coq_F -> Ring.coq_F -> Ring.coq_F

  val coq_Gone : Ring.coq_F

  val coq_Ggen : Ring.coq_F

  val coq_Gbool_eq : Ring.coq_F -> Ring.coq_F -> bool

  val coq_Gdisjoint : Ring.coq_F -> Ring.coq_F -> bool

  val coq_Ginv : Ring.coq_F -> Ring.coq_F
 end

module GroupFromFieldIns :
 functor (Field:FieldSig) ->
 sig
  type coq_G = Field.coq_F

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : coq_G

  val coq_Ggen : coq_G

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Gdisjoint : coq_G -> coq_G -> bool

  val coq_Ginv : coq_G -> coq_G
 end

module ProdGroupSigIns :
 functor (M1M:GroupSig) ->
 functor (M2M:GroupSig) ->
 sig
  type coq_G = M1M.coq_G * M2M.coq_G

  val coq_Gdot : coq_G -> coq_G -> M1M.coq_G * M2M.coq_G

  val coq_Gone : M1M.coq_G * M2M.coq_G

  val coq_Ggen : M1M.coq_G * M2M.coq_G

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Gdisjoint : coq_G -> coq_G -> bool

  val coq_Ginv : coq_G -> M1M.coq_G * M2M.coq_G
 end

module MixablePropIns :
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
 functor (Mix:sig
  type coq_KGR

  type coq_PK

  type coq_M = Message.coq_G

  val coq_Mop : Message.coq_G -> Message.coq_G -> Message.coq_G

  val coq_Mzero : Message.coq_G

  val coq_Mone : Message.coq_G

  val coq_Minv : Message.coq_G -> Message.coq_G

  val coq_Mbool_eq : Message.coq_G -> Message.coq_G -> bool

  val keygenMix : coq_KGR -> coq_PK

  val enc : coq_PK -> coq_M -> Ring.coq_F -> Ciphertext.coq_G
 end) ->
 sig
  module AddVSLemmas :
   sig
    module AL :
     sig
     end
   end

  module Mat :
   sig
    module F :
     sig
      type coq_A = Field.coq_F
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

      val eqA_dec : Field.coq_F -> Field.coq_F -> bool
     end

    module FSemiRingT :
     sig
      module ES :
       sig
        module Eq :
         sig
          type coq_A = F.coq_A
         end

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      val coq_A0 : Field.coq_F

      val coq_A1 : Field.coq_F

      val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

      val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = Field.coq_F t0

    val coq_VF_zero : nat -> Field.coq_F t0

    val coq_VF_one : nat -> Field.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val coq_VF_prod : nat -> coq_VF -> Field.coq_F

    val coq_VF_sum : nat -> coq_VF -> Field.coq_F

    val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_neg : nat -> coq_VF -> coq_VF

    val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

    val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

    val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

    val coq_MFisPermutation : nat -> coq_MF -> bool

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> Field.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module MatG :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Ciphertext.coq_G t0

    val coq_VG_id : nat -> Ciphertext.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mat.coq_MF -> coq_VG

    val coq_VG_scale_sum : nat -> nat -> nat -> Mat.coq_VF t0 t0 -> Mat.coq_VF t0
   end

  val reenc : Mix.coq_PK -> Ciphertext.coq_G -> Ring.coq_F -> Ciphertext.coq_G

  val bIsReEnc :
    Mix.coq_PK -> Ciphertext.coq_G -> Ciphertext.coq_G -> Ring.coq_F -> bool

  val decryptsToExt :
    Mix.coq_PK -> Ciphertext.coq_G -> Mix.coq_M -> Ring.coq_F -> bool
 end

module EncryptionSchemeProp :
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

  val coq_Mone : Message.coq_G

  val coq_Minv : Message.coq_G -> Message.coq_G

  val coq_Mbool_eq : Message.coq_G -> Message.coq_G -> bool

  val keygen : coq_KGR -> coq_PK * coq_SK

  val keygenMix : coq_KGR -> coq_PK

  val enc : coq_PK -> coq_M -> Ring.coq_F -> Ciphertext.coq_G

  val dec : coq_SK -> Ciphertext.coq_G -> coq_M

  val keymatch : coq_PK -> coq_SK -> bool
 end) ->
 sig
  module AddVSLemmas :
   sig
    module AL :
     sig
     end
   end

  module Mat :
   sig
    module F :
     sig
      type coq_A = Field.coq_F
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

      val eqA_dec : Field.coq_F -> Field.coq_F -> bool
     end

    module FSemiRingT :
     sig
      module ES :
       sig
        module Eq :
         sig
          type coq_A = F.coq_A
         end

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      val coq_A0 : Field.coq_F

      val coq_A1 : Field.coq_F

      val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

      val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = Field.coq_F t0

    val coq_VF_zero : nat -> Field.coq_F t0

    val coq_VF_one : nat -> Field.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val coq_VF_prod : nat -> coq_VF -> Field.coq_F

    val coq_VF_sum : nat -> coq_VF -> Field.coq_F

    val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_neg : nat -> coq_VF -> coq_VF

    val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

    val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

    val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

    val coq_MFisPermutation : nat -> coq_MF -> bool

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> Field.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module MatG :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Ciphertext.coq_G t0

    val coq_VG_id : nat -> Ciphertext.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mat.coq_MF -> coq_VG

    val coq_VG_scale_sum : nat -> nat -> nat -> Mat.coq_VF t0 t0 -> Mat.coq_VF t0
   end

  val reenc : Enc.coq_PK -> Ciphertext.coq_G -> Ring.coq_F -> Ciphertext.coq_G

  val bIsReEnc :
    Enc.coq_PK -> Ciphertext.coq_G -> Ciphertext.coq_G -> Ring.coq_F -> bool

  val decryptsToExt :
    Enc.coq_PK -> Ciphertext.coq_G -> Enc.coq_M -> Ring.coq_F -> bool
 end

module type Coq0_Nat =
 sig
  val coq_N : nat
 end

module ExtendedElGamal :
 functor (Hack:Coq0_Nat) ->
 functor (Group:GroupSig) ->
 functor (Field:FieldSig) ->
 functor (VS:sig
  val op : Group.coq_G -> Field.coq_F -> Group.coq_G
 end) ->
 functor (NthGroupM:sig
  type coq_G = Group.coq_G t0

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : Group.coq_G t0

  val coq_Ggen : Group.coq_G t0

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Gdisjoint : coq_G -> coq_G -> bool

  val coq_Ginv : coq_G -> Group.coq_G t0
 end) ->
 functor (DualGroup:sig
  type coq_G = Group.coq_G * Group.coq_G

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : Group.coq_G * Group.coq_G

  val coq_Ggen : Group.coq_G * Group.coq_G

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Gdisjoint : coq_G -> coq_G -> bool

  val coq_Ginv : (Group.coq_G * Group.coq_G) -> Group.coq_G * Group.coq_G
 end) ->
 functor (DVS:sig
  val op : DualGroup.coq_G -> Field.coq_F -> Group.coq_G * Group.coq_G
 end) ->
 functor (NthGroup:sig
  type coq_G = DualGroup.coq_G t0

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : DualGroup.coq_G t0

  val coq_Ggen : DualGroup.coq_G t0

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Gdisjoint : coq_G -> coq_G -> bool

  val coq_Ginv : coq_G -> DualGroup.coq_G t0
 end) ->
 functor (NthRing:sig
  type coq_F = Field.coq_F t0

  val coq_Fadd : coq_F -> coq_F -> Field.coq_F t0

  val coq_Fzero : Field.coq_F t0

  val coq_Fbool_eq : coq_F -> coq_F -> bool

  val coq_Fsub : coq_F -> coq_F -> Field.coq_F t0

  val coq_Finv : coq_F -> Field.coq_F t0

  val coq_Fmul : coq_F -> coq_F -> Field.coq_F t0

  val coq_Fone : Field.coq_F t0
 end) ->
 functor (NthVS:sig
  module MatF :
   sig
    module F :
     sig
      type coq_A = Field.coq_F
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

      val eqA_dec : Field.coq_F -> Field.coq_F -> bool
     end

    module FSemiRingT :
     sig
      module ES :
       sig
        module Eq :
         sig
          type coq_A = F.coq_A
         end

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      val coq_A0 : Field.coq_F

      val coq_A1 : Field.coq_F

      val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

      val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = Field.coq_F t0

    val coq_VF_zero : nat -> Field.coq_F t0

    val coq_VF_one : nat -> Field.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val coq_VF_prod : nat -> coq_VF -> Field.coq_F

    val coq_VF_sum : nat -> coq_VF -> Field.coq_F

    val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_neg : nat -> coq_VF -> coq_VF

    val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

    val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

    val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

    val coq_MFisPermutation : nat -> coq_MF -> bool

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> Field.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module Mat :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = DualGroup.coq_G t0

    val coq_VG_id : nat -> DualGroup.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> DualGroup.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> MatF.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_VG_scale_sum : nat -> nat -> nat -> MatF.coq_VF t0 t0 -> MatF.coq_VF t0
   end

  val op : NthGroup.coq_G -> Field.coq_F -> Mat.coq_VG
 end) ->
 functor (NthMVS:sig
  module MatF :
   sig
    module F :
     sig
      type coq_A = Field.coq_F
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

      val eqA_dec : Field.coq_F -> Field.coq_F -> bool
     end

    module FSemiRingT :
     sig
      module ES :
       sig
        module Eq :
         sig
          type coq_A = F.coq_A
         end

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      val coq_A0 : Field.coq_F

      val coq_A1 : Field.coq_F

      val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

      val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = Field.coq_F t0

    val coq_VF_zero : nat -> Field.coq_F t0

    val coq_VF_one : nat -> Field.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val coq_VF_prod : nat -> coq_VF -> Field.coq_F

    val coq_VF_sum : nat -> coq_VF -> Field.coq_F

    val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_neg : nat -> coq_VF -> coq_VF

    val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

    val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

    val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

    val coq_MFisPermutation : nat -> coq_MF -> bool

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> Field.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module Mat :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Group.coq_G t0

    val coq_VG_id : nat -> Group.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Group.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> MatF.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_VG_scale_sum : nat -> nat -> nat -> MatF.coq_VF t0 t0 -> MatF.coq_VF t0
   end

  val op : NthGroupM.coq_G -> Field.coq_F -> Mat.coq_VG
 end) ->
 functor (MVS:sig
  val op3 : NthRing.coq_F -> Field.coq_F -> Field.coq_F t0
 end) ->
 sig
  module Mo :
   sig
    module F :
     sig
      type coq_A = Field.coq_F
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

      val eqA_dec : Field.coq_F -> Field.coq_F -> bool
     end

    module FSemiRingT :
     sig
      module ES :
       sig
        module Eq :
         sig
          type coq_A = F.coq_A
         end

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      val coq_A0 : Field.coq_F

      val coq_A1 : Field.coq_F

      val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

      val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = Field.coq_F t0

    val coq_VF_zero : nat -> Field.coq_F t0

    val coq_VF_one : nat -> Field.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val coq_VF_prod : nat -> coq_VF -> Field.coq_F

    val coq_VF_sum : nat -> coq_VF -> Field.coq_F

    val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_neg : nat -> coq_VF -> coq_VF

    val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

    val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

    val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

    val coq_MFisPermutation : nat -> coq_MF -> bool

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> Field.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module MoM :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Group.coq_G t0

    val coq_VG_id : nat -> Group.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Group.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.coq_MF -> coq_VG

    val coq_VG_scale_sum : nat -> nat -> nat -> Mo.coq_VF t0 t0 -> Mo.coq_VF t0
   end

  module AddVSLemmas :
   sig
    module AL :
     sig
     end
   end

  type coq_KGR = MoM.coq_VG * Mo.coq_VF

  type coq_PK = NthGroup.coq_G

  type coq_SK = Mo.coq_VF

  type coq_M = NthGroupM.coq_G

  val coq_Mop : NthGroupM.coq_G -> NthGroupM.coq_G -> NthGroupM.coq_G

  val coq_Mzero : Group.coq_G t0

  val coq_Mone : Group.coq_G t0

  val coq_Minv : NthGroupM.coq_G -> Group.coq_G t0

  val coq_Mbool_eq : NthGroupM.coq_G -> NthGroupM.coq_G -> bool

  val keygen : coq_KGR -> coq_PK * coq_SK

  val keygenMix : coq_KGR -> coq_PK

  val enc : coq_PK -> coq_M -> Mo.coq_VF -> NthGroup.coq_G

  val dec : coq_SK -> NthGroup.coq_G -> coq_M

  val keymatch : coq_PK -> coq_SK -> bool
 end

module BasicComScheme :
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

      val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

      val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val vector_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val add_vectors :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

      val dot_product :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A
     end

    type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

    val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

    val mat_build_spec :
      nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

    val mat_build :
      nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

    val zero_matrix : nat -> nat -> matrix

    val id_matrix : nat -> matrix

    val inverse_matrix :
      (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix ->
      matrix

    type row_mat = matrix

    type col_mat = matrix

    val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

    val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

    val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

    val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

    val mat_transpose : nat -> nat -> matrix -> matrix

    val vec_plus :
      nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
      FSemiRingT.ES.Eq.coq_A t0

    val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

    val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

    val mat_vec_prod :
      nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0

    val mat_forall2'_dec :
      nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

    val mat_forall2_dec :
      nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
   end

  module ALR :
   sig
   end

  type coq_VF = Ring.coq_F t0

  val coq_VF_zero : nat -> Ring.coq_F t0

  val coq_VF_one : nat -> Ring.coq_F t0

  val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

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

  val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

  val coq_MF_perm_last : nat -> coq_MF -> index

  val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

  val matRecover_sub : nat -> Ring.coq_F -> nat

  val matRecover : nat -> coq_VF -> coq_MF
 end) ->
 sig
  module AddMLemmas :
   sig
   end

  module MoM :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Group.coq_G t0

    val coq_VG_id : nat -> Group.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Group.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Ring.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.coq_MF -> coq_VG

    val coq_VG_scale_sum : nat -> nat -> nat -> Mo.coq_VF t0 t0 -> Mo.coq_VF t0
   end

  val coq_PC : Group.coq_G -> Group.coq_G -> Ring.coq_F -> Ring.coq_F -> Group.coq_G

  val comPC :
    nat -> Group.coq_G -> Group.coq_G -> Mo.coq_VF -> Mo.coq_VF -> MoM.coq_VG
 end

module ExtendComScheme :
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

      val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

      val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val vector_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val add_vectors :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

      val dot_product :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A
     end

    type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

    val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

    val mat_build_spec :
      nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

    val mat_build :
      nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

    val zero_matrix : nat -> nat -> matrix

    val id_matrix : nat -> matrix

    val inverse_matrix :
      (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix ->
      matrix

    type row_mat = matrix

    type col_mat = matrix

    val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

    val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

    val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

    val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

    val mat_transpose : nat -> nat -> matrix -> matrix

    val vec_plus :
      nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
      FSemiRingT.ES.Eq.coq_A t0

    val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

    val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

    val mat_vec_prod :
      nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0

    val mat_forall2'_dec :
      nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

    val mat_forall2_dec :
      nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
   end

  module ALR :
   sig
   end

  type coq_VF = Ring.coq_F t0

  val coq_VF_zero : nat -> Ring.coq_F t0

  val coq_VF_one : nat -> Ring.coq_F t0

  val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

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

  val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

  val coq_MF_perm_last : nat -> coq_MF -> index

  val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

  val matRecover_sub : nat -> Ring.coq_F -> nat

  val matRecover : nat -> coq_VF -> coq_MF
 end) ->
 sig
  module MoM :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Group.coq_G t0

    val coq_VG_id : nat -> Group.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Group.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Ring.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.coq_MF -> coq_VG

    val coq_VG_scale_sum : nat -> nat -> nat -> Mo.coq_VF t0 t0 -> Mo.coq_VF t0
   end

  val coq_EPC :
    nat -> Group.coq_G -> MoM.coq_VG -> Mo.coq_VF -> Ring.coq_F -> Group.coq_G

  val comEPC :
    nat -> nat -> Group.coq_G -> MoM.coq_VG -> Mo.coq_VF t0 -> Mo.coq_VF ->
    MoM.coq_VG

  val comEPCvec :
    nat -> nat -> Group.coq_G -> MoM.coq_VG -> Mo.coq_VF -> Mo.coq_VF -> MoM.coq_VG

  val com : nat -> Group.coq_G -> MoM.coq_VG -> Mo.coq_MF -> Mo.coq_VF -> MoM.coq_VG
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

module BGSupportIns :
 functor (Message:GroupSig) ->
 functor (Ciphertext:GroupSig) ->
 functor (Commitment:GroupSig) ->
 functor (Ring:RingSig) ->
 functor (Field:FieldSig) ->
 functor (VS2:sig
  val op : Commitment.coq_G -> Field.coq_F -> Commitment.coq_G
 end) ->
 functor (VS1:sig
  val op : Ciphertext.coq_G -> Field.coq_F -> Ciphertext.coq_G
 end) ->
 functor (MVS:sig
  val op3 : Ring.coq_F -> Field.coq_F -> Ring.coq_F
 end) ->
 functor (VS3:sig
  val op : Message.coq_G -> Field.coq_F -> Message.coq_G
 end) ->
 functor (Hack:Coq0_Nat) ->
 functor (M:Coq0_Nat) ->
 functor (Coq_enc:sig
  type coq_KGR

  type coq_PK

  type coq_SK

  type coq_M = Message.coq_G

  val coq_Mop : Message.coq_G -> Message.coq_G -> Message.coq_G

  val coq_Mzero : Message.coq_G

  val coq_Mone : Message.coq_G

  val coq_Minv : Message.coq_G -> Message.coq_G

  val coq_Mbool_eq : Message.coq_G -> Message.coq_G -> bool

  val keygen : coq_KGR -> coq_PK * coq_SK

  val keygenMix : coq_KGR -> coq_PK

  val enc : coq_PK -> coq_M -> Ring.coq_F -> Ciphertext.coq_G

  val dec : coq_SK -> Ciphertext.coq_G -> coq_M

  val keymatch : coq_PK -> coq_SK -> bool
 end) ->
 sig
  val n : nat

  val m : nat

  module Mo :
   sig
    module Coq_mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module AL :
     sig
     end

    module FAL :
     sig
      module AL :
       sig
       end
     end

    val coq_VandermondeCol : nat -> Field.coq_F -> Field.coq_F t0

    val coq_VandermondeColGen : nat -> Field.coq_F -> nat -> Field.coq_F t0

    val coq_Vandermonde : nat -> Coq_mat.coq_VF -> Field.coq_F t0 t0

    module SSRfield :
     sig
      module AL :
       sig
       end

      type coq_R = Field.coq_F

      val eqr : coq_R -> coq_R -> bool

      val eqrP : coq_R Equality.axiom

      val coq_R_eqMixin : coq_R Equality.mixin_of

      val coq_R_eqType : Equality.coq_type

      val pickR : coq_R pred0 -> nat -> coq_R option

      val coq_R_choiceMixin : coq_R Choice.mixin_of

      val coq_R_choiceType : Choice.coq_type

      val coq_R_zmodmixin : Field.coq_F GRing.Zmodule.mixin_of

      val coq_R_zmodtype : GRing.Zmodule.coq_type

      val coq_R_comringmixin : GRing.Ring.mixin_of

      val coq_R_ring : GRing.Ring.coq_type

      val coq_R_comring : GRing.ComRing.coq_type

      val coq_Radd_monoid : Field.coq_F Monoid.law

      val coq_Radd_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_monoid : GRing.Zmodule.sort Monoid.law

      val coq_Rmul_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_mul_law : Field.coq_F Monoid.mul_law

      val coq_Radd_add_law : Field.coq_F Monoid.add_law

      val coq_Rinvx : coq_R -> Field.coq_F

      val unit_R : coq_R -> bool

      val coq_R_unitRingMixin : GRing.UnitRing.mixin_of

      val coq_R_unitRing : GRing.UnitRing.coq_type

      val coq_R_comUnitRingType : GRing.ComUnitRing.coq_type

      val coq_R_idomainType : GRing.IntegralDomain.coq_type

      val coq_R_field : GRing.Field.coq_type
     end

    val coq_VandermondeInv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_MF

    val nat_to_ord : nat -> nat -> ordinal

    val coq_VF_inv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_VF
   end

  module MoR :
   sig
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = Ring.coq_F t0

    val coq_VF_zero : nat -> Ring.coq_F t0

    val coq_VF_one : nat -> Ring.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

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

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> Ring.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module MoC :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Ciphertext.coq_G t0

    val coq_VG_id : nat -> Ciphertext.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
   end

  module EPC :
   sig
    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_EPC :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF -> Field.coq_F ->
      Commitment.coq_G

    val comEPC :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF t0 ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val comEPCvec :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val com :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_MF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module PC :
   sig
    module AddMLemmas :
     sig
     end

    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_PC :
      Commitment.coq_G -> Commitment.coq_G -> Field.coq_F -> Field.coq_F ->
      Commitment.coq_G

    val comPC :
      nat -> Commitment.coq_G -> Commitment.coq_G -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module MoM :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Message.coq_G t0

    val coq_VG_id : nat -> Message.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Message.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
   end

  module ALVS1 :
   sig
    module AL :
     sig
     end
   end

  module ALVS2 :
   sig
    module AL :
     sig
     end
   end

  module ALVS3 :
   sig
    module AL :
     sig
     end
   end

  module ALenc :
   sig
    module AddVSLemmas :
     sig
      module AL :
       sig
       end
     end

    module Mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module MatG :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Ciphertext.coq_G t0

      val coq_VG_id : nat -> Ciphertext.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_scale_sum : nat -> nat -> nat -> Mat.coq_VF t0 t0 -> Mat.coq_VF t0
     end

    val reenc : Coq_enc.coq_PK -> Ciphertext.coq_G -> Ring.coq_F -> Ciphertext.coq_G

    val bIsReEnc :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Ciphertext.coq_G -> Ring.coq_F -> bool

    val decryptsToExt :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Coq_enc.coq_M -> Ring.coq_F -> bool
   end

  module HardProb :
   sig
    val dLog : (Commitment.coq_G * Commitment.coq_G) -> Field.coq_F -> bool
   end

  module ALR :
   sig
   end

  val coq_ProdOfDiagonals : 'a1 -> ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 t0 t0 -> 'a1 t0

  val coq_ProdOfDiagonalsF : nat -> Field.coq_F t0 t0 -> Field.coq_F t0

  val coq_ProdOfDiagonalsVF : nat -> nat -> Field.coq_F t0 t0 t0 -> Field.coq_F t0 t0

  val coq_ProdOfDiagonalsG : nat -> Commitment.coq_G t0 t0 -> Commitment.coq_G t0

  val coq_RF_inProd : nat -> Mo.Coq_mat.coq_VF -> MoR.coq_VF -> Ring.coq_F

  val coq_RF_VCmult : nat -> Mo.Coq_mat.coq_MF -> MoR.coq_VF -> MoR.coq_VF

  val coq_WeirdCs :
    nat -> nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG

  val coq_EkGeneratorsSub :
    nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG

  val coq_EkGeneratorsSubAlt :
    nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
    MoC.coq_VG

  val coq_EkGenerators :
    Coq_enc.coq_PK -> nat -> Coq_enc.coq_M -> Ciphertext.coq_G t0 t0 ->
    Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0 -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF
    -> Ciphertext.coq_G t0

  val coq_EkGeneratorsSubRawM :
    nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF

  val coq_EkGeneratorsSubRawR :
    nat -> Ring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0

  val coq_EkGeneratorsRawM :
    nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
    Mo.Coq_mat.coq_VF

  val coq_EkGeneratorsRawR :
    nat -> Ring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0 -> MoR.coq_VF

  val makeSVectors : nat -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF t0
 end

module BGZeroArgIns :
 functor (Message:GroupSig) ->
 functor (Ciphertext:GroupSig) ->
 functor (Commitment:GroupSig) ->
 functor (Ring:RingSig) ->
 functor (Field:FieldSig) ->
 functor (VS2:sig
  val op : Commitment.coq_G -> Field.coq_F -> Commitment.coq_G
 end) ->
 functor (VS1:sig
  val op : Ciphertext.coq_G -> Field.coq_F -> Ciphertext.coq_G
 end) ->
 functor (Chal:sig
  type coq_G = Field.coq_F

  val coq_Gdot : Field.coq_F -> Field.coq_F -> Field.coq_F

  val coq_Gone : Field.coq_F

  val coq_Ggen : Field.coq_F

  val coq_Gbool_eq : Field.coq_F -> Field.coq_F -> bool

  val coq_Gdisjoint : Field.coq_F -> Field.coq_F -> bool

  val coq_Ginv : Field.coq_F -> Field.coq_F
 end) ->
 functor (MVS:sig
  val op3 : Ring.coq_F -> Field.coq_F -> Ring.coq_F
 end) ->
 functor (VS3:sig
  val op : Message.coq_G -> Field.coq_F -> Message.coq_G
 end) ->
 functor (Hack:Coq0_Nat) ->
 functor (M:Coq0_Nat) ->
 functor (Coq_enc:sig
  type coq_KGR

  type coq_PK

  type coq_SK

  type coq_M = Message.coq_G

  val coq_Mop : Message.coq_G -> Message.coq_G -> Message.coq_G

  val coq_Mzero : Message.coq_G

  val coq_Mone : Message.coq_G

  val coq_Minv : Message.coq_G -> Message.coq_G

  val coq_Mbool_eq : Message.coq_G -> Message.coq_G -> bool

  val keygen : coq_KGR -> coq_PK * coq_SK

  val keygenMix : coq_KGR -> coq_PK

  val enc : coq_PK -> coq_M -> Ring.coq_F -> Ciphertext.coq_G

  val dec : coq_SK -> Ciphertext.coq_G -> coq_M

  val keymatch : coq_PK -> coq_SK -> bool
 end) ->
 functor (Coq_support:sig
  val n : nat

  val m : nat

  module Mo :
   sig
    module Coq_mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module AL :
     sig
     end

    module FAL :
     sig
      module AL :
       sig
       end
     end

    val coq_VandermondeCol : nat -> Field.coq_F -> Field.coq_F t0

    val coq_VandermondeColGen : nat -> Field.coq_F -> nat -> Field.coq_F t0

    val coq_Vandermonde : nat -> Coq_mat.coq_VF -> Field.coq_F t0 t0

    module SSRfield :
     sig
      module AL :
       sig
       end

      type coq_R = Field.coq_F

      val eqr : coq_R -> coq_R -> bool

      val eqrP : coq_R Equality.axiom

      val coq_R_eqMixin : coq_R Equality.mixin_of

      val coq_R_eqType : Equality.coq_type

      val pickR : coq_R pred0 -> nat -> coq_R option

      val coq_R_choiceMixin : coq_R Choice.mixin_of

      val coq_R_choiceType : Choice.coq_type

      val coq_R_zmodmixin : Field.coq_F GRing.Zmodule.mixin_of

      val coq_R_zmodtype : GRing.Zmodule.coq_type

      val coq_R_comringmixin : GRing.Ring.mixin_of

      val coq_R_ring : GRing.Ring.coq_type

      val coq_R_comring : GRing.ComRing.coq_type

      val coq_Radd_monoid : Field.coq_F Monoid.law

      val coq_Radd_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_monoid : GRing.Zmodule.sort Monoid.law

      val coq_Rmul_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_mul_law : Field.coq_F Monoid.mul_law

      val coq_Radd_add_law : Field.coq_F Monoid.add_law

      val coq_Rinvx : coq_R -> Field.coq_F

      val unit_R : coq_R -> bool

      val coq_R_unitRingMixin : GRing.UnitRing.mixin_of

      val coq_R_unitRing : GRing.UnitRing.coq_type

      val coq_R_comUnitRingType : GRing.ComUnitRing.coq_type

      val coq_R_idomainType : GRing.IntegralDomain.coq_type

      val coq_R_field : GRing.Field.coq_type
     end

    val coq_VandermondeInv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_MF

    val nat_to_ord : nat -> nat -> ordinal

    val coq_VF_inv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_VF
   end

  module MoR :
   sig
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = Ring.coq_F t0

    val coq_VF_zero : nat -> Ring.coq_F t0

    val coq_VF_one : nat -> Ring.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

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

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> Ring.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module MoC :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Ciphertext.coq_G t0

    val coq_VG_id : nat -> Ciphertext.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
   end

  module EPC :
   sig
    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_EPC :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF -> Field.coq_F ->
      Commitment.coq_G

    val comEPC :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF t0 ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val comEPCvec :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val com :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_MF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module PC :
   sig
    module AddMLemmas :
     sig
     end

    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_PC :
      Commitment.coq_G -> Commitment.coq_G -> Field.coq_F -> Field.coq_F ->
      Commitment.coq_G

    val comPC :
      nat -> Commitment.coq_G -> Commitment.coq_G -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module MoM :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Message.coq_G t0

    val coq_VG_id : nat -> Message.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Message.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
   end

  module ALVS1 :
   sig
    module AL :
     sig
     end
   end

  module ALVS2 :
   sig
    module AL :
     sig
     end
   end

  module ALVS3 :
   sig
    module AL :
     sig
     end
   end

  module ALenc :
   sig
    module AddVSLemmas :
     sig
      module AL :
       sig
       end
     end

    module Mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module MatG :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Ciphertext.coq_G t0

      val coq_VG_id : nat -> Ciphertext.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_scale_sum : nat -> nat -> nat -> Mat.coq_VF t0 t0 -> Mat.coq_VF t0
     end

    val reenc : Coq_enc.coq_PK -> Ciphertext.coq_G -> Ring.coq_F -> Ciphertext.coq_G

    val bIsReEnc :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Ciphertext.coq_G -> Ring.coq_F -> bool

    val decryptsToExt :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Coq_enc.coq_M -> Ring.coq_F -> bool
   end

  module HardProb :
   sig
    val dLog : (Commitment.coq_G * Commitment.coq_G) -> Field.coq_F -> bool
   end

  module ALR :
   sig
   end

  val coq_ProdOfDiagonals : 'a1 -> ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 t0 t0 -> 'a1 t0

  val coq_ProdOfDiagonalsF : nat -> Field.coq_F t0 t0 -> Field.coq_F t0

  val coq_ProdOfDiagonalsVF : nat -> nat -> Field.coq_F t0 t0 t0 -> Field.coq_F t0 t0

  val coq_ProdOfDiagonalsG : nat -> Commitment.coq_G t0 t0 -> Commitment.coq_G t0

  val coq_RF_inProd : nat -> Mo.Coq_mat.coq_VF -> MoR.coq_VF -> Ring.coq_F

  val coq_RF_VCmult : nat -> Mo.Coq_mat.coq_MF -> MoR.coq_VF -> MoR.coq_VF

  val coq_WeirdCs :
    nat -> nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG

  val coq_EkGeneratorsSub :
    nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG

  val coq_EkGeneratorsSubAlt :
    nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
    MoC.coq_VG

  val coq_EkGenerators :
    Coq_enc.coq_PK -> nat -> Coq_enc.coq_M -> Ciphertext.coq_G t0 t0 ->
    Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0 -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF
    -> Ciphertext.coq_G t0

  val coq_EkGeneratorsSubRawM :
    nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF

  val coq_EkGeneratorsSubRawR :
    nat -> Ring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0

  val coq_EkGeneratorsRawM :
    nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
    Mo.Coq_mat.coq_VF

  val coq_EkGeneratorsRawR :
    nat -> Ring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0 -> MoR.coq_VF

  val makeSVectors : nat -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF t0
 end) ->
 sig
  val n : nat

  val m : nat

  module ALR :
   sig
   end

  val coq_BM :
    Field.coq_F -> Coq_support.Mo.Coq_mat.coq_VF -> Coq_support.Mo.Coq_mat.coq_VF ->
    Field.coq_F

  type coq_St =
    (((Commitment.coq_G * Coq_support.EPC.MoM.coq_VG) * Field.coq_F) * Coq_support.EPC.MoM.coq_VG) * Coq_support.EPC.MoM.coq_VG

  type coq_W =
    ((Coq_support.Mo.Coq_mat.coq_VF
    t0 * Coq_support.Mo.Coq_mat.coq_VF) * Coq_support.Mo.Coq_mat.coq_VF
    t0) * Coq_support.Mo.Coq_mat.coq_VF

  type coq_R =
    (((Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F) * (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF)

  type coq_C = (Commitment.coq_G * Commitment.coq_G) * Coq_support.EPC.MoM.coq_VG

  type coq_T =
    (((Coq_support.Mo.Coq_mat.coq_VF * Field.coq_F) * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  type coq_X = Coq_support.Mo.Coq_mat.coq_VF

  type coq_TE =
    ((((Coq_support.Mo.Coq_mat.coq_VF * Field.coq_F) * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F) * (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF)

  val coq_Rel : coq_St -> coq_W -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_V0 : (coq_St * coq_C) -> Field.coq_F -> (coq_St * coq_C) * Field.coq_F

  val coq_P1 :
    ((coq_St * coq_C) * Field.coq_F) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * Field.coq_F) * coq_T

  val coq_V1 : (((coq_St * coq_C) * Field.coq_F) * coq_T) -> bool

  val simMap : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_TE -> coq_R

  val simulator :
    coq_St -> coq_TE -> Field.coq_F -> ((coq_St * coq_C) * Field.coq_F) * coq_T

  val extractor : coq_T t0 -> Field.coq_F t0 -> coq_W

  val coq_M : nat

  val allDifferent : Chal.coq_G t0 -> bool
 end

module type SigmaPlus5 =
 sig
  type coq_E0

  type coq_E1

  type coq_St

  type coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C0

  type coq_C1

  type coq_R0

  type coq_R1

  val add0 : coq_E0 -> coq_E0 -> coq_E0

  val zero0 : coq_E0

  val inv0 : coq_E0 -> coq_E0

  val bool_eq0 : coq_E0 -> coq_E0 -> bool

  val disjoint0 : coq_E0 -> coq_E0 -> bool

  val add1 : coq_E1 -> coq_E1 -> coq_E1

  val zero1 : coq_E1

  val inv1 : coq_E1 -> coq_E1

  val bool_eq1 : coq_E1 -> coq_E1 -> bool

  val disjoint1 : coq_E1 -> coq_E1 -> bool

  type coq_T

  val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0

  val coq_P1 :
    ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
    ((coq_St * coq_C0) * coq_E0) * coq_C1

  val coq_P2 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) -> coq_W
    -> ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val coq_V2 : (((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T) -> bool

  type coq_TE0

  type coq_TE1

  type coq_X

  val simulator :
    coq_St -> (coq_TE0 * coq_TE1) -> (coq_E0 * coq_E1) ->
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val simMap :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_R0 * coq_R1) ->
    coq_TE0 * coq_TE1

  val simMapInv :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_TE0 * coq_TE1) ->
    coq_R0 * coq_R1

  val coq_M0 : nat

  val coq_M1 : nat

  val extractor : coq_T t0 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_W

  val allValid :
    coq_St -> coq_C0 -> coq_C1 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_T t0 t0 -> bool
 end

module SigmaPlus5CompIns :
 functor (E:GroupSig) ->
 functor (Coq_sig:sig
  type coq_St

  type coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C

  type coq_R

  type coq_T

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_P1 :
    ((coq_St * coq_C) * E.coq_G) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * E.coq_G) * coq_T

  val coq_V1 : (((coq_St * coq_C) * E.coq_G) * coq_T) -> bool

  type coq_TE

  type coq_X

  val simulator : coq_St -> coq_TE -> E.coq_G -> ((coq_St * coq_C) * E.coq_G) * coq_T

  val simMap : coq_St -> coq_W -> E.coq_G -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> E.coq_G -> coq_X -> coq_TE -> coq_R

  val coq_M : nat

  val extractor : coq_T t0 -> E.coq_G t0 -> coq_W

  val allDifferent : E.coq_G t0 -> bool
 end) ->
 functor (Coq_exp:sig
  type coq_E

  type coq_St

  type coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C

  type coq_R

  val add : coq_E -> coq_E -> coq_E

  val zero : coq_E

  val inv : coq_E -> coq_E

  val bool_eq : coq_E -> coq_E -> bool

  val disjoint : coq_E -> coq_E -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  type coq_C1

  type coq_R1

  val coq_P1 :
    ((coq_St * coq_C) * coq_E) -> coq_R1 -> coq_W ->
    ((coq_St * coq_C) * coq_E) * coq_C1

  val coq_ToSt : (((coq_St * coq_C) * coq_E) * coq_C1) -> Coq_sig.coq_St

  val coq_ToWit :
    ((coq_St * coq_C) * coq_E) -> coq_R -> coq_R1 -> coq_W -> Coq_sig.coq_W

  type coq_TE

  val coq_M : nat

  val extractor : Coq_sig.coq_W t0 -> coq_E t0 -> coq_W

  type coq_X

  val simulator : coq_St -> coq_TE -> coq_E -> coq_C * coq_C1

  val simMap : coq_St -> coq_W -> coq_E -> coq_X -> (coq_R * coq_R1) -> coq_TE

  val simMapInv : coq_St -> coq_W -> coq_E -> coq_X -> coq_TE -> coq_R * coq_R1

  val sigXcomp : coq_St -> coq_X -> Coq_sig.coq_X
 end) ->
 sig
  type coq_E0 = Coq_exp.coq_E

  type coq_E1 = E.coq_G

  type coq_St = Coq_exp.coq_St

  type coq_W = Coq_exp.coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C0 = Coq_exp.coq_C

  type coq_C1 = Coq_exp.coq_C1 * Coq_sig.coq_C

  type coq_R0 = Coq_exp.coq_R

  type coq_R1 = Coq_exp.coq_R1 * Coq_sig.coq_R

  val add0 : coq_E0 -> coq_E0 -> coq_E0

  val zero0 : coq_E0

  val inv0 : coq_E0 -> coq_E0

  val bool_eq0 : coq_E0 -> coq_E0 -> bool

  val disjoint0 : coq_E0 -> coq_E0 -> bool

  val add1 : coq_E1 -> coq_E1 -> coq_E1

  val zero1 : coq_E1

  val inv1 : coq_E1 -> coq_E1

  val bool_eq1 : coq_E1 -> coq_E1 -> bool

  val disjoint1 : coq_E1 -> coq_E1 -> bool

  type coq_T = Coq_sig.coq_T

  val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0

  val coq_P1 :
    ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
    ((coq_St * coq_C0) * coq_E0) * coq_C1

  val coq_P2 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) -> coq_W
    -> ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val coq_V2 : (((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T) -> bool

  type coq_TE0 = Coq_exp.coq_TE

  type coq_TE1 = Coq_sig.coq_TE

  type coq_X = Coq_exp.coq_X

  val simulator :
    coq_St -> (coq_TE0 * coq_TE1) -> (coq_E0 * coq_E1) ->
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val simMap :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_R0 * coq_R1) ->
    coq_TE0 * coq_TE1

  val simMapInv :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_TE0 * coq_TE1) ->
    coq_R0 * coq_R1

  val coq_M0 : nat

  val coq_M1 : nat

  val extractor : coq_T t0 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_W

  val allValid :
    coq_St -> coq_C0 -> coq_C1 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_T t0 t0 -> bool
 end

module SigmaPlusTo5simTofullIns :
 functor (E0:GroupSig) ->
 functor (Coq_sig:sig
  type coq_St

  type coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C

  type coq_R

  type coq_T

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_P1 :
    ((coq_St * coq_C) * E0.coq_G) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * E0.coq_G) * coq_T

  val coq_V1 : (((coq_St * coq_C) * E0.coq_G) * coq_T) -> bool

  type coq_TE

  type coq_X

  val simulator :
    coq_St -> coq_TE -> E0.coq_G -> ((coq_St * coq_C) * E0.coq_G) * coq_T

  val simMap : coq_St -> coq_W -> E0.coq_G -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> E0.coq_G -> coq_X -> coq_TE -> coq_R

  val coq_M : nat

  val extractor : coq_T t0 -> E0.coq_G t0 -> coq_W

  val allDifferent : E0.coq_G t0 -> bool
 end) ->
 functor (Coq_sigSim:sig
  type coq_E

  type coq_St

  type coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C

  type coq_R

  val add : coq_E -> coq_E -> coq_E

  val zero : coq_E

  val inv : coq_E -> coq_E

  val bool_eq : coq_E -> coq_E -> bool

  val disjoint : coq_E -> coq_E -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_ToSt : ((coq_St * coq_C) * coq_E) -> Coq_sig.coq_St

  val coq_ToWit : ((coq_St * coq_C) * coq_E) -> coq_R -> coq_W -> Coq_sig.coq_W

  type coq_TE

  val extractor : Coq_sig.coq_W -> coq_E -> coq_W

  type coq_X

  val simulator : coq_St -> coq_TE -> coq_E -> coq_C

  val simMap : coq_St -> coq_W -> coq_E -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> coq_E -> coq_X -> coq_TE -> coq_R

  val sigXcomp : coq_St -> coq_X -> Coq_sig.coq_X
 end) ->
 sig
  type coq_E = Coq_sigSim.coq_E

  type coq_St = Coq_sigSim.coq_St

  type coq_W = Coq_sigSim.coq_W

  val coq_Rel : Coq_sigSim.coq_St -> Coq_sigSim.coq_W -> bool

  type coq_C = Coq_sigSim.coq_C

  type coq_R = Coq_sigSim.coq_R

  val add : Coq_sigSim.coq_E -> Coq_sigSim.coq_E -> Coq_sigSim.coq_E

  val zero : coq_E

  val inv : coq_E -> coq_E

  val bool_eq : coq_E -> coq_E -> bool

  val disjoint : coq_E -> coq_E -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  type coq_C1 = unit

  type coq_R1 = unit

  val coq_P1 :
    ((coq_St * coq_C) * coq_E) -> coq_R1 -> coq_W ->
    ((coq_St * coq_C) * coq_E) * coq_C1

  val coq_ToSt : (((coq_St * coq_C) * coq_E) * coq_C1) -> Coq_sig.coq_St

  val coq_ToWit :
    ((coq_St * coq_C) * coq_E) -> coq_R -> coq_R1 -> coq_W -> Coq_sig.coq_W

  type coq_TE = Coq_sigSim.coq_TE

  val coq_M : nat

  val extractor : Coq_sig.coq_W t0 -> coq_E t0 -> coq_W

  type coq_X = Coq_sigSim.coq_X

  val simulator : coq_St -> coq_TE -> coq_E -> coq_C * coq_C1

  val simMap : coq_St -> coq_W -> coq_E -> coq_X -> (coq_R * coq_R1) -> coq_TE

  val simMapInv : coq_St -> coq_W -> coq_E -> coq_X -> coq_TE -> coq_R * coq_R1

  val sigXcomp : coq_St -> coq_X -> Coq_sig.coq_X
 end

module SigmaPlus5to5CompIns :
 functor (E:GroupSig) ->
 functor (Coq_sig:sig
  type coq_St

  type coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C

  type coq_R

  type coq_T

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_P1 :
    ((coq_St * coq_C) * E.coq_G) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * E.coq_G) * coq_T

  val coq_V1 : (((coq_St * coq_C) * E.coq_G) * coq_T) -> bool

  type coq_TE

  type coq_X

  val simulator : coq_St -> coq_TE -> E.coq_G -> ((coq_St * coq_C) * E.coq_G) * coq_T

  val simMap : coq_St -> coq_W -> E.coq_G -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> E.coq_G -> coq_X -> coq_TE -> coq_R

  val coq_M : nat

  val extractor : coq_T t0 -> E.coq_G t0 -> coq_W

  val allDifferent : E.coq_G t0 -> bool
 end) ->
 functor (Coq_sig5:SigmaPlus5) ->
 functor (Coq_exp:sig
  type coq_St

  type coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C

  type coq_R

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_ToStSig : (coq_St * coq_C) -> Coq_sig.coq_St

  val coq_ToWitSig : (coq_St * coq_C) -> coq_R -> coq_W -> Coq_sig.coq_W

  val coq_ToStSig5 : (coq_St * coq_C) -> Coq_sig5.coq_St

  val coq_ToWitSig5 : (coq_St * coq_C) -> coq_R -> coq_W -> Coq_sig5.coq_W

  type coq_TE

  val extractor : Coq_sig5.coq_W -> Coq_sig.coq_W -> coq_W

  type coq_X

  val simulator : coq_St -> coq_TE -> coq_C

  val simMap : coq_St -> coq_W -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> coq_X -> coq_TE -> coq_R

  val sigXcomp : coq_St -> coq_X -> Coq_sig.coq_X

  val sig5Xcomp : coq_St -> coq_X -> Coq_sig5.coq_X
 end) ->
 sig
  type coq_E0 = Coq_sig5.coq_E0 * E.coq_G

  type coq_E1 = Coq_sig5.coq_E1

  type coq_St = Coq_exp.coq_St

  type coq_W = Coq_exp.coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C0 = (Coq_exp.coq_C * Coq_sig5.coq_C0) * Coq_sig.coq_C

  type coq_C1 = Coq_sig5.coq_C1

  type coq_R0 = (Coq_exp.coq_R * Coq_sig5.coq_R0) * Coq_sig.coq_R

  type coq_R1 = Coq_sig5.coq_R1

  val add0 : coq_E0 -> coq_E0 -> coq_E0

  val zero0 : coq_E0

  val inv0 : coq_E0 -> coq_E0

  val bool_eq0 : coq_E0 -> coq_E0 -> bool

  val disjoint0 : coq_E0 -> coq_E0 -> bool

  val add1 : coq_E1 -> coq_E1 -> coq_E1

  val zero1 : coq_E1

  val inv1 : coq_E1 -> coq_E1

  val bool_eq1 : coq_E1 -> coq_E1 -> bool

  val disjoint1 : coq_E1 -> coq_E1 -> bool

  type coq_T = Coq_sig5.coq_T * Coq_sig.coq_T

  val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0

  val coq_P1 :
    ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
    ((coq_St * coq_C0) * coq_E0) * coq_C1

  val coq_P2 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) -> coq_W
    -> ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val coq_V2 : (((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T) -> bool

  type coq_TE0 = (Coq_exp.coq_TE * Coq_sig5.coq_TE0) * Coq_sig.coq_TE

  type coq_TE1 = Coq_sig5.coq_TE1

  type coq_X = Coq_exp.coq_X

  val simulator :
    coq_St -> (coq_TE0 * coq_TE1) -> (coq_E0 * coq_E1) ->
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val simMap :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_R0 * coq_R1) ->
    coq_TE0 * coq_TE1

  val simMapInv :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_TE0 * coq_TE1) ->
    coq_R0 * coq_R1

  val coq_M0 : nat

  val coq_M1 : nat

  val extractor : coq_T t0 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_W

  val allValid :
    coq_St -> coq_C0 -> coq_C1 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_T t0 t0 -> bool
 end

module BGHadProdIns :
 functor (Message:GroupSig) ->
 functor (Ciphertext:GroupSig) ->
 functor (Commitment:GroupSig) ->
 functor (Ring:RingSig) ->
 functor (Field:FieldSig) ->
 functor (VS2:sig
  val op : Commitment.coq_G -> Field.coq_F -> Commitment.coq_G
 end) ->
 functor (VS1:sig
  val op : Ciphertext.coq_G -> Field.coq_F -> Ciphertext.coq_G
 end) ->
 functor (Chal:sig
  type coq_G = Field.coq_F

  val coq_Gdot : Field.coq_F -> Field.coq_F -> Field.coq_F

  val coq_Gone : Field.coq_F

  val coq_Ggen : Field.coq_F

  val coq_Gbool_eq : Field.coq_F -> Field.coq_F -> bool

  val coq_Gdisjoint : Field.coq_F -> Field.coq_F -> bool

  val coq_Ginv : Field.coq_F -> Field.coq_F
 end) ->
 functor (MVS:sig
  val op3 : Ring.coq_F -> Field.coq_F -> Ring.coq_F
 end) ->
 functor (VS3:sig
  val op : Message.coq_G -> Field.coq_F -> Message.coq_G
 end) ->
 functor (Hack:Coq0_Nat) ->
 functor (M:Coq0_Nat) ->
 functor (Coq_enc:sig
  type coq_KGR

  type coq_PK

  type coq_SK

  type coq_M = Message.coq_G

  val coq_Mop : Message.coq_G -> Message.coq_G -> Message.coq_G

  val coq_Mzero : Message.coq_G

  val coq_Mone : Message.coq_G

  val coq_Minv : Message.coq_G -> Message.coq_G

  val coq_Mbool_eq : Message.coq_G -> Message.coq_G -> bool

  val keygen : coq_KGR -> coq_PK * coq_SK

  val keygenMix : coq_KGR -> coq_PK

  val enc : coq_PK -> coq_M -> Ring.coq_F -> Ciphertext.coq_G

  val dec : coq_SK -> Ciphertext.coq_G -> coq_M

  val keymatch : coq_PK -> coq_SK -> bool
 end) ->
 functor (Coq_support:sig
  val n : nat

  val m : nat

  module Mo :
   sig
    module Coq_mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module AL :
     sig
     end

    module FAL :
     sig
      module AL :
       sig
       end
     end

    val coq_VandermondeCol : nat -> Field.coq_F -> Field.coq_F t0

    val coq_VandermondeColGen : nat -> Field.coq_F -> nat -> Field.coq_F t0

    val coq_Vandermonde : nat -> Coq_mat.coq_VF -> Field.coq_F t0 t0

    module SSRfield :
     sig
      module AL :
       sig
       end

      type coq_R = Field.coq_F

      val eqr : coq_R -> coq_R -> bool

      val eqrP : coq_R Equality.axiom

      val coq_R_eqMixin : coq_R Equality.mixin_of

      val coq_R_eqType : Equality.coq_type

      val pickR : coq_R pred0 -> nat -> coq_R option

      val coq_R_choiceMixin : coq_R Choice.mixin_of

      val coq_R_choiceType : Choice.coq_type

      val coq_R_zmodmixin : Field.coq_F GRing.Zmodule.mixin_of

      val coq_R_zmodtype : GRing.Zmodule.coq_type

      val coq_R_comringmixin : GRing.Ring.mixin_of

      val coq_R_ring : GRing.Ring.coq_type

      val coq_R_comring : GRing.ComRing.coq_type

      val coq_Radd_monoid : Field.coq_F Monoid.law

      val coq_Radd_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_monoid : GRing.Zmodule.sort Monoid.law

      val coq_Rmul_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_mul_law : Field.coq_F Monoid.mul_law

      val coq_Radd_add_law : Field.coq_F Monoid.add_law

      val coq_Rinvx : coq_R -> Field.coq_F

      val unit_R : coq_R -> bool

      val coq_R_unitRingMixin : GRing.UnitRing.mixin_of

      val coq_R_unitRing : GRing.UnitRing.coq_type

      val coq_R_comUnitRingType : GRing.ComUnitRing.coq_type

      val coq_R_idomainType : GRing.IntegralDomain.coq_type

      val coq_R_field : GRing.Field.coq_type
     end

    val coq_VandermondeInv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_MF

    val nat_to_ord : nat -> nat -> ordinal

    val coq_VF_inv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_VF
   end

  module MoR :
   sig
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = Ring.coq_F t0

    val coq_VF_zero : nat -> Ring.coq_F t0

    val coq_VF_one : nat -> Ring.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

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

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> Ring.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module MoC :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Ciphertext.coq_G t0

    val coq_VG_id : nat -> Ciphertext.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
   end

  module EPC :
   sig
    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_EPC :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF -> Field.coq_F ->
      Commitment.coq_G

    val comEPC :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF t0 ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val comEPCvec :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val com :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_MF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module PC :
   sig
    module AddMLemmas :
     sig
     end

    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_PC :
      Commitment.coq_G -> Commitment.coq_G -> Field.coq_F -> Field.coq_F ->
      Commitment.coq_G

    val comPC :
      nat -> Commitment.coq_G -> Commitment.coq_G -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module MoM :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Message.coq_G t0

    val coq_VG_id : nat -> Message.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Message.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
   end

  module ALVS1 :
   sig
    module AL :
     sig
     end
   end

  module ALVS2 :
   sig
    module AL :
     sig
     end
   end

  module ALVS3 :
   sig
    module AL :
     sig
     end
   end

  module ALenc :
   sig
    module AddVSLemmas :
     sig
      module AL :
       sig
       end
     end

    module Mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module MatG :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Ciphertext.coq_G t0

      val coq_VG_id : nat -> Ciphertext.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_scale_sum : nat -> nat -> nat -> Mat.coq_VF t0 t0 -> Mat.coq_VF t0
     end

    val reenc : Coq_enc.coq_PK -> Ciphertext.coq_G -> Ring.coq_F -> Ciphertext.coq_G

    val bIsReEnc :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Ciphertext.coq_G -> Ring.coq_F -> bool

    val decryptsToExt :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Coq_enc.coq_M -> Ring.coq_F -> bool
   end

  module HardProb :
   sig
    val dLog : (Commitment.coq_G * Commitment.coq_G) -> Field.coq_F -> bool
   end

  module ALR :
   sig
   end

  val coq_ProdOfDiagonals : 'a1 -> ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 t0 t0 -> 'a1 t0

  val coq_ProdOfDiagonalsF : nat -> Field.coq_F t0 t0 -> Field.coq_F t0

  val coq_ProdOfDiagonalsVF : nat -> nat -> Field.coq_F t0 t0 t0 -> Field.coq_F t0 t0

  val coq_ProdOfDiagonalsG : nat -> Commitment.coq_G t0 t0 -> Commitment.coq_G t0

  val coq_RF_inProd : nat -> Mo.Coq_mat.coq_VF -> MoR.coq_VF -> Ring.coq_F

  val coq_RF_VCmult : nat -> Mo.Coq_mat.coq_MF -> MoR.coq_VF -> MoR.coq_VF

  val coq_WeirdCs :
    nat -> nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG

  val coq_EkGeneratorsSub :
    nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG

  val coq_EkGeneratorsSubAlt :
    nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
    MoC.coq_VG

  val coq_EkGenerators :
    Coq_enc.coq_PK -> nat -> Coq_enc.coq_M -> Ciphertext.coq_G t0 t0 ->
    Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0 -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF
    -> Ciphertext.coq_G t0

  val coq_EkGeneratorsSubRawM :
    nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF

  val coq_EkGeneratorsSubRawR :
    nat -> Ring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0

  val coq_EkGeneratorsRawM :
    nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
    Mo.Coq_mat.coq_VF

  val coq_EkGeneratorsRawR :
    nat -> Ring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0 -> MoR.coq_VF

  val makeSVectors : nat -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF t0
 end) ->
 functor (Coq_sig:sig
  val n : nat

  val m : nat

  module ALR :
   sig
   end

  val coq_BM :
    Field.coq_F -> Coq_support.Mo.Coq_mat.coq_VF -> Coq_support.Mo.Coq_mat.coq_VF ->
    Field.coq_F

  type coq_St =
    (((Commitment.coq_G * Coq_support.EPC.MoM.coq_VG) * Field.coq_F) * Coq_support.EPC.MoM.coq_VG) * Coq_support.EPC.MoM.coq_VG

  type coq_W =
    ((Coq_support.Mo.Coq_mat.coq_VF
    t0 * Coq_support.Mo.Coq_mat.coq_VF) * Coq_support.Mo.Coq_mat.coq_VF
    t0) * Coq_support.Mo.Coq_mat.coq_VF

  type coq_R =
    (((Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F) * (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF)

  type coq_C = (Commitment.coq_G * Commitment.coq_G) * Coq_support.EPC.MoM.coq_VG

  type coq_T =
    (((Coq_support.Mo.Coq_mat.coq_VF * Field.coq_F) * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  type coq_X = Coq_support.Mo.Coq_mat.coq_VF

  type coq_TE =
    ((((Coq_support.Mo.Coq_mat.coq_VF * Field.coq_F) * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F) * (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF)

  val coq_Rel : coq_St -> coq_W -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_V0 : (coq_St * coq_C) -> Field.coq_F -> (coq_St * coq_C) * Field.coq_F

  val coq_P1 :
    ((coq_St * coq_C) * Field.coq_F) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * Field.coq_F) * coq_T

  val coq_V1 : (((coq_St * coq_C) * Field.coq_F) * coq_T) -> bool

  val simMap : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_TE -> coq_R

  val simulator :
    coq_St -> coq_TE -> Field.coq_F -> ((coq_St * coq_C) * Field.coq_F) * coq_T

  val extractor : coq_T t0 -> Field.coq_F t0 -> coq_W

  val coq_M : nat

  val allDifferent : Chal.coq_G t0 -> bool
 end) ->
 sig
  val n : nat

  val m : nat

  module ALR :
   sig
   end

  module G2 :
   sig
    type coq_G = Field.coq_F

    val coq_Gdot : coq_G -> coq_G -> coq_G

    val coq_Gone : coq_G

    val coq_Ggen : coq_G

    val coq_Gbool_eq : coq_G -> coq_G -> bool

    val coq_Gdisjoint : coq_G -> coq_G -> bool

    val coq_Ginv : coq_G -> coq_G
   end

  type coq_E = G2.coq_G * Field.coq_F

  type coq_St =
    ((Commitment.coq_G * Coq_support.EPC.MoM.coq_VG) * Coq_support.EPC.MoM.coq_VG) * Commitment.coq_G

  type coq_W =
    ((Coq_support.Mo.Coq_mat.coq_VF
    t0 * Coq_support.Mo.Coq_mat.coq_VF) * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C = Coq_support.EPC.MoM.coq_VG

  type coq_R = Coq_support.Mo.Coq_mat.coq_VF

  val add : coq_E -> coq_E -> G2.coq_G * Field.coq_F

  val zero : G2.coq_G * Field.coq_F

  val inv : coq_E -> G2.coq_G * Field.coq_F

  val bool_eq : coq_E -> coq_E -> bool

  val disjoint : coq_E -> coq_E -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_ToSt : ((coq_St * coq_C) * coq_E) -> Coq_sig.coq_St

  val coq_ToWit : ((coq_St * coq_C) * coq_E) -> coq_R -> coq_W -> Coq_sig.coq_W

  type coq_TE = Coq_support.Mo.Coq_mat.coq_VF

  val extractor : Coq_sig.coq_W -> coq_E -> coq_W

  type coq_X = Coq_sig.coq_X

  val simulator : coq_St -> coq_TE -> coq_E -> coq_C

  val simMap : coq_St -> coq_W -> coq_E -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> coq_E -> coq_X -> coq_TE -> coq_R

  val sigXcomp : coq_St -> coq_X -> Coq_sig.coq_X
 end

module BGSingleProdIns :
 functor (Commitment:GroupSig) ->
 functor (Field:FieldSig) ->
 functor (VS2:sig
  val op : Commitment.coq_G -> Field.coq_F -> Commitment.coq_G
 end) ->
 functor (Chal:sig
  type coq_G = Field.coq_F

  val coq_Gdot : Field.coq_F -> Field.coq_F -> Field.coq_F

  val coq_Gone : Field.coq_F

  val coq_Ggen : Field.coq_F

  val coq_Gbool_eq : Field.coq_F -> Field.coq_F -> bool

  val coq_Gdisjoint : Field.coq_F -> Field.coq_F -> bool

  val coq_Ginv : Field.coq_F -> Field.coq_F
 end) ->
 functor (Hack:Coq0_Nat) ->
 sig
  val n : nat

  module Mo :
   sig
    module Coq_mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module AL :
     sig
     end

    module FAL :
     sig
      module AL :
       sig
       end
     end

    val coq_VandermondeCol : nat -> Field.coq_F -> Field.coq_F t0

    val coq_VandermondeColGen : nat -> Field.coq_F -> nat -> Field.coq_F t0

    val coq_Vandermonde : nat -> Coq_mat.coq_VF -> Field.coq_F t0 t0

    module SSRfield :
     sig
      module AL :
       sig
       end

      type coq_R = Field.coq_F

      val eqr : coq_R -> coq_R -> bool

      val eqrP : coq_R Equality.axiom

      val coq_R_eqMixin : coq_R Equality.mixin_of

      val coq_R_eqType : Equality.coq_type

      val pickR : coq_R pred0 -> nat -> coq_R option

      val coq_R_choiceMixin : coq_R Choice.mixin_of

      val coq_R_choiceType : Choice.coq_type

      val coq_R_zmodmixin : Field.coq_F GRing.Zmodule.mixin_of

      val coq_R_zmodtype : GRing.Zmodule.coq_type

      val coq_R_comringmixin : GRing.Ring.mixin_of

      val coq_R_ring : GRing.Ring.coq_type

      val coq_R_comring : GRing.ComRing.coq_type

      val coq_Radd_monoid : Field.coq_F Monoid.law

      val coq_Radd_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_monoid : GRing.Zmodule.sort Monoid.law

      val coq_Rmul_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_mul_law : Field.coq_F Monoid.mul_law

      val coq_Radd_add_law : Field.coq_F Monoid.add_law

      val coq_Rinvx : coq_R -> Field.coq_F

      val unit_R : coq_R -> bool

      val coq_R_unitRingMixin : GRing.UnitRing.mixin_of

      val coq_R_unitRing : GRing.UnitRing.coq_type

      val coq_R_comUnitRingType : GRing.ComUnitRing.coq_type

      val coq_R_idomainType : GRing.IntegralDomain.coq_type

      val coq_R_field : GRing.Field.coq_type
     end

    val coq_VandermondeInv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_MF

    val nat_to_ord : nat -> nat -> ordinal

    val coq_VF_inv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_VF
   end

  module EPC :
   sig
    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_EPC :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF -> Field.coq_F ->
      Commitment.coq_G

    val comEPC :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF t0 ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val comEPCvec :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val com :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_MF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module PC :
   sig
    module AddMLemmas :
     sig
     end

    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_PC :
      Commitment.coq_G -> Commitment.coq_G -> Field.coq_F -> Field.coq_F ->
      Commitment.coq_G

    val comPC :
      nat -> Commitment.coq_G -> Commitment.coq_G -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module HardProb :
   sig
    val dLog : (Commitment.coq_G * Commitment.coq_G) -> Field.coq_F -> bool
   end

  module RAL :
   sig
   end

  type coq_St =
    ((Commitment.coq_G * EPC.MoM.coq_VG) * Commitment.coq_G) * Field.coq_F

  type coq_W = Mo.Coq_mat.coq_VF * Field.coq_F

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C = (Commitment.coq_G * Commitment.coq_G) * Commitment.coq_G

  type coq_R =
    (((Mo.Coq_mat.coq_VF * Field.coq_F) * Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  type coq_T = ((Mo.Coq_mat.coq_VF * Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  val vecb : Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_P1 :
    ((coq_St * coq_C) * Field.coq_F) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * Field.coq_F) * coq_T

  val coq_V1 : (((coq_St * coq_C) * Field.coq_F) * coq_T) -> bool

  type coq_TE =
    (((Mo.Coq_mat.coq_VF * Field.coq_F) * Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  type coq_X = Mo.Coq_mat.coq_VF

  val simulator :
    coq_St -> coq_TE -> Field.coq_F -> ((coq_St * coq_C) * Field.coq_F) * coq_T

  val simMap : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_TE -> coq_R

  val coq_M : nat

  val extractor : coq_T t0 -> Field.coq_F t0 -> coq_W

  val coq_Polynomial :
    nat -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF -> Field.coq_F ->
    Mo.Coq_mat.coq_VF -> Field.coq_F

  val allDifferent : Field.coq_F t0 -> bool
 end

module ProdArgIns :
 functor (Message:GroupSig) ->
 functor (Ciphertext:GroupSig) ->
 functor (Commitment:GroupSig) ->
 functor (Ring:RingSig) ->
 functor (Field:FieldSig) ->
 functor (VS2:sig
  val op : Commitment.coq_G -> Field.coq_F -> Commitment.coq_G
 end) ->
 functor (VS1:sig
  val op : Ciphertext.coq_G -> Field.coq_F -> Ciphertext.coq_G
 end) ->
 functor (Chal:sig
  type coq_G = Field.coq_F

  val coq_Gdot : Field.coq_F -> Field.coq_F -> Field.coq_F

  val coq_Gone : Field.coq_F

  val coq_Ggen : Field.coq_F

  val coq_Gbool_eq : Field.coq_F -> Field.coq_F -> bool

  val coq_Gdisjoint : Field.coq_F -> Field.coq_F -> bool

  val coq_Ginv : Field.coq_F -> Field.coq_F
 end) ->
 functor (MVS:sig
  val op3 : Ring.coq_F -> Field.coq_F -> Ring.coq_F
 end) ->
 functor (VS3:sig
  val op : Message.coq_G -> Field.coq_F -> Message.coq_G
 end) ->
 functor (Hack:Coq0_Nat) ->
 functor (M:Coq0_Nat) ->
 functor (Coq_enc:sig
  type coq_KGR

  type coq_PK

  type coq_SK

  type coq_M = Message.coq_G

  val coq_Mop : Message.coq_G -> Message.coq_G -> Message.coq_G

  val coq_Mzero : Message.coq_G

  val coq_Mone : Message.coq_G

  val coq_Minv : Message.coq_G -> Message.coq_G

  val coq_Mbool_eq : Message.coq_G -> Message.coq_G -> bool

  val keygen : coq_KGR -> coq_PK * coq_SK

  val keygenMix : coq_KGR -> coq_PK

  val enc : coq_PK -> coq_M -> Ring.coq_F -> Ciphertext.coq_G

  val dec : coq_SK -> Ciphertext.coq_G -> coq_M

  val keymatch : coq_PK -> coq_SK -> bool
 end) ->
 functor (Coq_support:sig
  val n : nat

  val m : nat

  module Mo :
   sig
    module Coq_mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module AL :
     sig
     end

    module FAL :
     sig
      module AL :
       sig
       end
     end

    val coq_VandermondeCol : nat -> Field.coq_F -> Field.coq_F t0

    val coq_VandermondeColGen : nat -> Field.coq_F -> nat -> Field.coq_F t0

    val coq_Vandermonde : nat -> Coq_mat.coq_VF -> Field.coq_F t0 t0

    module SSRfield :
     sig
      module AL :
       sig
       end

      type coq_R = Field.coq_F

      val eqr : coq_R -> coq_R -> bool

      val eqrP : coq_R Equality.axiom

      val coq_R_eqMixin : coq_R Equality.mixin_of

      val coq_R_eqType : Equality.coq_type

      val pickR : coq_R pred0 -> nat -> coq_R option

      val coq_R_choiceMixin : coq_R Choice.mixin_of

      val coq_R_choiceType : Choice.coq_type

      val coq_R_zmodmixin : Field.coq_F GRing.Zmodule.mixin_of

      val coq_R_zmodtype : GRing.Zmodule.coq_type

      val coq_R_comringmixin : GRing.Ring.mixin_of

      val coq_R_ring : GRing.Ring.coq_type

      val coq_R_comring : GRing.ComRing.coq_type

      val coq_Radd_monoid : Field.coq_F Monoid.law

      val coq_Radd_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_monoid : GRing.Zmodule.sort Monoid.law

      val coq_Rmul_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_mul_law : Field.coq_F Monoid.mul_law

      val coq_Radd_add_law : Field.coq_F Monoid.add_law

      val coq_Rinvx : coq_R -> Field.coq_F

      val unit_R : coq_R -> bool

      val coq_R_unitRingMixin : GRing.UnitRing.mixin_of

      val coq_R_unitRing : GRing.UnitRing.coq_type

      val coq_R_comUnitRingType : GRing.ComUnitRing.coq_type

      val coq_R_idomainType : GRing.IntegralDomain.coq_type

      val coq_R_field : GRing.Field.coq_type
     end

    val coq_VandermondeInv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_MF

    val nat_to_ord : nat -> nat -> ordinal

    val coq_VF_inv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_VF
   end

  module MoR :
   sig
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = Ring.coq_F t0

    val coq_VF_zero : nat -> Ring.coq_F t0

    val coq_VF_one : nat -> Ring.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

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

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> Ring.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module MoC :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Ciphertext.coq_G t0

    val coq_VG_id : nat -> Ciphertext.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
   end

  module EPC :
   sig
    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_EPC :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF -> Field.coq_F ->
      Commitment.coq_G

    val comEPC :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF t0 ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val comEPCvec :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val com :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_MF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module PC :
   sig
    module AddMLemmas :
     sig
     end

    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_PC :
      Commitment.coq_G -> Commitment.coq_G -> Field.coq_F -> Field.coq_F ->
      Commitment.coq_G

    val comPC :
      nat -> Commitment.coq_G -> Commitment.coq_G -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module MoM :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Message.coq_G t0

    val coq_VG_id : nat -> Message.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Message.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
   end

  module ALVS1 :
   sig
    module AL :
     sig
     end
   end

  module ALVS2 :
   sig
    module AL :
     sig
     end
   end

  module ALVS3 :
   sig
    module AL :
     sig
     end
   end

  module ALenc :
   sig
    module AddVSLemmas :
     sig
      module AL :
       sig
       end
     end

    module Mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module MatG :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Ciphertext.coq_G t0

      val coq_VG_id : nat -> Ciphertext.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_scale_sum : nat -> nat -> nat -> Mat.coq_VF t0 t0 -> Mat.coq_VF t0
     end

    val reenc : Coq_enc.coq_PK -> Ciphertext.coq_G -> Ring.coq_F -> Ciphertext.coq_G

    val bIsReEnc :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Ciphertext.coq_G -> Ring.coq_F -> bool

    val decryptsToExt :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Coq_enc.coq_M -> Ring.coq_F -> bool
   end

  module HardProb :
   sig
    val dLog : (Commitment.coq_G * Commitment.coq_G) -> Field.coq_F -> bool
   end

  module ALR :
   sig
   end

  val coq_ProdOfDiagonals : 'a1 -> ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 t0 t0 -> 'a1 t0

  val coq_ProdOfDiagonalsF : nat -> Field.coq_F t0 t0 -> Field.coq_F t0

  val coq_ProdOfDiagonalsVF : nat -> nat -> Field.coq_F t0 t0 t0 -> Field.coq_F t0 t0

  val coq_ProdOfDiagonalsG : nat -> Commitment.coq_G t0 t0 -> Commitment.coq_G t0

  val coq_RF_inProd : nat -> Mo.Coq_mat.coq_VF -> MoR.coq_VF -> Ring.coq_F

  val coq_RF_VCmult : nat -> Mo.Coq_mat.coq_MF -> MoR.coq_VF -> MoR.coq_VF

  val coq_WeirdCs :
    nat -> nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG

  val coq_EkGeneratorsSub :
    nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG

  val coq_EkGeneratorsSubAlt :
    nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
    MoC.coq_VG

  val coq_EkGenerators :
    Coq_enc.coq_PK -> nat -> Coq_enc.coq_M -> Ciphertext.coq_G t0 t0 ->
    Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0 -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF
    -> Ciphertext.coq_G t0

  val coq_EkGeneratorsSubRawM :
    nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF

  val coq_EkGeneratorsSubRawR :
    nat -> Ring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0

  val coq_EkGeneratorsRawM :
    nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
    Mo.Coq_mat.coq_VF

  val coq_EkGeneratorsRawR :
    nat -> Ring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0 -> MoR.coq_VF

  val makeSVectors : nat -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF t0
 end) ->
 functor (Coq_sig2:sig
  val n : nat

  val m : nat

  module ALR :
   sig
   end

  val coq_BM :
    Field.coq_F -> Coq_support.Mo.Coq_mat.coq_VF -> Coq_support.Mo.Coq_mat.coq_VF ->
    Field.coq_F

  type coq_St =
    (((Commitment.coq_G * Coq_support.EPC.MoM.coq_VG) * Field.coq_F) * Coq_support.EPC.MoM.coq_VG) * Coq_support.EPC.MoM.coq_VG

  type coq_W =
    ((Coq_support.Mo.Coq_mat.coq_VF
    t0 * Coq_support.Mo.Coq_mat.coq_VF) * Coq_support.Mo.Coq_mat.coq_VF
    t0) * Coq_support.Mo.Coq_mat.coq_VF

  type coq_R =
    (((Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F) * (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF)

  type coq_C = (Commitment.coq_G * Commitment.coq_G) * Coq_support.EPC.MoM.coq_VG

  type coq_T =
    (((Coq_support.Mo.Coq_mat.coq_VF * Field.coq_F) * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  type coq_X = Coq_support.Mo.Coq_mat.coq_VF

  type coq_TE =
    ((((Coq_support.Mo.Coq_mat.coq_VF * Field.coq_F) * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F) * (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF)

  val coq_Rel : coq_St -> coq_W -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_V0 : (coq_St * coq_C) -> Field.coq_F -> (coq_St * coq_C) * Field.coq_F

  val coq_P1 :
    ((coq_St * coq_C) * Field.coq_F) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * Field.coq_F) * coq_T

  val coq_V1 : (((coq_St * coq_C) * Field.coq_F) * coq_T) -> bool

  val simMap : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_TE -> coq_R

  val simulator :
    coq_St -> coq_TE -> Field.coq_F -> ((coq_St * coq_C) * Field.coq_F) * coq_T

  val extractor : coq_T t0 -> Field.coq_F t0 -> coq_W

  val coq_M : nat

  val allDifferent : Chal.coq_G t0 -> bool
 end) ->
 functor (Coq_bgHadProdBase:sig
  val n : nat

  val m : nat

  module ALR :
   sig
   end

  module G2 :
   sig
    type coq_G = Field.coq_F

    val coq_Gdot : coq_G -> coq_G -> coq_G

    val coq_Gone : coq_G

    val coq_Ggen : coq_G

    val coq_Gbool_eq : coq_G -> coq_G -> bool

    val coq_Gdisjoint : coq_G -> coq_G -> bool

    val coq_Ginv : coq_G -> coq_G
   end

  type coq_E = G2.coq_G * Field.coq_F

  type coq_St =
    ((Commitment.coq_G * Coq_support.EPC.MoM.coq_VG) * Coq_support.EPC.MoM.coq_VG) * Commitment.coq_G

  type coq_W =
    ((Coq_support.Mo.Coq_mat.coq_VF
    t0 * Coq_support.Mo.Coq_mat.coq_VF) * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C = Coq_support.EPC.MoM.coq_VG

  type coq_R = Coq_support.Mo.Coq_mat.coq_VF

  val add : coq_E -> coq_E -> G2.coq_G * Field.coq_F

  val zero : G2.coq_G * Field.coq_F

  val inv : coq_E -> G2.coq_G * Field.coq_F

  val bool_eq : coq_E -> coq_E -> bool

  val disjoint : coq_E -> coq_E -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_ToSt : ((coq_St * coq_C) * coq_E) -> Coq_sig2.coq_St

  val coq_ToWit : ((coq_St * coq_C) * coq_E) -> coq_R -> coq_W -> Coq_sig2.coq_W

  type coq_TE = Coq_support.Mo.Coq_mat.coq_VF

  val extractor : Coq_sig2.coq_W -> coq_E -> coq_W

  type coq_X = Coq_sig2.coq_X

  val simulator : coq_St -> coq_TE -> coq_E -> coq_C

  val simMap : coq_St -> coq_W -> coq_E -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> coq_E -> coq_X -> coq_TE -> coq_R

  val sigXcomp : coq_St -> coq_X -> Coq_sig2.coq_X
 end) ->
 functor (Coq_bgHadProd:sig
  type coq_E = Coq_bgHadProdBase.coq_E

  type coq_St = Coq_bgHadProdBase.coq_St

  type coq_W = Coq_bgHadProdBase.coq_W

  val coq_Rel : Coq_bgHadProdBase.coq_St -> Coq_bgHadProdBase.coq_W -> bool

  type coq_C = Coq_bgHadProdBase.coq_C

  type coq_R = Coq_bgHadProdBase.coq_R

  val add :
    Coq_bgHadProdBase.coq_E -> Coq_bgHadProdBase.coq_E -> Coq_bgHadProdBase.coq_E

  val zero : coq_E

  val inv : coq_E -> coq_E

  val bool_eq : coq_E -> coq_E -> bool

  val disjoint : coq_E -> coq_E -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  type coq_C1 = unit

  type coq_R1 = unit

  val coq_P1 :
    ((coq_St * coq_C) * coq_E) -> coq_R1 -> coq_W ->
    ((coq_St * coq_C) * coq_E) * coq_C1

  val coq_ToSt : (((coq_St * coq_C) * coq_E) * coq_C1) -> Coq_sig2.coq_St

  val coq_ToWit :
    ((coq_St * coq_C) * coq_E) -> coq_R -> coq_R1 -> coq_W -> Coq_sig2.coq_W

  type coq_TE = Coq_bgHadProdBase.coq_TE

  val coq_M : nat

  val extractor : Coq_sig2.coq_W t0 -> coq_E t0 -> coq_W

  type coq_X = Coq_bgHadProdBase.coq_X

  val simulator : coq_St -> coq_TE -> coq_E -> coq_C * coq_C1

  val simMap : coq_St -> coq_W -> coq_E -> coq_X -> (coq_R * coq_R1) -> coq_TE

  val simMapInv : coq_St -> coq_W -> coq_E -> coq_X -> coq_TE -> coq_R * coq_R1

  val sigXcomp : coq_St -> coq_X -> Coq_sig2.coq_X
 end) ->
 functor (Coq_sig5:sig
  type coq_E0 = Coq_bgHadProd.coq_E

  type coq_E1 = Chal.coq_G

  type coq_St = Coq_bgHadProd.coq_St

  type coq_W = Coq_bgHadProd.coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C0 = Coq_bgHadProd.coq_C

  type coq_C1 = Coq_bgHadProd.coq_C1 * Coq_sig2.coq_C

  type coq_R0 = Coq_bgHadProd.coq_R

  type coq_R1 = Coq_bgHadProd.coq_R1 * Coq_sig2.coq_R

  val add0 : coq_E0 -> coq_E0 -> coq_E0

  val zero0 : coq_E0

  val inv0 : coq_E0 -> coq_E0

  val bool_eq0 : coq_E0 -> coq_E0 -> bool

  val disjoint0 : coq_E0 -> coq_E0 -> bool

  val add1 : coq_E1 -> coq_E1 -> coq_E1

  val zero1 : coq_E1

  val inv1 : coq_E1 -> coq_E1

  val bool_eq1 : coq_E1 -> coq_E1 -> bool

  val disjoint1 : coq_E1 -> coq_E1 -> bool

  type coq_T = Coq_sig2.coq_T

  val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0

  val coq_P1 :
    ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
    ((coq_St * coq_C0) * coq_E0) * coq_C1

  val coq_P2 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) -> coq_W
    -> ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val coq_V2 : (((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T) -> bool

  type coq_TE0 = Coq_bgHadProd.coq_TE

  type coq_TE1 = Coq_sig2.coq_TE

  type coq_X = Coq_bgHadProd.coq_X

  val simulator :
    coq_St -> (coq_TE0 * coq_TE1) -> (coq_E0 * coq_E1) ->
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val simMap :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_R0 * coq_R1) ->
    coq_TE0 * coq_TE1

  val simMapInv :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_TE0 * coq_TE1) ->
    coq_R0 * coq_R1

  val coq_M0 : nat

  val coq_M1 : nat

  val extractor : coq_T t0 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_W

  val allValid :
    coq_St -> coq_C0 -> coq_C1 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_T t0 t0 -> bool
 end) ->
 functor (Coq_sig:sig
  val n : nat

  module Mo :
   sig
    module Coq_mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module AL :
     sig
     end

    module FAL :
     sig
      module AL :
       sig
       end
     end

    val coq_VandermondeCol : nat -> Field.coq_F -> Field.coq_F t0

    val coq_VandermondeColGen : nat -> Field.coq_F -> nat -> Field.coq_F t0

    val coq_Vandermonde : nat -> Coq_mat.coq_VF -> Field.coq_F t0 t0

    module SSRfield :
     sig
      module AL :
       sig
       end

      type coq_R = Field.coq_F

      val eqr : coq_R -> coq_R -> bool

      val eqrP : coq_R Equality.axiom

      val coq_R_eqMixin : coq_R Equality.mixin_of

      val coq_R_eqType : Equality.coq_type

      val pickR : coq_R pred0 -> nat -> coq_R option

      val coq_R_choiceMixin : coq_R Choice.mixin_of

      val coq_R_choiceType : Choice.coq_type

      val coq_R_zmodmixin : Field.coq_F GRing.Zmodule.mixin_of

      val coq_R_zmodtype : GRing.Zmodule.coq_type

      val coq_R_comringmixin : GRing.Ring.mixin_of

      val coq_R_ring : GRing.Ring.coq_type

      val coq_R_comring : GRing.ComRing.coq_type

      val coq_Radd_monoid : Field.coq_F Monoid.law

      val coq_Radd_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_monoid : GRing.Zmodule.sort Monoid.law

      val coq_Rmul_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_mul_law : Field.coq_F Monoid.mul_law

      val coq_Radd_add_law : Field.coq_F Monoid.add_law

      val coq_Rinvx : coq_R -> Field.coq_F

      val unit_R : coq_R -> bool

      val coq_R_unitRingMixin : GRing.UnitRing.mixin_of

      val coq_R_unitRing : GRing.UnitRing.coq_type

      val coq_R_comUnitRingType : GRing.ComUnitRing.coq_type

      val coq_R_idomainType : GRing.IntegralDomain.coq_type

      val coq_R_field : GRing.Field.coq_type
     end

    val coq_VandermondeInv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_MF

    val nat_to_ord : nat -> nat -> ordinal

    val coq_VF_inv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_VF
   end

  module EPC :
   sig
    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_EPC :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF -> Field.coq_F ->
      Commitment.coq_G

    val comEPC :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF t0 ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val comEPCvec :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val com :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_MF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module PC :
   sig
    module AddMLemmas :
     sig
     end

    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_PC :
      Commitment.coq_G -> Commitment.coq_G -> Field.coq_F -> Field.coq_F ->
      Commitment.coq_G

    val comPC :
      nat -> Commitment.coq_G -> Commitment.coq_G -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module HardProb :
   sig
    val dLog : (Commitment.coq_G * Commitment.coq_G) -> Field.coq_F -> bool
   end

  module RAL :
   sig
   end

  type coq_St =
    ((Commitment.coq_G * EPC.MoM.coq_VG) * Commitment.coq_G) * Field.coq_F

  type coq_W = Mo.Coq_mat.coq_VF * Field.coq_F

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C = (Commitment.coq_G * Commitment.coq_G) * Commitment.coq_G

  type coq_R =
    (((Mo.Coq_mat.coq_VF * Field.coq_F) * Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  type coq_T = ((Mo.Coq_mat.coq_VF * Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  val vecb : Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_P1 :
    ((coq_St * coq_C) * Field.coq_F) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * Field.coq_F) * coq_T

  val coq_V1 : (((coq_St * coq_C) * Field.coq_F) * coq_T) -> bool

  type coq_TE =
    (((Mo.Coq_mat.coq_VF * Field.coq_F) * Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  type coq_X = Mo.Coq_mat.coq_VF

  val simulator :
    coq_St -> coq_TE -> Field.coq_F -> ((coq_St * coq_C) * Field.coq_F) * coq_T

  val simMap : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_TE -> coq_R

  val coq_M : nat

  val extractor : coq_T t0 -> Field.coq_F t0 -> coq_W

  val coq_Polynomial :
    nat -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF -> Field.coq_F ->
    Mo.Coq_mat.coq_VF -> Field.coq_F

  val allDifferent : Field.coq_F t0 -> bool
 end) ->
 sig
  val n : nat

  val m : nat

  module EPC :
   sig
    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Coq_support.Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll :
        nat -> coq_VG -> Coq_support.Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row :
        nat -> coq_VG -> Coq_support.Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Coq_support.Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Coq_support.Mo.Coq_mat.coq_VF t0 t0 ->
        Coq_support.Mo.Coq_mat.coq_VF t0
     end

    val coq_EPC :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Coq_support.Mo.Coq_mat.coq_VF ->
      Field.coq_F -> Commitment.coq_G

    val comEPC :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Coq_support.Mo.Coq_mat.coq_VF
      t0 -> Coq_support.Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val comEPCvec :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Coq_support.Mo.Coq_mat.coq_VF
      -> Coq_support.Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val com :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Coq_support.Mo.Coq_mat.coq_MF ->
      Coq_support.Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module ALenc :
   sig
    module AddVSLemmas :
     sig
      module AL :
       sig
       end
     end

    module Mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module MatG :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Ciphertext.coq_G t0

      val coq_VG_id : nat -> Ciphertext.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_scale_sum : nat -> nat -> nat -> Mat.coq_VF t0 t0 -> Mat.coq_VF t0
     end

    val reenc : Coq_enc.coq_PK -> Ciphertext.coq_G -> Ring.coq_F -> Ciphertext.coq_G

    val bIsReEnc :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Ciphertext.coq_G -> Ring.coq_F -> bool

    val decryptsToExt :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Coq_enc.coq_M -> Ring.coq_F -> bool
   end

  module ALR :
   sig
   end

  module G2 :
   sig
    type coq_G = Field.coq_F

    val coq_Gdot : coq_G -> coq_G -> coq_G

    val coq_Gone : coq_G

    val coq_Ggen : coq_G

    val coq_Gbool_eq : coq_G -> coq_G -> bool

    val coq_Gdisjoint : coq_G -> coq_G -> bool

    val coq_Ginv : coq_G -> coq_G
   end

  type coq_St = ((Commitment.coq_G * EPC.MoM.coq_VG) * EPC.MoM.coq_VG) * Field.coq_F

  type coq_W = Coq_support.Mo.Coq_mat.coq_VF t0 * Coq_support.Mo.Coq_mat.coq_VF

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C = Commitment.coq_G

  type coq_R = Field.coq_F

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_ToStSig : (coq_St * coq_C) -> Coq_sig.coq_St

  val coq_ToWitSig : (coq_St * coq_C) -> coq_R -> coq_W -> Coq_sig.coq_W

  val coq_ToStSig5 : (coq_St * coq_C) -> Coq_sig5.coq_St

  val coq_ToWitSig5 : (coq_St * coq_C) -> coq_R -> coq_W -> Coq_sig5.coq_W

  type coq_TE = Field.coq_F

  val extractor : Coq_sig5.coq_W -> Coq_sig.coq_W -> coq_W

  type coq_X = Coq_support.Mo.Coq_mat.coq_VF

  val simulator : coq_St -> coq_TE -> coq_C

  val simMap : coq_St -> coq_W -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> coq_X -> coq_TE -> coq_R

  val sigXcomp : coq_St -> coq_X -> Coq_sig.coq_X

  val sig5Xcomp : coq_St -> coq_X -> Coq_sig5.coq_X
 end

module BGMultiArgIns :
 functor (Message:GroupSig) ->
 functor (Ciphertext:GroupSig) ->
 functor (Commitment:GroupSig) ->
 functor (Ring:RingSig) ->
 functor (Field:FieldSig) ->
 functor (VS2:sig
  val op : Commitment.coq_G -> Field.coq_F -> Commitment.coq_G
 end) ->
 functor (VS1:sig
  val op : Ciphertext.coq_G -> Field.coq_F -> Ciphertext.coq_G
 end) ->
 functor (Chal:sig
  type coq_G = Field.coq_F

  val coq_Gdot : Field.coq_F -> Field.coq_F -> Field.coq_F

  val coq_Gone : Field.coq_F

  val coq_Ggen : Field.coq_F

  val coq_Gbool_eq : Field.coq_F -> Field.coq_F -> bool

  val coq_Gdisjoint : Field.coq_F -> Field.coq_F -> bool

  val coq_Ginv : Field.coq_F -> Field.coq_F
 end) ->
 functor (MVS:sig
  val op3 : Ring.coq_F -> Field.coq_F -> Ring.coq_F
 end) ->
 functor (VS3:sig
  val op : Message.coq_G -> Field.coq_F -> Message.coq_G
 end) ->
 functor (Hack:Coq0_Nat) ->
 functor (M:Coq0_Nat) ->
 functor (Coq_enc:sig
  type coq_KGR

  type coq_PK

  type coq_SK

  type coq_M = Message.coq_G

  val coq_Mop : Message.coq_G -> Message.coq_G -> Message.coq_G

  val coq_Mzero : Message.coq_G

  val coq_Mone : Message.coq_G

  val coq_Minv : Message.coq_G -> Message.coq_G

  val coq_Mbool_eq : Message.coq_G -> Message.coq_G -> bool

  val keygen : coq_KGR -> coq_PK * coq_SK

  val keygenMix : coq_KGR -> coq_PK

  val enc : coq_PK -> coq_M -> Ring.coq_F -> Ciphertext.coq_G

  val dec : coq_SK -> Ciphertext.coq_G -> coq_M

  val keymatch : coq_PK -> coq_SK -> bool
 end) ->
 functor (Coq_support:sig
  val n : nat

  val m : nat

  module Mo :
   sig
    module Coq_mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module AL :
     sig
     end

    module FAL :
     sig
      module AL :
       sig
       end
     end

    val coq_VandermondeCol : nat -> Field.coq_F -> Field.coq_F t0

    val coq_VandermondeColGen : nat -> Field.coq_F -> nat -> Field.coq_F t0

    val coq_Vandermonde : nat -> Coq_mat.coq_VF -> Field.coq_F t0 t0

    module SSRfield :
     sig
      module AL :
       sig
       end

      type coq_R = Field.coq_F

      val eqr : coq_R -> coq_R -> bool

      val eqrP : coq_R Equality.axiom

      val coq_R_eqMixin : coq_R Equality.mixin_of

      val coq_R_eqType : Equality.coq_type

      val pickR : coq_R pred0 -> nat -> coq_R option

      val coq_R_choiceMixin : coq_R Choice.mixin_of

      val coq_R_choiceType : Choice.coq_type

      val coq_R_zmodmixin : Field.coq_F GRing.Zmodule.mixin_of

      val coq_R_zmodtype : GRing.Zmodule.coq_type

      val coq_R_comringmixin : GRing.Ring.mixin_of

      val coq_R_ring : GRing.Ring.coq_type

      val coq_R_comring : GRing.ComRing.coq_type

      val coq_Radd_monoid : Field.coq_F Monoid.law

      val coq_Radd_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_monoid : GRing.Zmodule.sort Monoid.law

      val coq_Rmul_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_mul_law : Field.coq_F Monoid.mul_law

      val coq_Radd_add_law : Field.coq_F Monoid.add_law

      val coq_Rinvx : coq_R -> Field.coq_F

      val unit_R : coq_R -> bool

      val coq_R_unitRingMixin : GRing.UnitRing.mixin_of

      val coq_R_unitRing : GRing.UnitRing.coq_type

      val coq_R_comUnitRingType : GRing.ComUnitRing.coq_type

      val coq_R_idomainType : GRing.IntegralDomain.coq_type

      val coq_R_field : GRing.Field.coq_type
     end

    val coq_VandermondeInv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_MF

    val nat_to_ord : nat -> nat -> ordinal

    val coq_VF_inv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_VF
   end

  module MoR :
   sig
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = Ring.coq_F t0

    val coq_VF_zero : nat -> Ring.coq_F t0

    val coq_VF_one : nat -> Ring.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

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

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> Ring.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module MoC :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Ciphertext.coq_G t0

    val coq_VG_id : nat -> Ciphertext.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
   end

  module EPC :
   sig
    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_EPC :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF -> Field.coq_F ->
      Commitment.coq_G

    val comEPC :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF t0 ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val comEPCvec :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val com :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_MF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module PC :
   sig
    module AddMLemmas :
     sig
     end

    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_PC :
      Commitment.coq_G -> Commitment.coq_G -> Field.coq_F -> Field.coq_F ->
      Commitment.coq_G

    val comPC :
      nat -> Commitment.coq_G -> Commitment.coq_G -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module MoM :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Message.coq_G t0

    val coq_VG_id : nat -> Message.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Message.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
   end

  module ALVS1 :
   sig
    module AL :
     sig
     end
   end

  module ALVS2 :
   sig
    module AL :
     sig
     end
   end

  module ALVS3 :
   sig
    module AL :
     sig
     end
   end

  module ALenc :
   sig
    module AddVSLemmas :
     sig
      module AL :
       sig
       end
     end

    module Mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module MatG :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Ciphertext.coq_G t0

      val coq_VG_id : nat -> Ciphertext.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_scale_sum : nat -> nat -> nat -> Mat.coq_VF t0 t0 -> Mat.coq_VF t0
     end

    val reenc : Coq_enc.coq_PK -> Ciphertext.coq_G -> Ring.coq_F -> Ciphertext.coq_G

    val bIsReEnc :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Ciphertext.coq_G -> Ring.coq_F -> bool

    val decryptsToExt :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Coq_enc.coq_M -> Ring.coq_F -> bool
   end

  module HardProb :
   sig
    val dLog : (Commitment.coq_G * Commitment.coq_G) -> Field.coq_F -> bool
   end

  module ALR :
   sig
   end

  val coq_ProdOfDiagonals : 'a1 -> ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 t0 t0 -> 'a1 t0

  val coq_ProdOfDiagonalsF : nat -> Field.coq_F t0 t0 -> Field.coq_F t0

  val coq_ProdOfDiagonalsVF : nat -> nat -> Field.coq_F t0 t0 t0 -> Field.coq_F t0 t0

  val coq_ProdOfDiagonalsG : nat -> Commitment.coq_G t0 t0 -> Commitment.coq_G t0

  val coq_RF_inProd : nat -> Mo.Coq_mat.coq_VF -> MoR.coq_VF -> Ring.coq_F

  val coq_RF_VCmult : nat -> Mo.Coq_mat.coq_MF -> MoR.coq_VF -> MoR.coq_VF

  val coq_WeirdCs :
    nat -> nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG

  val coq_EkGeneratorsSub :
    nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG

  val coq_EkGeneratorsSubAlt :
    nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
    MoC.coq_VG

  val coq_EkGenerators :
    Coq_enc.coq_PK -> nat -> Coq_enc.coq_M -> Ciphertext.coq_G t0 t0 ->
    Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0 -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF
    -> Ciphertext.coq_G t0

  val coq_EkGeneratorsSubRawM :
    nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF

  val coq_EkGeneratorsSubRawR :
    nat -> Ring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0

  val coq_EkGeneratorsRawM :
    nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
    Mo.Coq_mat.coq_VF

  val coq_EkGeneratorsRawR :
    nat -> Ring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0 -> MoR.coq_VF

  val makeSVectors : nat -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF t0
 end) ->
 sig
  val n : nat

  val m : nat

  type coq_St =
    (((((Coq_enc.coq_PK * Commitment.coq_G) * Coq_support.EPC.MoM.coq_VG) * Ciphertext.coq_G
    t0 t0) * Ciphertext.coq_G) * Coq_support.EPC.MoM.coq_VG) * Coq_enc.coq_M

  type coq_W =
    (Coq_support.Mo.Coq_mat.coq_VF t0 * Coq_support.Mo.Coq_mat.coq_VF) * Ring.coq_F

  type coq_R =
    (((Coq_support.Mo.Coq_mat.coq_VF * Field.coq_F) * (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF)) * (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF)) * (Ring.coq_F
    t0 * Ring.coq_F t0)

  type coq_C = (Commitment.coq_G * Coq_support.EPC.MoM.coq_VG) * Ciphertext.coq_G t0

  type coq_T =
    (((Coq_support.Mo.Coq_mat.coq_VF * Field.coq_F) * Field.coq_F) * Field.coq_F) * Ring.coq_F

  type coq_X =
    (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF t0) * Ring.coq_F
    t0 t0

  type coq_TE =
    ((((Coq_support.Mo.Coq_mat.coq_VF * Field.coq_F) * Field.coq_F) * Field.coq_F) * Ring.coq_F) * (((Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF) * (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF)) * (Ring.coq_F
    t0 * Ring.coq_F t0))

  val coq_Rel : coq_St -> coq_W -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_P1 :
    ((coq_St * coq_C) * Field.coq_F) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * Field.coq_F) * coq_T

  val coq_V1 : (((coq_St * coq_C) * Field.coq_F) * coq_T) -> bool

  val simMap : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_TE -> coq_R

  val simulator :
    coq_St -> coq_TE -> Field.coq_F -> ((coq_St * coq_C) * Field.coq_F) * coq_T

  val coq_M : nat

  val extractor : coq_T t0 -> Field.coq_F t0 -> coq_W

  val disjoint : Field.coq_F -> Field.coq_F -> bool

  val allDifferent : Field.coq_F t0 -> bool
 end

module SigmaPlus5plus3to9Comp :
 functor (E:GroupSig) ->
 functor (Coq_sig:sig
  type coq_St

  type coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C

  type coq_R

  type coq_T

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_P1 :
    ((coq_St * coq_C) * E.coq_G) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * E.coq_G) * coq_T

  val coq_V1 : (((coq_St * coq_C) * E.coq_G) * coq_T) -> bool

  type coq_TE

  type coq_X

  val simulator : coq_St -> coq_TE -> E.coq_G -> ((coq_St * coq_C) * E.coq_G) * coq_T

  val simMap : coq_St -> coq_W -> E.coq_G -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> E.coq_G -> coq_X -> coq_TE -> coq_R

  val coq_M : nat

  val extractor : coq_T t0 -> E.coq_G t0 -> coq_W

  val allDifferent : E.coq_G t0 -> bool
 end) ->
 functor (Coq_sig5:SigmaPlus5) ->
 functor (Coq_exp:sig
  type coq_E0

  type coq_E1

  val add0 : coq_E0 -> coq_E0 -> coq_E0

  val zero0 : coq_E0

  val inv0 : coq_E0 -> coq_E0

  val bool_eq0 : coq_E0 -> coq_E0 -> bool

  val disjoint0 : coq_E0 -> coq_E0 -> bool

  val add1 : coq_E1 -> coq_E1 -> coq_E1

  val zero1 : coq_E1

  val inv1 : coq_E1 -> coq_E1

  val bool_eq1 : coq_E1 -> coq_E1 -> bool

  val disjoint1 : coq_E1 -> coq_E1 -> bool

  type coq_St

  type coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C0

  type coq_C1

  type coq_R0

  type coq_R1

  val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0

  val coq_P1 :
    ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
    ((coq_St * coq_C0) * coq_E0) * coq_C1

  val coq_ToStSig :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> Coq_sig.coq_St

  val coq_ToWitSig :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) -> coq_W
    -> Coq_sig.coq_W

  val coq_ToStSig5 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> Coq_sig5.coq_St

  val coq_ToWitSig5 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) -> coq_W
    -> Coq_sig5.coq_W

  type coq_TE0

  type coq_TE1

  type coq_X

  val sigXcomp : coq_St -> coq_X -> Coq_sig.coq_X

  val sig5Xcomp : coq_St -> coq_X -> Coq_sig5.coq_X

  val simulator :
    coq_St -> (coq_TE0 * coq_TE1) -> (coq_E0 * coq_E1) -> coq_C0 * coq_C1

  val simMap :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_R0 * coq_R1) ->
    coq_TE0 * coq_TE1

  val simMapInv :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_TE0 * coq_TE1) ->
    coq_R0 * coq_R1

  val coq_M0 : nat

  val coq_M1 : nat

  val extractor :
    (Coq_sig5.coq_W * Coq_sig.coq_W) t0 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_W
 end) ->
 sig
  type coq_E0 = Coq_exp.coq_E0

  type coq_E1 = Coq_exp.coq_E1

  type coq_E2 = Coq_sig5.coq_E0 * E.coq_G

  type coq_E3 = Coq_sig5.coq_E1

  type coq_St = Coq_exp.coq_St

  type coq_W = Coq_exp.coq_W

  val coq_Rel : Coq_exp.coq_St -> Coq_exp.coq_W -> bool

  type coq_C0 = Coq_exp.coq_C0

  type coq_C1 = Coq_exp.coq_C1

  type coq_C2 = Coq_sig5.coq_C0 * Coq_sig.coq_C

  type coq_C3 = Coq_sig5.coq_C1

  type coq_R0 = Coq_exp.coq_R0

  type coq_R1 = Coq_exp.coq_R1

  type coq_R2 = Coq_sig5.coq_R0 * Coq_sig.coq_R

  type coq_R3 = Coq_sig5.coq_R1

  val add0 : coq_E0 -> coq_E0 -> coq_E0

  val zero0 : coq_E0

  val inv0 : coq_E0 -> coq_E0

  val bool_eq0 : coq_E0 -> coq_E0 -> bool

  val disjoint0 : coq_E0 -> coq_E0 -> bool

  val add1 : coq_E1 -> coq_E1 -> coq_E1

  val zero1 : coq_E1

  val inv1 : coq_E1 -> coq_E1

  val bool_eq1 : coq_E1 -> coq_E1 -> bool

  val disjoint1 : coq_E1 -> coq_E1 -> bool

  val add2 : coq_E2 -> coq_E2 -> coq_E2

  val zero2 : coq_E2

  val inv2 : coq_E2 -> coq_E2

  val bool_eq2 : coq_E2 -> coq_E2 -> bool

  val disjoint2 : coq_E2 -> coq_E2 -> bool

  val add3 : coq_E3 -> coq_E3 -> coq_E3

  val zero3 : coq_E3

  val inv3 : coq_E3 -> coq_E3

  val bool_eq3 : coq_E3 -> coq_E3 -> bool

  val disjoint3 : coq_E3 -> coq_E3 -> bool

  type coq_T = Coq_sig5.coq_T * Coq_sig.coq_T

  val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0

  val coq_P1 :
    ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
    ((coq_St * coq_C0) * coq_E0) * coq_C1

  val coq_P2 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) ->
    ((coq_R0 * coq_R1) * coq_R2) -> coq_W ->
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2

  val coq_P3 :
    ((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) ->
    (((coq_R0 * coq_R1) * coq_R2) * coq_R3) -> coq_W ->
    ((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) * coq_C3

  val coq_P4 :
    ((((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) * coq_C3) * coq_E3)
    -> (((coq_R0 * coq_R1) * coq_R2) * coq_R3) -> coq_W ->
    ((((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) * coq_C3) * coq_E3) * coq_T

  val coq_V :
    (((((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) * coq_C3) * coq_E3) * coq_T)
    -> bool

  type coq_TE0 = Coq_exp.coq_TE0

  type coq_TE1 = Coq_exp.coq_TE1

  type coq_TE2 = Coq_sig5.coq_TE0 * Coq_sig.coq_TE

  type coq_TE3 = Coq_sig5.coq_TE1

  type coq_X = Coq_exp.coq_X

  val simulator :
    coq_St -> (((coq_TE0 * coq_TE1) * coq_TE2) * coq_TE3) ->
    (((coq_E0 * coq_E1) * coq_E2) * coq_E3) ->
    ((((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) * coq_C3) * coq_E3) * coq_T

  val simMap :
    coq_St -> coq_W -> (((coq_E0 * coq_E1) * coq_E2) * coq_E3) -> coq_X ->
    (((coq_R0 * coq_R1) * coq_R2) * coq_R3) ->
    ((coq_TE0 * coq_TE1) * coq_TE2) * coq_TE3

  val simMapInv :
    coq_St -> coq_W -> (((coq_E0 * coq_E1) * coq_E2) * coq_E3) -> coq_X ->
    (((coq_TE0 * coq_TE1) * coq_TE2) * coq_TE3) ->
    ((coq_R0 * coq_R1) * coq_R2) * coq_R3

  val coq_M0 : nat

  val coq_M1 : nat

  val coq_M2 : nat

  val coq_M3 : nat

  val getSig5Resp : coq_T t0 t0 -> Coq_sig5.coq_T t0 t0

  val getSig5Chal :
    (coq_E2 * coq_E3 t0) t0 -> (Coq_sig5.coq_E0 * Coq_sig5.coq_E1 t0) t0

  val getSigResp : coq_T t0 t0 -> Coq_sig.coq_T t0

  val getSigChal : (coq_E2 * coq_E3 t0) t0 -> E.coq_G t0

  val extractor :
    coq_T t0 t0 t0 t0 -> (coq_E0 * (coq_E1 * (coq_E2 * coq_E3 t0) t0) t0) t0 -> coq_W

  val getSig5Com : (coq_C2 * coq_C3 t0) -> Coq_sig5.coq_C0 * Coq_sig5.coq_C1 t0

  val getSigCom : (coq_C2 * coq_C3 t0) -> Coq_sig.coq_C
 end

module ShuffleArg :
 functor (Message:GroupSig) ->
 functor (Ciphertext:GroupSig) ->
 functor (Commitment:GroupSig) ->
 functor (Ring:RingSig) ->
 functor (Field:FieldSig) ->
 functor (VS2:sig
  val op : Commitment.coq_G -> Field.coq_F -> Commitment.coq_G
 end) ->
 functor (VS1:sig
  val op : Ciphertext.coq_G -> Field.coq_F -> Ciphertext.coq_G
 end) ->
 functor (Chal:sig
  type coq_G = Field.coq_F

  val coq_Gdot : Field.coq_F -> Field.coq_F -> Field.coq_F

  val coq_Gone : Field.coq_F

  val coq_Ggen : Field.coq_F

  val coq_Gbool_eq : Field.coq_F -> Field.coq_F -> bool

  val coq_Gdisjoint : Field.coq_F -> Field.coq_F -> bool

  val coq_Ginv : Field.coq_F -> Field.coq_F
 end) ->
 functor (MVS:sig
  val op3 : Ring.coq_F -> Field.coq_F -> Ring.coq_F
 end) ->
 functor (VS3:sig
  val op : Message.coq_G -> Field.coq_F -> Message.coq_G
 end) ->
 functor (Hack:Coq0_Nat) ->
 functor (M:Coq0_Nat) ->
 functor (Coq_enc:sig
  type coq_KGR

  type coq_PK

  type coq_SK

  type coq_M = Message.coq_G

  val coq_Mop : Message.coq_G -> Message.coq_G -> Message.coq_G

  val coq_Mzero : Message.coq_G

  val coq_Mone : Message.coq_G

  val coq_Minv : Message.coq_G -> Message.coq_G

  val coq_Mbool_eq : Message.coq_G -> Message.coq_G -> bool

  val keygen : coq_KGR -> coq_PK * coq_SK

  val keygenMix : coq_KGR -> coq_PK

  val enc : coq_PK -> coq_M -> Ring.coq_F -> Ciphertext.coq_G

  val dec : coq_SK -> Ciphertext.coq_G -> coq_M

  val keymatch : coq_PK -> coq_SK -> bool
 end) ->
 functor (Coq_support:sig
  val n : nat

  val m : nat

  module Mo :
   sig
    module Coq_mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module AL :
     sig
     end

    module FAL :
     sig
      module AL :
       sig
       end
     end

    val coq_VandermondeCol : nat -> Field.coq_F -> Field.coq_F t0

    val coq_VandermondeColGen : nat -> Field.coq_F -> nat -> Field.coq_F t0

    val coq_Vandermonde : nat -> Coq_mat.coq_VF -> Field.coq_F t0 t0

    module SSRfield :
     sig
      module AL :
       sig
       end

      type coq_R = Field.coq_F

      val eqr : coq_R -> coq_R -> bool

      val eqrP : coq_R Equality.axiom

      val coq_R_eqMixin : coq_R Equality.mixin_of

      val coq_R_eqType : Equality.coq_type

      val pickR : coq_R pred0 -> nat -> coq_R option

      val coq_R_choiceMixin : coq_R Choice.mixin_of

      val coq_R_choiceType : Choice.coq_type

      val coq_R_zmodmixin : Field.coq_F GRing.Zmodule.mixin_of

      val coq_R_zmodtype : GRing.Zmodule.coq_type

      val coq_R_comringmixin : GRing.Ring.mixin_of

      val coq_R_ring : GRing.Ring.coq_type

      val coq_R_comring : GRing.ComRing.coq_type

      val coq_Radd_monoid : Field.coq_F Monoid.law

      val coq_Radd_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_monoid : GRing.Zmodule.sort Monoid.law

      val coq_Rmul_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_mul_law : Field.coq_F Monoid.mul_law

      val coq_Radd_add_law : Field.coq_F Monoid.add_law

      val coq_Rinvx : coq_R -> Field.coq_F

      val unit_R : coq_R -> bool

      val coq_R_unitRingMixin : GRing.UnitRing.mixin_of

      val coq_R_unitRing : GRing.UnitRing.coq_type

      val coq_R_comUnitRingType : GRing.ComUnitRing.coq_type

      val coq_R_idomainType : GRing.IntegralDomain.coq_type

      val coq_R_field : GRing.Field.coq_type
     end

    val coq_VandermondeInv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_MF

    val nat_to_ord : nat -> nat -> ordinal

    val coq_VF_inv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_VF
   end

  module MoR :
   sig
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = Ring.coq_F t0

    val coq_VF_zero : nat -> Ring.coq_F t0

    val coq_VF_one : nat -> Ring.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

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

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> Ring.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module MoC :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Ciphertext.coq_G t0

    val coq_VG_id : nat -> Ciphertext.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
   end

  module EPC :
   sig
    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_EPC :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF -> Field.coq_F ->
      Commitment.coq_G

    val comEPC :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF t0 ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val comEPCvec :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val com :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_MF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module PC :
   sig
    module AddMLemmas :
     sig
     end

    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_PC :
      Commitment.coq_G -> Commitment.coq_G -> Field.coq_F -> Field.coq_F ->
      Commitment.coq_G

    val comPC :
      nat -> Commitment.coq_G -> Commitment.coq_G -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module MoM :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Message.coq_G t0

    val coq_VG_id : nat -> Message.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Message.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
   end

  module ALVS1 :
   sig
    module AL :
     sig
     end
   end

  module ALVS2 :
   sig
    module AL :
     sig
     end
   end

  module ALVS3 :
   sig
    module AL :
     sig
     end
   end

  module ALenc :
   sig
    module AddVSLemmas :
     sig
      module AL :
       sig
       end
     end

    module Mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module MatG :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Ciphertext.coq_G t0

      val coq_VG_id : nat -> Ciphertext.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_scale_sum : nat -> nat -> nat -> Mat.coq_VF t0 t0 -> Mat.coq_VF t0
     end

    val reenc : Coq_enc.coq_PK -> Ciphertext.coq_G -> Ring.coq_F -> Ciphertext.coq_G

    val bIsReEnc :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Ciphertext.coq_G -> Ring.coq_F -> bool

    val decryptsToExt :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Coq_enc.coq_M -> Ring.coq_F -> bool
   end

  module HardProb :
   sig
    val dLog : (Commitment.coq_G * Commitment.coq_G) -> Field.coq_F -> bool
   end

  module ALR :
   sig
   end

  val coq_ProdOfDiagonals : 'a1 -> ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 t0 t0 -> 'a1 t0

  val coq_ProdOfDiagonalsF : nat -> Field.coq_F t0 t0 -> Field.coq_F t0

  val coq_ProdOfDiagonalsVF : nat -> nat -> Field.coq_F t0 t0 t0 -> Field.coq_F t0 t0

  val coq_ProdOfDiagonalsG : nat -> Commitment.coq_G t0 t0 -> Commitment.coq_G t0

  val coq_RF_inProd : nat -> Mo.Coq_mat.coq_VF -> MoR.coq_VF -> Ring.coq_F

  val coq_RF_VCmult : nat -> Mo.Coq_mat.coq_MF -> MoR.coq_VF -> MoR.coq_VF

  val coq_WeirdCs :
    nat -> nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG

  val coq_EkGeneratorsSub :
    nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG

  val coq_EkGeneratorsSubAlt :
    nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
    MoC.coq_VG

  val coq_EkGenerators :
    Coq_enc.coq_PK -> nat -> Coq_enc.coq_M -> Ciphertext.coq_G t0 t0 ->
    Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0 -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF
    -> Ciphertext.coq_G t0

  val coq_EkGeneratorsSubRawM :
    nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF

  val coq_EkGeneratorsSubRawR :
    nat -> Ring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0

  val coq_EkGeneratorsRawM :
    nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
    Mo.Coq_mat.coq_VF

  val coq_EkGeneratorsRawR :
    nat -> Ring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0 -> MoR.coq_VF

  val makeSVectors : nat -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF t0
 end) ->
 functor (Coq_sig2:sig
  val n : nat

  val m : nat

  module ALR :
   sig
   end

  val coq_BM :
    Field.coq_F -> Coq_support.Mo.Coq_mat.coq_VF -> Coq_support.Mo.Coq_mat.coq_VF ->
    Field.coq_F

  type coq_St =
    (((Commitment.coq_G * Coq_support.EPC.MoM.coq_VG) * Field.coq_F) * Coq_support.EPC.MoM.coq_VG) * Coq_support.EPC.MoM.coq_VG

  type coq_W =
    ((Coq_support.Mo.Coq_mat.coq_VF
    t0 * Coq_support.Mo.Coq_mat.coq_VF) * Coq_support.Mo.Coq_mat.coq_VF
    t0) * Coq_support.Mo.Coq_mat.coq_VF

  type coq_R =
    (((Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F) * (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF)

  type coq_C = (Commitment.coq_G * Commitment.coq_G) * Coq_support.EPC.MoM.coq_VG

  type coq_T =
    (((Coq_support.Mo.Coq_mat.coq_VF * Field.coq_F) * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  type coq_X = Coq_support.Mo.Coq_mat.coq_VF

  type coq_TE =
    ((((Coq_support.Mo.Coq_mat.coq_VF * Field.coq_F) * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F) * (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF)

  val coq_Rel : coq_St -> coq_W -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_V0 : (coq_St * coq_C) -> Field.coq_F -> (coq_St * coq_C) * Field.coq_F

  val coq_P1 :
    ((coq_St * coq_C) * Field.coq_F) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * Field.coq_F) * coq_T

  val coq_V1 : (((coq_St * coq_C) * Field.coq_F) * coq_T) -> bool

  val simMap : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_TE -> coq_R

  val simulator :
    coq_St -> coq_TE -> Field.coq_F -> ((coq_St * coq_C) * Field.coq_F) * coq_T

  val extractor : coq_T t0 -> Field.coq_F t0 -> coq_W

  val coq_M : nat

  val allDifferent : Chal.coq_G t0 -> bool
 end) ->
 functor (Coq_bgHadProdBase:sig
  val n : nat

  val m : nat

  module ALR :
   sig
   end

  module G2 :
   sig
    type coq_G = Field.coq_F

    val coq_Gdot : coq_G -> coq_G -> coq_G

    val coq_Gone : coq_G

    val coq_Ggen : coq_G

    val coq_Gbool_eq : coq_G -> coq_G -> bool

    val coq_Gdisjoint : coq_G -> coq_G -> bool

    val coq_Ginv : coq_G -> coq_G
   end

  type coq_E = G2.coq_G * Field.coq_F

  type coq_St =
    ((Commitment.coq_G * Coq_support.EPC.MoM.coq_VG) * Coq_support.EPC.MoM.coq_VG) * Commitment.coq_G

  type coq_W =
    ((Coq_support.Mo.Coq_mat.coq_VF
    t0 * Coq_support.Mo.Coq_mat.coq_VF) * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C = Coq_support.EPC.MoM.coq_VG

  type coq_R = Coq_support.Mo.Coq_mat.coq_VF

  val add : coq_E -> coq_E -> G2.coq_G * Field.coq_F

  val zero : G2.coq_G * Field.coq_F

  val inv : coq_E -> G2.coq_G * Field.coq_F

  val bool_eq : coq_E -> coq_E -> bool

  val disjoint : coq_E -> coq_E -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_ToSt : ((coq_St * coq_C) * coq_E) -> Coq_sig2.coq_St

  val coq_ToWit : ((coq_St * coq_C) * coq_E) -> coq_R -> coq_W -> Coq_sig2.coq_W

  type coq_TE = Coq_support.Mo.Coq_mat.coq_VF

  val extractor : Coq_sig2.coq_W -> coq_E -> coq_W

  type coq_X = Coq_sig2.coq_X

  val simulator : coq_St -> coq_TE -> coq_E -> coq_C

  val simMap : coq_St -> coq_W -> coq_E -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> coq_E -> coq_X -> coq_TE -> coq_R

  val sigXcomp : coq_St -> coq_X -> Coq_sig2.coq_X
 end) ->
 functor (Coq_bgHadProd:sig
  type coq_E = Coq_bgHadProdBase.coq_E

  type coq_St = Coq_bgHadProdBase.coq_St

  type coq_W = Coq_bgHadProdBase.coq_W

  val coq_Rel : Coq_bgHadProdBase.coq_St -> Coq_bgHadProdBase.coq_W -> bool

  type coq_C = Coq_bgHadProdBase.coq_C

  type coq_R = Coq_bgHadProdBase.coq_R

  val add :
    Coq_bgHadProdBase.coq_E -> Coq_bgHadProdBase.coq_E -> Coq_bgHadProdBase.coq_E

  val zero : coq_E

  val inv : coq_E -> coq_E

  val bool_eq : coq_E -> coq_E -> bool

  val disjoint : coq_E -> coq_E -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  type coq_C1 = unit

  type coq_R1 = unit

  val coq_P1 :
    ((coq_St * coq_C) * coq_E) -> coq_R1 -> coq_W ->
    ((coq_St * coq_C) * coq_E) * coq_C1

  val coq_ToSt : (((coq_St * coq_C) * coq_E) * coq_C1) -> Coq_sig2.coq_St

  val coq_ToWit :
    ((coq_St * coq_C) * coq_E) -> coq_R -> coq_R1 -> coq_W -> Coq_sig2.coq_W

  type coq_TE = Coq_bgHadProdBase.coq_TE

  val coq_M : nat

  val extractor : Coq_sig2.coq_W t0 -> coq_E t0 -> coq_W

  type coq_X = Coq_bgHadProdBase.coq_X

  val simulator : coq_St -> coq_TE -> coq_E -> coq_C * coq_C1

  val simMap : coq_St -> coq_W -> coq_E -> coq_X -> (coq_R * coq_R1) -> coq_TE

  val simMapInv : coq_St -> coq_W -> coq_E -> coq_X -> coq_TE -> coq_R * coq_R1

  val sigXcomp : coq_St -> coq_X -> Coq_sig2.coq_X
 end) ->
 functor (Coq_sig5:sig
  type coq_E0 = Coq_bgHadProd.coq_E

  type coq_E1 = Chal.coq_G

  type coq_St = Coq_bgHadProd.coq_St

  type coq_W = Coq_bgHadProd.coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C0 = Coq_bgHadProd.coq_C

  type coq_C1 = Coq_bgHadProd.coq_C1 * Coq_sig2.coq_C

  type coq_R0 = Coq_bgHadProd.coq_R

  type coq_R1 = Coq_bgHadProd.coq_R1 * Coq_sig2.coq_R

  val add0 : coq_E0 -> coq_E0 -> coq_E0

  val zero0 : coq_E0

  val inv0 : coq_E0 -> coq_E0

  val bool_eq0 : coq_E0 -> coq_E0 -> bool

  val disjoint0 : coq_E0 -> coq_E0 -> bool

  val add1 : coq_E1 -> coq_E1 -> coq_E1

  val zero1 : coq_E1

  val inv1 : coq_E1 -> coq_E1

  val bool_eq1 : coq_E1 -> coq_E1 -> bool

  val disjoint1 : coq_E1 -> coq_E1 -> bool

  type coq_T = Coq_sig2.coq_T

  val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0

  val coq_P1 :
    ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
    ((coq_St * coq_C0) * coq_E0) * coq_C1

  val coq_P2 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) -> coq_W
    -> ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val coq_V2 : (((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T) -> bool

  type coq_TE0 = Coq_bgHadProd.coq_TE

  type coq_TE1 = Coq_sig2.coq_TE

  type coq_X = Coq_bgHadProd.coq_X

  val simulator :
    coq_St -> (coq_TE0 * coq_TE1) -> (coq_E0 * coq_E1) ->
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val simMap :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_R0 * coq_R1) ->
    coq_TE0 * coq_TE1

  val simMapInv :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_TE0 * coq_TE1) ->
    coq_R0 * coq_R1

  val coq_M0 : nat

  val coq_M1 : nat

  val extractor : coq_T t0 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_W

  val allValid :
    coq_St -> coq_C0 -> coq_C1 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_T t0 t0 -> bool
 end) ->
 functor (Coq_sig:sig
  val n : nat

  module Mo :
   sig
    module Coq_mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module AL :
     sig
     end

    module FAL :
     sig
      module AL :
       sig
       end
     end

    val coq_VandermondeCol : nat -> Field.coq_F -> Field.coq_F t0

    val coq_VandermondeColGen : nat -> Field.coq_F -> nat -> Field.coq_F t0

    val coq_Vandermonde : nat -> Coq_mat.coq_VF -> Field.coq_F t0 t0

    module SSRfield :
     sig
      module AL :
       sig
       end

      type coq_R = Field.coq_F

      val eqr : coq_R -> coq_R -> bool

      val eqrP : coq_R Equality.axiom

      val coq_R_eqMixin : coq_R Equality.mixin_of

      val coq_R_eqType : Equality.coq_type

      val pickR : coq_R pred0 -> nat -> coq_R option

      val coq_R_choiceMixin : coq_R Choice.mixin_of

      val coq_R_choiceType : Choice.coq_type

      val coq_R_zmodmixin : Field.coq_F GRing.Zmodule.mixin_of

      val coq_R_zmodtype : GRing.Zmodule.coq_type

      val coq_R_comringmixin : GRing.Ring.mixin_of

      val coq_R_ring : GRing.Ring.coq_type

      val coq_R_comring : GRing.ComRing.coq_type

      val coq_Radd_monoid : Field.coq_F Monoid.law

      val coq_Radd_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_monoid : GRing.Zmodule.sort Monoid.law

      val coq_Rmul_comoid : Field.coq_F Monoid.com_law

      val coq_Rmul_mul_law : Field.coq_F Monoid.mul_law

      val coq_Radd_add_law : Field.coq_F Monoid.add_law

      val coq_Rinvx : coq_R -> Field.coq_F

      val unit_R : coq_R -> bool

      val coq_R_unitRingMixin : GRing.UnitRing.mixin_of

      val coq_R_unitRing : GRing.UnitRing.coq_type

      val coq_R_comUnitRingType : GRing.ComUnitRing.coq_type

      val coq_R_idomainType : GRing.IntegralDomain.coq_type

      val coq_R_field : GRing.Field.coq_type
     end

    val coq_VandermondeInv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_MF

    val nat_to_ord : nat -> nat -> ordinal

    val coq_VF_inv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_VF
   end

  module EPC :
   sig
    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_EPC :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF -> Field.coq_F ->
      Commitment.coq_G

    val comEPC :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF t0 ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val comEPCvec :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val com :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_MF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module PC :
   sig
    module AddMLemmas :
     sig
     end

    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_PC :
      Commitment.coq_G -> Commitment.coq_G -> Field.coq_F -> Field.coq_F ->
      Commitment.coq_G

    val comPC :
      nat -> Commitment.coq_G -> Commitment.coq_G -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module HardProb :
   sig
    val dLog : (Commitment.coq_G * Commitment.coq_G) -> Field.coq_F -> bool
   end

  module RAL :
   sig
   end

  type coq_St =
    ((Commitment.coq_G * EPC.MoM.coq_VG) * Commitment.coq_G) * Field.coq_F

  type coq_W = Mo.Coq_mat.coq_VF * Field.coq_F

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C = (Commitment.coq_G * Commitment.coq_G) * Commitment.coq_G

  type coq_R =
    (((Mo.Coq_mat.coq_VF * Field.coq_F) * Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  type coq_T = ((Mo.Coq_mat.coq_VF * Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  val vecb : Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_P1 :
    ((coq_St * coq_C) * Field.coq_F) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * Field.coq_F) * coq_T

  val coq_V1 : (((coq_St * coq_C) * Field.coq_F) * coq_T) -> bool

  type coq_TE =
    (((Mo.Coq_mat.coq_VF * Field.coq_F) * Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  type coq_X = Mo.Coq_mat.coq_VF

  val simulator :
    coq_St -> coq_TE -> Field.coq_F -> ((coq_St * coq_C) * Field.coq_F) * coq_T

  val simMap : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_TE -> coq_R

  val coq_M : nat

  val extractor : coq_T t0 -> Field.coq_F t0 -> coq_W

  val coq_Polynomial :
    nat -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF -> Field.coq_F ->
    Mo.Coq_mat.coq_VF -> Field.coq_F

  val allDifferent : Field.coq_F t0 -> bool
 end) ->
 functor (Coq_prodArg:sig
  val n : nat

  val m : nat

  module EPC :
   sig
    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Commitment.coq_G t0

      val coq_VG_id : nat -> Commitment.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Commitment.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Coq_support.Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll :
        nat -> coq_VG -> Coq_support.Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row :
        nat -> coq_VG -> Coq_support.Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Coq_support.Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Coq_support.Mo.Coq_mat.coq_VF t0 t0 ->
        Coq_support.Mo.Coq_mat.coq_VF t0
     end

    val coq_EPC :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Coq_support.Mo.Coq_mat.coq_VF ->
      Field.coq_F -> Commitment.coq_G

    val comEPC :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Coq_support.Mo.Coq_mat.coq_VF
      t0 -> Coq_support.Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val comEPCvec :
      nat -> nat -> Commitment.coq_G -> MoM.coq_VG -> Coq_support.Mo.Coq_mat.coq_VF
      -> Coq_support.Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val com :
      nat -> Commitment.coq_G -> MoM.coq_VG -> Coq_support.Mo.Coq_mat.coq_MF ->
      Coq_support.Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module ALenc :
   sig
    module AddVSLemmas :
     sig
      module AL :
       sig
       end
     end

    module Mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module MatG :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Ciphertext.coq_G t0

      val coq_VG_id : nat -> Ciphertext.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_scale_sum : nat -> nat -> nat -> Mat.coq_VF t0 t0 -> Mat.coq_VF t0
     end

    val reenc : Coq_enc.coq_PK -> Ciphertext.coq_G -> Ring.coq_F -> Ciphertext.coq_G

    val bIsReEnc :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Ciphertext.coq_G -> Ring.coq_F -> bool

    val decryptsToExt :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Coq_enc.coq_M -> Ring.coq_F -> bool
   end

  module ALR :
   sig
   end

  module G2 :
   sig
    type coq_G = Field.coq_F

    val coq_Gdot : coq_G -> coq_G -> coq_G

    val coq_Gone : coq_G

    val coq_Ggen : coq_G

    val coq_Gbool_eq : coq_G -> coq_G -> bool

    val coq_Gdisjoint : coq_G -> coq_G -> bool

    val coq_Ginv : coq_G -> coq_G
   end

  type coq_St = ((Commitment.coq_G * EPC.MoM.coq_VG) * EPC.MoM.coq_VG) * Field.coq_F

  type coq_W = Coq_support.Mo.Coq_mat.coq_VF t0 * Coq_support.Mo.Coq_mat.coq_VF

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C = Commitment.coq_G

  type coq_R = Field.coq_F

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_ToStSig : (coq_St * coq_C) -> Coq_sig.coq_St

  val coq_ToWitSig : (coq_St * coq_C) -> coq_R -> coq_W -> Coq_sig.coq_W

  val coq_ToStSig5 : (coq_St * coq_C) -> Coq_sig5.coq_St

  val coq_ToWitSig5 : (coq_St * coq_C) -> coq_R -> coq_W -> Coq_sig5.coq_W

  type coq_TE = Field.coq_F

  val extractor : Coq_sig5.coq_W -> Coq_sig.coq_W -> coq_W

  type coq_X = Coq_support.Mo.Coq_mat.coq_VF

  val simulator : coq_St -> coq_TE -> coq_C

  val simMap : coq_St -> coq_W -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> coq_X -> coq_TE -> coq_R

  val sigXcomp : coq_St -> coq_X -> Coq_sig.coq_X

  val sig5Xcomp : coq_St -> coq_X -> Coq_sig5.coq_X
 end) ->
 functor (Coq_progArg2:sig
  type coq_E0 = Coq_sig5.coq_E0 * Chal.coq_G

  type coq_E1 = Coq_sig5.coq_E1

  type coq_St = Coq_prodArg.coq_St

  type coq_W = Coq_prodArg.coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C0 = (Coq_prodArg.coq_C * Coq_sig5.coq_C0) * Coq_sig.coq_C

  type coq_C1 = Coq_sig5.coq_C1

  type coq_R0 = (Coq_prodArg.coq_R * Coq_sig5.coq_R0) * Coq_sig.coq_R

  type coq_R1 = Coq_sig5.coq_R1

  val add0 : coq_E0 -> coq_E0 -> coq_E0

  val zero0 : coq_E0

  val inv0 : coq_E0 -> coq_E0

  val bool_eq0 : coq_E0 -> coq_E0 -> bool

  val disjoint0 : coq_E0 -> coq_E0 -> bool

  val add1 : coq_E1 -> coq_E1 -> coq_E1

  val zero1 : coq_E1

  val inv1 : coq_E1 -> coq_E1

  val bool_eq1 : coq_E1 -> coq_E1 -> bool

  val disjoint1 : coq_E1 -> coq_E1 -> bool

  type coq_T = Coq_sig5.coq_T * Coq_sig.coq_T

  val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0

  val coq_P1 :
    ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
    ((coq_St * coq_C0) * coq_E0) * coq_C1

  val coq_P2 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) -> coq_W
    -> ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val coq_V2 : (((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T) -> bool

  type coq_TE0 = (Coq_prodArg.coq_TE * Coq_sig5.coq_TE0) * Coq_sig.coq_TE

  type coq_TE1 = Coq_sig5.coq_TE1

  type coq_X = Coq_prodArg.coq_X

  val simulator :
    coq_St -> (coq_TE0 * coq_TE1) -> (coq_E0 * coq_E1) ->
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val simMap :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_R0 * coq_R1) ->
    coq_TE0 * coq_TE1

  val simMapInv :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_TE0 * coq_TE1) ->
    coq_R0 * coq_R1

  val coq_M0 : nat

  val coq_M1 : nat

  val extractor : coq_T t0 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_W

  val allValid :
    coq_St -> coq_C0 -> coq_C1 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_T t0 t0 -> bool
 end) ->
 functor (Coq_bGMultiArg:sig
  val n : nat

  val m : nat

  type coq_St =
    (((((Coq_enc.coq_PK * Commitment.coq_G) * Coq_support.EPC.MoM.coq_VG) * Ciphertext.coq_G
    t0 t0) * Ciphertext.coq_G) * Coq_support.EPC.MoM.coq_VG) * Coq_enc.coq_M

  type coq_W =
    (Coq_support.Mo.Coq_mat.coq_VF t0 * Coq_support.Mo.Coq_mat.coq_VF) * Ring.coq_F

  type coq_R =
    (((Coq_support.Mo.Coq_mat.coq_VF * Field.coq_F) * (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF)) * (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF)) * (Ring.coq_F
    t0 * Ring.coq_F t0)

  type coq_C = (Commitment.coq_G * Coq_support.EPC.MoM.coq_VG) * Ciphertext.coq_G t0

  type coq_T =
    (((Coq_support.Mo.Coq_mat.coq_VF * Field.coq_F) * Field.coq_F) * Field.coq_F) * Ring.coq_F

  type coq_X =
    (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF t0) * Ring.coq_F
    t0 t0

  type coq_TE =
    ((((Coq_support.Mo.Coq_mat.coq_VF * Field.coq_F) * Field.coq_F) * Field.coq_F) * Ring.coq_F) * (((Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF) * (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF)) * (Ring.coq_F
    t0 * Ring.coq_F t0))

  val coq_Rel : coq_St -> coq_W -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_P1 :
    ((coq_St * coq_C) * Field.coq_F) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * Field.coq_F) * coq_T

  val coq_V1 : (((coq_St * coq_C) * Field.coq_F) * coq_T) -> bool

  val simMap : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_TE -> coq_R

  val simulator :
    coq_St -> coq_TE -> Field.coq_F -> ((coq_St * coq_C) * Field.coq_F) * coq_T

  val coq_M : nat

  val extractor : coq_T t0 -> Field.coq_F t0 -> coq_W

  val disjoint : Field.coq_F -> Field.coq_F -> bool

  val allDifferent : Field.coq_F t0 -> bool
 end) ->
 sig
  module G2 :
   sig
    type coq_G = Field.coq_F

    val coq_Gdot : coq_G -> coq_G -> coq_G

    val coq_Gone : coq_G

    val coq_Ggen : coq_G

    val coq_Gbool_eq : coq_G -> coq_G -> bool

    val coq_Gdisjoint : coq_G -> coq_G -> bool

    val coq_Ginv : coq_G -> coq_G
   end

  module Chal2 :
   sig
    type coq_G = G2.coq_G * Chal.coq_G

    val coq_Gdot : coq_G -> coq_G -> G2.coq_G * Chal.coq_G

    val coq_Gone : G2.coq_G * Chal.coq_G

    val coq_Ggen : G2.coq_G * Chal.coq_G

    val coq_Gbool_eq : coq_G -> coq_G -> bool

    val coq_Gdisjoint : coq_G -> coq_G -> bool

    val coq_Ginv : coq_G -> G2.coq_G * Chal.coq_G
   end

  val n : nat

  val m : nat

  module MP :
   sig
    module AddVSLemmas :
     sig
      module AL :
       sig
       end
     end

    module Mat :
     sig
      module F :
       sig
        type coq_A = Field.coq_F
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

        val eqA_dec : Field.coq_F -> Field.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : Field.coq_F -> Field.coq_F -> bool
         end

        val coq_A0 : Field.coq_F

        val coq_A1 : Field.coq_F

        val coq_Aplus : Field.coq_F -> Field.coq_F -> Field.coq_F

        val coq_Amult : Field.coq_F -> Field.coq_F -> Field.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = Field.coq_F t0

      val coq_VF_zero : nat -> Field.coq_F t0

      val coq_VF_one : nat -> Field.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> Field.coq_F

      val coq_VF_sum : nat -> coq_VF -> Field.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> Field.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Field.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> Field.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> Field.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module MatG :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = Ciphertext.coq_G t0

      val coq_VG_id : nat -> Ciphertext.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_scale_sum : nat -> nat -> nat -> Mat.coq_VF t0 t0 -> Mat.coq_VF t0
     end

    val reenc : Coq_enc.coq_PK -> Ciphertext.coq_G -> Ring.coq_F -> Ciphertext.coq_G

    val bIsReEnc :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Ciphertext.coq_G -> Ring.coq_F -> bool

    val decryptsToExt :
      Coq_enc.coq_PK -> Ciphertext.coq_G -> Coq_enc.coq_M -> Ring.coq_F -> bool
   end

  module ALR :
   sig
   end

  type coq_E0 = Chal.coq_G

  type coq_E1 = Chal2.coq_G

  val add0 : coq_E0 -> coq_E0 -> coq_E0

  val zero0 : coq_E0

  val inv0 : coq_E0 -> coq_E0

  val bool_eq0 : coq_E0 -> coq_E0 -> bool

  val disjoint0 : coq_E0 -> coq_E0 -> bool

  val add1 : coq_E1 -> coq_E1 -> coq_E1

  val zero1 : coq_E1

  val inv1 : coq_E1 -> coq_E1

  val bool_eq1 : coq_E1 -> coq_E1 -> bool

  val disjoint1 : coq_E1 -> coq_E1 -> bool

  type coq_St =
    (((Coq_enc.coq_PK * Commitment.coq_G) * Coq_support.EPC.MoM.coq_VG) * Ciphertext.coq_G
    t0) * Ciphertext.coq_G t0

  type coq_W = Coq_support.Mo.Coq_mat.coq_VF t0 * Ring.coq_F t0

  val relReEnc :
    Coq_enc.coq_PK -> Ciphertext.coq_G t0 -> Ciphertext.coq_G t0 ->
    Coq_support.Mo.Coq_mat.coq_MF -> Ring.coq_F t0 -> bool

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C0 = Coq_support.EPC.MoM.coq_VG

  type coq_C1 = Coq_support.EPC.MoM.coq_VG

  type coq_R0 = Coq_support.Mo.Coq_mat.coq_VF

  type coq_R1 = Coq_support.Mo.Coq_mat.coq_VF

  val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0

  val coq_P1 :
    ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
    ((coq_St * coq_C0) * coq_E0) * coq_C1

  val coq_ToStSig :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> Coq_bGMultiArg.coq_St

  val coq_ToWitSig :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) -> coq_W
    -> Coq_bGMultiArg.coq_W

  val coq_ToStSig5 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> Coq_progArg2.coq_St

  val coq_ToWitSig5 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) -> coq_W
    -> Coq_progArg2.coq_W

  type coq_TE0 = Coq_support.Mo.Coq_mat.coq_VF

  type coq_TE1 = Coq_support.Mo.Coq_mat.coq_VF

  type coq_X =
    (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF t0) * Ring.coq_F
    t0 t0

  val sigXcomp : coq_St -> coq_X -> Coq_bGMultiArg.coq_X

  val sig5Xcomp : coq_St -> coq_X -> Coq_progArg2.coq_X

  val simulator :
    coq_St -> (coq_TE0 * coq_TE1) -> (coq_E0 * coq_E1) -> coq_C0 * coq_C1

  val simMap :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_R0 * coq_R1) ->
    coq_TE0 * coq_TE1

  val simMapInv :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_TE0 * coq_TE1) ->
    coq_R0 * coq_R1

  val coq_M0 : nat

  val coq_M1 : nat

  val extractor :
    (Coq_progArg2.coq_W * Coq_bGMultiArg.coq_W) t0 t0 -> (coq_E0 * coq_E1 t0) t0 ->
    coq_W
 end

val pminusN : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val is_lt : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

val div_eucl0 :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int

val egcd_log2 :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  ((Big_int_Z.big_int * Big_int_Z.big_int) * Big_int_Z.big_int) option

val egcd :
  Big_int_Z.big_int -> Big_int_Z.big_int ->
  (Big_int_Z.big_int * Big_int_Z.big_int) * Big_int_Z.big_int

val zegcd :
  Big_int_Z.big_int -> Big_int_Z.big_int ->
  (Big_int_Z.big_int * Big_int_Z.big_int) * Big_int_Z.big_int

type znz = Big_int_Z.big_int
  (* singleton inductive, whose constructor was mkznz *)

val val1 : Big_int_Z.big_int -> znz -> Big_int_Z.big_int

val zero4 : Big_int_Z.big_int -> znz

val one0 : Big_int_Z.big_int -> znz

val add4 : Big_int_Z.big_int -> znz -> znz -> znz

val sub1 : Big_int_Z.big_int -> znz -> znz -> znz

val mul0 : Big_int_Z.big_int -> znz -> znz -> znz

val opp0 : Big_int_Z.big_int -> znz -> znz

val inv4 : Big_int_Z.big_int -> znz -> znz

val div0 : Big_int_Z.big_int -> znz -> znz -> znz

val p : Big_int_Z.big_int

val q : Big_int_Z.big_int

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

val binary_power_mult2 : fp -> Big_int_Z.big_int -> fp -> fp

val binary_power2 : fp -> f -> fp

type g = fp

val gdot : g -> g -> g

val gone : g

val gbool_eq_init : g -> g -> bool

val ginv : g -> g

val op0 : g -> f -> g

module HeliosIACR2018G :
 sig
  type coq_G = g

  val coq_Gdot : g -> g -> g

  val coq_Gone : g

  val coq_Ggen : g

  val coq_Gbool_eq : g -> g -> bool

  val coq_Gdisjoint : g -> g -> bool

  val coq_Ginv : g -> g
 end

module HeliosIACR2018F :
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

module HeliosIACR2018VS :
 sig
  val op : g -> f -> g
 end

module Ciphertext :
 sig
  type coq_G = HeliosIACR2018G.coq_G * HeliosIACR2018G.coq_G

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : HeliosIACR2018G.coq_G * HeliosIACR2018G.coq_G

  val coq_Ggen : HeliosIACR2018G.coq_G * HeliosIACR2018G.coq_G

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Gdisjoint : coq_G -> coq_G -> bool

  val coq_Ginv :
    (HeliosIACR2018G.coq_G * HeliosIACR2018G.coq_G) ->
    HeliosIACR2018G.coq_G * HeliosIACR2018G.coq_G
 end

module DVS :
 sig
  val op :
    Ciphertext.coq_G -> HeliosIACR2018F.coq_F ->
    HeliosIACR2018G.coq_G * HeliosIACR2018G.coq_G
 end

module MVS :
 sig
  val op3 : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F
 end

module Chal :
 sig
  type coq_G = HeliosIACR2018F.coq_F

  val coq_Gdot :
    HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F

  val coq_Gone : HeliosIACR2018F.coq_F

  val coq_Ggen : HeliosIACR2018F.coq_F

  val coq_Gbool_eq : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool

  val coq_Gdisjoint : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool

  val coq_Ginv : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F
 end

module L :
 sig
  val coq_N : nat
 end

module NGroupM :
 sig
  type coq_G = HeliosIACR2018G.coq_G t0

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : HeliosIACR2018G.coq_G t0

  val coq_Ggen : HeliosIACR2018G.coq_G t0

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Gdisjoint : coq_G -> coq_G -> bool

  val coq_Ginv : coq_G -> HeliosIACR2018G.coq_G t0
 end

module NGroupC :
 sig
  type coq_G = Ciphertext.coq_G t0

  val coq_Gdot : coq_G -> coq_G -> coq_G

  val coq_Gone : Ciphertext.coq_G t0

  val coq_Ggen : Ciphertext.coq_G t0

  val coq_Gbool_eq : coq_G -> coq_G -> bool

  val coq_Gdisjoint : coq_G -> coq_G -> bool

  val coq_Ginv : coq_G -> Ciphertext.coq_G t0
 end

module Nthring :
 sig
  type coq_F = HeliosIACR2018F.coq_F t0

  val coq_Fadd : coq_F -> coq_F -> HeliosIACR2018F.coq_F t0

  val coq_Fzero : HeliosIACR2018F.coq_F t0

  val coq_Fbool_eq : coq_F -> coq_F -> bool

  val coq_Fsub : coq_F -> coq_F -> HeliosIACR2018F.coq_F t0

  val coq_Finv : coq_F -> HeliosIACR2018F.coq_F t0

  val coq_Fmul : coq_F -> coq_F -> HeliosIACR2018F.coq_F t0

  val coq_Fone : HeliosIACR2018F.coq_F t0
 end

module Nthvs :
 sig
  module MatF :
   sig
    module F :
     sig
      type coq_A = HeliosIACR2018F.coq_F
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

      val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
     end

    module FSemiRingT :
     sig
      module ES :
       sig
        module Eq :
         sig
          type coq_A = F.coq_A
         end

        val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
       end

      val coq_A0 : HeliosIACR2018F.coq_F

      val coq_A1 : HeliosIACR2018F.coq_F

      val coq_Aplus :
        HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F

      val coq_Amult :
        HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = HeliosIACR2018F.coq_F t0

    val coq_VF_zero : nat -> HeliosIACR2018F.coq_F t0

    val coq_VF_one : nat -> HeliosIACR2018F.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val coq_VF_prod : nat -> coq_VF -> HeliosIACR2018F.coq_F

    val coq_VF_sum : nat -> coq_VF -> HeliosIACR2018F.coq_F

    val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_neg : nat -> coq_VF -> coq_VF

    val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_scale : nat -> coq_VF -> HeliosIACR2018F.coq_F -> coq_VF

    val coq_VF_inProd : nat -> coq_VF -> coq_VF -> HeliosIACR2018F.coq_F

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

    val coq_MF_scal : nat -> coq_MF -> HeliosIACR2018F.coq_F -> coq_MF

    val coq_MFisPermutation : nat -> coq_MF -> bool

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> HeliosIACR2018F.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module Mat :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Ciphertext.coq_G t0

    val coq_VG_id : nat -> Ciphertext.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Ciphertext.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> MatF.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> HeliosIACR2018F.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_VG_scale_sum : nat -> nat -> nat -> MatF.coq_VF t0 t0 -> MatF.coq_VF t0
   end

  val op : NGroupC.coq_G -> HeliosIACR2018F.coq_F -> Mat.coq_VG
 end

module NthvsM :
 sig
  module MatF :
   sig
    module F :
     sig
      type coq_A = HeliosIACR2018F.coq_F
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

      val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
     end

    module FSemiRingT :
     sig
      module ES :
       sig
        module Eq :
         sig
          type coq_A = F.coq_A
         end

        val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
       end

      val coq_A0 : HeliosIACR2018F.coq_F

      val coq_A1 : HeliosIACR2018F.coq_F

      val coq_Aplus :
        HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F

      val coq_Amult :
        HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = HeliosIACR2018F.coq_F t0

    val coq_VF_zero : nat -> HeliosIACR2018F.coq_F t0

    val coq_VF_one : nat -> HeliosIACR2018F.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val coq_VF_prod : nat -> coq_VF -> HeliosIACR2018F.coq_F

    val coq_VF_sum : nat -> coq_VF -> HeliosIACR2018F.coq_F

    val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_neg : nat -> coq_VF -> coq_VF

    val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_scale : nat -> coq_VF -> HeliosIACR2018F.coq_F -> coq_VF

    val coq_VF_inProd : nat -> coq_VF -> coq_VF -> HeliosIACR2018F.coq_F

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

    val coq_MF_scal : nat -> coq_MF -> HeliosIACR2018F.coq_F -> coq_MF

    val coq_MFisPermutation : nat -> coq_MF -> bool

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> HeliosIACR2018F.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module Mat :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = HeliosIACR2018G.coq_G t0

    val coq_VG_id : nat -> HeliosIACR2018G.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> HeliosIACR2018G.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> MatF.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> HeliosIACR2018F.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> MatF.coq_MF -> coq_VG

    val coq_VG_scale_sum : nat -> nat -> nat -> MatF.coq_VF t0 t0 -> MatF.coq_VF t0
   end

  val op : NGroupM.coq_G -> HeliosIACR2018F.coq_F -> Mat.coq_VG
 end

module NthMVS :
 sig
  val op3 : Nthring.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F t0
 end

module Enc :
 sig
  module Mo :
   sig
    module F :
     sig
      type coq_A = HeliosIACR2018F.coq_F
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

      val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
     end

    module FSemiRingT :
     sig
      module ES :
       sig
        module Eq :
         sig
          type coq_A = F.coq_A
         end

        val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
       end

      val coq_A0 : HeliosIACR2018F.coq_F

      val coq_A1 : HeliosIACR2018F.coq_F

      val coq_Aplus :
        HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F

      val coq_Amult :
        HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = HeliosIACR2018F.coq_F t0

    val coq_VF_zero : nat -> HeliosIACR2018F.coq_F t0

    val coq_VF_one : nat -> HeliosIACR2018F.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val coq_VF_prod : nat -> coq_VF -> HeliosIACR2018F.coq_F

    val coq_VF_sum : nat -> coq_VF -> HeliosIACR2018F.coq_F

    val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_neg : nat -> coq_VF -> coq_VF

    val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_scale : nat -> coq_VF -> HeliosIACR2018F.coq_F -> coq_VF

    val coq_VF_inProd : nat -> coq_VF -> coq_VF -> HeliosIACR2018F.coq_F

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

    val coq_MF_scal : nat -> coq_MF -> HeliosIACR2018F.coq_F -> coq_MF

    val coq_MFisPermutation : nat -> coq_MF -> bool

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> HeliosIACR2018F.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module MoM :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = HeliosIACR2018G.coq_G t0

    val coq_VG_id : nat -> HeliosIACR2018G.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> HeliosIACR2018G.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> HeliosIACR2018F.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.coq_MF -> coq_VG

    val coq_VG_scale_sum : nat -> nat -> nat -> Mo.coq_VF t0 t0 -> Mo.coq_VF t0
   end

  module AddVSLemmas :
   sig
    module AL :
     sig
     end
   end

  type coq_KGR = MoM.coq_VG * Mo.coq_VF

  type coq_PK = NGroupC.coq_G

  type coq_SK = Mo.coq_VF

  type coq_M = NGroupM.coq_G

  val coq_Mop : NGroupM.coq_G -> NGroupM.coq_G -> NGroupM.coq_G

  val coq_Mzero : HeliosIACR2018G.coq_G t0

  val coq_Mone : HeliosIACR2018G.coq_G t0

  val coq_Minv : NGroupM.coq_G -> HeliosIACR2018G.coq_G t0

  val coq_Mbool_eq : NGroupM.coq_G -> NGroupM.coq_G -> bool

  val keygen : coq_KGR -> coq_PK * coq_SK

  val keygenMix : coq_KGR -> coq_PK

  val enc : coq_PK -> coq_M -> Mo.coq_VF -> NGroupC.coq_G

  val dec : coq_SK -> NGroupC.coq_G -> coq_M

  val keymatch : coq_PK -> coq_SK -> bool
 end

module N :
 sig
  val coq_N : nat
 end

module M :
 sig
  val coq_N : nat
 end

module Support :
 sig
  val n : nat

  val m : nat

  module Mo :
   sig
    module Coq_mat :
     sig
      module F :
       sig
        type coq_A = HeliosIACR2018F.coq_F
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

        val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
         end

        val coq_A0 : HeliosIACR2018F.coq_F

        val coq_A1 : HeliosIACR2018F.coq_F

        val coq_Aplus :
          HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F

        val coq_Amult :
          HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = HeliosIACR2018F.coq_F t0

      val coq_VF_zero : nat -> HeliosIACR2018F.coq_F t0

      val coq_VF_one : nat -> HeliosIACR2018F.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> HeliosIACR2018F.coq_F

      val coq_VF_sum : nat -> coq_VF -> HeliosIACR2018F.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> HeliosIACR2018F.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> HeliosIACR2018F.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> HeliosIACR2018F.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> HeliosIACR2018F.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module AL :
     sig
     end

    module FAL :
     sig
      module AL :
       sig
       end
     end

    val coq_VandermondeCol : nat -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F t0

    val coq_VandermondeColGen :
      nat -> HeliosIACR2018F.coq_F -> nat -> HeliosIACR2018F.coq_F t0

    val coq_Vandermonde : nat -> Coq_mat.coq_VF -> HeliosIACR2018F.coq_F t0 t0

    module SSRfield :
     sig
      module AL :
       sig
       end

      type coq_R = HeliosIACR2018F.coq_F

      val eqr : coq_R -> coq_R -> bool

      val eqrP : coq_R Equality.axiom

      val coq_R_eqMixin : coq_R Equality.mixin_of

      val coq_R_eqType : Equality.coq_type

      val pickR : coq_R pred0 -> nat -> coq_R option

      val coq_R_choiceMixin : coq_R Choice.mixin_of

      val coq_R_choiceType : Choice.coq_type

      val coq_R_zmodmixin : HeliosIACR2018F.coq_F GRing.Zmodule.mixin_of

      val coq_R_zmodtype : GRing.Zmodule.coq_type

      val coq_R_comringmixin : GRing.Ring.mixin_of

      val coq_R_ring : GRing.Ring.coq_type

      val coq_R_comring : GRing.ComRing.coq_type

      val coq_Radd_monoid : HeliosIACR2018F.coq_F Monoid.law

      val coq_Radd_comoid : HeliosIACR2018F.coq_F Monoid.com_law

      val coq_Rmul_monoid : GRing.Zmodule.sort Monoid.law

      val coq_Rmul_comoid : HeliosIACR2018F.coq_F Monoid.com_law

      val coq_Rmul_mul_law : HeliosIACR2018F.coq_F Monoid.mul_law

      val coq_Radd_add_law : HeliosIACR2018F.coq_F Monoid.add_law

      val coq_Rinvx : coq_R -> HeliosIACR2018F.coq_F

      val unit_R : coq_R -> bool

      val coq_R_unitRingMixin : GRing.UnitRing.mixin_of

      val coq_R_unitRing : GRing.UnitRing.coq_type

      val coq_R_comUnitRingType : GRing.ComUnitRing.coq_type

      val coq_R_idomainType : GRing.IntegralDomain.coq_type

      val coq_R_field : GRing.Field.coq_type
     end

    val coq_VandermondeInv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_MF

    val nat_to_ord : nat -> nat -> ordinal

    val coq_VF_inv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_VF
   end

  module MoR :
   sig
    module F :
     sig
      type coq_A = Nthring.coq_F
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

      val eqA_dec : Nthring.coq_F -> Nthring.coq_F -> bool
     end

    module FSemiRingT :
     sig
      module ES :
       sig
        module Eq :
         sig
          type coq_A = F.coq_A
         end

        val eqA_dec : Nthring.coq_F -> Nthring.coq_F -> bool
       end

      val coq_A0 : Nthring.coq_F

      val coq_A1 : Nthring.coq_F

      val coq_Aplus : Nthring.coq_F -> Nthring.coq_F -> Nthring.coq_F

      val coq_Amult : Nthring.coq_F -> Nthring.coq_F -> Nthring.coq_F
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

        val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

        val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val vector_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val add_vectors :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

        val dot_product :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A
       end

      type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

      val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

      val mat_build_spec :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val mat_build :
        nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

      val zero_matrix : nat -> nat -> matrix

      val id_matrix : nat -> matrix

      val inverse_matrix :
        (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
        -> matrix

      type row_mat = matrix

      type col_mat = matrix

      val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

      val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

      val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

      val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

      val mat_transpose : nat -> nat -> matrix -> matrix

      val vec_plus :
        nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
        FSemiRingT.ES.Eq.coq_A t0

      val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

      val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

      val mat_vec_prod :
        nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A
        t0

      val mat_forall2'_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

      val mat_forall2_dec :
        nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
     end

    module ALR :
     sig
     end

    type coq_VF = Nthring.coq_F t0

    val coq_VF_zero : nat -> Nthring.coq_F t0

    val coq_VF_one : nat -> Nthring.coq_F t0

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

    val coq_VF_prod : nat -> coq_VF -> Nthring.coq_F

    val coq_VF_sum : nat -> coq_VF -> Nthring.coq_F

    val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_neg : nat -> coq_VF -> coq_VF

    val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_scale : nat -> coq_VF -> Nthring.coq_F -> coq_VF

    val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Nthring.coq_F

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

    val coq_MF_scal : nat -> coq_MF -> Nthring.coq_F -> coq_MF

    val coq_MFisPermutation : nat -> coq_MF -> bool

    val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

    val coq_MF_perm_last : nat -> coq_MF -> index

    val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

    val matRecover_sub : nat -> Nthring.coq_F -> nat

    val matRecover : nat -> coq_VF -> coq_MF
   end

  module MoC :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = NGroupC.coq_G t0

    val coq_VG_id : nat -> NGroupC.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> NGroupC.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> HeliosIACR2018F.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
   end

  module EPC :
   sig
    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = HeliosIACR2018G.coq_G t0

      val coq_VG_id : nat -> HeliosIACR2018G.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> HeliosIACR2018G.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> HeliosIACR2018F.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_EPC :
      nat -> HeliosIACR2018G.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF ->
      HeliosIACR2018F.coq_F -> HeliosIACR2018G.coq_G

    val comEPC :
      nat -> nat -> HeliosIACR2018G.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF t0 ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val comEPCvec :
      nat -> nat -> HeliosIACR2018G.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val com :
      nat -> HeliosIACR2018G.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_MF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module PC :
   sig
    module AddMLemmas :
     sig
     end

    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = HeliosIACR2018G.coq_G t0

      val coq_VG_id : nat -> HeliosIACR2018G.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> HeliosIACR2018G.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> HeliosIACR2018F.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_PC :
      HeliosIACR2018G.coq_G -> HeliosIACR2018G.coq_G -> HeliosIACR2018F.coq_F ->
      HeliosIACR2018F.coq_F -> HeliosIACR2018G.coq_G

    val comPC :
      nat -> HeliosIACR2018G.coq_G -> HeliosIACR2018G.coq_G -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module MoM :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = NGroupM.coq_G t0

    val coq_VG_id : nat -> NGroupM.coq_G t0

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> NGroupM.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> HeliosIACR2018F.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
   end

  module ALVS1 :
   sig
    module AL :
     sig
     end
   end

  module ALVS2 :
   sig
    module AL :
     sig
     end
   end

  module ALVS3 :
   sig
    module AL :
     sig
     end
   end

  module ALenc :
   sig
    module AddVSLemmas :
     sig
      module AL :
       sig
       end
     end

    module Mat :
     sig
      module F :
       sig
        type coq_A = HeliosIACR2018F.coq_F
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

        val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
         end

        val coq_A0 : HeliosIACR2018F.coq_F

        val coq_A1 : HeliosIACR2018F.coq_F

        val coq_Aplus :
          HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F

        val coq_Amult :
          HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = HeliosIACR2018F.coq_F t0

      val coq_VF_zero : nat -> HeliosIACR2018F.coq_F t0

      val coq_VF_one : nat -> HeliosIACR2018F.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> HeliosIACR2018F.coq_F

      val coq_VF_sum : nat -> coq_VF -> HeliosIACR2018F.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> HeliosIACR2018F.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> HeliosIACR2018F.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> HeliosIACR2018F.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> HeliosIACR2018F.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module MatG :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = NGroupC.coq_G t0

      val coq_VG_id : nat -> NGroupC.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> NGroupC.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> HeliosIACR2018F.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_scale_sum : nat -> nat -> nat -> Mat.coq_VF t0 t0 -> Mat.coq_VF t0
     end

    val reenc : Enc.coq_PK -> NGroupC.coq_G -> Nthring.coq_F -> NGroupC.coq_G

    val bIsReEnc :
      Enc.coq_PK -> NGroupC.coq_G -> NGroupC.coq_G -> Nthring.coq_F -> bool

    val decryptsToExt :
      Enc.coq_PK -> NGroupC.coq_G -> Enc.coq_M -> Nthring.coq_F -> bool
   end

  module HardProb :
   sig
    val dLog :
      (HeliosIACR2018G.coq_G * HeliosIACR2018G.coq_G) -> HeliosIACR2018F.coq_F ->
      bool
   end

  module ALR :
   sig
   end

  val coq_ProdOfDiagonals : 'a1 -> ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 t0 t0 -> 'a1 t0

  val coq_ProdOfDiagonalsF :
    nat -> HeliosIACR2018F.coq_F t0 t0 -> HeliosIACR2018F.coq_F t0

  val coq_ProdOfDiagonalsVF :
    nat -> nat -> HeliosIACR2018F.coq_F t0 t0 t0 -> HeliosIACR2018F.coq_F t0 t0

  val coq_ProdOfDiagonalsG :
    nat -> HeliosIACR2018G.coq_G t0 t0 -> HeliosIACR2018G.coq_G t0

  val coq_RF_inProd : nat -> Mo.Coq_mat.coq_VF -> MoR.coq_VF -> Nthring.coq_F

  val coq_RF_VCmult : nat -> Mo.Coq_mat.coq_MF -> MoR.coq_VF -> MoR.coq_VF

  val coq_WeirdCs :
    nat -> nat -> NGroupC.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG

  val coq_EkGeneratorsSub :
    nat -> NGroupC.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG

  val coq_EkGeneratorsSubAlt :
    nat -> NGroupC.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
    MoC.coq_VG

  val coq_EkGenerators :
    Enc.coq_PK -> nat -> Enc.coq_M -> NGroupC.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 ->
    Nthring.coq_F t0 -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF -> NGroupC.coq_G t0

  val coq_EkGeneratorsSubRawM :
    nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF

  val coq_EkGeneratorsSubRawR :
    nat -> Nthring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Nthring.coq_F t0

  val coq_EkGeneratorsRawM :
    nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
    Mo.Coq_mat.coq_VF

  val coq_EkGeneratorsRawR :
    nat -> Nthring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Nthring.coq_F t0 ->
    MoR.coq_VF

  val makeSVectors : nat -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF t0
 end

module BGZeroarg :
 sig
  val n : nat

  val m : nat

  module ALR :
   sig
   end

  val coq_BM :
    HeliosIACR2018F.coq_F -> Support.Mo.Coq_mat.coq_VF -> Support.Mo.Coq_mat.coq_VF
    -> HeliosIACR2018F.coq_F

  type coq_St =
    (((HeliosIACR2018G.coq_G * Support.EPC.MoM.coq_VG) * HeliosIACR2018F.coq_F) * Support.EPC.MoM.coq_VG) * Support.EPC.MoM.coq_VG

  type coq_W =
    ((Support.Mo.Coq_mat.coq_VF
    t0 * Support.Mo.Coq_mat.coq_VF) * Support.Mo.Coq_mat.coq_VF
    t0) * Support.Mo.Coq_mat.coq_VF

  type coq_R =
    (((Support.Mo.Coq_mat.coq_VF * Support.Mo.Coq_mat.coq_VF) * HeliosIACR2018F.coq_F) * HeliosIACR2018F.coq_F) * (Support.Mo.Coq_mat.coq_VF * Support.Mo.Coq_mat.coq_VF)

  type coq_C =
    (HeliosIACR2018G.coq_G * HeliosIACR2018G.coq_G) * Support.EPC.MoM.coq_VG

  type coq_T =
    (((Support.Mo.Coq_mat.coq_VF * HeliosIACR2018F.coq_F) * Support.Mo.Coq_mat.coq_VF) * HeliosIACR2018F.coq_F) * HeliosIACR2018F.coq_F

  type coq_X = Support.Mo.Coq_mat.coq_VF

  type coq_TE =
    ((((Support.Mo.Coq_mat.coq_VF * HeliosIACR2018F.coq_F) * Support.Mo.Coq_mat.coq_VF) * HeliosIACR2018F.coq_F) * HeliosIACR2018F.coq_F) * (Support.Mo.Coq_mat.coq_VF * Support.Mo.Coq_mat.coq_VF)

  val coq_Rel : coq_St -> coq_W -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_V0 :
    (coq_St * coq_C) -> HeliosIACR2018F.coq_F ->
    (coq_St * coq_C) * HeliosIACR2018F.coq_F

  val coq_P1 :
    ((coq_St * coq_C) * HeliosIACR2018F.coq_F) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * HeliosIACR2018F.coq_F) * coq_T

  val coq_V1 : (((coq_St * coq_C) * HeliosIACR2018F.coq_F) * coq_T) -> bool

  val simMap : coq_St -> coq_W -> HeliosIACR2018F.coq_F -> coq_X -> coq_R -> coq_TE

  val simMapInv :
    coq_St -> coq_W -> HeliosIACR2018F.coq_F -> coq_X -> coq_TE -> coq_R

  val simulator :
    coq_St -> coq_TE -> HeliosIACR2018F.coq_F ->
    ((coq_St * coq_C) * HeliosIACR2018F.coq_F) * coq_T

  val extractor : coq_T t0 -> HeliosIACR2018F.coq_F t0 -> coq_W

  val coq_M : nat

  val allDifferent : Chal.coq_G t0 -> bool
 end

module BGHadprodbase :
 sig
  val n : nat

  val m : nat

  module ALR :
   sig
   end

  module G2 :
   sig
    type coq_G = HeliosIACR2018F.coq_F

    val coq_Gdot : coq_G -> coq_G -> coq_G

    val coq_Gone : coq_G

    val coq_Ggen : coq_G

    val coq_Gbool_eq : coq_G -> coq_G -> bool

    val coq_Gdisjoint : coq_G -> coq_G -> bool

    val coq_Ginv : coq_G -> coq_G
   end

  type coq_E = G2.coq_G * HeliosIACR2018F.coq_F

  type coq_St =
    ((HeliosIACR2018G.coq_G * Support.EPC.MoM.coq_VG) * Support.EPC.MoM.coq_VG) * HeliosIACR2018G.coq_G

  type coq_W =
    ((Support.Mo.Coq_mat.coq_VF
    t0 * Support.Mo.Coq_mat.coq_VF) * Support.Mo.Coq_mat.coq_VF) * HeliosIACR2018F.coq_F

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C = Support.EPC.MoM.coq_VG

  type coq_R = Support.Mo.Coq_mat.coq_VF

  val add : coq_E -> coq_E -> G2.coq_G * HeliosIACR2018F.coq_F

  val zero : G2.coq_G * HeliosIACR2018F.coq_F

  val inv : coq_E -> G2.coq_G * HeliosIACR2018F.coq_F

  val bool_eq : coq_E -> coq_E -> bool

  val disjoint : coq_E -> coq_E -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_ToSt : ((coq_St * coq_C) * coq_E) -> BGZeroarg.coq_St

  val coq_ToWit : ((coq_St * coq_C) * coq_E) -> coq_R -> coq_W -> BGZeroarg.coq_W

  type coq_TE = Support.Mo.Coq_mat.coq_VF

  val extractor : BGZeroarg.coq_W -> coq_E -> coq_W

  type coq_X = BGZeroarg.coq_X

  val simulator : coq_St -> coq_TE -> coq_E -> coq_C

  val simMap : coq_St -> coq_W -> coq_E -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> coq_E -> coq_X -> coq_TE -> coq_R

  val sigXcomp : coq_St -> coq_X -> BGZeroarg.coq_X
 end

module BGHadprod :
 sig
  type coq_E = BGHadprodbase.coq_E

  type coq_St = BGHadprodbase.coq_St

  type coq_W = BGHadprodbase.coq_W

  val coq_Rel : BGHadprodbase.coq_St -> BGHadprodbase.coq_W -> bool

  type coq_C = BGHadprodbase.coq_C

  type coq_R = BGHadprodbase.coq_R

  val add : BGHadprodbase.coq_E -> BGHadprodbase.coq_E -> BGHadprodbase.coq_E

  val zero : coq_E

  val inv : coq_E -> coq_E

  val bool_eq : coq_E -> coq_E -> bool

  val disjoint : coq_E -> coq_E -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  type coq_C1 = unit

  type coq_R1 = unit

  val coq_P1 :
    ((coq_St * coq_C) * coq_E) -> coq_R1 -> coq_W ->
    ((coq_St * coq_C) * coq_E) * coq_C1

  val coq_ToSt : (((coq_St * coq_C) * coq_E) * coq_C1) -> BGZeroarg.coq_St

  val coq_ToWit :
    ((coq_St * coq_C) * coq_E) -> coq_R -> coq_R1 -> coq_W -> BGZeroarg.coq_W

  type coq_TE = BGHadprodbase.coq_TE

  val coq_M : nat

  val extractor : BGZeroarg.coq_W t0 -> coq_E t0 -> coq_W

  type coq_X = BGHadprodbase.coq_X

  val simulator : coq_St -> coq_TE -> coq_E -> coq_C * coq_C1

  val simMap : coq_St -> coq_W -> coq_E -> coq_X -> (coq_R * coq_R1) -> coq_TE

  val simMapInv : coq_St -> coq_W -> coq_E -> coq_X -> coq_TE -> coq_R * coq_R1

  val sigXcomp : coq_St -> coq_X -> BGZeroarg.coq_X
 end

module Coq_sig5 :
 sig
  type coq_E0 = BGHadprod.coq_E

  type coq_E1 = Chal.coq_G

  type coq_St = BGHadprod.coq_St

  type coq_W = BGHadprod.coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C0 = BGHadprod.coq_C

  type coq_C1 = BGHadprod.coq_C1 * BGZeroarg.coq_C

  type coq_R0 = BGHadprod.coq_R

  type coq_R1 = BGHadprod.coq_R1 * BGZeroarg.coq_R

  val add0 : coq_E0 -> coq_E0 -> coq_E0

  val zero0 : coq_E0

  val inv0 : coq_E0 -> coq_E0

  val bool_eq0 : coq_E0 -> coq_E0 -> bool

  val disjoint0 : coq_E0 -> coq_E0 -> bool

  val add1 : coq_E1 -> coq_E1 -> coq_E1

  val zero1 : coq_E1

  val inv1 : coq_E1 -> coq_E1

  val bool_eq1 : coq_E1 -> coq_E1 -> bool

  val disjoint1 : coq_E1 -> coq_E1 -> bool

  type coq_T = BGZeroarg.coq_T

  val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0

  val coq_P1 :
    ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
    ((coq_St * coq_C0) * coq_E0) * coq_C1

  val coq_P2 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) -> coq_W
    -> ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val coq_V2 : (((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T) -> bool

  type coq_TE0 = BGHadprod.coq_TE

  type coq_TE1 = BGZeroarg.coq_TE

  type coq_X = BGHadprod.coq_X

  val simulator :
    coq_St -> (coq_TE0 * coq_TE1) -> (coq_E0 * coq_E1) ->
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val simMap :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_R0 * coq_R1) ->
    coq_TE0 * coq_TE1

  val simMapInv :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_TE0 * coq_TE1) ->
    coq_R0 * coq_R1

  val coq_M0 : nat

  val coq_M1 : nat

  val extractor : coq_T t0 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_W

  val allValid :
    coq_St -> coq_C0 -> coq_C1 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_T t0 t0 -> bool
 end

module Coq_sig :
 sig
  val n : nat

  module Mo :
   sig
    module Coq_mat :
     sig
      module F :
       sig
        type coq_A = HeliosIACR2018F.coq_F
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

        val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
         end

        val coq_A0 : HeliosIACR2018F.coq_F

        val coq_A1 : HeliosIACR2018F.coq_F

        val coq_Aplus :
          HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F

        val coq_Amult :
          HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = HeliosIACR2018F.coq_F t0

      val coq_VF_zero : nat -> HeliosIACR2018F.coq_F t0

      val coq_VF_one : nat -> HeliosIACR2018F.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> HeliosIACR2018F.coq_F

      val coq_VF_sum : nat -> coq_VF -> HeliosIACR2018F.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> HeliosIACR2018F.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> HeliosIACR2018F.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> HeliosIACR2018F.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> HeliosIACR2018F.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module AL :
     sig
     end

    module FAL :
     sig
      module AL :
       sig
       end
     end

    val coq_VandermondeCol : nat -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F t0

    val coq_VandermondeColGen :
      nat -> HeliosIACR2018F.coq_F -> nat -> HeliosIACR2018F.coq_F t0

    val coq_Vandermonde : nat -> Coq_mat.coq_VF -> HeliosIACR2018F.coq_F t0 t0

    module SSRfield :
     sig
      module AL :
       sig
       end

      type coq_R = HeliosIACR2018F.coq_F

      val eqr : coq_R -> coq_R -> bool

      val eqrP : coq_R Equality.axiom

      val coq_R_eqMixin : coq_R Equality.mixin_of

      val coq_R_eqType : Equality.coq_type

      val pickR : coq_R pred0 -> nat -> coq_R option

      val coq_R_choiceMixin : coq_R Choice.mixin_of

      val coq_R_choiceType : Choice.coq_type

      val coq_R_zmodmixin : HeliosIACR2018F.coq_F GRing.Zmodule.mixin_of

      val coq_R_zmodtype : GRing.Zmodule.coq_type

      val coq_R_comringmixin : GRing.Ring.mixin_of

      val coq_R_ring : GRing.Ring.coq_type

      val coq_R_comring : GRing.ComRing.coq_type

      val coq_Radd_monoid : HeliosIACR2018F.coq_F Monoid.law

      val coq_Radd_comoid : HeliosIACR2018F.coq_F Monoid.com_law

      val coq_Rmul_monoid : GRing.Zmodule.sort Monoid.law

      val coq_Rmul_comoid : HeliosIACR2018F.coq_F Monoid.com_law

      val coq_Rmul_mul_law : HeliosIACR2018F.coq_F Monoid.mul_law

      val coq_Radd_add_law : HeliosIACR2018F.coq_F Monoid.add_law

      val coq_Rinvx : coq_R -> HeliosIACR2018F.coq_F

      val unit_R : coq_R -> bool

      val coq_R_unitRingMixin : GRing.UnitRing.mixin_of

      val coq_R_unitRing : GRing.UnitRing.coq_type

      val coq_R_comUnitRingType : GRing.ComUnitRing.coq_type

      val coq_R_idomainType : GRing.IntegralDomain.coq_type

      val coq_R_field : GRing.Field.coq_type
     end

    val coq_VandermondeInv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_MF

    val nat_to_ord : nat -> nat -> ordinal

    val coq_VF_inv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_VF
   end

  module EPC :
   sig
    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = HeliosIACR2018G.coq_G t0

      val coq_VG_id : nat -> HeliosIACR2018G.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> HeliosIACR2018G.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> HeliosIACR2018F.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_EPC :
      nat -> HeliosIACR2018G.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF ->
      HeliosIACR2018F.coq_F -> HeliosIACR2018G.coq_G

    val comEPC :
      nat -> nat -> HeliosIACR2018G.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF t0 ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val comEPCvec :
      nat -> nat -> HeliosIACR2018G.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val com :
      nat -> HeliosIACR2018G.coq_G -> MoM.coq_VG -> Mo.Coq_mat.coq_MF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module PC :
   sig
    module AddMLemmas :
     sig
     end

    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = HeliosIACR2018G.coq_G t0

      val coq_VG_id : nat -> HeliosIACR2018G.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> HeliosIACR2018G.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> HeliosIACR2018F.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Mo.Coq_mat.coq_VF t0 t0 -> Mo.Coq_mat.coq_VF t0
     end

    val coq_PC :
      HeliosIACR2018G.coq_G -> HeliosIACR2018G.coq_G -> HeliosIACR2018F.coq_F ->
      HeliosIACR2018F.coq_F -> HeliosIACR2018G.coq_G

    val comPC :
      nat -> HeliosIACR2018G.coq_G -> HeliosIACR2018G.coq_G -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module HardProb :
   sig
    val dLog :
      (HeliosIACR2018G.coq_G * HeliosIACR2018G.coq_G) -> HeliosIACR2018F.coq_F ->
      bool
   end

  module RAL :
   sig
   end

  type coq_St =
    ((HeliosIACR2018G.coq_G * EPC.MoM.coq_VG) * HeliosIACR2018G.coq_G) * HeliosIACR2018F.coq_F

  type coq_W = Mo.Coq_mat.coq_VF * HeliosIACR2018F.coq_F

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C =
    (HeliosIACR2018G.coq_G * HeliosIACR2018G.coq_G) * HeliosIACR2018G.coq_G

  type coq_R =
    (((Mo.Coq_mat.coq_VF * HeliosIACR2018F.coq_F) * Mo.Coq_mat.coq_VF) * HeliosIACR2018F.coq_F) * HeliosIACR2018F.coq_F

  type coq_T =
    ((Mo.Coq_mat.coq_VF * Mo.Coq_mat.coq_VF) * HeliosIACR2018F.coq_F) * HeliosIACR2018F.coq_F

  val vecb : Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_P1 :
    ((coq_St * coq_C) * HeliosIACR2018F.coq_F) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * HeliosIACR2018F.coq_F) * coq_T

  val coq_V1 : (((coq_St * coq_C) * HeliosIACR2018F.coq_F) * coq_T) -> bool

  type coq_TE =
    (((Mo.Coq_mat.coq_VF * HeliosIACR2018F.coq_F) * Mo.Coq_mat.coq_VF) * HeliosIACR2018F.coq_F) * HeliosIACR2018F.coq_F

  type coq_X = Mo.Coq_mat.coq_VF

  val simulator :
    coq_St -> coq_TE -> HeliosIACR2018F.coq_F ->
    ((coq_St * coq_C) * HeliosIACR2018F.coq_F) * coq_T

  val simMap : coq_St -> coq_W -> HeliosIACR2018F.coq_F -> coq_X -> coq_R -> coq_TE

  val simMapInv :
    coq_St -> coq_W -> HeliosIACR2018F.coq_F -> coq_X -> coq_TE -> coq_R

  val coq_M : nat

  val extractor : coq_T t0 -> HeliosIACR2018F.coq_F t0 -> coq_W

  val coq_Polynomial :
    nat -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF -> HeliosIACR2018F.coq_F ->
    Mo.Coq_mat.coq_VF -> HeliosIACR2018F.coq_F

  val allDifferent : HeliosIACR2018F.coq_F t0 -> bool
 end

module Coq_prodarg :
 sig
  val n : nat

  val m : nat

  module EPC :
   sig
    module MoM :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = HeliosIACR2018G.coq_G t0

      val coq_VG_id : nat -> HeliosIACR2018G.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> HeliosIACR2018G.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Support.Mo.Coq_mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> HeliosIACR2018F.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Support.Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Support.Mo.Coq_mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Support.Mo.Coq_mat.coq_MF -> coq_VG

      val coq_VG_scale_sum :
        nat -> nat -> nat -> Support.Mo.Coq_mat.coq_VF t0 t0 ->
        Support.Mo.Coq_mat.coq_VF t0
     end

    val coq_EPC :
      nat -> HeliosIACR2018G.coq_G -> MoM.coq_VG -> Support.Mo.Coq_mat.coq_VF ->
      HeliosIACR2018F.coq_F -> HeliosIACR2018G.coq_G

    val comEPC :
      nat -> nat -> HeliosIACR2018G.coq_G -> MoM.coq_VG -> Support.Mo.Coq_mat.coq_VF
      t0 -> Support.Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val comEPCvec :
      nat -> nat -> HeliosIACR2018G.coq_G -> MoM.coq_VG -> Support.Mo.Coq_mat.coq_VF
      -> Support.Mo.Coq_mat.coq_VF -> MoM.coq_VG

    val com :
      nat -> HeliosIACR2018G.coq_G -> MoM.coq_VG -> Support.Mo.Coq_mat.coq_MF ->
      Support.Mo.Coq_mat.coq_VF -> MoM.coq_VG
   end

  module ALenc :
   sig
    module AddVSLemmas :
     sig
      module AL :
       sig
       end
     end

    module Mat :
     sig
      module F :
       sig
        type coq_A = HeliosIACR2018F.coq_F
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

        val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
         end

        val coq_A0 : HeliosIACR2018F.coq_F

        val coq_A1 : HeliosIACR2018F.coq_F

        val coq_Aplus :
          HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F

        val coq_Amult :
          HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = HeliosIACR2018F.coq_F t0

      val coq_VF_zero : nat -> HeliosIACR2018F.coq_F t0

      val coq_VF_one : nat -> HeliosIACR2018F.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> HeliosIACR2018F.coq_F

      val coq_VF_sum : nat -> coq_VF -> HeliosIACR2018F.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> HeliosIACR2018F.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> HeliosIACR2018F.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> HeliosIACR2018F.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> HeliosIACR2018F.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module MatG :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = NGroupC.coq_G t0

      val coq_VG_id : nat -> NGroupC.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> NGroupC.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> HeliosIACR2018F.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_scale_sum : nat -> nat -> nat -> Mat.coq_VF t0 t0 -> Mat.coq_VF t0
     end

    val reenc : Enc.coq_PK -> NGroupC.coq_G -> Nthring.coq_F -> NGroupC.coq_G

    val bIsReEnc :
      Enc.coq_PK -> NGroupC.coq_G -> NGroupC.coq_G -> Nthring.coq_F -> bool

    val decryptsToExt :
      Enc.coq_PK -> NGroupC.coq_G -> Enc.coq_M -> Nthring.coq_F -> bool
   end

  module ALR :
   sig
   end

  module G2 :
   sig
    type coq_G = HeliosIACR2018F.coq_F

    val coq_Gdot : coq_G -> coq_G -> coq_G

    val coq_Gone : coq_G

    val coq_Ggen : coq_G

    val coq_Gbool_eq : coq_G -> coq_G -> bool

    val coq_Gdisjoint : coq_G -> coq_G -> bool

    val coq_Ginv : coq_G -> coq_G
   end

  type coq_St =
    ((HeliosIACR2018G.coq_G * EPC.MoM.coq_VG) * EPC.MoM.coq_VG) * HeliosIACR2018F.coq_F

  type coq_W = Support.Mo.Coq_mat.coq_VF t0 * Support.Mo.Coq_mat.coq_VF

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C = HeliosIACR2018G.coq_G

  type coq_R = HeliosIACR2018F.coq_F

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_ToStSig : (coq_St * coq_C) -> Coq_sig.coq_St

  val coq_ToWitSig : (coq_St * coq_C) -> coq_R -> coq_W -> Coq_sig.coq_W

  val coq_ToStSig5 : (coq_St * coq_C) -> Coq_sig5.coq_St

  val coq_ToWitSig5 : (coq_St * coq_C) -> coq_R -> coq_W -> Coq_sig5.coq_W

  type coq_TE = HeliosIACR2018F.coq_F

  val extractor : Coq_sig5.coq_W -> Coq_sig.coq_W -> coq_W

  type coq_X = Support.Mo.Coq_mat.coq_VF

  val simulator : coq_St -> coq_TE -> coq_C

  val simMap : coq_St -> coq_W -> coq_X -> coq_R -> coq_TE

  val simMapInv : coq_St -> coq_W -> coq_X -> coq_TE -> coq_R

  val sigXcomp : coq_St -> coq_X -> Coq_sig.coq_X

  val sig5Xcomp : coq_St -> coq_X -> Coq_sig5.coq_X
 end

module Coq_prodarg2 :
 sig
  type coq_E0 = Coq_sig5.coq_E0 * Chal.coq_G

  type coq_E1 = Coq_sig5.coq_E1

  type coq_St = Coq_prodarg.coq_St

  type coq_W = Coq_prodarg.coq_W

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C0 = (Coq_prodarg.coq_C * Coq_sig5.coq_C0) * Coq_sig.coq_C

  type coq_C1 = Coq_sig5.coq_C1

  type coq_R0 = (Coq_prodarg.coq_R * Coq_sig5.coq_R0) * Coq_sig.coq_R

  type coq_R1 = Coq_sig5.coq_R1

  val add0 : coq_E0 -> coq_E0 -> coq_E0

  val zero0 : coq_E0

  val inv0 : coq_E0 -> coq_E0

  val bool_eq0 : coq_E0 -> coq_E0 -> bool

  val disjoint0 : coq_E0 -> coq_E0 -> bool

  val add1 : coq_E1 -> coq_E1 -> coq_E1

  val zero1 : coq_E1

  val inv1 : coq_E1 -> coq_E1

  val bool_eq1 : coq_E1 -> coq_E1 -> bool

  val disjoint1 : coq_E1 -> coq_E1 -> bool

  type coq_T = Coq_sig5.coq_T * Coq_sig.coq_T

  val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0

  val coq_P1 :
    ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
    ((coq_St * coq_C0) * coq_E0) * coq_C1

  val coq_P2 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) -> coq_W
    -> ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val coq_V2 : (((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T) -> bool

  type coq_TE0 = (Coq_prodarg.coq_TE * Coq_sig5.coq_TE0) * Coq_sig.coq_TE

  type coq_TE1 = Coq_sig5.coq_TE1

  type coq_X = Coq_prodarg.coq_X

  val simulator :
    coq_St -> (coq_TE0 * coq_TE1) -> (coq_E0 * coq_E1) ->
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T

  val simMap :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_R0 * coq_R1) ->
    coq_TE0 * coq_TE1

  val simMapInv :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_TE0 * coq_TE1) ->
    coq_R0 * coq_R1

  val coq_M0 : nat

  val coq_M1 : nat

  val extractor : coq_T t0 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_W

  val allValid :
    coq_St -> coq_C0 -> coq_C1 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_T t0 t0 -> bool
 end

module BGMultiarg :
 sig
  val n : nat

  val m : nat

  type coq_St =
    (((((Enc.coq_PK * HeliosIACR2018G.coq_G) * Support.EPC.MoM.coq_VG) * NGroupC.coq_G
    t0 t0) * NGroupC.coq_G) * Support.EPC.MoM.coq_VG) * Enc.coq_M

  type coq_W =
    (Support.Mo.Coq_mat.coq_VF t0 * Support.Mo.Coq_mat.coq_VF) * Nthring.coq_F

  type coq_R =
    (((Support.Mo.Coq_mat.coq_VF * HeliosIACR2018F.coq_F) * (Support.Mo.Coq_mat.coq_VF * Support.Mo.Coq_mat.coq_VF)) * (Support.Mo.Coq_mat.coq_VF * Support.Mo.Coq_mat.coq_VF)) * (Nthring.coq_F
    t0 * Nthring.coq_F t0)

  type coq_C = (HeliosIACR2018G.coq_G * Support.EPC.MoM.coq_VG) * NGroupC.coq_G t0

  type coq_T =
    (((Support.Mo.Coq_mat.coq_VF * HeliosIACR2018F.coq_F) * HeliosIACR2018F.coq_F) * HeliosIACR2018F.coq_F) * Nthring.coq_F

  type coq_X =
    (Support.Mo.Coq_mat.coq_VF * Support.Mo.Coq_mat.coq_VF t0) * Nthring.coq_F t0 t0

  type coq_TE =
    ((((Support.Mo.Coq_mat.coq_VF * HeliosIACR2018F.coq_F) * HeliosIACR2018F.coq_F) * HeliosIACR2018F.coq_F) * Nthring.coq_F) * (((Support.Mo.Coq_mat.coq_VF * Support.Mo.Coq_mat.coq_VF) * (Support.Mo.Coq_mat.coq_VF * Support.Mo.Coq_mat.coq_VF)) * (Nthring.coq_F
    t0 * Nthring.coq_F t0))

  val coq_Rel : coq_St -> coq_W -> bool

  val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C

  val coq_P1 :
    ((coq_St * coq_C) * HeliosIACR2018F.coq_F) -> coq_R -> coq_W ->
    ((coq_St * coq_C) * HeliosIACR2018F.coq_F) * coq_T

  val coq_V1 : (((coq_St * coq_C) * HeliosIACR2018F.coq_F) * coq_T) -> bool

  val simMap : coq_St -> coq_W -> HeliosIACR2018F.coq_F -> coq_X -> coq_R -> coq_TE

  val simMapInv :
    coq_St -> coq_W -> HeliosIACR2018F.coq_F -> coq_X -> coq_TE -> coq_R

  val simulator :
    coq_St -> coq_TE -> HeliosIACR2018F.coq_F ->
    ((coq_St * coq_C) * HeliosIACR2018F.coq_F) * coq_T

  val coq_M : nat

  val extractor : coq_T t0 -> HeliosIACR2018F.coq_F t0 -> coq_W

  val disjoint : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool

  val allDifferent : HeliosIACR2018F.coq_F t0 -> bool
 end

module SH :
 sig
  module G2 :
   sig
    type coq_G = HeliosIACR2018F.coq_F

    val coq_Gdot : coq_G -> coq_G -> coq_G

    val coq_Gone : coq_G

    val coq_Ggen : coq_G

    val coq_Gbool_eq : coq_G -> coq_G -> bool

    val coq_Gdisjoint : coq_G -> coq_G -> bool

    val coq_Ginv : coq_G -> coq_G
   end

  module Chal2 :
   sig
    type coq_G = G2.coq_G * Chal.coq_G

    val coq_Gdot : coq_G -> coq_G -> G2.coq_G * Chal.coq_G

    val coq_Gone : G2.coq_G * Chal.coq_G

    val coq_Ggen : G2.coq_G * Chal.coq_G

    val coq_Gbool_eq : coq_G -> coq_G -> bool

    val coq_Gdisjoint : coq_G -> coq_G -> bool

    val coq_Ginv : coq_G -> G2.coq_G * Chal.coq_G
   end

  val n : nat

  val m : nat

  module MP :
   sig
    module AddVSLemmas :
     sig
      module AL :
       sig
       end
     end

    module Mat :
     sig
      module F :
       sig
        type coq_A = HeliosIACR2018F.coq_F
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

        val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> bool
         end

        val coq_A0 : HeliosIACR2018F.coq_F

        val coq_A1 : HeliosIACR2018F.coq_F

        val coq_Aplus :
          HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F

        val coq_Amult :
          HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F -> HeliosIACR2018F.coq_F
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

          val zero_vec : nat -> FSemiRingT.ES.Eq.coq_A t0

          val id_vec : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

          val vector_plus :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A t0

          val add_vectors :
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 t0 -> FSemiRingT.ES.Eq.coq_A t0

          val dot_product :
            nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
            FSemiRingT.ES.Eq.coq_A
         end

        type matrix = FSemiRingT.ES.Eq.coq_A t0 t0

        val get_row : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_col : nat -> nat -> matrix -> nat -> FSemiRingT.ES.Eq.coq_A t0

        val get_elem : nat -> nat -> matrix -> nat -> nat -> FSemiRingT.ES.Eq.coq_A

        val mat_build_spec :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val mat_build :
          nat -> nat -> (nat -> nat -> __ -> __ -> FSemiRingT.ES.Eq.coq_A) -> matrix

        val zero_matrix : nat -> nat -> matrix

        val id_matrix : nat -> matrix

        val inverse_matrix :
          (FSemiRingT.ES.Eq.coq_A -> FSemiRingT.ES.Eq.coq_A) -> nat -> nat -> matrix
          -> matrix

        type row_mat = matrix

        type col_mat = matrix

        val vec_to_row_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> row_mat

        val vec_to_col_mat : nat -> FSemiRingT.ES.Eq.coq_A t0 -> col_mat

        val row_mat_to_vec : nat -> row_mat -> FSemiRingT.ES.Eq.coq_A t0

        val col_mat_to_vec : nat -> col_mat -> FSemiRingT.ES.Eq.coq_A t0

        val mat_transpose : nat -> nat -> matrix -> matrix

        val vec_plus :
          nat -> FSemiRingT.ES.Eq.coq_A t0 -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_plus : nat -> nat -> matrix -> matrix -> FSemiRingT.ES.Eq.coq_A t0 t0

        val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

        val mat_vec_prod :
          nat -> nat -> matrix -> FSemiRingT.ES.Eq.coq_A t0 ->
          FSemiRingT.ES.Eq.coq_A t0

        val mat_forall2'_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec

        val mat_forall2_dec :
          nat -> nat -> FSemiRingT.ES.Eq.coq_A rel_dec -> matrix rel_dec
       end

      module ALR :
       sig
       end

      type coq_VF = HeliosIACR2018F.coq_F t0

      val coq_VF_zero : nat -> HeliosIACR2018F.coq_F t0

      val coq_VF_one : nat -> HeliosIACR2018F.coq_F t0

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0

      val coq_VF_prod : nat -> coq_VF -> HeliosIACR2018F.coq_F

      val coq_VF_sum : nat -> coq_VF -> HeliosIACR2018F.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> HeliosIACR2018F.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> HeliosIACR2018F.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> HeliosIACR2018F.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool

      val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool

      val coq_MF_perm_last : nat -> coq_MF -> index

      val coq_MF_perm_sub : nat -> coq_MF -> coq_MF

      val matRecover_sub : nat -> HeliosIACR2018F.coq_F -> nat

      val matRecover : nat -> coq_VF -> coq_MF
     end

    module MatG :
     sig
      module AddMLemmas :
       sig
       end

      type coq_VG = NGroupC.coq_G t0

      val coq_VG_id : nat -> NGroupC.coq_G t0

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> NGroupC.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mat.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> HeliosIACR2018F.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mat.coq_MF -> coq_VG

      val coq_VG_scale_sum : nat -> nat -> nat -> Mat.coq_VF t0 t0 -> Mat.coq_VF t0
     end

    val reenc : Enc.coq_PK -> NGroupC.coq_G -> Nthring.coq_F -> NGroupC.coq_G

    val bIsReEnc :
      Enc.coq_PK -> NGroupC.coq_G -> NGroupC.coq_G -> Nthring.coq_F -> bool

    val decryptsToExt :
      Enc.coq_PK -> NGroupC.coq_G -> Enc.coq_M -> Nthring.coq_F -> bool
   end

  module ALR :
   sig
   end

  type coq_E0 = Chal.coq_G

  type coq_E1 = Chal2.coq_G

  val add0 : coq_E0 -> coq_E0 -> coq_E0

  val zero0 : coq_E0

  val inv0 : coq_E0 -> coq_E0

  val bool_eq0 : coq_E0 -> coq_E0 -> bool

  val disjoint0 : coq_E0 -> coq_E0 -> bool

  val add1 : coq_E1 -> coq_E1 -> coq_E1

  val zero1 : coq_E1

  val inv1 : coq_E1 -> coq_E1

  val bool_eq1 : coq_E1 -> coq_E1 -> bool

  val disjoint1 : coq_E1 -> coq_E1 -> bool

  type coq_St =
    (((Enc.coq_PK * HeliosIACR2018G.coq_G) * Support.EPC.MoM.coq_VG) * NGroupC.coq_G
    t0) * NGroupC.coq_G t0

  type coq_W = Support.Mo.Coq_mat.coq_VF t0 * Nthring.coq_F t0

  val relReEnc :
    Enc.coq_PK -> NGroupC.coq_G t0 -> NGroupC.coq_G t0 -> Support.Mo.Coq_mat.coq_MF
    -> Nthring.coq_F t0 -> bool

  val coq_Rel : coq_St -> coq_W -> bool

  type coq_C0 = Support.EPC.MoM.coq_VG

  type coq_C1 = Support.EPC.MoM.coq_VG

  type coq_R0 = Support.Mo.Coq_mat.coq_VF

  type coq_R1 = Support.Mo.Coq_mat.coq_VF

  val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0

  val coq_P1 :
    ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
    ((coq_St * coq_C0) * coq_E0) * coq_C1

  val coq_ToStSig :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> BGMultiarg.coq_St

  val coq_ToWitSig :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) -> coq_W
    -> BGMultiarg.coq_W

  val coq_ToStSig5 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> Coq_prodarg2.coq_St

  val coq_ToWitSig5 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) -> coq_W
    -> Coq_prodarg2.coq_W

  type coq_TE0 = Support.Mo.Coq_mat.coq_VF

  type coq_TE1 = Support.Mo.Coq_mat.coq_VF

  type coq_X =
    (Support.Mo.Coq_mat.coq_VF * Support.Mo.Coq_mat.coq_VF t0) * Nthring.coq_F t0 t0

  val sigXcomp : coq_St -> coq_X -> BGMultiarg.coq_X

  val sig5Xcomp : coq_St -> coq_X -> Coq_prodarg2.coq_X

  val simulator :
    coq_St -> (coq_TE0 * coq_TE1) -> (coq_E0 * coq_E1) -> coq_C0 * coq_C1

  val simMap :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_R0 * coq_R1) ->
    coq_TE0 * coq_TE1

  val simMapInv :
    coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_TE0 * coq_TE1) ->
    coq_R0 * coq_R1

  val coq_M0 : nat

  val coq_M1 : nat

  val extractor :
    (Coq_prodarg2.coq_W * BGMultiarg.coq_W) t0 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_W
 end

module ShuffleSigma :
 sig
  type coq_E0 = SH.coq_E0

  type coq_E1 = SH.coq_E1

  type coq_E2 = Coq_prodarg2.coq_E0 * Chal.coq_G

  type coq_E3 = Coq_prodarg2.coq_E1

  type coq_St = SH.coq_St

  type coq_W = SH.coq_W

  val coq_Rel : SH.coq_St -> SH.coq_W -> bool

  type coq_C0 = SH.coq_C0

  type coq_C1 = SH.coq_C1

  type coq_C2 = Coq_prodarg2.coq_C0 * BGMultiarg.coq_C

  type coq_C3 = Coq_prodarg2.coq_C1

  type coq_R0 = SH.coq_R0

  type coq_R1 = SH.coq_R1

  type coq_R2 = Coq_prodarg2.coq_R0 * BGMultiarg.coq_R

  type coq_R3 = Coq_prodarg2.coq_R1

  val add0 : coq_E0 -> coq_E0 -> coq_E0

  val zero0 : coq_E0

  val inv0 : coq_E0 -> coq_E0

  val bool_eq0 : coq_E0 -> coq_E0 -> bool

  val disjoint0 : coq_E0 -> coq_E0 -> bool

  val add1 : coq_E1 -> coq_E1 -> coq_E1

  val zero1 : coq_E1

  val inv1 : coq_E1 -> coq_E1

  val bool_eq1 : coq_E1 -> coq_E1 -> bool

  val disjoint1 : coq_E1 -> coq_E1 -> bool

  val add2 : coq_E2 -> coq_E2 -> coq_E2

  val zero2 : coq_E2

  val inv2 : coq_E2 -> coq_E2

  val bool_eq2 : coq_E2 -> coq_E2 -> bool

  val disjoint2 : coq_E2 -> coq_E2 -> bool

  val add3 : coq_E3 -> coq_E3 -> coq_E3

  val zero3 : coq_E3

  val inv3 : coq_E3 -> coq_E3

  val bool_eq3 : coq_E3 -> coq_E3 -> bool

  val disjoint3 : coq_E3 -> coq_E3 -> bool

  type coq_T = Coq_prodarg2.coq_T * BGMultiarg.coq_T

  val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0

  val coq_P1 :
    ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
    ((coq_St * coq_C0) * coq_E0) * coq_C1

  val coq_P2 :
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) ->
    ((coq_R0 * coq_R1) * coq_R2) -> coq_W ->
    ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2

  val coq_P3 :
    ((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) ->
    (((coq_R0 * coq_R1) * coq_R2) * coq_R3) -> coq_W ->
    ((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) * coq_C3

  val coq_P4 :
    ((((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) * coq_C3) * coq_E3)
    -> (((coq_R0 * coq_R1) * coq_R2) * coq_R3) -> coq_W ->
    ((((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) * coq_C3) * coq_E3) * coq_T

  val coq_V :
    (((((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) * coq_C3) * coq_E3) * coq_T)
    -> bool

  type coq_TE0 = SH.coq_TE0

  type coq_TE1 = SH.coq_TE1

  type coq_TE2 = Coq_prodarg2.coq_TE0 * BGMultiarg.coq_TE

  type coq_TE3 = Coq_prodarg2.coq_TE1

  type coq_X = SH.coq_X

  val simulator :
    coq_St -> (((coq_TE0 * coq_TE1) * coq_TE2) * coq_TE3) ->
    (((coq_E0 * coq_E1) * coq_E2) * coq_E3) ->
    ((((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) * coq_C3) * coq_E3) * coq_T

  val simMap :
    coq_St -> coq_W -> (((coq_E0 * coq_E1) * coq_E2) * coq_E3) -> coq_X ->
    (((coq_R0 * coq_R1) * coq_R2) * coq_R3) ->
    ((coq_TE0 * coq_TE1) * coq_TE2) * coq_TE3

  val simMapInv :
    coq_St -> coq_W -> (((coq_E0 * coq_E1) * coq_E2) * coq_E3) -> coq_X ->
    (((coq_TE0 * coq_TE1) * coq_TE2) * coq_TE3) ->
    ((coq_R0 * coq_R1) * coq_R2) * coq_R3

  val coq_M0 : nat

  val coq_M1 : nat

  val coq_M2 : nat

  val coq_M3 : nat

  val getSig5Resp : coq_T t0 t0 -> Coq_prodarg2.coq_T t0 t0

  val getSig5Chal :
    (coq_E2 * coq_E3 t0) t0 -> (Coq_prodarg2.coq_E0 * Coq_prodarg2.coq_E1 t0) t0

  val getSigResp : coq_T t0 t0 -> BGMultiarg.coq_T t0

  val getSigChal : (coq_E2 * coq_E3 t0) t0 -> Chal.coq_G t0

  val extractor :
    coq_T t0 t0 t0 t0 -> (coq_E0 * (coq_E1 * (coq_E2 * coq_E3 t0) t0) t0) t0 -> coq_W

  val getSig5Com :
    (coq_C2 * coq_C3 t0) -> Coq_prodarg2.coq_C0 * Coq_prodarg2.coq_C1 t0

  val getSigCom : (coq_C2 * coq_C3 t0) -> BGMultiarg.coq_C
 end
