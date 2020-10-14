
type __ = Obj.t

val negb : bool -> bool

type nat =
| O
| S of nat

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
                   simMapInv : (__ -> __ -> 'e -> __ -> __);
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
    'a1 form -> 'a1 coq_S -> 'a1 coq_W -> 'a1 -> 'a1 coq_R -> 'a1 coq_T

  val simMapInv :
    'a1 form -> 'a1 coq_S -> 'a1 coq_W -> 'a1 -> 'a1 coq_T -> 'a1 coq_R

  val extractor :
    'a1 form -> 'a1 coq_T -> 'a1 coq_T -> 'a1 -> 'a1 -> 'a1 coq_W
 end

val eqSigmaProtocol : 'a1 Sigma.form -> 'a1 Sigma.form

val disSigmaProtocol : 'a1 Sigma.form -> 'a1 Sigma.form

val parSigmaProtocol :
  'a1 Sigma.form -> 'a2 Sigma.form -> ('a1 * 'a2) Sigma.form

type 'a rel_dec = 'a -> 'a -> bool

val dec_beq : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool

type 'a t =
| Nil
| Cons of 'a * nat * 'a t

val caseS : ('a1 -> nat -> 'a1 t -> 'a2) -> nat -> 'a1 t -> 'a2

val hd : nat -> 'a1 t -> 'a1

val const : 'a1 -> nat -> 'a1 t

val tl : nat -> 'a1 t -> 'a1 t

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

val vnth : nat -> 'a1 t -> nat -> 'a1

val vreplace : nat -> 'a1 t -> nat -> 'a1 -> 'a1 t

val vmap : ('a1 -> 'a2) -> nat -> 'a1 t -> 'a2 t

val bVforall : ('a1 -> bool) -> nat -> 'a1 t -> bool

val vforall2_aux_dec :
  ('a1 -> 'a2 -> bool) -> nat -> 'a1 t -> nat -> 'a2 t -> bool

val vforall2_dec : ('a1 -> 'a2 -> bool) -> nat -> 'a1 t -> 'a2 t -> bool

val bVforall2_aux :
  ('a1 -> 'a2 -> bool) -> nat -> nat -> 'a1 t -> 'a2 t -> bool

val bVforall2 : ('a1 -> 'a2 -> bool) -> nat -> 'a1 t -> 'a2 t -> bool

val vbuild_spec : nat -> (nat -> __ -> 'a1) -> 'a1 t

val vbuild : nat -> (nat -> __ -> 'a1) -> 'a1 t

val vfold_left : ('a1 -> 'a2 -> 'a1) -> nat -> 'a1 -> 'a2 t -> 'a1

val vfold_left_rev : ('a1 -> 'a2 -> 'a1) -> nat -> 'a1 -> 'a2 t -> 'a1

val vmap2 : ('a1 -> 'a2 -> 'a3) -> nat -> 'a1 t -> 'a2 t -> 'a3 t

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

  val zero_vec : nat -> SRT.ES.Eq.coq_A t

  val id_vec : nat -> nat -> SRT.ES.Eq.coq_A t

  val vector_plus :
    nat -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A t

  val add_vectors : nat -> nat -> SRT.ES.Eq.coq_A t t -> SRT.ES.Eq.coq_A t

  val dot_product :
    nat -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A
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

    val zero_vec : nat -> SRT.ES.Eq.coq_A t

    val id_vec : nat -> nat -> SRT.ES.Eq.coq_A t

    val vector_plus :
      nat -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A t

    val add_vectors : nat -> nat -> SRT.ES.Eq.coq_A t t -> SRT.ES.Eq.coq_A t

    val dot_product :
      nat -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A
   end

  type matrix = SRT.ES.Eq.coq_A t t

  val get_row : nat -> nat -> matrix -> nat -> SRT.ES.Eq.coq_A t

  val get_col : nat -> nat -> matrix -> nat -> SRT.ES.Eq.coq_A t

  val get_elem : nat -> nat -> matrix -> nat -> nat -> SRT.ES.Eq.coq_A

  val mat_build_spec :
    nat -> nat -> (nat -> nat -> __ -> __ -> SRT.ES.Eq.coq_A) -> matrix

  val mat_build :
    nat -> nat -> (nat -> nat -> __ -> __ -> SRT.ES.Eq.coq_A) -> matrix

  val zero_matrix : nat -> nat -> matrix

  val id_matrix : nat -> matrix

  val inverse_matrix :
    (SRT.ES.Eq.coq_A -> SRT.ES.Eq.coq_A) -> nat -> nat -> matrix -> matrix

  type row_mat = matrix

  type col_mat = matrix

  val vec_to_row_mat : nat -> SRT.ES.Eq.coq_A t -> row_mat

  val vec_to_col_mat : nat -> SRT.ES.Eq.coq_A t -> col_mat

  val row_mat_to_vec : nat -> row_mat -> SRT.ES.Eq.coq_A t

  val col_mat_to_vec : nat -> col_mat -> SRT.ES.Eq.coq_A t

  val mat_transpose : nat -> nat -> matrix -> matrix

  val vec_plus :
    nat -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A t

  val mat_plus : nat -> nat -> matrix -> matrix -> SRT.ES.Eq.coq_A t t

  val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix

  val mat_vec_prod :
    nat -> nat -> matrix -> SRT.ES.Eq.coq_A t -> SRT.ES.Eq.coq_A t

  val mat_forall2'_dec :
    nat -> nat -> SRT.ES.Eq.coq_A rel_dec -> matrix rel_dec

  val mat_forall2_dec :
    nat -> nat -> SRT.ES.Eq.coq_A rel_dec -> matrix rel_dec
 end

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
 sig
  module AddMLemmas :
   sig
   end

  type coq_VG = Group.coq_G t

  val coq_VG_id : nat -> Group.coq_G t

  val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

  val coq_VG_inv : nat -> coq_VG -> coq_VG

  val coq_VG_prod : nat -> coq_VG -> Group.coq_G

  val coq_VG_Pexp : nat -> coq_VG -> MatF.coq_VF -> coq_VG

  val coq_VG_Sexp : nat -> coq_VG -> Ring.coq_F -> coq_VG

  val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

  val coq_VG_MF_exp_coll : nat -> coq_VG -> MatF.coq_MF -> coq_VG

  val coq_VG_MF_exp_row : nat -> coq_VG -> MatF.coq_MF -> coq_VG

  val coq_PexpMatrix : nat -> coq_VG -> MatF.coq_MF -> coq_VG

  val coq_VG_scale_sum : nat -> nat -> nat -> MatF.coq_VF t t -> MatF.coq_VF t
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
   end

  val reenc : Enc.coq_PK -> Ciphertext.coq_G -> Ring.coq_F -> Ciphertext.coq_G

  val decryptsToExt :
    Enc.coq_PK -> Ciphertext.coq_G -> Enc.coq_M -> Ring.coq_F -> bool
 end

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

  val keygenMix : coq_KGR -> coq_PK

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
 sig
  module AddMLemmas :
   sig
   end

  module MoM :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = Group.coq_G t

    val coq_VG_id : nat -> Group.coq_G t

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> Group.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> Mo.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> Ring.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> Mo.coq_MF -> coq_VG

    val coq_VG_scale_sum : nat -> nat -> nat -> Mo.coq_VF t t -> Mo.coq_VF t
   end

  val coq_PC :
    Group.coq_G -> Group.coq_G -> Ring.coq_F -> Ring.coq_F -> Group.coq_G

  val comPC :
    nat -> Group.coq_G -> Group.coq_G -> Mo.coq_VF -> Mo.coq_VF -> MoM.coq_VG
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

    type coq_VF = Field.coq_F t

    val coq_VF_zero : nat -> Field.coq_F t

    val coq_VF_one : nat -> Field.coq_F t

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t

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

      type coq_VG = Group.coq_G t

      val coq_VG_id : nat -> Group.coq_G t

      val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

      val coq_VG_inv : nat -> coq_VG -> coq_VG

      val coq_VG_prod : nat -> coq_VG -> Group.coq_G

      val coq_VG_Pexp : nat -> coq_VG -> Mo.coq_VF -> coq_VG

      val coq_VG_Sexp : nat -> coq_VG -> Field.coq_F -> coq_VG

      val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

      val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.coq_MF -> coq_VG

      val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.coq_MF -> coq_VG

      val coq_PexpMatrix : nat -> coq_VG -> Mo.coq_MF -> coq_VG

      val coq_VG_scale_sum : nat -> nat -> nat -> Mo.coq_VF t t -> Mo.coq_VF t
     end

    val coq_PC :
      Group.coq_G -> Group.coq_G -> Field.coq_F -> Field.coq_F -> Group.coq_G

    val comPC :
      nat -> Group.coq_G -> Group.coq_G -> Mo.coq_VF -> Mo.coq_VF ->
      MoM.coq_VG
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

  val simulator_mapper_inv :
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

  val empty_simulator_mapper_inv :
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

  val dLog2_simulator_mapper_inv :
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

module ElectionGuard :
 functor (ElectionGuardG:GroupSig) ->
 functor (ElectionGuardF:FieldSig) ->
 functor (ElectionGuardVS:sig
  val op :
    ElectionGuardG.coq_G -> ElectionGuardF.coq_F -> ElectionGuardG.coq_G
 end) ->
 sig
  module BS :
   sig
    module HardProb :
     sig
      val dLog :
        (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F
        -> bool
     end

    module Mo :
     sig
      module F :
       sig
        type coq_A = ElectionGuardF.coq_F
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

        val eqA_dec : ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> bool
         end

        val coq_A0 : ElectionGuardF.coq_F

        val coq_A1 : ElectionGuardF.coq_F

        val coq_Aplus :
          ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F

        val coq_Amult :
          ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F
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
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t t ->
            FSemiRingT.ES.Eq.coq_A t

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

      type coq_VF = ElectionGuardF.coq_F t

      val coq_VF_zero : nat -> ElectionGuardF.coq_F t

      val coq_VF_one : nat -> ElectionGuardF.coq_F t

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t

      val coq_VF_prod : nat -> coq_VF -> ElectionGuardF.coq_F

      val coq_VF_sum : nat -> coq_VF -> ElectionGuardF.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> ElectionGuardF.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> ElectionGuardF.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> ElectionGuardF.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool
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

        type coq_VG = ElectionGuardG.coq_G t

        val coq_VG_id : nat -> ElectionGuardG.coq_G t

        val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

        val coq_VG_inv : nat -> coq_VG -> coq_VG

        val coq_VG_prod : nat -> coq_VG -> ElectionGuardG.coq_G

        val coq_VG_Pexp : nat -> coq_VG -> Mo.coq_VF -> coq_VG

        val coq_VG_Sexp : nat -> coq_VG -> ElectionGuardF.coq_F -> coq_VG

        val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

        val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.coq_MF -> coq_VG

        val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.coq_MF -> coq_VG

        val coq_PexpMatrix : nat -> coq_VG -> Mo.coq_MF -> coq_VG

        val coq_VG_scale_sum :
          nat -> nat -> nat -> Mo.coq_VF t t -> Mo.coq_VF t
       end

      val coq_PC :
        ElectionGuardG.coq_G -> ElectionGuardG.coq_G -> ElectionGuardF.coq_F
        -> ElectionGuardF.coq_F -> ElectionGuardG.coq_G

      val comPC :
        nat -> ElectionGuardG.coq_G -> ElectionGuardG.coq_G -> Mo.coq_VF ->
        Mo.coq_VF -> MoM.coq_VG
     end

    module AddVSLemmas :
     sig
     end

    val valid_P0 :
      (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F
      -> ElectionGuardF.coq_F ->
      (ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G

    val valid_V0 :
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G)
      -> ElectionGuardF.coq_F ->
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F

    val valid_P1 :
      (((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F)
      -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F ->
      (((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * ElectionGuardF.coq_F

    val valid_V1 :
      ((((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * ElectionGuardF.coq_F)
      -> bool

    val simulator_mapper :
      (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F
      -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F

    val simulator_mapper_inv :
      (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F
      -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F

    val simulator :
      (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F
      -> ElectionGuardF.coq_F ->
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
      (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F
      -> (ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardF.coq_F

    val empty_P1 :
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardF.coq_F)
      -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F ->
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * ElectionGuardF.coq_F

    val empty_V1 :
      (((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * ElectionGuardF.coq_F)
      -> bool

    val empty_simulator_mapper :
      ElectionGuardG.coq_G -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F ->
      ElectionGuardF.coq_F -> ElectionGuardF.coq_F

    val empty_simulator_mapper_inv :
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
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G)
      -> (ElectionGuardF.coq_F * ElectionGuardF.coq_F) -> bool

    val dLog2_P0 :
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G)
      -> (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
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
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G)
      -> (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
      ElectionGuardF.coq_F -> (ElectionGuardF.coq_F * ElectionGuardF.coq_F)
      -> ElectionGuardF.coq_F * ElectionGuardF.coq_F

    val dLog2_simulator_mapper_inv :
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G)
      -> (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
      ElectionGuardF.coq_F -> (ElectionGuardF.coq_F * ElectionGuardF.coq_F)
      -> ElectionGuardF.coq_F * ElectionGuardF.coq_F

    val dLog2_simulator :
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G)
      -> (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
      ElectionGuardF.coq_F ->
      ((((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * (ElectionGuardF.coq_F * ElectionGuardF.coq_F)

    val dLog2_extractor :
      (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
      (ElectionGuardF.coq_F * ElectionGuardF.coq_F) -> ElectionGuardF.coq_F
      -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F * ElectionGuardF.coq_F

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

    val keygenMix : coq_KGR -> coq_PK

    val enc :
      coq_PK -> ElectionGuardG.coq_G -> ElectionGuardF.coq_F -> DG.coq_G

    val dec : ElectionGuardF.coq_F -> DG.coq_G -> coq_M

    val keymatch : coq_PK -> coq_SK -> bool
   end

  module ALES :
   sig
    module AddVSLemmas :
     sig
     end

    val reenc : ES.coq_PK -> DG.coq_G -> ElectionGuardF.coq_F -> DG.coq_G

    val decryptsToExt :
      ES.coq_PK -> DG.coq_G -> ES.coq_M -> ElectionGuardF.coq_F -> bool
   end

  module MatrixF :
   sig
    module F :
     sig
      type coq_A = ElectionGuardF.coq_F
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

      val eqA_dec : ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> bool
     end

    module FSemiRingT :
     sig
      module ES :
       sig
        module Eq :
         sig
          type coq_A = F.coq_A
         end

        val eqA_dec : ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> bool
       end

      val coq_A0 : ElectionGuardF.coq_F

      val coq_A1 : ElectionGuardF.coq_F

      val coq_Aplus :
        ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F

      val coq_Amult :
        ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F
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

    type coq_VF = ElectionGuardF.coq_F t

    val coq_VF_zero : nat -> ElectionGuardF.coq_F t

    val coq_VF_one : nat -> ElectionGuardF.coq_F t

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t

    val coq_VF_prod : nat -> coq_VF -> ElectionGuardF.coq_F

    val coq_VF_sum : nat -> coq_VF -> ElectionGuardF.coq_F

    val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_neg : nat -> coq_VF -> coq_VF

    val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_scale : nat -> coq_VF -> ElectionGuardF.coq_F -> coq_VF

    val coq_VF_inProd : nat -> coq_VF -> coq_VF -> ElectionGuardF.coq_F

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

    val coq_MF_scal : nat -> coq_MF -> ElectionGuardF.coq_F -> coq_MF

    val coq_MFisPermutation : nat -> coq_MF -> bool
   end

  module Matrix :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = ElectionGuardG.coq_G t

    val coq_VG_id : nat -> ElectionGuardG.coq_G t

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> ElectionGuardG.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> MatrixF.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> ElectionGuardF.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> MatrixF.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> MatrixF.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> MatrixF.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> MatrixF.coq_VF t t -> MatrixF.coq_VF t
   end

  module MoC :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = DG.coq_G t

    val coq_VG_id : nat -> DG.coq_G t

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> DG.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> MatrixF.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> ElectionGuardF.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> MatrixF.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> MatrixF.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> MatrixF.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> MatrixF.coq_VF t t -> MatrixF.coq_VF t
   end

  val coq_DHTForm : ElectionGuardF.coq_F Sigma.form

  val coq_DHTDisForm : ElectionGuardF.coq_F Sigma.form

  val oneOrZero :
    ElectionGuardF.coq_F Sigma.coq_S -> ElectionGuardF.coq_F Sigma.coq_S

  val oneOrZeroCipher :
    ES.coq_PK -> DG.coq_G -> ElectionGuardF.coq_F Sigma.coq_S

  val decFactorStatment :
    ES.coq_PK -> DG.coq_G -> ElectionGuardG.coq_G -> ElectionGuardF.coq_F
    Sigma.coq_S

  type recChalType = __

  type recChalTypeSelDec = __

  val coq_OneOfNSigma : nat -> recChalType Sigma.form

  val coq_DecryptionSigma : nat -> recChalType Sigma.form

  val coq_BallotDecSigma : nat -> nat -> recChalTypeSelDec Sigma.form

  val coq_OneOfNStatment :
    nat -> ES.coq_PK -> DG.coq_G -> DG.coq_G t -> recChalType Sigma.coq_S

  val coq_DecryptionSigmaStatment :
    nat -> (ElectionGuardG.coq_G * ElectionGuardG.coq_G) ->
    ElectionGuardG.coq_G -> ElectionGuardG.coq_G t -> ElectionGuardG.coq_G t
    -> recChalType Sigma.coq_S

  val coq_BallotDecSigmaStatment :
    nat -> nat -> ElectionGuardG.coq_G -> ElectionGuardG.coq_G t -> DG.coq_G
    t -> ElectionGuardG.coq_G t t -> recChalTypeSelDec Sigma.coq_S

  val mapToGroup :
    ElectionGuardG.coq_G -> ElectionGuardF.coq_F -> ElectionGuardG.coq_G

  type 'a coq_ProofTranscript = ('a Sigma.coq_C * 'a) * 'a Sigma.coq_T

  val coq_ProofTranDecAuthComm :
    nat -> nat -> recChalTypeSelDec Sigma.coq_C -> recChalTypeSelDec
    Sigma.coq_C

  val coq_ProofTranDecAuthChal :
    nat -> nat -> recChalTypeSelDec -> recChalTypeSelDec

  val coq_ProofTranDecAuthResp :
    nat -> nat -> recChalTypeSelDec Sigma.coq_T -> recChalTypeSelDec
    Sigma.coq_T

  val coq_ProofTranDecAuth :
    nat -> nat -> recChalTypeSelDec coq_ProofTranscript -> recChalTypeSelDec
    coq_ProofTranscript

  val coq_TransComp :
    'a1 Sigma.form -> 'a1 Sigma.coq_S -> 'a1 coq_ProofTranscript -> (('a1
    Sigma.coq_S * 'a1 Sigma.coq_C) * 'a1) * 'a1 Sigma.coq_T

  type tally = __

  type ballot = __

  type ballotProof = __

  val coq_SelectionVerifier :
    ES.coq_PK -> nat -> DG.coq_G t -> recChalType coq_ProofTranscript -> bool

  val coq_BallotVerifier :
    ES.coq_PK -> nat -> nat t -> ballot -> ballotProof -> bool

  type decryptionFactors = __

  type decrytionProof = __

  val coq_SelectionDecVerifier :
    nat -> nat -> ElectionGuardG.coq_G -> ElectionGuardG.coq_G t -> DG.coq_G
    t -> ElectionGuardG.coq_G t t -> recChalTypeSelDec coq_ProofTranscript ->
    bool

  val coq_DecryptionVerifier :
    nat -> nat -> ElectionGuardG.coq_G -> ElectionGuardG.coq_G t -> nat t ->
    ballot -> decryptionFactors -> decrytionProof -> bool

  val coq_SumOfProd : nat -> recChalType Sigma.coq_W -> ElectionGuardF.coq_F

  val multBallots : nat -> nat t -> ballot -> ballot -> ballot

  val zeroBallot : nat -> nat t -> ballot

  val coq_Verifier :
    nat -> nat -> nat -> nat t -> ElectionGuardG.coq_G ->
    ElectionGuardG.coq_G t -> ballot t -> ballotProof t -> decryptionFactors
    -> decrytionProof -> bool
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

module EG :
 sig
  module BS :
   sig
    module HardProb :
     sig
      val dLog :
        (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F
        -> bool
     end

    module Mo :
     sig
      module F :
       sig
        type coq_A = ElectionGuardF.coq_F
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

        val eqA_dec : ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> bool
       end

      module FSemiRingT :
       sig
        module ES :
         sig
          module Eq :
           sig
            type coq_A = F.coq_A
           end

          val eqA_dec : ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> bool
         end

        val coq_A0 : ElectionGuardF.coq_F

        val coq_A1 : ElectionGuardF.coq_F

        val coq_Aplus :
          ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F

        val coq_Amult :
          ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F
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
            nat -> nat -> FSemiRingT.ES.Eq.coq_A t t ->
            FSemiRingT.ES.Eq.coq_A t

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

      type coq_VF = ElectionGuardF.coq_F t

      val coq_VF_zero : nat -> ElectionGuardF.coq_F t

      val coq_VF_one : nat -> ElectionGuardF.coq_F t

      val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t

      val coq_VF_prod : nat -> coq_VF -> ElectionGuardF.coq_F

      val coq_VF_sum : nat -> coq_VF -> ElectionGuardF.coq_F

      val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_neg : nat -> coq_VF -> coq_VF

      val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

      val coq_VF_scale : nat -> coq_VF -> ElectionGuardF.coq_F -> coq_VF

      val coq_VF_inProd : nat -> coq_VF -> coq_VF -> ElectionGuardF.coq_F

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

      val coq_MF_scal : nat -> coq_MF -> ElectionGuardF.coq_F -> coq_MF

      val coq_MFisPermutation : nat -> coq_MF -> bool
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

        type coq_VG = ElectionGuardG.coq_G t

        val coq_VG_id : nat -> ElectionGuardG.coq_G t

        val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

        val coq_VG_inv : nat -> coq_VG -> coq_VG

        val coq_VG_prod : nat -> coq_VG -> ElectionGuardG.coq_G

        val coq_VG_Pexp : nat -> coq_VG -> Mo.coq_VF -> coq_VG

        val coq_VG_Sexp : nat -> coq_VG -> ElectionGuardF.coq_F -> coq_VG

        val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

        val coq_VG_MF_exp_coll : nat -> coq_VG -> Mo.coq_MF -> coq_VG

        val coq_VG_MF_exp_row : nat -> coq_VG -> Mo.coq_MF -> coq_VG

        val coq_PexpMatrix : nat -> coq_VG -> Mo.coq_MF -> coq_VG

        val coq_VG_scale_sum :
          nat -> nat -> nat -> Mo.coq_VF t t -> Mo.coq_VF t
       end

      val coq_PC :
        ElectionGuardG.coq_G -> ElectionGuardG.coq_G -> ElectionGuardF.coq_F
        -> ElectionGuardF.coq_F -> ElectionGuardG.coq_G

      val comPC :
        nat -> ElectionGuardG.coq_G -> ElectionGuardG.coq_G -> Mo.coq_VF ->
        Mo.coq_VF -> MoM.coq_VG
     end

    module AddVSLemmas :
     sig
     end

    val valid_P0 :
      (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F
      -> ElectionGuardF.coq_F ->
      (ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G

    val valid_V0 :
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G)
      -> ElectionGuardF.coq_F ->
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F

    val valid_P1 :
      (((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F)
      -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F ->
      (((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * ElectionGuardF.coq_F

    val valid_V1 :
      ((((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * ElectionGuardF.coq_F)
      -> bool

    val simulator_mapper :
      (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F
      -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F

    val simulator_mapper_inv :
      (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F
      -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F

    val simulator :
      (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F
      -> ElectionGuardF.coq_F ->
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
      (ElectionGuardG.coq_G * ElectionGuardG.coq_G) -> ElectionGuardF.coq_F
      -> (ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardF.coq_F

    val empty_P1 :
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardF.coq_F)
      -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F ->
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * ElectionGuardF.coq_F

    val empty_V1 :
      (((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * ElectionGuardF.coq_F)
      -> bool

    val empty_simulator_mapper :
      ElectionGuardG.coq_G -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F ->
      ElectionGuardF.coq_F -> ElectionGuardF.coq_F

    val empty_simulator_mapper_inv :
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
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G)
      -> (ElectionGuardF.coq_F * ElectionGuardF.coq_F) -> bool

    val dLog2_P0 :
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G)
      -> (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
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
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G)
      -> (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
      ElectionGuardF.coq_F -> (ElectionGuardF.coq_F * ElectionGuardF.coq_F)
      -> ElectionGuardF.coq_F * ElectionGuardF.coq_F

    val dLog2_simulator_mapper_inv :
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G)
      -> (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
      ElectionGuardF.coq_F -> (ElectionGuardF.coq_F * ElectionGuardF.coq_F)
      -> ElectionGuardF.coq_F * ElectionGuardF.coq_F

    val dLog2_simulator :
      ((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G)
      -> (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
      ElectionGuardF.coq_F ->
      ((((ElectionGuardG.coq_G * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardG.coq_G) * ElectionGuardF.coq_F) * (ElectionGuardF.coq_F * ElectionGuardF.coq_F)

    val dLog2_extractor :
      (ElectionGuardF.coq_F * ElectionGuardF.coq_F) ->
      (ElectionGuardF.coq_F * ElectionGuardF.coq_F) -> ElectionGuardF.coq_F
      -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F * ElectionGuardF.coq_F

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

    val keygenMix : coq_KGR -> coq_PK

    val enc :
      coq_PK -> ElectionGuardG.coq_G -> ElectionGuardF.coq_F -> DG.coq_G

    val dec : ElectionGuardF.coq_F -> DG.coq_G -> coq_M

    val keymatch : coq_PK -> coq_SK -> bool
   end

  module ALES :
   sig
    module AddVSLemmas :
     sig
     end

    val reenc : ES.coq_PK -> DG.coq_G -> ElectionGuardF.coq_F -> DG.coq_G

    val decryptsToExt :
      ES.coq_PK -> DG.coq_G -> ES.coq_M -> ElectionGuardF.coq_F -> bool
   end

  module MatrixF :
   sig
    module F :
     sig
      type coq_A = ElectionGuardF.coq_F
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

      val eqA_dec : ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> bool
     end

    module FSemiRingT :
     sig
      module ES :
       sig
        module Eq :
         sig
          type coq_A = F.coq_A
         end

        val eqA_dec : ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> bool
       end

      val coq_A0 : ElectionGuardF.coq_F

      val coq_A1 : ElectionGuardF.coq_F

      val coq_Aplus :
        ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F

      val coq_Amult :
        ElectionGuardF.coq_F -> ElectionGuardF.coq_F -> ElectionGuardF.coq_F
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

    type coq_VF = ElectionGuardF.coq_F t

    val coq_VF_zero : nat -> ElectionGuardF.coq_F t

    val coq_VF_one : nat -> ElectionGuardF.coq_F t

    val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t

    val coq_VF_prod : nat -> coq_VF -> ElectionGuardF.coq_F

    val coq_VF_sum : nat -> coq_VF -> ElectionGuardF.coq_F

    val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_neg : nat -> coq_VF -> coq_VF

    val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF

    val coq_VF_scale : nat -> coq_VF -> ElectionGuardF.coq_F -> coq_VF

    val coq_VF_inProd : nat -> coq_VF -> coq_VF -> ElectionGuardF.coq_F

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

    val coq_MF_scal : nat -> coq_MF -> ElectionGuardF.coq_F -> coq_MF

    val coq_MFisPermutation : nat -> coq_MF -> bool
   end

  module Matrix :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = ElectionGuardG.coq_G t

    val coq_VG_id : nat -> ElectionGuardG.coq_G t

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> ElectionGuardG.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> MatrixF.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> ElectionGuardF.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> MatrixF.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> MatrixF.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> MatrixF.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> MatrixF.coq_VF t t -> MatrixF.coq_VF t
   end

  module MoC :
   sig
    module AddMLemmas :
     sig
     end

    type coq_VG = DG.coq_G t

    val coq_VG_id : nat -> DG.coq_G t

    val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG

    val coq_VG_inv : nat -> coq_VG -> coq_VG

    val coq_VG_prod : nat -> coq_VG -> DG.coq_G

    val coq_VG_Pexp : nat -> coq_VG -> MatrixF.coq_VF -> coq_VG

    val coq_VG_Sexp : nat -> coq_VG -> ElectionGuardF.coq_F -> coq_VG

    val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool

    val coq_VG_MF_exp_coll : nat -> coq_VG -> MatrixF.coq_MF -> coq_VG

    val coq_VG_MF_exp_row : nat -> coq_VG -> MatrixF.coq_MF -> coq_VG

    val coq_PexpMatrix : nat -> coq_VG -> MatrixF.coq_MF -> coq_VG

    val coq_VG_scale_sum :
      nat -> nat -> nat -> MatrixF.coq_VF t t -> MatrixF.coq_VF t
   end

  val coq_DHTForm : ElectionGuardF.coq_F Sigma.form

  val coq_DHTDisForm : ElectionGuardF.coq_F Sigma.form

  val oneOrZero :
    ElectionGuardF.coq_F Sigma.coq_S -> ElectionGuardF.coq_F Sigma.coq_S

  val oneOrZeroCipher :
    ES.coq_PK -> DG.coq_G -> ElectionGuardF.coq_F Sigma.coq_S

  val decFactorStatment :
    ES.coq_PK -> DG.coq_G -> ElectionGuardG.coq_G -> ElectionGuardF.coq_F
    Sigma.coq_S

  type recChalType = __

  type recChalTypeSelDec = __

  val coq_OneOfNSigma : nat -> recChalType Sigma.form

  val coq_DecryptionSigma : nat -> recChalType Sigma.form

  val coq_BallotDecSigma : nat -> nat -> recChalTypeSelDec Sigma.form

  val coq_OneOfNStatment :
    nat -> ES.coq_PK -> DG.coq_G -> DG.coq_G t -> recChalType Sigma.coq_S

  val coq_DecryptionSigmaStatment :
    nat -> (ElectionGuardG.coq_G * ElectionGuardG.coq_G) ->
    ElectionGuardG.coq_G -> ElectionGuardG.coq_G t -> ElectionGuardG.coq_G t
    -> recChalType Sigma.coq_S

  val coq_BallotDecSigmaStatment :
    nat -> nat -> ElectionGuardG.coq_G -> ElectionGuardG.coq_G t -> DG.coq_G
    t -> ElectionGuardG.coq_G t t -> recChalTypeSelDec Sigma.coq_S

  val mapToGroup :
    ElectionGuardG.coq_G -> ElectionGuardF.coq_F -> ElectionGuardG.coq_G

  type 'a coq_ProofTranscript = ('a Sigma.coq_C * 'a) * 'a Sigma.coq_T

  val coq_ProofTranDecAuthComm :
    nat -> nat -> recChalTypeSelDec Sigma.coq_C -> recChalTypeSelDec
    Sigma.coq_C

  val coq_ProofTranDecAuthChal :
    nat -> nat -> recChalTypeSelDec -> recChalTypeSelDec

  val coq_ProofTranDecAuthResp :
    nat -> nat -> recChalTypeSelDec Sigma.coq_T -> recChalTypeSelDec
    Sigma.coq_T

  val coq_ProofTranDecAuth :
    nat -> nat -> recChalTypeSelDec coq_ProofTranscript -> recChalTypeSelDec
    coq_ProofTranscript

  val coq_TransComp :
    'a1 Sigma.form -> 'a1 Sigma.coq_S -> 'a1 coq_ProofTranscript -> (('a1
    Sigma.coq_S * 'a1 Sigma.coq_C) * 'a1) * 'a1 Sigma.coq_T

  type tally = __

  type ballot = __

  type ballotProof = __

  val coq_SelectionVerifier :
    ES.coq_PK -> nat -> DG.coq_G t -> recChalType coq_ProofTranscript -> bool

  val coq_BallotVerifier :
    ES.coq_PK -> nat -> nat t -> ballot -> ballotProof -> bool

  type decryptionFactors = __

  type decrytionProof = __

  val coq_SelectionDecVerifier :
    nat -> nat -> ElectionGuardG.coq_G -> ElectionGuardG.coq_G t -> DG.coq_G
    t -> ElectionGuardG.coq_G t t -> recChalTypeSelDec coq_ProofTranscript ->
    bool

  val coq_DecryptionVerifier :
    nat -> nat -> ElectionGuardG.coq_G -> ElectionGuardG.coq_G t -> nat t ->
    ballot -> decryptionFactors -> decrytionProof -> bool

  val coq_SumOfProd : nat -> recChalType Sigma.coq_W -> ElectionGuardF.coq_F

  val multBallots : nat -> nat t -> ballot -> ballot -> ballot

  val zeroBallot : nat -> nat t -> ballot

  val coq_Verifier :
    nat -> nat -> nat -> nat t -> ElectionGuardG.coq_G ->
    ElectionGuardG.coq_G t -> ballot t -> ballotProof t -> decryptionFactors
    -> decrytionProof -> bool
 end
