
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3 **)

let uncurry f0 = function
| (x, y) -> f0 x y

(** val prod_curry_subdef : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3 **)

let prod_curry_subdef =
  uncurry

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

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h



(** val pred : nat -> nat **)

let pred n0 = match n0 with
| O -> n0
| S u -> u

(** val add : nat -> nat -> nat **)

let rec add n0 m0 =
  match n0 with
  | O -> m0
  | S p0 -> S (add p0 m0)

(** val mul : nat -> nat -> nat **)

let rec mul n0 m0 =
  match n0 with
  | O -> O
  | S p0 -> add m0 (mul p0 m0)

(** val sub : nat -> nat -> nat **)

let rec sub n0 m0 =
  match n0 with
  | O -> n0
  | S k -> (match m0 with
            | O -> n0
            | S l -> sub k l)

(** val max : nat -> nat -> nat **)

let rec max n0 m0 =
  match n0 with
  | O -> m0
  | S n' -> (match m0 with
             | O -> n0
             | S m' -> S (max n' m'))

type reflect =
| ReflectT
| ReflectF

module Nat =
 struct
  (** val pred : nat -> nat **)

  let pred n0 = match n0 with
  | O -> n0
  | S u -> u

  (** val add : nat -> nat -> nat **)

  let rec add n0 m0 =
    match n0 with
    | O -> m0
    | S p0 -> S (add p0 m0)

  (** val mul : nat -> nat -> nat **)

  let rec mul n0 m0 =
    match n0 with
    | O -> O
    | S p0 -> add m0 (mul p0 m0)

  (** val sub : nat -> nat -> nat **)

  let rec sub n0 m0 =
    match n0 with
    | O -> n0
    | S k -> (match m0 with
              | O -> n0
              | S l -> sub k l)

  (** val divmod : nat -> nat -> nat -> nat -> nat * nat **)

  let rec divmod x y q0 u =
    match x with
    | O -> (q0, u)
    | S x' -> (match u with
               | O -> divmod x' y (S q0) y
               | S u' -> divmod x' y q0 u')

  (** val div : nat -> nat -> nat **)

  let div x y = match y with
  | O -> y
  | S y' -> fst (divmod x y' O y')

  (** val modulo : nat -> nat -> nat **)

  let modulo x = function
  | O -> x
  | S y' -> sub y' (snd (divmod x y' O y'))
 end

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of Big_int_Z.big_int
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec succ = Big_int_Z.succ_big_int

  (** val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec add = Big_int_Z.add_big_int

  (** val add_carry : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add_carry p0 q0))
        (fun q0 -> Big_int_Z.mult_int_big_int 2 (add_carry p0 q0))
        (fun _ -> (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (succ p0))
        y)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> Big_int_Z.mult_int_big_int 2 (add_carry p0 q0))
        (fun q0 ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add p0 q0))
        (fun _ -> Big_int_Z.mult_int_big_int 2 (succ p0))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (succ q0))
        (fun q0 -> Big_int_Z.mult_int_big_int 2 (succ q0))
        (fun _ -> (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        Big_int_Z.unit_big_int)
        y)
      x

  (** val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 -> (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 p0))
      (fun p0 -> (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (pred_double p0))
      (fun _ -> Big_int_Z.unit_big_int)
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of Big_int_Z.big_int
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos Big_int_Z.unit_big_int
  | IsPos p0 ->
    IsPos ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) p0)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p0 -> IsPos (Big_int_Z.mult_int_big_int 2 p0)
  | x0 -> x0

  (** val double_pred_mask : Big_int_Z.big_int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 -> IsPos (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      p0)))
      (fun p0 -> IsPos (Big_int_Z.mult_int_big_int 2 (pred_double p0)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : Big_int_Z.big_int -> Big_int_Z.big_int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> double_mask (sub_mask p0 q0))
        (fun q0 -> succ_double_mask (sub_mask p0 q0))
        (fun _ -> IsPos (Big_int_Z.mult_int_big_int 2 p0))
        y)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> succ_double_mask (sub_mask_carry p0 q0))
        (fun q0 -> double_mask (sub_mask p0 q0))
        (fun _ -> IsPos (pred_double p0))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : Big_int_Z.big_int -> Big_int_Z.big_int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> succ_double_mask (sub_mask_carry p0 q0))
        (fun q0 -> double_mask (sub_mask p0 q0))
        (fun _ -> IsPos (pred_double p0))
        y)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> double_mask (sub_mask_carry p0 q0))
        (fun q0 -> succ_double_mask (sub_mask_carry p0 q0))
        (fun _ -> double_pred_mask p0)
        y)
      (fun _ -> IsNeg)
      x

  (** val mul : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec mul = Big_int_Z.mult_big_int

  (** val compare_cont :
      comparison -> Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let rec compare_cont = (fun c x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then c else if s < 0 then Lt else Gt)

  (** val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let compare = (fun x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then Eq else if s < 0 then Lt else Gt)

  (** val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec eqb p0 q0 =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p1 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q1 -> eqb p1 q1)
        (fun _ -> false)
        (fun _ -> false)
        q0)
      (fun p1 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun q1 -> eqb p1 q1)
        (fun _ -> false)
        q0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q0)
      p0
 end

module Z =
 struct
  (** val double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let double x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p0 -> (Big_int_Z.mult_int_big_int 2 p0))
      (fun p0 -> Big_int_Z.minus_big_int (Big_int_Z.mult_int_big_int 2 p0))
      x

  (** val succ_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let succ_double x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.unit_big_int)
      (fun p0 -> ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      p0))
      (fun p0 -> Big_int_Z.minus_big_int (Coq_Pos.pred_double p0))
      x

  (** val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let pred_double x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.minus_big_int Big_int_Z.unit_big_int)
      (fun p0 -> (Coq_Pos.pred_double p0))
      (fun p0 -> Big_int_Z.minus_big_int
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) p0))
      x

  (** val pos_sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> double (pos_sub p0 q0))
        (fun q0 -> succ_double (pos_sub p0 q0))
        (fun _ -> (Big_int_Z.mult_int_big_int 2 p0))
        y)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> pred_double (pos_sub p0 q0))
        (fun q0 -> double (pos_sub p0 q0))
        (fun _ -> (Coq_Pos.pred_double p0))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> Big_int_Z.minus_big_int (Big_int_Z.mult_int_big_int 2
        q0))
        (fun q0 -> Big_int_Z.minus_big_int (Coq_Pos.pred_double q0))
        (fun _ -> Big_int_Z.zero_big_int)
        y)
      x

  (** val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let add = Big_int_Z.add_big_int

  (** val opp : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let opp = Big_int_Z.minus_big_int

  (** val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sub = Big_int_Z.sub_big_int

  (** val mul : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let mul = Big_int_Z.mult_big_int

  (** val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let compare = (fun x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then Eq else if s < 0 then Lt else Gt)

  (** val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let eqb x y =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> false)
        (fun q0 -> Coq_Pos.eqb p0 q0)
        (fun _ -> false)
        y)
      (fun p0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q0 -> Coq_Pos.eqb p0 q0)
        y)
      x

  (** val of_N : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let of_N = (fun p -> p)

  (** val pos_div_eucl :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' =
        add (mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) r)
          Big_int_Z.unit_big_int
      in
      if ltb r' b
      then ((mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) q0), r')
      else ((add (mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) q0)
              Big_int_Z.unit_big_int), (sub r' b)))
      (fun a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) r in
      if ltb r' b
      then ((mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) q0), r')
      else ((add (mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) q0)
              Big_int_Z.unit_big_int), (sub r' b)))
      (fun _ ->
      if leb (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) b
      then (Big_int_Z.zero_big_int, Big_int_Z.unit_big_int)
      else (Big_int_Z.unit_big_int, Big_int_Z.zero_big_int))
      a

  (** val div_eucl :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int **)

  let div_eucl a b =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> (Big_int_Z.zero_big_int, Big_int_Z.zero_big_int))
      (fun a' ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> (Big_int_Z.zero_big_int, a))
        (fun _ -> pos_div_eucl a' b)
        (fun b' ->
        let (q0, r) = pos_div_eucl a' b' in
        ((fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
           (fun _ -> ((opp q0), Big_int_Z.zero_big_int))
           (fun _ -> ((opp (add q0 Big_int_Z.unit_big_int)), (add b r)))
           (fun _ -> ((opp (add q0 Big_int_Z.unit_big_int)), (add b r)))
           r))
        b)
      (fun a' ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> (Big_int_Z.zero_big_int, a))
        (fun _ ->
        let (q0, r) = pos_div_eucl a' b in
        ((fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
           (fun _ -> ((opp q0), Big_int_Z.zero_big_int))
           (fun _ -> ((opp (add q0 Big_int_Z.unit_big_int)), (sub b r)))
           (fun _ -> ((opp (add q0 Big_int_Z.unit_big_int)), (sub b r)))
           r))
        (fun b' -> let (q0, r) = pos_div_eucl a' b' in (q0, (opp r)))
        b)
      a

  (** val modulo : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let modulo a b = Big_int_Z.mod_big_int a b
 end

type t =
| F1 of nat
| FS of nat * t

(** val to_nat : nat -> t -> nat **)

let rec to_nat _ = function
| F1 _ -> O
| FS (n1, p0) -> S (to_nat n1 p0)

(** val of_nat_lt : nat -> nat -> t **)

let rec of_nat_lt p0 = function
| O -> assert false (* absurd case *)
| S n' -> (match p0 with
           | O -> F1 n'
           | S p' -> FS (n', (of_nat_lt p' n')))

type 'a t0 =
| Nil
| Cons of 'a * nat * 'a t0

(** val caseS : ('a1 -> nat -> 'a1 t0 -> 'a2) -> nat -> 'a1 t0 -> 'a2 **)

let caseS h _ = function
| Nil -> Obj.magic __
| Cons (h0, n0, t1) -> h h0 n0 t1

(** val hd : nat -> 'a1 t0 -> 'a1 **)

let hd n0 =
  caseS (fun h _ _ -> h) n0

(** val const : 'a1 -> nat -> 'a1 t0 **)

let rec const a = function
| O -> Nil
| S n1 -> Cons (a, n1, (const a n1))

(** val tl : nat -> 'a1 t0 -> 'a1 t0 **)

let tl n0 =
  caseS (fun _ _ t1 -> t1) n0

(** val locked_with : unit -> 'a1 -> 'a1 **)

let locked_with _ x =
  x

(** val ssr_have : 'a1 -> ('a1 -> 'a2) -> 'a2 **)

let ssr_have step rest =
  rest step

module Option =
 struct
  (** val apply : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2 **)

  let apply f0 x = function
  | Some y -> f0 y
  | None -> x

  (** val default : 'a1 -> 'a1 option -> 'a1 **)

  let default x =
    apply (fun x0 -> x0) x

  (** val bind : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option **)

  let bind f0 =
    apply f0 None

  (** val map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

  let map f0 =
    bind (fun x -> Some (f0 x))
 end

type ('aT, 'rT) simpl_fun =
  'aT -> 'rT
  (* singleton inductive, whose constructor was SimplFun *)

(** val fun_of_simpl : ('a1, 'a2) simpl_fun -> 'a1 -> 'a2 **)

let fun_of_simpl f0 =
  f0

(** val comp : ('a2 -> 'a1) -> ('a3 -> 'a2) -> 'a3 -> 'a1 **)

let comp f0 g0 x =
  f0 (g0 x)

(** val pcomp : ('a2 -> 'a1 option) -> ('a3 -> 'a2 option) -> 'a3 -> 'a1 option **)

let pcomp f0 g0 x =
  Option.bind f0 (g0 x)

(** val tag : ('a1, 'a2) sigT -> 'a1 **)

let tag =
  projT1

(** val tagged : ('a1, 'a2) sigT -> 'a2 **)

let tagged =
  projT2

(** val tagged0 : 'a1 -> 'a2 -> ('a1, 'a2) sigT **)

let tagged0 i x =
  ExistT (i, x)

(** val addb : bool -> bool -> bool **)

let addb = function
| true -> negb
| false -> (fun x -> x)

(** val isSome : 'a1 option -> bool **)

let isSome = function
| Some _ -> true
| None -> false

(** val introP : bool -> reflect **)

let introP = function
| true -> ReflectT
| false -> ReflectF

(** val iffP : bool -> reflect -> reflect **)

let iffP _ pb =
  let _evar_0_ = fun _ _ _ -> ReflectT in
  let _evar_0_0 = fun _ _ _ -> ReflectF in
  (match pb with
   | ReflectT -> _evar_0_ __ __ __
   | ReflectF -> _evar_0_0 __ __ __)

(** val idP : bool -> reflect **)

let idP = function
| true -> ReflectT
| false -> ReflectF

(** val andP : bool -> bool -> reflect **)

let andP b1 b2 =
  if b1 then if b2 then ReflectT else ReflectF else ReflectF

type 't pred0 = 't -> bool

type 't predType =
  __ -> 't pred0
  (* singleton inductive, whose constructor was PredType *)

type 't pred_sort = __

(** val predPredType : 'a1 predType **)

let predPredType x =
  Obj.magic x

type 't simpl_pred = ('t, bool) simpl_fun

(** val simplPred : 'a1 pred0 -> 'a1 simpl_pred **)

let simplPred p0 =
  p0

(** val predT : 'a1 simpl_pred **)

let predT _ = true

(** val predD : 'a1 pred0 -> 'a1 pred0 -> 'a1 simpl_pred **)

let predD p1 p2 =
  simplPred (fun x -> (&&) (negb (p2 x)) (p1 x))

module PredOfSimpl =
 struct
  (** val coerce : 'a1 simpl_pred -> 'a1 pred0 **)

  let coerce =
    fun_of_simpl
 end

(** val simplPredType : 'a1 predType **)

let simplPredType =
  Obj.magic PredOfSimpl.coerce

(** val pred_of_argType : 'a1 simpl_pred **)

let pred_of_argType =
  predT

type 't rel = 't -> 't pred0

type 't mem_pred = 't pred0
  (* singleton inductive, whose constructor was Mem *)

(** val pred_of_mem : 'a1 mem_pred -> 'a1 pred_sort **)

let pred_of_mem mp =
  Obj.magic mp

(** val in_mem : 'a1 -> 'a1 mem_pred -> bool **)

let in_mem x mp =
  Obj.magic pred_of_mem mp x

(** val simpl_of_mem : 'a1 mem_pred -> 'a1 simpl_pred **)

let simpl_of_mem mp =
  simplPred (fun x -> in_mem x mp)

(** val mem : 'a1 predType -> 'a1 pred_sort -> 'a1 mem_pred **)

let mem pT =
  pT

type 't qualifier =
  't pred_sort
  (* singleton inductive, whose constructor was Qualifier *)

(** val has_quality : nat -> 'a1 qualifier -> 'a1 pred_sort **)

let has_quality _ q0 =
  Obj.magic (fun x -> Obj.magic q0 x)

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

module RingAddationalLemmas =
 functor (Ring:RingSig) ->
 struct
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

module FieldAddationalLemmas =
 functor (Field:FieldSig) ->
 struct
  module AL = RingAddationalLemmas(Field)
 end

module VectorSpaceAddationalLemmas =
 functor (Group:GroupSig) ->
 functor (Field:FieldSig) ->
 functor (VS:sig
  val op : Group.coq_G -> Field.coq_F -> Group.coq_G
 end) ->
 struct
  module AL = RingAddationalLemmas(Field)
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

  (** val coq_Ggen : Group.coq_G * Group.coq_G **)

  let coq_Ggen =
    (Group.coq_Ggen, Group.coq_Ggen)

  (** val coq_Gbool_eq : coq_G -> coq_G -> bool **)

  let coq_Gbool_eq a b =
    (&&) (Group.coq_Gbool_eq (fst a) (fst b)) (Group.coq_Gbool_eq (snd a) (snd b))

  (** val coq_Gdisjoint : coq_G -> coq_G -> bool **)

  let coq_Gdisjoint a b =
    (&&) (Group.coq_Gdisjoint (fst a) (fst b)) (Group.coq_Gdisjoint (snd a) (snd b))

  (** val coq_Ginv : (Group.coq_G * Group.coq_G) -> Group.coq_G * Group.coq_G **)

  let coq_Ginv a =
    ((Group.coq_Ginv (fst a)), (Group.coq_Ginv (snd a)))
 end

module DualVectorSpaceIns =
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
 struct
  (** val op : DualGroup.coq_G -> Field.coq_F -> Group.coq_G * Group.coq_G **)

  let op a b =
    ((VS.op (fst a) b), (VS.op (snd a) b))
 end

type 'a rel_dec = 'a -> 'a -> bool

(** val dec_beq : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool **)

let dec_beq beq x y =
  let b = beq x y in if b then true else false

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

(** val vcast : nat -> 'a1 t0 -> nat -> 'a1 t0 **)

let vcast _ v _ =
  v

(** val vnth : nat -> 'a1 t0 -> nat -> 'a1 **)

let rec vnth _ v i =
  match v with
  | Nil -> assert false (* absurd case *)
  | Cons (x, wildcard', v') -> (match i with
                                | O -> x
                                | S j -> vnth wildcard' v' j)

(** val vadd : nat -> 'a1 t0 -> 'a1 -> 'a1 t0 **)

let rec vadd _ v x =
  match v with
  | Nil -> Cons (x, O, Nil)
  | Cons (a, n0, v') -> Cons (a, (S n0), (vadd n0 v' x))

(** val vreplace : nat -> 'a1 t0 -> nat -> 'a1 -> 'a1 t0 **)

let rec vreplace _ v i a =
  match v with
  | Nil -> assert false (* absurd case *)
  | Cons (h, wildcard', v') ->
    (match i with
     | O -> Cons (a, wildcard', v')
     | S i' -> Cons (h, wildcard', (vreplace wildcard' v' i' a)))

(** val vapp : nat -> nat -> 'a1 t0 -> 'a1 t0 -> 'a1 t0 **)

let rec vapp _ n2 v1 v2 =
  match v1 with
  | Nil -> v2
  | Cons (a, n0, v') -> Cons (a, (add n0 n2), (vapp n0 n2 v' v2))

(** val vbreak : nat -> nat -> 'a1 t0 -> 'a1 t0 * 'a1 t0 **)

let rec vbreak n1 n2 v =
  match n1 with
  | O -> (Nil, v)
  | S p1 ->
    let w =
      vbreak p1 n2
        (tl
          (let rec add5 n0 m0 =
             match n0 with
             | O -> m0
             | S p0 -> S (add5 p0 m0)
           in add5 p1 n2) v)
    in
    ((Cons
    ((hd
       (let rec add5 n0 m0 =
          match n0 with
          | O -> m0
          | S p0 -> S (add5 p0 m0)
        in add5 p1 n2) v), p1, (fst w))), (snd w))

(** val vsub : nat -> 'a1 t0 -> nat -> nat -> 'a1 t0 **)

let rec vsub n0 v i = function
| O -> Nil
| S k' -> Cons ((vnth n0 v i), k', (vsub n0 v (S i) k'))

(** val vremove_last : nat -> 'a1 t0 -> 'a1 t0 **)

let vremove_last n0 v =
  vsub (S n0) v O n0

(** val vlast : 'a1 -> nat -> 'a1 t0 -> 'a1 **)

let rec vlast default0 _ = function
| Nil -> default0
| Cons (x, n0, v') -> vlast x n0 v'

(** val vmap : ('a1 -> 'a2) -> nat -> 'a1 t0 -> 'a2 t0 **)

let rec vmap f0 _ = function
| Nil -> Nil
| Cons (a, n0, v') -> Cons ((f0 a), n0, (vmap f0 n0 v'))

(** val bVforall : ('a1 -> bool) -> nat -> 'a1 t0 -> bool **)

let rec bVforall f0 _ = function
| Nil -> true
| Cons (a, n0, w) -> (&&) (f0 a) (bVforall f0 n0 w)

(** val vforall2_aux_dec :
    ('a1 -> 'a2 -> bool) -> nat -> 'a1 t0 -> nat -> 'a2 t0 -> bool **)

let rec vforall2_aux_dec r_dec _ v1 _ v2 =
  match v1 with
  | Nil -> (match v2 with
            | Nil -> true
            | Cons (_, _, _) -> false)
  | Cons (h, n0, t1) ->
    (match v2 with
     | Nil -> false
     | Cons (h0, n1, t2) ->
       let s = vforall2_aux_dec r_dec n0 t1 n1 t2 in if s then r_dec h h0 else false)

(** val vforall2_dec : ('a1 -> 'a2 -> bool) -> nat -> 'a1 t0 -> 'a2 t0 -> bool **)

let vforall2_dec r_dec n0 v w =
  vforall2_aux_dec r_dec n0 v n0 w

(** val bVforall2_aux :
    ('a1 -> 'a2 -> bool) -> nat -> nat -> 'a1 t0 -> 'a2 t0 -> bool **)

let rec bVforall2_aux f0 _ _ v1 v2 =
  match v1 with
  | Nil -> (match v2 with
            | Nil -> true
            | Cons (_, _, _) -> false)
  | Cons (x, n0, xs) ->
    (match v2 with
     | Nil -> false
     | Cons (y, n1, ys) -> (&&) (f0 x y) (bVforall2_aux f0 n0 n1 xs ys))

(** val bVforall2 : ('a1 -> 'a2 -> bool) -> nat -> 'a1 t0 -> 'a2 t0 -> bool **)

let bVforall2 f0 n0 v1 v2 =
  bVforall2_aux f0 n0 n0 v1 v2

(** val bVexists : ('a1 -> bool) -> nat -> 'a1 t0 -> bool **)

let rec bVexists f0 _ = function
| Nil -> false
| Cons (a, n0, v') -> (||) (f0 a) (bVexists f0 n0 v')

(** val vbuild : nat -> (nat -> __ -> 'a1) -> 'a1 t0 **)

let rec vbuild n0 x =
  match n0 with
  | O -> Nil
  | S p0 -> Cons ((x O __), p0, (vbuild p0 (fun i _ -> x (S i) __)))

(** val vfold_left : ('a1 -> 'a2 -> 'a1) -> nat -> 'a1 -> 'a2 t0 -> 'a1 **)

let rec vfold_left f0 _ a = function
| Nil -> a
| Cons (b, n0, w) -> vfold_left f0 n0 (f0 a b) w

(** val vfold_left_rev : ('a1 -> 'a2 -> 'a1) -> nat -> 'a1 -> 'a2 t0 -> 'a1 **)

let rec vfold_left_rev f0 _ a = function
| Nil -> a
| Cons (b, n0, w) -> f0 (vfold_left_rev f0 n0 a w) b

(** val vmap2 : ('a1 -> 'a2 -> 'a3) -> nat -> 'a1 t0 -> 'a2 t0 -> 'a3 t0 **)

let rec vmap2 f0 n0 x x0 =
  match n0 with
  | O -> Nil
  | S n1 -> Cons ((f0 (hd n1 x) (hd n1 x0)), n1, (vmap2 f0 n1 (tl n1 x) (tl n1 x0)))

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

  (** val zero_vec : nat -> SRT.ES.Eq.coq_A t0 **)

  let zero_vec =
    const SRT.coq_A0

  (** val id_vec : nat -> nat -> SRT.ES.Eq.coq_A t0 **)

  let id_vec n0 i =
    vreplace n0 (zero_vec n0) i SRT.coq_A1

  (** val vector_plus :
      nat -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A t0 **)

  let vector_plus n0 v1 v2 =
    vmap2 SRT.coq_Aplus n0 v1 v2

  (** val add_vectors : nat -> nat -> SRT.ES.Eq.coq_A t0 t0 -> SRT.ES.Eq.coq_A t0 **)

  let add_vectors n0 k v =
    vfold_left_rev (vector_plus n0) k (zero_vec n0) v

  (** val dot_product :
      nat -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A **)

  let dot_product n0 l r =
    vfold_left_rev SRT.coq_Aplus n0 SRT.coq_A0 (vmap2 SRT.coq_Amult n0 l r)
 end

module Matrix =
 functor (SRT:SemiRingType) ->
 struct
  module SR = SemiRing(SRT)

  module VA = VectorArith(SRT)

  type matrix = SRT.ES.Eq.coq_A t0 t0

  (** val get_row : nat -> nat -> matrix -> nat -> SRT.ES.Eq.coq_A t0 **)

  let get_row m0 _ m1 i =
    vnth m0 m1 i

  (** val get_col : nat -> nat -> matrix -> nat -> SRT.ES.Eq.coq_A t0 **)

  let get_col m0 n0 m1 i =
    vmap (fun v -> vnth n0 v i) m0 m1

  (** val get_elem : nat -> nat -> matrix -> nat -> nat -> SRT.ES.Eq.coq_A **)

  let get_elem m0 n0 m1 i j =
    vnth n0 (get_row m0 n0 m1 i) j

  (** val mat_build_spec :
      nat -> nat -> (nat -> nat -> __ -> __ -> SRT.ES.Eq.coq_A) -> matrix **)

  let rec mat_build_spec n0 n1 gen =
    match n0 with
    | O -> Nil
    | S n2 ->
      let gen' = fun i j -> gen (S i) j __ in
      let s = mat_build_spec n2 n1 (fun i j _ -> gen' i j) in
      let gen_1 = fun j -> gen O j __ in
      let mhd = vbuild n1 gen_1 in Cons (mhd, n2, s)

  (** val mat_build :
      nat -> nat -> (nat -> nat -> __ -> __ -> SRT.ES.Eq.coq_A) -> matrix **)

  let mat_build =
    mat_build_spec

  (** val zero_matrix : nat -> nat -> matrix **)

  let zero_matrix m0 n0 =
    mat_build m0 n0 (fun _ _ _ _ -> SRT.coq_A0)

  (** val id_matrix : nat -> matrix **)

  let id_matrix n0 =
    vbuild n0 (fun i _ -> VA.id_vec n0 i)

  (** val inverse_matrix :
      (SRT.ES.Eq.coq_A -> SRT.ES.Eq.coq_A) -> nat -> nat -> matrix -> matrix **)

  let inverse_matrix inv5 m0 n0 m1 =
    mat_build m0 n0 (fun i j _ _ -> inv5 (get_elem m0 n0 m1 i j))

  type row_mat = matrix

  type col_mat = matrix

  (** val vec_to_row_mat : nat -> SRT.ES.Eq.coq_A t0 -> row_mat **)

  let vec_to_row_mat _ v =
    Cons (v, O, Nil)

  (** val vec_to_col_mat : nat -> SRT.ES.Eq.coq_A t0 -> col_mat **)

  let vec_to_col_mat n0 v =
    vmap (fun i -> Cons (i, O, Nil)) n0 v

  (** val row_mat_to_vec : nat -> row_mat -> SRT.ES.Eq.coq_A t0 **)

  let row_mat_to_vec n0 m0 =
    get_row (S O) n0 m0 O

  (** val col_mat_to_vec : nat -> col_mat -> SRT.ES.Eq.coq_A t0 **)

  let col_mat_to_vec n0 m0 =
    get_col n0 (S O) m0 O

  (** val mat_transpose : nat -> nat -> matrix -> matrix **)

  let mat_transpose m0 n0 m1 =
    mat_build n0 m0 (fun i j _ _ -> get_elem m0 n0 m1 j i)

  (** val vec_plus :
      nat -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A t0 **)

  let vec_plus n0 l r =
    vmap2 SRT.coq_Aplus n0 l r

  (** val mat_plus : nat -> nat -> matrix -> matrix -> SRT.ES.Eq.coq_A t0 t0 **)

  let mat_plus m0 n0 l r =
    vmap2 (vec_plus n0) m0 l r

  (** val mat_mult : nat -> nat -> nat -> matrix -> matrix -> matrix **)

  let mat_mult m0 n0 p0 l r =
    mat_build m0 p0 (fun i j _ _ ->
      VA.dot_product n0 (get_row m0 n0 l i) (get_col n0 p0 r j))

  (** val mat_vec_prod :
      nat -> nat -> matrix -> SRT.ES.Eq.coq_A t0 -> SRT.ES.Eq.coq_A t0 **)

  let mat_vec_prod m0 n0 m1 v =
    col_mat_to_vec m0 (mat_mult m0 n0 (S O) m1 (vec_to_col_mat n0 v))

  (** val mat_forall2'_dec :
      nat -> nat -> SRT.ES.Eq.coq_A rel_dec -> matrix rel_dec **)

  let mat_forall2'_dec m0 n0 p_dec m1 n1 =
    vforall2_dec (vforall2_dec p_dec n0) m0 m1 n1

  (** val mat_forall2_dec :
      nat -> nat -> SRT.ES.Eq.coq_A rel_dec -> matrix rel_dec **)

  let mat_forall2_dec =
    mat_forall2'_dec
 end

(** val vlastS : nat -> 'a1 t0 -> 'a1 **)

let vlastS n0 a =
  vlast (hd n0 a) (S n0) a

(** val rev : nat -> 'a1 t0 -> 'a1 t0 **)

let rev n0 input =
  vbuild n0 (fun i _ -> vnth n0 input (sub (sub n0 i) (S O)))

(** val zip : nat -> 'a1 t0 -> 'a2 t0 -> ('a1 * 'a2) t0 **)

let zip n0 a b =
  vmap2 (fun x y -> (x, y)) n0 a b

(** val unzipLeft : nat -> ('a1 * 'a2) t0 -> 'a1 t0 **)

let unzipLeft n0 ab =
  vmap fst n0 ab

(** val unzipRight : nat -> ('a1 * 'a2) t0 -> 'a2 t0 **)

let unzipRight n0 ab =
  vmap snd n0 ab

(** val pairwisePredicate : nat -> ('a1 -> 'a1 -> bool) -> 'a1 t0 -> bool **)

let rec pairwisePredicate _ f0 = function
| Nil -> true
| Cons (a, n0, w) -> (&&) (bVforall (f0 a) n0 w) (pairwisePredicate n0 f0 w)

(** val bVforall3 :
    nat -> ('a1 -> 'a2 -> 'a3 -> bool) -> 'a1 t0 -> 'a2 t0 -> 'a3 t0 -> bool **)

let rec bVforall3 n0 f0 x x0 x1 =
  match n0 with
  | O -> true
  | S a ->
    (&&) (f0 (hd a x) (hd a x0) (hd a x1))
      (bVforall3 a f0 (tl a x) (tl a x0) (tl a x1))

type index = nat

(** val makeIndex : nat -> nat -> index **)

let makeIndex _ i =
  i

(** val makeIndexSucc : nat -> index -> index **)

let makeIndexSucc _ x =
  S x

(** val vremove : nat -> 'a1 t0 -> nat -> 'a1 t0 **)

let vremove n0 v i =
  vcast (add i (sub (S n0) (S i)))
    (vapp i (sub (S n0) (S i)) (vsub (S n0) v O i)
      (vsub (S n0) v (S i) (sub (S n0) (S i)))) n0

(** val vecToMat : nat -> nat -> 'a1 t0 -> 'a1 t0 t0 **)

let vecToMat n0 n' v =
  vbuild n' (fun i _ -> vsub (mul n0 n') v (mul n0 i) n0)

(** val matToVec : nat -> nat -> 'a1 t0 t0 -> 'a1 t0 **)

let matToVec n0 n' v =
  vbuild (mul n0 n') (fun i _ ->
    vnth n0 (vnth n' v (Nat.div i n0)) (Nat.modulo i n0))

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

  module ALR = RingAddationalLemmas(Ring)

  type coq_VF = Ring.coq_F t0

  (** val coq_VF_zero : nat -> Ring.coq_F t0 **)

  let coq_VF_zero =
    const Ring.coq_Fzero

  (** val coq_VF_one : nat -> Ring.coq_F t0 **)

  let coq_VF_one =
    const Ring.coq_Fone

  (** val coq_VF_n_id : nat -> nat -> FSemiRingT.ES.Eq.coq_A t0 **)

  let coq_VF_n_id n0 n1 =
    FMatrix.VA.id_vec n1 n0

  (** val coq_VF_prod : nat -> coq_VF -> Ring.coq_F **)

  let coq_VF_prod n0 v =
    vfold_left Ring.coq_Fmul n0 Ring.coq_Fone v

  (** val coq_VF_sum : nat -> coq_VF -> Ring.coq_F **)

  let coq_VF_sum n0 v =
    vfold_left Ring.coq_Fadd n0 Ring.coq_Fzero v

  (** val coq_VF_add : nat -> coq_VF -> coq_VF -> coq_VF **)

  let coq_VF_add =
    FMatrix.VA.vector_plus

  (** val coq_VF_neg : nat -> coq_VF -> coq_VF **)

  let coq_VF_neg n0 v1 =
    vmap Ring.coq_Finv n0 v1

  (** val coq_VF_sub : nat -> coq_VF -> coq_VF -> coq_VF **)

  let coq_VF_sub n0 v1 v2 =
    coq_VF_add n0 v1 (coq_VF_neg n0 v2)

  (** val coq_VF_mult : nat -> coq_VF -> coq_VF -> coq_VF **)

  let coq_VF_mult n0 v1 v2 =
    vmap2 Ring.coq_Fmul n0 v1 v2

  (** val coq_VF_scale : nat -> coq_VF -> Ring.coq_F -> coq_VF **)

  let coq_VF_scale n0 v s =
    vmap (fun x -> Ring.coq_Fmul x s) n0 v

  (** val coq_VF_inProd : nat -> coq_VF -> coq_VF -> Ring.coq_F **)

  let coq_VF_inProd =
    FMatrix.VA.dot_product

  (** val coq_VF_beq : nat -> coq_VF -> coq_VF -> bool **)

  let coq_VF_beq n0 r r' =
    bVforall2 Ring.coq_Fbool_eq n0 r r'

  (** val coq_VF_an_id : nat -> coq_VF -> bool **)

  let coq_VF_an_id n0 v =
    bVexists (coq_VF_beq n0 v) n0 (vbuild n0 (fun i _ -> FMatrix.VA.id_vec n0 i))

  type coq_MF = FMatrix.matrix

  (** val coq_MF_id : nat -> coq_MF **)

  let coq_MF_id =
    FMatrix.id_matrix

  (** val coq_MF_col : nat -> coq_MF -> nat -> coq_VF **)

  let coq_MF_col n0 m0 i =
    FMatrix.get_col n0 n0 m0 i

  (** val coq_MF_row : nat -> coq_MF -> nat -> coq_VF **)

  let coq_MF_row n0 m0 i =
    FMatrix.get_row n0 n0 m0 i

  (** val coq_MF_mult : nat -> coq_MF -> coq_MF -> coq_MF **)

  let coq_MF_mult n0 m0 m' =
    FMatrix.mat_mult n0 n0 n0 m0 m'

  (** val coq_MF_trans : nat -> coq_MF -> coq_MF **)

  let coq_MF_trans n0 m0 =
    FMatrix.mat_transpose n0 n0 m0

  (** val coq_MF_CVmult : nat -> coq_MF -> coq_VF -> coq_VF **)

  let coq_MF_CVmult n0 m0 v =
    FMatrix.mat_vec_prod n0 n0 m0 v

  (** val coq_MF_VCmult : nat -> coq_VF -> coq_MF -> coq_VF **)

  let coq_MF_VCmult n0 v m0 =
    FMatrix.row_mat_to_vec n0
      (FMatrix.mat_mult (S O) n0 n0 (FMatrix.vec_to_row_mat n0 v) m0)

  (** val coq_MF_Fscal : nat -> coq_MF -> coq_VF -> coq_MF **)

  let coq_MF_Fscal n0 m0 v =
    FMatrix.mat_build n0 n0 (fun i j _ _ ->
      vnth n0 (coq_VF_mult n0 (FMatrix.get_row n0 n0 m0 i) v) j)

  (** val coq_MF_scal : nat -> coq_MF -> Ring.coq_F -> coq_MF **)

  let coq_MF_scal n0 m0 a =
    FMatrix.mat_build n0 n0 (fun i j _ _ ->
      Ring.coq_Fmul (FMatrix.get_elem n0 n0 m0 i j) a)

  (** val coq_MFisPermutation : nat -> coq_MF -> bool **)

  let coq_MFisPermutation n0 m0 =
    (&&) (bVforall (coq_VF_an_id n0) n0 m0)
      (bVforall (coq_VF_an_id n0) n0 (FMatrix.mat_transpose n0 n0 m0))

  (** val coq_VF_eq_dec : nat -> coq_VF -> coq_VF -> bool **)

  let coq_VF_eq_dec n0 a y =
    if coq_VF_beq n0 a y then true else false

  (** val coq_MF_perm_last : nat -> coq_MF -> index **)

  let rec coq_MF_perm_last n0 x =
    match n0 with
    | O -> makeIndex (S O) O
    | S a ->
      if coq_VF_beq (S (S a)) (hd (S a) x) (FMatrix.VA.id_vec (S (S a)) (S a))
      then makeIndex (S (S a)) O
      else makeIndexSucc (S a)
             (coq_MF_perm_last a (vmap (fun a0 -> tl (S a) a0) (S a) (tl (S a) x)))

  (** val coq_MF_perm_sub : nat -> coq_MF -> coq_MF **)

  let coq_MF_perm_sub n0 m0 =
    vmap (fun a -> vremove_last n0 a) n0 (vremove n0 m0 (coq_MF_perm_last n0 m0))

  (** val matRecover_sub : nat -> Ring.coq_F -> nat **)

  let rec matRecover_sub m0 f0 =
    match m0 with
    | O -> O
    | S a ->
      if Ring.coq_Fbool_eq f0 (coq_VF_sum a (const Ring.coq_Fone a))
      then a
      else matRecover_sub a f0

  (** val matRecover : nat -> coq_VF -> coq_MF **)

  let matRecover n0 a =
    vmap (fun a0 -> FMatrix.VA.id_vec (S n0) (matRecover_sub (S n0) a0)) (S n0) a
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
 struct
  module AddMLemmas = ModuleAddationalLemmas(Group)(Ring)(M)

  type coq_VG = Group.coq_G t0

  (** val coq_VG_id : nat -> Group.coq_G t0 **)

  let coq_VG_id =
    const Group.coq_Gone

  (** val coq_VG_mult : nat -> coq_VG -> coq_VG -> coq_VG **)

  let coq_VG_mult n0 v v' =
    vmap2 Group.coq_Gdot n0 v v'

  (** val coq_VG_inv : nat -> coq_VG -> coq_VG **)

  let coq_VG_inv n0 v =
    vmap Group.coq_Ginv n0 v

  (** val coq_VG_prod : nat -> coq_VG -> Group.coq_G **)

  let coq_VG_prod n0 v =
    vfold_left Group.coq_Gdot n0 Group.coq_Gone v

  (** val coq_VG_Pexp : nat -> coq_VG -> MatF.coq_VF -> coq_VG **)

  let coq_VG_Pexp n0 v v' =
    vmap2 M.op n0 v v'

  (** val coq_VG_Sexp : nat -> coq_VG -> Ring.coq_F -> coq_VG **)

  let coq_VG_Sexp n0 v e =
    vmap (fun x -> M.op x e) n0 v

  (** val coq_VG_eq : nat -> coq_VG -> coq_VG -> bool **)

  let coq_VG_eq n0 m0 m' =
    bVforall2 Group.coq_Gbool_eq n0 m0 m'

  (** val coq_VG_MF_exp_coll : nat -> coq_VG -> MatF.coq_MF -> coq_VG **)

  let coq_VG_MF_exp_coll n0 c b =
    vbuild n0 (fun i _ -> coq_VG_prod n0 (coq_VG_Pexp n0 c (MatF.coq_MF_col n0 b i)))

  (** val coq_VG_MF_exp_row : nat -> coq_VG -> MatF.coq_MF -> coq_VG **)

  let coq_VG_MF_exp_row n0 c b =
    vbuild n0 (fun i _ -> coq_VG_prod n0 (coq_VG_Pexp n0 c (vnth n0 b i)))

  (** val coq_PexpMatrix : nat -> coq_VG -> MatF.coq_MF -> coq_VG **)

  let coq_PexpMatrix n0 c e =
    vmap (fun row -> coq_VG_prod n0 (coq_VG_Pexp n0 c row)) n0 e

  (** val coq_VG_scale_sum :
      nat -> nat -> nat -> MatF.coq_VF t0 t0 -> MatF.coq_VF t0 **)

  let coq_VG_scale_sum n0 j m0 b =
    vfold_left (fun x y -> vmap2 (MatF.coq_VF_add n0) j x y) m0
      (const (MatF.coq_VF_zero n0) j) b
 end

(** val predType0 : ('a2 -> 'a1 pred0) -> 'a1 predType **)

let predType0 x =
  Obj.magic x

module Equality =
 struct
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  (** val op : 'a1 mixin_of -> 'a1 rel **)

  let op m0 =
    m0.op

  type coq_type = __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort mixin_of **)

  let coq_class cT =
    cT
 end

(** val eq_op : Equality.coq_type -> Equality.sort rel **)

let eq_op t1 =
  (Equality.coq_class t1).Equality.op

(** val eqP : Equality.coq_type -> Equality.sort Equality.axiom **)

let eqP t1 =
  let _evar_0_ = fun _ a -> a in
  let { Equality.op = op1; Equality.mixin_of__1 = a } = t1 in _evar_0_ op1 a

(** val eqb0 : bool -> bool -> bool **)

let eqb0 b =
  addb (negb b)

(** val eqbP : bool Equality.axiom **)

let eqbP __top_assumption_ =
  let _evar_0_ = fun __top_assumption_0 ->
    let _evar_0_ = ReflectT in
    let _evar_0_0 = ReflectF in if __top_assumption_0 then _evar_0_ else _evar_0_0
  in
  let _evar_0_0 = fun __top_assumption_0 ->
    let _evar_0_0 = ReflectF in
    let _evar_0_1 = ReflectT in if __top_assumption_0 then _evar_0_0 else _evar_0_1
  in
  if __top_assumption_ then _evar_0_ else _evar_0_0

(** val bool_eqMixin : bool Equality.mixin_of **)

let bool_eqMixin =
  { Equality.op = eqb0; Equality.mixin_of__1 = eqbP }

(** val bool_eqType : Equality.coq_type **)

let bool_eqType =
  Obj.magic bool_eqMixin

(** val pred1 : Equality.coq_type -> Equality.sort -> Equality.sort simpl_pred **)

let pred1 t1 a1 =
  simplPred (fun x -> eq_op t1 x a1)

type 't subType = { val0 : (__ -> 't); sub0 : ('t -> __ -> __);
                    subType__2 : (__ -> ('t -> __ -> __) -> __ -> __) }

type 't sub_sort = __

(** val sub0 : 'a1 pred0 -> 'a1 subType -> 'a1 -> 'a1 sub_sort **)

let sub0 _ s x =
  s.sub0 x __

(** val insub : 'a1 pred0 -> 'a1 subType -> 'a1 -> 'a1 sub_sort option **)

let insub p0 sT x =
  match idP (p0 x) with
  | ReflectT -> Some (sub0 p0 sT x)
  | ReflectF -> None

(** val insubd : 'a1 pred0 -> 'a1 subType -> 'a1 sub_sort -> 'a1 -> 'a1 sub_sort **)

let insubd p0 sT u0 x =
  Option.default u0 (insub p0 sT x)

(** val s2val : 'a1 sig2 -> 'a1 **)

let s2val u =
  u

(** val inj_eq
m :
    Equality.coq_type -> ('a1 -> Equality.sort) -> 'a1 Equality.axiom **)

let inj_eqAxiom eT f0 x y =
  iffP (eq_op eT (f0 x) (f0 y)) (eqP eT (f0 x) (f0 y))

(** val injEqMixin :
    Equality.coq_type -> ('a1 -> Equality.sort) -> 'a1 Equality.mixin_of **)

let injEqMixin eT f0 =
  { Equality.op = (fun x y -> eq_op eT (f0 x) (f0 y)); Equality.mixin_of__1 =
    (inj_eqAxiom eT f0) }

(** val pcanEqMixin :
    Equality.coq_type -> ('a1 -> Equality.sort) -> (Equality.sort -> 'a1 option) ->
    'a1 Equality.mixin_of **)

let pcanEqMixin eT f0 _ =
  injEqMixin eT f0

(** val val_eqP :
    Equality.coq_type -> Equality.sort pred0 -> Equality.sort subType ->
    Equality.sort sub_sort Equality.axiom **)

let val_eqP t1 _ sT =
  inj_eqAxiom t1 sT.val0

(** val sub_eqMixin :
    Equality.coq_type -> Equality.sort pred0 -> Equality.sort subType ->
    Equality.sort sub_sort Equality.mixin_of **)

let sub_eqMixin t1 p0 sT =
  { Equality.op = (fun x y -> eq_op t1 (sT.val0 x) (sT.val0 y));
    Equality.mixin_of__1 = (val_eqP t1 p0 sT) }

(** val pair_eq :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort) rel **)

let pair_eq t1 t2 u v =
  (&&) (eq_op t1 (fst u) (fst v)) (eq_op t2 (snd u) (snd v))

(** val pair_eqP :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
    Equality.axiom **)

let pair_eqP t1 t2 __top_assumption_ =
  let _evar_0_ = fun x1 x2 __top_assumption_0 ->
    let _evar_0_ = fun y1 y2 ->
      iffP
        ((&&) (eq_op t1 (fst (x1, x2)) (fst (y1, y2)))
          (eq_op t2 (snd (x1, x2)) (snd (y1, y2))))
        (andP (eq_op t1 (fst (x1, x2)) (fst (y1, y2)))
          (eq_op t2 (snd (x1, x2)) (snd (y1, y2))))
    in
    let (a, b) = __top_assumption_0 in _evar_0_ a b
  in
  let (a, b) = __top_assumption_ in _evar_0_ a b

(** val prod_eqMixin :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
    Equality.mixin_of **)

let prod_eqMixin t1 t2 =
  { Equality.op = (pair_eq t1 t2); Equality.mixin_of__1 = (pair_eqP t1 t2) }

(** val prod_eqType : Equality.coq_type -> Equality.coq_type -> Equality.coq_type **)

let prod_eqType t1 t2 =
  Obj.magic prod_eqMixin t1 t2

(** val tagged_as :
    Equality.coq_type -> (Equality.sort, 'a1) sigT -> (Equality.sort, 'a1) sigT ->
    'a1 **)

let tagged_as i u v =
  match eqP i (tag u) (tag v) with
  | ReflectT -> tagged v
  | ReflectF -> tagged u

(** val tag_eq :
    Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> (Equality.sort,
    Equality.sort) sigT -> (Equality.sort, Equality.sort) sigT -> bool **)

let tag_eq i t_ u v =
  (&&) (eq_op i (tag u) (tag v)) (eq_op (t_ (tag u)) (tagged u) (tagged_as i u v))

(** val tag_eqP :
    Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> (Equality.sort,
    Equality.sort) sigT Equality.axiom **)

let tag_eqP i t_ __top_assumption_ =
  let _evar_0_ = fun i0 x __top_assumption_0 ->
    let _evar_0_ = fun j ->
      let _evar_0_ = fun y ->
        iffP (eq_op (t_ i0) x (tagged_as i (ExistT (i0, x)) (ExistT (i0, y))))
          (eqP (t_ i0) x (tagged_as i (ExistT (i0, x)) (ExistT (i0, y))))
      in
      let _evar_0_0 = fun _ -> ReflectF in
      (match eqP i i0 j with
       | ReflectT -> _evar_0_
       | ReflectF -> _evar_0_0)
    in
    let ExistT (x0, p0) = __top_assumption_0 in _evar_0_ x0 p0
  in
  let ExistT (x, p0) = __top_assumption_ in _evar_0_ x p0

(** val tag_eqMixin :
    Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> (Equality.sort,
    Equality.sort) sigT Equality.mixin_of **)

let tag_eqMixin i t_ =
  { Equality.op = (tag_eq i t_); Equality.mixin_of__1 = (tag_eqP i t_) }

(** val tag_eqType :
    Equality.coq_type -> (Equality.sort -> Equality.coq_type) -> Equality.coq_type **)

let tag_eqType i t_ =
  Obj.magic tag_eqMixin i t_

(** val eqn : nat -> nat -> bool **)

let rec eqn m0 n0 =
  match m0 with
  | O -> (match n0 with
          | O -> true
          | S _ -> false)
  | S m' -> (match n0 with
             | O -> false
             | S n' -> eqn m' n')

(** val eqnP : nat Equality.axiom **)

let eqnP n0 m0 =
  iffP (eqn n0 m0) (idP (eqn n0 m0))

(** val nat_eqMixin : nat Equality.mixin_of **)

let nat_eqMixin =
  { Equality.op = eqn; Equality.mixin_of__1 = eqnP }

(** val nat_eqType : Equality.coq_type **)

let nat_eqType =
  Obj.magic nat_eqMixin

(** val addn_rec : nat -> nat -> nat **)

let addn_rec =
  add

(** val addn : nat -> nat -> nat **)

let addn =
  addn_rec

(** val subn_rec : nat -> nat -> nat **)

let subn_rec =
  sub

(** val subn : nat -> nat -> nat **)

let subn =
  subn_rec

(** val leq : nat -> nat -> bool **)

let leq m0 n0 =
  eq_op nat_eqType (Obj.magic subn m0 n0) (Obj.magic O)

(** val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iter n0 f0 x =
  match n0 with
  | O -> x
  | S i -> f0 (iter i f0 x)

(** val iteri : nat -> (nat -> 'a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iteri n0 f0 x =
  match n0 with
  | O -> x
  | S i -> f0 i (iteri i f0 x)

(** val iterop : nat -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

let iterop n0 op1 x =
  let f0 = fun i y -> match i with
                      | O -> x
                      | S _ -> op1 x y in iteri n0 f0

(** val muln_rec : nat -> nat -> nat **)

let muln_rec =
  mul

(** val muln : nat -> nat -> nat **)

let muln =
  muln_rec

(** val expn_rec : nat -> nat -> nat **)

let expn_rec m0 n0 =
  iterop n0 muln m0 (S O)

(** val expn : nat -> nat -> nat **)

let expn =
  expn_rec

(** val nat_of_bool : bool -> nat **)

let nat_of_bool = function
| true -> S O
| false -> O

(** val odd : nat -> bool **)

let rec odd = function
| O -> false
| S n' -> negb (odd n')

(** val double_rec : nat -> nat **)

let rec double_rec = function
| O -> O
| S n' -> S (S (double_rec n'))

(** val double0 : nat -> nat **)

let double0 =
  double_rec

(** val size : 'a1 list -> nat **)

let rec size = function
| [] -> O
| _ :: s' -> S (size s')

(** val cat : 'a1 list -> 'a1 list -> 'a1 list **)

let rec cat s1 s2 =
  match s1 with
  | [] -> s2
  | x :: s1' -> x :: (cat s1' s2)

(** val nth : 'a1 -> 'a1 list -> nat -> 'a1 **)

let rec nth x0 s n0 =
  match s with
  | [] -> x0
  | x :: s' -> (match n0 with
                | O -> x
                | S n' -> nth x0 s' n')

(** val find : 'a1 pred0 -> 'a1 list -> nat **)

let rec find a = function
| [] -> O
| x :: s' -> if a x then O else S (find a s')

(** val filter : 'a1 pred0 -> 'a1 list -> 'a1 list **)

let rec filter a = function
| [] -> []
| x :: s' -> if a x then x :: (filter a s') else filter a s'

(** val eqseq :
    Equality.coq_type -> Equality.sort list -> Equality.sort list -> bool **)

let rec eqseq t1 s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _ :: _ -> false)
  | x1 :: s1' ->
    (match s2 with
     | [] -> false
     | x2 :: s2' -> (&&) (eq_op t1 x1 x2) (eqseq t1 s1' s2'))

(** val eqseqP : Equality.coq_type -> Equality.sort list Equality.axiom **)

let eqseqP t1 _top_assumption_ =
  let _evar_0_ = fun __top_assumption_ ->
    let _evar_0_ = ReflectT in
    let _evar_0_0 = fun _ _ -> ReflectF in
    (match __top_assumption_ with
     | [] -> _evar_0_
     | a :: l -> _evar_0_0 a l)
  in
  let _evar_0_0 = fun x1 s1 iHs __top_assumption_ ->
    let _evar_0_0 = ReflectF in
    let _evar_0_1 = fun x2 s2 ->
      ssr_have (eqP t1 x1 x2) (fun __top_assumption_0 ->
        let _evar_0_1 = fun _ -> iffP (eqseq t1 s1 s2) (iHs s2) in
        let _evar_0_2 = fun _ -> ReflectF in
        (match __top_assumption_0 with
         | ReflectT -> _evar_0_1 __
         | ReflectF -> _evar_0_2 __))
    in
    (match __top_assumption_ with
     | [] -> _evar_0_0
     | a :: l -> _evar_0_1 a l)
  in
  let rec f0 = function
  | [] -> _evar_0_
  | y :: l0 -> _evar_0_0 y l0 (f0 l0)
  in f0 _top_assumption_

(** val seq_eqMixin : Equality.coq_type -> Equality.sort list Equality.mixin_of **)

let seq_eqMixin t1 =
  { Equality.op = (eqseq t1); Equality.mixin_of__1 = (eqseqP t1) }

(** val seq_eqType : Equality.coq_type -> Equality.coq_type **)

let seq_eqType t1 =
  Obj.magic seq_eqMixin t1

(** val mem_seq :
    Equality.coq_type -> Equality.sort list -> Equality.sort -> bool **)

let rec mem_seq t1 = function
| [] -> (fun _ -> false)
| y :: s' -> let p0 = mem_seq t1 s' in (fun x -> (||) (eq_op t1 x y) (p0 x))

type seq_eqclass = Equality.sort list

(** val pred_of_seq : Equality.coq_type -> seq_eqclass -> Equality.sort pred_sort **)

let pred_of_seq t1 s =
  Obj.magic mem_seq t1 s

(** val seq_predType : Equality.coq_type -> Equality.sort predType **)

let seq_predType t1 =
  predType0 (Obj.magic pred_of_seq t1)

(** val uniq : Equality.coq_type -> Equality.sort list -> bool **)

let rec uniq t1 = function
| [] -> true
| x :: s' ->
  (&&) (negb (in_mem x (mem (seq_predType t1) (Obj.magic s')))) (uniq t1 s')

(** val undup : Equality.coq_type -> Equality.sort list -> Equality.sort list **)

let rec undup t1 = function
| [] -> []
| x :: s' ->
  if in_mem x (mem (seq_predType t1) (Obj.magic s'))
  then undup t1 s'
  else x :: (undup t1 s')

(** val index0 : Equality.coq_type -> Equality.sort -> Equality.sort list -> nat **)

let index0 t1 x =
  find (PredOfSimpl.coerce (pred1 t1 x))

(** val map0 : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map0 f0 = function
| [] -> []
| x :: s' -> (f0 x) :: (map0 f0 s')

(** val pmap : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list **)

let rec pmap f0 = function
| [] -> []
| x :: s' -> let r = pmap f0 s' in Option.apply (fun x0 -> x0 :: r) r (f0 x)

(** val iota : nat -> nat -> nat list **)

let rec iota m0 = function
| O -> []
| S n' -> m0 :: (iota (S m0) n')

(** val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldr f0 z0 = function
| [] -> z0
| x :: s' -> f0 x (foldr f0 z0 s')

(** val flatten : 'a1 list list -> 'a1 list **)

let flatten s =
  foldr cat [] s

module CodeSeq =
 struct
  (** val code : nat list -> nat **)

  let code =
    foldr (fun n0 m0 -> muln (expn (S (S O)) n0) (S (double0 m0))) O

  (** val decode_rec : nat -> nat -> nat -> nat list **)

  let rec decode_rec v q0 r =
    match q0 with
    | O -> v :: []
    | S q' ->
      (match r with
       | O -> v :: (decode_rec O q' q')
       | S n0 ->
         (match n0 with
          | O -> decode_rec (S v) q' q'
          | S r' -> decode_rec v q' r'))

  (** val decode : nat -> nat list **)

  let decode n0 = match n0 with
  | O -> []
  | S _ -> decode_rec O (pred n0) (pred n0)
 end

(** val tag_of_pair : ('a1 * 'a2) -> ('a1, 'a2) sigT **)

let tag_of_pair p0 =
  tagged0 (fst p0) (snd p0)

(** val pair_of_tag : ('a1, 'a2) sigT -> 'a1 * 'a2 **)

let pair_of_tag u =
  ((tag u), (tagged u))

module Choice =
 struct
  type 't mixin_of =
    't pred0 -> nat -> 't option
    (* singleton inductive, whose constructor was Mixin *)

  (** val find : 'a1 mixin_of -> 'a1 pred0 -> nat -> 'a1 option **)

  let find m0 =
    m0

  type 't class_of = { base : 't Equality.mixin_of; mixin : 't mixin_of }

  (** val base : 'a1 class_of -> 'a1 Equality.mixin_of **)

  let base c =
    c.base

  (** val mixin : 'a1 class_of -> 'a1 mixin_of **)

  let mixin c =
    c.mixin

  type coq_type = __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort class_of **)

  let coq_class cT =
    cT

  (** val pack :
      'a1 mixin_of -> 'a1 Equality.mixin_of -> Equality.coq_type -> coq_type **)

  let pack m0 b _ =
    { base = (Obj.magic b); mixin = (Obj.magic m0) }

  (** val eqType : coq_type -> Equality.coq_type **)

  let eqType cT =
    (coq_class cT).base

  module InternalTheory =
   struct
    (** val find : coq_type -> sort pred0 -> nat -> sort option **)

    let find t1 =
      find (coq_class t1).mixin
   end
 end

(** val pcanChoiceMixin :
    Choice.coq_type -> ('a1 -> Choice.sort) -> (Choice.sort -> 'a1 option) -> 'a1
    Choice.mixin_of **)

let pcanChoiceMixin t1 _ f' =
  let liftP = fun sP -> simplPred (fun x -> Option.apply sP false (f' x)) in
  let sf = fun sP n0 ->
    Option.bind f' (Choice.InternalTheory.find t1 (PredOfSimpl.coerce (liftP sP)) n0)
  in
  (fun sP -> fun_of_simpl (sf sP))

(** val canChoiceMixin :
    Choice.coq_type -> ('a1 -> Choice.sort) -> (Choice.sort -> 'a1) -> 'a1
    Choice.mixin_of **)

let canChoiceMixin t1 f0 f' =
  pcanChoiceMixin t1 f0 (fun y -> Some (f' y))

(** val sub_choiceMixin :
    Choice.coq_type -> Choice.sort pred0 -> Choice.sort subType -> Choice.sort
    sub_sort Choice.mixin_of **)

let sub_choiceMixin t1 p0 sT =
  pcanChoiceMixin t1 sT.val0 (insub p0 sT)

(** val sub_choiceClass :
    Choice.coq_type -> Choice.sort pred0 -> Choice.sort subType -> Choice.sort
    sub_sort Choice.class_of **)

let sub_choiceClass t1 p0 sT =
  { Choice.base = (sub_eqMixin (Choice.eqType t1) p0 sT); Choice.mixin =
    (sub_choiceMixin t1 p0 sT) }

(** val sub_choiceType :
    Choice.coq_type -> Choice.sort pred0 -> Choice.sort subType -> Choice.coq_type **)

let sub_choiceType =
  sub_choiceClass

(** val seq_choiceMixin : Choice.coq_type -> Choice.sort list Choice.mixin_of **)

let seq_choiceMixin t1 =
  let r = fun f0 xs x -> f0 (x :: xs) in
  let f0 =
    let rec f0 sP ns xs =
      match ns with
      | [] -> if sP xs then Some xs else None
      | n0 :: ns1 ->
        let fr = fun_of_simpl (r (f0 sP ns1)) xs in
        Option.bind fr (Choice.InternalTheory.find t1 (fun x -> isSome (fr x)) n0)
    in f0
  in
  (fun sP nn -> f0 sP (CodeSeq.decode nn) [])

(** val seq_choiceType : Choice.coq_type -> Choice.coq_type **)

let seq_choiceType t1 =
  { Choice.base = (Equality.coq_class (seq_eqType (Choice.eqType t1)));
    Choice.mixin = (Obj.magic seq_choiceMixin t1) }

(** val tagged_choiceMixin :
    Choice.coq_type -> (Choice.sort -> Choice.coq_type) -> (Choice.sort,
    Choice.sort) sigT Choice.mixin_of **)

let tagged_choiceMixin i t_ =
  let ft = fun tP n0 i0 ->
    Option.map (tagged0 i0)
      (Choice.InternalTheory.find (t_ i0) (comp tP (tagged0 i0)) n0)
  in
  let fi = fun tP ni nt ->
    Option.bind (ft tP nt)
      (Choice.InternalTheory.find i (fun i0 -> isSome (ft tP nt i0)) ni)
  in
  (fun tP n0 ->
  match CodeSeq.decode n0 with
  | [] -> None
  | ni :: l ->
    (match l with
     | [] -> None
     | nt :: l0 -> (match l0 with
                    | [] -> fi tP ni nt
                    | _ :: _ -> None)))

(** val tagged_choiceType :
    Choice.coq_type -> (Choice.sort -> Choice.coq_type) -> Choice.coq_type **)

let tagged_choiceType i t_ =
  { Choice.base =
    (Equality.coq_class
      (tag_eqType (Choice.eqType i) (fun i0 -> Choice.eqType (t_ i0))));
    Choice.mixin = (Obj.magic tagged_choiceMixin i t_) }

(** val nat_choiceMixin : nat Choice.mixin_of **)

let nat_choiceMixin =
  let f0 = fun p0 n0 -> if p0 n0 then Some n0 else None in
  (fun p0 -> fun_of_simpl (f0 p0))

(** val nat_choiceType : Choice.coq_type **)

let nat_choiceType =
  { Choice.base = (Equality.coq_class nat_eqType); Choice.mixin =
    (Obj.magic nat_choiceMixin) }

(** val bool_choiceMixin : bool Choice.mixin_of **)

let bool_choiceMixin =
  canChoiceMixin nat_choiceType (Obj.magic nat_of_bool) (Obj.magic odd)

(** val bool_choiceType : Choice.coq_type **)

let bool_choiceType =
  { Choice.base = (Equality.coq_class bool_eqType); Choice.mixin =
    (Obj.magic bool_choiceMixin) }

(** val prod_choiceMixin :
    Choice.coq_type -> Choice.coq_type -> (Choice.sort * Choice.sort) Choice.mixin_of **)

let prod_choiceMixin t1 t2 =
  canChoiceMixin (tagged_choiceType t1 (fun _ -> t2)) (Obj.magic tag_of_pair)
    (Obj.magic pair_of_tag)

(** val prod_choiceType : Choice.coq_type -> Choice.coq_type -> Choice.coq_type **)

let prod_choiceType t1 t2 =
  { Choice.base =
    (Equality.coq_class (prod_eqType (Choice.eqType t1) (Choice.eqType t2)));
    Choice.mixin = (Obj.magic prod_choiceMixin t1 t2) }

module Countable =
 struct
  type 't mixin_of = { pickle : ('t -> nat); unpickle : (nat -> 't option) }

  (** val pickle : 'a1 mixin_of -> 'a1 -> nat **)

  let pickle m0 =
    m0.pickle

  (** val unpickle : 'a1 mixin_of -> nat -> 'a1 option **)

  let unpickle m0 =
    m0.unpickle

  type 't class_of = { base : 't Choice.class_of; mixin : 't mixin_of }

  (** val base : 'a1 class_of -> 'a1 Choice.class_of **)

  let base c =
    c.base

  (** val mixin : 'a1 class_of -> 'a1 mixin_of **)

  let mixin c =
    c.mixin

  type coq_type = __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort class_of **)

  let coq_class cT =
    cT

  (** val pack :
      'a1 mixin_of -> Choice.coq_type -> 'a1 Choice.class_of -> coq_type **)

  let pack m0 _ b =
    { base = (Obj.magic b); mixin = (Obj.magic m0) }

  (** val eqType : coq_type -> Equality.coq_type **)

  let eqType cT =
    (coq_class cT).base.Choice.base

  (** val choiceType : coq_type -> Choice.coq_type **)

  let choiceType cT =
    (coq_class cT).base
 end

(** val unpickle0 : Countable.coq_type -> nat -> Countable.sort option **)

let unpickle0 t1 =
  (Countable.coq_class t1).Countable.mixin.Countable.unpickle

(** val pickle0 : Countable.coq_type -> Countable.sort -> nat **)

let pickle0 t1 =
  (Countable.coq_class t1).Countable.mixin.Countable.pickle

(** val pcanCountMixin :
    Countable.coq_type -> ('a1 -> Countable.sort) -> (Countable.sort -> 'a1 option)
    -> 'a1 Countable.mixin_of **)

let pcanCountMixin t1 f0 f' =
  { Countable.pickle = (comp (pickle0 t1) f0); Countable.unpickle =
    (pcomp f' (unpickle0 t1)) }

(** val canCountMixin :
    Countable.coq_type -> ('a1 -> Countable.sort) -> (Countable.sort -> 'a1) -> 'a1
    Countable.mixin_of **)

let canCountMixin t1 f0 f' =
  pcanCountMixin t1 f0 (fun y -> Some (f' y))

(** val sub_countMixin :
    Countable.coq_type -> Countable.sort pred0 -> Countable.sort subType ->
    Countable.sort sub_sort Countable.mixin_of **)

let sub_countMixin t1 p0 sT =
  pcanCountMixin t1 sT.val0 (insub p0 sT)

(** val pickle_seq : Countable.coq_type -> Countable.sort list -> nat **)

let pickle_seq t1 s =
  CodeSeq.code (map0 (pickle0 t1) s)

(** val unpickle_seq : Countable.coq_type -> nat -> Countable.sort list option **)

let unpickle_seq t1 n0 =
  Some (pmap (unpickle0 t1) (CodeSeq.decode n0))

(** val seq_countMixin :
    Countable.coq_type -> Countable.sort list Countable.mixin_of **)

let seq_countMixin t1 =
  { Countable.pickle = (pickle_seq t1); Countable.unpickle = (unpickle_seq t1) }

(** val seq_countType : Countable.coq_type -> Countable.coq_type **)

let seq_countType t1 =
  { Countable.base = (Choice.coq_class (seq_choiceType (Countable.choiceType t1)));
    Countable.mixin = (Obj.magic seq_countMixin t1) }

type subCountType = { subCount_sort : Choice.sort subType;
                      subCountType__1 : Choice.sort sub_sort Countable.mixin_of }

(** val sub_countType :
    Choice.coq_type -> Choice.sort pred0 -> subCountType -> Countable.coq_type **)

let sub_countType t1 p0 sT =
  { Countable.base = (Choice.coq_class (sub_choiceType t1 p0 sT.subCount_sort));
    Countable.mixin = sT.subCountType__1 }

(** val pickle_tagged :
    Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> (Countable.sort,
    Countable.sort) sigT -> nat **)

let pickle_tagged i t_ u =
  CodeSeq.code ((pickle0 i (tag u)) :: ((pickle0 (t_ (tag u)) (tagged u)) :: []))

(** val unpickle_tagged :
    Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> nat ->
    (Countable.sort, Countable.sort) sigT option **)

let unpickle_tagged i t_ s =
  match CodeSeq.decode s with
  | [] -> None
  | ni :: l ->
    (match l with
     | [] -> None
     | nx :: l0 ->
       (match l0 with
        | [] ->
          Option.bind (fun i0 -> Option.map (tagged0 i0) (unpickle0 (t_ i0) nx))
            (unpickle0 i ni)
        | _ :: _ -> None))

(** val tag_countMixin :
    Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> (Countable.sort,
    Countable.sort) sigT Countable.mixin_of **)

let tag_countMixin i t_ =
  { Countable.pickle = (pickle_tagged i t_); Countable.unpickle =
    (unpickle_tagged i t_) }

(** val tag_countType :
    Countable.coq_type -> (Countable.sort -> Countable.coq_type) ->
    Countable.coq_type **)

let tag_countType i t_ =
  { Countable.base =
    (Choice.coq_class
      (tagged_choiceType (Countable.choiceType i) (fun i0 ->
        Countable.choiceType (t_ i0)))); Countable.mixin =
    (Obj.magic tag_countMixin i t_) }

(** val nat_countMixin : nat Countable.mixin_of **)

let nat_countMixin =
  { Countable.pickle = (fun x -> x); Countable.unpickle = (fun x -> Some x) }

(** val nat_countType : Countable.coq_type **)

let nat_countType =
  { Countable.base = (Choice.coq_class nat_choiceType); Countable.mixin =
    (Obj.magic nat_countMixin) }

(** val bool_countMixin : bool Countable.mixin_of **)

let bool_countMixin =
  canCountMixin nat_countType (Obj.magic nat_of_bool) (Obj.magic odd)

(** val bool_countType : Countable.coq_type **)

let bool_countType =
  { Countable.base = (Choice.coq_class bool_choiceType); Countable.mixin =
    (Obj.magic bool_countMixin) }

(** val prod_countMixin :
    Countable.coq_type -> Countable.coq_type -> (Countable.sort * Countable.sort)
    Countable.mixin_of **)

let prod_countMixin t1 t2 =
  canCountMixin (tag_countType t1 (fun _ -> t2)) (Obj.magic tag_of_pair)
    (Obj.magic pair_of_tag)

module Finite =
 struct
  type mixin_of = { mixin_base : Equality.sort Countable.mixin_of;
                    mixin_enum : Equality.sort list }

  (** val mixin_base :
      Equality.coq_type -> mixin_of -> Equality.sort Countable.mixin_of **)

  let mixin_base _ m0 =
    m0.mixin_base

  (** val mixin_enum : Equality.coq_type -> mixin_of -> Equality.sort list **)

  let mixin_enum _ m0 =
    m0.mixin_enum

  (** val coq_EnumMixin : Countable.coq_type -> Countable.sort list -> mixin_of **)

  let coq_EnumMixin t1 e =
    let m0 = t1.Countable.mixin in { mixin_base = m0; mixin_enum = e }

  (** val coq_UniqMixin : Countable.coq_type -> Countable.sort list -> mixin_of **)

  let coq_UniqMixin =
    coq_EnumMixin

  type 't class_of = { base : 't Choice.class_of; mixin : mixin_of }

  (** val base : 'a1 class_of -> 'a1 Choice.class_of **)

  let base c =
    c.base

  (** val mixin : 'a1 class_of -> mixin_of **)

  let mixin c =
    c.mixin

  (** val base2 : 'a1 class_of -> 'a1 Countable.class_of **)

  let base2 c =
    { Countable.base = c.base; Countable.mixin = (Obj.magic c.mixin.mixin_base) }

  type coq_type = __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort class_of **)

  let coq_class cT =
    cT

  (** val pack :
      'a1 Equality.mixin_of -> mixin_of -> Choice.coq_type -> 'a1 Choice.class_of ->
      mixin_of -> coq_type **)

  let pack _ _ _ b m0 =
    { base = (Obj.magic b); mixin = m0 }

  (** val eqType : coq_type -> Equality.coq_type **)

  let eqType cT =
    (coq_class cT).base.Choice.base

  (** val choiceType : coq_type -> Choice.coq_type **)

  let choiceType cT =
    (coq_class cT).base

  (** val countType : coq_type -> Countable.coq_type **)

  let countType cT =
    base2 (coq_class cT)

  module type EnumSig =
   sig
    val enum : coq_type -> sort list
   end

  module EnumDef =
   struct
    (** val enum : coq_type -> Equality.sort list **)

    let enum cT =
      (coq_class cT).mixin.mixin_enum

    (** val enumDef : __ **)

    let enumDef =
      __
   end
 end

type fin_pred_sort = Finite.sort pred_sort

(** val enum_mem : Finite.coq_type -> Finite.sort mem_pred -> Finite.sort list **)

let enum_mem t1 mA =
  filter (PredOfSimpl.coerce (simpl_of_mem mA)) (Finite.EnumDef.enum t1)

module type CardDefSig =
 sig
  val card : Finite.coq_type -> Finite.sort mem_pred -> nat
 end

module CardDef =
 struct
  (** val card : Finite.coq_type -> Finite.sort mem_pred -> nat **)

  let card t1 mA =
    size (enum_mem t1 mA)

  (** val cardEdef : __ **)

  let cardEdef =
    __
 end

(** val pred0b : Finite.coq_type -> Finite.sort pred0 -> bool **)

let pred0b t1 p0 =
  eq_op nat_eqType (Obj.magic CardDef.card t1 (mem predPredType (Obj.magic p0)))
    (Obj.magic O)

module FiniteQuant =
 struct
  type quantified = bool
    (* singleton inductive, whose constructor was Quantified *)

  (** val all :
      Finite.coq_type -> quantified -> Finite.sort -> Finite.sort -> quantified **)

  let all _ b _ _ =
    negb b
 end

module type SubsetDefSig =
 sig
  val subset :
    Finite.coq_type -> Finite.sort mem_pred -> Finite.sort mem_pred -> bool
 end

module SubsetDef =
 struct
  (** val subset :
      Finite.coq_type -> Finite.sort mem_pred -> Finite.sort mem_pred -> bool **)

  let subset t1 a b =
    pred0b t1
      (PredOfSimpl.coerce
        (predD (PredOfSimpl.coerce (simpl_of_mem a))
          (PredOfSimpl.coerce (simpl_of_mem b))))

  (** val subsetEdef : __ **)

  let subsetEdef =
    __
 end

type pick_spec =
| Pick of Finite.sort
| Nopick

(** val pickP : Finite.coq_type -> Finite.sort pred0 -> pick_spec **)

let pickP t1 p0 =
  let _evar_0_ = fun _ -> Nopick in
  let _evar_0_0 = fun x _ -> Pick x in
  (match enum_mem t1 (mem predPredType (Obj.magic p0)) with
   | [] -> _evar_0_ __
   | a :: l -> _evar_0_0 a l)

(** val pred0P : Finite.coq_type -> Finite.sort pred0 -> reflect **)

let pred0P t1 p0 =
  iffP
    (eq_op nat_eqType (Obj.magic CardDef.card t1 (mem predPredType (Obj.magic p0)))
      (Obj.magic O))
    (eqP nat_eqType (Obj.magic CardDef.card t1 (mem predPredType (Obj.magic p0)))
      (Obj.magic O))

(** val forallPP :
    Finite.coq_type -> Finite.sort pred0 -> (Finite.sort -> reflect) -> reflect **)

let forallPP t1 p0 _ =
  iffP
    (pred0b t1
      (PredOfSimpl.coerce (simplPred (fun x -> FiniteQuant.all t1 (p0 x) x x))))
    (pred0P t1
      (PredOfSimpl.coerce (simplPred (fun x -> FiniteQuant.all t1 (p0 x) x x))))

(** val eqfunP :
    Finite.coq_type -> (Finite.sort -> Equality.coq_type) -> (Finite.sort ->
    Equality.sort) -> (Finite.sort -> Equality.sort) -> reflect **)

let eqfunP t1 rT f1 f2 =
  forallPP t1 (fun x -> eq_op (rT x) (f1 x) (f2 x)) (fun x ->
    eqP (rT x) (f1 x) (f2 x))

(** val dinjectiveb :
    Finite.coq_type -> Equality.coq_type -> (Finite.sort -> Equality.sort) ->
    Finite.sort pred_sort -> bool **)

let dinjectiveb aT rT f0 d =
  uniq rT (map0 f0 (enum_mem aT (mem predPredType d)))

(** val injectiveb :
    Finite.coq_type -> Equality.coq_type -> (Finite.sort -> Equality.sort) -> bool **)

let injectiveb aT rT f0 =
  dinjectiveb aT rT f0 (Obj.magic PredOfSimpl.coerce pred_of_argType)

(** val image_mem :
    Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort mem_pred -> 'a1 list **)

let image_mem t1 f0 mA =
  map0 f0 (enum_mem t1 mA)

(** val codom : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 list **)

let codom t1 f0 =
  image_mem t1 f0 (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType))

(** val iinv_proof :
    Finite.coq_type -> Equality.coq_type -> (Finite.sort -> Equality.sort) ->
    Finite.sort pred_sort -> Equality.sort -> Finite.sort sig2 **)

let iinv_proof t1 t' f0 a y =
  let b = fun x -> (&&) (Obj.magic a x) (eq_op t' (f0 x) y) in
  let _evar_0_ = fun x -> x in
  let _evar_0_0 = fun _ -> assert false (* absurd case *) in
  (match pickP t1 b with
   | Pick x -> _evar_0_ x
   | Nopick -> _evar_0_0 __)

(** val iinv :
    Finite.coq_type -> Equality.coq_type -> (Finite.sort -> Equality.sort) ->
    Finite.sort pred_sort -> Equality.sort -> Finite.sort **)

let iinv t1 t' f0 a y =
  s2val (iinv_proof t1 t' f0 a y)

(** val bool_finMixin : Finite.mixin_of **)

let bool_finMixin =
  { Finite.mixin_base = (Obj.magic bool_countMixin); Finite.mixin_enum =
    ((Obj.magic true) :: ((Obj.magic false) :: [])) }

(** val bool_finType : Finite.coq_type **)

let bool_finType =
  { Finite.base = (Choice.coq_class bool_choiceType); Finite.mixin = bool_finMixin }

(** val pcanFinMixin :
    Countable.coq_type -> Finite.coq_type -> (Countable.sort -> Finite.sort) ->
    (Finite.sort -> Countable.sort option) -> Finite.mixin_of **)

let pcanFinMixin eT fT _ g0 =
  Finite.coq_EnumMixin eT
    (undup (Countable.eqType eT) (pmap g0 (Finite.EnumDef.enum fT)))

(** val sub_enum :
    Finite.coq_type -> Finite.sort pred0 -> subCountType -> Choice.sort sub_sort list **)

let sub_enum t1 p0 sT =
  pmap (insub p0 sT.subCount_sort) (Finite.EnumDef.enum t1)

(** val subFinMixin :
    Finite.coq_type -> Finite.sort pred0 -> subCountType -> Finite.mixin_of **)

let subFinMixin t1 p0 sT =
  Finite.coq_UniqMixin (sub_countType (Finite.choiceType t1) p0 sT)
    (sub_enum t1 p0 sT)

(** val subFinMixin_for :
    Finite.coq_type -> Finite.sort pred0 -> subCountType -> Equality.coq_type ->
    Finite.mixin_of **)

let subFinMixin_for t1 p0 sT _ =
  subFinMixin t1 p0 sT

type ordinal = nat
  (* singleton inductive, whose constructor was Ordinal *)

(** val nat_of_ord : nat -> ordinal -> nat **)

let nat_of_ord _ i =
  i

(** val ordinal_subType : nat -> nat subType **)

let ordinal_subType n0 =
  { val0 = (Obj.magic nat_of_ord n0); sub0 = (Obj.magic (fun x _ -> x));
    subType__2 = (fun _ k_S u -> k_S (Obj.magic u) __) }

(** val ordinal_eqMixin : nat -> ordinal Equality.mixin_of **)

let ordinal_eqMixin n0 =
  { Equality.op = (fun x y ->
    eq_op nat_eqType (Obj.magic nat_of_ord n0 x) (Obj.magic nat_of_ord n0 y));
    Equality.mixin_of__1 =
    (Obj.magic val_eqP nat_eqType (fun x -> leq (S (Obj.magic x)) n0)
      (ordinal_subType n0)) }

(** val ordinal_eqType : nat -> Equality.coq_type **)

let ordinal_eqType n0 =
  Obj.magic ordinal_eqMixin n0

(** val ordinal_choiceMixin : nat -> ordinal Choice.mixin_of **)

let ordinal_choiceMixin n0 =
  Obj.magic sub_choiceMixin nat_choiceType (fun x -> leq (S (Obj.magic x)) n0)
    (ordinal_subType n0)

(** val ordinal_choiceType : nat -> Choice.coq_type **)

let ordinal_choiceType n0 =
  { Choice.base = (Equality.coq_class (ordinal_eqType n0)); Choice.mixin =
    (Obj.magic ordinal_choiceMixin n0) }

(** val ordinal_countMixin : nat -> ordinal Countable.mixin_of **)

let ordinal_countMixin n0 =
  Obj.magic sub_countMixin nat_countType (fun x -> leq (S (Obj.magic x)) n0)
    (ordinal_subType n0)

(** val ord_enum : nat -> ordinal list **)

let ord_enum n0 =
  pmap (Obj.magic insub (fun x -> leq (S x) n0) (ordinal_subType n0)) (iota O n0)

(** val ordinal_finMixin : nat -> Finite.mixin_of **)

let ordinal_finMixin n0 =
  { Finite.mixin_base = (Obj.magic ordinal_countMixin n0); Finite.mixin_enum =
    (Obj.magic ord_enum n0) }

(** val ordinal_finType : nat -> Finite.coq_type **)

let ordinal_finType n0 =
  { Finite.base = (Choice.coq_class (ordinal_choiceType n0)); Finite.mixin =
    (ordinal_finMixin n0) }

(** val enum_rank_in :
    Finite.coq_type -> Finite.sort -> Finite.sort pred_sort -> Equality.sort -> nat
    sub_sort **)

let enum_rank_in t1 _ a x =
  insubd (fun x0 ->
    leq (S x0)
      (CardDef.card t1 (mem predPredType (Obj.magic (fun x1 -> Obj.magic a x1)))))
    (ordinal_subType
      (CardDef.card t1 (mem predPredType (Obj.magic (fun x0 -> Obj.magic a x0)))))
    (Obj.magic O) (index0 (Finite.eqType t1) x (enum_mem t1 (mem predPredType a)))

(** val enum_rank : Finite.coq_type -> Finite.sort -> nat sub_sort **)

let enum_rank t1 x =
  enum_rank_in t1 x (Obj.magic PredOfSimpl.coerce pred_of_argType) x

(** val bump : nat -> nat -> nat **)

let bump h i =
  addn (nat_of_bool (leq h i)) i

(** val lift : nat -> ordinal -> ordinal -> ordinal **)

let lift n0 h i =
  bump (nat_of_ord n0 h) (nat_of_ord (pred n0) i)

(** val prod_enum :
    Finite.coq_type -> Finite.coq_type -> (Finite.sort * Finite.sort) list **)

let prod_enum t1 t2 =
  flatten
    (map0 (fun x1 ->
      map0 (fun x2 -> (x1, x2))
        (enum_mem t2
          (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType))))
      (enum_mem t1 (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType))))

(** val prod_finMixin : Finite.coq_type -> Finite.coq_type -> Finite.mixin_of **)

let prod_finMixin t1 t2 =
  { Finite.mixin_base =
    (Obj.magic prod_countMixin (Finite.countType t1) (Finite.countType t2));
    Finite.mixin_enum = (Obj.magic prod_enum t1 t2) }

(** val prod_finType : Finite.coq_type -> Finite.coq_type -> Finite.coq_type **)

let prod_finType t1 t2 =
  { Finite.base =
    (Choice.coq_class
      (prod_choiceType (Finite.choiceType t1) (Finite.choiceType t2)));
    Finite.mixin = (prod_finMixin t1 t2) }

(** val tag_enum :
    Finite.coq_type -> (Finite.sort -> Finite.coq_type) -> (Finite.sort,
    Finite.sort) sigT list **)

let tag_enum i t_ =
  flatten
    (map0 (fun i0 -> map0 (fun x -> tagged0 i0 x) (Finite.EnumDef.enum (t_ i0)))
      (Finite.EnumDef.enum i))

(** val tag_finMixin :
    Finite.coq_type -> (Finite.sort -> Finite.coq_type) -> Finite.mixin_of **)

let tag_finMixin i t_ =
  { Finite.mixin_base =
    (Obj.magic tag_countMixin (Finite.countType i) (fun i0 ->
      Finite.countType (t_ i0))); Finite.mixin_enum = (Obj.magic tag_enum i t_) }

(** val tag_finType :
    Finite.coq_type -> (Finite.sort -> Finite.coq_type) -> Finite.coq_type **)

let tag_finType i t_ =
  { Finite.base =
    (Choice.coq_class
      (tagged_choiceType (Finite.choiceType i) (fun i0 -> Finite.choiceType (t_ i0))));
    Finite.mixin = (tag_finMixin i t_) }

type 't tuple_of = 't list
  (* singleton inductive, whose constructor was Tuple *)

(** val tval : nat -> 'a1 tuple_of -> 'a1 list **)

let tval _ t1 =
  t1

(** val tuple_subType : nat -> 'a1 list subType **)

let tuple_subType n0 =
  { val0 = (Obj.magic tval n0); sub0 = (Obj.magic (fun x _ -> x)); subType__2 =
    (fun _ k_S u -> k_S (Obj.magic u) __) }

(** val tnth_default : nat -> 'a1 tuple_of -> ordinal -> 'a1 **)

let tnth_default n0 t1 =
  let _evar_0_ = fun _ -> assert false (* absurd case *) in
  let _evar_0_0 = fun a _ _ -> a in
  (match tval n0 t1 with
   | [] -> _evar_0_
   | a :: l -> _evar_0_0 a l)

(** val tnth : nat -> 'a1 tuple_of -> ordinal -> 'a1 **)

let tnth n0 t1 i =
  nth (tnth_default n0 t1 i) (tval n0 t1) (nat_of_ord n0 i)

(** val tuple : nat -> 'a1 tuple_of -> (__ -> 'a1 tuple_of) -> 'a1 tuple_of **)

let tuple _ _ mkT =
  mkT __

(** val map_tuple : nat -> ('a1 -> 'a2) -> 'a1 tuple_of -> 'a2 tuple_of **)

let map_tuple n0 f0 t1 =
  map0 f0 (tval n0 t1)

(** val tuple_eqMixin :
    nat -> Equality.coq_type -> Equality.sort tuple_of Equality.mixin_of **)

let tuple_eqMixin n0 t1 =
  { Equality.op = (fun x y ->
    eq_op (seq_eqType t1) (Obj.magic tval n0 x) (Obj.magic tval n0 y));
    Equality.mixin_of__1 =
    (Obj.magic val_eqP (seq_eqType t1) (fun x ->
      eq_op nat_eqType (Obj.magic size x) (Obj.magic n0)) (tuple_subType n0)) }

(** val tuple_eqType : nat -> Equality.coq_type -> Equality.coq_type **)

let tuple_eqType n0 t1 =
  Obj.magic tuple_eqMixin n0 t1

(** val tuple_choiceMixin :
    nat -> Choice.coq_type -> Choice.sort tuple_of Choice.mixin_of **)

let tuple_choiceMixin n0 t1 =
  Obj.magic sub_choiceMixin (seq_choiceType t1) (fun x ->
    eq_op nat_eqType (Obj.magic size x) (Obj.magic n0)) (tuple_subType n0)

(** val tuple_choiceType : nat -> Choice.coq_type -> Choice.coq_type **)

let tuple_choiceType n0 t1 =
  { Choice.base = (Equality.coq_class (tuple_eqType n0 (Choice.eqType t1)));
    Choice.mixin = (Obj.magic tuple_choiceMixin n0 t1) }

(** val tuple_countMixin :
    nat -> Countable.coq_type -> Countable.sort tuple_of Countable.mixin_of **)

let tuple_countMixin n0 t1 =
  Obj.magic sub_countMixin (seq_countType t1) (fun x ->
    eq_op nat_eqType (Obj.magic size x) (Obj.magic n0)) (tuple_subType n0)

(** val tuple_countType : nat -> Countable.coq_type -> Countable.coq_type **)

let tuple_countType n0 t1 =
  { Countable.base =
    (Choice.coq_class (tuple_choiceType n0 (Countable.choiceType t1)));
    Countable.mixin = (Obj.magic tuple_countMixin n0 t1) }

module type FinTupleSig =
 sig
  val enum : nat -> Finite.coq_type -> Finite.sort tuple_of list
 end

module FinTuple =
 struct
  (** val enum : nat -> Finite.coq_type -> Finite.sort tuple_of list **)

  let enum n0 t1 =
    let extend = fun e -> flatten (codom t1 (fun x -> map0 (fun x0 -> x :: x0) e)) in
    pmap
      (Obj.magic insub (fun x -> eq_op nat_eqType (Obj.magic size x) (Obj.magic n0))
        (tuple_subType n0)) (iter n0 extend ([] :: []))

  (** val enumP : __ **)

  let enumP =
    __

  (** val size_enum : __ **)

  let size_enum =
    __
 end

(** val tuple_finMixin : nat -> Finite.coq_type -> Finite.mixin_of **)

let tuple_finMixin n0 t1 =
  { Finite.mixin_base = (Obj.magic tuple_countMixin n0 (Finite.countType t1));
    Finite.mixin_enum = (Obj.magic FinTuple.enum n0 t1) }

(** val tuple_finType : nat -> Finite.coq_type -> Finite.coq_type **)

let tuple_finType n0 t1 =
  { Finite.base = (Choice.coq_class (tuple_choiceType n0 (Finite.choiceType t1)));
    Finite.mixin = (tuple_finMixin n0 t1) }

(** val enum_tuple :
    Finite.coq_type -> Finite.sort pred_sort -> Finite.sort tuple_of **)

let enum_tuple t1 a =
  enum_mem t1 (mem predPredType a)

(** val codom_tuple : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 tuple_of **)

let codom_tuple t1 f0 =
  tuple
    (CardDef.card t1
      (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType)))
    (map_tuple
      (CardDef.card t1
        (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType))) f0
      (enum_tuple t1 (Obj.magic PredOfSimpl.coerce pred_of_argType))) (fun _ ->
    codom t1 f0)

type 'rT finfun_on =
| Finfun_nil
| Finfun_cons of Finite.sort * Finite.sort list * 'rT * 'rT finfun_on

(** val finfun_rec :
    Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort list -> 'a1 finfun_on **)

let rec finfun_rec aT g0 = function
| [] -> Finfun_nil
| x1 :: s1 -> Finfun_cons (x1, s1, (g0 x1), (finfun_rec aT g0 s1))

(** val fun_of_fin_rec :
    Finite.coq_type -> Equality.sort -> Finite.sort list -> 'a1 finfun_on -> 'a1 **)

let fun_of_fin_rec aT x s f_s =
  let rec fun_of_fin_rec0 x0 _ = function
  | Finfun_nil -> (fun _ -> assert false (* absurd case *))
  | Finfun_cons (x1, s1, y1, f_s1) ->
    (match eqP (Finite.eqType aT) x0 x1 with
     | ReflectT -> (fun _ -> y1)
     | ReflectF -> fun_of_fin_rec0 x0 s1 f_s1)
  in fun_of_fin_rec0 x s f_s __

type 'rT finfun_of =
  'rT finfun_on
  (* singleton inductive, whose constructor was FinfunOf *)

type 'rT dfinfun_of = 'rT finfun_of

(** val fun_of_fin : Finite.coq_type -> 'a1 finfun_of -> Equality.sort -> 'a1 **)

let fun_of_fin aT f0 x =
  fun_of_fin_rec aT x
    (enum_mem aT (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType)))
    f0

module type FinfunDefSig =
 sig
  val finfun : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 finfun_of
 end

module FinfunDef =
 struct
  (** val finfun : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 finfun_of **)

  let finfun aT g0 =
    finfun_rec aT g0
      (enum_mem aT (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType)))

  (** val finfunE : __ **)

  let finfunE =
    __
 end

(** val total_fun :
    Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort -> (Finite.sort, 'a1) sigT **)

let total_fun _ g0 x =
  tagged0 x (g0 x)

(** val tfgraph :
    Finite.coq_type -> 'a1 finfun_of -> (Finite.sort, 'a1) sigT tuple_of **)

let tfgraph aT f0 =
  codom_tuple aT (total_fun aT (fun_of_fin aT f0))

(** val tfgraph_inv :
    Finite.coq_type -> (Finite.sort, 'a1) sigT tuple_of -> 'a1 finfun_of option **)

let tfgraph_inv aT g0 =
  match eqfunP aT (fun _ -> Finite.eqType aT) (fun x ->
          tag
            (tnth
              (CardDef.card aT
                (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType)))
              g0 (Obj.magic enum_rank aT x))) (fun x -> x) with
  | ReflectT ->
    Some
      (FinfunDef.finfun aT (fun x ->
        tagged
          (tnth
            (CardDef.card aT
              (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType))) g0
            (Obj.magic enum_rank aT x))))
  | ReflectF -> None

(** val eqMixin :
    Finite.coq_type -> (Finite.sort -> Equality.coq_type) -> Equality.sort
    dfinfun_of Equality.mixin_of **)

let eqMixin aT rT =
  pcanEqMixin
    (tuple_eqType
      (CardDef.card aT
        (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType)))
      (tag_eqType (Finite.eqType aT) rT)) (Obj.magic tfgraph aT)
    (Obj.magic tfgraph_inv aT)

(** val finfun_eqType : Finite.coq_type -> Equality.coq_type -> Equality.coq_type **)

let finfun_eqType aT rT =
  Obj.magic eqMixin aT (fun _ -> rT)

(** val dfinfun_eqType :
    Finite.coq_type -> (Finite.sort -> Equality.coq_type) -> Equality.coq_type **)

let dfinfun_eqType aT rT =
  Obj.magic eqMixin aT rT

(** val choiceMixin :
    Finite.coq_type -> (Finite.sort -> Choice.coq_type) -> Choice.sort dfinfun_of
    Choice.mixin_of **)

let choiceMixin aT rT =
  pcanChoiceMixin
    (tuple_choiceType
      (CardDef.card aT
        (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType)))
      (tagged_choiceType (Finite.choiceType aT) rT)) (Obj.magic tfgraph aT)
    (Obj.magic tfgraph_inv aT)

(** val finfun_choiceType : Finite.coq_type -> Choice.coq_type -> Choice.coq_type **)

let finfun_choiceType aT rT =
  Choice.pack (Obj.magic choiceMixin aT (fun _ -> rT))
    (Equality.coq_class (finfun_eqType aT (Choice.eqType rT)))
    (finfun_eqType aT (Choice.eqType rT))

(** val dfinfun_choiceType :
    Finite.coq_type -> (Finite.sort -> Choice.coq_type) -> Choice.coq_type **)

let dfinfun_choiceType aT rT =
  Choice.pack (Obj.magic choiceMixin aT rT)
    (Equality.coq_class (dfinfun_eqType aT (fun x -> Choice.eqType (rT x))))
    (dfinfun_eqType aT (fun x -> Choice.eqType (rT x)))

(** val countMixin :
    Finite.coq_type -> (Finite.sort -> Countable.coq_type) -> Countable.sort
    dfinfun_of Countable.mixin_of **)

let countMixin aT rT =
  pcanCountMixin
    (tuple_countType
      (CardDef.card aT
        (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType)))
      (tag_countType (Finite.countType aT) rT)) (Obj.magic tfgraph aT)
    (Obj.magic tfgraph_inv aT)

(** val finfun_countType :
    Finite.coq_type -> Countable.coq_type -> Countable.coq_type **)

let finfun_countType aT rT =
  Countable.pack (Obj.magic countMixin aT (fun _ -> rT))
    (finfun_choiceType aT (Countable.choiceType rT))
    (Choice.coq_class (finfun_choiceType aT (Countable.choiceType rT)))

(** val dfinfun_countType :
    Finite.coq_type -> (Finite.sort -> Countable.coq_type) -> Countable.coq_type **)

let dfinfun_countType aT rT =
  Countable.pack (Obj.magic countMixin aT rT)
    (dfinfun_choiceType aT (fun x -> Countable.choiceType (rT x)))
    (Choice.coq_class (dfinfun_choiceType aT (fun x -> Countable.choiceType (rT x))))

(** val finMixin :
    Finite.coq_type -> (Finite.sort -> Finite.coq_type) -> Finite.mixin_of **)

let finMixin aT rT =
  pcanFinMixin (dfinfun_countType aT (fun x -> Finite.countType (rT x)))
    (tuple_finType
      (CardDef.card aT
        (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType)))
      (tag_finType aT rT)) (Obj.magic tfgraph aT) (Obj.magic tfgraph_inv aT)

(** val finfun_finType : Finite.coq_type -> Finite.coq_type -> Finite.coq_type **)

let finfun_finType aT rT =
  Finite.pack
    (Countable.coq_class (dfinfun_countType aT (fun _ -> Finite.countType rT))).Countable.base.Choice.base
    (finMixin aT (fun _ -> rT)) (finfun_choiceType aT (Finite.choiceType rT))
    (Choice.coq_class (finfun_choiceType aT (Finite.choiceType rT)))
    (finMixin aT (fun _ -> rT))

module Monoid =
 struct
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

(** val applybig : ('a1, 'a2) bigbody -> 'a1 -> 'a1 **)

let applybig body x =
  let BigBody (_, op1, b, v) = body in if b then op1 v x else x

(** val reducebig : 'a1 -> 'a2 list -> ('a2 -> ('a1, 'a2) bigbody) -> 'a1 **)

let reducebig idx r body =
  foldr (comp applybig body) idx r

module type BigOpSig =
 sig
  val bigop : 'a1 -> 'a2 list -> ('a2 -> ('a1, 'a2) bigbody) -> 'a1
 end

module BigOp =
 struct
  (** val bigop : 'a1 -> 'a2 list -> ('a2 -> ('a1, 'a2) bigbody) -> 'a1 **)

  let bigop =
    reducebig

  (** val bigopE : __ **)

  let bigopE =
    __
 end

(** val index_enum_key : unit **)

let index_enum_key =
  ()

(** val index_enum : Finite.coq_type -> Finite.sort list **)

let index_enum t1 =
  locked_with index_enum_key (Finite.EnumDef.enum t1)

type set_type = bool finfun_of
  (* singleton inductive, whose constructor was FinSet *)

(** val finfun_of_set : Finite.coq_type -> set_type -> bool finfun_of **)

let finfun_of_set _ a =
  a

type set_of = set_type

(** val set_subType : Finite.coq_type -> bool finfun_of subType **)

let set_subType t1 =
  { val0 = (Obj.magic finfun_of_set t1); sub0 = (fun x _ -> Obj.magic x);
    subType__2 = (fun _ iH u -> iH (Obj.magic u) __) }

(** val set_eqMixin : Finite.coq_type -> set_type Equality.mixin_of **)

let set_eqMixin t1 =
  { Equality.op = (fun x y ->
    eq_op (finfun_eqType t1 bool_eqType) (Obj.magic finfun_of_set t1 x)
      (Obj.magic finfun_of_set t1 y)); Equality.mixin_of__1 =
    (Obj.magic val_eqP (finfun_eqType t1 bool_eqType) (fun _ -> true)
      (set_subType t1)) }

(** val set_eqType : Finite.coq_type -> Equality.coq_type **)

let set_eqType t1 =
  Obj.magic set_eqMixin t1

(** val set_choiceMixin : Finite.coq_type -> set_type Choice.mixin_of **)

let set_choiceMixin t1 =
  Obj.magic sub_choiceMixin (finfun_choiceType t1 bool_choiceType) (fun _ -> true)
    (set_subType t1)

(** val set_choiceType : Finite.coq_type -> Choice.coq_type **)

let set_choiceType t1 =
  { Choice.base = (Equality.coq_class (set_eqType t1)); Choice.mixin =
    (Obj.magic set_choiceMixin t1) }

(** val set_countMixin : Finite.coq_type -> set_type Countable.mixin_of **)

let set_countMixin t1 =
  Obj.magic sub_countMixin (finfun_countType t1 bool_countType) (fun _ -> true)
    (set_subType t1)

(** val set_countType : Finite.coq_type -> Countable.coq_type **)

let set_countType t1 =
  { Countable.base = (Choice.coq_class (set_choiceType t1)); Countable.mixin =
    (Obj.magic set_countMixin t1) }

(** val set_subCountType : Finite.coq_type -> subCountType **)

let set_subCountType t1 =
  { subCount_sort = (Obj.magic set_subType t1); subCountType__1 =
    (Obj.magic set_countMixin t1) }

(** val set_finMixin : Finite.coq_type -> Finite.mixin_of **)

let set_finMixin t1 =
  subFinMixin_for (finfun_finType t1 bool_finType) (fun _ -> true)
    (set_subCountType t1) (set_eqType t1)

(** val set_finType : Finite.coq_type -> Finite.coq_type **)

let set_finType t1 =
  { Finite.base = (Choice.coq_class (set_choiceType t1)); Finite.mixin =
    (set_finMixin t1) }

module type SetDefSig =
 sig
  val finset : Finite.coq_type -> Finite.sort pred0 -> set_of

  val pred_of_set : Finite.coq_type -> set_type -> fin_pred_sort
 end

module SetDef =
 struct
  (** val finset : Finite.coq_type -> (Finite.sort -> bool) -> set_type **)

  let finset =
    FinfunDef.finfun

  (** val pred_of_set : Finite.coq_type -> set_type -> Equality.sort -> bool **)

  let pred_of_set t1 a = __
  (** val finsetE : __ **)

  let finsetE =
    __

  (** val pred_of_setE : __ **)

  let pred_of_setE =
    __
 end

(** val set_of_choiceType : Finite.coq_type -> Choice.coq_type **)

let set_of_choiceType t1 =
  Choice.coq_class (set_choiceType t1)

(** val set_of_countType : Finite.coq_type -> Countable.coq_type **)

let set_of_countType t1 =
  Countable.coq_class (set_countType t1)

(** val set_of_finType : Finite.coq_type -> Finite.coq_type **)

let set_of_finType t1 =
  Finite.coq_class (set_finType t1)

(** val setTfor : Finite.coq_type -> set_of **)

let setTfor t1 =
  SetDef.finset t1 (fun _ -> true)

(** val set1 : Finite.coq_type -> Finite.sort -> set_of **)

let set1 t1 a =
  SetDef.finset t1 (fun x -> eq_op (Finite.eqType t1) x a)

(** val setI : Finite.coq_type -> set_of -> set_of -> set_of **)

let setI t1 a b =
  SetDef.finset t1 (fun x ->
    (&&) (in_mem x (mem predPredType (SetDef.pred_of_set t1 a)))
      (in_mem x (mem predPredType (SetDef.pred_of_set t1 b))))

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

module Imset =
 struct
  (** val imset :
      Finite.coq_type -> Finite.coq_type -> (Finite.sort -> Finite.sort) ->
      Finite.sort mem_pred -> set_of **)

  let imset aT rT f0 mD =
    SetDef.finset rT (fun y ->
      in_mem y (mem (seq_predType (Finite.eqType rT)) (Obj.magic image_mem aT f0 mD)))

  (** val imset2 :
      Finite.coq_type -> Finite.coq_type -> Finite.coq_type -> (Finite.sort ->
      Finite.sort -> Finite.sort) -> Finite.sort mem_pred -> (Finite.sort ->
      Finite.sort mem_pred) -> set_of **)

  let imset2 aT1 aT2 rT f0 d1 d2 =
    SetDef.finset rT (fun y ->
      in_mem y
        (mem (seq_predType (Finite.eqType rT))
          (Obj.magic image_mem (prod_finType aT1 aT2) (prod_curry_subdef f0)
            (mem simplPredType
              (Obj.magic simplPred (fun u ->
                (&&) (PredOfSimpl.coerce (simpl_of_mem d1) (fst u))
                  (PredOfSimpl.coerce (simpl_of_mem (d2 (fst u))) (snd u))))))))

  (** val imsetE : __ **)

  let imsetE =
    __

  (** val imset2E : __ **)

  let imset2E =
    __
 end

(** val preimset :
    Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 mem_pred -> set_of **)

let preimset aT f0 r =
  SetDef.finset aT (fun x -> in_mem (f0 x) r)

module FinGroup =
 struct
  type 't mixin_of = { mul : ('t -> 't -> 't); one : 't; inv : ('t -> 't) }

  (** val mul : 'a1 mixin_of -> 'a1 -> 'a1 -> 'a1 **)

  let mul m0 =
    m0.mul

  (** val one : 'a1 mixin_of -> 'a1 **)

  let one m0 =
    m0.one

  (** val inv : 'a1 mixin_of -> 'a1 -> 'a1 **)

  let inv m0 =
    m0.inv

  type base_type = { base_type__0 : __ mixin_of; base_type__1 : __ Finite.class_of }

  type sort = __

  type arg_sort = sort

  (** val mixin : base_type -> sort mixin_of **)

  let mixin t1 =
    t1.base_type__0

  (** val finClass : base_type -> sort Finite.class_of **)

  let finClass t1 =
    t1.base_type__1

  type coq_type = base_type
    (* singleton inductive, whose constructor was Pack *)

  (** val base : coq_type -> base_type **)

  let base t1 =
    t1

  (** val coq_Mixin : 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> 'a1 mixin_of **)

  let coq_Mixin one1 mul1 inv5 =
    { mul = mul1; one = one1; inv = inv5 }

  (** val finType : base_type -> Finite.coq_type **)

  let finType =
    finClass

  (** val arg_finType : base_type -> Finite.coq_type **)

  let arg_finType bT =
    Finite.coq_class (finType bT)
 end

(** val oneg : FinGroup.base_type -> FinGroup.sort **)

let oneg t1 =
  (FinGroup.mixin t1).FinGroup.one

(** val mulg :
    FinGroup.base_type -> FinGroup.arg_sort -> FinGroup.arg_sort -> FinGroup.sort **)

let mulg t1 =
  (FinGroup.mixin t1).FinGroup.mul

(** val invg : FinGroup.base_type -> FinGroup.arg_sort -> FinGroup.sort **)

let invg t1 =
  (FinGroup.mixin t1).FinGroup.inv

(** val set_mulg : FinGroup.base_type -> set_of -> set_of -> set_of **)

let set_mulg gT a b =
  Imset.imset2 (FinGroup.arg_finType gT) (FinGroup.arg_finType gT)
    (FinGroup.finType gT) (mulg gT)
    (mem predPredType (SetDef.pred_of_set (FinGroup.arg_finType gT) a)) (fun _ ->
    mem predPredType (SetDef.pred_of_set (FinGroup.arg_finType gT) b))

(** val set_invg : FinGroup.base_type -> set_of -> set_of **)

let set_invg gT a =
  preimset (FinGroup.arg_finType gT) (invg gT)
    (mem predPredType (SetDef.pred_of_set (FinGroup.arg_finType gT) a))

(** val group_set_baseGroupMixin :
    FinGroup.base_type -> set_type FinGroup.mixin_of **)

let group_set_baseGroupMixin gT =
  { FinGroup.mul = (set_mulg gT); FinGroup.one =
    (set1 (FinGroup.finType gT) (oneg gT)); FinGroup.inv = (set_invg gT) }

(** val group_set_of_baseGroupType : FinGroup.base_type -> FinGroup.base_type **)

let group_set_of_baseGroupType gT =
  { FinGroup.base_type__0 = (Obj.magic group_set_baseGroupMixin gT);
    FinGroup.base_type__1 =
    (Finite.coq_class (set_finType (FinGroup.arg_finType gT))) }

module GroupSet =
 struct
  type sort = set_of
 end

(** val group_set_eqType : FinGroup.base_type -> Equality.coq_type **)

let group_set_eqType gT =
  Obj.magic set_eqMixin (FinGroup.arg_finType gT)

(** val group_set_choiceType : FinGroup.base_type -> Choice.coq_type **)

let group_set_choiceType gT =
  Choice.coq_class (set_of_choiceType (FinGroup.arg_finType gT))

(** val group_set_countType : FinGroup.base_type -> Countable.coq_type **)

let group_set_countType gT =
  Countable.coq_class (set_of_countType (FinGroup.arg_finType gT))

(** val group_set_finType : FinGroup.base_type -> Finite.coq_type **)

let group_set_finType gT =
  Finite.coq_class (set_of_finType (FinGroup.arg_finType gT))

(** val group_set : FinGroup.coq_type -> set_of -> bool **)

let group_set gT a =
  (&&)
    (in_mem (oneg (FinGroup.base gT))
      (mem predPredType
        (SetDef.pred_of_set (FinGroup.arg_finType (FinGroup.base gT)) a)))
    (SubsetDef.subset (FinGroup.arg_finType (FinGroup.base gT))
      (mem predPredType
        (SetDef.pred_of_set (FinGroup.arg_finType (FinGroup.base gT))
          (Obj.magic mulg (group_set_of_baseGroupType (FinGroup.base gT)) a a)))
      (mem predPredType
        (SetDef.pred_of_set (FinGroup.arg_finType (FinGroup.base gT)) a)))

type group_type = GroupSet.sort
  (* singleton inductive, whose constructor was Group *)

(** val gval : FinGroup.coq_type -> group_type -> GroupSet.sort **)

let gval _ g0 =
  g0

(** val group_subType : FinGroup.coq_type -> GroupSet.sort subType **)

let group_subType gT =
  { val0 = (Obj.magic gval gT); sub0 = (Obj.magic (fun x _ -> x)); subType__2 =
    (fun _ k_S u -> k_S (Obj.magic u) __) }

(** val group_eqMixin : FinGroup.coq_type -> group_type Equality.mixin_of **)

let group_eqMixin gT =
  { Equality.op = (fun x y ->
    eq_op (group_set_eqType (FinGroup.base gT)) (Obj.magic gval gT x)
      (Obj.magic gval gT y)); Equality.mixin_of__1 =
    (Obj.magic val_eqP (group_set_eqType (FinGroup.base gT)) (group_set gT)
      (group_subType gT)) }

(** val group_eqType : FinGroup.coq_type -> Equality.coq_type **)

let group_eqType gT =
  Obj.magic group_eqMixin gT

(** val group_choiceMixin : FinGroup.coq_type -> group_type Choice.mixin_of **)

let group_choiceMixin gT =
  Obj.magic sub_choiceMixin (group_set_choiceType (FinGroup.base gT)) (group_set gT)
    (group_subType gT)

(** val group_choiceType : FinGroup.coq_type -> Choice.coq_type **)

let group_choiceType gT =
  { Choice.base = (Equality.coq_class (group_eqType gT)); Choice.mixin =
    (Obj.magic group_choiceMixin gT) }

(** val group_countMixin : FinGroup.coq_type -> group_type Countable.mixin_of **)

let group_countMixin gT =
  Obj.magic sub_countMixin (group_set_countType (FinGroup.base gT)) (group_set gT)
    (group_subType gT)

(** val group_subCountType : FinGroup.coq_type -> subCountType **)

let group_subCountType gT =
  { subCount_sort = (Obj.magic group_subType gT); subCountType__1 =
    (Obj.magic group_countMixin gT) }

(** val group_finMixin : FinGroup.coq_type -> Finite.mixin_of **)

let group_finMixin gT =
  subFinMixin_for (group_set_finType (FinGroup.base gT)) (Obj.magic group_set gT)
    (group_subCountType gT) (group_eqType gT)

(** val group_finType : FinGroup.coq_type -> Finite.coq_type **)

let group_finType gT =
  { Finite.base = (Choice.coq_class (group_choiceType gT)); Finite.mixin =
    (group_finMixin gT) }

(** val group_of_finType : FinGroup.coq_type -> Finite.coq_type **)

let group_of_finType gT =
  Finite.coq_class (group_finType gT)

(** val generated : FinGroup.coq_type -> set_of -> set_of **)

let generated gT a =
  BigOp.bigop (setTfor (FinGroup.arg_finType (FinGroup.base gT)))
    (Obj.magic index_enum (group_of_finType gT)) (fun g0 -> BigBody (g0,
    (setI (FinGroup.arg_finType (FinGroup.base gT))),
    (SubsetDef.subset (FinGroup.arg_finType (FinGroup.base gT))
      (mem predPredType
        (SetDef.pred_of_set (FinGroup.arg_finType (FinGroup.base gT)) a))
      (mem predPredType
        (SetDef.pred_of_set (FinGroup.arg_finType (FinGroup.base gT)) (gval gT g0)))),
    (gval gT g0)))

(** val cycle : FinGroup.coq_type -> FinGroup.arg_sort -> set_of **)

let cycle gT x =
  generated gT (set1 (FinGroup.arg_finType (FinGroup.base gT)) x)

type perm_type =
  Finite.sort finfun_of
  (* singleton inductive, whose constructor was Perm *)

(** val pval : Finite.coq_type -> perm_type -> Finite.sort finfun_of **)

let pval _ p0 =
  p0

type perm_of = perm_type

(** val perm_subType : Finite.coq_type -> Finite.sort finfun_of subType **)

let perm_subType t1 =
  { val0 = (Obj.magic pval t1); sub0 = (Obj.magic (fun x _ -> x)); subType__2 =
    (fun _ k_S u -> k_S (Obj.magic u) __) }

(** val perm_eqMixin : Finite.coq_type -> perm_type Equality.mixin_of **)

let perm_eqMixin t1 =
  { Equality.op = (fun x y ->
    eq_op (finfun_eqType t1 (Finite.eqType t1)) (Obj.magic pval t1 x)
      (Obj.magic pval t1 y)); Equality.mixin_of__1 =
    (Obj.magic val_eqP (finfun_eqType t1 (Finite.eqType t1)) (fun x ->
      injectiveb t1 (Finite.eqType t1) (fun_of_fin t1 (Obj.magic x)))
      (perm_subType t1)) }

(** val perm_eqType : Finite.coq_type -> Equality.coq_type **)

let perm_eqType t1 =
  Obj.magic perm_eqMixin t1

(** val perm_choiceMixin : Finite.coq_type -> perm_type Choice.mixin_of **)

let perm_choiceMixin t1 =
  Obj.magic sub_choiceMixin (finfun_choiceType t1 (Finite.choiceType t1)) (fun x ->
    injectiveb t1 (Finite.eqType t1) (fun_of_fin t1 (Obj.magic x))) (perm_subType t1)

(** val perm_choiceType : Finite.coq_type -> Choice.coq_type **)

let perm_choiceType t1 =
  { Choice.base = (Equality.coq_class (perm_eqType t1)); Choice.mixin =
    (Obj.magic perm_choiceMixin t1) }

(** val perm_countMixin : Finite.coq_type -> perm_type Countable.mixin_of **)

let perm_countMixin t1 =
  Obj.magic sub_countMixin (finfun_countType t1 (Finite.countType t1)) (fun x ->
    injectiveb t1 (Finite.eqType t1) (fun_of_fin t1 (Obj.magic x))) (perm_subType t1)

(** val perm_subCountType : Finite.coq_type -> subCountType **)

let perm_subCountType t1 =
  { subCount_sort = (Obj.magic perm_subType t1); subCountType__1 =
    (Obj.magic perm_countMixin t1) }

(** val perm_finMixin : Finite.coq_type -> Finite.mixin_of **)

let perm_finMixin t1 =
  subFinMixin_for (finfun_finType t1 t1) (fun x ->
    injectiveb t1 (Finite.eqType t1) (fun_of_fin t1 (Obj.magic x)))
    (perm_subCountType t1) (perm_eqType t1)

(** val perm_finType : Finite.coq_type -> Finite.coq_type **)

let perm_finType t1 =
  { Finite.base = (Choice.coq_class (perm_choiceType t1)); Finite.mixin =
    (perm_finMixin t1) }

(** val perm_for_finType : Finite.coq_type -> Finite.coq_type **)

let perm_for_finType t1 =
  Finite.coq_class (perm_finType t1)

module type PermDefSig =
 sig
  val fun_of_perm : Finite.coq_type -> perm_type -> Finite.sort -> Finite.sort

  val perm : Finite.coq_type -> (Finite.sort -> Finite.sort) -> perm_of
 end

module PermDef =
 struct
  (** val fun_of_perm :
      Finite.coq_type -> perm_type -> Finite.sort -> Finite.sort **)

  let fun_of_perm t1 u =
    fun_of_fin t1 ((perm_subType t1).val0 (Obj.magic u))

  (** val perm : Finite.coq_type -> (Finite.sort -> Finite.sort) -> perm_type **)

  let perm =
    FinfunDef.finfun

  (** val fun_of_permE : __ **)

  let fun_of_permE =
    __

  (** val permE : __ **)

  let permE =
    __
 end

(** val perm_one : Finite.coq_type -> perm_of **)

let perm_one t1 =
  PermDef.perm t1 (fun x -> x)

(** val perm_inv : Finite.coq_type -> perm_of -> perm_of **)

let perm_inv t1 s =
  PermDef.perm t1 (fun x ->
    iinv t1 (Finite.eqType t1) (PermDef.fun_of_perm t1 s)
      (Obj.magic PredOfSimpl.coerce pred_of_argType) x)

(** val perm_mul : Finite.coq_type -> perm_of -> perm_of -> perm_of **)

let perm_mul t1 s t2 =
  PermDef.perm t1 (comp (PermDef.fun_of_perm t1 t2) (PermDef.fun_of_perm t1 s))

(** val perm_of_baseFinGroupMixin :
    Finite.coq_type -> perm_type FinGroup.mixin_of **)

let perm_of_baseFinGroupMixin t1 =
  FinGroup.coq_Mixin (perm_one t1) (perm_mul t1) (perm_inv t1)

(** val perm_of_baseFinGroupType : Finite.coq_type -> FinGroup.base_type **)

let perm_of_baseFinGroupType t1 =
  { FinGroup.base_type__0 = (Obj.magic perm_of_baseFinGroupMixin t1);
    FinGroup.base_type__1 = (Finite.coq_class (perm_finType t1)) }

(** val perm_of_finGroupType : Finite.coq_type -> FinGroup.coq_type **)

let perm_of_finGroupType =
  perm_of_baseFinGroupType

(** val aperm : Finite.coq_type -> Finite.sort -> perm_of -> Finite.sort **)

let aperm t1 x s =
  PermDef.fun_of_perm t1 s x

(** val porbit : Finite.coq_type -> perm_of -> Finite.sort -> set_of **)

let porbit t1 s x =
  Imset.imset (perm_for_finType t1) t1 (Obj.magic aperm t1 x)
    (mem predPredType
      (SetDef.pred_of_set
        (FinGroup.arg_finType (FinGroup.base (perm_of_finGroupType t1)))
        (cycle (perm_of_finGroupType t1) (Obj.magic s))))

(** val porbits : Finite.coq_type -> perm_of -> set_of **)

let porbits t1 s =
  Imset.imset t1 (set_of_finType t1) (Obj.magic porbit t1 s)
    (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType))

(** val odd_perm : Finite.coq_type -> perm_type -> bool **)

let odd_perm t1 s =
  addb
    (odd
      (CardDef.card t1
        (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType))))
    (odd
      (CardDef.card (set_of_finType t1)
        (mem predPredType (SetDef.pred_of_set (set_of_finType t1) (porbits t1 s)))))

module GRing =
 struct
  module Zmodule =
   struct
    type 'v mixin_of = { zero : 'v; opp : ('v -> 'v); add : ('v -> 'v -> 'v) }

    (** val zero : 'a1 mixin_of -> 'a1 **)

    let zero m0 =
      m0.zero

    (** val opp : 'a1 mixin_of -> 'a1 -> 'a1 **)

    let opp m0 =
      m0.opp

    (** val add : 'a1 mixin_of -> 'a1 -> 'a1 -> 'a1 **)

    let add m0 =
      m0.add

    type 't class_of = { base : 't Choice.class_of; mixin : 't mixin_of }

    (** val base : 'a1 class_of -> 'a1 Choice.class_of **)

    let base c =
      c.base

    (** val mixin : 'a1 class_of -> 'a1 mixin_of **)

    let mixin c =
      c.mixin

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    (** val coq_class : coq_type -> sort class_of **)

    let coq_class cT =
      cT

    (** val pack :
        'a1 mixin_of -> Choice.coq_type -> 'a1 Choice.class_of -> coq_type **)

    let pack m0 _ b =
      { base = (Obj.magic b); mixin = (Obj.magic m0) }

    (** val choiceType : coq_type -> Choice.coq_type **)

    let choiceType cT =
      (coq_class cT).base
   end

  (** val zero : Zmodule.coq_type -> Zmodule.sort **)

  let zero v =
    (Zmodule.coq_class v).Zmodule.mixin.Zmodule.zero

  (** val opp : Zmodule.coq_type -> Zmodule.sort -> Zmodule.sort **)

  let opp v =
    (Zmodule.coq_class v).Zmodule.mixin.Zmodule.opp

  (** val add : Zmodule.coq_type -> Zmodule.sort -> Zmodule.sort -> Zmodule.sort **)

  let add v =
    (Zmodule.coq_class v).Zmodule.mixin.Zmodule.add

  module Ring =
   struct
    type mixin_of = { one : Zmodule.sort;
                      mul : (Zmodule.sort -> Zmodule.sort -> Zmodule.sort) }

    (** val one : Zmodule.coq_type -> mixin_of -> Zmodule.sort **)

    let one _ m0 =
      m0.one

    (** val mul :
        Zmodule.coq_type -> mixin_of -> Zmodule.sort -> Zmodule.sort -> Zmodule.sort **)

    let mul _ m0 =
      m0.mul

    (** val coq_EtaMixin :
        Zmodule.coq_type -> Zmodule.sort -> (Zmodule.sort -> Zmodule.sort ->
        Zmodule.sort) -> mixin_of **)

    let coq_EtaMixin _ one1 mul1 =
      { one = one1; mul = mul1 }

    type 'r class_of = { base : 'r Zmodule.class_of; mixin : mixin_of }

    (** val base : 'a1 class_of -> 'a1 Zmodule.class_of **)

    let base c =
      c.base

    (** val mixin : 'a1 class_of -> mixin_of **)

    let mixin c =
      c.mixin

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    (** val coq_class : coq_type -> sort class_of **)

    let coq_class cT =
      cT

    (** val pack :
        'a1 Zmodule.class_of -> mixin_of -> Zmodule.coq_type -> 'a1 Zmodule.class_of
        -> mixin_of -> coq_type **)

    let pack _ _ _ b m0 =
      { base = (Obj.magic b); mixin = m0 }

    (** val zmodType : coq_type -> Zmodule.coq_type **)

    let zmodType cT =
      (coq_class cT).base
   end

  (** val one : Ring.coq_type -> Ring.sort **)

  let one r =
    (Ring.coq_class r).Ring.mixin.Ring.one

  (** val mul : Ring.coq_type -> Ring.sort -> Ring.sort -> Ring.sort **)

  let mul r =
    (Ring.coq_class r).Ring.mixin.Ring.mul

  (** val exp : Ring.coq_type -> Ring.sort -> nat -> Ring.sort **)

  let exp r x n0 =
    iterop n0 (mul r) x (one r)

  module Lmodule =
   struct
    type mixin_of =
      Ring.sort -> Zmodule.sort -> Zmodule.sort
      (* singleton inductive, whose constructor was Mixin *)

    (** val scale :
        Ring.coq_type -> Zmodule.coq_type -> mixin_of -> Ring.sort -> Zmodule.sort
        -> Zmodule.sort **)

    let scale _ _ m0 =
      m0

    type 'v class_of = { base : 'v Zmodule.class_of; mixin : mixin_of }

    (** val base : Ring.coq_type -> 'a1 class_of -> 'a1 Zmodule.class_of **)

    let base _ c =
      c.base

    (** val mixin : Ring.coq_type -> 'a1 class_of -> mixin_of **)

    let mixin _ c =
      c.mixin

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    (** val coq_class : Ring.coq_type -> coq_type -> sort class_of **)

    let coq_class _ cT =
      cT
   end

  (** val scale :
      Ring.coq_type -> Lmodule.coq_type -> Ring.sort -> Lmodule.sort -> Lmodule.sort **)

  let scale r v =
    Lmodule.scale r (Lmodule.coq_class r v).Lmodule.base
      (Lmodule.coq_class r v).Lmodule.mixin

  module ComRing =
   struct
    (** val coq_RingMixin :
        Zmodule.coq_type -> Zmodule.sort -> (Zmodule.sort -> Zmodule.sort ->
        Zmodule.sort) -> Ring.mixin_of **)

    let coq_RingMixin =
      Ring.coq_EtaMixin

    type 'r class_of =
      'r Ring.class_of
      (* singleton inductive, whose constructor was Class *)

    (** val base : 'a1 class_of -> 'a1 Ring.class_of **)

    let base c =
      c

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    (** val coq_class : coq_type -> sort class_of **)

    let coq_class cT =
      cT

    (** val pack :
        ('a1 -> 'a1 -> 'a1) -> Ring.coq_type -> 'a1 Ring.class_of -> coq_type **)

    let pack _ _ b =
      Obj.magic b
   end

  module UnitRing =
   struct
    type mixin_of = { coq_unit : Ring.sort pred0; inv : (Ring.sort -> Ring.sort) }

    (** val coq_unit : Ring.coq_type -> mixin_of -> Ring.sort pred0 **)

    let coq_unit _ m0 =
      m0.coq_unit

    (** val inv : Ring.coq_type -> mixin_of -> Ring.sort -> Ring.sort **)

    let inv _ m0 =
      m0.inv

    (** val coq_EtaMixin :
        Ring.coq_type -> Ring.sort pred0 -> (Ring.sort -> Ring.sort) -> mixin_of **)

    let coq_EtaMixin _ unit1 inv5 =
      { coq_unit = unit1; inv = inv5 }

    type 'r class_of = { base : 'r Ring.class_of; mixin : mixin_of }

    (** val base : 'a1 class_of -> 'a1 Ring.class_of **)

    let base c =
      c.base

    (** val mixin : 'a1 class_of -> mixin_of **)

    let mixin c =
      c.mixin

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    (** val coq_class : coq_type -> sort class_of **)

    let coq_class cT =
      cT

    (** val ringType : coq_type -> Ring.coq_type **)

    let ringType cT =
      (coq_class cT).base
   end

  (** val coq_unit : UnitRing.coq_type -> UnitRing.sort qualifier **)

  let coq_unit r =
    Obj.magic (fun u -> (UnitRing.coq_class r).UnitRing.mixin.UnitRing.coq_unit u)

  (** val inv : UnitRing.coq_type -> UnitRing.sort -> UnitRing.sort **)

  let inv r =
    (UnitRing.coq_class r).UnitRing.mixin.UnitRing.inv

  module ComUnitRing =
   struct
    type 'r class_of = { base : 'r ComRing.class_of; mixin : UnitRing.mixin_of }

    (** val base : 'a1 class_of -> 'a1 ComRing.class_of **)

    let base c =
      c.base

    (** val mixin : 'a1 class_of -> UnitRing.mixin_of **)

    let mixin c =
      c.mixin

    (** val base2 : 'a1 class_of -> 'a1 UnitRing.class_of **)

    let base2 m0 =
      { UnitRing.base = (ComRing.base m0.base); UnitRing.mixin = m0.mixin }

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    (** val coq_class : coq_type -> sort class_of **)

    let coq_class cT =
      cT

    (** val ringType : coq_type -> Ring.coq_type **)

    let ringType cT =
      ComRing.base (coq_class cT).base

    (** val unitRingType : coq_type -> UnitRing.coq_type **)

    let unitRingType cT =
      base2 (coq_class cT)
   end

  module IntegralDomain =
   struct
    type 'r class_of =
      'r ComUnitRing.class_of
      (* singleton inductive, whose constructor was Class *)

    (** val base : 'a1 class_of -> 'a1 ComUnitRing.class_of **)

    let base c =
      c

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    (** val coq_class : coq_type -> sort class_of **)

    let coq_class cT =
      cT
   end

  module Field =
   struct
    type 'f class_of =
      'f IntegralDomain.class_of
      (* singleton inductive, whose constructor was Class *)

    (** val base : 'a1 class_of -> 'a1 IntegralDomain.class_of **)

    let base c =
      c

    type coq_type = __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    (** val coq_class : coq_type -> sort class_of **)

    let coq_class cT =
      cT

    (** val pack :
        'a1 UnitRing.class_of -> IntegralDomain.coq_type -> 'a1
        IntegralDomain.class_of -> coq_type **)

    let pack _ _ b =
      Obj.magic b

    (** val comUnitRingType : coq_type -> ComUnitRing.coq_type **)

    let comUnitRingType cT =
      IntegralDomain.base (base (coq_class cT))
   end
 end

type 'r matrix0 = 'r finfun_of
  (* singleton inductive, whose constructor was Matrix *)

(** val mx_val : nat -> nat -> 'a1 matrix0 -> 'a1 finfun_of **)

let mx_val _ _ a =
  a

(** val matrix_subType : nat -> nat -> 'a1 finfun_of subType **)

let matrix_subType m0 n0 =
  { val0 = (Obj.magic mx_val m0 n0); sub0 = (fun x _ -> Obj.magic x); subType__2 =
    (fun _ iH u -> iH (Obj.magic u) __) }

(** val matrix_key : unit **)

let matrix_key =
  ()

(** val matrix_of_fun_def :
    nat -> nat -> (Finite.sort -> Finite.sort -> 'a1) -> 'a1 matrix0 **)

let matrix_of_fun_def m0 n0 f0 =
  FinfunDef.finfun (prod_finType (ordinal_finType m0) (ordinal_finType n0))
    (fun ij -> f0 (fst (Obj.magic ij)) (snd (Obj.magic ij)))

(** val matrix_of_fun :
    nat -> nat -> unit -> (Finite.sort -> Finite.sort -> 'a1) -> 'a1 matrix0 **)

let matrix_of_fun m0 n0 k =
  locked_with k (matrix_of_fun_def m0 n0)

(** val fun_of_matrix : nat -> nat -> 'a1 matrix0 -> ordinal -> ordinal -> 'a1 **)

let fun_of_matrix m0 n0 a i j =
  fun_of_fin (prod_finType (ordinal_finType m0) (ordinal_finType n0))
    (mx_val m0 n0 a) (Obj.magic (i, j))

(** val matrix_eqMixin :
    Equality.coq_type -> nat -> nat -> Equality.sort matrix0 Equality.mixin_of **)

let matrix_eqMixin r m0 n0 =
  { Equality.op = (fun x y ->
    eq_op (finfun_eqType (prod_finType (ordinal_finType m0) (ordinal_finType n0)) r)
      (Obj.magic mx_val m0 n0 x) (Obj.magic mx_val m0 n0 y)); Equality.mixin_of__1 =
    (Obj.magic val_eqP
      (finfun_eqType (prod_finType (ordinal_finType m0) (ordinal_finType n0)) r)
      (fun _ -> true) (matrix_subType m0 n0)) }

(** val matrix_eqType : Equality.coq_type -> nat -> nat -> Equality.coq_type **)

let matrix_eqType r m0 n0 =
  Obj.magic matrix_eqMixin r m0 n0

(** val matrix_choiceMixin :
    Choice.coq_type -> nat -> nat -> Choice.sort matrix0 Choice.mixin_of **)

let matrix_choiceMixin r m0 n0 =
  Obj.magic sub_choiceMixin
    (finfun_choiceType (prod_finType (ordinal_finType m0) (ordinal_finType n0)) r)
    (fun _ -> true) (matrix_subType m0 n0)

(** val matrix_choiceType : Choice.coq_type -> nat -> nat -> Choice.coq_type **)

let matrix_choiceType r m0 n0 =
  { Choice.base = (Equality.coq_class (matrix_eqType (Choice.eqType r) m0 n0));
    Choice.mixin = (Obj.magic matrix_choiceMixin r m0 n0) }

(** val const_mx_key : unit **)

let const_mx_key =
  ()

(** val const_mx : nat -> nat -> 'a1 -> 'a1 matrix0 **)

let const_mx m0 n0 a =
  matrix_of_fun m0 n0 const_mx_key (fun _ _ -> a)

(** val row' : nat -> nat -> ordinal -> 'a1 matrix0 -> 'a1 matrix0 **)

let row' m0 n0 i0 a =
  matrix_of_fun (pred m0) n0 matrix_key (fun i j ->
    fun_of_matrix m0 n0 a (lift m0 i0 (Obj.magic i)) (Obj.magic j))

(** val col' : nat -> nat -> ordinal -> 'a1 matrix0 -> 'a1 matrix0 **)

let col' m0 n0 j0 a =
  matrix_of_fun m0 (pred n0) matrix_key (fun i j ->
    fun_of_matrix m0 n0 a (Obj.magic i) (lift n0 j0 (Obj.magic j)))

(** val oppmx_key : unit **)

let oppmx_key =
  ()

(** val addmx_key : unit **)

let addmx_key =
  ()

(** val oppmx :
    GRing.Zmodule.coq_type -> nat -> nat -> GRing.Zmodule.sort matrix0 ->
    GRing.Zmodule.sort matrix0 **)

let oppmx v m0 n0 a =
  matrix_of_fun m0 n0 oppmx_key (fun i j ->
    GRing.opp v (fun_of_matrix m0 n0 a (Obj.magic i) (Obj.magic j)))

(** val addmx :
    GRing.Zmodule.coq_type -> nat -> nat -> GRing.Zmodule.sort matrix0 ->
    GRing.Zmodule.sort matrix0 -> GRing.Zmodule.sort matrix0 **)

let addmx v m0 n0 a b =
  matrix_of_fun m0 n0 addmx_key (fun i j ->
    GRing.add v (fun_of_matrix m0 n0 a (Obj.magic i) (Obj.magic j))
      (fun_of_matrix m0 n0 b (Obj.magic i) (Obj.magic j)))

(** val matrix_zmodMixin :
    GRing.Zmodule.coq_type -> nat -> nat -> GRing.Zmodule.sort matrix0
    GRing.Zmodule.mixin_of **)

let matrix_zmodMixin v m0 n0 =
  { GRing.Zmodule.zero = (const_mx m0 n0 (GRing.zero v)); GRing.Zmodule.opp =
    (oppmx v m0 n0); GRing.Zmodule.add = (addmx v m0 n0) }

(** val matrix_zmodType :
    GRing.Zmodule.coq_type -> nat -> nat -> GRing.Zmodule.coq_type **)

let matrix_zmodType v m0 n0 =
  { GRing.Zmodule.base =
    (Choice.coq_class (matrix_choiceType (GRing.Zmodule.choiceType v) m0 n0));
    GRing.Zmodule.mixin = (Obj.magic matrix_zmodMixin v m0 n0) }

(** val scalemx_key : unit **)

let scalemx_key =
  ()

(** val scalemx :
    GRing.Ring.coq_type -> nat -> nat -> GRing.Ring.sort -> GRing.Ring.sort matrix0
    -> GRing.Ring.sort matrix0 **)

let scalemx r m0 n0 x a =
  matrix_of_fun m0 n0 scalemx_key (fun i j ->
    GRing.mul r x (fun_of_matrix m0 n0 a (Obj.magic i) (Obj.magic j)))

(** val matrix_lmodMixin :
    GRing.Ring.coq_type -> nat -> nat -> GRing.Lmodule.mixin_of **)

let matrix_lmodMixin r m0 n0 =
  Obj.magic scalemx r m0 n0

(** val matrix_lmodType :
    GRing.Ring.coq_type -> nat -> nat -> GRing.Lmodule.coq_type **)

let matrix_lmodType r m0 n0 =
  { GRing.Lmodule.base =
    (GRing.Zmodule.coq_class (matrix_zmodType (GRing.Ring.zmodType r) m0 n0));
    GRing.Lmodule.mixin = (matrix_lmodMixin r m0 n0) }

(** val determinant :
    GRing.Ring.coq_type -> nat -> GRing.Ring.sort matrix0 -> GRing.Ring.sort **)

let determinant r n0 a =
  BigOp.bigop (GRing.zero (GRing.Ring.zmodType r))
    (Obj.magic index_enum (perm_for_finType (ordinal_finType n0))) (fun s -> BigBody
    (s, (GRing.add (GRing.Ring.zmodType r)), true,
    (GRing.mul r
      (GRing.exp r (GRing.opp (GRing.Ring.zmodType r) (GRing.one r))
        (nat_of_bool (odd_perm (ordinal_finType n0) s)))
      (BigOp.bigop (GRing.one r) (index_enum (ordinal_finType n0)) (fun i -> BigBody
        (i, (GRing.mul r), true,
        (fun_of_matrix n0 n0 a (Obj.magic i)
          (Obj.magic PermDef.fun_of_perm (ordinal_finType n0) s i))))))))

(** val cofactor :
    GRing.Ring.coq_type -> nat -> GRing.Ring.sort matrix0 -> ordinal -> ordinal ->
    GRing.Ring.sort **)

let cofactor r n0 a i j =
  GRing.mul r
    (GRing.exp r (GRing.opp (GRing.Ring.zmodType r) (GRing.one r))
      (addn (nat_of_ord n0 i) (nat_of_ord n0 j)))
    (determinant r (pred n0) (row' n0 (pred n0) i (col' n0 n0 j a)))

(** val adjugate_key : unit **)

let adjugate_key =
  ()

(** val adjugate :
    GRing.Ring.coq_type -> nat -> GRing.Ring.sort matrix0 -> GRing.Ring.sort matrix0 **)

let adjugate r n0 a =
  matrix_of_fun n0 n0 adjugate_key (fun i j ->
    cofactor r n0 a (Obj.magic j) (Obj.magic i))

(** val unitmx :
    GRing.ComUnitRing.coq_type -> nat -> GRing.ComUnitRing.sort matrix0 pred0 **)

let unitmx r n0 a =
  in_mem (determinant (GRing.ComUnitRing.ringType r) n0 a)
    (mem predPredType
      (has_quality (S O) (GRing.coq_unit (GRing.ComUnitRing.unitRingType r))))

(** val invmx :
    GRing.ComUnitRing.coq_type -> nat -> GRing.ComUnitRing.sort matrix0 ->
    GRing.Lmodule.sort **)

let invmx r n0 a =
  if in_mem a (mem predPredType (Obj.magic unitmx r n0))
  then GRing.scale (GRing.UnitRing.ringType (GRing.ComUnitRing.unitRingType r))
         (matrix_lmodType
           (GRing.UnitRing.ringType (GRing.ComUnitRing.unitRingType r)) n0 n0)
         (GRing.inv (GRing.ComUnitRing.unitRingType r)
           (determinant (GRing.ComUnitRing.ringType r) n0 a))
         (Obj.magic adjugate (GRing.ComUnitRing.ringType r) n0 a)
  else Obj.magic a

(** val epsilon_statement : __ -> 'a1 **)

let epsilon_statement a =
  failwith "AXIOM TO BE REALIZED"

(** val epsilon : __ -> 'a1 **)

let epsilon _ =
  epsilon_statement __

module Coq_makeField =
 functor (Coq_f:FieldSig) ->
 struct
  module AL = RingAddationalLemmas(Coq_f)

  type coq_R = Coq_f.coq_F

  (** val eqr : coq_R -> coq_R -> bool **)

  let eqr =
    Coq_f.coq_Fbool_eq

  (** val eqrP : coq_R Equality.axiom **)

  let eqrP x y =
    introP (Coq_f.coq_Fbool_eq x y)

  (** val coq_R_eqMixin : coq_R Equality.mixin_of **)

  let coq_R_eqMixin =
    { Equality.op = eqr; Equality.mixin_of__1 = eqrP }

  (** val coq_R_eqType : Equality.coq_type **)

  let coq_R_eqType =
    Obj.magic coq_R_eqMixin

  (** val pickR : coq_R pred0 -> nat -> coq_R option **)

  let pickR p0 _ =
    let x = epsilon __ in if p0 x then Some x else None

  (** val coq_R_choiceMixin : coq_R Choice.mixin_of **)

  let coq_R_choiceMixin =
    pickR

  (** val coq_R_choiceType : Choice.coq_type **)

  let coq_R_choiceType =
    { Choice.base = (Equality.coq_class coq_R_eqType); Choice.mixin =
      (Obj.magic coq_R_choiceMixin) }

  (** val coq_R_zmodmixin : Coq_f.coq_F GRing.Zmodule.mixin_of **)

  let coq_R_zmodmixin =
    { GRing.Zmodule.zero = Coq_f.coq_Fzero; GRing.Zmodule.opp = Coq_f.coq_Finv;
      GRing.Zmodule.add = Coq_f.coq_Fadd }

  (** val coq_R_zmodtype : GRing.Zmodule.coq_type **)

  let coq_R_zmodtype =
    GRing.Zmodule.pack (Obj.magic coq_R_zmodmixin) coq_R_choiceType
      (Choice.coq_class coq_R_choiceType)

  (** val coq_R_comringmixin : GRing.Ring.mixin_of **)

  let coq_R_comringmixin =
    GRing.ComRing.coq_RingMixin coq_R_zmodtype (Obj.magic Coq_f.coq_Fone)
      (Obj.magic Coq_f.coq_Fmul)

  (** val coq_R_ring : GRing.Ring.coq_type **)

  let coq_R_ring =
    GRing.Ring.pack (GRing.Zmodule.coq_class coq_R_zmodtype) coq_R_comringmixin
      coq_R_zmodtype (GRing.Zmodule.coq_class coq_R_zmodtype) coq_R_comringmixin

  (** val coq_R_comring : GRing.ComRing.coq_type **)

  let coq_R_comring =
    GRing.ComRing.pack (Obj.magic Coq_f.coq_Fmul) coq_R_ring
      (GRing.Ring.coq_class coq_R_ring)

  (** val coq_Radd_monoid : Coq_f.coq_F Monoid.law **)

  let coq_Radd_monoid =
    Coq_f.coq_Fadd

  (** val coq_Radd_comoid : Coq_f.coq_F Monoid.com_law **)

  let coq_Radd_comoid =
    coq_Radd_monoid

  (** val coq_Rmul_monoid : GRing.Zmodule.sort Monoid.law **)

  let coq_Rmul_monoid =
    Obj.magic Coq_f.coq_Fmul

  (** val coq_Rmul_comoid : Coq_f.coq_F Monoid.com_law **)

  let coq_Rmul_comoid =
    Obj.magic coq_Rmul_monoid

  (** val coq_Rmul_mul_law : Coq_f.coq_F Monoid.mul_law **)

  let coq_Rmul_mul_law =
    Coq_f.coq_Fmul

  (** val coq_Radd_add_law : Coq_f.coq_F Monoid.add_law **)

  let coq_Radd_add_law =
    coq_Radd_comoid

  (** val coq_Rinvx : coq_R -> Coq_f.coq_F **)

  let coq_Rinvx r =
    if negb (eqr r Coq_f.coq_Fzero) then Coq_f.coq_FmulInv r else r

  (** val unit_R : coq_R -> bool **)

  let unit_R r =
    negb (eqr r Coq_f.coq_Fzero)

  (** val coq_R_unitRingMixin : GRing.UnitRing.mixin_of **)

  let coq_R_unitRingMixin =
    GRing.UnitRing.coq_EtaMixin coq_R_ring (Obj.magic unit_R) (Obj.magic coq_Rinvx)

  (** val coq_R_unitRing : GRing.UnitRing.coq_type **)

  let coq_R_unitRing =
    { GRing.UnitRing.base = (GRing.Ring.coq_class coq_R_ring);
      GRing.UnitRing.mixin = coq_R_unitRingMixin }

  (** val coq_R_comUnitRingType : GRing.ComUnitRing.coq_type **)

  let coq_R_comUnitRingType =
    { GRing.ComUnitRing.base = (GRing.ComRing.coq_class coq_R_comring);
      GRing.ComUnitRing.mixin = coq_R_unitRingMixin }

  (** val coq_R_idomainType : GRing.IntegralDomain.coq_type **)

  let coq_R_idomainType =
    GRing.ComUnitRing.coq_class coq_R_comUnitRingType

  (** val coq_R_field : GRing.Field.coq_type **)

  let coq_R_field =
    GRing.Field.pack (GRing.UnitRing.coq_class coq_R_unitRing) coq_R_idomainType
      (GRing.IntegralDomain.coq_class coq_R_idomainType)
 end

(** val vector_inv_S : nat -> 'a1 t0 -> ('a1, 'a1 t0) sigT **)

let vector_inv_S _ = function
| Nil -> Obj.magic __
| Cons (x, _, v') -> ExistT (x, v')

(** val fin_inv_S : nat -> t -> (__, t) sum **)

let fin_inv_S _ = function
| F1 _ -> Inl __
| FS (_, t1) -> Inr t1

(** val vector_to_finite_fun : nat -> 'a1 t0 -> t -> 'a1 **)

let rec vector_to_finite_fun n0 v f0 =
  match n0 with
  | O -> assert false (* absurd case *)
  | S n1 ->
    let s = vector_inv_S n1 v in
    let ExistT (x, p0) = s in
    let s0 = fin_inv_S n1 f0 in
    (match s0 with
     | Inl _ -> x
     | Inr b -> vector_to_finite_fun n1 p0 b)

(** val finite_fun_to_vector : nat -> (t -> 'a1) -> 'a1 t0 **)

let rec finite_fun_to_vector n0 f0 =
  match n0 with
  | O -> Nil
  | S n1 ->
    Cons ((f0 (F1 n1)), n1, (finite_fun_to_vector n1 (fun m0 -> f0 (FS (n1, m0)))))

type 'r matrix1 = 'r t0 t0

(** val finite_fun_to_matrix : nat -> nat -> (t -> t -> 'a1) -> 'a1 matrix1 **)

let finite_fun_to_matrix n0 m0 f0 =
  finite_fun_to_vector m0 (fun x -> finite_fun_to_vector n0 (fun y -> f0 y x))

(** val matrix_to_finite_fun : nat -> nat -> 'a1 matrix1 -> t -> t -> 'a1 **)

let matrix_to_finite_fun n0 m0 mx x y =
  vector_to_finite_fun n0 (vector_to_finite_fun m0 mx y) x

(** val finite_to_ord : nat -> t -> ordinal **)

let finite_to_ord =
  to_nat

(** val ord_to_finite : nat -> ordinal -> t **)

let ord_to_finite n0 x =
  ssr_have __ (fun _ -> of_nat_lt (nat_of_ord n0 x) n0)

(** val matrix_to_matrix : nat -> nat -> 'a1 matrix1 -> 'a1 matrix0 **)

let matrix_to_matrix n0 m0 mx =
  matrix_of_fun n0 m0 matrix_key (fun i j ->
    matrix_to_finite_fun n0 m0 mx (ord_to_finite n0 (Obj.magic i))
      (ord_to_finite m0 (Obj.magic j)))

(** val matrix_to_Matrix : nat -> nat -> 'a1 matrix0 -> 'a1 matrix1 **)

let matrix_to_Matrix n0 m0 mx =
  finite_fun_to_matrix n0 m0 (fun i j ->
    fun_of_matrix n0 m0 mx (finite_to_ord n0 i) (finite_to_ord m0 j))

(** val matrix_inv :
    GRing.Field.coq_type -> nat -> GRing.Field.sort matrix1 -> GRing.Field.sort
    matrix1 **)

let matrix_inv r n0 mx =
  matrix_to_Matrix n0 n0
    (Obj.magic invmx (GRing.Field.comUnitRingType r) n0 (matrix_to_matrix n0 n0 mx))

module MatricesFieldIns =
 functor (Field:FieldSig) ->
 struct
  module Coq_mat = MatricesFIns(Field)

  module AL = RingAddationalLemmas(Field)

  module FAL = FieldAddationalLemmas(Field)

  (** val coq_VandermondeCol : nat -> Field.coq_F -> Field.coq_F t0 **)

  let coq_VandermondeCol m0 c =
    vbuild m0 (fun i _ -> Coq_mat.coq_VF_prod i (const c i))

  (** val coq_VandermondeColGen : nat -> Field.coq_F -> nat -> Field.coq_F t0 **)

  let coq_VandermondeColGen m0 c base0 =
    vbuild m0 (fun i _ -> Coq_mat.coq_VF_prod (add i base0) (const c (add i base0)))

  (** val coq_Vandermonde : nat -> Coq_mat.coq_VF -> Field.coq_F t0 t0 **)

  let coq_Vandermonde m0 c =
    vmap (coq_VandermondeCol m0) m0 c

  module SSRfield = Coq_makeField(Field)

  (** val coq_VandermondeInv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_MF **)

  let coq_VandermondeInv m0 c =
    Obj.magic matrix_inv SSRfield.coq_R_field m0 (coq_Vandermonde m0 c)

  (** val nat_to_ord : nat -> nat -> ordinal **)

  let nat_to_ord i _ =
    i

  (** val coq_VF_inv : nat -> Coq_mat.coq_VF -> Coq_mat.coq_VF **)

  let coq_VF_inv n0 v1 =
    vmap Field.coq_FmulInv n0 v1
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

module type Coq_Nat =
 sig
  val coq_N : nat
 end

module GroupNthIns =
 functor (Group:GroupSig) ->
 functor (Hack:Coq_Nat) ->
 struct
  type coq_G = Group.coq_G t0

  (** val coq_Gdot : coq_G -> coq_G -> coq_G **)

  let coq_Gdot a b =
    vmap2 Group.coq_Gdot (S Hack.coq_N) a b

  (** val coq_Gone : Group.coq_G t0 **)

  let coq_Gone =
    const Group.coq_Gone (S Hack.coq_N)

  (** val coq_Ggen : Group.coq_G t0 **)

  let coq_Ggen =
    const Group.coq_Ggen (S Hack.coq_N)

  (** val coq_Gbool_eq : coq_G -> coq_G -> bool **)

  let coq_Gbool_eq a b =
    bVforall2 Group.coq_Gbool_eq (S Hack.coq_N) a b

  (** val coq_Gdisjoint : coq_G -> coq_G -> bool **)

  let coq_Gdisjoint a b =
    bVforall2 Group.coq_Gdisjoint (S Hack.coq_N) a b

  (** val coq_Ginv : coq_G -> Group.coq_G t0 **)

  let coq_Ginv a =
    vmap Group.coq_Ginv (S Hack.coq_N) a
 end

module NthRingIns =
 functor (Hack:Coq_Nat) ->
 functor (Ring:RingSig) ->
 struct
  type coq_F = Ring.coq_F t0

  (** val coq_Fadd : coq_F -> coq_F -> Ring.coq_F t0 **)

  let coq_Fadd a b =
    vmap2 Ring.coq_Fadd (S Hack.coq_N) a b

  (** val coq_Fzero : Ring.coq_F t0 **)

  let coq_Fzero =
    const Ring.coq_Fzero (S Hack.coq_N)

  (** val coq_Fbool_eq : coq_F -> coq_F -> bool **)

  let coq_Fbool_eq a b =
    bVforall2 Ring.coq_Fbool_eq (S Hack.coq_N) a b

  (** val coq_Fsub : coq_F -> coq_F -> Ring.coq_F t0 **)

  let coq_Fsub a b =
    vmap2 Ring.coq_Fsub (S Hack.coq_N) a b

  (** val coq_Finv : coq_F -> Ring.coq_F t0 **)

  let coq_Finv a =
    vmap Ring.coq_Finv (S Hack.coq_N) a

  (** val coq_Fmul : coq_F -> coq_F -> Ring.coq_F t0 **)

  let coq_Fmul a b =
    vmap2 Ring.coq_Fmul (S Hack.coq_N) a b

  (** val coq_Fone : Ring.coq_F t0 **)

  let coq_Fone =
    const Ring.coq_Fone (S Hack.coq_N)
 end

module NthVectorSpaceIns =
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
 struct
  module MatF = MatricesFIns(Field)

  module Mat = MatricesG(Group)(Field)(VS)(MatF)

  (** val op : NthGroup.coq_G -> Field.coq_F -> Mat.coq_VG **)

  let op a b =
    Mat.coq_VG_Sexp (S Hack.coq_N) a b
 end

module VectorSpaceModuleSameGroupNthStackIns =
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
 struct
  (** val op3 : NthRing.coq_F -> Field.coq_F -> Ring.coq_F t0 **)

  let op3 a b =
    vmap (fun x -> MVS.op3 x b) (S Hack.coq_N) a
 end

module GroupFromRingIns =
 functor (Ring:RingSig) ->
 struct
  type coq_G = Ring.coq_F

  (** val coq_Gdot : Ring.coq_F -> Ring.coq_F -> Ring.coq_F **)

  let coq_Gdot =
    Ring.coq_Fadd

  (** val coq_Gone : Ring.coq_F **)

  let coq_Gone =
    Ring.coq_Fzero

  (** val coq_Ggen : Ring.coq_F **)

  let coq_Ggen =
    Ring.coq_Fone

  (** val coq_Gbool_eq : Ring.coq_F -> Ring.coq_F -> bool **)

  let coq_Gbool_eq =
    Ring.coq_Fbool_eq

  (** val coq_Gdisjoint : Ring.coq_F -> Ring.coq_F -> bool **)

  let coq_Gdisjoint a b =
    negb (Ring.coq_Fbool_eq a b)

  (** val coq_Ginv : Ring.coq_F -> Ring.coq_F **)

  let coq_Ginv =
    Ring.coq_Finv
 end

module GroupFromFieldIns =
 functor (Field:FieldSig) ->
 struct
  type coq_G = Field.coq_F

  (** val coq_Gdot : coq_G -> coq_G -> coq_G **)

  let coq_Gdot =
    Field.coq_Fmul

  (** val coq_Gone : coq_G **)

  let coq_Gone =
    Field.coq_Fone

  (** val coq_Ggen : coq_G **)

  let coq_Ggen =
    Field.coq_Fone

  (** val coq_Gbool_eq : coq_G -> coq_G -> bool **)

  let coq_Gbool_eq =
    Field.coq_Fbool_eq

  (** val coq_Gdisjoint : coq_G -> coq_G -> bool **)

  let coq_Gdisjoint h h0 =
    negb (Field.coq_Fbool_eq h h0)

  (** val coq_Ginv : coq_G -> coq_G **)

  let coq_Ginv =
    Field.coq_FmulInv
 end

module ProdGroupSigIns =
 functor (M1M:GroupSig) ->
 functor (M2M:GroupSig) ->
 struct
  type coq_G = M1M.coq_G * M2M.coq_G

  (** val coq_Gdot : coq_G -> coq_G -> M1M.coq_G * M2M.coq_G **)

  let coq_Gdot a b =
    ((M1M.coq_Gdot (fst a) (fst b)), (M2M.coq_Gdot (snd a) (snd b)))

  (** val coq_Gone : M1M.coq_G * M2M.coq_G **)

  let coq_Gone =
    (M1M.coq_Gone, M2M.coq_Gone)

  (** val coq_Ggen : M1M.coq_G * M2M.coq_G **)

  let coq_Ggen =
    (M1M.coq_Ggen, M2M.coq_Ggen)

  (** val coq_Gbool_eq : coq_G -> coq_G -> bool **)

  let coq_Gbool_eq a b =
    (&&) (M1M.coq_Gbool_eq (fst a) (fst b)) (M2M.coq_Gbool_eq (snd a) (snd b))

  (** val coq_Gdisjoint : coq_G -> coq_G -> bool **)

  let coq_Gdisjoint a b =
    (&&) (M1M.coq_Gdisjoint (fst a) (fst b)) (M2M.coq_Gdisjoint (snd a) (snd b))

  (** val coq_Ginv : coq_G -> M1M.coq_G * M2M.coq_G **)

  let coq_Ginv a =
    ((M1M.coq_Ginv (fst a)), (M2M.coq_Ginv (snd a)))
 end

module MixablePropIns =
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
 struct
  module AddVSLemmas = VectorSpaceAddationalLemmas(Ciphertext)(Field)(VS)

  module Mat = MatricesFIns(Field)

  module MatG = MatricesG(Ciphertext)(Field)(VS)(Mat)

  (** val reenc :
      Mix.coq_PK -> Ciphertext.coq_G -> Ring.coq_F -> Ciphertext.coq_G **)

  let reenc pk c r =
    Ciphertext.coq_Gdot (Mix.enc pk Mix.coq_Mzero r) c

  (** val bIsReEnc :
      Mix.coq_PK -> Ciphertext.coq_G -> Ciphertext.coq_G -> Ring.coq_F -> bool **)

  let bIsReEnc pk c1 c2 r =
    Ciphertext.coq_Gbool_eq c2 (reenc pk c1 r)

  (** val decryptsToExt :
      Mix.coq_PK -> Ciphertext.coq_G -> Mix.coq_M -> Ring.coq_F -> bool **)

  let decryptsToExt pk c m0 r =
    let c' = Mix.enc pk m0 r in Ciphertext.coq_Gbool_eq c' c
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

  val coq_Mone : Message.coq_G

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

  module Mat = MatricesFIns(Field)

  module MatG = MatricesG(Ciphertext)(Field)(VS)(Mat)

  (** val reenc :
      Enc.coq_PK -> Ciphertext.coq_G -> Ring.coq_F -> Ciphertext.coq_G **)

  let reenc pk c r =
    Ciphertext.coq_Gdot (Enc.enc pk Enc.coq_Mzero r) c

  (** val bIsReEnc :
      Enc.coq_PK -> Ciphertext.coq_G -> Ciphertext.coq_G -> Ring.coq_F -> bool **)

  let bIsReEnc pk c1 c2 r =
    Ciphertext.coq_Gbool_eq c2 (reenc pk c1 r)

  (** val decryptsToExt :
      Enc.coq_PK -> Ciphertext.coq_G -> Enc.coq_M -> Ring.coq_F -> bool **)

  let decryptsToExt pk c m0 r =
    let c' = Enc.enc pk m0 r in Ciphertext.coq_Gbool_eq c' c
 end

module type Coq0_Nat =
 sig
  val coq_N : nat
 end

module ExtendedElGamal =
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
 struct
  module Mo = MatricesFIns(Field)

  module MoM = MatricesG(Group)(Field)(VS)(Mo)

  module AddVSLemmas = VectorSpaceAddationalLemmas(Group)(Field)(VS)

  type coq_KGR = MoM.coq_VG * Mo.coq_VF

  type coq_PK = NthGroup.coq_G

  type coq_SK = Mo.coq_VF

  type coq_M = NthGroupM.coq_G

  (** val coq_Mop : NthGroupM.coq_G -> NthGroupM.coq_G -> NthGroupM.coq_G **)

  let coq_Mop =
    NthGroupM.coq_Gdot

  (** val coq_Mzero : Group.coq_G t0 **)

  let coq_Mzero =
    NthGroupM.coq_Gone

  (** val coq_Mone : Group.coq_G t0 **)

  let coq_Mone =
    NthGroupM.coq_Ggen

  (** val coq_Minv : NthGroupM.coq_G -> Group.coq_G t0 **)

  let coq_Minv =
    NthGroupM.coq_Ginv

  (** val coq_Mbool_eq : NthGroupM.coq_G -> NthGroupM.coq_G -> bool **)

  let coq_Mbool_eq =
    NthGroupM.coq_Gbool_eq

  (** val keygen : coq_KGR -> coq_PK * coq_SK **)

  let keygen kgr =
    ((vmap2 (fun x y -> (x, (VS.op x y))) (S Hack.coq_N) (fst kgr) (snd kgr)),
      (snd kgr))

  (** val keygenMix : coq_KGR -> coq_PK **)

  let keygenMix kgr =
    fst (keygen kgr)

  (** val enc : coq_PK -> coq_M -> Mo.coq_VF -> NthGroup.coq_G **)

  let enc pk m0 r =
    let mr = vmap2 (fun x y -> (x, y)) (S Hack.coq_N) m0 r in
    vmap2 (fun pk0 mr0 -> ((VS.op (fst pk0) (snd mr0)),
      (Group.coq_Gdot (VS.op (snd pk0) (snd mr0)) (fst mr0)))) (S Hack.coq_N) pk mr

  (** val dec : coq_SK -> NthGroup.coq_G -> coq_M **)

  let dec sk c =
    vmap2 (fun sk0 c0 ->
      Group.coq_Gdot (snd c0) (Group.coq_Ginv (VS.op (fst c0) sk0))) (S Hack.coq_N)
      sk c

  (** val keymatch : coq_PK -> coq_SK -> bool **)

  let keymatch pk sk =
    MoM.coq_VG_eq (S Hack.coq_N)
      (vmap2 (fun pk0 sk0 -> VS.op (fst pk0) sk0) (S Hack.coq_N) pk sk)
      (vmap fst (S Hack.coq_N) pk)
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
 struct
  module AddMLemmas = ModuleAddationalLemmas(Group)(Ring)(M)

  module MoM = MatricesG(Group)(Ring)(M)(Mo)

  (** val coq_PC :
      Group.coq_G -> Group.coq_G -> Ring.coq_F -> Ring.coq_F -> Group.coq_G **)

  let coq_PC h h1 m0 r =
    Group.coq_Gdot (M.op h r) (M.op h1 m0)

  (** val comPC :
      nat -> Group.coq_G -> Group.coq_G -> Mo.coq_VF -> Mo.coq_VF -> MoM.coq_VG **)

  let comPC n0 h h1 m0 r =
    vmap2 (coq_PC h h1) n0 m0 r
 end

module ExtendComScheme =
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
 struct
  module MoM = MatricesG(Group)(Ring)(M)(Mo)

  (** val coq_EPC :
      nat -> Group.coq_G -> MoM.coq_VG -> Mo.coq_VF -> Ring.coq_F -> Group.coq_G **)

  let coq_EPC n0 h hs m0 r =
    Group.coq_Gdot (M.op h r) (MoM.coq_VG_prod n0 (MoM.coq_VG_Pexp n0 hs m0))

  (** val comEPC :
      nat -> nat -> Group.coq_G -> MoM.coq_VG -> Mo.coq_VF t0 -> Mo.coq_VF ->
      MoM.coq_VG **)

  let comEPC n0 n' h hs m0 r =
    vmap2 (coq_EPC n0 h hs) n' m0 r

  (** val comEPCvec :
      nat -> nat -> Group.coq_G -> MoM.coq_VG -> Mo.coq_VF -> Mo.coq_VF -> MoM.coq_VG **)

  let comEPCvec n0 n' h hs m0 r =
    comEPC n0 n' h hs (vecToMat n0 n' m0) r

  (** val com :
      nat -> Group.coq_G -> MoM.coq_VG -> Mo.coq_MF -> Mo.coq_VF -> MoM.coq_VG **)

  let com n0 h hs m0 r =
    comEPC n0 n0 h hs m0 r
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

module BGSupportIns =
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
 struct
  (** val n : nat **)

  let n =
    S (S (S Hack.coq_N))

  (** val m : nat **)

  let m =
    S (S M.coq_N)

  module Mo = MatricesFieldIns(Field)

  module MoR = MatricesFIns(Ring)

  module MoC = MatricesG(Ciphertext)(Field)(VS1)(Mo.Coq_mat)

  module EPC = ExtendComScheme(Commitment)(Field)(VS2)(Mo.Coq_mat)

  module PC = BasicComScheme(Commitment)(Field)(VS2)(Mo.Coq_mat)

  module MoM = MatricesG(Message)(Field)(VS3)(Mo.Coq_mat)

  module ALVS1 = VectorSpaceAddationalLemmas(Ciphertext)(Field)(VS1)

  module ALVS2 = VectorSpaceAddationalLemmas(Commitment)(Field)(VS2)

  module ALVS3 = VectorSpaceAddationalLemmas(Message)(Field)(VS3)

  module ALenc =
   EncryptionSchemeProp(Message)(Ciphertext)(Ring)(Field)(VS1)(MVS)(Coq_enc)

  module HardProb = HardProblems(Commitment)(Field)(VS2)

  module ALR = RingAddationalLemmas(Ring)

  (** val coq_ProdOfDiagonals :
      'a1 -> ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 t0 t0 -> 'a1 t0 **)

  let coq_ProdOfDiagonals a f0 n0 a0 =
    let left =
      vbuild (S n0) (fun i _ ->
        vfold_left f0 (S i) a
          (vbuild (S i) (fun j _ ->
            vnth (S n0) (vnth (S n0) a0 j) (add j (sub n0 i)))))
    in
    let right =
      vbuild n0 (fun i _ ->
        vfold_left f0 (S i) a
          (vbuild (S i) (fun j _ ->
            vnth (S n0) (vnth (S n0) a0 (add j (sub n0 i))) j)))
    in
    vapp (S n0) n0 left (rev n0 right)

  (** val coq_ProdOfDiagonalsF : nat -> Field.coq_F t0 t0 -> Field.coq_F t0 **)

  let coq_ProdOfDiagonalsF =
    coq_ProdOfDiagonals Field.coq_Fzero Field.coq_Fadd

  (** val coq_ProdOfDiagonalsVF :
      nat -> nat -> Field.coq_F t0 t0 t0 -> Field.coq_F t0 t0 **)

  let coq_ProdOfDiagonalsVF n0 =
    coq_ProdOfDiagonals (Mo.Coq_mat.coq_VF_zero n0) (Mo.Coq_mat.coq_VF_add n0)

  (** val coq_ProdOfDiagonalsG :
      nat -> Commitment.coq_G t0 t0 -> Commitment.coq_G t0 **)

  let coq_ProdOfDiagonalsG =
    coq_ProdOfDiagonals Commitment.coq_Gone Commitment.coq_Gdot

  (** val coq_RF_inProd : nat -> Mo.Coq_mat.coq_VF -> MoR.coq_VF -> Ring.coq_F **)

  let coq_RF_inProd n0 a b =
    vfold_left Ring.coq_Fadd n0 Ring.coq_Fzero (vmap2 MVS.op3 n0 b a)

  (** val coq_RF_VCmult : nat -> Mo.Coq_mat.coq_MF -> MoR.coq_VF -> MoR.coq_VF **)

  let coq_RF_VCmult n0 m0 v =
    vmap (fun a -> coq_RF_inProd n0 a v) n0 m0

  (** val coq_WeirdCs :
      nat -> nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG **)

  let coq_WeirdCs a j cBar a0 =
    let first =
      vbuild j (fun i _ ->
        MoC.coq_VG_prod (add (S O) i)
          (vmap2 (fun x y -> MoC.coq_VG_prod a (MoC.coq_VG_Pexp a x y))
            (add (S O) i) (vsub j cBar (sub j (add (S O) i)) (add (S O) i))
            (vsub (add (S O) j) a0 O (add (S O) i))))
    in
    let second =
      vbuild j (fun i _ ->
        MoC.coq_VG_prod (add (S O) i)
          (vmap2 (fun x y -> MoC.coq_VG_prod a (MoC.coq_VG_Pexp a x y))
            (add (S O) i) (vsub j cBar O (add (S O) i))
            (vsub (add (S O) j) a0 (sub (S j) (add (S O) i)) (add (S O) i))))
    in
    vapp j j first (rev j second)

  (** val coq_EkGeneratorsSub :
      nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> MoC.coq_VG **)

  let coq_EkGeneratorsSub j cBar a =
    vbuild j (fun i _ ->
      let cBarSub = vsub j cBar (sub j (add (S O) i)) (add (S O) i) in
      let asub = vsub j a O (add (S O) i) in
      MoC.coq_VG_prod (add (S O) i)
        (vmap2 (fun x y -> MoC.coq_VG_prod n (MoC.coq_VG_Pexp n x y)) (add (S O) i)
          cBarSub asub))

  (** val coq_EkGeneratorsSubAlt :
      nat -> Ciphertext.coq_G t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
      MoC.coq_VG **)

  let coq_EkGeneratorsSubAlt j cBar a x =
    vbuild j (fun i _ ->
      MoC.coq_VG_prod (add (S O) i)
        (vmap (fun y -> MoC.coq_VG_prod n (MoC.coq_VG_Pexp n (vnth j cBar i) y))
          (add (S O) i)
          (vmap2 (Mo.Coq_mat.coq_VF_scale n) (add (S O) i)
            (vsub j a O (add (S O) i))
            (vsub j x (sub j (add (S O) i)) (add (S O) i)))))

  (** val coq_EkGenerators :
      Coq_enc.coq_PK -> nat -> Coq_enc.coq_M -> Ciphertext.coq_G t0 t0 ->
      Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0 -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF -> Ciphertext.coq_G t0 **)

  let coq_EkGenerators pk l g0 cBar a0 tau b x =
    let e1 = vmap2 (fun x0 y -> Coq_enc.enc pk (VS3.op g0 x0) y) (add l l) b tau in
    let epre = coq_EkGeneratorsSub l cBar (vremove_last l a0) in
    let epost = rev l (coq_EkGeneratorsSub l (rev l cBar) (rev l (tl l a0))) in
    let e2 = vapp l l epre epost in
    vmap2 Ciphertext.coq_Gdot (add l l) e1 (MoC.coq_VG_Pexp (add l l) e2 x)

  (** val coq_EkGeneratorsSubRawM :
      nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF **)

  let coq_EkGeneratorsSubRawM j ca a =
    vbuild j (fun i _ ->
      let cBarSub = vsub j ca (sub j (add (S O) i)) (add (S O) i) in
      let asub = vsub j a O (add (S O) i) in
      Mo.Coq_mat.coq_VF_sum (add (S O) i)
        (vmap2 (fun x y -> Mo.Coq_mat.coq_VF_sum n (Mo.Coq_mat.coq_VF_mult n x y))
          (add (S O) i) cBarSub asub))

  (** val coq_EkGeneratorsSubRawR :
      nat -> Ring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0 **)

  let coq_EkGeneratorsSubRawR j ctau a =
    vbuild j (fun i _ ->
      let cBarSub = vsub j ctau (sub j (add (S O) i)) (add (S O) i) in
      let asub = vsub j a O (add (S O) i) in
      MoR.coq_VF_sum (add (S O) i)
        (vmap2 (fun x y -> MoR.coq_VF_sum n (vmap2 MVS.op3 n x y)) (add (S O) i)
          cBarSub asub))

  (** val coq_EkGeneratorsRawM :
      nat -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF t0 -> Mo.Coq_mat.coq_VF ->
      Mo.Coq_mat.coq_VF **)

  let coq_EkGeneratorsRawM l ca a0 b =
    let messagePre = coq_EkGeneratorsSubRawM l ca (vremove_last l a0) in
    let messagePost = rev l (coq_EkGeneratorsSubRawM l (rev l ca) (rev l (tl l a0)))
    in
    Mo.Coq_mat.coq_VF_add (add l l) b (vapp l l messagePre messagePost)

  (** val coq_EkGeneratorsRawR :
      nat -> Ring.coq_F t0 t0 -> Mo.Coq_mat.coq_VF t0 -> Ring.coq_F t0 -> MoR.coq_VF **)

  let coq_EkGeneratorsRawR l ctau a0 tau =
    let randomnessPre = coq_EkGeneratorsSubRawR l ctau (vremove_last l a0) in
    let randomnessPost =
      rev l (coq_EkGeneratorsSubRawR l (rev l ctau) (rev l (tl l a0)))
    in
    MoR.coq_VF_add (add l l) tau (vapp l l randomnessPre randomnessPost)

  (** val makeSVectors : nat -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF t0 **)

  let makeSVectors l s =
    vbuild l (fun i _ -> vsub (add l l) s (sub (sub l i) (S O)) (add (S O) l))
 end

module BGZeroArgIns =
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
 struct
  (** val n : nat **)

  let n =
    S (S (S Hack.coq_N))

  (** val m : nat **)

  let m =
    S (S M.coq_N)

  module ALR = RingAddationalLemmas(Ring)

  (** val coq_BM :
      Field.coq_F -> Coq_support.Mo.Coq_mat.coq_VF -> Coq_support.Mo.Coq_mat.coq_VF
      -> Field.coq_F **)

  let coq_BM y a b =
    let y0 = Coq_support.Mo.coq_VandermondeColGen n y (S O) in
    Coq_support.Mo.Coq_mat.coq_VF_sum n
      (vmap2 Field.coq_Fmul n (vmap2 Field.coq_Fmul n a b) y0)

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

  (** val coq_Rel : coq_St -> coq_W -> bool **)

  let coq_Rel s w =
    let (p0, cB) = s in
    let (p1, cA) = p0 in
    let (p2, y) = p1 in
    let (h, hs) = p2 in
    let (p3, s0) = w in
    let (p4, b) = p3 in
    let (a, r) = p4 in
    (&&)
      ((&&)
        (Coq_support.EPC.MoM.coq_VG_eq m cA (Coq_support.EPC.comEPC n m h hs a r))
        (Coq_support.EPC.MoM.coq_VG_eq m cB (Coq_support.EPC.comEPC n m h hs b s0)))
      (Field.coq_Fbool_eq Field.coq_Fzero
        (Coq_support.Mo.Coq_mat.coq_VF_sum m (vmap2 (coq_BM y) m a b)))

  (** val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C **)

  let coq_P0 stat rand wit =
    let (p0, _) = stat in
    let (p1, _) = p0 in
    let (p2, y) = p1 in
    let (h, hs) = p2 in
    let a0 = fst (fst (fst (fst rand))) in
    let bm = snd (fst (fst (fst rand))) in
    let r0 = snd (fst (fst rand)) in
    let sm = snd (fst rand) in
    let t1 = snd rand in
    let a = fst (fst (fst wit)) in
    let b = snd (fst wit) in
    let cA0 = Coq_support.EPC.coq_EPC n h hs a0 r0 in
    let cBM = Coq_support.EPC.coq_EPC n h hs bm sm in
    let mat =
      Coq_support.Mo.Coq_mat.FMatrix.mat_build (S m) (S m) (fun i j _ _ ->
        coq_BM y (vnth (S m) (Cons (a0, m, a)) i) (vnth (S m) (vadd m b bm) j))
    in
    let cD =
      Coq_support.PC.comPC (add (S m) m) h (hd (S (S Hack.coq_N)) hs)
        (Coq_support.coq_ProdOfDiagonalsF m mat)
        (vapp (S m) (S (S M.coq_N)) (fst t1) (Cons (Field.coq_Fzero, (S M.coq_N),
          (snd t1))))
    in
    (stat, ((cA0, cBM), cD))

  (** val coq_V0 :
      (coq_St * coq_C) -> Field.coq_F -> (coq_St * coq_C) * Field.coq_F **)

  let coq_V0 ggtoxgtor c =
    (ggtoxgtor, c)

  (** val coq_P1 :
      ((coq_St * coq_C) * Field.coq_F) -> coq_R -> coq_W ->
      ((coq_St * coq_C) * Field.coq_F) * coq_T **)

  let coq_P1 ggtoxgtorc r w =
    let c = snd ggtoxgtorc in
    let a0 = fst (fst (fst (fst r))) in
    let bm = snd (fst (fst (fst r))) in
    let r0 = snd (fst (fst r)) in
    let sm = snd (fst r) in
    let t1 = snd r in
    let a = fst (fst (fst w)) in
    let r1 = snd (fst (fst w)) in
    let b = snd (fst w) in
    let s = snd w in
    let xBar = Coq_support.Mo.coq_VandermondeCol (S m) c in
    let xK = Coq_support.Mo.coq_VandermondeCol (add (S m) m) c in
    let aT =
      vfold_left (Coq_support.Mo.Coq_mat.coq_VF_add n) (S m)
        (Coq_support.Mo.Coq_mat.coq_VF_zero n)
        (vmap2 (Coq_support.Mo.Coq_mat.coq_VF_scale n) (S m) (Cons (a0, m, a)) xBar)
    in
    let rT =
      Coq_support.Mo.Coq_mat.coq_VF_sum (S m)
        (Coq_support.Mo.Coq_mat.coq_VF_mult (S m) xBar (Cons (r0, m, r1)))
    in
    let bT =
      vfold_left (Coq_support.Mo.Coq_mat.coq_VF_add n) (S m)
        (Coq_support.Mo.Coq_mat.coq_VF_zero n)
        (vmap2 (Coq_support.Mo.Coq_mat.coq_VF_scale n) (S m) (vadd m b bm)
          (rev (S m) xBar))
    in
    let sT =
      Coq_support.Mo.Coq_mat.coq_VF_sum (S m)
        (Coq_support.Mo.Coq_mat.coq_VF_mult (S m) (rev (S m) xBar) (vadd m s sm))
    in
    let tT =
      Coq_support.Mo.Coq_mat.coq_VF_sum (add (S m) m)
        (Coq_support.Mo.Coq_mat.coq_VF_mult (add (S m) m) xK
          (vapp (S m) (S (S M.coq_N)) (fst t1) (Cons (Field.coq_Fzero, (S M.coq_N),
            (snd t1)))))
    in
    (ggtoxgtorc, ((((aT, rT), bT), sT), tT))

  (** val coq_V1 : (((coq_St * coq_C) * Field.coq_F) * coq_T) -> bool **)

  let coq_V1 transcript =
    let stat = fst (fst (fst transcript)) in
    let comm = snd (fst (fst transcript)) in
    let chal = snd (fst transcript) in
    let resp = snd transcript in
    let (p0, cB) = stat in
    let (p1, cA) = p0 in
    let (p2, y) = p1 in
    let (h, hs) = p2 in
    let cA0 = fst (fst comm) in
    let cBM = snd (fst comm) in
    let cD = snd comm in
    let xBar = Coq_support.Mo.coq_VandermondeCol (S m) chal in
    let xK = Coq_support.Mo.coq_VandermondeCol (add (S m) m) chal in
    let aT = fst (fst (fst (fst resp))) in
    let rT = snd (fst (fst (fst resp))) in
    let bT = snd (fst (fst resp)) in
    let sT = snd (fst resp) in
    let tT = snd resp in
    let eq1 =
      Commitment.coq_Gbool_eq
        (Coq_support.EPC.MoM.coq_VG_prod (S m)
          (Coq_support.EPC.MoM.coq_VG_Pexp (S m) (Cons (cA0, m, cA)) xBar))
        (Coq_support.EPC.coq_EPC n h hs aT rT)
    in
    let eq2 =
      Commitment.coq_Gbool_eq
        (Coq_support.EPC.MoM.coq_VG_prod (S m)
          (Coq_support.EPC.MoM.coq_VG_Pexp (S m) (vadd m cB cBM) (rev (S m) xBar)))
        (Coq_support.EPC.coq_EPC n h hs bT sT)
    in
    let eq3 =
      Commitment.coq_Gbool_eq
        (Coq_support.EPC.MoM.coq_VG_prod (add (S m) m)
          (Coq_support.EPC.MoM.coq_VG_Pexp (add (S m) m) cD xK))
        (Coq_support.PC.coq_PC h (vnth n hs O) (coq_BM y aT bT) tT)
    in
    let eq4 =
      Commitment.coq_Gbool_eq (vnth (add (S m) m) cD (S Coq_support.m))
        (Coq_support.PC.coq_PC h (vnth n hs O) Field.coq_Fzero Field.coq_Fzero)
    in
    (&&) ((&&) ((&&) eq1 eq2) eq3) eq4

  (** val simMap : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_R -> coq_TE **)

  let simMap s w c x r =
    let (p0, _) = s in
    let (p1, _) = p0 in
    let (_, y) = p1 in
    let a0 = fst (fst (fst (fst r))) in
    let bm = snd (fst (fst (fst r))) in
    let r0 = snd (fst (fst r)) in
    let sm = snd (fst r) in
    let t1 = snd r in
    let a = fst (fst (fst w)) in
    let r1 = snd (fst (fst w)) in
    let b = snd (fst w) in
    let s0 = snd w in
    let xBar = Coq_support.Mo.coq_VandermondeCol (S m) c in
    let xK = Coq_support.Mo.coq_VandermondeCol (add (S m) m) c in
    let aT =
      vfold_left (Coq_support.Mo.Coq_mat.coq_VF_add n) (S m)
        (Coq_support.Mo.Coq_mat.coq_VF_zero n)
        (vmap2 (Coq_support.Mo.Coq_mat.coq_VF_scale n) (S m) (Cons (a0, m, a)) xBar)
    in
    let rT =
      Coq_support.Mo.Coq_mat.coq_VF_sum (S m)
        (Coq_support.Mo.Coq_mat.coq_VF_mult (S m) xBar (Cons (r0, m, r1)))
    in
    let bT =
      vfold_left (Coq_support.Mo.Coq_mat.coq_VF_add n) (S m)
        (Coq_support.Mo.Coq_mat.coq_VF_zero n)
        (vmap2 (Coq_support.Mo.Coq_mat.coq_VF_scale n) (S m) (vadd m b bm)
          (rev (S m) xBar))
    in
    let sT =
      Coq_support.Mo.Coq_mat.coq_VF_sum (S m)
        (Coq_support.Mo.Coq_mat.coq_VF_mult (S m) (rev (S m) xBar) (vadd m s0 sm))
    in
    let tT =
      Coq_support.Mo.Coq_mat.coq_VF_sum (add (S m) m)
        (Coq_support.Mo.Coq_mat.coq_VF_mult (add (S m) m) xK
          (vapp (S m) (S (S M.coq_N)) (fst t1) (Cons (Field.coq_Fzero, (S M.coq_N),
            (snd t1)))))
    in
    let mat =
      Coq_support.Mo.Coq_mat.FMatrix.mat_build (S m) (S m) (fun i j _ _ ->
        coq_BM y (vnth (S m) (Cons (a0, m, a)) i) (vnth (S m) (vadd m b bm) j))
    in
    let cDFirst =
      Coq_support.Mo.Coq_mat.coq_VF_add m (tl m (fst t1))
        (Coq_support.Mo.Coq_mat.coq_VF_scale m
          (tl m (fst (vbreak (S m) m (Coq_support.coq_ProdOfDiagonalsF m mat))))
          (hd (S (S Hack.coq_N)) x))
    in
    let cDSecond =
      Coq_support.Mo.Coq_mat.coq_VF_add (S M.coq_N) (snd t1)
        (Coq_support.Mo.Coq_mat.coq_VF_scale (S M.coq_N)
          (tl (S M.coq_N)
            (snd (vbreak (S m) m (Coq_support.coq_ProdOfDiagonalsF m mat))))
          (hd (S (S Hack.coq_N)) x))
    in
    (((((aT, rT), bT), sT), tT), (cDFirst, cDSecond))

  (** val simMapInv : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_TE -> coq_R **)

  let simMapInv s w c x t1 =
    let (p0, _) = s in
    let (p1, _) = p0 in
    let (_, y) = p1 in
    let aT = fst (fst (fst (fst (fst t1)))) in
    let rT = snd (fst (fst (fst (fst t1)))) in
    let bT = snd (fst (fst (fst t1))) in
    let sT = snd (fst (fst t1)) in
    let tT = snd (fst t1) in
    let cDFirst = fst (snd t1) in
    let cDSecond = snd (snd t1) in
    let a = fst (fst (fst w)) in
    let r = snd (fst (fst w)) in
    let b = snd (fst w) in
    let s0 = snd w in
    let xBar = Coq_support.Mo.coq_VandermondeCol (S m) c in
    let xK = Coq_support.Mo.coq_VandermondeCol (add (S m) m) c in
    let a0 =
      Coq_support.Mo.Coq_mat.coq_VF_sub n aT
        (vfold_left (Coq_support.Mo.Coq_mat.coq_VF_add n) m
          (Coq_support.Mo.Coq_mat.coq_VF_zero n)
          (vmap2 (Coq_support.Mo.Coq_mat.coq_VF_scale n) m a (tl m xBar)))
    in
    let r0 =
      Field.coq_Fadd rT
        (Field.coq_Finv
          (Coq_support.Mo.Coq_mat.coq_VF_sum m
            (Coq_support.Mo.Coq_mat.coq_VF_mult m (tl m xBar) r)))
    in
    let b0 =
      Coq_support.Mo.Coq_mat.coq_VF_sub n bT
        (vfold_left (Coq_support.Mo.Coq_mat.coq_VF_add n) m
          (Coq_support.Mo.Coq_mat.coq_VF_zero n)
          (vmap2 (Coq_support.Mo.Coq_mat.coq_VF_scale n) m b (rev m (tl m xBar))))
    in
    let s1 =
      Field.coq_Fadd sT
        (Field.coq_Finv
          (Coq_support.Mo.Coq_mat.coq_VF_sum m
            (Coq_support.Mo.Coq_mat.coq_VF_mult m (rev m (tl m xBar)) s0)))
    in
    let mat =
      Coq_support.Mo.Coq_mat.FMatrix.mat_build (S m) (S m) (fun i j _ _ ->
        coq_BM y (vnth (S m) (Cons (a0, m, a)) i) (vnth (S m) (vadd m b b0) j))
    in
    let t2 =
      Coq_support.Mo.Coq_mat.coq_VF_sub m cDFirst
        (Coq_support.Mo.Coq_mat.coq_VF_scale m
          (tl m (fst (vbreak (S m) m (Coq_support.coq_ProdOfDiagonalsF m mat))))
          (hd (S (S Hack.coq_N)) x))
    in
    let t3 =
      Coq_support.Mo.Coq_mat.coq_VF_sub (S M.coq_N) cDSecond
        (Coq_support.Mo.Coq_mat.coq_VF_scale (S M.coq_N)
          (tl (S M.coq_N)
            (snd (vbreak (S m) m (Coq_support.coq_ProdOfDiagonalsF m mat))))
          (hd (S (S Hack.coq_N)) x))
    in
    let tau =
      Field.coq_Fadd tT
        (Field.coq_Finv
          (Coq_support.Mo.Coq_mat.coq_VF_sum (S
            (let rec add5 n0 m0 =
               match n0 with
               | O -> m0
               | S p2 -> S (add5 p2 m0)
             in add5 (S M.coq_N) m))
            (Coq_support.Mo.Coq_mat.coq_VF_mult (S
              (let rec add5 n0 m0 =
                 match n0 with
                 | O -> m0
                 | S p2 -> S (add5 p2 m0)
               in add5 (S M.coq_N) m))
              (tl (S
                (let rec add5 n0 m0 =
                   match n0 with
                   | O -> m0
                   | S p2 -> S (add5 p2 m0)
                 in add5 (S M.coq_N) m)) xK)
              (vapp m (S (S M.coq_N)) t2 (Cons (Field.coq_Fzero, (S M.coq_N), t3))))))
    in
    ((((a0, b0), r0), s1), ((Cons (tau, m, t2)), t3))

  (** val simulator :
      coq_St -> coq_TE -> Field.coq_F -> ((coq_St * coq_C) * Field.coq_F) * coq_T **)

  let simulator s z0 e =
    let (p0, cB) = s in
    let (p1, cA) = p0 in
    let (p2, y) = p1 in
    let (h, hs) = p2 in
    let xBar = Coq_support.Mo.coq_VandermondeCol (S m) e in
    let xK = Coq_support.Mo.coq_VandermondeCol (add (S m) m) e in
    let aT = fst (fst (fst (fst (fst z0)))) in
    let rT = snd (fst (fst (fst (fst z0)))) in
    let bT = snd (fst (fst (fst z0))) in
    let sT = snd (fst (fst z0)) in
    let tT = snd (fst z0) in
    let cDFirst = vmap (fun x -> VS2.op h x) m (fst (snd z0)) in
    let cDSecond = vmap (fun x -> VS2.op h x) (S M.coq_N) (snd (snd z0)) in
    let cA0 =
      Commitment.coq_Gdot (Coq_support.EPC.coq_EPC n h hs aT rT)
        (Commitment.coq_Ginv
          (Coq_support.EPC.MoM.coq_VG_prod m
            (Coq_support.EPC.MoM.coq_VG_Pexp m cA (tl m xBar))))
    in
    let cBM =
      Commitment.coq_Gdot (Coq_support.EPC.coq_EPC n h hs bT sT)
        (Commitment.coq_Ginv
          (Coq_support.EPC.MoM.coq_VG_prod m
            (Coq_support.EPC.MoM.coq_VG_Pexp m cB (vremove_last m (rev (S m) xBar)))))
    in
    let cDM = Coq_support.PC.coq_PC h (vnth n hs O) Field.coq_Fzero Field.coq_Fzero
    in
    let cD0 =
      Commitment.coq_Gdot
        (Coq_support.PC.coq_PC h (vnth n hs O) (coq_BM y aT bT) tT)
        (Commitment.coq_Ginv
          (Coq_support.EPC.MoM.coq_VG_prod (add m (S (S M.coq_N)))
            (Coq_support.EPC.MoM.coq_VG_Pexp (add m (S (S M.coq_N)))
              (vapp m (S (S M.coq_N)) cDFirst (Cons (cDM, (S M.coq_N), cDSecond)))
              (tl (S
                (let rec add5 n0 m0 =
                   match n0 with
                   | O -> m0
                   | S p3 -> S (add5 p3 m0)
                 in add5 (S M.coq_N) m)) xK))))
    in
    let cD =
      vapp (S m) (S (S M.coq_N)) (Cons (cD0, m, cDFirst)) (Cons (cDM, (S M.coq_N),
        cDSecond))
    in
    (((s, ((cA0, cBM), cD)), e), (fst z0))

  (** val extractor : coq_T t0 -> Field.coq_F t0 -> coq_W **)

  let extractor s c =
    let sM = fst (vbreak (S m) m s) in
    let cM = fst (vbreak (S m) m c) in
    let aT =
      Coq_support.Mo.Coq_mat.FMatrix.mat_transpose (S m) n
        (vmap (fun s1 -> fst (fst (fst (fst s1)))) (S m) sM)
    in
    let rT = vmap (fun s1 -> snd (fst (fst (fst s1)))) (S m) sM in
    let bT =
      Coq_support.Mo.Coq_mat.FMatrix.mat_transpose (S m) n
        (vmap (fun s1 -> snd (fst (fst s1))) (S m) sM)
    in
    let sT = vmap (fun s1 -> snd (fst s1)) (S m) sM in
    let yM1 =
      Coq_support.Mo.Coq_mat.FMatrix.mat_transpose (S m) (S m)
        (Coq_support.Mo.coq_VandermondeInv (S m) cM)
    in
    let yM2 =
      Coq_support.Mo.Coq_mat.FMatrix.mat_transpose (S m) (S m)
        (rev (S m) (Coq_support.Mo.coq_VandermondeInv (S m) cM))
    in
    ((((tl m
         (Coq_support.Mo.Coq_mat.FMatrix.mat_transpose n (S m)
           (Coq_support.Mo.Coq_mat.FMatrix.mat_mult n (S m) (S m) aT yM1))),
    (tl m
      (hd O
        (Coq_support.Mo.Coq_mat.FMatrix.mat_mult (S O) (S m) (S m) (Cons (rT, O,
          Nil)) yM1)))),
    (vremove_last m
      (Coq_support.Mo.Coq_mat.FMatrix.mat_transpose n (S m)
        (Coq_support.Mo.Coq_mat.FMatrix.mat_mult n (S m) (S m) bT yM2)))),
    (vremove_last m
      (hd O
        (Coq_support.Mo.Coq_mat.FMatrix.mat_mult (S O) (S m) (S m) (Cons (sT, O,
          Nil)) yM2))))

  (** val coq_M : nat **)

  let coq_M =
    Nat.add (S m) m

  (** val allDifferent : Chal.coq_G t0 -> bool **)

  let allDifferent e =
    pairwisePredicate coq_M Chal.coq_Gdisjoint e
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

module SigmaPlus5CompIns =
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
 struct
  type coq_E0 = Coq_exp.coq_E

  type coq_E1 = E.coq_G

  type coq_St = Coq_exp.coq_St

  type coq_W = Coq_exp.coq_W

  (** val coq_Rel : coq_St -> coq_W -> bool **)

  let coq_Rel =
    Coq_exp.coq_Rel

  type coq_C0 = Coq_exp.coq_C

  type coq_C1 = Coq_exp.coq_C1 * Coq_sig.coq_C

  type coq_R0 = Coq_exp.coq_R

  type coq_R1 = Coq_exp.coq_R1 * Coq_sig.coq_R

  (** val add0 : coq_E0 -> coq_E0 -> coq_E0 **)

  let add0 =
    Coq_exp.add

  (** val zero0 : coq_E0 **)

  let zero0 =
    Coq_exp.zero

  (** val inv0 : coq_E0 -> coq_E0 **)

  let inv0 =
    Coq_exp.inv

  (** val bool_eq0 : coq_E0 -> coq_E0 -> bool **)

  let bool_eq0 =
    Coq_exp.bool_eq

  (** val disjoint0 : coq_E0 -> coq_E0 -> bool **)

  let disjoint0 =
    Coq_exp.disjoint

  (** val add1 : coq_E1 -> coq_E1 -> coq_E1 **)

  let add1 =
    E.coq_Gdot

  (** val zero1 : coq_E1 **)

  let zero1 =
    E.coq_Gone

  (** val inv1 : coq_E1 -> coq_E1 **)

  let inv1 =
    E.coq_Ginv

  (** val bool_eq1 : coq_E1 -> coq_E1 -> bool **)

  let bool_eq1 =
    E.coq_Gbool_eq

  (** val disjoint1 : coq_E1 -> coq_E1 -> bool **)

  let disjoint1 =
    E.coq_Gdisjoint

  type coq_T = Coq_sig.coq_T

  (** val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0 **)

  let coq_P0 =
    Coq_exp.coq_P0

  (** val coq_P1 :
      ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
      ((coq_St * coq_C0) * coq_E0) * coq_C1 **)

  let coq_P1 tran r w =
    (tran, ((snd (Coq_exp.coq_P1 tran (fst (snd r)) w)),
      (snd
        (Coq_sig.coq_P0
          (Coq_exp.coq_ToSt (tran, (snd (Coq_exp.coq_P1 tran (fst (snd r)) w))))
          (snd (snd r)) (Coq_exp.coq_ToWit tran (fst r) (fst (snd r)) w)))))

  (** val coq_P2 :
      ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) ->
      coq_W -> ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T **)

  let coq_P2 tran r w =
    (tran,
      (snd
        (Coq_sig.coq_P1
          (((Coq_exp.coq_ToSt ((fst (fst tran)), (fst (snd (fst tran))))),
          (snd (snd (fst tran)))), (snd tran)) (snd (snd r))
          (Coq_exp.coq_ToWit (fst (fst tran)) (fst r) (fst (snd r)) w))))

  (** val coq_V2 :
      (((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T) -> bool **)

  let coq_V2 tran =
    Coq_sig.coq_V1
      ((((Coq_exp.coq_ToSt ((fst (fst (fst tran))), (fst (snd (fst (fst tran)))))),
      (snd (snd (fst (fst tran))))), (snd (fst tran))), (snd tran))

  type coq_TE0 = Coq_exp.coq_TE

  type coq_TE1 = Coq_sig.coq_TE

  type coq_X = Coq_exp.coq_X

  (** val simulator :
      coq_St -> (coq_TE0 * coq_TE1) -> (coq_E0 * coq_E1) ->
      ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T **)

  let simulator st t1 e =
    (((((st, (fst (Coq_exp.simulator st (fst t1) (fst e)))), (fst e)),
      ((snd (Coq_exp.simulator st (fst t1) (fst e))),
      (snd
        (fst
          (fst
            (Coq_sig.simulator
              (Coq_exp.coq_ToSt (((st,
                (fst (Coq_exp.simulator st (fst t1) (fst e)))), (fst e)),
                (snd (Coq_exp.simulator st (fst t1) (fst e))))) (snd t1) (snd e))))))),
      (snd e)),
      (snd
        (Coq_sig.simulator
          (Coq_exp.coq_ToSt (((st, (fst (Coq_exp.simulator st (fst t1) (fst e)))),
            (fst e)), (snd (Coq_exp.simulator st (fst t1) (fst e))))) (snd t1)
          (snd e))))

  (** val simMap :
      coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_R0 * coq_R1) ->
      coq_TE0 * coq_TE1 **)

  let simMap st w e x r =
    ((Coq_exp.simMap st w (fst e) x ((fst r), (fst (snd r)))),
      (Coq_sig.simMap
        (Coq_exp.coq_ToSt
          (Coq_exp.coq_P1 ((Coq_exp.coq_P0 st (fst r) w), (fst e)) (fst (snd r)) w))
        (Coq_exp.coq_ToWit ((Coq_exp.coq_P0 st (fst r) w), (fst e)) (fst r)
          (fst (snd r)) w) (snd e) (Coq_exp.sigXcomp st x) (snd (snd r))))

  (** val simMapInv :
      coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_TE0 * coq_TE1) ->
      coq_R0 * coq_R1 **)

  let simMapInv st w e x t1 =
    ((fst (Coq_exp.simMapInv st w (fst e) x (fst t1))),
      ((snd (Coq_exp.simMapInv st w (fst e) x (fst t1))),
      (Coq_sig.simMapInv
        (Coq_exp.coq_ToSt (((st, (fst (Coq_exp.simulator st (fst t1) (fst e)))),
          (fst e)), (snd (Coq_exp.simulator st (fst t1) (fst e)))))
        (Coq_exp.coq_ToWit ((st, (fst (Coq_exp.simulator st (fst t1) (fst e)))),
          (fst e)) (fst (Coq_exp.simMapInv st w (fst e) x (fst t1)))
          (snd (Coq_exp.simMapInv st w (fst e) x (fst t1))) w) (snd e)
        (Coq_exp.sigXcomp st x) (snd t1))))

  (** val coq_M0 : nat **)

  let coq_M0 =
    Coq_exp.coq_M

  (** val coq_M1 : nat **)

  let coq_M1 =
    Coq_sig.coq_M

  (** val extractor : coq_T t0 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_W **)

  let extractor t1 e =
    Coq_exp.extractor (vmap2 (fun a b -> Coq_sig.extractor a (snd b)) coq_M0 t1 e)
      (vmap fst coq_M0 e)

  (** val allValid :
      coq_St -> coq_C0 -> coq_C1 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_T t0 t0 -> bool **)

  let allValid s c0 c1 e t1 =
    bVforall3 coq_M0 (fun c e0 t2 ->
      bVforall2 (fun e1 t3 -> coq_V2 (((((s, c0), (fst e0)), c), e1), t3)) coq_M1
        (snd e0) t2) c1 e t1
 end

module SigmaPlusTo5simTofullIns =
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
 struct
  type coq_E = Coq_sigSim.coq_E

  type coq_St = Coq_sigSim.coq_St

  type coq_W = Coq_sigSim.coq_W

  (** val coq_Rel : Coq_sigSim.coq_St -> Coq_sigSim.coq_W -> bool **)

  let coq_Rel =
    Coq_sigSim.coq_Rel

  type coq_C = Coq_sigSim.coq_C

  type coq_R = Coq_sigSim.coq_R

  (** val add : Coq_sigSim.coq_E -> Coq_sigSim.coq_E -> Coq_sigSim.coq_E **)

  let add =
    Coq_sigSim.add

  (** val zero : coq_E **)

  let zero =
    Coq_sigSim.zero

  (** val inv : coq_E -> coq_E **)

  let inv =
    Coq_sigSim.inv

  (** val bool_eq : coq_E -> coq_E -> bool **)

  let bool_eq =
    Coq_sigSim.bool_eq

  (** val disjoint : coq_E -> coq_E -> bool **)

  let disjoint =
    Coq_sigSim.disjoint

  (** val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C **)

  let coq_P0 =
    Coq_sigSim.coq_P0

  type coq_C1 = unit

  type coq_R1 = unit

  (** val coq_P1 :
      ((coq_St * coq_C) * coq_E) -> coq_R1 -> coq_W ->
      ((coq_St * coq_C) * coq_E) * coq_C1 **)

  let coq_P1 sce _ _ =
    (sce, ())

  (** val coq_ToSt : (((coq_St * coq_C) * coq_E) * coq_C1) -> Coq_sig.coq_St **)

  let coq_ToSt s =
    Coq_sigSim.coq_ToSt (fst s)

  (** val coq_ToWit :
      ((coq_St * coq_C) * coq_E) -> coq_R -> coq_R1 -> coq_W -> Coq_sig.coq_W **)

  let coq_ToWit s r _ w =
    Coq_sigSim.coq_ToWit s r w

  type coq_TE = Coq_sigSim.coq_TE

  (** val coq_M : nat **)

  let coq_M =
    S O

  (** val extractor : Coq_sig.coq_W t0 -> coq_E t0 -> coq_W **)

  let extractor w e =
    Coq_sigSim.extractor (hd O w) (hd O e)

  type coq_X = Coq_sigSim.coq_X

  (** val simulator : coq_St -> coq_TE -> coq_E -> coq_C * coq_C1 **)

  let simulator s t1 e =
    ((Coq_sigSim.simulator s t1 e), ())

  (** val simMap :
      coq_St -> coq_W -> coq_E -> coq_X -> (coq_R * coq_R1) -> coq_TE **)

  let simMap s w e x r =
    Coq_sigSim.simMap s w e x (fst r)

  (** val simMapInv :
      coq_St -> coq_W -> coq_E -> coq_X -> coq_TE -> coq_R * coq_R1 **)

  let simMapInv s w e x t1 =
    ((Coq_sigSim.simMapInv s w e x t1), ())

  (** val sigXcomp : coq_St -> coq_X -> Coq_sig.coq_X **)

  let sigXcomp =
    Coq_sigSim.sigXcomp
 end

module SigmaPlus5to5CompIns =
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
 struct
  type coq_E0 = Coq_sig5.coq_E0 * E.coq_G

  type coq_E1 = Coq_sig5.coq_E1

  type coq_St = Coq_exp.coq_St

  type coq_W = Coq_exp.coq_W

  (** val coq_Rel : coq_St -> coq_W -> bool **)

  let coq_Rel =
    Coq_exp.coq_Rel

  type coq_C0 = (Coq_exp.coq_C * Coq_sig5.coq_C0) * Coq_sig.coq_C

  type coq_C1 = Coq_sig5.coq_C1

  type coq_R0 = (Coq_exp.coq_R * Coq_sig5.coq_R0) * Coq_sig.coq_R

  type coq_R1 = Coq_sig5.coq_R1

  (** val add0 : coq_E0 -> coq_E0 -> coq_E0 **)

  let add0 a b =
    ((Coq_sig5.add0 (fst a) (fst b)), (E.coq_Gdot (snd a) (snd b)))

  (** val zero0 : coq_E0 **)

  let zero0 =
    (Coq_sig5.zero0, E.coq_Gone)

  (** val inv0 : coq_E0 -> coq_E0 **)

  let inv0 a =
    ((Coq_sig5.inv0 (fst a)), (E.coq_Ginv (snd a)))

  (** val bool_eq0 : coq_E0 -> coq_E0 -> bool **)

  let bool_eq0 a b =
    (&&) (Coq_sig5.bool_eq0 (fst a) (fst b)) (E.coq_Gbool_eq (snd a) (snd b))

  (** val disjoint0 : coq_E0 -> coq_E0 -> bool **)

  let disjoint0 a b =
    (&&) (Coq_sig5.disjoint0 (fst a) (fst b)) (E.coq_Gdisjoint (snd a) (snd b))

  (** val add1 : coq_E1 -> coq_E1 -> coq_E1 **)

  let add1 =
    Coq_sig5.add1

  (** val zero1 : coq_E1 **)

  let zero1 =
    Coq_sig5.zero1

  (** val inv1 : coq_E1 -> coq_E1 **)

  let inv1 =
    Coq_sig5.inv1

  (** val bool_eq1 : coq_E1 -> coq_E1 -> bool **)

  let bool_eq1 =
    Coq_sig5.bool_eq1

  (** val disjoint1 : coq_E1 -> coq_E1 -> bool **)

  let disjoint1 =
    Coq_sig5.disjoint1

  type coq_T = Coq_sig5.coq_T * Coq_sig.coq_T

  (** val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0 **)

  let coq_P0 s r w =
    let (p0, r'') = r in
    let (r0, r') = p0 in
    let c = Coq_exp.coq_P0 s r0 w in
    (s, (((snd c),
    (snd
      (Coq_sig5.coq_P0 (Coq_exp.coq_ToStSig5 c) r' (Coq_exp.coq_ToWitSig5 c r0 w)))),
    (snd (Coq_sig.coq_P0 (Coq_exp.coq_ToStSig c) r'' (Coq_exp.coq_ToWitSig c r0 w)))))

  (** val coq_P1 :
      ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
      ((coq_St * coq_C0) * coq_E0) * coq_C1 **)

  let coq_P1 tran r w =
    let (p0, e0) = tran in
    let (s, c0) = p0 in
    let (p1, _) = c0 in
    let (c, c') = p1 in
    let (e, _) = e0 in
    let (r0, r''') = r in
    let (p2, _) = r0 in
    let (r1, r') = p2 in
    (tran,
    (snd
      (Coq_sig5.coq_P1 (((Coq_exp.coq_ToStSig5 (s, c)), c'), e) (r', r''')
        (Coq_exp.coq_ToWitSig5 (s, c) r1 w))))

  (** val coq_P2 :
      ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) ->
      coq_W -> ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T **)

  let coq_P2 tran r w =
    let (p0, e1) = tran in
    let (p1, c1) = p0 in
    let (p2, e0) = p1 in
    let (s, c0) = p2 in
    let (p3, c'') = c0 in
    let (c, c') = p3 in
    let (e, e') = e0 in
    let (r0, r''') = r in
    let (p4, r'') = r0 in
    let (r1, r') = p4 in
    (tran,
    ((snd
       (Coq_sig5.coq_P2 (((((Coq_exp.coq_ToStSig5 (s, c)), c'), e), c1), e1) (r',
         r''') (Coq_exp.coq_ToWitSig5 (s, c) r1 w))),
    (snd
      (Coq_sig.coq_P1 (((Coq_exp.coq_ToStSig (s, c)), c''), e') r''
        (Coq_exp.coq_ToWitSig (s, c) r1 w)))))

  (** val coq_V2 :
      (((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T) -> bool **)

  let coq_V2 = function
  | (p0, t1) ->
    let (p1, e1) = p0 in
    let (p2, c1) = p1 in
    let (p3, e) = p2 in
    let (s, c0) = p3 in
    let (p4, c'') = c0 in
    let (c, c') = p4 in
    (&&)
      (Coq_sig5.coq_V2 ((((((Coq_exp.coq_ToStSig5 (s, c)), c'), (fst e)), c1), e1),
        (fst t1)))
      (Coq_sig.coq_V1 ((((Coq_exp.coq_ToStSig (s, c)), c''), (snd e)), (snd t1)))

  type coq_TE0 = (Coq_exp.coq_TE * Coq_sig5.coq_TE0) * Coq_sig.coq_TE

  type coq_TE1 = Coq_sig5.coq_TE1

  type coq_X = Coq_exp.coq_X

  (** val simulator :
      coq_St -> (coq_TE0 * coq_TE1) -> (coq_E0 * coq_E1) ->
      ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_T **)

  let simulator st t1 e =
    let (t2, t''') = t1 in
    let (p0, t'') = t2 in
    let (t3, t') = p0 in
    let (e0, e'') = e in
    let (e1, e') = e0 in
    let c = Coq_exp.simulator st t3 in
    let a = Coq_sig5.simulator (Coq_exp.coq_ToStSig5 (st, c)) (t', t''') (e1, e'') in
    let b = Coq_sig.simulator (Coq_exp.coq_ToStSig (st, c)) t'' e' in
    (((((st, ((c, (snd (fst (fst (fst (fst a)))))), (snd (fst (fst b))))), (e1,
    e')), (snd (fst (fst a)))), e''), ((snd a), (snd b)))

  (** val simMap :
      coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_R0 * coq_R1) ->
      coq_TE0 * coq_TE1 **)

  let simMap st w e x r =
    let (e0, e'') = e in
    let (e1, e') = e0 in
    let (r0, r''') = r in
    let (p0, r'') = r0 in
    let (r1, r') = p0 in
    ((((Coq_exp.simMap st w x r1),
    (fst
      (Coq_sig5.simMap (Coq_exp.coq_ToStSig5 (Coq_exp.coq_P0 st r1 w))
        (Coq_exp.coq_ToWitSig5 (Coq_exp.coq_P0 st r1 w) r1 w) (e1, e'')
        (Coq_exp.sig5Xcomp st x) (r', r''')))),
    (Coq_sig.simMap (Coq_exp.coq_ToStSig (Coq_exp.coq_P0 st r1 w))
      (Coq_exp.coq_ToWitSig (Coq_exp.coq_P0 st r1 w) r1 w) e'
      (Coq_exp.sigXcomp st x) r'')),
    (snd
      (Coq_sig5.simMap (Coq_exp.coq_ToStSig5 (Coq_exp.coq_P0 st r1 w))
        (Coq_exp.coq_ToWitSig5 (Coq_exp.coq_P0 st r1 w) r1 w) (e1, e'')
        (Coq_exp.sig5Xcomp st x) (r', r'''))))

  (** val simMapInv :
      coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_TE0 * coq_TE1) ->
      coq_R0 * coq_R1 **)

  let simMapInv st w e x t1 =
    let (e0, e'') = e in
    let (e1, e') = e0 in
    let (t2, t''') = t1 in
    let (p0, t'') = t2 in
    let (t3, t') = p0 in
    let r = Coq_exp.simMapInv st w x t3 in
    (((r,
    (fst
      (Coq_sig5.simMapInv (Coq_exp.coq_ToStSig5 (st, (Coq_exp.simulator st t3)))
        (Coq_exp.coq_ToWitSig5 (st, (Coq_exp.simulator st t3)) r w) (e1, e'')
        (Coq_exp.sig5Xcomp st x) (t', t''')))),
    (Coq_sig.simMapInv (Coq_exp.coq_ToStSig (Coq_exp.coq_P0 st r w))
      (Coq_exp.coq_ToWitSig (Coq_exp.coq_P0 st r w) r w) e' (Coq_exp.sigXcomp st x)
      t'')),
    (snd
      (Coq_sig5.simMapInv (Coq_exp.coq_ToStSig5 (Coq_exp.coq_P0 st r w))
        (Coq_exp.coq_ToWitSig5 (Coq_exp.coq_P0 st r w) r w) (e1, e'')
        (Coq_exp.sig5Xcomp st x) (t', t'''))))

  (** val coq_M0 : nat **)

  let coq_M0 =
    max Coq_sig5.coq_M0 Coq_sig.coq_M

  (** val coq_M1 : nat **)

  let coq_M1 =
    S (Nat.pred Coq_sig5.coq_M1)

  (** val extractor : coq_T t0 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_W **)

  let extractor t1 e =
    Coq_exp.extractor
      (Coq_sig5.extractor
        (vsub coq_M0
          (vmap (fun a ->
            vcast (S (Nat.pred Coq_sig5.coq_M1))
              (unzipLeft (S (Nat.pred Coq_sig5.coq_M1)) a) Coq_sig5.coq_M1) coq_M0
            t1) O Coq_sig5.coq_M0)
        (vsub coq_M0
          (vmap (fun a -> ((fst (fst a)),
            (vcast (S (Nat.pred Coq_sig5.coq_M1)) (snd a) Coq_sig5.coq_M1))) coq_M0
            e) O Coq_sig5.coq_M0))
      (Coq_sig.extractor
        (vsub coq_M0
          (vmap (fun a ->
            hd (Nat.pred Coq_sig5.coq_M1)
              (unzipRight (S (Nat.pred Coq_sig5.coq_M1)) a)) coq_M0 t1) O
          Coq_sig.coq_M)
        (vsub coq_M0 (unzipRight coq_M0 (unzipLeft coq_M0 e)) O Coq_sig.coq_M))

  (** val allValid :
      coq_St -> coq_C0 -> coq_C1 t0 -> (coq_E0 * coq_E1 t0) t0 -> coq_T t0 t0 -> bool **)

  let allValid s c0 c1 e t1 =
    bVforall3 coq_M0 (fun c e0 t2 ->
      bVforall2 (fun e1 t3 -> coq_V2 (((((s, c0), (fst e0)), c), e1), t3)) coq_M1
        (snd e0) t2) c1 e t1
 end

module BGHadProdIns =
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
 struct
  (** val n : nat **)

  let n =
    S (S (S Hack.coq_N))

  (** val m : nat **)

  let m =
    S (S M.coq_N)

  module ALR = RingAddationalLemmas(Ring)

  module G2 = GroupFromFieldIns(Field)

  type coq_E = G2.coq_G * Field.coq_F

  type coq_St =
    ((Commitment.coq_G * Coq_support.EPC.MoM.coq_VG) * Coq_support.EPC.MoM.coq_VG) * Commitment.coq_G

  type coq_W =
    ((Coq_support.Mo.Coq_mat.coq_VF
    t0 * Coq_support.Mo.Coq_mat.coq_VF) * Coq_support.Mo.Coq_mat.coq_VF) * Field.coq_F

  (** val coq_Rel : coq_St -> coq_W -> bool **)

  let coq_Rel s w =
    let h = fst (fst (fst s)) in
    let hs = snd (fst (fst s)) in
    let cA = snd (fst s) in
    let cB = snd s in
    let a = fst (fst (fst w)) in
    let r = snd (fst (fst w)) in
    let b = snd (fst w) in
    let s0 = snd w in
    (&&)
      ((&&)
        (Coq_support.EPC.MoM.coq_VG_eq m cA (Coq_support.EPC.comEPC n m h hs a r))
        (Commitment.coq_Gbool_eq cB (Coq_support.EPC.coq_EPC n h hs b s0)))
      (Coq_support.Mo.Coq_mat.coq_VF_beq n b
        (vfold_left (Coq_support.Mo.Coq_mat.coq_VF_mult n) m
          (Coq_support.Mo.Coq_mat.coq_VF_one n) a))

  type coq_C = Coq_support.EPC.MoM.coq_VG

  type coq_R = Coq_support.Mo.Coq_mat.coq_VF

  (** val add : coq_E -> coq_E -> G2.coq_G * Field.coq_F **)

  let add e1 e2 =
    ((G2.coq_Gdot (fst e1) (fst e2)), (Field.coq_Fadd (snd e1) (snd e2)))

  (** val zero : G2.coq_G * Field.coq_F **)

  let zero =
    (G2.coq_Gone, Field.coq_Fzero)

  (** val inv : coq_E -> G2.coq_G * Field.coq_F **)

  let inv e =
    ((G2.coq_Ginv (fst e)), (Field.coq_Finv (snd e)))

  (** val bool_eq : coq_E -> coq_E -> bool **)

  let bool_eq e1 e2 =
    (&&) (G2.coq_Gbool_eq (fst e1) (fst e2)) (Field.coq_Fbool_eq (snd e1) (snd e2))

  (** val disjoint : coq_E -> coq_E -> bool **)

  let disjoint e1 e2 =
    (&&) (negb (G2.coq_Gbool_eq (fst e1) (fst e2)))
      (negb (Field.coq_Fbool_eq (snd e1) (snd e2)))

  (** val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C **)

  let coq_P0 st r w =
    let h = fst (fst (fst st)) in
    let hs = snd (fst (fst st)) in
    let a = fst (fst (fst w)) in
    (st,
    (Coq_support.EPC.comEPC n M.coq_N h hs
      (vbuild M.coq_N (fun i _ ->
        vfold_left (Coq_support.Mo.Coq_mat.coq_VF_mult n) (S (S i))
          (Coq_support.Mo.Coq_mat.coq_VF_one n) (vsub m a O (S (S i))))) r))

  (** val coq_ToSt : ((coq_St * coq_C) * coq_E) -> Coq_sig.coq_St **)

  let coq_ToSt sce =
    let s = fst (fst sce) in
    let c = snd (fst sce) in
    let e = snd sce in
    let h = fst (fst (fst s)) in
    let hs = snd (fst (fst s)) in
    let cA = snd (fst s) in
    let cB = snd s in
    let x = fst e in
    let y = snd e in
    ((((h, hs), y),
    (vadd (S M.coq_N) (tl (S M.coq_N) cA)
      (Coq_support.EPC.coq_EPC n h hs
        (Coq_support.Mo.Coq_mat.coq_VF_neg n (Coq_support.Mo.Coq_mat.coq_VF_one n))
        Field.coq_Fzero))),
    (vadd (S M.coq_N)
      (Coq_support.EPC.MoM.coq_VG_Pexp (S M.coq_N) (Cons ((hd (S M.coq_N) cA),
        M.coq_N, c)) (tl (S M.coq_N) (Coq_support.Mo.coq_VandermondeCol m x)))
      (Coq_support.EPC.MoM.coq_VG_prod (S M.coq_N)
        (Coq_support.EPC.MoM.coq_VG_Pexp (S M.coq_N) (vadd M.coq_N c cB)
          (tl (S M.coq_N) (Coq_support.Mo.coq_VandermondeCol m x))))))

  (** val coq_ToWit :
      ((coq_St * coq_C) * coq_E) -> coq_R -> coq_W -> Coq_sig.coq_W **)

  let coq_ToWit sce r w =
    let x = fst (snd sce) in
    let a = fst (fst (fst w)) in
    let r' = snd (fst (fst w)) in
    let s = snd w in
    ((((vadd (S M.coq_N) (tl (S M.coq_N) a)
         (Coq_support.Mo.Coq_mat.coq_VF_neg n (Coq_support.Mo.Coq_mat.coq_VF_one n))),
    (vadd (S M.coq_N) (tl (S M.coq_N) r') Field.coq_Fzero)),
    (vadd (S M.coq_N) (Cons
      ((Coq_support.Mo.Coq_mat.coq_VF_scale n (hd (S M.coq_N) a) x), M.coq_N,
      (vmap2 (Coq_support.Mo.Coq_mat.coq_VF_scale n) M.coq_N
        (vbuild M.coq_N (fun i _ ->
          vfold_left (Coq_support.Mo.Coq_mat.coq_VF_mult n) (S (S i))
            (Coq_support.Mo.Coq_mat.coq_VF_one n) (vsub m a O (S (S i)))))
        (tl M.coq_N (tl (S M.coq_N) (Coq_support.Mo.coq_VandermondeCol m x))))))
      (vfold_left (Coq_support.Mo.Coq_mat.coq_VF_add n) (S M.coq_N)
        (Coq_support.Mo.Coq_mat.coq_VF_zero n)
        (vmap2 (Coq_support.Mo.Coq_mat.coq_VF_scale n) (S M.coq_N)
          (vbuild (S M.coq_N) (fun i _ ->
            vfold_left (Coq_support.Mo.Coq_mat.coq_VF_mult n) (S (S i))
              (Coq_support.Mo.Coq_mat.coq_VF_one n) (vsub m a O (S (S i)))))
          (tl (S M.coq_N) (Coq_support.Mo.coq_VandermondeCol m x)))))),
    (vadd (S M.coq_N) (Cons ((Field.coq_Fmul (hd (S M.coq_N) r') x), M.coq_N,
      (Coq_support.Mo.Coq_mat.coq_VF_mult M.coq_N r
        (tl M.coq_N (tl (S M.coq_N) (Coq_support.Mo.coq_VandermondeCol m x))))))
      (Coq_support.Mo.Coq_mat.coq_VF_sum (S M.coq_N)
        (Coq_support.Mo.Coq_mat.coq_VF_mult (S M.coq_N) (vadd M.coq_N r s)
          (tl (S M.coq_N) (Coq_support.Mo.coq_VandermondeCol m x))))))

  type coq_TE = Coq_support.Mo.Coq_mat.coq_VF

  (** val extractor : Coq_sig.coq_W -> coq_E -> coq_W **)

  let extractor w e =
    let a = fst (fst (fst w)) in
    let r = snd (fst (fst w)) in
    let b = snd (fst w) in
    let s = snd w in
    ((((Cons
    ((Coq_support.Mo.Coq_mat.coq_VF_scale Coq_sig.n (hd (S M.coq_N) b)
       (Field.coq_FmulInv (fst e))), (S M.coq_N), (vremove_last (S M.coq_N) a))),
    (Cons ((Field.coq_Fmul (hd (S M.coq_N) s) (Field.coq_FmulInv (fst e))), (S
    M.coq_N), (vremove_last (S M.coq_N) r)))),
    (Coq_support.Mo.Coq_mat.coq_VF_scale Coq_sig.n
      (Coq_support.Mo.Coq_mat.coq_VF_add Coq_sig.n (vlastS (S M.coq_N) b)
        (Coq_support.Mo.Coq_mat.coq_VF_neg Coq_sig.n
          (vfold_left (Coq_support.Mo.Coq_mat.coq_VF_add Coq_sig.n) M.coq_N
            (Coq_support.Mo.Coq_mat.coq_VF_zero Coq_sig.n)
            (vmap2 (Coq_support.Mo.Coq_mat.coq_VF_scale Coq_sig.n) M.coq_N
              (tl M.coq_N (vremove_last (S M.coq_N) b))
              (const (Field.coq_FmulInv (fst e)) M.coq_N)))))
      (Field.coq_FmulInv
        (vlastS M.coq_N
          (tl (S M.coq_N) (Coq_support.Mo.coq_VandermondeCol m (fst e))))))),
    (Field.coq_Fmul
      (Field.coq_Fadd (vlastS (S M.coq_N) s)
        (Field.coq_Finv
          (vfold_left Field.coq_Fadd M.coq_N Field.coq_Fzero
            (vmap2 Field.coq_Fmul M.coq_N (tl M.coq_N (vremove_last (S M.coq_N) s))
              (const (Field.coq_FmulInv (fst e)) M.coq_N)))))
      (Field.coq_FmulInv
        (vlastS M.coq_N
          (tl (S M.coq_N) (Coq_support.Mo.coq_VandermondeCol m (fst e)))))))

  type coq_X = Coq_sig.coq_X

  (** val simulator : coq_St -> coq_TE -> coq_E -> coq_C **)

  let simulator s t1 _ =
    let h = fst (fst (fst s)) in
    let hs = snd (fst (fst s)) in
    vmap (fun x ->
      Coq_support.EPC.coq_EPC n h hs (Coq_support.Mo.Coq_mat.coq_VF_zero n) x)
      M.coq_N t1

  (** val simMap : coq_St -> coq_W -> coq_E -> coq_X -> coq_R -> coq_TE **)

  let simMap _ w _ x r =
    Coq_support.Mo.Coq_mat.coq_VF_add M.coq_N r
      (vbuild M.coq_N (fun i _ ->
        Coq_support.Mo.Coq_mat.coq_VF_inProd Coq_sig.n x
          (vfold_left (Coq_support.Mo.Coq_mat.coq_VF_mult n) (S (S i))
            (Coq_support.Mo.Coq_mat.coq_VF_one n)
            (vsub m (fst (fst (fst w))) O (S (S i))))))

  (** val simMapInv : coq_St -> coq_W -> coq_E -> coq_X -> coq_TE -> coq_R **)

  let simMapInv _ w _ x t1 =
    Coq_support.Mo.Coq_mat.coq_VF_sub M.coq_N t1
      (vbuild M.coq_N (fun i _ ->
        Coq_support.Mo.Coq_mat.coq_VF_inProd Coq_sig.n x
          (vfold_left (Coq_support.Mo.Coq_mat.coq_VF_mult n) (S (S i))
            (Coq_support.Mo.Coq_mat.coq_VF_one n)
            (vsub m (fst (fst (fst w))) O (S (S i))))))

  (** val sigXcomp : coq_St -> coq_X -> Coq_sig.coq_X **)

  let sigXcomp _ x =
    x
 end

module BGSingleProdIns =
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
 struct
  (** val n : nat **)

  let n =
    S (S (S Hack.coq_N))

  module Mo = MatricesFieldIns(Field)

  module EPC = ExtendComScheme(Commitment)(Field)(VS2)(Mo.Coq_mat)

  module PC = BasicComScheme(Commitment)(Field)(VS2)(Mo.Coq_mat)

  module HardProb = HardProblems(Commitment)(Field)(VS2)

  module RAL = RingAddationalLemmas(Field)

  type coq_St =
    ((Commitment.coq_G * EPC.MoM.coq_VG) * Commitment.coq_G) * Field.coq_F

  type coq_W = Mo.Coq_mat.coq_VF * Field.coq_F

  (** val coq_Rel : coq_St -> coq_W -> bool **)

  let coq_Rel s w =
    let (p0, b) = s in
    let (p1, _) = p0 in
    let (h, hs) = p1 in
    let (a, r) = w in
    (&&) (Commitment.coq_Gbool_eq (snd (fst s)) (EPC.coq_EPC n h hs a r))
      (Field.coq_Fbool_eq b (Mo.Coq_mat.coq_VF_prod n a))

  type coq_C = (Commitment.coq_G * Commitment.coq_G) * Commitment.coq_G

  type coq_R =
    (((Mo.Coq_mat.coq_VF * Field.coq_F) * Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  type coq_T = ((Mo.Coq_mat.coq_VF * Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  (** val vecb : Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF **)

  let vecb a =
    vbuild n (fun i _ -> Mo.Coq_mat.coq_VF_prod (S i) (vsub n a O (S i)))

  (** val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C **)

  let coq_P0 s r w =
    let (p0, _) = s in
    let (p1, _) = p0 in
    let (h, hs) = p1 in
    let (p2, sx) = r in
    let (p3, s1) = p2 in
    let (p4, delta) = p3 in
    let (d, randr) = p4 in
    let (a, _) = w in
    let delta1 = hd (S (S Hack.coq_N)) d in
    (s, (((EPC.coq_EPC n h hs d randr),
    (EPC.coq_EPC (S (S Hack.coq_N)) h (vremove_last (S (S Hack.coq_N)) hs) (Cons
      ((Field.coq_Fmul (Field.coq_Finv delta1)
         (hd (S Hack.coq_N) (tl (S (S Hack.coq_N)) d))), (S Hack.coq_N),
      (vbuild (S Hack.coq_N) (fun i _ ->
        Field.coq_Fmul (Field.coq_Finv (vnth (S Hack.coq_N) delta i))
          (vnth (S Hack.coq_N) (tl (S Hack.coq_N) (tl (S (S Hack.coq_N)) d)) i)))))
      s1)),
    (EPC.coq_EPC (S (S Hack.coq_N)) h (vremove_last (S (S Hack.coq_N)) hs) (Cons
      ((Field.coq_Fadd
         (Field.coq_Fadd (hd Hack.coq_N delta)
           (Field.coq_Finv
             (Field.coq_Fmul (hd (S Hack.coq_N) (tl (S (S Hack.coq_N)) a)) delta1)))
         (Field.coq_Finv
           (Field.coq_Fmul (hd (S (S Hack.coq_N)) (vecb a))
             (hd (S Hack.coq_N) (tl (S (S Hack.coq_N)) d))))), (S Hack.coq_N),
      (vadd Hack.coq_N
        (vbuild Hack.coq_N (fun i _ ->
          Field.coq_Fadd
            (Field.coq_Fadd (vnth Hack.coq_N (tl Hack.coq_N delta) i)
              (Field.coq_Finv
                (Field.coq_Fmul
                  (vnth Hack.coq_N
                    (tl Hack.coq_N
                      (tl (S Hack.coq_N) (vremove_last (S (S Hack.coq_N)) a))) i)
                  (vnth Hack.coq_N (vremove_last Hack.coq_N delta) i))))
            (Field.coq_Finv
              (Field.coq_Fmul
                (vnth Hack.coq_N
                  (tl Hack.coq_N
                    (vremove_last (S Hack.coq_N)
                      (vremove_last (S (S Hack.coq_N)) (vecb a)))) i)
                (vnth Hack.coq_N
                  (tl Hack.coq_N
                    (tl (S Hack.coq_N) (vremove_last (S (S Hack.coq_N)) d))) i)))))
        (Field.coq_Fadd
          (Field.coq_Fmul (Field.coq_Finv (vlastS (S (S Hack.coq_N)) a))
            (vlastS Hack.coq_N delta))
          (Field.coq_Finv
            (Field.coq_Fmul
              (vlastS (S Hack.coq_N) (vremove_last (S (S Hack.coq_N)) (vecb a)))
              (vlastS (S (S Hack.coq_N)) d))))))) sx)))

  (** val coq_P1 :
      ((coq_St * coq_C) * Field.coq_F) -> coq_R -> coq_W ->
      ((coq_St * coq_C) * Field.coq_F) * coq_T **)

  let coq_P1 sce r w =
    let (p0, sx) = r in
    let (p1, s1) = p0 in
    let (p2, delta) = p1 in
    let (d, rd) = p2 in
    let (a, r0) = w in
    (sce, ((((Mo.Coq_mat.coq_VF_add n (Mo.Coq_mat.coq_VF_scale n a (snd sce)) d),
    (Mo.Coq_mat.coq_VF_add n (Mo.Coq_mat.coq_VF_scale n (vecb a) (snd sce)) (Cons
      ((hd (S (S Hack.coq_N)) d), (S (S Hack.coq_N)),
      (vadd (S Hack.coq_N) delta Field.coq_Fzero))))),
    (Field.coq_Fadd (Field.coq_Fmul (snd sce) r0) rd)),
    (Field.coq_Fadd (Field.coq_Fmul (snd sce) sx) s1)))

  (** val coq_V1 : (((coq_St * coq_C) * Field.coq_F) * coq_T) -> bool **)

  let coq_V1 scet =
    let (p0, b) = fst (fst (fst scet)) in
    let (p1, c) = p0 in
    let (h, hs) = p1 in
    let (p2, cDelta) = snd (fst (fst scet)) in
    let (cd, cdelta) = p2 in
    let (p3, s) = snd scet in
    let (p4, r) = p3 in
    let (a, bvec) = p4 in
    let x = snd (fst scet) in
    (&&)
      ((&&)
        ((&&)
          (Commitment.coq_Gbool_eq (Commitment.coq_Gdot (VS2.op c x) cd)
            (EPC.coq_EPC n h hs a r))
          (Commitment.coq_Gbool_eq (Commitment.coq_Gdot (VS2.op cDelta x) cdelta)
            (EPC.coq_EPC (S (S Hack.coq_N)) h (vremove_last (S (S Hack.coq_N)) hs)
              (Mo.Coq_mat.coq_VF_sub (S (S Hack.coq_N))
                (Mo.Coq_mat.coq_VF_scale (S (S Hack.coq_N))
                  (tl (S (S Hack.coq_N)) bvec) x)
                (Mo.Coq_mat.coq_VF_mult (S (S Hack.coq_N))
                  (vremove_last (S (S Hack.coq_N)) bvec) (tl (S (S Hack.coq_N)) a)))
              s)))
        (Field.coq_Fbool_eq (hd (S (S Hack.coq_N)) bvec) (hd (S (S Hack.coq_N)) a)))
      (Field.coq_Fbool_eq (vlastS (S (S Hack.coq_N)) bvec) (Field.coq_Fmul x b))

  type coq_TE =
    (((Mo.Coq_mat.coq_VF * Field.coq_F) * Mo.Coq_mat.coq_VF) * Field.coq_F) * Field.coq_F

  type coq_X = Mo.Coq_mat.coq_VF

  (** val simulator :
      coq_St -> coq_TE -> Field.coq_F -> ((coq_St * coq_C) * Field.coq_F) * coq_T **)

  let simulator s t1 x =
    let (p0, b) = s in
    let (p1, c) = p0 in
    let (h, hs) = p1 in
    let (p2, sx) = t1 in
    let (p3, s1) = p2 in
    let (p4, delta) = p3 in
    let (d, randr) = p4 in
    (((s,
    (((Commitment.coq_Gdot (EPC.coq_EPC n h hs d randr)
        (Commitment.coq_Ginv (VS2.op c x))),
    (Commitment.coq_Gdot
      (EPC.coq_EPC (S (S Hack.coq_N)) h (vremove_last (S (S Hack.coq_N)) hs) (Cons
        ((Field.coq_Fadd (Field.coq_Fmul x (hd Hack.coq_N delta))
           (Field.coq_Finv
             (Field.coq_Fmul (hd (S (S Hack.coq_N)) d)
               (hd (S Hack.coq_N) (tl (S (S Hack.coq_N)) d))))), (S Hack.coq_N),
        (vadd Hack.coq_N
          (vbuild Hack.coq_N (fun i _ ->
            Field.coq_Fadd
              (Field.coq_Fmul x (vnth Hack.coq_N (tl Hack.coq_N delta) i))
              (Field.coq_Finv
                (Field.coq_Fmul (vnth Hack.coq_N (vremove_last Hack.coq_N delta) i)
                  (vnth Hack.coq_N
                    (tl Hack.coq_N
                      (tl (S Hack.coq_N) (vremove_last (S (S Hack.coq_N)) d))) i)))))
          (Field.coq_Fadd (Field.coq_Fmul (Field.coq_Fmul x x) b)
            (Field.coq_Finv
              (Field.coq_Fmul (vlastS Hack.coq_N delta)
                (vlastS (S (S Hack.coq_N)) d))))))) s1)
      (VS2.op h (Field.coq_Fmul (Field.coq_Finv sx) x)))),
    (EPC.coq_EPC (S (S Hack.coq_N)) h (vremove_last (S (S Hack.coq_N)) hs)
      (Mo.Coq_mat.coq_VF_zero (S (S Hack.coq_N))) sx))), x), (((d, (Cons
    ((hd (S (S Hack.coq_N)) d), (S (S Hack.coq_N)),
    (vadd (S Hack.coq_N) delta (Field.coq_Fmul x b))))), randr), s1))

  (** val simMap : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_R -> coq_TE **)

  let simMap _ w x xx r =
    let (a, witr) = w in
    let (p0, sx) = r in
    let (p1, s1) = p0 in
    let (p2, delta) = p1 in
    let (d, randr) = p2 in
    let delta1 = hd (S (S Hack.coq_N)) d in
    (((((Mo.Coq_mat.coq_VF_add n (Mo.Coq_mat.coq_VF_scale n a x) d),
    (Field.coq_Fadd (Field.coq_Fmul x witr) randr)),
    (Mo.Coq_mat.coq_VF_add (S Hack.coq_N)
      (Mo.Coq_mat.coq_VF_scale (S Hack.coq_N)
        (tl (S Hack.coq_N) (vremove_last (S (S Hack.coq_N)) (vecb a))) x) delta)),
    (Field.coq_Fadd (Field.coq_Fmul x sx) s1)),
    (Field.coq_Fadd sx
      (Mo.Coq_mat.coq_VF_inProd (S (S Hack.coq_N))
        (vremove_last (S (S Hack.coq_N)) xx) (Cons
        ((Field.coq_Fadd
           (Field.coq_Fadd (hd Hack.coq_N delta)
             (Field.coq_Finv
               (Field.coq_Fmul (hd (S Hack.coq_N) (tl (S (S Hack.coq_N)) a)) delta1)))
           (Field.coq_Finv
             (Field.coq_Fmul (hd (S (S Hack.coq_N)) (vecb a))
               (hd (S Hack.coq_N) (tl (S (S Hack.coq_N)) d))))), (S Hack.coq_N),
        (vadd Hack.coq_N
          (vbuild Hack.coq_N (fun i _ ->
            Field.coq_Fadd
              (Field.coq_Fadd (vnth Hack.coq_N (tl Hack.coq_N delta) i)
                (Field.coq_Finv
                  (Field.coq_Fmul
                    (vnth Hack.coq_N
                      (tl Hack.coq_N
                        (tl (S Hack.coq_N) (vremove_last (S (S Hack.coq_N)) a))) i)
                    (vnth Hack.coq_N (vremove_last Hack.coq_N delta) i))))
              (Field.coq_Finv
                (Field.coq_Fmul
                  (vnth Hack.coq_N
                    (tl Hack.coq_N
                      (vremove_last (S Hack.coq_N)
                        (vremove_last (S (S Hack.coq_N)) (vecb a)))) i)
                  (vnth Hack.coq_N
                    (tl Hack.coq_N
                      (tl (S Hack.coq_N) (vremove_last (S (S Hack.coq_N)) d))) i)))))
          (Field.coq_Fadd
            (Field.coq_Fmul (Field.coq_Finv (vlastS (S (S Hack.coq_N)) a))
              (vlastS Hack.coq_N delta))
            (Field.coq_Finv
              (Field.coq_Fmul
                (vlastS (S Hack.coq_N) (vremove_last (S (S Hack.coq_N)) (vecb a)))
                (vlastS (S (S Hack.coq_N)) d))))))))))

  (** val simMapInv : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_TE -> coq_R **)

  let simMapInv _ w x xx t1 =
    let (a, witr) = w in
    let (p0, sx) = t1 in
    let (p1, s1) = p0 in
    let (p2, delta) = p1 in
    let (d, randr) = p2 in
    let org_d = Mo.Coq_mat.coq_VF_sub n d (Mo.Coq_mat.coq_VF_scale n a x) in
    let org_r = Field.coq_Fadd randr (Field.coq_Finv (Field.coq_Fmul x witr)) in
    let org_delta =
      Mo.Coq_mat.coq_VF_sub (S Hack.coq_N) delta
        (Mo.Coq_mat.coq_VF_scale (S Hack.coq_N)
          (tl (S Hack.coq_N) (vremove_last (S (S Hack.coq_N)) (vecb a))) x)
    in
    let delta1 = hd (S (S Hack.coq_N)) org_d in
    let org_sx =
      Field.coq_Fadd sx
        (Field.coq_Finv
          (Mo.Coq_mat.coq_VF_inProd (S (S Hack.coq_N))
            (vremove_last (S (S Hack.coq_N)) xx) (Cons
            ((Field.coq_Fadd
               (Field.coq_Fadd (hd Hack.coq_N org_delta)
                 (Field.coq_Finv
                   (Field.coq_Fmul (hd (S Hack.coq_N) (tl (S (S Hack.coq_N)) a))
                     delta1)))
               (Field.coq_Finv
                 (Field.coq_Fmul (hd (S (S Hack.coq_N)) (vecb a))
                   (hd (S Hack.coq_N) (tl (S (S Hack.coq_N)) org_d))))), (S
            Hack.coq_N),
            (vadd Hack.coq_N
              (vbuild Hack.coq_N (fun i _ ->
                Field.coq_Fadd
                  (Field.coq_Fadd (vnth Hack.coq_N (tl Hack.coq_N org_delta) i)
                    (Field.coq_Finv
                      (Field.coq_Fmul
                        (vnth Hack.coq_N
                          (tl Hack.coq_N
                            (tl (S Hack.coq_N) (vremove_last (S (S Hack.coq_N)) a)))
                          i) (vnth Hack.coq_N (vremove_last Hack.coq_N org_delta) i))))
                  (Field.coq_Finv
                    (Field.coq_Fmul
                      (vnth Hack.coq_N
                        (tl Hack.coq_N
                          (vremove_last (S Hack.coq_N)
                            (vremove_last (S (S Hack.coq_N)) (vecb a)))) i)
                      (vnth Hack.coq_N
                        (tl Hack.coq_N
                          (tl (S Hack.coq_N) (vremove_last (S (S Hack.coq_N)) org_d)))
                        i)))))
              (Field.coq_Fadd
                (Field.coq_Fmul (Field.coq_Finv (vlastS (S (S Hack.coq_N)) a))
                  (vlastS Hack.coq_N org_delta))
                (Field.coq_Finv
                  (Field.coq_Fmul
                    (vlastS (S Hack.coq_N)
                      (vremove_last (S (S Hack.coq_N)) (vecb a)))
                    (vlastS (S (S Hack.coq_N)) org_d)))))))))
    in
    ((((org_d, org_r), org_delta),
    (Field.coq_Fadd s1 (Field.coq_Finv (Field.coq_Fmul x org_sx)))), org_sx)

  (** val coq_M : nat **)

  let coq_M =
    S (S O)

  (** val extractor : coq_T t0 -> Field.coq_F t0 -> coq_W **)

  let extractor t1 e =
    ((Mo.Coq_mat.coq_VF_scale n
       (Mo.Coq_mat.coq_VF_sub n (fst (fst (fst (hd (S O) t1))))
         (fst (fst (fst (vlastS (S O) t1)))))
       (Field.coq_FmulInv
         (Field.coq_Fadd (hd (S O) e) (Field.coq_Finv (vlastS (S O) e))))),
      (Field.coq_Fmul
        (Field.coq_Fadd (snd (fst (hd (S O) t1)))
          (Field.coq_Finv (snd (fst (vlastS (S O) t1)))))
        (Field.coq_FmulInv
          (Field.coq_Fadd (hd (S O) e) (Field.coq_Finv (vlastS (S O) e))))))

  (** val coq_Polynomial :
      nat -> Mo.Coq_mat.coq_VF -> Mo.Coq_mat.coq_VF -> Field.coq_F ->
      Mo.Coq_mat.coq_VF -> Field.coq_F **)

  let rec coq_Polynomial n0 w u e a =
    match n0 with
    | O -> Field.coq_Fadd (Field.coq_Fmul e (hd O w)) (hd O u)
    | S n1 ->
      Field.coq_Fadd
        (Field.coq_Fadd
          (Field.coq_Fmul
            (coq_Polynomial n1 (vremove_last (S n1) w) (vremove_last (S n1) u) e
              (vremove_last n1 a)) (vlastS n1 a))
          (Field.coq_Fmul (Mo.Coq_mat.coq_VF_prod (S (S n1)) (const e (S (S n1))))
            (vlastS (S n1) w)))
        (Field.coq_Fmul (Mo.Coq_mat.coq_VF_prod (S n1) (const e (S n1)))
          (vlastS (S n1) u))

  (** val allDifferent : Field.coq_F t0 -> bool **)

  let allDifferent e =
    pairwisePredicate coq_M Chal.coq_Gdisjoint e
 end

module ProdArgIns =
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
 struct
  (** val n : nat **)

  let n =
    S (S (S Hack.coq_N))

  (** val m : nat **)

  let m =
    S (S M.coq_N)

  module EPC = ExtendComScheme(Commitment)(Field)(VS2)(Coq_support.Mo.Coq_mat)

  module ALenc =
   EncryptionSchemeProp(Message)(Ciphertext)(Ring)(Field)(VS1)(MVS)(Coq_enc)

  module ALR = RingAddationalLemmas(Ring)

  module G2 = GroupFromFieldIns(Field)

  type coq_St = ((Commitment.coq_G * EPC.MoM.coq_VG) * EPC.MoM.coq_VG) * Field.coq_F

  type coq_W = Coq_support.Mo.Coq_mat.coq_VF t0 * Coq_support.Mo.Coq_mat.coq_VF

  (** val coq_Rel : coq_St -> coq_W -> bool **)

  let coq_Rel s w =
    let h = fst (fst (fst s)) in
    let hs = snd (fst (fst s)) in
    let cA = snd (fst s) in
    let b = snd s in
    let a = fst w in
    let r = snd w in
    (&&) (EPC.MoM.coq_VG_eq m cA (EPC.comEPC n m h hs a r))
      (Field.coq_Fbool_eq
        (Coq_support.Mo.Coq_mat.coq_VF_prod n
          (vfold_left (Coq_support.Mo.Coq_mat.coq_VF_mult n) m
            (Coq_support.Mo.Coq_mat.coq_VF_one n) a)) b)

  type coq_C = Commitment.coq_G

  type coq_R = Field.coq_F

  (** val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C **)

  let coq_P0 s rand w =
    let (p0, _) = s in
    let (p1, _) = p0 in
    let (h, hs) = p1 in
    let (a, _) = w in
    (s,
    (EPC.coq_EPC n h hs
      (vfold_left (Coq_support.Mo.Coq_mat.coq_VF_mult n) m
        (Coq_support.Mo.Coq_mat.coq_VF_one n) a) rand))

  (** val coq_ToStSig : (coq_St * coq_C) -> Coq_sig.coq_St **)

  let coq_ToStSig = function
  | (s, c) -> let (p0, b) = s in let (p1, _) = p0 in ((p1, c), b)

  (** val coq_ToWitSig : (coq_St * coq_C) -> coq_R -> coq_W -> Coq_sig.coq_W **)

  let coq_ToWitSig _ rand = function
  | (a, _) ->
    ((vfold_left (Coq_support.Mo.Coq_mat.coq_VF_mult n) m
       (Coq_support.Mo.Coq_mat.coq_VF_one n) a), rand)

  (** val coq_ToStSig5 : (coq_St * coq_C) -> Coq_sig5.coq_St **)

  let coq_ToStSig5 = function
  | (s0, c) -> let (p0, _) = s0 in (p0, c)

  (** val coq_ToWitSig5 : (coq_St * coq_C) -> coq_R -> coq_W -> Coq_sig5.coq_W **)

  let coq_ToWitSig5 _ rand = function
  | (a, r) ->
    (((a, r),
      (vfold_left (Coq_support.Mo.Coq_mat.coq_VF_mult n) m
        (Coq_support.Mo.Coq_mat.coq_VF_one n) a)), rand)

  type coq_TE = Field.coq_F

  (** val extractor : Coq_sig5.coq_W -> Coq_sig.coq_W -> coq_W **)

  let extractor w _ =
    let (p0, _) = w in let (p1, _) = p0 in p1

  type coq_X = Coq_support.Mo.Coq_mat.coq_VF

  (** val simulator : coq_St -> coq_TE -> coq_C **)

  let simulator s t1 =
    let (p0, _) = s in
    let (p1, _) = p0 in
    let (h, hs) = p1 in EPC.coq_EPC n h hs (Coq_support.Mo.Coq_mat.coq_VF_zero n) t1

  (** val simMap : coq_St -> coq_W -> coq_X -> coq_R -> coq_TE **)

  let simMap _ w x r =
    let (a, _) = w in
    Field.coq_Fadd r
      (Coq_support.Mo.Coq_mat.coq_VF_inProd n x
        (vfold_left (Coq_support.Mo.Coq_mat.coq_VF_mult n) m
          (Coq_support.Mo.Coq_mat.coq_VF_one n) a))

  (** val simMapInv : coq_St -> coq_W -> coq_X -> coq_TE -> coq_R **)

  let simMapInv _ w x t1 =
    let (a, _) = w in
    Field.coq_Fadd t1
      (Field.coq_Finv
        (Coq_support.Mo.Coq_mat.coq_VF_inProd n x
          (vfold_left (Coq_support.Mo.Coq_mat.coq_VF_mult n) m
            (Coq_support.Mo.Coq_mat.coq_VF_one n) a)))

  (** val sigXcomp : coq_St -> coq_X -> Coq_sig.coq_X **)

  let sigXcomp _ x =
    x

  (** val sig5Xcomp : coq_St -> coq_X -> Coq_sig5.coq_X **)

  let sig5Xcomp _ x =
    x
 end

module BGMultiArgIns =
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
 struct
  (** val n : nat **)

  let n =
    S (S (S Hack.coq_N))

  (** val m : nat **)

  let m =
    S (S M.coq_N)

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

  (** val coq_Rel : coq_St -> coq_W -> bool **)

  let coq_Rel s w =
    let (p0, _) = s in
    let (p1, cA) = p0 in
    let (p2, c) = p1 in
    let (p3, cbar) = p2 in
    let (p4, hs) = p3 in
    let (pk, h) = p4 in
    let a = fst (fst w) in
    let r = snd (fst w) in
    let p5 = snd w in
    (&&) (Coq_support.EPC.MoM.coq_VG_eq m cA (Coq_support.EPC.comEPC n m h hs a r))
      (Ciphertext.coq_Gbool_eq c
        (Ciphertext.coq_Gdot (Coq_enc.enc pk Coq_enc.coq_Mzero p5)
          (Coq_support.MoC.coq_VG_prod m
            (vmap2 (fun x y ->
              Coq_support.MoC.coq_VG_prod n (Coq_support.MoC.coq_VG_Pexp n x y)) m
              cbar a))))

  (** val coq_P0 : coq_St -> coq_R -> coq_W -> coq_St * coq_C **)

  let coq_P0 st r w =
    let (p0, g0) = st in
    let (p1, _) = p0 in
    let (p2, _) = p1 in
    let (p3, cbar) = p2 in
    let (p4, hs) = p3 in
    let (pk, h) = p4 in
    let (p5, tau) = r in
    let (p6, s) = p5 in
    let (p7, b) = p6 in
    let (a0, r0) = p7 in
    let b0 =
      vapp m (S (S M.coq_N)) (fst b) (Cons (Field.coq_Fzero, (S M.coq_N), (snd b)))
    in
    let s0 =
      vapp m (S (S M.coq_N)) (fst s) (Cons (Field.coq_Fzero, (S M.coq_N), (snd s)))
    in
    let a = Cons (a0, m, (fst (fst w))) in
    let p8 = snd w in
    let tau0 = vapp m (S (S M.coq_N)) (fst tau) (Cons (p8, (S M.coq_N), (snd tau)))
    in
    let cA0 = Coq_support.EPC.coq_EPC n h hs a0 r0 in
    let cB0 =
      Coq_support.PC.comPC (add m (S (S M.coq_N))) h (hd (S (S Hack.coq_N)) hs) b0 s0
    in
    let e0 =
      Coq_support.coq_EkGenerators pk m g0 cbar a tau0 b0
        (Coq_support.Mo.Coq_mat.coq_VF_one (add m m))
    in
    (st, ((cA0, cB0), e0))

  (** val coq_P1 :
      ((coq_St * coq_C) * Field.coq_F) -> coq_R -> coq_W ->
      ((coq_St * coq_C) * Field.coq_F) * coq_T **)

  let coq_P1 ggtoxgtorc r w =
    let c = snd ggtoxgtorc in
    let a = fst (fst w) in
    let a0 = fst (fst (fst (fst r))) in
    let r0 = snd (fst (fst (fst r))) in
    let b =
      vapp m (S (S M.coq_N)) (fst (snd (fst (fst r)))) (Cons (Field.coq_Fzero, (S
        M.coq_N), (snd (snd (fst (fst r))))))
    in
    let s0 =
      vapp m (S (S M.coq_N)) (fst (snd (fst r))) (Cons (Field.coq_Fzero, (S
        M.coq_N), (snd (snd (fst r)))))
    in
    let tau =
      vapp m (S (S M.coq_N)) (fst (snd r)) (Cons ((snd w), (S M.coq_N),
        (snd (snd r))))
    in
    let r1 = snd (fst w) in
    let xBar = Coq_support.Mo.coq_VandermondeCol (add (S O) m) c in
    let xK = Coq_support.Mo.coq_VandermondeCol (add m m) c in
    let aT =
      hd O
        (Coq_support.Mo.Coq_mat.FMatrix.mat_mult (S O) (add (S O) m) n (Cons (xBar,
          O, Nil)) (Cons (a0, m, a)))
    in
    let rT = Coq_support.Mo.Coq_mat.coq_VF_inProd (S m) (Cons (r0, m, r1)) xBar in
    let bT = Coq_support.Mo.Coq_mat.coq_VF_inProd (add m (S (S M.coq_N))) b xK in
    let sT = Coq_support.Mo.Coq_mat.coq_VF_inProd (add m (S (S M.coq_N))) s0 xK in
    let tauT =
      Coq_support.MoR.coq_VF_sum (add m (S (S M.coq_N)))
        (vmap2 MVS.op3 (add m (S (S M.coq_N))) tau xK)
    in
    (ggtoxgtorc, ((((aT, rT), bT), sT), tauT))

  (** val coq_V1 : (((coq_St * coq_C) * Field.coq_F) * coq_T) -> bool **)

  let coq_V1 = function
  | (p0, resp) ->
    let (p1, chal) = p0 in
    let (stat, comm) = p1 in
    let (p2, g0) = stat in
    let (p3, cA) = p2 in
    let (p4, c) = p3 in
    let (p5, cbar) = p4 in
    let (p6, hs) = p5 in
    let (pk, h) = p6 in
    let (p7, e) = comm in
    let (cA0, cB) = p7 in
    let x = rev m (Coq_support.Mo.coq_VandermondeCol m chal) in
    let xBar = Coq_support.Mo.coq_VandermondeCol (add (S O) m) chal in
    let xK = Coq_support.Mo.coq_VandermondeCol (add m m) chal in
    let aT = fst (fst (fst (fst resp))) in
    let rT = snd (fst (fst (fst resp))) in
    let bT = snd (fst (fst resp)) in
    let sT = snd (fst resp) in
    let tauT = snd resp in
    let eq1 =
      Commitment.coq_Gbool_eq
        (Coq_support.EPC.MoM.coq_VG_prod (S m)
          (Coq_support.EPC.MoM.coq_VG_Pexp (S m) (Cons (cA0, m, cA)) xBar))
        (Coq_support.EPC.coq_EPC n h hs aT rT)
    in
    let eq2 =
      Commitment.coq_Gbool_eq
        (Coq_support.EPC.MoM.coq_VG_prod (add m m)
          (Coq_support.EPC.MoM.coq_VG_Pexp (add m m) cB xK))
        (Coq_support.PC.coq_PC h (hd (S (S Hack.coq_N)) hs) bT sT)
    in
    let eq3 =
      Ciphertext.coq_Gbool_eq
        (Coq_support.MoC.coq_VG_prod (add m m)
          (Coq_support.MoC.coq_VG_Pexp (add m m) e xK))
        (Ciphertext.coq_Gdot (Coq_enc.enc pk (VS3.op g0 bT) tauT)
          (Coq_support.MoC.coq_VG_prod m
            (vmap2 (fun ci xi ->
              Coq_support.MoC.coq_VG_prod n
                (Coq_support.MoC.coq_VG_Pexp n ci
                  (Coq_support.Mo.Coq_mat.coq_VF_scale n aT xi))) m cbar x)))
    in
    let eq4 =
      Commitment.coq_Gbool_eq (vnth (add m m) cB Coq_support.m)
        (Coq_support.PC.coq_PC h (hd (S (S Hack.coq_N)) hs) Field.coq_Fzero
          Field.coq_Fzero)
    in
    let eq5 = Ciphertext.coq_Gbool_eq (vnth (add m m) e Coq_support.m) c in
    (&&) ((&&) ((&&) ((&&) eq1 eq2) eq3) eq4) eq5

  (** val simMap : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_R -> coq_TE **)

  let simMap _ w c x r =
    let a = fst (fst w) in
    let p0 = snd w in
    let (p1, p2) = r in
    let (p3, p4) = p1 in
    let (p5, p6) = p3 in
    let (a0, r0) = p5 in
    let (b0, b1) = p6 in
    let (s0, s1) = p4 in
    let (tau0, tau1) = p2 in
    let b = vapp m (S (S M.coq_N)) b0 (Cons (Field.coq_Fzero, (S M.coq_N), b1)) in
    let s = vapp m (S (S M.coq_N)) s0 (Cons (Field.coq_Fzero, (S M.coq_N), s1)) in
    let tau = vapp m (S (S M.coq_N)) tau0 (Cons (p0, (S M.coq_N), tau1)) in
    let xBar = Coq_support.Mo.coq_VandermondeCol (add (S O) m) c in
    let xK = Coq_support.Mo.coq_VandermondeCol (add m m) c in
    let aT =
      hd O
        (Coq_support.Mo.Coq_mat.FMatrix.mat_mult (S O) (add (S O) m) n (Cons (xBar,
          O, Nil)) (Cons (a0, m, a)))
    in
    let rT =
      Coq_support.Mo.Coq_mat.coq_VF_inProd (S m) (Cons (r0, m, (snd (fst w)))) xBar
    in
    let bT = Coq_support.Mo.Coq_mat.coq_VF_inProd (add m (S (S M.coq_N))) b xK in
    let sT = Coq_support.Mo.Coq_mat.coq_VF_inProd (add m (S (S M.coq_N))) s xK in
    let tauT =
      Coq_support.MoR.coq_VF_sum (add m (S (S M.coq_N)))
        (vmap2 MVS.op3 (add m (S (S M.coq_N))) tau xK)
    in
    let bs = Coq_support.coq_EkGeneratorsRawM m (snd (fst x)) (Cons (a0, m, a)) b in
    let taus = Coq_support.coq_EkGeneratorsRawR m (snd x) (Cons (a0, m, a)) tau in
    let ss =
      Coq_support.Mo.Coq_mat.coq_VF_add (add m (S (S M.coq_N))) s
        (Coq_support.Mo.Coq_mat.coq_VF_scale (add m (S (S M.coq_N))) b
          (hd (S (S Hack.coq_N)) (fst (fst x))))
    in
    (((((aT, rT), bT), sT), tauT), ((((tl (S M.coq_N) (fst (vbreak m m bs))),
    (tl (S M.coq_N) (snd (vbreak m m bs)))),
    ((tl (S M.coq_N) (fst (vbreak m (S (S M.coq_N)) ss))),
    (tl (S M.coq_N) (snd (vbreak m (S (S M.coq_N)) ss))))),
    ((tl (S M.coq_N) (fst (vbreak m m taus))),
    (tl (S M.coq_N) (snd (vbreak m m taus))))))

  (** val simMapInv : coq_St -> coq_W -> Field.coq_F -> coq_X -> coq_TE -> coq_R **)

  let simMapInv _ w c x t1 =
    let a = fst (fst w) in
    let (p0, p1) = t1 in
    let (p2, tauT) = p0 in
    let (p3, sT) = p2 in
    let (p4, bT) = p3 in
    let (aT, rT) = p4 in
    let (p5, p6) = p1 in
    let (p7, p8) = p5 in
    let (cB0, cB1) = p7 in
    let (s0, s1) = p8 in
    let (e1, e2) = p6 in
    let xBar = Coq_support.Mo.coq_VandermondeCol (add (S O) m) c in
    let xK = Coq_support.Mo.coq_VandermondeCol (add m m) c in
    let a0 =
      Coq_support.Mo.Coq_mat.coq_VF_sub n aT
        (hd O
          (Coq_support.Mo.Coq_mat.FMatrix.mat_mult (S O) m n (Cons ((tl m xBar), O,
            Nil)) a))
    in
    let p9 =
      hd (S M.coq_N)
        (snd
          (vbreak m m
            (Coq_support.coq_EkGeneratorsRawR m (snd x) (Cons (a0, m, a))
              (vapp m (S (S M.coq_N)) (Coq_support.MoR.coq_VF_zero m) (Cons
                ((snd w), (S M.coq_N), (Coq_support.MoR.coq_VF_zero (S M.coq_N))))))))
    in
    let b0 =
      hd (S M.coq_N)
        (snd
          (vbreak m m
            (Coq_support.coq_EkGeneratorsRawM m (snd (fst x)) (Cons (a0, m, a))
              (vapp m (S (S M.coq_N)) (Coq_support.Mo.Coq_mat.coq_VF_zero m) (Cons
                (Field.coq_Fzero, (S M.coq_N),
                (Coq_support.Mo.Coq_mat.coq_VF_zero (S M.coq_N))))))))
    in
    let bb =
      Coq_support.Mo.Coq_mat.coq_VF_sub (add (S M.coq_N) (S (S M.coq_N)))
        (vapp (S M.coq_N) (S (S M.coq_N)) cB0 (Cons (b0, (S M.coq_N), cB1)))
        (tl (S
          (let rec add5 n0 m0 =
             match n0 with
             | O -> m0
             | S p10 -> S (add5 p10 m0)
           in add5 M.coq_N m))
          (Coq_support.coq_EkGeneratorsRawM m (snd (fst x)) (Cons (a0, m, a))
            (Coq_support.Mo.Coq_mat.coq_VF_zero (add m m))))
    in
    let ss =
      Coq_support.Mo.Coq_mat.coq_VF_sub (add (S M.coq_N) (S (S M.coq_N)))
        (vapp (S M.coq_N) (S (S M.coq_N)) s0 (Cons (Field.coq_Fzero, (S M.coq_N),
          s1)))
        (Coq_support.Mo.Coq_mat.coq_VF_scale (add (S M.coq_N) (S (S M.coq_N))) bb
          (hd (S (S Hack.coq_N)) (fst (fst x))))
    in
    let taus =
      Coq_support.MoR.coq_VF_sub (add (S M.coq_N) (S (S M.coq_N)))
        (vapp (S M.coq_N) (S (S M.coq_N)) e1 (Cons (p9, (S M.coq_N), e2)))
        (tl (S
          (let rec add5 n0 m0 =
             match n0 with
             | O -> m0
             | S p10 -> S (add5 p10 m0)
           in add5 M.coq_N m))
          (Coq_support.coq_EkGeneratorsRawR m (snd x) (Cons (a0, m, a))
            (Coq_support.MoR.coq_VF_zero (add m m))))
    in
    let r0 =
      Field.coq_Fadd rT
        (Field.coq_Finv
          (Coq_support.Mo.Coq_mat.coq_VF_inProd m (snd (fst w)) (tl m xBar)))
    in
    let b =
      Field.coq_Fadd bT
        (Field.coq_Finv
          (Coq_support.Mo.Coq_mat.coq_VF_inProd (add (S M.coq_N) (S (S M.coq_N))) bb
            (tl (S
              (let rec add5 n0 m0 =
                 match n0 with
                 | O -> m0
                 | S p10 -> S (add5 p10 m0)
               in add5 M.coq_N m)) xK)))
    in
    let s =
      Field.coq_Fadd sT
        (Field.coq_Finv
          (Coq_support.Mo.Coq_mat.coq_VF_inProd (add (S M.coq_N) (S (S M.coq_N))) ss
            (tl (S
              (let rec add5 n0 m0 =
                 match n0 with
                 | O -> m0
                 | S p10 -> S (add5 p10 m0)
               in add5 M.coq_N m)) xK)))
    in
    let tau =
      Ring.coq_Fsub tauT
        (Coq_support.MoR.coq_VF_sum (add (S M.coq_N) (S (S M.coq_N)))
          (vmap2 MVS.op3 (add (S M.coq_N) (S (S M.coq_N))) taus
            (tl (S
              (let rec add5 n0 m0 =
                 match n0 with
                 | O -> m0
                 | S p10 -> S (add5 p10 m0)
               in add5 M.coq_N m)) xK)))
    in
    ((((a0, r0), ((Cons (b, (S M.coq_N),
    (fst (vbreak (S M.coq_N) (S (S M.coq_N)) bb)))),
    (tl (S M.coq_N) (snd (vbreak (S M.coq_N) (S (S M.coq_N)) bb))))), ((Cons (s, (S
    M.coq_N), (fst (vbreak (S M.coq_N) (S (S M.coq_N)) ss)))),
    (tl (S M.coq_N) (snd (vbreak (S M.coq_N) (S (S M.coq_N)) ss))))), ((Cons (tau,
    (S M.coq_N), (fst (vbreak (S M.coq_N) (S (S M.coq_N)) taus)))),
    (tl (S M.coq_N) (snd (vbreak (S M.coq_N) (S (S M.coq_N)) taus)))))

  (** val simulator :
      coq_St -> coq_TE -> Field.coq_F -> ((coq_St * coq_C) * Field.coq_F) * coq_T **)

  let simulator s z0 e =
    let (p0, g0) = s in
    let (p1, cA) = p0 in
    let (p2, c) = p1 in
    let (p3, cbar) = p2 in
    let (p4, hs) = p3 in
    let (pk, h) = p4 in
    let (p5, p6) = z0 in
    let (p7, tauT) = p5 in
    let (p8, sT) = p7 in
    let (p9, bT) = p8 in
    let (aT, rT) = p9 in
    let (p10, p11) = p6 in
    let (p12, p13) = p10 in
    let (cB0, cB1) = p12 in
    let (s0, s1) = p13 in
    let (e1, e2) = p11 in
    let cB =
      vmap (VS2.op h) (add (S M.coq_N) (S (S M.coq_N)))
        (vapp (S M.coq_N) (S (S M.coq_N)) s0 (Cons (Field.coq_Fzero, (S M.coq_N),
          s1)))
    in
    let e0 =
      vapp (S M.coq_N) (S (S M.coq_N))
        (vmap2 (fun w v -> Coq_enc.enc pk (VS3.op g0 w) v) (S M.coq_N) cB0 e1) (Cons
        (c, (S M.coq_N),
        (vmap2 (fun w v -> Coq_enc.enc pk (VS3.op g0 w) v) (S M.coq_N) cB1 e2)))
    in
    let x = rev m (Coq_support.Mo.coq_VandermondeCol m e) in
    let xBar = Coq_support.Mo.coq_VandermondeCol (add (S O) m) e in
    let xK = Coq_support.Mo.coq_VandermondeCol (add m m) e in
    let cA0 =
      Commitment.coq_Gdot (Coq_support.EPC.coq_EPC n h hs aT rT)
        (Commitment.coq_Ginv
          (Coq_support.EPC.MoM.coq_VG_prod m
            (Coq_support.EPC.MoM.coq_VG_Pexp m cA (tl m xBar))))
    in
    let cB2 =
      Commitment.coq_Gdot (Coq_support.PC.coq_PC h (hd (S (S Hack.coq_N)) hs) bT sT)
        (Commitment.coq_Ginv
          (Coq_support.EPC.MoM.coq_VG_prod (add (S M.coq_N) (S (S M.coq_N)))
            (Coq_support.EPC.MoM.coq_VG_Pexp (add (S M.coq_N) (S (S M.coq_N))) cB
              (tl (S
                (let rec add5 n0 m0 =
                   match n0 with
                   | O -> m0
                   | S p14 -> S (add5 p14 m0)
                 in add5 M.coq_N m)) xK))))
    in
    let eK =
      Ciphertext.coq_Gdot
        (Ciphertext.coq_Gdot (Coq_enc.enc pk (VS3.op g0 bT) tauT)
          (Coq_support.MoC.coq_VG_prod m
            (vmap2 (fun ci xi ->
              Coq_support.MoC.coq_VG_prod n
                (Coq_support.MoC.coq_VG_Pexp n ci
                  (Coq_support.Mo.Coq_mat.coq_VF_scale n aT xi))) m cbar x)))
        (Ciphertext.coq_Ginv
          (Coq_support.MoC.coq_VG_prod (add (S M.coq_N) (S (S M.coq_N)))
            (Coq_support.MoC.coq_VG_Pexp (add (S M.coq_N) (S (S M.coq_N))) e0
              (tl (S
                (let rec add5 n0 m0 =
                   match n0 with
                   | O -> m0
                   | S p14 -> S (add5 p14 m0)
                 in add5 M.coq_N m)) xK))))
    in
    (((s, ((cA0, (Cons (cB2, (add (S M.coq_N) (S (S M.coq_N))), cB))), (Cons (eK,
    (add (S M.coq_N) (S (S M.coq_N))), e0)))), e), (fst z0))

  (** val coq_M : nat **)

  let coq_M =
    Nat.mul (S (S O)) m

  (** val extractor : coq_T t0 -> Field.coq_F t0 -> coq_W **)

  let extractor s c =
    let sM1 =
      fst
        (vbreak (Nat.add (S O) Coq_support.m) (Nat.sub Coq_support.m (S O))
          (vcast (mul (S (S O)) m) s
            (Nat.add (Nat.add (S O) Coq_support.m) (Nat.sub Coq_support.m (S O)))))
    in
    let aT =
      Coq_support.Mo.Coq_mat.FMatrix.mat_transpose (Nat.add (S O) Coq_support.m) n
        (vmap (fun s1 -> fst (fst (fst (fst s1)))) (Nat.add (S O) Coq_support.m) sM1)
    in
    let rT =
      vmap (fun s1 -> snd (fst (fst (fst s1)))) (Nat.add (S O) Coq_support.m) sM1
    in
    let tauT =
      vcast (mul (S (S O)) m) (vmap snd (mul (S (S O)) m) s)
        (Nat.add Coq_support.m Coq_support.m)
    in
    let yM1 =
      Coq_support.Mo.Coq_mat.FMatrix.mat_transpose (Nat.add (S O) Coq_support.m)
        (Nat.add (S O) Coq_support.m)
        (Coq_support.Mo.coq_VandermondeInv (Nat.add (S O) Coq_support.m)
          (fst
            (vbreak (Nat.add (S O) Coq_support.m) (Nat.sub Coq_support.m (S O))
              (vcast (mul (S (S O)) m) c
                (Nat.add (Nat.add (S O) Coq_support.m) (Nat.sub Coq_support.m (S O)))))))
    in
    let y2M =
      Coq_support.Mo.coq_VandermondeInv (Nat.add Coq_support.m Coq_support.m)
        (vcast (mul (S (S O)) m) c (Nat.add Coq_support.m Coq_support.m))
    in
    (((tl Coq_support.m
        (Coq_support.Mo.Coq_mat.FMatrix.mat_transpose n
          (Nat.add (S O) Coq_support.m)
          (Coq_support.Mo.Coq_mat.FMatrix.mat_mult n (Nat.add (S O) Coq_support.m)
            (Nat.add (S O) Coq_support.m) aT yM1))),
    (tl Coq_support.m
      (hd O
        (Coq_support.Mo.Coq_mat.FMatrix.mat_mult (S O) (Nat.add (S O) Coq_support.m)
          (Nat.add (S O) Coq_support.m) (Cons (rT, O, Nil)) yM1)))),
    (Coq_support.coq_RF_inProd (Nat.add Coq_support.m Coq_support.m)
      (vnth (Nat.add Coq_support.m Coq_support.m) y2M Coq_support.m) tauT))

  (** val disjoint : Field.coq_F -> Field.coq_F -> bool **)

  let disjoint c1 c2 =
    negb (Field.coq_Fbool_eq c1 c2)

  (** val allDifferent : Field.coq_F t0 -> bool **)

  let allDifferent e =
    pairwisePredicate coq_M disjoint e
 end

module SigmaPlus5plus3to9Comp =
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
 struct
  type coq_E0 = Coq_exp.coq_E0

  type coq_E1 = Coq_exp.coq_E1

  type coq_E2 = Coq_sig5.coq_E0 * E.coq_G

  type coq_E3 = Coq_sig5.coq_E1

  type coq_St = Coq_exp.coq_St

  type coq_W = Coq_exp.coq_W

  (** val coq_Rel : Coq_exp.coq_St -> Coq_exp.coq_W -> bool **)

  let coq_Rel =
    Coq_exp.coq_Rel

  type coq_C0 = Coq_exp.coq_C0

  type coq_C1 = Coq_exp.coq_C1

  type coq_C2 = Coq_sig5.coq_C0 * Coq_sig.coq_C

  type coq_C3 = Coq_sig5.coq_C1

  type coq_R0 = Coq_exp.coq_R0

  type coq_R1 = Coq_exp.coq_R1

  type coq_R2 = Coq_sig5.coq_R0 * Coq_sig.coq_R

  type coq_R3 = Coq_sig5.coq_R1

  (** val add0 : coq_E0 -> coq_E0 -> coq_E0 **)

  let add0 =
    Coq_exp.add0

  (** val zero0 : coq_E0 **)

  let zero0 =
    Coq_exp.zero0

  (** val inv0 : coq_E0 -> coq_E0 **)

  let inv0 =
    Coq_exp.inv0

  (** val bool_eq0 : coq_E0 -> coq_E0 -> bool **)

  let bool_eq0 =
    Coq_exp.bool_eq0

  (** val disjoint0 : coq_E0 -> coq_E0 -> bool **)

  let disjoint0 =
    Coq_exp.disjoint0

  (** val add1 : coq_E1 -> coq_E1 -> coq_E1 **)

  let add1 =
    Coq_exp.add1

  (** val zero1 : coq_E1 **)

  let zero1 =
    Coq_exp.zero1

  (** val inv1 : coq_E1 -> coq_E1 **)

  let inv1 =
    Coq_exp.inv1

  (** val bool_eq1 : coq_E1 -> coq_E1 -> bool **)

  let bool_eq1 =
    Coq_exp.bool_eq1

  (** val disjoint1 : coq_E1 -> coq_E1 -> bool **)

  let disjoint1 =
    Coq_exp.disjoint1

  (** val add2 : coq_E2 -> coq_E2 -> coq_E2 **)

  let add2 a b =
    ((Coq_sig5.add0 (fst a) (fst b)), (E.coq_Gdot (snd a) (snd b)))

  (** val zero2 : coq_E2 **)

  let zero2 =
    (Coq_sig5.zero0, E.coq_Gone)

  (** val inv2 : coq_E2 -> coq_E2 **)

  let inv2 a =
    ((Coq_sig5.inv0 (fst a)), (E.coq_Ginv (snd a)))

  (** val bool_eq2 : coq_E2 -> coq_E2 -> bool **)

  let bool_eq2 a b =
    (&&) (Coq_sig5.bool_eq0 (fst a) (fst b)) (E.coq_Gbool_eq (snd a) (snd b))

  (** val disjoint2 : coq_E2 -> coq_E2 -> bool **)

  let disjoint2 a b =
    (&&) (Coq_sig5.disjoint0 (fst a) (fst b)) (E.coq_Gdisjoint (snd a) (snd b))

  (** val add3 : coq_E3 -> coq_E3 -> coq_E3 **)

  let add3 =
    Coq_sig5.add1

  (** val zero3 : coq_E3 **)

  let zero3 =
    Coq_sig5.zero1

  (** val inv3 : coq_E3 -> coq_E3 **)

  let inv3 =
    Coq_sig5.inv1

  (** val bool_eq3 : coq_E3 -> coq_E3 -> bool **)

  let bool_eq3 =
    Coq_sig5.bool_eq1

  (** val disjoint3 : coq_E3 -> coq_E3 -> bool **)

  let disjoint3 =
    Coq_sig5.disjoint1

  type coq_T = Coq_sig5.coq_T * Coq_sig.coq_T

  (** val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0 **)

  let coq_P0 =
    Coq_exp.coq_P0

  (** val coq_P1 :
      ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
      ((coq_St * coq_C0) * coq_E0) * coq_C1 **)

  let coq_P1 =
    Coq_exp.coq_P1

  (** val coq_P2 :
      ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) ->
      ((coq_R0 * coq_R1) * coq_R2) -> coq_W ->
      ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2 **)

  let coq_P2 s r w =
    let (_, r2) = r in
    let (r21, r22) = r2 in
    (s,
    ((snd
       (Coq_sig5.coq_P0 (Coq_exp.coq_ToStSig5 s) r21
         (Coq_exp.coq_ToWitSig5 s (fst r) w))),
    (snd
      (Coq_sig.coq_P0 (Coq_exp.coq_ToStSig s) r22 (Coq_exp.coq_ToWitSig s (fst r) w)))))

  (** val coq_P3 :
      ((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) ->
      (((coq_R0 * coq_R1) * coq_R2) * coq_R3) -> coq_W ->
      ((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) * coq_C3 **)

  let coq_P3 s r w =
    let (p0, r3) = r in
    let (_, r2) = p0 in
    let (r21, _) = r2 in
    (s,
    (snd
      (Coq_sig5.coq_P1 (((Coq_exp.coq_ToStSig5 (fst (fst s))), (fst (snd (fst s)))),
        (fst (snd s))) (r21, r3)
        (Coq_exp.coq_ToWitSig5 (fst (fst s)) (fst (fst r)) w))))

  (** val coq_P4 :
      ((((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) * coq_C3) * coq_E3)
      -> (((coq_R0 * coq_R1) * coq_R2) * coq_R3) -> coq_W ->
      ((((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) * coq_C3) * coq_E3) * coq_T **)

  let coq_P4 s r w =
    let e3 = snd s in
    let c3 = snd (fst s) in
    let e2 = snd (fst (fst s)) in
    let c2 = snd (fst (fst (fst s))) in
    let (p0, r3) = r in
    let (_, r2) = p0 in
    let (r21, r22) = r2 in
    (s,
    ((snd
       (Coq_sig5.coq_P2 (((((Coq_exp.coq_ToStSig5 (fst (fst (fst (fst s))))),
         (fst c2)), (fst e2)), c3), e3) (r21, r3)
         (Coq_exp.coq_ToWitSig5 (fst (fst (fst (fst s)))) (fst (fst r)) w))),
    (snd
      (Coq_sig.coq_P1 (((Coq_exp.coq_ToStSig (fst (fst (fst (fst s))))), (snd c2)),
        (snd e2)) r22
        (Coq_exp.coq_ToWitSig (fst (fst (fst (fst s)))) (fst (fst r)) w)))))

  (** val coq_V :
      (((((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) * coq_C3) * coq_E3) * coq_T)
      -> bool **)

  let coq_V s =
    let t1 = snd s in
    let e3 = snd (fst s) in
    let c3 = snd (fst (fst s)) in
    let e2 = snd (fst (fst (fst s))) in
    let c2 = snd (fst (fst (fst (fst s)))) in
    (&&)
      (Coq_sig5.coq_V2 ((((((Coq_exp.coq_ToStSig5 (fst (fst (fst (fst (fst s)))))),
        (fst c2)), (fst e2)), c3), e3), (fst t1)))
      (Coq_sig.coq_V1 ((((Coq_exp.coq_ToStSig (fst (fst (fst (fst (fst s)))))),
        (snd c2)), (snd e2)), (snd t1)))

  type coq_TE0 = Coq_exp.coq_TE0

  type coq_TE1 = Coq_exp.coq_TE1

  type coq_TE2 = Coq_sig5.coq_TE0 * Coq_sig.coq_TE

  type coq_TE3 = Coq_sig5.coq_TE1

  type coq_X = Coq_exp.coq_X

  (** val simulator :
      coq_St -> (((coq_TE0 * coq_TE1) * coq_TE2) * coq_TE3) ->
      (((coq_E0 * coq_E1) * coq_E2) * coq_E3) ->
      ((((((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) * coq_C2) * coq_E2) * coq_C3) * coq_E3) * coq_T **)

  let simulator s t1 e = match e with
  | (p0, e3) ->
    let (p1, e2) = p0 in
    let (e0, e1) = p1 in
    let (e21, e22) = e2 in
    let (p2, t3) = t1 in
    let (_, t2) = p2 in
    let (t21, t22) = t2 in
    let c = Coq_exp.simulator s (fst (fst t1)) (fst (fst e)) in
    let a =
      Coq_sig5.simulator (Coq_exp.coq_ToStSig5 ((((s, (fst c)), e0), (snd c)), e1))
        (t21, t3) (e21, e3)
    in
    let b =
      Coq_sig.simulator (Coq_exp.coq_ToStSig ((((s, (fst c)), e0), (snd c)), e1))
        t22 e22
    in
    (((((((((s, (fst c)), e0), (snd c)), e1), ((snd (fst (fst (fst (fst a))))),
    (snd (fst (fst b))))), (e21, e22)), (snd (fst (fst a)))), e3), ((snd a),
    (snd b)))

  (** val simMap :
      coq_St -> coq_W -> (((coq_E0 * coq_E1) * coq_E2) * coq_E3) -> coq_X ->
      (((coq_R0 * coq_R1) * coq_R2) * coq_R3) ->
      ((coq_TE0 * coq_TE1) * coq_TE2) * coq_TE3 **)

  let simMap s w e x r =
    let r0 = fst (fst (fst r)) in
    let r2 = snd (fst r) in
    let r3 = snd r in
    let (p0, e3) = e in
    let (p1, e2) = p0 in
    let (e0, e1) = p1 in
    let a = Coq_exp.coq_P0 s r0 w in
    let b = Coq_exp.coq_P1 (a, e0) (fst (fst r)) w in
    (((Coq_exp.simMap s w (fst (fst e)) x (fst (fst r))),
    ((fst
       (Coq_sig5.simMap (Coq_exp.coq_ToStSig5 ((((s, (snd a)), e0), (snd b)), e1))
         (Coq_exp.coq_ToWitSig5 ((((s, (snd a)), e0), (snd b)), e1) (fst (fst r)) w)
         ((fst e2), e3) (Coq_exp.sig5Xcomp s x) ((fst r2), r3))),
    (Coq_sig.simMap (Coq_exp.coq_ToStSig ((((s, (snd a)), e0), (snd b)), e1))
      (Coq_exp.coq_ToWitSig ((((s, (snd a)), e0), (snd b)), e1) (fst (fst r)) w)
      (snd e2) (Coq_exp.sigXcomp s x) (snd r2)))),
    (snd
      (Coq_sig5.simMap (Coq_exp.coq_ToStSig5 ((((s, (snd a)), e0), (snd b)), e1))
        (Coq_exp.coq_ToWitSig5 ((((s, (snd a)), e0), (snd b)), e1) (fst (fst r)) w)
        ((fst e2), e3) (Coq_exp.sig5Xcomp s x) ((fst r2), r3))))

  (** val simMapInv :
      coq_St -> coq_W -> (((coq_E0 * coq_E1) * coq_E2) * coq_E3) -> coq_X ->
      (((coq_TE0 * coq_TE1) * coq_TE2) * coq_TE3) ->
      ((coq_R0 * coq_R1) * coq_R2) * coq_R3 **)

  let simMapInv s w e x t1 =
    let t2 = snd (fst t1) in
    let t3 = snd t1 in
    let (p0, e3) = e in
    let (p1, e2) = p0 in
    let (e0, e1) = p1 in
    let a = Coq_exp.simulator s (fst (fst t1)) (fst (fst e)) in
    let b = Coq_exp.simMapInv s w (fst (fst e)) x (fst (fst t1)) in
    ((b,
    ((fst
       (Coq_sig5.simMapInv
         (Coq_exp.coq_ToStSig5 ((((s, (fst a)), e0), (snd a)), e1))
         (Coq_exp.coq_ToWitSig5 ((((s, (fst a)), e0), (snd a)), e1) b w) ((fst e2),
         e3) (Coq_exp.sig5Xcomp s x) ((fst t2), t3))),
    (Coq_sig.simMapInv (Coq_exp.coq_ToStSig ((((s, (fst a)), e0), (snd a)), e1))
      (Coq_exp.coq_ToWitSig ((((s, (fst a)), e0), (snd a)), e1) b w) (snd e2)
      (Coq_exp.sigXcomp s x) (snd t2)))),
    (snd
      (Coq_sig5.simMapInv (Coq_exp.coq_ToStSig5 ((((s, (fst a)), e0), (snd a)), e1))
        (Coq_exp.coq_ToWitSig5 ((((s, (fst a)), e0), (snd a)), e1) b w) ((fst e2),
        e3) (Coq_exp.sig5Xcomp s x) ((fst t2), t3))))

  (** val coq_M0 : nat **)

  let coq_M0 =
    Coq_exp.coq_M0

  (** val coq_M1 : nat **)

  let coq_M1 =
    Coq_exp.coq_M1

  (** val coq_M2 : nat **)

  let coq_M2 =
    max Coq_sig5.coq_M0 Coq_sig.coq_M

  (** val coq_M3 : nat **)

  let coq_M3 =
    S (Nat.pred Coq_sig5.coq_M1)

  (** val getSig5Resp : coq_T t0 t0 -> Coq_sig5.coq_T t0 t0 **)

  let getSig5Resp t1 =
    vmap (fun g0 ->
      unzipLeft Coq_sig5.coq_M1
        (vcast (S (Nat.pred Coq_sig5.coq_M1)) g0 Coq_sig5.coq_M1)) Coq_sig5.coq_M0
      (vsub coq_M2 t1 O Coq_sig5.coq_M0)

  (** val getSig5Chal :
      (coq_E2 * coq_E3 t0) t0 -> (Coq_sig5.coq_E0 * Coq_sig5.coq_E1 t0) t0 **)

  let getSig5Chal e =
    vmap (fun g0 -> ((fst (fst g0)),
      (vcast (S (Nat.pred Coq_sig5.coq_M1)) (snd g0) Coq_sig5.coq_M1)))
      Coq_sig5.coq_M0 (vsub coq_M2 e O Coq_sig5.coq_M0)

  (** val getSigResp : coq_T t0 t0 -> Coq_sig.coq_T t0 **)

  let getSigResp t1 =
    vmap (fun g0 -> snd (hd (Nat.pred Coq_sig5.coq_M1) g0)) Coq_sig.coq_M
      (vsub coq_M2 t1 O Coq_sig.coq_M)

  (** val getSigChal : (coq_E2 * coq_E3 t0) t0 -> E.coq_G t0 **)

  let getSigChal e =
    vmap (fun g0 -> snd (fst g0)) Coq_sig.coq_M (vsub coq_M2 e O Coq_sig.coq_M)

  (** val extractor :
      coq_T t0 t0 t0 t0 -> (coq_E0 * (coq_E1 * (coq_E2 * coq_E3 t0) t0) t0) t0 ->
      coq_W **)

  let extractor t1 e =
    let w0 =
      vmap2 (fun t2 e1 ->
        vmap2 (fun t3 e3 ->
          Coq_sig5.extractor (getSig5Resp t3) (getSig5Chal (snd e3))) coq_M1 t2
          (snd e1)) coq_M0 t1 e
    in
    let w1 =
      vmap2 (fun c d ->
        vmap2 (fun a b -> Coq_sig.extractor (getSigResp a) (getSigChal (snd b)))
          coq_M1 c (snd d)) coq_M0 t1 e
    in
    Coq_exp.extractor (vmap2 (fun a b -> zip coq_M1 a b) coq_M0 w0 w1)
      (vmap (fun a -> ((fst a), (unzipLeft coq_M1 (snd a)))) coq_M0 e)

  (** val getSig5Com :
      (coq_C2 * coq_C3 t0) -> Coq_sig5.coq_C0 * Coq_sig5.coq_C1 t0 **)

  let getSig5Com c =
    ((fst (fst c)), (vsub coq_M2 (snd c) O Coq_sig5.coq_M0))

  (** val getSigCom : (coq_C2 * coq_C3 t0) -> Coq_sig.coq_C **)

  let getSigCom c =
    snd (fst c)
 end

module ShuffleArg =
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
 struct
  module G2 = GroupFromFieldIns(Field)

  module Chal2 = ProdGroupSigIns(G2)(Chal)

  (** val n : nat **)

  let n =
    S (S (S Hack.coq_N))

  (** val m : nat **)

  let m =
    S (S M.coq_N)

  module MP = MixablePropIns(Message)(Ciphertext)(Ring)(Field)(VS1)(MVS)(Coq_enc)

  module ALR = RingAddationalLemmas(Field)

  type coq_E0 = Chal.coq_G

  type coq_E1 = Chal2.coq_G

  (** val add0 : coq_E0 -> coq_E0 -> coq_E0 **)

  let add0 =
    Chal.coq_Gdot

  (** val zero0 : coq_E0 **)

  let zero0 =
    Chal.coq_Gone

  (** val inv0 : coq_E0 -> coq_E0 **)

  let inv0 =
    Chal.coq_Ginv

  (** val bool_eq0 : coq_E0 -> coq_E0 -> bool **)

  let bool_eq0 =
    Chal.coq_Gbool_eq

  (** val disjoint0 : coq_E0 -> coq_E0 -> bool **)

  let disjoint0 =
    Chal.coq_Gdisjoint

  (** val add1 : coq_E1 -> coq_E1 -> coq_E1 **)

  let add1 =
    Chal2.coq_Gdot

  (** val zero1 : coq_E1 **)

  let zero1 =
    Chal2.coq_Gone

  (** val inv1 : coq_E1 -> coq_E1 **)

  let inv1 =
    Chal2.coq_Ginv

  (** val bool_eq1 : coq_E1 -> coq_E1 -> bool **)

  let bool_eq1 =
    Chal2.coq_Gbool_eq

  (** val disjoint1 : coq_E1 -> coq_E1 -> bool **)

  let disjoint1 =
    Chal2.coq_Gdisjoint

  type coq_St =
    (((Coq_enc.coq_PK * Commitment.coq_G) * Coq_support.EPC.MoM.coq_VG) * Ciphertext.coq_G
    t0) * Ciphertext.coq_G t0

  type coq_W = Coq_support.Mo.Coq_mat.coq_VF t0 * Ring.coq_F t0

  (** val relReEnc :
      Coq_enc.coq_PK -> Ciphertext.coq_G t0 -> Ciphertext.coq_G t0 ->
      Coq_support.Mo.Coq_mat.coq_MF -> Ring.coq_F t0 -> bool **)

  let relReEnc pk e e' mat r =
    let e'' = Coq_support.MoC.coq_PexpMatrix (mul n m) e mat in
    bVforall3 (mul n m) (fun e0 e'0 r' -> Coq_support.ALenc.bIsReEnc pk e0 e'0 r')
      e'' e' r

  (** val coq_Rel : coq_St -> coq_W -> bool **)

  let coq_Rel s w =
    let (p0, cBar') = s in
    let (p1, cBar) = p0 in
    let (p2, _) = p1 in
    let (pk, _) = p2 in
    let (mat, rho) = w in
    (&&) (Coq_support.Mo.Coq_mat.coq_MFisPermutation (mul n m) mat)
      (relReEnc pk cBar cBar' mat rho)

  type coq_C0 = Coq_support.EPC.MoM.coq_VG

  type coq_C1 = Coq_support.EPC.MoM.coq_VG

  type coq_R0 = Coq_support.Mo.Coq_mat.coq_VF

  type coq_R1 = Coq_support.Mo.Coq_mat.coq_VF

  (** val coq_P0 : coq_St -> coq_R0 -> coq_W -> coq_St * coq_C0 **)

  let coq_P0 s r w =
    let (p0, _) = s in
    let (p1, _) = p0 in
    let (p2, hs) = p1 in
    let (_, h) = p2 in
    let (mat, _) = w in
    let aVec =
      Coq_support.Mo.Coq_mat.coq_MF_CVmult (mul n m) mat
        (vbuild (mul n m) (fun i _ ->
          Coq_support.Mo.Coq_mat.coq_VF_sum i (const Field.coq_Fone i)))
    in
    (s, (Coq_support.EPC.comEPCvec n m h hs aVec r))

  (** val coq_P1 :
      ((coq_St * coq_C0) * coq_E0) -> (coq_R0 * coq_R1) -> coq_W ->
      ((coq_St * coq_C0) * coq_E0) * coq_C1 **)

  let coq_P1 s r w =
    let (p0, e0) = s in
    let (s0, _) = p0 in
    let (p1, _) = s0 in
    let (p2, _) = p1 in
    let (p3, hs) = p2 in
    let (_, h) = p3 in
    let (mat, _) = w in
    let bVec =
      Coq_support.Mo.Coq_mat.coq_MF_CVmult (mul n m) mat
        (vbuild (mul n m) (fun i _ ->
          Coq_support.Mo.Coq_mat.coq_VF_prod i (const e0 i)))
    in
    (s, (Coq_support.EPC.comEPCvec n m h hs bVec (snd r)))

  (** val coq_ToStSig :
      ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> Coq_bGMultiArg.coq_St **)

  let coq_ToStSig = function
  | (p0, _) ->
    let (p1, c1) = p0 in
    let (p2, e0) = p1 in
    let (s0, _) = p2 in
    let (p3, cBar') = s0 in
    let (p4, cBar) = p3 in
    ((((p4, (vecToMat n m cBar')),
    (Coq_support.MoC.coq_VG_prod (mul n m)
      (Coq_support.MoC.coq_VG_Pexp (mul n m) cBar
        (Coq_support.Mo.coq_VandermondeCol (mul n m) e0)))), c1), Message.coq_Ggen)

  (** val coq_ToWitSig :
      ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) ->
      coq_W -> Coq_bGMultiArg.coq_W **)

  let coq_ToWitSig s r w =
    let (p0, _) = s in
    let (p1, _) = p0 in
    let (_, e0) = p1 in
    let mat = fst w in
    let rho = snd w in
    let bVec =
      Coq_support.Mo.Coq_mat.coq_MF_CVmult (mul n m) mat
        (vbuild (mul n m) (fun i _ ->
          Coq_support.Mo.Coq_mat.coq_VF_prod i (const e0 i)))
    in
    (((vecToMat n m bVec), (snd r)),
    (Coq_support.MoR.coq_VF_sum (mul n m)
      (Coq_support.MoR.coq_VF_neg (mul n m) (vmap2 MVS.op3 (mul n m) rho bVec))))

  (** val coq_ToStSig5 :
      ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> Coq_progArg2.coq_St **)

  let coq_ToStSig5 = function
  | (p0, e2) ->
    let (p1, c1) = p0 in
    let (p2, x) = p1 in
    let (s0, c0) = p2 in
    let (p3, _) = s0 in
    let (p4, _) = p3 in
    let (p5, hs) = p4 in
    let (_, h) = p5 in
    let y = fst e2 in
    let z0 = snd e2 in
    (((h, hs),
    (Coq_support.EPC.MoM.coq_VG_mult m
      (Coq_support.EPC.MoM.coq_VG_mult m (Coq_support.EPC.MoM.coq_VG_Sexp m c0 y) c1)
      (Coq_support.EPC.MoM.coq_VG_inv m
        (Coq_support.EPC.comEPC n m h hs (const (const z0 n) m)
          (Coq_support.Mo.Coq_mat.coq_VF_zero m))))),
    (Coq_support.Mo.Coq_mat.coq_VF_prod (mul n m)
      (vbuild (mul n m) (fun i _ ->
        Field.coq_Fadd
          (Field.coq_Fadd
            (Field.coq_Fmul y
              (Coq_support.Mo.Coq_mat.coq_VF_sum i (const Field.coq_Fone i)))
            (Coq_support.Mo.Coq_mat.coq_VF_prod i (const x i))) (Field.coq_Finv z0)))))

  (** val coq_ToWitSig5 :
      ((((coq_St * coq_C0) * coq_E0) * coq_C1) * coq_E1) -> (coq_R0 * coq_R1) ->
      coq_W -> Coq_progArg2.coq_W **)

  let coq_ToWitSig5 s r w =
    let (p0, e) = s in
    let (p1, _) = p0 in
    let (_, x) = p1 in
    let (y, z0) = e in
    let mat = fst w in
    let aVec =
      Coq_support.Mo.Coq_mat.coq_MF_CVmult (mul n m) mat
        (vbuild (mul n m) (fun i _ ->
          Coq_support.Mo.Coq_mat.coq_VF_sum i (const Field.coq_Fone i)))
    in
    let bVec =
      Coq_support.Mo.Coq_mat.coq_MF_CVmult (mul n m) mat
        (vbuild (mul n m) (fun i _ ->
          Coq_support.Mo.Coq_mat.coq_VF_prod i (const x i)))
    in
    let dVec =
      Coq_support.Mo.Coq_mat.coq_VF_sub (mul n m)
        (Coq_support.Mo.Coq_mat.coq_VF_add (mul n m)
          (Coq_support.Mo.Coq_mat.coq_VF_scale (mul n m) aVec y) bVec)
        (const z0 (mul n m))
    in
    ((vecToMat n m dVec),
    (Coq_support.Mo.Coq_mat.coq_VF_add m
      (Coq_support.Mo.Coq_mat.coq_VF_scale m (fst r) y) (snd r)))

  type coq_TE0 = Coq_support.Mo.Coq_mat.coq_VF

  type coq_TE1 = Coq_support.Mo.Coq_mat.coq_VF

  type coq_X =
    (Coq_support.Mo.Coq_mat.coq_VF * Coq_support.Mo.Coq_mat.coq_VF t0) * Ring.coq_F
    t0 t0

  (** val sigXcomp : coq_St -> coq_X -> Coq_bGMultiArg.coq_X **)

  let sigXcomp _ x =
    x

  (** val sig5Xcomp : coq_St -> coq_X -> Coq_progArg2.coq_X **)

  let sig5Xcomp _ x =
    fst (fst x)

  (** val simulator :
      coq_St -> (coq_TE0 * coq_TE1) -> (coq_E0 * coq_E1) -> coq_C0 * coq_C1 **)

  let simulator s t1 _ =
    let (p0, _) = s in
    let (p1, _) = p0 in
    let (p2, hs) = p1 in
    let (_, h) = p2 in
    ((Coq_support.EPC.comEPC n m h hs
       (const (Coq_support.Mo.Coq_mat.coq_VF_zero n) m) (fst t1)),
    (Coq_support.EPC.comEPC n m h hs
      (const (Coq_support.Mo.Coq_mat.coq_VF_zero n) m) (snd t1)))

  (** val simMap :
      coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_R0 * coq_R1) ->
      coq_TE0 * coq_TE1 **)

  let simMap _ w e x r =
    let (mat, _) = w in
    let aVec =
      Coq_support.Mo.Coq_mat.coq_MF_CVmult (mul n m) mat
        (vbuild (mul n m) (fun i _ ->
          Coq_support.Mo.Coq_mat.coq_VF_sum i (const Field.coq_Fone i)))
    in
    let bVec =
      Coq_support.Mo.Coq_mat.coq_MF_CVmult (mul n m) mat
        (vbuild (mul n m) (fun i _ ->
          Coq_support.Mo.Coq_mat.coq_VF_prod i (const (fst e) i)))
    in
    ((Coq_support.Mo.Coq_mat.coq_VF_add m (fst r)
       (vmap (fun a -> Coq_support.Mo.Coq_mat.coq_VF_inProd n (fst (fst x)) a) m
         (vecToMat n m aVec))),
    (Coq_support.Mo.Coq_mat.coq_VF_add m (snd r)
      (vmap (fun a -> Coq_support.Mo.Coq_mat.coq_VF_inProd n (fst (fst x)) a) m
        (vecToMat n m bVec))))

  (** val simMapInv :
      coq_St -> coq_W -> (coq_E0 * coq_E1) -> coq_X -> (coq_TE0 * coq_TE1) ->
      coq_R0 * coq_R1 **)

  let simMapInv _ w e x t1 =
    let (mat, _) = w in
    let aVec =
      Coq_support.Mo.Coq_mat.coq_MF_CVmult (mul n m) mat
        (vbuild (mul n m) (fun i _ ->
          Coq_support.Mo.Coq_mat.coq_VF_sum i (const Field.coq_Fone i)))
    in
    let bVec =
      Coq_support.Mo.Coq_mat.coq_MF_CVmult (mul n m) mat
        (vbuild (mul n m) (fun i _ ->
          Coq_support.Mo.Coq_mat.coq_VF_prod i (const (fst e) i)))
    in
    ((Coq_support.Mo.Coq_mat.coq_VF_sub m (fst t1)
       (vmap (fun a -> Coq_support.Mo.Coq_mat.coq_VF_inProd n (fst (fst x)) a) m
         (vecToMat n m aVec))),
    (Coq_support.Mo.Coq_mat.coq_VF_sub m (snd t1)
      (vmap (fun a -> Coq_support.Mo.Coq_mat.coq_VF_inProd n (fst (fst x)) a) m
        (vecToMat n m bVec))))

  (** val coq_M0 : nat **)

  let coq_M0 =
    mul n m

  (** val coq_M1 : nat **)

  let coq_M1 =
    S O

  (** val extractor :
      (Coq_progArg2.coq_W * Coq_bGMultiArg.coq_W) t0 t0 -> (coq_E0 * coq_E1 t0) t0
      -> coq_W **)

  let extractor w e =
    let mat =
      Coq_support.Mo.Coq_mat.matRecover (S
        (let rec add5 n0 m0 =
           match n0 with
           | O -> m0
           | S p0 -> S (add5 p0 m0)
         in add5 M.coq_N
              (let rec mul1 n0 m0 =
                 match n0 with
                 | O -> O
                 | S p0 -> add m0 (mul1 p0 m0)
               in mul1 (S (S Hack.coq_N)) m)))
        (matToVec Coq_prodArg.n m
          (vbuild m (fun i _ ->
            Coq_support.Mo.Coq_mat.coq_VF_scale Coq_prodArg.n
              (Coq_support.Mo.Coq_mat.coq_VF_add Coq_prodArg.n
                (Coq_support.Mo.Coq_mat.coq_VF_add Coq_prodArg.n
                  (vnth Coq_prodArg.m
                    (fst
                      (fst
                        (hd O
                          (hd (S
                            (let rec add5 n0 m0 =
                               match n0 with
                               | O -> m0
                               | S p0 -> S (add5 p0 m0)
                             in add5 M.coq_N
                                  (let rec mul1 n0 m0 =
                                     match n0 with
                                     | O -> O
                                     | S p0 -> add m0 (mul1 p0 m0)
                                   in mul1 (S (S Hack.coq_N)) m))) w)))) i)
                  (const
                    (snd
                      (hd O
                        (snd
                          (hd (S
                            (let rec add5 n0 m0 =
                               match n0 with
                               | O -> m0
                               | S p0 -> S (add5 p0 m0)
                             in add5 M.coq_N
                                  (let rec mul1 n0 m0 =
                                     match n0 with
                                     | O -> O
                                     | S p0 -> add m0 (mul1 p0 m0)
                                   in mul1 (S (S Hack.coq_N)) m))) e)))) n))
                (Coq_support.Mo.Coq_mat.coq_VF_neg Coq_bGMultiArg.n
                  (vnth Coq_bGMultiArg.m
                    (fst
                      (fst
                        (snd
                          (hd O
                            (hd (S
                              (let rec add5 n0 m0 =
                                 match n0 with
                                 | O -> m0
                                 | S p0 -> S (add5 p0 m0)
                               in add5 M.coq_N
                                    (let rec mul1 n0 m0 =
                                       match n0 with
                                       | O -> O
                                       | S p0 -> add m0 (mul1 p0 m0)
                                     in mul1 (S (S Hack.coq_N)) m))) w))))) i)))
              (Field.coq_FmulInv
                (fst
                  (hd O
                    (snd
                      (hd (S
                        (let rec add5 n0 m0 =
                           match n0 with
                           | O -> m0
                           | S p0 -> S (add5 p0 m0)
                         in add5 M.coq_N
                              (let rec mul1 n0 m0 =
                                 match n0 with
                                 | O -> O
                                 | S p0 -> add m0 (mul1 p0 m0)
                               in mul1 (S (S Hack.coq_N)) m))) e))))))))
    in
    (mat,
    (vmap (fun a ->
      Coq_support.MoR.coq_VF_sum coq_M0
        (vmap2 MVS.op3 coq_M0
          (vmap (fun a0 -> Ring.coq_Finv (snd (snd (hd O a0)))) coq_M0 w) a)) (S (S
      (let rec add5 n0 m0 =
         match n0 with
         | O -> m0
         | S p0 -> S (add5 p0 m0)
       in add5 M.coq_N
            (let rec mul1 n0 m0 =
               match n0 with
               | O -> O
               | S p0 -> add m0 (mul1 p0 m0)
             in mul1 (S (S Hack.coq_N)) m))))
      (Coq_support.Mo.Coq_mat.coq_MF_mult (S (S
        (let rec add5 n0 m0 =
           match n0 with
           | O -> m0
           | S p0 -> S (add5 p0 m0)
         in add5 M.coq_N
              (let rec mul1 n0 m0 =
                 match n0 with
                 | O -> O
                 | S p0 -> add m0 (mul1 p0 m0)
               in mul1 (S (S Hack.coq_N)) m)))) mat
        (Coq_support.Mo.coq_VandermondeInv coq_M0 (unzipLeft coq_M0 e)))))
 end

(** val pminusN : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let pminusN x y =
  match Coq_Pos.sub_mask x y with
  | Coq_Pos.IsPos k -> k
  | _ -> Big_int_Z.zero_big_int

(** val is_lt : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let is_lt n0 m0 =
  match Coq_Pos.compare n0 m0 with
  | Lt -> true
  | _ -> false

(** val div_eucl0 :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int **)

let rec div_eucl0 a b =
  (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
    (fun a' ->
    let (q0, r) = div_eucl0 a' b in
    ((fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
       (fun _ ->
       (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
         (fun _ -> (Big_int_Z.zero_big_int, Big_int_Z.zero_big_int))
         (fun r0 ->
         if is_lt
              ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
              r0) b
         then (Big_int_Z.zero_big_int,
                ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
                r0))
         else (Big_int_Z.unit_big_int,
                (pminusN
                  ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
                  r0) b)))
         r)
       (fun q1 ->
       (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
         (fun _ ->
         if is_lt Big_int_Z.unit_big_int b
         then ((Big_int_Z.mult_int_big_int 2 q1), Big_int_Z.unit_big_int)
         else (((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
                q1), Big_int_Z.zero_big_int))
         (fun r0 ->
         if is_lt
              ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
              r0) b
         then ((Big_int_Z.mult_int_big_int 2 q1),
                ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
                r0))
         else (((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
                q1),
                (pminusN
                  ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
                  r0) b)))
         r)
       q0))
    (fun a' ->
    let (q0, r) = div_eucl0 a' b in
    ((fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
       (fun _ ->
       (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
         (fun _ -> (Big_int_Z.zero_big_int, Big_int_Z.zero_big_int))
         (fun r0 ->
         if is_lt (Big_int_Z.mult_int_big_int 2 r0) b
         then (Big_int_Z.zero_big_int, (Big_int_Z.mult_int_big_int 2 r0))
         else (Big_int_Z.unit_big_int, (pminusN (Big_int_Z.mult_int_big_int 2 r0) b)))
         r)
       (fun q1 ->
       (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
         (fun _ -> ((Big_int_Z.mult_int_big_int 2 q1),
         Big_int_Z.zero_big_int))
         (fun r0 ->
         if is_lt (Big_int_Z.mult_int_big_int 2 r0) b
         then ((Big_int_Z.mult_int_big_int 2 q1), (Big_int_Z.mult_int_big_int 2 r0))
         else (((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
                q1), (pminusN (Big_int_Z.mult_int_big_int 2 r0) b)))
         r)
       q0))
    (fun _ ->
    if is_lt Big_int_Z.unit_big_int b
    then (Big_int_Z.zero_big_int, Big_int_Z.unit_big_int)
    else (Big_int_Z.unit_big_int, Big_int_Z.zero_big_int))
    a

(** val egcd_log2 :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    ((Big_int_Z.big_int * Big_int_Z.big_int) * Big_int_Z.big_int) option **)

let rec egcd_log2 a b c =
  let (q0, n0) = div_eucl0 a b in
  ((fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
     (fun _ -> Some ((Big_int_Z.zero_big_int, Big_int_Z.unit_big_int), b))
     (fun r ->
     let (q', n1) = div_eucl0 b r in
     ((fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
        (fun _ -> Some ((Big_int_Z.unit_big_int, (Z.opp (Z.of_N q0))), r))
        (fun r' ->
        (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
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
        n1))
     n0)

(** val egcd :
    Big_int_Z.big_int -> Big_int_Z.big_int ->
    (Big_int_Z.big_int * Big_int_Z.big_int) * Big_int_Z.big_int **)

let egcd a b =
  match egcd_log2 a b (Big_int_Z.mult_int_big_int 2 b) with
  | Some p0 -> p0
  | None ->
    ((Big_int_Z.unit_big_int, Big_int_Z.unit_big_int), Big_int_Z.unit_big_int)

(** val zegcd :
    Big_int_Z.big_int -> Big_int_Z.big_int ->
    (Big_int_Z.big_int * Big_int_Z.big_int) * Big_int_Z.big_int **)

let zegcd a b =
  (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
    (fun _ ->
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> ((Big_int_Z.zero_big_int, Big_int_Z.zero_big_int),
      Big_int_Z.zero_big_int))
      (fun _ -> ((Big_int_Z.zero_big_int, Big_int_Z.unit_big_int), b))
      (fun _ -> ((Big_int_Z.zero_big_int, (Big_int_Z.minus_big_int
      Big_int_Z.unit_big_int)), (Z.opp b)))
      b)
    (fun a0 ->
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> ((Big_int_Z.unit_big_int, Big_int_Z.zero_big_int), a))
      (fun b0 -> let (p0, w) = egcd a0 b0 in (p0, w))
      (fun b0 -> let (p0, w) = egcd a0 b0 in let (u, v) = p0 in ((u, (Z.opp v)), w))
      b)
    (fun a0 ->
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> (((Big_int_Z.minus_big_int Big_int_Z.unit_big_int),
      Big_int_Z.zero_big_int), (Z.opp a)))
      (fun b0 ->
      let (p0, w) = egcd a0 b0 in let (u, v) = p0 in (((Z.opp u), v), w))
      (fun b0 ->
      let (p0, w) = egcd a0 b0 in let (u, v) = p0 in (((Z.opp u), (Z.opp v)), w))
      b)
    a

type znz = Big_int_Z.big_int
  (* singleton inductive, whose constructor was mkznz *)

(** val val1 : Big_int_Z.big_int -> znz -> Big_int_Z.big_int **)

let val1 _ z0 =
  z0

(** val zero4 : Big_int_Z.big_int -> znz **)

let zero4 n0 =
  Z.modulo Big_int_Z.zero_big_int n0

(** val one0 : Big_int_Z.big_int -> znz **)

let one0 n0 =
  Z.modulo Big_int_Z.unit_big_int n0

(** val add4 : Big_int_Z.big_int -> znz -> znz -> znz **)

let add4 n0 v1 v2 =
  Z.modulo (Z.add (val1 n0 v1) (val1 n0 v2)) n0

(** val sub1 : Big_int_Z.big_int -> znz -> znz -> znz **)

let sub1 n0 v1 v2 =
  Z.modulo (Z.sub (val1 n0 v1) (val1 n0 v2)) n0

(** val mul0 : Big_int_Z.big_int -> znz -> znz -> znz **)

let mul0 n0 v1 v2 =
  Z.modulo (Z.mul (val1 n0 v1) (val1 n0 v2)) n0

(** val opp0 : Big_int_Z.big_int -> znz -> znz **)

let opp0 n0 v =
  Z.modulo (Z.opp (val1 n0 v)) n0

(** val inv4 : Big_int_Z.big_int -> znz -> znz **)

let inv4 p0 v =
  Z.modulo (fst (fst (zegcd (val1 p0 v) p0))) p0

(** val div0 : Big_int_Z.big_int -> znz -> znz -> znz **)

let div0 p0 v1 v2 =
  mul0 p0 v1 (inv4 p0 v2)

(** val p : Big_int_Z.big_int **)

let p = Big_int_Z.big_int_of_string "0xB7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF324E7738926CFBE5F4BF8D8D8C31D763DA06C80ABB1185EB4F7C7B5757F5958490CFD47D7C19BB42158D9554F7B46BCED55C4D79FD5F24D6613C31C3839A2DDF8A9A276BCFBFA1C877C56284DAB79CD4C2B3293D20E9E5EAF02AC60ACC93ED874422A52ECB238FEEE5AB6ADD835FD1A0753D0A8F78E537D2B95BB79D8DCAEC642C1E9F23B829B5C2780BF38737DF8BB300D01334A0D0BD8645CBFA73A6160FFE393C48CBBBCA060F0FF8EC6D31BEB5CCEED7F2F0BB088017163BC60DF45A0ECB1BCD289B06CBBFEA21AD08E1847F3F7378D56CED94640D6EF0D3D37BE69D0063"

(** val q : Big_int_Z.big_int **)

let q = Big_int_Z.big_int_of_string "0x5BF0A8B1457695355FB8AC404E7A79E3B1738B079C5A6D2B53C26C8228C867F799273B9C49367DF2FA5FC6C6C618EBB1ED0364055D88C2F5A7BE3DABABFACAC24867EA3EBE0CDDA10AC6CAAA7BDA35E76AAE26BCFEAF926B309E18E1C1CD16EFC54D13B5E7DFD0E43BE2B1426D5BCE6A6159949E9074F2F5781563056649F6C3A21152976591C7F772D5B56EC1AFE8D03A9E8547BC729BE95CADDBCEC6E57632160F4F91DC14DAE13C05F9C39BEFC5D98068099A50685EC322E5FD39D30B07FF1C9E2465DDE5030787FC763698DF5AE6776BF9785D84400B8B1DE306FA2D07658DE6944D8365DFF510D68470C23F9FB9BC6AB676CA3206B77869E9BDF34E8031"

type fp = znz

(** val fpMul : fp -> fp -> fp **)

let fpMul =
  mul0 p

(** val fpOne : fp **)

let fpOne =
  one0 p

type f = znz

(** val fadd : f -> f -> f **)

let fadd =
  add4 q

(** val fzero : f **)

let fzero =
  zero4 q

(** val fbool_eq_init : f -> f -> bool **)

let fbool_eq_init a b =
  Z.eqb (val1 q a) (val1 q b)

(** val fsub : f -> f -> f **)

let fsub =
  sub1 q

(** val finv : f -> f **)

let finv =
  opp0 q

(** val fmul : f -> f -> f **)

let fmul =
  mul0 q

(** val fone : f **)

let fone =
  one0 q

(** val fmulInv : f -> f **)

let fmulInv =
  inv4 q

(** val fdiv : f -> f -> f **)

let fdiv =
  div0 q

(** val binary_power_mult2 : fp -> Big_int_Z.big_int -> fp -> fp **)

let rec binary_power_mult2 x n0 acc =
  (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
    (fun w -> binary_power_mult2 (fpMul x x) w (fpMul acc x))
    (fun w -> binary_power_mult2 (fpMul x x) w acc)
    (fun _ -> fpMul x acc)
    n0

(** val binary_power2 : fp -> f -> fp **)

let binary_power2 x n0 =
  let e = val1 q n0 in
  ((fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
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
  one0 p

(** val gbool_eq_init : g -> g -> bool **)

let gbool_eq_init a b =
  Z.eqb (val1 p a) (val1 p b)

(** val ginv : g -> g **)

let ginv a =
  inv4 p a

(** val op0 : g -> f -> g **)

let op0 =
  binary_power2

module HeliosIACR2018G =
 struct
  type coq_G = g

  (** val coq_Gdot : g -> g -> g **)

  let coq_Gdot =
    gdot

  (** val coq_Gone : g **)

  let coq_Gone =
    gone

  (** val coq_Ggen : g **)

  let coq_Ggen =
     Big_int_Z.big_int_of_string "0xAF407708062F827D7CE58E8B47A82F8F55094570F6E2DB370F2E11E196C6469691BB7266D2DCA4C3340F8A93B1BABBEC80C7CCF3CA4B0163456D4BA2597690E0110139593003A0A433A82D94B4B1545F32F2969EDC301F7D6CE85C9C8423A3609121DB1306277EDED30BEC5DDB2622508D043EF456D14DEDECDF075B96139ECBB0B9A10069DC55E145A027AD348D6D965D751650D9DA6DE23665DCF43C25ACAD4725842E852F069EA61A54C2EB3344B3C6BBE7B7653342D04A320D1738C3232A089D8752DAEF68001E6DAEDF2A2D1F55E980C69D9231E6839913FD230C9A34BE4EBE29CD924F2828B5FC79FCA7C7886944523F05FA04EF6391D7C11B4262F541"


  (** val coq_Gbool_eq : g -> g -> bool **)

  let coq_Gbool_eq =
    gbool_eq_init

  (** val coq_Gdisjoint : g -> g -> bool **)

  let coq_Gdisjoint a b =
    negb (gbool_eq_init a b)

  (** val coq_Ginv : g -> g **)

  let coq_Ginv =
    ginv
 end

module HeliosIACR2018F =
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

module HeliosIACR2018VS =
 struct
  (** val op : g -> f -> g **)

  let op =
    op0
 end

module Ciphertext = DualGroupIns(HeliosIACR2018G)

module DVS =
 DualVectorSpaceIns(HeliosIACR2018G)(Ciphertext)(HeliosIACR2018F)(HeliosIACR2018VS)

module MVS = VectorSpaceModuleSameGroupInsIns(Ciphertext)(HeliosIACR2018F)(DVS)

module Chal = GroupFromRingIns(HeliosIACR2018F)

module L =
 struct
  (** val coq_N : nat **)

  let coq_N =
    S O
 end

module NGroupM = GroupNthIns(HeliosIACR2018G)(L)

module NGroupC = GroupNthIns(Ciphertext)(L)

module Nthring = NthRingIns(L)(HeliosIACR2018F)

module Nthvs = NthVectorSpaceIns(L)(Ciphertext)(HeliosIACR2018F)(NGroupC)(DVS)

module NthvsM =
 NthVectorSpaceIns(L)(HeliosIACR2018G)(HeliosIACR2018F)(NGroupM)(HeliosIACR2018VS)

module NthMVS =
 VectorSpaceModuleSameGroupNthStackIns(L)(Ciphertext)(HeliosIACR2018F)(HeliosIACR2018F)(DVS)(NGroupC)(Nthring)(Nthvs)(MVS)

module Enc =
 ExtendedElGamal(L)(HeliosIACR2018G)(HeliosIACR2018F)(HeliosIACR2018VS)(NGroupM)(Ciphertext)(DVS)(NGroupC)(Nthring)(Nthvs)(NthvsM)(NthMVS)

module N =
 struct
  (** val coq_N : nat **)

  let coq_N =
    S (S (S (S (S O))))
 end

module M =
 struct
  (** val coq_N : nat **)

  let coq_N =
    S (S (S (S (S (S O)))))
 end

module Support =
 BGSupportIns(NGroupM)(NGroupC)(HeliosIACR2018G)(Nthring)(HeliosIACR2018F)(HeliosIACR2018VS)(Nthvs)(NthMVS)(NthvsM)(N)(M)(Enc)

module BGZeroarg =
 BGZeroArgIns(NGroupM)(NGroupC)(HeliosIACR2018G)(Nthring)(HeliosIACR2018F)(HeliosIACR2018VS)(Nthvs)(Chal)(NthMVS)(NthvsM)(N)(M)(Enc)(Support)

module BGHadprodbase =
 BGHadProdIns(NGroupM)(NGroupC)(HeliosIACR2018G)(Nthring)(HeliosIACR2018F)(HeliosIACR2018VS)(Nthvs)(Chal)(NthMVS)(NthvsM)(N)(M)(Enc)(Support)(BGZeroarg)

module BGHadprod = SigmaPlusTo5simTofullIns(Chal)(BGZeroarg)(BGHadprodbase)

module Coq_sig5 = SigmaPlus5CompIns(Chal)(BGZeroarg)(BGHadprod)

module Coq_sig =
 BGSingleProdIns(HeliosIACR2018G)(HeliosIACR2018F)(HeliosIACR2018VS)(Chal)(N)

module Coq_prodarg =
 ProdArgIns(NGroupM)(NGroupC)(HeliosIACR2018G)(Nthring)(HeliosIACR2018F)(HeliosIACR2018VS)(Nthvs)(Chal)(NthMVS)(NthvsM)(N)(M)(Enc)(Support)(BGZeroarg)(BGHadprodbase)(BGHadprod)(Coq_sig5)(Coq_sig)

module Coq_prodarg2 = SigmaPlus5to5CompIns(Chal)(Coq_sig)(Coq_sig5)(Coq_prodarg)

module BGMultiarg =
 BGMultiArgIns(NGroupM)(NGroupC)(HeliosIACR2018G)(Nthring)(HeliosIACR2018F)(HeliosIACR2018VS)(Nthvs)(Chal)(NthMVS)(NthvsM)(N)(M)(Enc)(Support)

module SH =
 ShuffleArg(NGroupM)(NGroupC)(HeliosIACR2018G)(Nthring)(HeliosIACR2018F)(HeliosIACR2018VS)(Nthvs)(Chal)(NthMVS)(NthvsM)(N)(M)(Enc)(Support)(BGZeroarg)(BGHadprodbase)(BGHadprod)(Coq_sig5)(Coq_sig)(Coq_prodarg)(Coq_prodarg2)(BGMultiarg)

module ShuffleSigma = SigmaPlus5plus3to9Comp(Chal)(BGMultiarg)(Coq_prodarg2)(SH)
