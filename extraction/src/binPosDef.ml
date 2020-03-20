open Datatypes
open Decimal
open Nat0

module Pos =
 struct
  type t = int

  (** val succ : int -> int **)

  let rec succ x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->2*p) (succ p))
      (fun p -> (fun p->1+2*p) p)
      (fun _ -> (fun p->2*p) 1)
      x

  (** val add : int -> int -> int **)

  let rec add x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun q -> (fun p->2*p) (add p q))
        (fun _ -> (fun p->1+2*p) p)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (succ q))
        (fun q -> (fun p->1+2*p) q)
        (fun _ -> (fun p->2*p) 1)
        y)
      x

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val pred : int -> int **)

  let pred x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->2*p) p)
      (fun p -> pred_double p)
      (fun _ -> 1)
      x

  (** val pred_N : int -> int **)

  let pred_N x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> ((fun p->2*p) p))
      (fun p -> (pred_double p))
      (fun _ -> 0)
      x

  type mask =
  | IsNul
  | IsPos of int
  | IsNeg

  (** val mask_rect : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1

  (** val mask_rec : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos 1
  | IsPos p -> IsPos ((fun p->1+2*p) p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos ((fun p->2*p) p)
  | x0 -> x0

  (** val double_pred_mask : int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> IsPos ((fun p->2*p) ((fun p->2*p) p)))
      (fun p -> IsPos ((fun p->2*p) (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val pred_mask : mask -> mask **)

  let pred_mask = function
  | IsPos q ->
    ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun _ -> IsPos (pred q))
       (fun _ -> IsPos (pred q))
       (fun _ -> IsNul)
       q)
  | _ -> IsNeg

  (** val sub_mask : int -> int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask p q))
        (fun q -> succ_double_mask (sub_mask p q))
        (fun _ -> IsPos ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : int -> int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask_carry p q))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val sub : int -> int -> int **)

  let sub x y =
    match sub_mask x y with
    | IsPos z -> z
    | _ -> 1

  (** val mul : int -> int -> int **)

  let rec mul x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> add y ((fun p->2*p) (mul p y)))
      (fun p -> (fun p->2*p) (mul p y))
      (fun _ -> y)
      x

  (** val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 **)

  let rec iter f x n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n

  (** val pow : int -> int -> int **)

  let pow x =
    iter (mul x) 1

  (** val square : int -> int **)

  let rec square p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> (fun p->1+2*p) ((fun p->2*p)
      (add (square p0) p0)))
      (fun p0 -> (fun p->2*p) ((fun p->2*p) (square p0)))
      (fun _ -> 1)
      p

  (** val div2 : int -> int **)

  let div2 p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> p0)
      (fun p0 -> p0)
      (fun _ -> 1)
      p

  (** val div2_up : int -> int **)

  let div2_up p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> succ p0)
      (fun p0 -> p0)
      (fun _ -> 1)
      p

  (** val size_nat : int -> nat **)

  let rec size_nat p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> S (size_nat p0))
      (fun p0 -> S (size_nat p0))
      (fun _ -> S O)
      p

  (** val size : int -> int **)

  let rec size p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> succ (size p0))
      (fun p0 -> succ (size p0))
      (fun _ -> 1)
      p

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont r x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> compare_cont r p q)
        (fun q -> compare_cont Gt p q)
        (fun _ -> Gt)
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> compare_cont Lt p q)
        (fun q -> compare_cont r p q)
        (fun _ -> Gt)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> Lt)
        (fun _ -> Lt)
        (fun _ -> r)
        y)
      x

  (** val compare : int -> int -> comparison **)

  let compare =
    compare_cont Eq

  (** val min : int -> int -> int **)

  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p

  (** val max : int -> int -> int **)

  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val sqrtrem_step :
      (int -> int) -> (int -> int) -> (int * mask) -> int * mask **)

  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = (fun p->1+2*p) ((fun p->2*p) s) in
       let r' = g (f r) in
       if leb s' r'
       then (((fun p->1+2*p) s), (sub_mask r' s'))
       else (((fun p->2*p) s), (IsPos r'))
     | _ ->
       (((fun p->2*p) s),
         (sub_mask (g (f 1)) ((fun p->2*p) ((fun p->2*p) 1)))))

  (** val sqrtrem : int -> int * mask **)

  let rec sqrtrem p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->1+2*p) x) (fun x -> (fun p->1+2*p) x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->2*p) x) (fun x -> (fun p->1+2*p) x)
          (sqrtrem p1))
        (fun _ -> (1, (IsPos ((fun p->2*p) 1))))
        p0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->1+2*p) x) (fun x -> (fun p->2*p) x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->2*p) x) (fun x -> (fun p->2*p) x)
          (sqrtrem p1))
        (fun _ -> (1, (IsPos 1)))
        p0)
      (fun _ -> (1, IsNul))
      p

  (** val sqrt : int -> int **)

  let sqrt p =
    fst (sqrtrem p)

  (** val gcdn : nat -> int -> int -> int **)

  let rec gcdn n a b =
    match n with
    | O -> 1
    | S n0 ->
      ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
         (fun a' ->
         (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
           (fun b' ->
           match compare a' b' with
           | Eq -> a
           | Lt -> gcdn n0 (sub b' a') a
           | Gt -> gcdn n0 (sub a' b') b)
           (fun b0 -> gcdn n0 a b0)
           (fun _ -> 1)
           b)
         (fun a0 ->
         (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
           (fun _ -> gcdn n0 a0 b)
           (fun b0 -> (fun p->2*p) (gcdn n0 a0 b0))
           (fun _ -> 1)
           b)
         (fun _ -> 1)
         a)

  (** val gcd : int -> int -> int **)

  let gcd a b =
    gcdn (Nat0.add (size_nat a) (size_nat b)) a b

  (** val ggcdn : nat -> int -> int -> int * (int * int) **)

  let rec ggcdn n a b =
    match n with
    | O -> (1, (a, b))
    | S n0 ->
      ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
         (fun a' ->
         (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
           (fun b' ->
           match compare a' b' with
           | Eq -> (a, (1, 1))
           | Lt ->
             let (g, p) = ggcdn n0 (sub b' a') a in
             let (ba, aa) = p in (g, (aa, (add aa ((fun p->2*p) ba))))
           | Gt ->
             let (g, p) = ggcdn n0 (sub a' b') b in
             let (ab, bb) = p in (g, ((add bb ((fun p->2*p) ab)), bb)))
           (fun b0 ->
           let (g, p) = ggcdn n0 a b0 in
           let (aa, bb) = p in (g, (aa, ((fun p->2*p) bb))))
           (fun _ -> (1, (a, 1)))
           b)
         (fun a0 ->
         (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
           (fun _ ->
           let (g, p) = ggcdn n0 a0 b in
           let (aa, bb) = p in (g, (((fun p->2*p) aa), bb)))
           (fun b0 ->
           let (g, p) = ggcdn n0 a0 b0 in (((fun p->2*p) g), p))
           (fun _ -> (1, (a, 1)))
           b)
         (fun _ -> (1, (1, b)))
         a)

  (** val ggcd : int -> int -> int * (int * int) **)

  let ggcd a b =
    ggcdn (Nat0.add (size_nat a) (size_nat b)) a b

  (** val coq_Nsucc_double : int -> int **)

  let coq_Nsucc_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val coq_Ndouble : int -> int **)

  let coq_Ndouble n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n

  (** val coq_lor : int -> int -> int **)

  let rec coq_lor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun _ -> p)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->2*p) (coq_lor p0 q0))
        (fun _ -> (fun p->1+2*p) p0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> q)
        (fun q0 -> (fun p->1+2*p) q0)
        (fun _ -> q)
        q)
      p

  (** val coq_land : int -> int -> int **)

  let rec coq_land p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 1)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 1)
        (fun _ -> 0)
        (fun _ -> 1)
        q)
      p

  (** val ldiff : int -> int -> int **)

  let rec ldiff p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Nsucc_double (ldiff p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun _ -> p)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 0)
        (fun _ -> 1)
        (fun _ -> 0)
        q)
      p

  (** val coq_lxor : int -> int -> int **)

  let rec coq_lxor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun _ -> ((fun p->1+2*p) p0))
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> ((fun p->2*p) q0))
        (fun q0 -> ((fun p->1+2*p) q0))
        (fun _ -> 0)
        q)
      p

  (** val shiftl_nat : int -> nat -> int **)

  let rec shiftl_nat p = function
  | O -> p
  | S n0 -> (fun p->2*p) (shiftl_nat p n0)

  (** val shiftr_nat : int -> nat -> int **)

  let rec shiftr_nat p = function
  | O -> p
  | S n0 -> div2 (shiftr_nat p n0)

  (** val shiftl : int -> int -> int **)

  let shiftl p n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> p)
      (fun n0 -> iter (fun x -> (fun p->2*p) x) p n0)
      n

  (** val shiftr : int -> int -> int **)

  let shiftr p n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> p)
      (fun n0 -> iter div2 p n0)
      n

  (** val testbit_nat : int -> nat -> bool **)

  let rec testbit_nat p n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      match n with
      | O -> true
      | S n' -> testbit_nat p0 n')
      (fun p0 ->
      match n with
      | O -> false
      | S n' -> testbit_nat p0 n')
      (fun _ -> match n with
                | O -> true
                | S _ -> false)
      p

  (** val testbit : int -> int -> bool **)

  let rec testbit p n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun n0 -> testbit p0 (pred_N n0))
        n)
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> false)
        (fun n0 -> testbit p0 (pred_N n0))
        n)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun _ -> false)
        n)
      p

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> nat **)

  let to_nat x =
    iter_op Nat0.add x (S O)

  (** val of_nat : nat -> int **)

  let rec of_nat = function
  | O -> 1
  | S x -> (match x with
            | O -> 1
            | S _ -> succ (of_nat x))

  (** val of_succ_nat : nat -> int **)

  let rec of_succ_nat = function
  | O -> 1
  | S x -> succ (of_succ_nat x)

  (** val of_uint_acc : uint -> int -> int **)

  let rec of_uint_acc d acc =
    match d with
    | Nil -> acc
    | D0 l ->
      of_uint_acc l (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc)
    | D1 l ->
      of_uint_acc l
        (add 1 (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D2 l ->
      of_uint_acc l
        (add ((fun p->2*p) 1)
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D3 l ->
      of_uint_acc l
        (add ((fun p->1+2*p) 1)
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D4 l ->
      of_uint_acc l
        (add ((fun p->2*p) ((fun p->2*p) 1))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D5 l ->
      of_uint_acc l
        (add ((fun p->1+2*p) ((fun p->2*p) 1))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D6 l ->
      of_uint_acc l
        (add ((fun p->2*p) ((fun p->1+2*p) 1))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D7 l ->
      of_uint_acc l
        (add ((fun p->1+2*p) ((fun p->1+2*p) 1))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D8 l ->
      of_uint_acc l
        (add ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | D9 l ->
      of_uint_acc l
        (add ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))

  (** val of_uint : uint -> int **)

  let rec of_uint = function
  | Nil -> 0
  | D0 l -> of_uint l
  | D1 l -> (of_uint_acc l 1)
  | D2 l -> (of_uint_acc l ((fun p->2*p) 1))
  | D3 l -> (of_uint_acc l ((fun p->1+2*p) 1))
  | D4 l -> (of_uint_acc l ((fun p->2*p) ((fun p->2*p) 1)))
  | D5 l -> (of_uint_acc l ((fun p->1+2*p) ((fun p->2*p) 1)))
  | D6 l -> (of_uint_acc l ((fun p->2*p) ((fun p->1+2*p) 1)))
  | D7 l -> (of_uint_acc l ((fun p->1+2*p) ((fun p->1+2*p) 1)))
  | D8 l -> (of_uint_acc l ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
  | D9 l -> (of_uint_acc l ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))

  (** val of_int : unit -> int option **)

  let of_int d =
    (fun _ _ _ -> assert false)
      (fun d0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> None)
        (fun p -> Some p)
        (of_uint d0))
      (fun _ -> None)
      d

  (** val to_little_uint : int -> uint **)

  let rec to_little_uint p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> Little.succ_double (to_little_uint p0))
      (fun p0 -> Little.double (to_little_uint p0))
      (fun _ -> D1 Nil)
      p

  (** val to_uint : int -> uint **)

  let to_uint p =
    rev (to_little_uint p)

  (** val to_int : int -> unit **)

  let to_int n =
    (fun _ -> ()) (to_uint n)
 end
