open Datatypes

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  match n with
  | O -> (match l with
          | [] -> default
          | x :: _ -> x)
  | S m -> (match l with
            | [] -> default
            | _ :: t -> nth m t default)

(** val nth_error : 'a1 list -> nat -> 'a1 option **)

let rec nth_error l = function
| O -> (match l with
        | [] -> None
        | x :: _ -> Some x)
| S n0 -> (match l with
           | [] -> None
           | _ :: l0 -> nth_error l0 n0)

(** val nth_default : 'a1 -> 'a1 list -> nat -> 'a1 **)

let nth_default default l n =
  match nth_error l n with
  | Some x -> x
  | None -> default

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t -> fold_left f t (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x :: tl ->
    (match l' with
     | [] -> []
     | y :: tl' -> (x, y) :: (combine tl tl'))

(** val firstn : nat -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  match n with
  | O -> []
  | S n0 -> (match l with
             | [] -> []
             | a :: l0 -> a :: (firstn n0 l0))

(** val skipn : nat -> 'a1 list -> 'a1 list **)

let rec skipn n l =
  match n with
  | O -> l
  | S n0 -> (match l with
             | [] -> []
             | _ :: l0 -> skipn n0 l0)

(** val repeat : 'a1 -> nat -> 'a1 list **)

let rec repeat x = function
| O -> []
| S k -> x :: (repeat x k)
