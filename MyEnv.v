Require Import List String.

Import ListNotations.

Definition env (A : Type) := list (string * A).

(** Lookup by variable name *)
Fixpoint lookup {A} (ρ : env A) (key : string) : option A :=
  match ρ with
  | [] => None
  | (nm,a) :: ρ' =>
    if (eqb nm key) then Some a else lookup ρ' key
  end.

Fixpoint lookup_with_ind_rec {A} (i : nat) (ρ : env A) (key : string) : option (nat * A) :=
  match ρ with
  | [] => None
  | (nm,a) :: ρ' =>
    if (eqb nm key) then Some (i,a)
    else lookup_with_ind_rec (1+i) ρ' key
  end.

Definition lookup_with_ind {A} (ρ : env A) (key : string)
  : option (nat * A) := lookup_with_ind_rec 0 ρ key.


  (** Lookup by index (similar to [List.nth_error], but defined by recursion on env *)
Fixpoint lookup_i {A} (ρ : env A) (i : nat) : option A :=
  match ρ with
  | [] => None
  | (nm,a) :: ρ' =>
    if (Nat.eqb i 0) then Some a else lookup_i ρ' (i-1)
  end.

  (** A value environment lookup: *)
Notation "ρ # '(' k ')'" := (lookup ρ k) (at level 10).
(** A value environment extension: *)
Notation "ρ # [ k ~> v ]" := ( (k,v) :: ρ) (at level 50).

Fixpoint remove_by_key {A} (key : string) (ρ : env A) : env A :=
  match ρ with
  | [] => []
  | (nm,a) :: ρ' => if (eqb nm key) then remove_by_key key ρ'
                  else (nm,a) :: (remove_by_key key ρ')
  end.