From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import FutharkExtract.
From ConCert.Extraction Require Import FutharkPretty.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Utils Require Import StringExtra.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Arith.
From Coq Require Import Floats.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import Kernames.
From MetaCoq.Template Require Import Loader.
From MetaCoq.Template Require Import TemplateMonad.
From MetaCoq Require Import monad_utils.
From MetaCoq Require Import utils.


Definition float_zero := S754_zero false.

Definition nat_to_float : nat -> spec_float :=
    fun n => match n with
          | O => float_zero
          | S _ => S754_finite false (Pos.of_nat n) 0
          end.

(** We remap Coq's types to the corresponding Futhark types.
 All required operations should be remapped as well. *)
Definition TT :=
  [ remap <%% nat %%> "u32"
  ; remap <%% plus %%> "addU32"
  ; remap <%% mult %%> "multU32"
  ; remap <%% Z %%> "i32"
  ; remap <%% Z.add %%> "addI32"
  ; remap <%% Z.mul %%> "multI32"
  ; remap <%% list %%> "[]"
  ; remap <%% @List.length %%> "length"
  ; remap <%% spec_float %%> "f64"
  ; remap <%% float_zero %%> "0.0"
  ; remap <%% SF64add %%> "addF64"
  ; remap <%% SF64div %%> "divF64"
  ; remap <%% nat_to_float %%> "f64.i64"
  ; remap <%% List.fold_right %%> "reduce"].

Definition TT_ctors :=
  [ ("O", "0u32")
  ; ("Z0", "0i32")].

Open Scope string.

Module Sum.

  (** A simple example of reduction *)

  Definition sum (xs: list nat) := fold_right plus 0 xs.

  Definition test_input := [4;3;2;1].
  Definition test_output := 10.

  Example sum_test : sum test_input = test_output. reflexivity. Qed.

  Definition futhark_sum_test :=
    {| FTname := "Sum test"
     ; FTinput := string_of_list (fun n => string_of_nat n ++ "u32") test_input
     ; FToutput := string_of_nat test_output ++ "u32" |}.

  MetaCoq Run (futhark_extraction "" u32_ops TT TT_ctors
                                  (Some futhark_sum_test)
                                  sum).

End Sum.

Module Average.

  (** An example from the fronpage of https://futhark-lang.org/ *)

  (** We use the [spec_float] type, which is a specification of IEEE754 floating-point numbers in Coq.
   That allows for proving properties related to the precision of operations on floats.*)

  Open Scope float.

  Definition average (xs: list spec_float) : spec_float :=
    SF64div (fold_right SF64add float_zero xs) (nat_to_float (length xs)).


  Example average_test : average (map Prim2SF [10.5; 20.5]) = Prim2SF 15.5.
  Proof. reflexivity. Qed.

  Definition futhark_average_test :=
    {| FTname := "Average test"
     ; FTinput := "[10.5f64,20.5f64]" (* we can't print float literals currently *)
     ; FToutput := "15.5f64" |}.

  MetaCoq Run (futhark_extraction "" f64_ops TT TT_ctors
                                  (Some futhark_average_test)
                                  average).

End Average.

Module Monoid.
  (** In this example, we provide a "safe" parallel reduction operation.
   It is safe in the sense that it requires an operation and a neutral element of a carrier type to be a monoid *)

  Class IsMonoid (M : Type) (op : M -> M -> M) (e : M) : Prop:=
    { munit_left : forall m, op e m = m;
      munit_right : forall m, op m e = m;
      massoc : forall m1 m2 m3, op m1 (op m2 m3) = op (op m1 m2) m3
    }.

  Definition parallel_reduce {A : Type} (op : A -> A -> A) (e : A) `{IsMonoid A op e} (xs : list A) :=
    fold_right op e xs.

  (** We cannot define [sum], because Coq cannot find appropriate instance *)
  Fail Definition sum (xs : list Z) := parallel_reduce Z.add 0%Z.

  (** So, we define the required instance *)
  #[refine]
  Instance Z_add_monoid : IsMonoid Z Z.add 0%Z :=
    {| munit_left := fun m => _;
       munit_right := _;
       massoc := _
    |}.
  * reflexivity.
  * apply Z.add_0_r.
  * intros;apply Z.add_assoc.
  Defined.

  (** Now, it works as expected *)
  Definition sum (xs : list Z) := parallel_reduce Z.add 0%Z.

  (** We tell our extraction that our parallel reduce is Futhark's reduce *)
  Definition TT_extra :=
    [ remap <%% @parallel_reduce %%> "reduce"].

  (** The witness of the instance [Z_add_monoid] is erased, because it's a proposition.
   So, we are left with an ordinary Futhark function *)
  MetaCoq Run (futhark_extraction "" i32_ops (TT ++ TT_extra) TT_ctors
                                  None
                                  sum).
  (* Geneterates the following function: *)
  (* let sum  = reduce addI32 0i32 *)
End Monoid.

Module DotProduct.

  Open Scope Z.

  Definition map2 {A B C : Type} (f : A -> B -> C) (xs : list A) (ys : list B)
             (p : length xs = length ys) : list C :=
    map (fun '(x,y) => f x y) (combine xs ys).

  Definition TT_extra :=
    [ remap <%% @map2 %%> "map2"
    ; remap <%% List.split %%> "unzip"].

  (** A function computing a dot product of two lists.
   It also takes a proof that the two lists have the same length.
   Eventually, we should be able to use vectors (sized lists) in such functions *)
  Definition dotprod (xs: list Z) (ys: list Z) (p : length xs = length ys):=
    fold_right Z.add 0%Z (map2 Z.mul xs ys p).

  (** The input is a list of pairs, which is basically N x 2 matrix.
   We take a dot product of the two vertical columns.
   We can prove that the sizes of the arguments to [dotprod] are of the same size *)
  Program Definition dotprod_list_of_pairs (xs : list (Z * Z)) :=
    let pair_of_lists := List.split xs in
    dotprod pair_of_lists.1 pair_of_lists.2 _.
  Next Obligation.
    intros. subst pair_of_lists.
    now rewrite split_length_l, split_length_r.
  Defined.

  Definition test_input :=
    [(1, 4)
    ;(2,-5)
    ;(3, 6)].

  Definition test_output := 12.

  Example dotprod_test : dotprod_list_of_pairs test_input = test_output. reflexivity. Qed.

  Definition futhark_dotprod_test :=
    {| FTname := "Dotproduct test"
     ; FTinput := string_of_list
                      (fun '(n,m) => parens false (string_of_Z n ++ "," ++ string_of_Z m)) test_input
     ; FToutput := string_of_Z test_output |}.


  (** Unfortunately, Futhark test syntax doesn't support tuples, so we don't generate a test *)
  MetaCoq Run (futhark_extraction "" i32_ops (TT ++ TT_extra) TT_ctors
                                  None
                                  dotprod_list_of_pairs).

End DotProduct.
