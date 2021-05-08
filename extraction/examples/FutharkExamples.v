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


Definition TT :=
  [ (<%% nat %%>, "u32")
  ; (<%% list %%>, "[]")
  ; (<%% @List.length %%>, "length")
  ; (<%% spec_float %%>, "f64")
  ; (<%% float_zero %%>, "0.0")
  ; (<%% SF64add %%>, "addF64")
  ; (<%% SF64div %%>, "divF64")
  ; (<%% nat_to_float %%>, "f64.i64")
  ; (<%% plus %%>, "addU32")
  ; (<%% List.fold_right %%>, "reduce")].

Definition TT_ctors :=
  [ ("O", "0") ].

Open Scope string.

Module Sum.

  Definition sum (xs: list nat) := fold_right plus 0 xs.

  Definition test_input := [4;3;2;1].
  Definition test_output := 10.
  Example sum_test : sum test_input = test_output. reflexivity. Qed.

  Compute string_of_list string_of_nat test_input.
  SearchPattern (list _ -> string).

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
     ; FTinput := "[10.5f64,20.5f64]" (* we can'r print float literals currently *)
     ; FToutput := "15.5f64" |}.

  MetaCoq Run (futhark_extraction "" f64_ops TT TT_ctors
                                  (Some futhark_average_test)
                                  average).

End Average.
