open BinNat
open Bool
open Datatypes

val zero : char

val one : char

val shift : bool -> char -> char

val eqb_spec : char -> char -> reflect

val ascii_of_pos : int -> char

val ascii_of_N : int -> char

val ascii_of_nat : nat -> char


