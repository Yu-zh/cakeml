(*Generated by Lem from simpleIO.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasivesTheory lem_pervasives_extraTheory libTheory ffiTheory;

val _ = numLib.prefer_num();



val _ = new_theory "simpleIO"

(*open import Pervasives*)
(*open import Pervasives_extra*)
(*open import Lib*)
(*open import Ffi*)

val _ = Hol_datatype `
 simpleIO = <| input :  word8 llist; output :  word8 llist |>`;


(*val isEof : oracle_function simpleIO*)
val _ = Define `
 (isEof st conf input=  
 ((case input of
    [] => Oracle_final FFI_failed
  | x::xs => Oracle_return st ((if st.input = LNIL then n2w (( 1 : num)) else n2w (( 0 : num)))::xs)
  )))`;


(*val getChar : oracle_function simpleIO*)
val _ = Define `
 (getChar st conf input=  
 ((case input of
    [] => Oracle_final FFI_failed
  | x::xs =>
      (case LHD st.input of
        SOME y => Oracle_return (( st with<| input := (THE (LTL st.input)) |>)) (y::xs)
      | _ => Oracle_final FFI_failed
      )
  )))`;


(*val putChar : oracle_function simpleIO*)
val _ = Define `
 (putChar st conf input=  
 ((case input of
    [] => Oracle_final FFI_failed
  | x::_ => Oracle_return (( st with<| output := (LCONS x st.output) |>)) input
  )))`;


(*val exit : oracle_function simpleIO*)
val _ = Define `
 (exit st conf input=  Oracle_final FFI_diverged)`;


(*val simpleIO_oracle : oracle simpleIO*)
val _ = Define `
 (simpleIO_oracle s st conf input=  
 (if s = "isEof" then
    isEof st conf input
  else if s = "getChar" then
    getChar st conf input
  else if s = "putChar" then
    putChar st conf input
  else if s = "exit" then
    exit st conf input
  else
    Oracle_final FFI_failed))`;

val _ = export_theory()

