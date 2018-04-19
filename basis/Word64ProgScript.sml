open preamble ml_translatorLib ml_progLib basisFunctionsLib
     CharProgTheory

val _ = new_theory "Word64Prog";

val _ = translation_extends "CharProg";

(* Word64 module -- translated *)

val _ = ml_prog_update (open_module "Word64");

val () = generate_sigs := true;

val _ = append_dec ``Dtabbrev unknown_loc [] "word" (Tapp [] TC_word64)``;
val _ = trans "fromInt" `n2w:num->word64`
val _ = trans "toInt" `w2n:word64->num`
val _ = trans "andb" `word_and:word64->word64->word64`;
val _ = trans "orb" `word_or:word64->word64->word64`;
val _ = trans "xorb" `word_xor:word64->word64->word64`;

val notb_eqn = Q.prove(`~(w:word64) = (w ⊕ 0xFFFFFFFFFFFFFFFFw)`,rw[]);
val _ = (next_ml_names := ["notb"]);
val _ = translate notb_eqn;

val _ = translate (shift_left_def
                     |> INST_TYPE [alpha|->``:64``]
                     |> PURE_REWRITE_RULE [dimindex_64]);
val _ = (next_ml_names := ["<<"]);
val _ = translate(shift_left_rwt |> INST_TYPE [alpha|->``:64``]);

val _ = translate (shift_right_def
                     |> INST_TYPE [alpha|->``:64``]
                     |> PURE_REWRITE_RULE [dimindex_64]);
val _ = (next_ml_names := [">>"]);
val _ = translate(shift_right_rwt |> INST_TYPE [alpha|->``:64``]);

val word64_msb_thm = Q.prove(
  `!w. word_msb (w:word64) = ((w && 0x8000000000000000w) = 0x8000000000000000w)`,
  wordsLib.WORD_DECIDE_TAC);

val _ = translate word64_msb_thm;

val arith_shift_right_ind = (
  arith_shift_right_ind |> INST_TYPE [alpha|->``:64``]
                        |> PURE_REWRITE_RULE [dimindex_64]
                        |> CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV))
  |> curry save_thm "arith_shift_right_ind";

val _ = add_preferred_thy "-";

val res = translate (arith_shift_right_def
                     |> INST_TYPE [alpha|->``:64``]
                     |> PURE_REWRITE_RULE [dimindex_64]
                     |> CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV));
  
val _ = (next_ml_names := ["~>>"]);
val _ = translate(arith_shift_right_rwt |> INST_TYPE [alpha|->``:64``]);

val sigs = module_signatures ["fromInt", "toInt", "andb", "orb", "xorb", "notb",
                              "~>>",">>","<<"];

val _ = ml_prog_update (close_module (SOME sigs));

val _ = export_theory();
