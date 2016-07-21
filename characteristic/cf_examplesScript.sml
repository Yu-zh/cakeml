open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib ml_translatorTheory
open semanticPrimitivesTheory ConseqConv
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfHeapsLib
open cfAppTheory cfTheory
open cfTacticsTheory cfTacticsBaseLib cfTacticsLib

val initial_prog = EVAL ``basis_program`` |> concl |> rand
val initial_st = ml_progLib.add_prog initial_prog pick_name ml_progLib.init_state

val example_let0 = parse ``nTopLevelDecs`` ``ptree_TopLevelDecs``
  "fun example_let0 n = let val a = 3; in a end"

val st0 = ml_progLib.add_prog example_let0 pick_name initial_st

val example_let0_spec = Q.prove (
  `!nv. app (p:'ffi ffi_proj) ^(fetch_v "example_let0" st0) [nv]
          emp
          (\v. cond (INT 3 v))`,
  xcf st0 "example_let0" \\ xlet `\v. cond (INT 3 v)` `a`
  THEN1 (xret \\ hsimpl \\ fs [INT_def]) \\
  xret \\ hsimpl \\ fs []
)

val example_let1 = parse ``nTopLevelDecs`` ``ptree_TopLevelDecs``
  "fun example_let1 _ = let val a = (); in a end"

val st1 = ml_progLib.add_prog example_let1 pick_name initial_st

val example_let1_spec = Q.prove (
  `!uv. app (p:'ffi ffi_proj) ^(fetch_v "example_let1" st1) [uv]
          emp
          (\v. cond (UNIT_TYPE () v))`,
  xcf st1 "example_let1" \\ xlet `\v. cond (UNIT_TYPE () v)` `a`
  THEN1 (xret \\ hsimpl \\ fs [UNIT_TYPE_def]) \\
  xret \\ hsimpl \\ fs []
)

val example_let2 = parse ``nTopLevelDecs`` ``ptree_TopLevelDecs``
  "fun example_let2 u = let val a = u; in a end"

val st2 = ml_progLib.add_prog example_let2 pick_name initial_st

val example_let2_spec = Q.prove (
  `!uv. app (p:'ffi ffi_proj) ^(fetch_v "example_let2" st2) [uv]
          emp
          (\v. cond (v = uv))`,
  xcf st2 "example_let2" \\ xlet `\v. cond (v = uv)` `a`
  THEN1 (xret \\ hsimpl) \\
  xret \\ hsimpl
)
