(*Generated by Lem from intLang.lem.*)
open bossLib Theory Parse res_quanTheory
open fixedPointTheory finite_mapTheory listTheory pairTheory pred_setTheory
open integerTheory set_relationTheory sortingTheory stringTheory wordsTheory

val _ = numLib.prefer_num();



open CompilerPrimitivesTheory BytecodeTheory CompilerLibTheory SemanticPrimitivesTheory AstTheory LibTheory

val _ = new_theory "IntLang"

(* Intermediate language *)

(*open CompilerLib*)
(*open Ast*)
(*open SemanticPrimitives*)

(* Syntax *)

(* pure applicative primitives with bytecode counterparts *)
val _ = Hol_datatype `
 Cprim1 = CRef | CDer`;

val _ = Hol_datatype `
 Cprim2 = CAdd | CSub | CMul | CDiv | CMod | CLt | CEq`;


val _ = Hol_datatype `
 Cpat =
    CPvar
  | CPlit of lit
  | CPcon of num => Cpat list
  | CPref of Cpat`;


(* values in compile-time environment *)
val _ = Hol_datatype `
 ccbind = CCArg of num | CCRef of num | CCEnv of num`;

val _ = Hol_datatype `
 ctbind = CTLet of num | CTEnv of ccbind`;

(* CTLet n means stack[sz - n]
   CCArg n means stack[sz + n]
   CCEnv n means El n of the environment, which is at stack[sz]
   CCRef n means El n of the environment, but it's a ref pointer *)
val _ = type_abbrev( "ccenv" , ``: ccbind list``);
val _ = type_abbrev( "ceenv" , ``: num list # num list``); (* indices of recursive closures, free variables *)
val _ = type_abbrev( "ctenv" , ``: ctbind list``);

val _ = Hol_datatype `
 Cexp =
    CRaise of error
  | CHandle of Cexp => Cexp
  | CVar of num
  | CLit of lit
  | CCon of num => Cexp list
  | CTagEq of Cexp => num
  | CProj of Cexp => num
  | CLet of Cexp => Cexp
  | CLetrec of (( (num # (ccenv # ceenv))option) # (num # Cexp)) list => Cexp
  | CFun of (( (num # (ccenv # ceenv))option) # (num # Cexp))
  | CCall of Cexp => Cexp list
  | CPrim1 of Cprim1 => Cexp
  | CPrim2 of Cprim2 => Cexp => Cexp
  | CUpd of Cexp => Cexp
  | CIf of Cexp => Cexp => Cexp`;


val _ = type_abbrev( "def" , ``: (( (num # (ccenv # ceenv))option) # (num # Cexp))``);

(* Semantics *)

val _ = Hol_datatype `
 Cv =
    CLitv of lit
  | CConv of num => Cv list
  | CRecClos of Cv list => def list => num
  | CLoc of num`;


 val no_closures_defn = Hol_defn "no_closures" `

(no_closures (CLitv _) = T)
/\
(no_closures (CConv _ vs) = ( EVERY no_closures vs))
/\
(no_closures (CRecClos _ _ _) = F)
/\
(no_closures (CLoc _) = T)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn no_closures_defn;

 val doPrim2_def = Define `

(doPrim2 b ty op (CLitv (IntLit x)) (CLitv (IntLit y)) =  
(if b /\ (y = i0) then Rerr (Rraise Div_error)
  else Rval (CLitv (ty (op x y)))))
/\
(doPrim2 _ _ _ _ _ = (Rerr Rtype_error))`;


 val CevalPrim2_def = Define `

(CevalPrim2 CAdd = ( doPrim2 F IntLit int_add))
/\
(CevalPrim2 CSub = ( doPrim2 F IntLit (int_sub)))
/\
(CevalPrim2 CMul = ( doPrim2 F IntLit int_mul))
/\
(CevalPrim2 CDiv = ( doPrim2 T IntLit int_div))
/\
(CevalPrim2 CMod = ( doPrim2 T IntLit int_mod))
/\
(CevalPrim2 CLt = ( doPrim2 F Bool int_lt))
/\
(CevalPrim2 CEq = (\ v1 v2 .
  if no_closures v1 /\ no_closures v2
  then Rval (CLitv (Bool (v1 = v2)))
  else Rerr Rtype_error))`;


 val CevalUpd_def = Define `

(CevalUpd s (CLoc n) (v:Cv) =  
(if n < LENGTH s
  then (LUPDATE v n s, Rval (CLitv Unit))
  else (s, Rerr Rtype_error)))
/\
(CevalUpd s _ _ = (s, Rerr Rtype_error))`;


 val CevalPrim1_def = Define `

(CevalPrim1 CRef s v = ((s ++[v]), Rval (CLoc ( LENGTH s))))
/\
(CevalPrim1 CDer s (CLoc n) =
  (s, (case el_check n s of
        NONE => Rerr Rtype_error
      | SOME v => Rval v
      )))
/\
(CevalPrim1 _ s _ = (s, Rerr Rtype_error))`;


val _ = Hol_reln `
(! s env error.
T
==>
Cevaluate s env (CRaise error) (s, Rerr (Rraise error)))

/\
(! s1 env e1 e2 s2 v.
(Cevaluate s1 env e1 (s2, Rval v))
==>
Cevaluate s1 env (CHandle e1 e2) (s2, Rval v))
/\
(! s1 env e1 e2 s2 n res.
(Cevaluate s1 env e1 (s2, Rerr (Rraise (Int_error n))) /\
Cevaluate s2 ((CLitv (IntLit n)) ::env) e2 res)
==>
Cevaluate s1 env (CHandle e1 e2) res)
/\
(! s1 env e1 e2 s2 err.
(Cevaluate s1 env e1 (s2, Rerr err) /\
(! n. ~  (err = Rraise (Int_error n))))
==>
Cevaluate s1 env (CHandle e1 e2) (s2, Rerr err))

/\
(! s env n.
(n < LENGTH env)
==>
Cevaluate s env (CVar n) (s, Rval ( EL  n  env)))

/\
(! s env l.
T
==>
Cevaluate s env (CLit l) (s, Rval (CLitv l)))

/\
(! s env n es s' vs.
(Cevaluate_list s env es (s', Rval vs))
==>
Cevaluate s env (CCon n es) (s', Rval (CConv n vs)))
/\
(! s env n es s' err.
(Cevaluate_list s env es (s', Rerr err))
==>
Cevaluate s env (CCon n es) (s', Rerr err))

/\
(! s env e n m s' vs.
(Cevaluate s env e (s', Rval (CConv m vs)))
==>
Cevaluate s env (CTagEq e n) (s', Rval (CLitv (Bool (n = m)))))
/\
(! s env e n s' err.
(Cevaluate s env e (s', Rerr err))
==>
Cevaluate s env (CTagEq e n) (s', Rerr err))

/\
(! s env e n m s' vs.
(Cevaluate s env e (s', Rval (CConv m vs)) /\
n < LENGTH vs)
==>
Cevaluate s env (CProj e n) (s', Rval ( EL  n  vs)))
/\
(! s env e n s' err.
(Cevaluate s env e (s', Rerr err))
==>
Cevaluate s env (CProj e n) (s', Rerr err))

/\
(! s env e b s' v r.
(Cevaluate s env e (s', Rval v) /\
Cevaluate s' (v ::env) b r)
==>
Cevaluate s env (CLet e b) r)
/\
(! s env e b s' err.
(Cevaluate s env e (s', Rerr err))
==>
Cevaluate s env (CLet e b) (s', Rerr err))

/\
(! s env defs b r.
(Cevaluate s
  ( APPEND ( GENLIST (CRecClos env defs) ( LENGTH defs)) env)
  b r)
==>
Cevaluate s env (CLetrec defs b) r)

/\
(! s env def.
T
==>
Cevaluate s env (CFun def) (s, Rval (CRecClos env [def] 0)))

/\
(! s env e es s' cenv defs n def b env'' s'' vs r.
(Cevaluate s env e (s', Rval (CRecClos cenv defs n)) /\
n < LENGTH defs /\ ( EL  n  defs = def) /\
Cevaluate_list s' env es (s'', Rval vs) /\
((T, LENGTH vs,env'',b) =
  (case def of
    (NONE,(k,b)) =>
    (T
    ,k
    ,(( REVERSE vs) ++(( GENLIST (CRecClos cenv defs) ( LENGTH defs)) ++cenv))
    ,b)
  | (SOME (_,(_,(recs,envs))),(k,b)) =>
    ( ( EVERY (\ n . n < LENGTH cenv) envs /\ EVERY (\ n . n < LENGTH defs) recs)
    ,k
    , ( REVERSE vs ++(((CRecClos cenv defs n) :: MAP (CRecClos cenv defs) recs) ++ MAP (\n. EL n  cenv) envs))
    ,b)
  )) /\
Cevaluate s'' env'' b r)
==>
Cevaluate s env (CCall e es) r)
/\
(! s env e s' v es s'' err.
(Cevaluate s env e (s', Rval v) /\
Cevaluate_list s' env es (s'', Rerr err))
==>
Cevaluate s env (CCall e es) (s'', Rerr err))

/\
(! s env e es s' err.
(Cevaluate s env e (s', Rerr err))
==>
Cevaluate s env (CCall e es) (s', Rerr err))

/\
(! s env uop e s' v.
(Cevaluate s env e (s', Rval v))
==>
Cevaluate s env (CPrim1 uop e) (CevalPrim1 uop s' v))
/\
(! s env uop e s' err.
(Cevaluate s env e (s', Rerr err))
==>
Cevaluate s env (CPrim1 uop e) (s', Rerr err))

/\
(! s env p2 e1 e2 s' v1 v2.
(Cevaluate_list s env [e1;e2] (s', Rval [v1;v2]))
==>
Cevaluate s env (CPrim2 p2 e1 e2) (s', CevalPrim2 p2 v1 v2))
/\
(! s env p2 e1 e2 s' err.
(Cevaluate_list s env [e1;e2] (s', Rerr err))
==>
Cevaluate s env (CPrim2 p2 e1 e2) (s', Rerr err))

/\
(! s env e1 e2 s' v1 v2.
(Cevaluate_list s env [e1;e2] (s', Rval [v1;v2]))
==>
Cevaluate s env (CUpd e1 e2) (CevalUpd s' v1 v2))
/\
(! s env e1 e2 s' err.
(Cevaluate_list s env [e1;e2] (s', Rerr err))
==>
Cevaluate s env (CUpd e1 e2) (s', Rerr err))

/\
(! s env e1 e2 e3 s' b1 r.
(Cevaluate s env e1 (s', Rval (CLitv (Bool b1))) /\
Cevaluate s' env (if b1 then e2 else e3) r)
==>
Cevaluate s env (CIf e1 e2 e3) r)
/\
(! s env e1 e2 e3 s' err.
(Cevaluate s env e1 (s', Rerr err))
==>
Cevaluate s env (CIf e1 e2 e3) (s', Rerr err))

/\
(! s env.
T
==>
Cevaluate_list s env [] (s, Rval []))
/\
(! s env e es s' v s'' vs.
(Cevaluate s env e (s', Rval v) /\
Cevaluate_list s' env es (s'', Rval vs))
==>
Cevaluate_list s env (e ::es) (s'', Rval (v ::vs)))
/\
(! s env e es s' err.
(Cevaluate s env e (s', Rerr err))
==>
Cevaluate_list s env (e ::es) (s', Rerr err))
/\
(! s env e es s' v s'' err.
(Cevaluate s env e (s', Rval v) /\
Cevaluate_list s' env es (s'', Rerr err))
==>
Cevaluate_list s env (e ::es) (s'', Rerr err))`;

(* Equivalence relations on expressions and values *)

 val syneq_cb_aux_def = Define `

(syneq_cb_aux d nz ez (NONE,(az,e)) = ((d <nz),az,e,(nz +ez),
  (\ n . if n < nz then CCRef n else
           if n < nz +ez then CCEnv (n - nz)
           else CCArg n)))
/\
(syneq_cb_aux d nz ez (SOME(_,(_,(recs,envs))),(az,e)) =
  ( ( EVERY (\ n . n < nz) recs /\ EVERY (\ n . n < ez) envs /\
   d < nz)
  ,az
  ,e
  ,(1 + LENGTH recs + LENGTH envs)
  ,(\ n . if n = 0 then if d < nz then CCRef d else CCArg n else
            if n < 1 + LENGTH recs then
              if ( EL  (n - 1)  recs) < nz
              then CCRef ( EL  (n - 1)  recs)
              else CCArg n
            else
            if n < 1 + LENGTH recs + LENGTH envs then
              if ( EL  (n - 1 - LENGTH recs)  envs) < ez
              then CCEnv ( EL  (n - 1 - LENGTH recs)  envs)
              else CCArg n
            else CCArg n)
  ))`;


 val syneq_cb_V_def = Define `
 (syneq_cb_V az r1 r2 V V' v1 v2 =  
((v1 < az /\ (v2 = v1)) \/
  (az <= v1 /\ az <= v2 /\
   ((? j1 j2. ((r1 (v1 - az) = CCRef j1) /\ (r2 (v2 - az) = CCRef j2) /\ V' j1 j2)) \/
    (? j1 j2. ((r1 (v1 - az) = CCEnv j1) /\ (r2 (v2 - az) = CCEnv j2) /\ V  j1 j2)) \/
    (? j. (r1 (v1 - az) = CCArg j) /\ (r2 (v2 - az) = CCArg j))))))`;


val _ = Hol_reln `
(! ez1 ez2 V err.
T
==>
syneq_exp ez1 ez2 V (CRaise err) (CRaise err))
/\
(! ez1 ez2 V e1 b1 e2 b2.
(syneq_exp ez1 ez2 V e1 e2 /\
syneq_exp (ez1 +1) (ez2 +1) (\ v1 v2 . ((v1 = 0) /\ (v2 = 0)) \/ 0 < v1 /\ 0 < v2 /\ V (v1 - 1) (v2 - 1)) b1 b2)
==>
syneq_exp ez1 ez2 V (CHandle e1 b1) (CHandle e2 b2))
/\
(! ez1 ez2 V v1 v2.
((v1 < ez1 /\ v2 < ez2 /\ V v1 v2) \/
(ez1 <= v1 /\ ez2 <= v2 /\ (v1 = v2)))
==>
syneq_exp ez1 ez2 V (CVar v1) (CVar v2))
/\
(! ez1 ez2 V lit.
T
==>
syneq_exp ez1 ez2 V (CLit lit) (CLit lit))
/\
(! ez1 ez2 V cn es1 es2. ( EVERY2 (syneq_exp ez1 ez2 V) es1 es2)
==>
syneq_exp ez1 ez2 V (CCon cn es1) (CCon cn es2))
/\
(! ez1 ez2 V n e1 e2.
(syneq_exp ez1 ez2 V e1 e2)
==>
syneq_exp ez1 ez2 V (CTagEq e1 n) (CTagEq e2 n))
/\
(! ez1 ez2 V n e1 e2.
(syneq_exp ez1 ez2 V e1 e2)
==>
syneq_exp ez1 ez2 V (CProj e1 n) (CProj e2 n))
/\
(! ez1 ez2 V e1 b1 e2 b2.
(syneq_exp ez1 ez2 V e1 e2 /\
syneq_exp (ez1 +1) (ez2 +1) (\ v1 v2 . ((v1 = 0) /\ (v2 = 0)) \/ 0 < v1 /\ 0 < v2 /\ V (v1 - 1) (v2 - 1)) b1 b2)
==>
syneq_exp ez1 ez2 V (CLet e1 b1) (CLet e2 b2))
/\
(! ez1 ez2 V defs1 defs2 b1 b2 V'.
(syneq_defs ez1 ez2 V defs1 defs2 V' /\
syneq_exp (ez1 +( LENGTH defs1)) (ez2 +( LENGTH defs2))
 (\ v1 v2 . (v1 < LENGTH defs1 /\ v2 < LENGTH defs2 /\ V' v1 v2) \/
               ( LENGTH defs1 <= v1 /\ LENGTH defs2 <= v2 /\ V (v1 - LENGTH defs1) (v2 - LENGTH defs2)))
 b1 b2)
==>
syneq_exp ez1 ez2 V (CLetrec defs1 b1) (CLetrec defs2 b2))
/\
(! ez1 ez2 V cb1 cb2 V'.
(syneq_defs ez1 ez2 V [cb1] [cb2] V' /\
V' 0 0)
==>
syneq_exp ez1 ez2 V (CFun cb1) (CFun cb2))
/\
(! ez1 ez2 V e1 e2 es1 es2.
(syneq_exp ez1 ez2 V e1 e2 /\ EVERY2 (syneq_exp ez1 ez2 V) es1 es2)
==>
syneq_exp ez1 ez2 V (CCall e1 es1) (CCall e2 es2))
/\
(! ez1 ez2 V p1 e1 e2.
(syneq_exp ez1 ez2 V e1 e2)
==>
syneq_exp ez1 ez2 V (CPrim1 p1 e1) (CPrim1 p1 e2))
/\
(! ez1 ez2 V p2 e11 e21 e12 e22.
(syneq_exp ez1 ez2 V e11 e12 /\
syneq_exp ez1 ez2 V e21 e22)
==>
syneq_exp ez1 ez2 V (CPrim2 p2 e11 e21) (CPrim2 p2 e12 e22))
/\
(! ez1 ez2 V e11 e21 e12 e22.
(syneq_exp ez1 ez2 V e11 e12 /\
syneq_exp ez1 ez2 V e21 e22)
==>
syneq_exp ez1 ez2 V (CUpd e11 e21) (CUpd e12 e22))
/\
(! ez1 ez2 V e11 e21 e31 e12 e22 e32.
(syneq_exp ez1 ez2 V e11 e12 /\
syneq_exp ez1 ez2 V e21 e22 /\
syneq_exp ez1 ez2 V e31 e32)
==>
syneq_exp ez1 ez2 V (CIf e11 e21 e31) (CIf e12 e22 e32))
/\
(! ez1 ez2 V defs1 defs2 U.
(! n1 n2. U n1 n2 ==>
  n1 < LENGTH defs1 /\ n2 < LENGTH defs2 /\
  (? b az e1 j1 r1 e2 j2 r2.
  (! d e. ( EL  n1  defs1 = (SOME d,e)) ==> ( EL  n2  defs2 = EL  n1  defs1)) /\
  ((b,az,e1,j1,r1) = syneq_cb_aux n1 ( LENGTH defs1) ez1 ( EL  n1  defs1)) /\
  ((b,az,e2,j2,r2) = syneq_cb_aux n2 ( LENGTH defs2) ez2 ( EL  n2  defs2)) /\
  (b ==> syneq_exp (az +j1) (az +j2) (syneq_cb_V az r1 r2 V U) e1 e2 /\
    (! l ccenv recs envs b. ( EL  n1  defs1 = (SOME(l,(ccenv,(recs,envs))),b)) ==> EVERY (\ v . U v v) recs /\ EVERY (\ v . V v v) envs))))
==>
syneq_defs ez1 ez2 V defs1 defs2 U)`;

val _ = Hol_reln `
(! l.
T
==>
syneq (CLitv l) (CLitv l))
/\
(! cn vs1 vs2. ( EVERY2 (syneq) vs1 vs2)
==>
syneq (CConv cn vs1) (CConv cn vs2))
/\
(! V env1 env2 defs1 defs2 d1 d2 V'.
((! v1 v2. V v1 v2 ==>
  (v1 < LENGTH env1 /\ v2 < LENGTH env2 /\
   syneq ( EL  v1  env1) ( EL  v2  env2))) /\
syneq_defs ( LENGTH env1) ( LENGTH env2) V defs1 defs2 V' /\
((d1 < LENGTH defs1 /\ d2 < LENGTH defs2 /\ V' d1 d2) \/
 ( LENGTH defs1 <= d1 /\ LENGTH defs2 <= d2 /\ (d1 = d2))))
==>
syneq (CRecClos env1 defs1 d1) (CRecClos env2 defs2 d2))
/\
(! n.
T
==>
syneq (CLoc n) (CLoc n))`;

(* auxiliary functions over the syntax *)

 val no_labs_defn = Hol_defn "no_labs" `

(no_labs (CRaise _) = T)
/\
(no_labs (CHandle e1 e2) = (no_labs e1 /\ no_labs e2))
/\
(no_labs (CVar _) = T)
/\
(no_labs (CLit _) = T)
/\
(no_labs (CCon _ es) = (no_labs_list es))
/\
(no_labs (CTagEq e _) = (no_labs e))
/\
(no_labs (CProj e _) = (no_labs e))
/\
(no_labs (CLet e b) = (no_labs e /\ no_labs b))
/\
(no_labs (CLetrec defs e) = (no_labs_defs defs /\ no_labs e))
/\
(no_labs (CFun def) = (no_labs_def def))
/\
(no_labs (CCall e es) = (no_labs e /\ no_labs_list es))
/\
(no_labs (CPrim2 _ e1 e2) = (no_labs e1 /\ no_labs e2))
/\
(no_labs (CUpd e1 e2) = (no_labs e1 /\ no_labs e2))
/\
(no_labs (CPrim1 _ e) = (no_labs e))
/\
(no_labs (CIf e1 e2 e3) = (no_labs e1 /\ no_labs e2 /\ no_labs e3))
/\
(no_labs_list [] = T)
/\
(no_labs_list (e::es) = (no_labs e /\ no_labs_list es))
/\
(no_labs_defs [] = T)
/\
(no_labs_defs (d::ds) = (no_labs_def d /\ no_labs_defs ds))
/\
(no_labs_def (SOME _,_) = F)
/\
(no_labs_def (NONE,(_,b)) = (no_labs b))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn no_labs_defn;

 val all_labs_defn = Hol_defn "all_labs" `

(all_labs (CRaise _) = T)
/\
(all_labs (CHandle e1 e2) = (all_labs e1 /\ all_labs e2))
/\
(all_labs (CVar _) = T)
/\
(all_labs (CLit _) = T)
/\
(all_labs (CCon _ es) = (all_labs_list es))
/\
(all_labs (CTagEq e _) = (all_labs e))
/\
(all_labs (CProj e _) = (all_labs e))
/\
(all_labs (CLet e b) = (all_labs e /\ all_labs b))
/\
(all_labs (CLetrec defs e) = (all_labs_defs defs /\ all_labs e))
/\
(all_labs (CFun def) = (all_labs_def def))
/\
(all_labs (CCall e es) = (all_labs e /\ all_labs_list es))
/\
(all_labs (CPrim2 _ e1 e2) = (all_labs e1 /\ all_labs e2))
/\
(all_labs (CUpd e1 e2) = (all_labs e1 /\ all_labs e2))
/\
(all_labs (CPrim1 _ e) = (all_labs e))
/\
(all_labs (CIf e1 e2 e3) = (all_labs e1 /\ all_labs e2 /\ all_labs e3))
/\
(all_labs_list [] = T)
/\
(all_labs_list (e::es) = (all_labs e /\ all_labs_list es))
/\
(all_labs_defs [] = T)
/\
(all_labs_defs (d::ds) = (all_labs_def d /\ all_labs_defs ds))
/\
(all_labs_def (SOME _,(_,b)) = (all_labs b))
/\
(all_labs_def (NONE,_) = F)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn all_labs_defn;
val _ = export_theory()

