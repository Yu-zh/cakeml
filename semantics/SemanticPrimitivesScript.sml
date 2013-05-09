(*Generated by Lem from semanticPrimitives.lem.*)
open bossLib Theory Parse res_quanTheory
open fixedPointTheory finite_mapTheory listTheory pairTheory pred_setTheory
open integerTheory set_relationTheory sortingTheory stringTheory wordsTheory

val _ = numLib.prefer_num();



open ElabTheory AstTheory TokensTheory LibTheory

val _ = new_theory "SemanticPrimitives"

(*open Lib*)
(*open Ast*)

(* Value forms *)
val _ = Hol_datatype `
 v =
    Litv of lit
  (* Constructor application. *)
  | Conv of conN id => v list 
  (* Function closures
     The environment is used for the free variables in the function *)
  | Closure of (varN, v) env => varN => exp
  (* Function closure for recursive functions
   * See Closure and Letrec above
   * The last variable name indicates which function from the mutually
   * recursive bundle this closure value represents *)
  | Recclosure of (varN, v) env => (varN # varN # exp) list => varN
  | Loc of num`;


(* The result of evaluation *)
val _ = Hol_datatype `
 error_result =
    Rtype_error
  | Rraise of error`;


val _ = Hol_datatype `
 result =
    Rval of 'a
  | Rerr of error_result`;


(* Stores *)
(* The nth item in the list is the value at location n *)
val _ = type_abbrev( "store" , ``: v list``);

(*val empty_store : store*)
val _ = Define `
 empty_store = ([])`;


(*val store_lookup : num -> store -> option v*)
val _ = Define `
 (store_lookup l st =  
(if l < LENGTH st then
    SOME ( EL  l  st)
  else
    NONE))`;


(*val store_alloc : v -> store -> store * num*)
val _ = Define `
 (store_alloc v st =
  ((st ++ [v]), LENGTH st))`;


(*val store_assign : num -> v -> store -> option store*)
val _ = Define `
 (store_assign n v st =  
(if n < LENGTH st then
    SOME ( LUPDATE v n st)
  else
    NONE))`;


(* Maps each constructor to its arity and which type it is from *)
val _ = type_abbrev( "envC" , ``: (( conN id), (num # typeN id)) env``);

val _ = type_abbrev( "envE" , ``: (varN, v) env``);

(* The bindings of a module *)
val _ = type_abbrev( "envM" , ``: (modN, envE) env``);

(*val lookup_var_id : id varN -> envM -> envE -> option v*)
val _ = Define `
 (lookup_var_id id menv envE =  
((case id of
      Short x => lookup x envE
    | Long x y =>
        (case lookup x menv of
            NONE => NONE
          | SOME env => lookup y env
        )
  )))`;


(* Other primitives *)
(* Check that a constructor is properly applied *)
(*val do_con_check : envC -> id conN -> num -> bool*)
val _ = Define `
 (do_con_check cenv n l =  
((case lookup n cenv of
      NONE => F
    | SOME (l',ns) => l = l'
  )))`;


(*val lit_same_type : lit -> lit -> bool*)
val _ = Define `
 (lit_same_type l1 l2 =  
((case (l1,l2) of
      (IntLit _, IntLit _) => T
    | (Bool _, Bool _) => T
    | (Unit, Unit) => T
    | _ => F
  )))`;


val _ = Hol_datatype `
 match_result =
    No_match
  | Match_type_error
  | Match of envE`;


(* A big-step pattern matcher.  If the value matches the pattern, return an
 * environment with the pattern variables bound to the corresponding sub-terms
 * of the value; this environment extends the environment given as an argument.
 * No_match is returned when there is no match, but any constructors
 * encountered in determining the match failure are applied to the correct
 * number of arguments, and constructors in corresponding positions in the
 * pattern and value come from the same type.  Match_type_error is returned
 * when one of these conditions is violated *)
(*val pmatch : envC -> store -> pat -> v -> envE -> match_result*)
 val pmatch_defn = Hol_defn "pmatch" `

(pmatch envC s (Pvar x) v' env = (Match (bind x v' env)))
/\
(pmatch envC s (Plit l) (Litv l') env =  
(if l = l' then
    Match env
  else if lit_same_type l l' then
    No_match
  else
    Match_type_error))
/\
(pmatch envC s (Pcon n ps) (Conv n' vs) env =  
((case (lookup n envC, lookup n' envC) of
      (SOME (l, t), SOME (l', t')) =>
        if (t = t') /\ ( LENGTH ps = l) /\ ( LENGTH vs = l') then
          if n = n' then
            pmatch_list envC s ps vs env
          else
            No_match
        else
          Match_type_error
    | (_, _) => Match_type_error
  )))
/\
(pmatch envC s (Pref p) (Loc lnum) env =  
((case store_lookup lnum s of
      SOME v => pmatch envC s p v env
    | NONE => Match_type_error
  )))
/\
(pmatch envC _ _ _ env = Match_type_error)
/\
(pmatch_list envC s [] [] env = (Match env))
/\
(pmatch_list envC s (p::ps) (v::vs) env =  
((case pmatch envC s p v env of
      No_match => No_match
    | Match_type_error => Match_type_error
    | Match env' => pmatch_list envC s ps vs env'
  )))
/\
(pmatch_list envC s _ _ env = Match_type_error)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn pmatch_defn;

(* Bind each function of a mutually recursive set of functions to its closure *)
(*val build_rec_env : list (varN * varN * exp) -> envE -> envE -> envE*)
val _ = Define `
 (build_rec_env funs cl_env add_to_env = ( FOLDR 
    (\ (f,x,e) env' . bind f (Recclosure cl_env funs f) env') 
    add_to_env 
    funs))`;


(* Lookup in the list of mutually recursive functions *)
(*val find_recfun : varN -> list (varN * varN * exp) -> option (varN * exp)*)
 val find_recfun_defn = Hol_defn "find_recfun" `
 (find_recfun n funs =  
((case funs of
      [] => NONE
    | (f,x,e) :: funs =>
        if f = n then
          SOME (x,e)
        else
          find_recfun n funs
  )))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn find_recfun_defn;

(* Check whether a value contains a closure, but don't indirect through the store *)
(*val contains_closure : v -> bool*)
 val contains_closure_defn = Hol_defn "contains_closure" `

(contains_closure (Litv l) = F)
/\
(contains_closure (Conv cn vs) = ( EXISTS contains_closure vs))
/\
(contains_closure (Closure env n e) = T)
/\
(contains_closure (Recclosure env funs n) = T)
/\
(contains_closure (Loc n) = F)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn contains_closure_defn;

(*val do_uapp : store -> uop -> v -> option (store * v)*)
val _ = Define `
 (do_uapp s uop v =  
((case uop of
      Opderef =>
        (case v of
            Loc n =>
              (case store_lookup n s of
                  SOME v => SOME (s,v)
                | NONE => NONE
              )
          | _ => NONE
        )
    | Opref =>
        let (s',n) = ( store_alloc v s) in
          SOME (s', Loc n)
  )))`;


(* Do an application *)
(*val do_app : store -> envE -> op -> v -> v -> option (store * envE * exp)*)
val _ = Define `
 (do_app s env' op v1 v2 =  
((case (op, v1, v2) of
      (Opapp, Closure env n e, v) =>
        SOME (s, bind n v env, e)
    | (Opapp, Recclosure env funs n, v) =>
        (case find_recfun n funs of
            SOME (n,e) => SOME (s, bind n v (build_rec_env funs env env), e)
          | NONE => NONE
        )
    | (Opn op, Litv (IntLit n1), Litv (IntLit n2)) =>
        if ((op = Divide) \/ (op = Modulo)) /\ (n2 = & 0) then
          SOME (s, env', Raise Div_error)
        else
          SOME (s, env',Lit (IntLit (opn_lookup op n1 n2)))
    | (Opb op, Litv (IntLit n1), Litv (IntLit n2)) =>
        SOME (s, env', Lit (Bool (opb_lookup op n1 n2)))
    | (Equality, v1, v2) =>
        if contains_closure v1 \/ contains_closure v2 then
          NONE
        else
          SOME (s, env', Lit (Bool (v1 = v2)))
    | (Opassign, (Loc lnum), v) =>
        (case store_assign lnum v s of
          SOME st => SOME (st, env', Lit Unit)
        | NONE => NONE
        )
    | _ => NONE
  )))`;


(* Do a logical operation *)
(*val do_log : lop -> v -> exp -> option exp*)
val _ = Define `
 (do_log l v e =  
((case (l, v) of
      (And, Litv (Bool T)) => SOME e
    | (Or, Litv (Bool F)) => SOME e
    | (_, Litv (Bool b)) => SOME (Lit (Bool b))
    | _ => NONE
  )))`;


(* Do an if-then-else *)
(*val do_if : v -> exp -> exp -> option exp*)
val _ = Define `
 (do_if v e1 e2 =  
(if v = Litv (Bool T) then
    SOME e1
  else if v = Litv (Bool F) then
    SOME e2
  else
    NONE))`;


(* Semantic helpers for definitions *)

(* Add the given type definition to the given constructor environment *)
(*val build_tdefs : option modN -> list (list tvarN * typeN * list (conN * list t)) -> envC*)
val _ = Define `
 (build_tdefs mn tds = ( FLAT
    ( MAP
      (\ (tvs, tn, condefs) . MAP
           (\ (conN, ts) .
              (mk_id mn conN, ( LENGTH ts, mk_id mn tn)))
           condefs)
      tds)))`;


(* Checks that no constructor is defined twice *)
(*val check_dup_ctors :
    forall 'a. option modN -> env (id conN) 'a -> list (list tvarN * typeN * list (conN * list t)) -> bool*)
val _ = Define `
 (check_dup_ctors mn_opt cenv tds =  
((! ((tvs, tn, condefs) :: 
  LIST_TO_SET tds) ((n, ts) :: LIST_TO_SET condefs).
     lookup (mk_id mn_opt n) cenv = NONE) /\ ALL_DISTINCT (let x2 = 
  ([]) in FOLDR  (\(tvs, tn, condefs) x2 . FOLDR  (\(n, ts) x2 . 
  if T then n :: x2 else x2)  x2  condefs)  x2  tds)))`;


(*val combine_dec_result : forall 'a 'b 'c 'd. env 'a 'b -> env 'c 'd -> result (env 'a 'b * env 'c 'd) -> result (env 'a 'b * env 'c 'd)*)
val _ = Define `
 (combine_dec_result cenv env r =  
((case r of
      Rerr e => Rerr e
    | Rval (cenv',env') => Rval (merge cenv' cenv, merge env' env)
  )))`;


(*val combine_mod_result : forall 'a 'b 'c 'd 'e 'f. env 'a 'b -> env 'c 'd -> env 'e 'f -> result (env 'a 'b * env 'c 'd * env 'e 'f) -> result (env 'a 'b * env 'c 'd * env 'e 'f)*)
val _ = Define `
 (combine_mod_result menv cenv env r =  
((case r of
      Rerr e => Rerr e
    | Rval (menv',cenv',env') => Rval (merge menv' menv, merge cenv' cenv, merge env' env)
  )))`;


val _ = export_theory()

