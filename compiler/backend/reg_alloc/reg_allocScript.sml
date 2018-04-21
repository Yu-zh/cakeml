(*
 * A monadic graph coloring register allocator
 *)

open preamble state_transformerTheory
open ml_monadBaseLib ml_monadBaseTheory
open sortingTheory

val _ = new_theory "reg_alloc"
val _ = ParseExtras.temp_tight_equality();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = hide "state";

(* The graph-coloring register allocator *)

(* Datatype representing the state of nodes
  Fixed n : means it is fixed to color n
  Atemp   : means that the node is allowed to be allocated to any register or stack pos
  Stemp   : only allowed to be mapped to k, k+1, ...
*)
val _ = Datatype`
  tag = Fixed num | Atemp | Stemp`

(*
  Inputs are tagged with Fixed, Atemp , Stemp

  At all times, maintain invariant that adjacent nodes cannot be both Fixed
  to the same number

  First pass changes all Atemps to either Fixed or Stemp
  - Proofs: Fixed/Stemp stays unchanged

  Second pass changes all Stemps to Fixed with argument ≥ k
  - Proof: No remaining Stemp, every input node is mapped to Fixed
*)

(* Coloring state
  Notes
  - Invariant: all the arrays have dimension = dim
  - adj_ls represents the graph as an adj list
  - node_tag is the tag for each node
  - degrees represents the graph degree of each node.
    it should probably be implemented as a functional min heap instead

*)
val _ = Hol_datatype `
  ra_state = <|
     (* Info about the graph *)
       adj_ls   : (num list) list (* adjacency list -- arr of lists *)
     ; node_tag : tag list        (* tags for each node -- arr *)
     ; degrees  : num list        (* degrees for each node -- arr *)
     ; dim      : num             (* num vertices in the graph *)

     (* worklists *)
     ; simp_wl  : num list        (* simp worklist -- list, non-move related deg < k *)
     ; spill_wl : num list        (* spill worklist -- list, deg ≥ k *)
     ; freeze_wl : num list       (* freeze worklist -- list, move related deg < k *)

     ; avail_moves_wl : (num,(num # num)) alist   (* active moves -- list, sorted by pri *)
     ; unavail_moves_wl : (num,(num # num)) alist (* inactive moves -- list *)

     (* book keeping *)
     ; coalesced : (num option) list  (* keep track of coalesce for each node -- arr *)
     ; move_related : bool list       (* fast check if a node is still move related -- arr *)

     (*
     ; constrained_moves : num list
     ; active_moves : num list
     ; move_list : (num list) list

     ; coalesced_nodes : num list
     ; alias : num list
      *)
     ; stack    : num list
     |>`;

val accessors = define_monad_access_funs ``:ra_state``;

val adj_ls_accessors = el 1 accessors;
val (adj_ls,get_adj_ls_def,set_adj_ls_def) = adj_ls_accessors;

val node_tag_accessors = el 2 accessors;
val (node_tag,get_node_tag_def,set_node_tag_def) = node_tag_accessors;

val degrees_accessors = el 3 accessors;
val (degrees,get_degrees_def,set_degrees_def) = degrees_accessors;

val coalesced_accessors = el 10 accessors;
val (coalesced, get_coalesced_def, set_coalesced_def) = coalesced_accessors;

val move_related_accessors = el 11 accessors;
val (move_related, get_move_related_def, set_move_related_def) = move_related_accessors;

(*
val move_list_accessors = el 12 accessors; (* ? *)
val (move_list, get_move_list_def, set_move_list_def) = move_list_accessors

val alias_accessors = el 14 accessors; (* ? *)
val (alias, get_move_list_def, set_move_list_def) = move_list_accessors
*)

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | Subscript`;

(* Monadic functions to handle the exceptions *)
val exn_functions = define_monad_exception_functions ``:state_exn`` ``:ra_state``;
val _ = temp_overload_on ("failwith", ``raise_Fail``);

val sub_exn = ``Subscript``;
val update_exn = ``Subscript``;

(* Fixed-size array manipulators *)
val arr_manip = define_MFarray_manip_funs
  [adj_ls_accessors,node_tag_accessors,degrees_accessors,
   coalesced_accessors, move_related_accessors] sub_exn update_exn;

fun accessor_thm (a,b,c,d,e,f) = LIST_CONJ [b,c,d,e,f]

val adj_ls_manip = el 1 arr_manip;
val node_tag_manip = el 2 arr_manip;
val degrees_manip = el 3 arr_manip;
val coalesced_manip = el 4 arr_manip;
val move_related_manip = el 5 arr_manip;

(*
val move_list_manip = el 4 arr_manip;
val alias_manip = el 5 arr_manip;
*)

val adj_ls_accessor = save_thm("adj_ls_accessor",accessor_thm adj_ls_manip);
val node_tag_accessor = save_thm("node_tag_accessor",accessor_thm node_tag_manip);
val degrees_accessor = save_thm("degrees_accessor",accessor_thm degrees_manip);
val coalesced_accessor = save_thm("coalesced_accessor",accessor_thm coalesced_manip);
val move_related_accessor = save_thm("move_related_accessor",accessor_thm move_related_manip);

(*
val move_list_accessor = save_thm("move_list_accessor",accessor_thm move_list_manip);
val alias_accessor = save_thm("alias_accessor",accessor_thm alias_manip);
*)

(* Helper functions for defining the allocator *)

(* Monadic list functions -- doesn't care about order *)
val st_ex_FOREACH_def = Define `
  (st_ex_FOREACH [] a = return ()) ∧
  (st_ex_FOREACH (x::xs) a =
  do
    a x;
    st_ex_FOREACH xs a
  od)`

val st_ex_MAP_def = Define `
  (st_ex_MAP f [] = return []) ∧
  (st_ex_MAP f (x::xs) =
  do
    fx <- f x;
    fxs <- st_ex_MAP f xs;
    return (fx::fxs)
  od)`

val st_ex_PARTITION_def = Define`
  (st_ex_PARTITION P [] tt ff = return (tt,ff)) ∧
  (st_ex_PARTITION P (x::xs) tt ff =
  do
    Px <- P x;
    if Px then
      st_ex_PARTITION P xs (x::tt) ff
    else
      st_ex_PARTITION P xs tt (x::ff)
  od)`

val st_ex_FILTER_def = Define`
  (st_ex_FILTER P [] acc = return acc) ∧
  (st_ex_FILTER P (x::xs) acc =
  do
    Px <- P x;
    if Px then
      st_ex_FILTER P xs (x::acc)
    else
      st_ex_FILTER P xs acc
  od)`

(* Insert an undirect edge into the adj list representation
  -- This is VERY lightly optimized to remove duplicates
  -- alternative: maintain an "invisible" invariant that
     all the adj_lists are sorted
*)

val insert_edge_def = Define`
  insert_edge x y =
  do
    adjx <- adj_ls_sub x;
    adjy <- adj_ls_sub y;
    if MEM y adjx then return ()
    else
    do
      update_adj_ls x (y::adjx);
      update_adj_ls y (x::adjy)
    od
  od`;

(* insert a list of edges all adjacent to one node *)
val list_insert_edge_def = Define`
  (list_insert_edge x [] = return ()) ∧
  (list_insert_edge x (y::ys) =
    do
      insert_edge x y;
      list_insert_edge x ys
    od)`;

val clique_insert_edge_def = Define`
  (clique_insert_edge [] = return ()) ∧
  (clique_insert_edge (x::xs) =
  do
    list_insert_edge x xs;
    clique_insert_edge xs
  od)`;

(* assuming vertices in cli already forms a clique,
   extend it with new members
*)
val extend_clique_def = Define`
  (extend_clique [] cli = return cli) ∧
  (extend_clique (x::xs) cli =
    if MEM x cli
    then
      extend_clique xs cli
    else
    do
      list_insert_edge x cli;
      extend_clique xs (x::cli)
    od)`;

(* The allocator heuristics, designed to minimize proof at the
   cost of some extra computation *)

(* (Safely) decrement the degree of all vertices adjacent to n by 1 *)
val dec_deg_def = Define`
  dec_deg n =
  do
    cd <- degrees_sub n;
    update_degrees n (cd-1)
  od`

val dec_degree_def = Define`
  dec_degree n =
  do
    d <- get_dim; (* TODO: check unnecessary *)
    if n < d then
    do
      adjs <- adj_ls_sub n;
      st_ex_FOREACH adjs dec_deg
    od
    else
      return ()
  od`

val add_simp_wl_def = Define`
  add_simp_wl ls =
  do
    swl <- get_simp_wl;
    set_simp_wl (ls ++ swl)
  od`

val add_spill_wl_def = Define`
  add_spill_wl ls =
  do
    swl <- get_spill_wl;
    set_spill_wl (ls ++ swl)
  od`

val add_freeze_wl_def = Define`
  add_freeze_wl ls =
  do
    fwl <- get_freeze_wl;
    set_freeze_wl (ls ++ fwl)
  od`

(* push x onto the stack, deleting it from "existence" *)
val push_stack_def = Define`
  push_stack x =
  do
    swl <- get_stack;
    update_degrees x 0;
    update_move_related x F;
    set_stack (x::swl)
  od`

val add_unavail_moves_wl_def = Define`
  add_unavail_moves_wl ls =
  do
    swl <- get_unavail_moves_wl;
    set_unavail_moves_wl (ls ++ swl)
  od`

(*
val add_moves_wl_def = Define`
  add_moves_wl ls =
  do
    mwl <- get_moves_wl;
    set_moves_wl (ls ++ mwl)
  od`

val add_coalesced_moves_def = Define`
  add_coalesced_moves xs =
  do
    ys <- get_coalesced_moves;
    set_coalesced_moves (xs ++ ys)
  od`

val add_coalesced_nodes_def = Define`
  add_coalesced_nodes xs =
  do
    ys <- get_coalesced_nodes;
    set_coalesced_nodes (xs ++ ys)
  od`

val add_active_moves_def = Define`
  add_active_moves xs =
  do
    ys <- get_active_moves;
    set_active_moves (xs ++ ys)
  od`

val add_constrained_moves_def = Define`
  add_constrained_moves xs =
  do
    ys <- get_constrained_moves;
    set_constrained_moves (xs ++ ys)
  od`

*)

(* unspill:
   Move any vertices in the spill list that has
   degree < k into the simplify or freeze worklist
   Revive all neighboring moves of these nodes
*)
val split_degree_def = Define`
  split_degree d k v =
  if v < d then (* TODO: unnecessary *)
  do
    vd <- degrees_sub v;
    return (vd < k)
  od
  else
    return T`

(* sort moves by priority *)
val sort_moves_def = Define`
  sort_moves ls =
    QSORT (λp:num,x p',x'. p>p') ls`

(* merge two sorted lists *)
val merge_def = Define`
  (merge [] ys = ys) ∧
  (merge xs [] = xs) ∧
  (merge ((p:num,m)::xs) ((p',m')::ys) =
    if p>=p' then
      (p,m) :: merge xs ((p',m')::ys)
    else
      (p',m') :: merge ((p,m)::xs) ys
  )`

(*
  revive the unavailable moves that touch each neighbor
*)
val revive_moves_def = Define`
  revive_moves vs =
  do
    nbs <- st_ex_MAP adj_ls_sub vs;
    uam <- get_unavail_moves_wl;
    am <- get_avail_moves_wl;
    let fnbs = FLAT nbs in
    let (rev,unavail) = PARTITION
      (λ(_,(x,y)). MEM x fnbs ∨ MEM y fnbs) uam in
    let sorted = merge (sort_moves rev) am in
    do
      set_avail_moves_wl sorted;
      set_unavail_moves_wl unavail
    od
  od`

val unspill_def = Define`
  unspill (k:num) =
  do
    d <- get_dim;
    swl <- get_spill_wl ;
    (ltk,gtk) <- st_ex_PARTITION (split_degree d k) swl [] [];
    (* The nodes in ltk have turned into low degree nodes *)
    revive_moves ltk;
    (ltkfreeze,ltksimp) <- st_ex_PARTITION (move_related_sub) ltk [] [];
    set_spill_wl gtk;
    add_simp_wl ltksimp;
    add_freeze_wl ltkfreeze
  od`

(* simplify:
  Directly simplifies the entire list
  instead of doing it 1-by-1
  T = successful simplification
  F = no simplification
*)
val do_simplify_def = Define`
  do_simplify k =
  do
    simps <- get_simp_wl;
    if NULL simps then
      return F
    else
    do
      st_ex_FOREACH simps dec_degree;
      st_ex_FOREACH simps push_stack;
      set_simp_wl [];
      unspill k;
      return T
    od
  od`

(* increment degree of n by d *)
val inc_deg_def = Define`
  inc_deg n d =
  do
    cd <- degrees_sub n;
    update_degrees n (cd+d)
  od`

(*
  do coalesce for real :
  perform a coalesce of (x,y) by merging y into x

  we only "pretend" to delete y from the graph
*)
val pair_rename_def = Define`
  pair_rename x y (p,(a,b)) =
  let a = if a = y then x else a in
  let b = if b = y then x else b in
  (p,(a,b))`

val do_coalesce_real_def = Define`
  do_coalesce_real x y =
  do
    (* mark y as coalesced to x *)
    update_coalesced y (SOME x);
    (* replace all instances of y in the move lists to x *)
    am <- get_avail_moves_wl;
    set_avail_moves_wl (MAP (pair_rename x y) am);
    uam <- get_unavail_moves_wl;
    set_unavail_moves_wl (MAP (pair_rename x y) uam);
    (* their respective edge lists *)
    adjx <- adj_ls_sub x;
    adjy <- adj_ls_sub y;
    (*
      Now we need to update the degrees of adjacent edges correctly
      Case 1:
      x -> v <- y, then the degree of v is reduced by 1
      Case 2:
      x -/-> v <- y, then the degree of x is increased by 1
      Case 3:
      x -> v <-/- y, no change

      In both cases, we leave the v-y edge dangling
    *)
    let (case1,case2) = PARTITION (λv. MEM v adjx) adjy in
    do
      inc_deg x (LENGTH case2);
      list_insert_edge x case2;
      st_ex_FOREACH case1 dec_deg;
      push_stack y
    od
  od`

(* The coalesceable criterion, Briggs and George *)

(*
  Briggs:
  the result of combining x,y should have fewer than k neighbors
  of significant degree (i.e. degree ≥ k)

  George:
  assume that x is a high degree node (typically a "Fixed" node)
  then coalescing y into x is allowed if every neighbor of y not already
  a neighbor of x (i.e. case 2) has degree < k

  TODO: The implementation here isn't super great,
  because the George check is only
  really efficient if one has a true adjacency matrix representation
*)
val bg_ok_def = Define`
  bg_ok k x y =
  do
    adjx <- adj_ls_sub x;
    adjy <- adj_ls_sub y;
    (* see do_coalesce_real for the cases *)
    let (case1,case2) = PARTITION (λv. MEM v adjx) adjy in
    do
      (* First we check the George criterion *)
      case2degs <- st_ex_MAP degrees_sub case2;
      let c2len = LENGTH (FILTER (λx. x >= k) case2degs) in
      if c2len = 0 then
        return T
      else
      let case3 = FILTER (λv. ¬MEM v adjy) adjx in
      do
        case1degs <- st_ex_MAP degrees_sub case1;
        case3degs <- st_ex_MAP degrees_sub case3;
        c1len <- return (LENGTH (FILTER (λx. x-1 >= k) case1degs));
        c3len <- return (LENGTH (FILTER (λx. x >= k) case3degs));
        return (c1len+c2len+c3len < k)
      od
    od
  od`

val is_Fixed_def = Define`
  is_Fixed x =
  do
    xt <- node_tag_sub x;
    return (case xt of Fixed n => T | _ => F)
  od`

(*
  We will also need consistency checks for moves.
  Any moves failing this check can be directly discarded
  1) x ≠ y
  2) x,y must not already clash
  3) if x is a phy_var, then y move_related
  4) else both x,y move_related and y is not a phy_var
*)

val consistency_ok_def = Define`
  consistency_ok x y =
  if x = y then
    return F (* check 1 *)
  else
  do
    d <- get_dim; (* unnecessary*)
    if x ≥ d ∨ y ≥ d then return F (* unnecessary *)
    else
    do
      adjy <- adj_ls_sub y; (* check 2 *)
      if MEM x adjy then return F
      else
      do
        b <- is_Fixed x;
        movrelx <- move_related_sub x;
        movrely <- move_related_sub y;
        return ((b ∨ movrelx) ∧ movrely);
      od
    od
  od`

(*
  Picks apart the available moves worklist
  1) If we find any inconsistent ones -> throw them away
  2) returns the first bg_ok move, that is also consistent
*)

val st_ex_FIRST_def = Define`
  (st_ex_FIRST P Q [] unavail = return (NONE,unavail)) ∧
  (st_ex_FIRST P Q (m::ms) unavail =
    let (p,(x,y)) = m in
    do
      b1 <- P x y;
      if ¬b1 then
        st_ex_FIRST P Q ms unavail
      else
      do
        b2 <- Q x y;
        if b2 then
          return (SOME ((x,y),ms),unavail)
        else
          st_ex_FIRST P Q ms (m::unavail)
      od
    od)`

val do_coalesce_def = Define`
  do_coalesce k =
  do
    am <- get_avail_moves_wl;
    (ores,unavail) <- st_ex_FIRST consistency_ok (bg_ok k) am [];
    add_unavail_moves_wl unavail;
    case ores of
      NONE =>
        do
          set_avail_moves_wl [];
          return F
        od
    | SOME ((x,y),ms) =>
    do
      set_avail_moves_wl ms;
      (* coalesce y into x *)
      do_coalesce_real x y;
      unspill k;
      (*
        TODO: x might have high degree after coalescing, so it may
        need to be respilled from the freeze worklist into the spill worklist!
      *)
      return T
    od
  od`

(*
  prefreeze: make the freeze and spill worklists consistent.

  If this makes a node simplifiable, then we skip freezing

  If we got here, it means coalescing failed, i.e. everything is
  an "unavailable" move now

  Here, we cleanup any potential mess in the coalescing phase
  1) Filter out all nodes y that have been coalesced
  2) delete any moves in the unavailable list, that are actually invalid
  3) mark only nodes involved in the remaining moves as "move related"
  4) simplify any resulting non-move-related nodes

*)
val is_not_coalesced_def = Define`
  is_not_coalesced d =
  do
    dt <- coalesced_sub d;
    return (dt = NONE)
  od`

val reset_move_related_def = Define`
  reset_move_related ls =
  do
    d <- get_dim;
    (* zero out move_related *)
    st_ex_FOREACH (COUNT_LIST d) (λx. update_move_related x F);
    (* reset to correct values *)
    st_ex_FOREACH ls (λ(_,(x,y)).
        do
          update_move_related x T;
          update_move_related y T
        od)
  od`

val do_prefreeze_def = Define`
  do_prefreeze k =
  do
    fwl_pre <- get_freeze_wl;
    fwl <- st_ex_FILTER is_not_coalesced fwl_pre [];

    swl_pre <- get_spill_wl;
    swl <- st_ex_FILTER is_not_coalesced swl_pre [];
    set_spill_wl swl;

    uam_pre <- get_unavail_moves_wl;
    uam <- st_ex_FILTER (λ(_,(x,y)).consistency_ok x y) uam_pre [];
    reset_move_related uam;
    uam <- set_unavail_moves_wl uam;

    (ltkfreeze,ltksimp) <- st_ex_PARTITION (move_related_sub) fwl [] [];
    add_simp_wl ltksimp;
    set_freeze_wl ltkfreeze;
    do_simplify k
  od`

(* if prefreeze failed, then just freeze *)

val do_freeze_def = Define`
  do_freeze k =
  do
    freeze <- get_freeze_wl;
    if NULL freeze then
      return F
    else
    case freeze of
      [] => return F
    | x::xs =>
      do
        dec_degree x;
        push_stack x;
        set_freeze_wl xs;
        unspill k;
        return T
      od
  od`

(* spill:
  Picks the cheapest node in the spill worklist,
  based on spill cost / d
*)
val st_ex_list_MIN_cost_def = Define`
  (st_ex_list_MIN_cost sc [] d k v acc = return (k,acc)) ∧
  (st_ex_list_MIN_cost sc (x::xs) d k v acc =
  if x < d then
    do
      xv <- degrees_sub x;
      cost <- return (lookup_any x sc 0n DIV xv);
      if v > cost then
        st_ex_list_MIN_cost sc xs d x cost (k::acc)
      else
        st_ex_list_MIN_cost sc xs d k v (x::acc)
    od
  else
    st_ex_list_MIN_cost sc xs d k v acc)`

val do_spill_def = Define`
  do_spill sc k =
  do
    spills <- get_spill_wl;
    d <- get_dim;
    case spills of
      [] => return F
    | (x::xs) =>
      if x >= d then return T else
      do
        xv <- degrees_sub x;
        (y,ys) <- st_ex_list_MIN_cost sc xs d x (lookup_any x sc 0n DIV xv) [];
        dec_deg y;
        unspill k;
        push_stack y;
        set_spill_wl ys;
        return T
      od
  od`

(*
(* TODO: if a node i is a copy from x to y, this should return the pair x, y.
 * I don't know where to get this info. *)
val node_as_copy_def = Define`
  node_as_copy i =
  node_as_copy i`

(* TODO: check *)
val get_deep_alias_def = Define`
  get_deep_alias i =
  do
    coals <- get_coalesced_nodes;
    if MEM i coals then
      do
        n' <- alias_sub n;
        get_deep_alias n'
      od
    else
      return n
  od`

(* TODO: check *)

val add_worklist_def = Define`
  add_worklist k u =
  do
    u_precolored <- is_Fixed u;
    u_mv_rl <- move_related u;
    u_deg <- degrees_sub u;
    if (not u_precolored andalso not u_mv_rl andalso u_deg < k) then
      do
        remove_freeze u;
        add_simp_wl [u]
      od
    else
      return ()
  od`


val is_ok_def = Define`
  is_ok k t r =
  do
    d <- degrees_sub t;
    if d then
      return T
    else
      do
        t_precolored <- is_Fixed t;
        if t_precolored then
          return T
        else
          do
            adj_t <- adj_ls_sub t;
            if MEM r adj_t then
              return T
            else
              return F
          od
      od
  od`

val adjacent_def = Define`
  adjacent n =
  do
    adj <- adj_ls_sub n;
    stk <- get_stack;
    coal <- get_coalesced_nodes;
    st_ex_FILTER (\x. MEM x stk orelse MEM x coal) adj []
  od`

val node_moves_def = Define`
  node_moves n =
  do
    xs <- move_list_sub n;
    (* is this right? I think there may be a typo in George/Appel paper.
     * they have an array called moveList in their specification, but elsewhere,
     * they refer to nodeMoves as an array in the state. But nodeMoves is
     * not included in the specification. *)

    ys <- get_active_moves;
    zs <- get_moves_wl;
    return (FILTER (\x. MEM x ys orelse MEM x zs) xs)
  od`


val move_related_def = Define`
  move_related n =
  do
    xs <- node_moves n;
    return (LENGTH xs ≥ 0)
  od`


val conservative_def = Define`
  conservative k acc nodes =
  case nodes of
     [] => return (acc < k)
   | x::xs =>
     do
       deg <- degrees_sub x;
       let acc' = if def ≥ k then acc + 1 else acc in
       conservative k acc' xs
     od`

val remove_spill_def = Define`
  remove_spill x =
  do
    spl_wl <- get_spill_wl;
    let spl_wl' = FILTER (\y. y ≠ x) spl_wl in
    set_spill_wl spl_wl'
  od`

val remove_freeze_def = Define`
  remove_freeze x =
  do
    frz_wl <- get_freeze_wl;
    let frz_wl' = FILTER (\y. y ≠ x) frz_wl in
    set_freeze_wl frz_wl'
  od`

(* TODO: check *)
val combine_def = Define`
  combine u v =
  do
    (* TODO: this is dumb, we traverse the list twice! *)
    frz_wl <- get_freeze_wl;
    (if MEM v frz_wl then remove_freeze v else remove_spill v);
    add_coalesced_nodes [v];

    update_alias v u;

    nmvs_u <- move_list_sub u;
    nmvs_v <- move_list_sub v;
    update_move_list u (nmvs_u ++ nmvs_v);

    adj_v <- adjacent v;
    st_ex_FOREACH adj_v
      (\t.
        do
          insert_edge t u;
          dec_degree t
        od);

    deg_u <- degrees_sub u;
    if deg_u ≥ k andalso MEM u frz_wl then
      do
        remove_freeze u;
        add_spill [u]
      od
    else
      return ()
  od`
*)

val do_step_def = Define`
  do_step sc k =
  do
    b <- do_simplify k;
    if b then return ()
    else
    do
      b <- do_coalesce k;
      if b then return ()
      else
      do
        b <- do_prefreeze k;
        if b then return ()
        else
        do
          b <- do_freeze k;
          if b then
            return ()
          else
            do
              b <- do_spill sc k;
              return ()
            od
        od
      od
    od
  od`

val rpt_do_step_def = Define`
  (rpt_do_step sc k 0 = return ()) ∧
  (rpt_do_step sc k (SUC c) =
  do
    do_step sc k;
    rpt_do_step sc k c
  od)`

(*
  The coloring functions
*)

(* Removing adjacent colours from ks *)
val remove_colours_def = Define`
  (*No more available colours*)
  (remove_colours (ls:num list) [] = return []) ∧
  (*Some available colour after checking*)
  (remove_colours [] (ks:num list) = return ks) ∧
  (*Do the check for vertex x*)
  (remove_colours (x::xs) ks =
    do
      cx <- node_tag_sub x;
      r <-
      (case cx of
        Fixed c =>
          remove_colours xs (FILTER (λx.x ≠ c) ks)
      | _ =>
          remove_colours xs ks);
      return r
    od)`

(* First colouring -- turns all Atemps into Fixeds or Stemps drawing from colors in ks *)
(* Assign a tag to an Atemp node, skipping if it is not actually an Atemp *)

val assign_Atemp_tag_def = Define`
  assign_Atemp_tag ks prefs n =
  do
    ntag <- node_tag_sub n;
    case ntag of
      Atemp =>
      do
        adjs <- adj_ls_sub n;
        ks <- remove_colours adjs ks;
        case ks of
          [] => update_node_tag n Stemp
        | (x::_) =>
          do
            c <- prefs n ks; (* Apply monadic preference oracle *)
            case c of
              NONE =>
              update_node_tag n (Fixed x)
            | SOME y =>
              update_node_tag n (Fixed y)
          od
      od
    | _ => return ()
  od`

(* The first allocation step *)
(* k = num registers, ls = heuristic list, prefs = coloring preference *)
val assign_Atemps_def = Define`
  assign_Atemps k ls prefs =
  do
    d <- get_dim;
    ls <- return (FILTER (λn. n < d) ls);
    ks <- return (GENLIST (\x.x) k);
    cs <- return (GENLIST (\x.x) d); (* actually, only need to do those not already in ls *)
    (* Assign all the ones that the ls tells us to *)
    st_ex_FOREACH ls (assign_Atemp_tag ks prefs);
    (* actually, assign_Atemp_tag already filters for Atemps, so just pass it all the nodes *)
    st_ex_FOREACH cs (assign_Atemp_tag ks prefs)
  od`

(* Default makes it easier to translate, doesn't matter for our purposes what
   the default is *)
val tag_col_def = Define`
  (tag_col (Fixed n) = n) ∧
  (tag_col _ = 0n)`

(* Find the first available in k,k+1,...
   assuming input is sorted
*)
val unbound_colour_def = Define `
  (unbound_colour col [] = col) ∧
  (unbound_colour col ((x:num)::xs) =
    if col < x then
      col
    else if x = col then
      unbound_colour (col+1) xs
    else
      unbound_colour col xs)`

(* Second colouring -- turns all Stemps into Fixed ≥ k *)
val assign_Stemp_tag_def = Define`
  assign_Stemp_tag k n =
  do
    ntag <- node_tag_sub n;
    case ntag of
      Stemp =>
      do
        adjs <- adj_ls_sub n;
        tags <- st_ex_MAP node_tag_sub adjs;
        col <- return (unbound_colour k (QSORT (λx y. x≤y) (MAP tag_col tags)));
        update_node_tag n (Fixed col)
      od
    | _ => return ()
  od`

(* The second allocation step *)
val assign_Stemps_def = Define`
  assign_Stemps k =
  do
    d <- get_dim;
    cs <- return (GENLIST (\x.x) d);
    st_ex_FOREACH cs (assign_Stemp_tag k)
  od`

(* Monadic biased selection oracle, finds the first matching color *)
val first_match_col_def = Define`
  (first_match_col ks [] = return NONE) ∧
  (first_match_col ks (x::xs) =
    do
      c <- node_tag_sub x;
      case c of
        Fixed m =>
          if MEM m ks then return (SOME m) else first_match_col ks xs
      | _ => first_match_col ks xs
    od)`

(* Clash tree representation of a program -- this is designed as an interface:
  wordLang program -> clash tree -> reg alloc

  It only represents wordLang programs, which do not have back-edges
  The allocator itself is more general, and supports arbitrary graphs
  It serves two purposes:
  1) slightly more efficient checking of coloring oracles
  2) it gets compiled in to the clash graphs for the allocator

  TODO: probably want to move the clash tree representation up and separate it
  from the allocator
*)

val _ = Datatype`
  clash_tree = Delta (num list) (num list) (* (Writes list, Reads list) *)
             | Set num_set (* Fixed set *)
             | Branch (num_set option) clash_tree clash_tree
             | Seq clash_tree clash_tree`
             (* Binary branch, with an optional liveset at the head*)

(* --- clash_tree oracle checks --- *)
val numset_list_delete_def = Define`
  (numset_list_delete [] (t:'a num_map) = t) ∧
  (numset_list_delete (x::xs) t = numset_list_delete xs (delete x t))`

(*Check that a numset is injective over the clash sets in an interpreted tree*)
val check_col_def = Define`
  check_col f t =
    let names = MAP (f o FST) (toAList t) in
    if ALL_DISTINCT names then
      SOME (t,fromAList (MAP (λx. (x,())) names))
    else NONE`

val check_partial_col_def = Define`
  (check_partial_col f [] t ft = SOME (t,ft)) ∧
  (check_partial_col f (x::xs) t ft =
    case lookup x t of
      SOME () => check_partial_col f xs t ft
    | NONE =>
    case lookup (f x) ft of
      NONE => check_partial_col f xs (insert x () t) (insert (f x) () ft)
    | SOME () => NONE)`

(* The checking function, used by oracle, and also used as part of the correctness proof *)
(* live = the liveset, flive = the liveset with f applied over it*)
val check_clash_tree_def = Define`
  (check_clash_tree f (Delta w r) live flive =
    case check_partial_col f w live flive of
      NONE => NONE
    | SOME _ =>
    let del_w = (numset_list_delete w live) in
    let fdel_w = (numset_list_delete (MAP f w) flive) in
    check_partial_col f r del_w fdel_w) ∧
  (check_clash_tree f (Set t) live flive = check_col f t) ∧
  (check_clash_tree f (Branch topt t1 t2) live flive =
    case check_clash_tree f t1 live flive of
      NONE => NONE
    | SOME (t1_out,ft1_out) =>
    case check_clash_tree f t2 live flive of
      NONE => NONE
    | SOME (t2_out,ft2_out) =>
    case topt of
      NONE =>
        (* This check can be done in either direction *)
        check_partial_col f (MAP FST (toAList (difference t2_out t1_out))) t1_out ft1_out
    | SOME t => check_col f t) ∧
  (check_clash_tree f (Seq t1 t2) live flive =
    case check_clash_tree f t2 live flive of
      NONE => NONE
    | SOME (t2_out,ft2_out) =>
      check_clash_tree f t1 t2_out ft2_out)`

(* --
compile clash_trees into a register allocator state
This produces two sptrees that re-map clash_tree variables
into the register allocator state, and vice versa
The second remap is probably not necessary?
-- *)

(* Map clash tree variables into allocator nodes, also computes the
  size of the array required
  ta = to allocator
  fa = from allocator
  nv = next fresh name
*)
val list_remap_def = Define`
  (list_remap [] (ta,fa,nv) = (ta,fa,nv)) ∧
  (list_remap (x::xs) (ta,fa,nv) =
    case lookup x ta of
      SOME v => list_remap xs (ta,fa,nv)
    | NONE =>
      list_remap xs (insert x nv ta,insert nv x fa,nv+1))`

val mk_bij_aux_def = Define`
  (mk_bij_aux (Delta writes reads) tfn =
    list_remap writes (list_remap reads tfn)) ∧
  (mk_bij_aux (Set t) tfn =
    list_remap (MAP FST (toAList t)) tfn) ∧
  (mk_bij_aux (Branch topt t1 t2) tfn =
     let tfn' = mk_bij_aux t2 (mk_bij_aux t1 tfn) in
     case topt of
       NONE => tfn'
     | SOME ts => list_remap (MAP FST (toAList ts)) tfn') ∧
  (mk_bij_aux (Seq t1 t2) tfn =
    mk_bij_aux t1 (mk_bij_aux t2 tfn))`

val mk_bij_def = Define`
  mk_bij t =
    let (ta,fa,n) = mk_bij_aux t (LN,LN,0n) in
    (ta,fa,n)`
    (* Hide the sptree impl
    ((λi. lookup_any i ta 0),(λi. lookup_any i fa 0), n)` *)

(*Distinguish 3 kinds of variables:
  Evens are physical registers
  4n+1 are allocatable registers
  4n+3 are stack registers*)

val is_stack_var_def = Define`
  is_stack_var (n:num) = (n MOD 4 = 3)`;
val is_phy_var_def = Define`
  is_phy_var (n:num) = (n MOD 2 = 0)`;
val is_alloc_var_def = Define`
  is_alloc_var (n:num) = (n MOD 4 = 1)`;

val convention_partitions = Q.store_thm("convention_partitions",`
  ∀n. (is_stack_var n ⇔ (¬is_phy_var n) ∧ ¬(is_alloc_var n)) ∧
      (is_phy_var n ⇔ (¬is_stack_var n) ∧ ¬(is_alloc_var n)) ∧
      (is_alloc_var n ⇔ (¬is_phy_var n) ∧ ¬(is_stack_var n))`,
  rw[is_stack_var_def,is_phy_var_def,is_alloc_var_def,EQ_IMP_THM]
  \\ `n MOD 2 = (n MOD 4) MOD 2` by
   (ONCE_REWRITE_TAC [GSYM (EVAL ``2*2:num``)]
    \\ fs [arithmeticTheory.MOD_MULT_MOD])
  \\ fs []
  \\ `n MOD 4 < 4` by fs []
  \\ IMP_RES_TAC (DECIDE
       ``n < 4 ==> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num)``)
  \\ fs []);

(* Set the tags according to wordLang conventions *)
val mk_tags_def = Define`
  mk_tags n fa =
  do
    inds <- return (GENLIST (\x.x) n);
    st_ex_FOREACH inds
    (λi.
      let v = fa i in
      let remainder = v MOD 4 in
      if remainder = 1 then
        update_node_tag i Atemp
      else if remainder = 3 then
        update_node_tag i Stemp
      else
        update_node_tag i (Fixed (v DIV 2)))
  od`;

(* Initializes the clash_graph using a clash_tree and a remapping bijection *)
val mk_graph_def = Define`
  (mk_graph ta (Delta w r) liveout =
    do
      wta  <- return(MAP ta w);
      rta  <- return(MAP ta r);
      live <- extend_clique wta liveout;
      live <- return (FILTER (λx. ¬MEM x wta) live);
      livein <- extend_clique rta live;
      return livein
    od) ∧
  (mk_graph ta (Set t) liveout =
    do
      live <- return(MAP ta (MAP FST (toAList t)));
      clique_insert_edge live;
      return live
    od) ∧
  (mk_graph ta (Branch topt t1 t2) liveout =
    do
      t1_live <- mk_graph ta t1 liveout;
      t2_live <- mk_graph ta t2 liveout;
      (case topt of
        NONE =>
        do
          livein <- extend_clique t1_live t2_live;
          return livein
        od
      | SOME t =>
        do
          clashes <- return (MAP ta (MAP FST (toAList t)));
          clique_insert_edge clashes;
          return clashes
        od)
    od) ∧
  (mk_graph ta (Seq t1 t2) liveout =
    do
      live <- mk_graph ta t2 liveout;
      mk_graph ta t1 live
    od)`;

val sp_default_def = Define`
  sp_default t i =
  (case lookup i t of NONE => if is_phy_var i then i DIV 2 else i | SOME x => x)`

val extend_graph_def = Define`
  (extend_graph ta [] = return ()) ∧
  (extend_graph ta ((x,y)::xs) =
  do
    insert_edge (ta x) (ta y);
    extend_graph ta xs
  od)`

(* sets up the register allocator init state with the clash_tree input
  TODO: should the sptrees be hidden right away?
  It might be easier to transfer an sptree directly for the oracle register
  allocator

  ct = clash_tree
  forced = forced edges -- will need new proof that all forced edges are in the tree
*)
val init_ra_state_def = Define`
  init_ra_state ct forced (ta,fa,n) =
  do
    mk_graph (sp_default ta) ct []; (* Put in the usual edges *)
    extend_graph (sp_default ta) forced;
    mk_tags n (sp_default fa);
  od`;

val is_Atemp_def = Define`
  is_Atemp d =
  do
    dt <- node_tag_sub d;
    return (dt = Atemp)
  od`

(* Initializer for the first allocation step *)
val init_alloc1_heu_def = Define`
  init_alloc1_heu moves d k =
  do
    ds <- return (COUNT_LIST d);
    st_ex_FOREACH ds (* Set the degree for each node *)
      (λi.
      do
        adjls <- adj_ls_sub i;
        update_degrees i (LENGTH adjls)
      od
      );
    allocs <- st_ex_FILTER is_Atemp ds []; (* only need to allocate Atemps *)
    (* pretend all the allocs are move related to reuse some earlier code *)
    st_ex_FOREACH allocs (λx. update_move_related x T);
    moves <- st_ex_FILTER (λ(_,(x,y)).consistency_ok x y) moves [];
    set_avail_moves_wl (sort_moves moves);
    reset_move_related moves;

    (ltk,gtk) <- st_ex_PARTITION (split_degree d k) allocs [] [];
    (ltkfreeze,ltksimp) <- st_ex_PARTITION (move_related_sub) ltk [] [];
    set_spill_wl gtk;
    set_simp_wl ltksimp;
    set_freeze_wl ltkfreeze;
    return (LENGTH allocs)
  od`

val do_alloc1_def = Define`
  do_alloc1 moves sc k =
  do
    d <- get_dim;
    l <- init_alloc1_heu moves d k;
    rpt_do_step sc k l;
    st <- get_stack;
    return st
  od`

val extract_tag_def = Define`
  (extract_tag t = case t of
    Fixed m => m
  | _ => 0)` (* never happens*)

(* return the final coloring as an sptree *)
val extract_color_def = Define`
  extract_color ta =
  do
    taa <- return (toAList ta);
    itags <- st_ex_MAP (λ(k,v).
      do
        t <- node_tag_sub v;
        return (k,extract_tag t)
      od) taa; (* can make the sptree directly *)
    return (fromAList itags)
  od`

val pri_move_insert_def = Define`
  pri_move_insert p x y acc =
  case lookup x acc of
    NONE =>
      insert x [(p,y)] acc
  | SOME ls =>
      insert x ((p,y)::ls) acc`

val undir_move_insert_def = Define`
  undir_move_insert p x y acc =
    pri_move_insert p x y (pri_move_insert p y x acc)`

val moves_to_sp_def = Define`
  (moves_to_sp [] acc = acc) ∧
  (moves_to_sp (move::xs) acc =
    let (p,x,y) = move in
    moves_to_sp xs (undir_move_insert p x y acc))`

(*Do a consistency sort after setting up the sptree of moves*)
val resort_moves_def = Define`
  resort_moves acc =
  map (λls. MAP SND (QSORT (λp:num,x p',x'. p>p') ls )) acc`

val _ = Datatype`
  algorithm = Simple | IRC`

(* mtable is an sptree lookup for the moves *)
val biased_pref_def = Define`
  biased_pref mtable n ks =
  do
    d <- get_dim;
    if n < d then
    do
      copt <- coalesced_sub n;
      (case copt of
        NONE =>
        (case lookup n mtable of
          NONE => return NONE
        | SOME vs =>
          handle_Subscript (first_match_col ks vs) (return NONE))
      | SOME v =>
          handle_Subscript (first_match_col ks [v]) (return NONE))
    od
    else
      return NONE
  od`

(* Putting everything together in one call *)
val do_reg_alloc_def = Define`
  do_reg_alloc alg sc k moves ct forced (ta,fa,n) =
  do
    init_ra_state ct forced (ta,fa,n);
    moves <- return (MAP  (λ(p,(x,y)). (p,(sp_default ta x),(sp_default ta y))) moves);
    ls <- do_alloc1 (if alg = Simple then [] else moves) sc k;
    assign_Atemps k ls (biased_pref (resort_moves (moves_to_sp moves LN)));
    assign_Stemps k;
    spcol <- extract_color ta;
    return spcol (* return the composed from wordLang into the graph + the allocation *)
  od`

(* As we are using fixed-size array, we need to define a different record type for the initialization *)
val array_fields_names = ["adj_ls", "node_tag", "degrees","coalesced","move_related"];
val run_ira_state_def = define_run ``:ra_state``
                                       array_fields_names
                                      "ira_state";

(* The top-level (non-monadic) reg_alloc call which should be modified to fit
   the translator's requirements *)

val reg_alloc_aux_def = Define`
  reg_alloc_aux alg sc k moves ct forced (ta,fa,n) =
    run_ira_state (do_reg_alloc alg sc k moves ct forced (ta,fa,n))
                      <| adj_ls    := (n, [])
                       ; node_tag  := (n, Atemp)
                       ; degrees   := (n, 0)
                       ; dim       := n
                       ; simp_wl   := []
                       ; spill_wl  := []
                       ; freeze_wl := []
                       ; avail_moves_wl   := []
                       ; unavail_moves_wl := []
                       ; coalesced := (n,NONE)
                       ; move_related := (n,F)
                       ; stack     := [] |>`;

val reg_alloc_def = Define`
  reg_alloc alg sc k moves ct forced =
    reg_alloc_aux alg sc k moves ct forced (mk_bij ct)`;

val _ = export_theory();
