open preamble primSemEnvTheory semanticsPropsTheory
     backendTheory
     source_to_modProofTheory
     mod_to_conProofTheory
     con_to_decProofTheory
     dec_to_exhProofTheory
     exh_to_patProofTheory
     pat_to_closProofTheory
     clos_to_bvlProofTheory
     bvl_to_bviProofTheory
     bvi_to_dataProofTheory
     data_to_wordProofTheory
     word_to_stackProofTheory
     stack_to_labProofTheory
     lab_to_targetProofTheory
     backend_commonTheory
local open dataPropsTheory in end
open word_to_stackTheory

val _ = new_theory"backendProof";

(* TODO: move *)

fun Abbrev_intro th =
  EQ_MP (SYM(SPEC(concl th)markerTheory.Abbrev_def)) th

val EVERY_sec_label_ok = store_thm("EVERY_sec_label_ok",
  ``EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) (extract_labels l) ∧
    ALL_DISTINCT (extract_labels l) ⇒
    EVERY (sec_label_ok n) l``,
  Induct_on`l`>>simp[labPropsTheory.extract_labels_def]>>
  Cases>>simp[labPropsTheory.extract_labels_def]);

val EVERY_FST_SND = Q.store_thm("EVERY_FST_SND",
  `EVERY (λ(a,b). P a ∧ Q b) ls ⇔ EVERY P (MAP FST ls) ∧ EVERY Q (MAP SND ls)`,
  rw[EVERY_MEM,MEM_MAP,UNCURRY,EXISTS_PROD,FORALL_PROD,PULL_EXISTS]
  \\ metis_tac[]);

val pair_CASE_eq = Q.store_thm("pair_CASE_eq",
  `pair_CASE p f = a ⇔ ∃x y. p = (x,y) ∧ f x y = a`,
  Cases_on`p`>>rw[]);

val BIJ_FLOOKUP_MAPKEYS = Q.store_thm("BIJ_FLOOKUP_MAPKEYS",
  `BIJ bij UNIV UNIV ==>
    FLOOKUP (MAP_KEYS (LINV bij UNIV) f) n = FLOOKUP f (bij n)`,
  fs [FLOOKUP_DEF,MAP_KEYS_def,BIJ_DEF] \\ strip_tac
  \\ match_mp_tac (METIS_PROVE []
      ``x=x'/\(x /\ x' ==> y=y') ==> (if x then y else z) = (if x' then y' else z)``)
  \\ fs [] \\ rw []
  THEN1 (eq_tac \\ rw [] \\ metis_tac [BIJ_LINV_INV,BIJ_DEF,IN_UNIV,LINV_DEF])
  \\ `BIJ (LINV bij UNIV) UNIV UNIV` by metis_tac [BIJ_LINV_BIJ,BIJ_DEF]
  \\ `INJ (LINV bij UNIV) (FDOM f) UNIV` by fs [INJ_DEF,IN_UNIV,BIJ_DEF]
  \\ fs [MAP_KEYS_def] \\ metis_tac [BIJ_LINV_INV,BIJ_DEF,IN_UNIV,LINV_DEF]);

val word_list_exists_imp = Q.store_thm("word_list_exists_imp",
  `dm = addresses a n /\
    dimindex (:'a) DIV 8 * n < dimword (:'a) ∧ good_dimindex (:'a) ⇒
    word_list_exists a n (fun2set (m1,dm:'a word set))`,
  metis_tac [stack_removeProofTheory.word_list_exists_addresses]);

val addresses_thm = Q.store_thm("addresses_thm",
  `!n a. addresses a n = { a + n2w i * bytes_in_word | i < n }`,
  Induct \\ fs [stack_removeProofTheory.addresses_def]
  \\ rw [EXTENSION] \\ eq_tac \\ rw []
  THEN1 (qexists_tac `0` \\ fs [])
  THEN1 (qexists_tac `SUC i` \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ Cases_on `i` \\ fs []
  \\ disj2_tac \\ fs []
  \\ once_rewrite_tac [CONJ_COMM]
  \\ asm_exists_tac \\ fs []
  \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]);

val byte_aligned_mult = Q.store_thm("byte_aligned_mult",
  `good_dimindex (:'a) ==>
    byte_aligned (a + bytes_in_word * n2w i) = byte_aligned (a:'a word)`,
  fs [alignmentTheory.byte_aligned_def,labPropsTheory.good_dimindex_def]
  \\ rw [] \\ fs [bytes_in_word_def,word_mul_n2w]
  \\ once_rewrite_tac [MULT_COMM]
  \\ rewrite_tac [GSYM (EVAL ``2n**2``),GSYM (EVAL ``2n**3``),
        data_to_word_memoryProofTheory.aligned_add_pow]);

val IMP_MULT_DIV_LESS = Q.store_thm("IMP_MULT_DIV_LESS",
  `m <> 0 /\ d < k ==> m * (d DIV m) < k`,
  strip_tac \\ `0 < m` by decide_tac
  \\ drule DIVISION
  \\ disch_then (qspec_then `d` assume_tac)
  \\ decide_tac);

val WORD_LS_IMP = Q.store_thm("WORD_LS_IMP",
  `a <=+ b ==>
    ?k. Abbrev (b = a + n2w k) /\
        w2n (b - a) = k /\
        (!w. a <=+ w /\ w <+ b <=> ?i. w = a + n2w i /\ i < k)`,
  Cases_on `a` \\ Cases_on `b` \\ fs [WORD_LS]
  \\ fs [markerTheory.Abbrev_def]
  \\ full_simp_tac std_ss [GSYM word_sub_def,addressTheory.word_arith_lemma2]
  \\ fs [] \\ rw [] THEN1
   (rewrite_tac [GSYM word_sub_def]
    \\ once_rewrite_tac [WORD_ADD_COMM]
    \\ rewrite_tac [WORD_ADD_SUB])
  \\ Cases_on `w` \\ fs [WORD_LO,word_add_n2w]
  \\ eq_tac \\ rw [] \\ fs []
  \\ rename1 `k < m:num` \\ qexists_tac `k - n` \\ fs [])

val DIV_LESS_DIV = Q.store_thm("DIV_LESS_DIV",
  `n MOD k = 0 /\ m MOD k = 0 /\ n < m /\ 0 < k ==> n DIV k < m DIV k`,
  strip_tac
  \\ drule DIVISION \\ disch_then (qspec_then `n` (strip_assume_tac o GSYM))
  \\ drule DIVISION \\ disch_then (qspec_then `m` (strip_assume_tac o GSYM))
  \\ rfs [] \\ metis_tac [LT_MULT_LCANCEL]);

val MOD_SUB_LEMMA = Q.store_thm("MOD_SUB_LEMMA",
  `n MOD k = 0 /\ m MOD k = 0 /\ 0 < k ==> (n - m) MOD k = 0`,
  Cases_on `m <= n` \\ fs []
  \\ imp_res_tac LESS_EQ_EXISTS \\ rw []
  \\ qpat_x_assum `(m + _) MOD k = 0` mp_tac
  \\ drule MOD_PLUS
  \\ disch_then (fn th => once_rewrite_tac [GSYM th]) \\ fs []);

val LESS_MULT_LEMMA = Q.store_thm("LESS_MULT_LEMMA",
  `n1 < n2 /\ d < k ==> k * n1 + d < k * n2:num`,
  Cases_on `n2` \\ fs [MULT_CLAUSES] \\ rw []
  \\ fs [DECIDE ``n1 < SUC k <=> n1 <= k``]
  \\ match_mp_tac (DECIDE ``n < n' /\ m <= m' ==> n + m < n' + m':num``)
  \\ fs []);

val nsLookup_Bind_v_some = Q.store_thm("nsLookup_Bind_v_some",
  `nsLookup (Bind v []) k = SOME x ⇔
   ∃y. k = Short y ∧ ALOOKUP v y = SOME x`,
  Cases_on`k` \\ EVAL_TAC \\ simp[]);

val prim_config_eq = save_thm("prim_config_eq", EVAL ``prim_config`` |> SIMP_RULE std_ss [FUNION_FUPDATE_1,FUNION_FEMPTY_1]);

val IMP_init_state_ok = Q.store_thm("IMP_init_state_ok",
  `
  4 < kkk /\
    (bitmaps:'a word list) = 4w::t ∧
    good_dimindex (:α) /\
  (∀n.
    (λ((bm0,cfg),progs).
     EVERY
       (post_alloc_conventions kkk ∘ SND ∘ SND) progs ∧
     EVERY (flat_exp_conventions ∘ SND ∘ SND) progs ∧
     EVERY ((λy. raise_stub_location ≠ y) ∘ FST) progs ∧
     (n = 0 ⇒ bm0 = bitmaps)) (word_oracle n)) ∧
  stack_oracle =
  (λn.
   (λ((bm0,cfg),progs).
      (λ(progs,bm). (cfg,progs,DROP (LENGTH bm0) bm))
        (compile_word_to_stack
           kkk progs
           bm0)) (word_oracle n)) ∧
    (full_make_init sc dc max_heap stk stoff bitmaps p6 lab_st save_regs data_sp stack_oracle = (fmis,SOME xxx))
    ==>
    init_state_ok kkk fmis word_oracle`,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_def] \\ strip_tac
  \\ every_case_tac \\ fs []
  \\ fs [init_state_ok_def,data_to_word_gcProofTheory.gc_fun_ok_word_gc_fun]
  \\ conj_tac THEN1 fs [labPropsTheory.good_dimindex_def]
  \\ qpat_x_assum`_ = fmis` sym_sub_tac \\ rveq\\ fs[]
  \\ `init_prop (is_gen_gc dc.gc_kind) max_heap data_sp x /\ x.bitmaps = 4w::t` by
        (fs [stack_removeProofTheory.make_init_opt_def]
         \\ every_case_tac \\ fs [stack_removeProofTheory.init_reduce_def] \\ rw [])
  \\ fs [stack_removeProofTheory.init_prop_def]
  \\ `x.stack <> []` by (rpt strip_tac \\ fs [])
  \\ `?t1 t2. x.stack = SNOC t1 t2` by metis_tac [SNOC_CASES]
  \\ fs [] \\ rpt var_eq_tac \\ fs[ADD1]
  \\ qpat_x_assum `LENGTH t2 = x.stack_space` (assume_tac o GSYM)
  \\ fs [DROP_LENGTH_APPEND] \\ fs [FLOOKUP_DEF] >>
  fs[data_to_word_gcProofTheory.gc_fun_ok_word_gc_fun] >>
  qhdtm_x_assum `make_init_opt` mp_tac>>
  simp[stack_removeProofTheory.make_init_opt_def]>>
  every_case_tac>>fs[stack_removeProofTheory.init_reduce_def]>>rw[]>>fs[]);

val extend_with_resource_limit_not_fail = Q.store_thm("extend_with_resource_limit_not_fail",
  `x ∈ extend_with_resource_limit y ∧ Fail ∉ y ⇒ x ≠ Fail`,
  rw[extend_with_resource_limit_def] \\ metis_tac[])

val full_make_init_buffer = Q.prove(`
  (FST(full_make_init a b c d e f g h i j k)).code_buffer.buffer = [] ∧
  (FST(full_make_init a b c d e f g h i j k)).data_buffer.buffer = []`,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
     stack_removeProofTheory.make_init_any_def] >>
  every_case_tac>>fs[]>>
  EVAL_TAC>>
  pop_assum mp_tac>>fs[stack_removeProofTheory.make_init_opt_def]>>
  every_case_tac>>rw[]>>
  fs [stack_removeProofTheory.init_prop_def]);

val full_make_init_ffi = Q.prove(`
  (FST(full_make_init a b c d e f g h i j k)).ffi = h.ffi`,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def] >>
  fs [stack_removeProofTheory.make_init_any_ffi] \\ EVAL_TAC);

(*
val full_make_init_ffi = Q.prove(
  `(full_make_init
         (bitmaps,c1,code,f,ggg,jump,k,max_heap,off,regs,
          make_init mc_conf ffi io_regs cc_regs t m dm ms code2 compiler cbpos cbspace coracle,
          save_regs)).ffi = ffi`,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_ffi] \\ EVAL_TAC);

val full_make_init_code =
  ``(^(full_make_init_def |> SPEC_ALL |> concl |> dest_eq |> fst)).code``
  |> SIMP_CONV (srw_ss()) [full_make_init_def,stack_allocProofTheory.make_init_def];

val args = full_make_init_semantics_fail |> concl |> dest_imp |> #1 |> dest_conj |> #1 |> rand
val defn = full_make_init_semantics_fail |> concl |> dest_imp |> #1 |> dest_conj |> #2 |> lhs
val full_init_pre_fail_def =
  Define`full_init_pre_fail ^args = ^defn`;

val full_make_init_bitmaps = Q.prove(
  `full_init_pre_fail args = SOME x ==>
    (full_make_init args).bitmaps = FST args`,
  PairCases_on`args` \\
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_bitmaps]
  \\ every_case_tac \\ fs [] \\ fs [full_init_pre_fail_def]);
*)

val fun2set_disjoint_union = Q.store_thm("fun2set_disjoint_union",
  `
   DISJOINT d1 d2 ∧
  p (fun2set (m,d1)) ∧
   q (fun2set (m,d2))
   ⇒ (p * q) (fun2set (m,d1 ∪ d2))`,
  rw[set_sepTheory.fun2set_def,set_sepTheory.STAR_def,set_sepTheory.SPLIT_def]
  \\ first_assum(part_match_exists_tac (last o strip_conj) o concl) \\ simp[]
  \\ first_assum(part_match_exists_tac (last o strip_conj) o concl) \\ simp[]
  \\ simp[EXTENSION]
  \\ conj_tac >- metis_tac[]
  \\ fs[IN_DISJOINT,FORALL_PROD]);

val DISJOINT_INTER = Q.store_thm("DISJOINT_INTER",
  `DISJOINT b c ⇒ DISJOINT (a ∩ b) (a ∩ c)`,
  rw[IN_DISJOINT] \\ metis_tac[]);

(* -- *)

(* TODO: should be defined in targetSem *)
(* CakeML code, bytes, and code buffer space, cspace, and FFI functions, ffi,
   are installed into the machine, mc_conf + ms
   r1 and r2 are the names of registers containing
   the first address of the CakeML heap and the first address past the CakeML stack
   i.e., the range of the data memory
*)
val installed_def = Define`
  installed bytes cbspace bitmaps data_sp ffi_names ffi (r1,r2) mc_conf ms ⇔
    ∃t m io_regs cc_regs bitmap_ptr bitmaps_dm.
      (*let bitmaps_dm = { w | bitmap_ptr <=+ w ∧ w <+ bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)} in*)
      let heap_stack_dm = { w | t.regs r1 <=+ w ∧ w <+ t.regs r2 } in
      good_init_state mc_conf ms ffi bytes cbspace t m (heap_stack_dm ∪ bitmaps_dm) io_regs cc_regs ∧
      DISJOINT heap_stack_dm bitmaps_dm ∧
      m (t.regs r1) = Word bitmap_ptr ∧
      m (t.regs r1 + bytes_in_word) =
        Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) ∧
      m (t.regs r1 + 2w * bytes_in_word) =
        Word (bitmap_ptr + bytes_in_word * n2w data_sp +
              bytes_in_word * n2w (LENGTH bitmaps)) ∧
      m (t.regs r1 + 3w * bytes_in_word) =
        Word (mc_conf.target.get_pc ms + n2w (LENGTH bytes)) ∧
      m (t.regs r1 + 4w * bytes_in_word) =
        Word (mc_conf.target.get_pc ms + n2w cbspace + n2w (LENGTH bytes)) ∧
      (word_list bitmap_ptr (MAP Word bitmaps) *
        word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) data_sp)
       (fun2set (m,byte_aligned ∩ bitmaps_dm)) ∧
      ffi_names = SOME mc_conf.ffi_names`;

val byte_aligned_MOD = Q.store_thm("byte_aligned_MOD",`
  good_dimindex (:'a) ⇒
  ∀x:'a word.x ∈ byte_aligned ⇒
  w2n x MOD (dimindex (:'a) DIV 8) = 0`,
  rw[IN_DEF]>>
  fs [stack_removeProofTheory.aligned_w2n, alignmentTheory.byte_aligned_def]>>
  rfs[labPropsTheory.good_dimindex_def] \\ rfs []);

val prim_config = prim_config_eq |> concl |> lhs

val backend_config_ok_def = Define`
  backend_config_ok (c:'a config) ⇔
    c.source_conf = ^prim_config.source_conf ∧
    c.mod_conf = ^prim_config.mod_conf ∧
    0 < c.clos_conf.max_app ∧
    c.bvl_conf.next_name2 = bvl_num_stubs + 2 ∧
    LENGTH c.lab_conf.asm_conf.avoid_regs + 13 ≤ c.lab_conf.asm_conf.reg_count ∧
    c.lab_conf.pos = 0 ∧
    c.lab_conf.labels = LN ∧
    conf_ok (:'a) c.data_conf ∧
    (c.data_conf.has_longdiv ⇒ c.lab_conf.asm_conf.ISA = x86_64) /\
    (c.data_conf.has_div ⇒
      c.lab_conf.asm_conf.ISA = ARMv8 ∨ c.lab_conf.asm_conf.ISA = MIPS ∨
      c.lab_conf.asm_conf.ISA = RISC_V) ∧
    addr_offset_ok c.lab_conf.asm_conf 0w ∧
    (∀w. -8w ≤ w ∧ w ≤ 8w ⇒ byte_offset_ok c.lab_conf.asm_conf w) ∧
    c.lab_conf.asm_conf.valid_imm (INL Add) 8w ∧
    c.lab_conf.asm_conf.valid_imm (INL Add) 4w ∧
    c.lab_conf.asm_conf.valid_imm (INL Add) 1w ∧
    c.lab_conf.asm_conf.valid_imm (INL Sub) 1w ∧
    find_name c.stack_conf.reg_names PERMUTES UNIV ∧
    names_ok c.stack_conf.reg_names c.lab_conf.asm_conf.reg_count c.lab_conf.asm_conf.avoid_regs ∧
    fixed_names c.stack_conf.reg_names c.lab_conf.asm_conf ∧
    (∀s. addr_offset_ok c.lab_conf.asm_conf (store_offset s)) ∧
    (∀n.
         n ≤ max_stack_alloc ⇒
         c.lab_conf.asm_conf.valid_imm (INL Sub) (n2w (n * (dimindex (:α) DIV 8))) ∧
         c.lab_conf.asm_conf.valid_imm (INL Add) (n2w (n * (dimindex (:α) DIV 8))))`;

val backend_config_ok_with_bvl_conf_updated = Q.store_thm("backend_config_ok_with_bvl_conf_updated[simp]",
  `(f cc.bvl_conf).next_name2 = cc.bvl_conf.next_name2 ⇒
   (backend_config_ok (cc with bvl_conf updated_by f) ⇔ backend_config_ok cc)`,
  rw[backend_config_ok_def]);

val backend_config_ok_with_word_to_word_conf_updated = Q.store_thm("backend_config_ok_with_word_to_word_conf_updated[simp]",
  `backend_config_ok (cc with word_to_word_conf updated_by f) ⇔ backend_config_ok cc`,
  rw[backend_config_ok_def]);

(* not true...
val encode_header_with_has_fp_ops = Q.store_thm("encode_header_with_has_fp_ops[simp]",
  `encode_header (c with has_fp_ops := x) = encode_header c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val tag_mask_with_has_fp_ops = Q.store_thm("tag_mask_with_has_fp_ops[simp]",
  `tag_mask (c with has_fp_ops := x) = tag_mask c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val ptr_bits_with_has_fp_ops = Q.store_thm("ptr_bits_with_has_fp_ops[simp]",
  `ptr_bits (c with has_fp_ops := x) = ptr_bits c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val Make_ptr_bits_code_with_has_fp_ops = Q.store_thm("Make_ptr_bits_code_with_has_fp_ops[simp]",
  `Make_ptr_bits_code (c with has_fp_ops := x) = Make_ptr_bits_code c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val small_shift_length_with_has_fp_ops = Q.store_thm("small_shift_length_with_has_fp_ops[simp]",
  `small_shift_length (c with has_fp_ops := x) = small_shift_length c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val real_addr_with_has_fp_ops = Q.store_thm("real_addr_with_has_fp_ops[simp]",
  `real_addr (c with has_fp_ops := x) = real_addr c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val real_offset_with_has_fp_ops = Q.store_thm("real_offset_with_has_fp_ops[simp]",
  `real_offset (c with has_fp_ops := x) = real_offset c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val bignum_words_with_has_fp_ops = Q.store_thm("bignum_words_with_has_fp_ops[simp]",
  `bignum_words (c with has_fp_ops := x) = bignum_words c`,
  rw[FUN_EQ_THM] \\ rw[data_to_wordTheory.bignum_words_def]);

val WriteWord64_on_32_with_has_fp_ops = Q.store_thm("WriteWord64_on_32_with_has_fp_ops[simp]",
  `WriteWord64_on_32 (c with has_fp_ops := x) = WriteWord64_on_32 c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val assign_with_has_fp_ops = Q.store_thm("assign_with_has_fp_ops",
  `assign (c with has_fp_ops := x) secn l dest op args names =
   assign c secn l dest op args names`,
  rw[data_to_wordTheory.assign_def] \\
  PURE_TOP_CASE_TAC \\ fsrw_tac[][]
*)

val backend_config_ok_call_empty_ffi = store_thm("backend_config_ok_call_empty_ffi[simp]",
  ``backend_config_ok (cc with
      data_conf updated_by (λc. c with call_empty_ffi updated_by x)) =
    backend_config_ok cc``,
  fs [backend_config_ok_def,data_to_wordTheory.conf_ok_def,
      data_to_wordTheory.shift_length_def]);

(* TODO: ?? where to put these ?? *)
val mc_init_ok_def = Define`
  mc_init_ok c mc ⇔
  EVERY (λr. MEM (find_name c.stack_conf.reg_names (r + mc.target.config.reg_count -(LENGTH mc.target.config.avoid_regs+5))) mc.callee_saved_regs) [2;3;4] ∧
  find_name c.stack_conf.reg_names 4 = mc.len2_reg ∧
  find_name c.stack_conf.reg_names 3 = mc.ptr2_reg ∧
  find_name c.stack_conf.reg_names 2 = mc.len_reg ∧
  find_name c.stack_conf.reg_names 1 = mc.ptr_reg ∧
  find_name c.stack_conf.reg_names 0 =
    (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ∧
  (* the next four are implied by injectivity of find_name *)
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.len_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.ptr_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.len2_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.ptr2_reg ∧
  ¬MEM (case mc.target.config.link_reg of NONE => 0 | SOME n => n) mc.callee_saved_regs ∧
   c.lab_conf.asm_conf = mc.target.config`

val mc_init_ok_with_bvl_conf_updated = Q.store_thm("mc_init_ok_with_bvl_conf_updated[simp]",
  `mc_init_ok (cc with bvl_conf updated_by f) mc ⇔ mc_init_ok cc mc`,
  rw[mc_init_ok_def]);

val mc_init_ok_with_word_to_word_conf_updated = Q.store_thm("mc_init_ok_with_word_to_word_conf_updated[simp]",
  `mc_init_ok (cc with word_to_word_conf updated_by f) mc ⇔ mc_init_ok cc mc`,
  rw[mc_init_ok_def]);

val mc_init_ok_call_empty_ffi = store_thm("mc_init_ok_call_empty_ffi[simp]",
  ``mc_init_ok (cc with
      data_conf updated_by (λc. c with call_empty_ffi updated_by x)) =
    mc_init_ok cc``,
  fs [mc_init_ok_def,data_to_wordTheory.conf_ok_def,
      data_to_wordTheory.shift_length_def,FUN_EQ_THM]);

val heap_regs_def = Define`
  heap_regs reg_names =
    (find_name reg_names 2, find_name reg_names 4)`;

val _ = temp_overload_on("bvl_inline_compile_prog",``bvl_inline$compile_prog``);
val _ = temp_overload_on("bvi_tailrec_compile_prog",``bvi_tailrec$compile_prog``);
val _ = temp_overload_on("bvi_to_data_compile_prog",``bvi_to_data$compile_prog``);
val _ = temp_overload_on("bvl_to_bvi_compile_prog",``bvl_to_bvi$compile_prog``);

val compile_correct = Q.store_thm("compile_correct",
  `compile (c:'a config) prog = SOME (bytes,bitmaps,c') ⇒
   let (s,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
   ¬semantics_prog s env prog Fail ∧
   backend_config_ok c ∧ mc_conf_ok mc ∧ mc_init_ok c mc ∧
   installed bytes cbspace bitmaps data_sp c'.ffi_names ffi (heap_regs c.stack_conf.reg_names) mc ms ⇒
     machine_sem (mc:(α,β,γ) machine_config) ffi ms ⊆
       extend_with_resource_limit (semantics_prog s env prog)`,
  srw_tac[][compile_eq_from_source,from_source_def,backend_config_ok_def,heap_regs_def] >>
  `c.lab_conf.asm_conf = mc.target.config` by fs[mc_init_ok_def] >>
  `c'.ffi_names = SOME mc.ffi_names` by fs[installed_def] >>
  drule(GEN_ALL(MATCH_MP SWAP_IMP source_to_modProofTheory.compile_correct)) >>
  fs[primSemEnvTheory.prim_sem_env_eq] >>
  qpat_x_assum`_ = s`(assume_tac o Abbrev_intro o SYM) >>
  qpat_x_assum`_ = env`(assume_tac o Abbrev_intro o SYM) >>
  `∃s2 env2 gtagenv.
     precondition s env c.source_conf s2 env2 ∧
     nsDomMod env2.c = {[]} ∧
     s2.globals = [] ∧
     s2.ffi = ffi ∧
     s2.refs = [] ∧
     s2.defined_types = s.defined_types ∧
     (* s2.defined_mods = s.defined_mods ∧ *)
     envC_tagged env2.c (prim_config:'a backend$config).mod_conf.tag_env gtagenv ∧
     exhaustive_env_correct (prim_config:'a backend$config).mod_conf.exh_ctors_env gtagenv ∧
     gtagenv_wf gtagenv ∧
     next_inv s.defined_types
       (prim_config:'a backend$config).mod_conf.next_exception gtagenv` by (
    simp[source_to_modProofTheory.precondition_def] >>
    simp[Abbr`env`,Abbr`s`] >>
    srw_tac[QUANT_INST_ss[pair_default_qp,record_default_qp]][] >>
    rw[source_to_modProofTheory.invariant_def] >>
    rw[source_to_modProofTheory.s_rel_cases] >>
    (* TODO: Not sure why these got broken *)
    rw[Once source_to_modProofTheory.v_rel_cases] >>
    simp[Once (GSYM PULL_EXISTS)]>> CONJ_TAC >-
      (rw[]>>Cases_on`x`>>fs[namespaceTheory.nsLookup_def])>>
    rw[Once prim_config_eq] >>
    simp[Once (GSYM PULL_EXISTS)]>> CONJ_TAC >-
      (rw[namespaceTheory.nsDomMod_def,EXTENSION,GSPECIFICATION,PULL_EXISTS]>>
      simp[EXISTS_PROD]>>Cases_on`x`>>fs[namespaceTheory.nsLookupMod_def])>>
    rw[envC_tagged_def, mod_to_conTheory.lookup_tag_env_def,PULL_EXISTS] >>
    CONV_TAC(PATH_CONV"blrbbblr"EVAL) >>
    rw[prim_config_eq,option_fold_def] >>
    CONV_TAC(PATH_CONV"blrbbbrbblr"EVAL) >>
    (fn g as (asl,w) =>
      let
        val tms = w |> dest_exists |> #2
                    |> dest_conj |> #1
                    |> strip_forall |> #2
                    |> dest_imp |> #2
                    |> strip_exists |> #2
                    |> funpow 2 (rand o rator)
                    |> lhs |> funpow 2 (rand o rator)
        val (ls,ty) = listSyntax.dest_list tms
        val (ty1,ty2) = pairSyntax.dest_prod ty
        val (ty2,ty3) = pairSyntax.dest_prod ty2
        val (ty3,ty4) = pairSyntax.dest_prod ty3
        val ty1 = pairSyntax.mk_prod(ty1,ty4)
        val ty2 = pairSyntax.mk_prod (ty3,ty2)
        fun fix_pair tm =
          let val ls = pairSyntax.strip_pair tm
          in pairSyntax.mk_pair(pairSyntax.mk_pair(el 1 ls, el 4 ls),
                                pairSyntax.mk_pair(el 3 ls, el 2 ls))
          end
        val ls = map fix_pair ls
        val fm = finite_mapSyntax.list_mk_fupdate
                  (finite_mapSyntax.mk_fempty (ty1,ty2), ls)
      in exists_tac fm end g) >>
    conj_tac
    >- (
      Cases \\ simp[nsLookup_Bind_v_some,FLOOKUP_UPDATE,namespaceTheory.id_to_n_def] >>
      rpt ( IF_CASES_TAC \\ fs[] \\ rveq \\ fs[] )) >>
    conj_tac >- (
      simp[exhaustive_env_correct_def,IN_FRANGE,FLOOKUP_UPDATE,PULL_EXISTS] >>
      srw_tac[DNF_ss][] >>
      EVAL_TAC >>
      pop_assum mp_tac >> rw[] >>
      EVAL_TAC >>
      simp[PULL_EXISTS]) >>
    conj_tac >- (
      EVAL_TAC >> rw[] >> fs[semanticPrimitivesTheory.same_tid_def,namespaceTheory.id_to_n_def] ) >>
    simp[next_inv_def,PULL_EXISTS] >>
    simp[FLOOKUP_UPDATE] >>
    rw[] >> EVAL_TAC >>
    srw_tac[QUANT_INST_ss[std_qp]][]) >>
  disch_then drule >> strip_tac >>
  pairarg_tac \\ fs[] >>
  qhdtm_x_assum`from_mod`mp_tac >>
  srw_tac[][from_mod_def,mod_to_conTheory.compile_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_assum_abbrev_tac`semantics_prog s env prog sem2` >>
  `sem2 ≠ Fail` by metis_tac[] >>
  `semantics_prog s env prog = { sem2 }` by (
    simp[EXTENSION,IN_DEF] >>
    metis_tac[semantics_prog_deterministic] ) >>
  qunabbrev_tac`sem2` >>
  drule (GEN_ALL mod_to_conProofTheory.compile_prog_semantics) >>
  fs[] >> rveq >>
  simp[AND_IMP_INTRO] >> simp[Once CONJ_COMM] >>
  disch_then drule >>
  simp[mod_to_conProofTheory.invariant_def,
       mod_to_conTheory.get_exh_def,
       mod_to_conTheory.get_tagenv_def] >>
  simp[mod_to_conProofTheory.s_rel_cases] >>
  CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++QUANT_INST_ss[record_default_qp,pair_default_qp])[])) >>
  simp[mod_to_conProofTheory.cenv_inv_def] >>
  disch_then(qspec_then`gtagenv`mp_tac)>>
  impl_tac >- ( fs[] >> rw[Abbr`s`,prim_config_eq] ) >>
  strip_tac >>
  pop_assum(assume_tac o SYM) >> simp[] >>
  qmatch_assum_rename_tac`from_con ccon _ = _` \\
  qunabbrev_tac`ccon`>>
  qhdtm_x_assum`from_con`mp_tac >>
  srw_tac[][from_con_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  rfs[] >> fs[] >>
  qpat_x_assum`Fail ≠ _`(assume_tac o GSYM) >>
  drule(GEN_ALL(MATCH_MP SWAP_IMP (REWRITE_RULE[GSYM AND_IMP_INTRO]con_to_decProofTheory.compile_semantics))) >>
  simp[] >>
  impl_tac >- (
    qhdtm_x_assum`mod_to_con$compile_prog`mp_tac >>
    simp[prim_config_eq] >> EVAL_TAC >>
    `semantics env2 s2 p ≠ Fail` by simp[] >>
    pop_assum mp_tac >>
    simp_tac(srw_ss())[modSemTheory.semantics_def] >>
    IF_CASES_TAC >> simp[] >> disch_then kall_tac >>
    pop_assum mp_tac >>
    simp[modSemTheory.evaluate_prog_def] >>
    BasicProvers.TOP_CASE_TAC >> simp[] >> strip_tac >> fs[] >>
    `¬MEM "option" (prog_to_top_types p)` by (
      fs[modSemTheory.no_dup_top_types_def,IN_DISJOINT,MEM_MAP] >>
      fs[Abbr`s`] >> metis_tac[] ) >>
    strip_tac >>
    match_mp_tac compile_prog_exh_unchanged >>
    asm_exists_tac >> simp[] >>
    qmatch_assum_abbrev_tac`compile_prog st p = _` >>
    qexists_tac`st`>>simp[Abbr`st`,mod_to_conTheory.get_exh_def] >>
    simp[FLOOKUP_UPDATE]) >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qhdtm_x_assum`from_dec`mp_tac >> srw_tac[][from_dec_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qhdtm_x_assum`con_to_dec$compile`mp_tac >>
  qmatch_assum_rename_tac`compile _ _ = (cc,_)` >>
  `cc.next_global = 0` by (
    fs[source_to_modTheory.compile_def,LET_THM] >>
    pairarg_tac >> fs[] >>
    rveq >> simp[prim_config_eq] ) >> fs[] >>
  strip_tac >> fs[] >>
  qmatch_assum_rename_tac`from_exh c3 _ = _` >>
  qunabbrev_tac`c3`>>fs[] >>
  qmatch_abbrev_tac`_ ⊆ _ { decSem$semantics env3 st3 [e3] }` >>
  (dec_to_exhProofTheory.compile_semantics
    |> Q.GENL[`env`,`st`,`e`,`envh`,`sth`]
    |> qispl_then[`env3`,`st3`,`e3`]mp_tac) >>
  simp[Abbr`env3`] >>
  simp[Once dec_to_exhProofTheory.v_rel_cases] >>
  simp[dec_to_exhProofTheory.state_rel_def] >>
  fs[Abbr`st3`,con_to_decProofTheory.compile_state_def] >>
  CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++QUANT_INST_ss[record_default_qp,pair_default_qp])[])) >>
  simp[Abbr`e3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qhdtm_x_assum`from_exh`mp_tac >>
  srw_tac[][from_exh_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  fs[exh_to_patTheory.compile_def] >>
  qmatch_abbrev_tac`_ ⊆ _ { exhSem$semantics env3 st3 es3 }` >>
  cheat);
  (*
  (exh_to_patProofTheory.compile_exp_semantics
   |> Q.GENL[`env`,`st`,`es`]
   |> qispl_then[`env3`,`st3`,`es3`]mp_tac) >>
  simp[Abbr`es3`,Abbr`env3`] >>
  fs[exh_to_patProofTheory.compile_state_def,Abbr`st3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qhdtm_x_assum`from_pat`mp_tac >>
  srw_tac[][from_pat_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_abbrev_tac`_ ⊆ _ { patSem$semantics env3 st3 es3 }` >>
  (pat_to_closProofTheory.compile_semantics
   |> Q.GENL[`env`,`st`,`es`,`max_app`]
   |> qispl_then[`env3`,`st3`,`es3`]mp_tac) >>
  simp[Abbr`env3`,Abbr`es3`] >>
  first_assum(fn th => disch_then(mp_tac o C MATCH_MP th)) >>
  fs[pat_to_closProofTheory.compile_state_def,Abbr`st3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qhdtm_x_assum`from_clos`mp_tac >>
  srw_tac[][from_clos_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_abbrev_tac`_ ⊆ _ { closSem$semantics [] st3 [e3] }` >>
  qhdtm_x_assum`from_bvl`mp_tac >>
  simp[from_bvl_def] >>
  pairarg_tac \\ fs[] \\ strip_tac \\
  qhdtm_x_assum`from_bvi`mp_tac >>
  rw[from_bvi_def] >>
  qmatch_assum_abbrev_tac `from_data c4 p4 = _` \\
  qhdtm_x_assum`from_data`mp_tac
  \\ simp[from_data_def]
  \\ pairarg_tac \\ fs[]
  \\ strip_tac
  \\ rename1`compile _ _ _ p4 = (col,p5)` \\
  qhdtm_x_assum`from_word`mp_tac \\
  simp[from_word_def] \\ pairarg_tac \\ fs[] \\ strip_tac \\
  qmatch_assum_rename_tac`compile _ p5 = (c6,p6)` \\
  fs[from_stack_def,from_lab_def] \\
  qmatch_assum_abbrev_tac`_ _ (compile c4.lab_conf p7) = SOME (bytes,_,c')`
  \\ `compile c4.lab_conf p7 = SOME (bytes,c')`
  by (
    Cases_on`compile c4.lab_conf p7` \\ fs[attach_bitmaps_def] \\
    Cases_on`x` \\ fs[attach_bitmaps_def] ) \\
  fs[installed_def] \\
  qmatch_assum_abbrev_tac`good_init_state mc ms ffi bytes cbspace tar_st m dm io_regs cc_regs` \\
  qpat_x_assum`Abbrev(p7 = _)` mp_tac>>
  qmatch_goalsub_abbrev_tac`compile _ _ _ stk stoff`>>
  strip_tac \\
  qabbrev_tac`kkk = stk - 2`>>
  (clos_to_bvlProofTheory.compile_semantics
   |> GEN_ALL
   |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s","e","c"]))
   |> INST_TYPE[gamma|->``:(num#bvl$exp)num_map#num#num#(α word list # α lab_to_target$config)``]
   |> qispl_then[`st3`,`e3`,`c.clos_conf`]mp_tac) >>
  simp[] >>
  (* TODO: define "construct oracle" in all languages,
     also, the arguments should be instantiated properly *)
  qabbrev_tac`clos_oracle = λn:num.
    ((l,n1,n2,
      (bitmaps,<| labels := c'.labels; pos := LENGTH bytes; asm_conf := mc.target.config; ffi_names := SOME mc.ffi_names|>)),
      []:(num#num#bvl$exp)list)` >>
  qabbrev_tac`data_oracle = ((I ## compile_prog) o full_co c.bvl_conf clos_oracle)` \\
  qabbrev_tac `c4_data_conf = (c4.data_conf with has_fp_ops := (1 < c4.lab_conf.asm_conf.fp_reg_count))` \\
  qabbrev_tac`word_oracle =
    (I ## MAP (λp. full_compile_single tt kk aa c4.lab_conf.asm_conf (p,NONE))) o
    (I ## MAP (compile_part c4_data_conf)) o
    data_oracle`>>
  qabbrev_tac`stack_oracle =
     (λn.
      let ((bm0,cfg),progs) = word_oracle n in
      let (progs,bm) = word_to_stack$compile_word_to_stack kkk progs bm0 in
        (cfg,progs,DROP (LENGTH bm0) bm))`>>
  qabbrev_tac`lab_oracle =
    (λn.
     let (cfg,p,b) = stack_oracle n in
       (cfg,compile_no_stubs c4.stack_conf.reg_names c4.stack_conf.jump stoff stk p))`\\
  qabbrev_tac`lab_st:('a,'a lab_to_target$config,'ffi) labSem$state = make_init mc ffi io_regs cc_regs tar_st m (dm ∩ byte_aligned) ms p7 lab_to_target$compile
       (mc.target.get_pc ms + n2w (LENGTH bytes)) cbspace lab_oracle` \\
  qabbrev_tac`stack_st_opt =
    full_make_init
      c4.stack_conf
      c4.data_conf
      (2 * max_heap_limit (:'a) c4_data_conf - 1)
      stk
      stoff
      c6.bitmaps
      p6
      lab_st
      (set mc.callee_saved_regs)
      data_sp
      stack_oracle` >>
  qabbrev_tac`stack_st = FST stack_st_opt` >>
  qabbrev_tac`word_st = make_init kkk stack_st (fromAList p5) word_oracle` \\
  qabbrev_tac`data_cc =
    (λcfg.
        lift (I ## MAP upper_w2w ## I) ∘
        (λprogs. word_st.compile cfg
          (MAP (λp. full_compile_single tt kk aa c4.lab_conf.asm_conf (p,NONE)) progs)) ∘
        MAP (compile_part c4_data_conf))` >>
  disch_then(qspecl_then[
    `full_cc c.bvl_conf (λcfg prog. data_cc cfg (compile_prog prog))`,
    `clos_oracle`]mp_tac) >>
  impl_tac >- (
    `esgc_free e3 ∧ BAG_ALL_DISTINCT (set_globals e3)` by
      (unabbrev_all_tac>>
      fs[con_to_decTheory.compile_def]>> pairarg_tac>>fs[]>>
      metis_tac[SND,
      mod_to_conProofTheory.compile_no_set_globals,con_to_decProofTheory.no_set_globals_imp_esgc_free,con_to_decTheory.compile_def,dec_to_exhProofTheory.compile_esgc_free,exh_to_patProofTheory.compile_esgc_free,pat_to_closProofTheory.compile_esgc_free,
      mod_to_conProofTheory.compile_no_set_globals,con_to_decProofTheory.no_set_globals_imp_bag_all_distinct,con_to_decTheory.compile_def,dec_to_exhProofTheory.compile_distinct_setglobals,exh_to_patProofTheory.compile_distinct_setglobals,pat_to_closProofTheory.compile_distinct_setglobals])>>
    EVAL_TAC>>simp[Abbr`st3`]>>
    unabbrev_all_tac >>
    simp[pat_to_closProofTheory.compile_contains_App_SOME] >>
    simp[pat_to_closProofTheory.compile_every_Fn_vs_NONE] >>
    simp[EVEN_ADD,EVEN_EXP_IFF])>>
  simp[Abbr`e3`] >>
  fs[Abbr`st3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qmatch_goalsub_abbrev_tac`semantics _ _ clos_oracle (full_cc bvl_c bvl_cc) _` >>
  Q.ISPECL_THEN[`s2.ffi`,`clos_oracle`,`bvl_cc`]drule
    ((Q.GENL[`ffi0`,`co`,`cc`] bvl_to_bviProofTheory.compile_semantics)) >>
  qunabbrev_tac`c'''`>>fs[] >>
  simp[Abbr`clos_oracle`,Abbr`bvl_c`,Abbr`bvl_cc`] >>
  once_rewrite_tac[GSYM AND_IMP_INTRO] >>
  impl_tac >- (
    qhdtm_x_assum`bvl_to_bvi$compile`mp_tac \\
    simp[bvl_to_bviTheory.compile_def] \\
    rpt(pairarg_tac \\ fs[]) \\ strip_tac \\
    drule bvi_tailrecProofTheory.compile_prog_next_mono \\
    strip_tac \\ rveq \\ simp[] ) \\
  impl_keep_tac >- (
    match_mp_tac (GEN_ALL clos_to_bvlProofTheory.compile_all_distinct_locs)>>
    qexists_tac`e''''`>>
    qexists_tac`c''`>>
    qexists_tac`c.clos_conf`>>
    simp[]>>
    EVAL_TAC >>
    simp[EVEN_ADD,EVEN_EXP_IFF])>>
  disch_then(CHANGED_TAC o SUBST_ALL_TAC o SYM) >>
  qmatch_abbrev_tac`_ ⊆ _ { bviSem$semantics ffi (fromAList p3) clos_co clos_cc s3 }` >>
  `∀n. SND (clos_co n) = []` by ( (* this won't be true later *)
    simp[Abbr`clos_co`,full_co_def,
         bvi_tailrecProofTheory.mk_co_def,
         bvl_inlineProofTheory.state_co_def] \\
    rpt (pairarg_tac \\ fs[] \\ rveq) \\
    ntac 2 (pop_assum mp_tac) \\
    EVAL_TAC \\ strip_tac \\ rveq \\
    EVAL_TAC \\ strip_tac \\ rveq \\
    pop_assum mp_tac \\ EVAL_TAC \\
    strip_tac \\ rveq \\ REFL_TAC ) \\
  `∀n. EVERY ($<= data_num_stubs) (MAP FST (SND (clos_co n)))` by (
    simp[] (* real proof could be like this:
    simp[Abbr`clos_co`,full_co_def,
         bvi_tailrecProofTheory.mk_co_def,
         bvl_inlineProofTheory.state_co_def] \\
    pairarg_tac \\ fs[] \\
    pairarg_tac \\ fs[] \\
    pairarg_tac \\ fs[] \\
    pairarg_tac \\ fs[] \\ rveq \\
    pairarg_tac \\ fs[] \\ rveq \\
    simp[EVERY_MEM] \\ ntac 2 strip_tac \\
    drule (GEN_ALL bvi_tailrecProofTheory.compile_prog_MEM) \\
    disch_then drule \\
    strip_tac >- (
      drule (GEN_ALL compile_inc_next_range) \\
      disch_then drule \\ strip_tac \\
      qmatch_rename_tac`_ ≤ x` \\
      `bvl_num_stubs ≤ x` by (pop_assum mp_tac \\ rw[] \\ fs[]) \\
      pop_assum mp_tac \\
      EVAL_TAC \\ simp[] ) \\
    rveq \\
    fs[bvl_to_bviTheory.compile_def] \\
    pairarg_tac \\ fs[] \\
    pairarg_tac \\ fs[] \\
    pairarg_tac \\ fs[] \\
    drule bvi_tailrecProofTheory.compile_prog_next_mono \\
    rw[] \\ EVAL_TAC \\ simp[] *)) \\
  (bvi_to_dataProofTheory.compile_prog_semantics
   |> GEN_ALL
   |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["prog","start","ffi0","cc","co"]))
   |> qispl_then[`p3`,`s3`,`ffi`,`data_cc`,`clos_co`]mp_tac) >>
  impl_tac >- simp[]>> simp[] >>
  disch_then (CHANGED_TAC o SUBST_ALL_TAC o SYM)
  \\ `s3 = InitGlobals_location` by
   (fs [bvl_to_bviTheory.compile_def,bvl_to_bviTheory.compile_prog_def]
    \\ rpt (pairarg_tac \\ fs []))
  \\ qhdtm_x_assum`data_to_word$compile`mp_tac
  \\ (data_to_word_compile_conventions
     |> Q.GENL[`data_conf`,`wc`,`ac`,`prog`]
     |> C (specl_args_of_then``data_to_word$compile``)mp_tac)
  \\ impl_tac >- fs[mc_conf_ok_def]
  \\ strip_tac \\ fs[]
  \\ (data_to_word_compile_lab_pres
     |> Q.GENL[`data_conf`,`word_conf`,`asm_conf`,`prog`]
     |> C (specl_args_of_then``data_to_word$compile``)mp_tac)
  \\ ntac 2 strip_tac
  \\ FULL_SIMP_TAC std_ss [Once LET_THM]>>
  imp_res_tac (word_to_stack_compile_lab_pres |> INST_TYPE [beta|->alpha])>>
  pop_assum (qspec_then`c4.lab_conf.asm_conf` assume_tac)>>fs[]>>
  rfs[]>>
  (word_to_stack_stack_asm_convs |> GEN_ALL |> Q.SPECL_THEN[`p5`,`c4.lab_conf.asm_conf`] mp_tac)>>
  impl_tac>-
    (fs[Abbr`c4`,EVERY_MEM,FORALL_PROD]>>
     unabbrev_all_tac \\ fs[] >>
    metis_tac[])>>
  strip_tac>>
  drule (word_to_stack_stack_convs|> GEN_ALL)>>
  simp[]>>
  impl_tac>-
    (fs[backend_config_ok_def,Abbr`c4`]>>
    unabbrev_all_tac >>
    fs[EVERY_MEM,FORALL_PROD,MEM_MAP,EXISTS_PROD]>>
    fs[PULL_EXISTS]>>
    metis_tac[])>>
  strip_tac>>
  fs[data_to_wordTheory.compile_def]
  \\ qmatch_assum_abbrev_tac`compile _ _ t_code = (_,p5)`
  \\ drule (GEN_ALL compile_distinct_names)
  \\ `MAP FST p4 = MAP FST p3`
    by metis_tac[bvi_to_dataProofTheory.MAP_FST_compile_prog]
  \\ simp[]
  \\ disch_then(qspec_then`0`mp_tac) \\ simp[] \\ strip_tac
  (*
  \\ first_assum(qspec_then`0`mp_tac)
  \\ impl_keep_tac >- fs[] \\ strip_tac
  *)
  \\ `stubs (:'a) c4.data_conf = stubs (:'a) c4_data_conf` by ( simp[Abbr`c4_data_conf`] )
  \\ `code_rel c4_data_conf (fromAList p4) (fromAList t_code)`
  by (
    simp[data_to_word_gcProofTheory.code_rel_def] \\
    simp[Abbr`t_code`,lookup_fromAList,ALOOKUP_APPEND,EVERY_MEM,FORALL_PROD] \\
    conj_tac>-
      (fs[domain_fromAList]>>
      simp[Once UNION_COMM,SimpRHS]>>
      AP_TERM_TAC>>
      simp[data_to_wordTheory.compile_part_def,FST_triple,MAP_MAP_o,o_DEF,LAMBDA_PROD])>>
    conj_tac >- (
      rw[] \\
      drule(ONCE_REWRITE_RULE[CONJ_COMM] ALOOKUP_ALL_DISTINCT_MEM) \\
      impl_tac >- MATCH_ACCEPT_TAC ALL_DISTINCT_MAP_FST_stubs \\ simp[] ) \\
    rw[] \\
    reverse CASE_TAC >- (
      imp_res_tac ALOOKUP_MEM \\
      qpat_x_assum`MAP FST p4 = _`(assume_tac o SYM) \\ fs[] \\
      fs[EVERY_MEM,EVERY_MAP,FORALL_PROD] \\
      res_tac \\
      imp_res_tac(SIMP_RULE(std_ss)[MEM_MAP,Once EXISTS_PROD,PULL_EXISTS]MAP_FST_stubs_bound) \\
      fs[] ) \\
    match_mp_tac ALOOKUP_ALL_DISTINCT_MEM \\
    simp[MAP_MAP_o,o_DEF,LAMBDA_PROD,data_to_wordTheory.compile_part_def,FST_triple,MEM_MAP,EXISTS_PROD] \\
    metis_tac[ALOOKUP_MEM] ) \\
  `code_rel_ext (fromAList t_code) (fromAList p5)` by metis_tac[code_rel_ext_word_to_word] \\
  qpat_x_assum`Abbrev(tar_st = _)`kall_tac \\
  (* syntactic properties from stack_to_lab *)
  `all_enc_ok_pre c4.lab_conf.asm_conf p7` by (
    fs[Abbr`p7`,Abbr`stoff`,Abbr`stk`]>>
    match_mp_tac stack_to_lab_compile_all_enc_ok>>
    fs[stackPropsTheory.reg_name_def,Abbr`c4`,mc_conf_ok_def]>>
    unabbrev_all_tac >>
    fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]>>rfs[]>>
    `-8w ≤ 0w:'a word ∧ 0w:'a word ≤ 8w` by
      fs[WORD_LE,labPropsTheory.good_dimindex_def,word_2comp_n2w,dimword_def,word_msb_n2w]>>
    metis_tac[])>>
  `labels_ok p7` by
    (fs[Abbr`p7`]>>
    match_mp_tac stack_to_lab_compile_lab_pres>>
    rw[]>>EVAL_TAC>>
    fs[EVERY_MEM]>> rpt strip_tac>>
    first_x_assum drule>>
    EVAL_TAC>>rw[])>>
  (data_to_wordProofTheory.compile_semantics
   |> GEN_ALL
   |> SIMP_RULE (srw_ss()) [markerTheory.Abbrev_def]
   |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["t","co","x1","start","prog","c"]))
   |> Q.ISPECL_THEN [`word_st`,`data_oracle`]mp_tac) \\
  disch_then(qspecl_then[`fromAList t_code`,`InitGlobals_location`,`p4`,`c4_data_conf`]mp_tac) \\
  (* TODO: make this auto *)
  disch_then(qspecl_then[`tt`,`kk`,`c4.lab_conf.asm_conf`,`aa`]mp_tac) \\
  impl_tac >- (
    simp[Abbr`word_st`,word_to_stackProofTheory.make_init_def,Abbr`c4`,Abbr`c4_data_conf`] \\
    (*
    qmatch_goalsub_rename_tac`c5.data_conf` \\ qunabbrev_tac`c5` \\
    *)
    fs[mc_conf_ok_def] \\
    conj_tac >- (
      simp[Abbr`stack_st`] \\
      simp[full_make_init_def,stack_allocProofTheory.make_init_def,Abbr`stack_st_opt`] ) \\
    simp[Abbr`stack_st`] \\
    conj_tac>-
      (match_mp_tac (GEN_ALL IMP_init_store_ok)
       \\ simp[Abbr`stack_st_opt`]
       \\ metis_tac[PAIR])>>
    fs[Abbr`stack_st_opt`,full_make_init_buffer]>>
    fs[Abbr`lab_st`,full_make_init_ffi]>>
    fs[Abbr`word_oracle`,Abbr`t_code`,domain_fromAList]>>
    conj_tac
    >- fs [data_to_wordTheory.conf_ok_def,
           data_to_wordTheory.shift_length_def] \\
    CONJ_TAC>- (
      fs[Abbr`data_oracle`,full_co_def,bvi_tailrecProofTheory.mk_co_def]>>
      `∀n. EVERY ((<=) data_num_stubs o FST) (compile_prog (SND (clos_co n)))`
        suffices_by simp[EVERY_o,EVERY_MAP,LAMBDA_PROD] \\
      simp[EVERY_o] ) \\
      (*
    conj_tac >- (
    *)
      AP_TERM_TAC>>
      simp[data_to_wordTheory.compile_part_def,FST_triple,MAP_MAP_o,o_DEF,LAMBDA_PROD])>>
   (* CONJ_TAC>-
      fs[make_init_def]>> *)
  `lab_st.ffi = ffi` by ( fs[Abbr`lab_st`] ) \\
  `word_st.ffi = ffi` by (
    simp[Abbr`word_st`,word_to_stackProofTheory.make_init_def] \\
    fs[Abbr`stack_st`,Abbr`lab_st`,Abbr`stack_st_opt`] \\
    fs [full_make_init_def,stack_allocProofTheory.make_init_def,
        stack_removeProofTheory.make_init_any_ffi] \\ EVAL_TAC) \\
  `ffi.final_event = NONE` by
    fs[installed_def,good_init_state_def]>>
  (*impl_tac >- fs[Abbr`word_st`,word_to_stackProofTheory.make_init_def] \\ *)
  strip_tac \\
  qmatch_abbrev_tac`x ⊆ extend_with_resource_limit y` \\
  `Fail ∉ y` by fs[Abbr`y`] \\
  pop_assum mp_tac \\ simp[GSYM implements_def] \\
  simp[Abbr`y`] \\
  drule (GEN_ALL semantics_compile) \\
  disch_then(drule o CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(optionSyntax.is_some o rhs))))) \\
  simp[Abbr`c4`] \\
  disch_then(drule o CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``good_init_state`` o fst o strip_comb))))) \\
  disch_then(qspec_then`lab_oracle`mp_tac) \\
  impl_tac >- (
    conj_tac >- (
      simp[compiler_oracle_ok_def,good_code_def] \\
      fs[Abbr`stack_oracle`,Abbr`word_oracle`,Abbr`data_oracle`,Abbr`lab_oracle`] >>
      conj_tac >- (
        simp[PAIR_MAP] >>
        simp[compile_no_stubs_def]>>
        EVAL_TAC>>
        gen_tac \\ pairarg_tac \\ fs[] \\
        rpt(pairarg_tac \\ fs[]) \\ rveq \\
        pop_assum mp_tac \\ EVAL_TAC \\ strip_tac \\
        rveq \\ simp[])>>
      simp[Abbr`clos_co`] \\
      rpt(pairarg_tac \\ fs[]) \\
      fs[full_co_def,bvi_tailrecProofTheory.mk_co_def] \\
      rpt(pairarg_tac \\ fs[]) \\
      fs[bvl_inlineProofTheory.state_co_def] \\
      rpt(pairarg_tac \\ fs[]) \\
      rveq \\ fs[] \\
      rveq \\ fs[])>>
    fs[good_code_def,labels_ok_def] \\
    (*
    qmatch_goalsub_rename_tac`c5.lab_conf.labels` \\ qunabbrev_tac`c5` >>
    *)
    rfs[]>>rw[]
    >-
      fs[Abbr`p7`,stack_to_labTheory.compile_def]
    >-
      (match_mp_tac (MP_CANON EVERY_MONOTONIC)>>
      simp[Once CONJ_COMM]>>
      qpat_x_assum`all_enc_ok_pre _ _` kall_tac>>
      asm_exists_tac>>
      simp[]>>Cases>> simp[]>>
      rpt(pop_assum kall_tac)>>
      metis_tac [EVERY_sec_label_ok])
    >-
      (qpat_x_assum`ALL_DISTINCT (MAP _ p7)` mp_tac>>
      qmatch_goalsub_abbrev_tac`MAP ff p7`>>
      `ff = Section_num` by
        (simp[Abbr`ff`,FUN_EQ_THM]>>
        Cases>>simp[])>>
      simp[])
    >-
      (match_mp_tac (MP_CANON EVERY_MONOTONIC)>>
      simp[Once CONJ_COMM]>>
      qpat_x_assum`all_enc_ok_pre _ _` kall_tac>>
      asm_exists_tac>>
      simp[]>>Cases>> simp[]))>>
  strip_tac \\
  qpat_x_assum`Abbrev(stack_st_opt = _)`(mp_tac o REWRITE_RULE[markerTheory.Abbrev_def]) \\
  disch_then(assume_tac o SYM) \\
  Cases_on`stack_st_opt` \\
  drule full_make_init_semantics \\
  (*
  qmatch_asmsub_rename_tac`c5 with bvl_conf updated_by _` \\
  qunabbrev_tac`c5` \\ fs[] \\
  *)
  impl_tac >- (
    simp_tac std_ss [Once EVERY_FST_SND] \\
    qunabbrev_tac`stack_st` \\
    fs[Abbr`lab_st`,make_init_def] \\
    fs[mc_init_ok_def, mc_conf_ok_def, Abbr`stk`,byte_aligned_MOD] \\
    `max_heap_limit (:'a) c4_data_conf = max_heap_limit (:'a) c.data_conf` by
      (simp[Abbr`c4_data_conf`] \\ EVAL_TAC) \\
    conj_tac>- fs[Abbr`p7`] \\
    conj_tac>- simp[ETA_AX] \\
    conj_tac >- (
      rfs[memory_assumption_def,Abbr`dm`]
      \\ qmatch_goalsub_abbrev_tac`a <=+ b` >>
      `(w2n:'a word -> num) bytes_in_word = dimindex (:α) DIV 8` by
       rfs [labPropsTheory.good_dimindex_def,bytes_in_word_def,dimword_def]>>
      fs [attach_bitmaps_def] \\
      once_rewrite_tac[INTER_COMM] \\
      rewrite_tac[UNION_OVER_INTER] \\
      once_rewrite_tac[UNION_COMM] \\
      strip_tac \\
      match_mp_tac fun2set_disjoint_union \\
      conj_tac >- (
        match_mp_tac DISJOINT_INTER
        \\ metis_tac[DISJOINT_SYM] ) \\
      conj_tac >- (
        fs[attach_bitmaps_def] )
      \\ (
        match_mp_tac word_list_exists_imp>>
        fs [addresses_thm]>>
        fs[mc_conf_ok_def]>>
        `0 < dimindex (:α) DIV 8` by
          rfs [labPropsTheory.good_dimindex_def]>>
        reverse conj_tac >-
         (fs [] \\ match_mp_tac IMP_MULT_DIV_LESS \\ fs [w2n_lt]
          \\ rfs [labPropsTheory.good_dimindex_def])
        \\ `a <=+ b` by metis_tac[WORD_LOWER_IMP_LOWER_OR_EQ]
        \\ drule WORD_LS_IMP \\ strip_tac \\ fs [EXTENSION]
        \\ fs [IN_DEF,PULL_EXISTS,bytes_in_word_def,word_mul_n2w]
        \\ rw [] \\ reverse eq_tac THEN1
         (rw [] \\ fs [] \\ qexists_tac `i * (dimindex (:α) DIV 8)` \\ fs []
          \\ `0 < dimindex (:α) DIV 8` by rfs [labPropsTheory.good_dimindex_def]
          \\ drule X_LT_DIV \\ disch_then (fn th => fs [th])
          \\ fs [RIGHT_ADD_DISTRIB]
          \\ fs [GSYM word_mul_n2w,GSYM bytes_in_word_def]
          \\ fs [byte_aligned_mult])
        \\ rw [] \\ fs []
        \\ `i < dimword (:'a)` by metis_tac [LESS_TRANS,w2n_lt] \\ fs []
        \\ qexists_tac `i DIV (dimindex (:α) DIV 8)`
        \\ rfs [alignmentTheory.byte_aligned_def,
             ONCE_REWRITE_RULE [WORD_ADD_COMM] alignmentTheory.aligned_add_sub]
        \\ fs [stack_removeProofTheory.aligned_w2n]
        \\ drule DIVISION
        \\ disch_then (qspec_then `i` (strip_assume_tac o GSYM))
        \\ `2 ** LOG2 (dimindex (:α) DIV 8) = dimindex (:α) DIV 8` by
             (fs [labPropsTheory.good_dimindex_def] \\ NO_TAC)
        \\ fs [] \\ rfs [] \\ `-1w * a + b = b - a` by fs []
        \\ full_simp_tac std_ss []
        \\ Cases_on `a` \\ Cases_on `b`
        \\ full_simp_tac std_ss [WORD_LS,addressTheory.word_arith_lemma2]
        \\ fs [] \\ match_mp_tac DIV_LESS_DIV \\ fs []
        \\ rfs [] \\ fs [] \\ match_mp_tac MOD_SUB_LEMMA \\ fs []))>>
    conj_tac>- (
      fs[stack_to_labProofTheory.good_code_def]>>
      rfs[]>>
      CONJ_TAC>-
        (fs[ALL_DISTINCT_MAP_FST_stubs,ALL_DISTINCT_APPEND]
        \\ fs[EVERY_MEM]
        \\ rw[] \\ CCONTR_TAC \\ fs[]
        \\ res_tac
        \\ imp_res_tac MAP_FST_stubs_bound
        \\ pop_assum mp_tac \\ EVAL_TAC
        \\ pop_assum mp_tac \\ EVAL_TAC
        \\ pop_assum mp_tac \\ EVAL_TAC
        \\ TRY (
          strip_tac
          \\ qpat_x_assum`MEM k _ `mp_tac
          \\ EVAL_TAC
          \\ simp[] \\ NO_TAC )
        \\ decide_tac )>>
      (* simple syntactic thing *)
      simp[EVERY_FST_SND]>>
      CONJ_TAC>- EVAL_TAC>>
      `!k. data_num_stubs<= k ⇒ stack_num_stubs <=k` by
        (EVAL_TAC>>fs[])>>
      CONJ_TAC>-
        EVAL_TAC>>
      metis_tac[EVERY_MONOTONIC])
    >>
      fs[stack_to_labProofTheory.good_code_def,Abbr`stack_oracle`]>>
      fs[Abbr`word_oracle`,Abbr`data_oracle`]>>
      simp[PAIR_MAP] >>
      EVAL_TAC >>
      gen_tac >>
      pairarg_tac >> fs[] >>
      EVAL_TAC )>>
  CASE_TAC
  >- (
    strip_tac \\
    match_mp_tac (GEN_ALL (MP_CANON implements_trans)) \\
    simp[Once CONJ_COMM] \\ rfs[] \\
    asm_exists_tac \\ simp[] \\
    metis_tac[dataPropsTheory.Resource_limit_hit_implements_semantics] ) \\
  fs[Abbr`word_st`] \\ rfs[] \\
  strip_tac \\
  match_mp_tac (GEN_ALL (MP_CANON implements_trans)) \\
  qmatch_assum_abbrev_tac`z InitGlobals_location ∈ _ {_}` \\
  qexists_tac`{z InitGlobals_location}` \\
  fsrw_tac [ETA_ss] []>>
  conj_tac >- (
    match_mp_tac (GEN_ALL(MP_CANON implements_intro_ext)) \\
    simp[] ) \\
  simp[Abbr`z`] \\
  (word_to_stackProofTheory.compile_semantics
   |> Q.GENL[`t`,`code`,`asm_conf`,`start`]
   |> GEN_ALL
   |> Q.ISPECL_THEN[`kkk`,`word_oracle`,`stack_st`,`p5`,`c.lab_conf.asm_conf`,`InitGlobals_location`]mp_tac) \\
  impl_tac >- (
    fs[] \\
    conj_tac >- (
      fs[Abbr`stack_st`,full_make_init_def]
      \\ rveq
      \\ fs[stack_allocProofTheory.make_init_def] ) \\
    conj_tac >- (
      fs[Abbr`kkk`,Abbr`stk`]) >>
    conj_tac >- (
      match_mp_tac (GEN_ALL IMP_init_state_ok) \\
      fs[Abbr`kkk`,Abbr`stk`]>>
      fs[mc_conf_ok_def,backend_config_ok_def,Abbr`stack_st`] >>
      rfs[ETA_AX,Abbr`word_oracle`,Abbr`data_oracle`]>>
      simp[PAIR_MAP] >>
      simp[GSYM PULL_EXISTS] >>
      drule compile_word_to_stack_bitmaps>>
      CASE_TAC>>strip_tac>>
      fs[attach_bitmaps_def]>>
      CONV_TAC(STRIP_QUANT_CONV(LAND_CONV EVAL)) >>
      simp[UNCURRY] >>
      simp[Abbr`clos_co`,full_co_def,bvi_tailrecProofTheory.mk_co_def,bvl_inlineProofTheory.state_co_def] >>
      rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[] \\ rveq \\ fs[] \\
      metis_tac[])>>
    conj_tac >- (
      qunabbrev_tac`t_code` \\
      imp_res_tac data_to_word_names \\
      simp[ALOOKUP_NONE] \\
      conj_tac >- EVAL_TAC \\
      strip_tac \\ fs[EVERY_MEM] \\
      res_tac \\ pop_assum mp_tac >> EVAL_TAC) \\
    conj_tac >- (
      simp[Abbr`stack_st`] \\
      fs[full_make_init_def] \\ rveq \\
      simp[stack_allocProofTheory.make_init_def,
           stack_removeProofTheory.make_init_any_bitmaps] ) \\
    conj_tac >- (
      fs[EVERY_MEM,FORALL_PROD] \\
      metis_tac[] ) \\
    strip_tac \\ fs[] \\
    fs[extend_with_resource_limit_def] ) \\
  strip_tac \\
  match_mp_tac (GEN_ALL (MP_CANON implements_trans)) \\
  qmatch_assum_abbrev_tac`z ∈ _ {_}` \\
  qexists_tac`{z}` \\
  conj_tac >- (
    match_mp_tac (GEN_ALL(MP_CANON implements_intro_ext)) \\
    simp[] ) \\
  simp[Abbr`z`] \\
  simp[Abbr`stack_st`] \\
  simp[Abbr`x`] \\
  match_mp_tac (GEN_ALL (MP_CANON implements_trans)) \\
  ONCE_REWRITE_TAC[CONJ_COMM] \\
  asm_exists_tac \\ simp[]
  \\ first_x_assum match_mp_tac
  \\ match_mp_tac (GEN_ALL extend_with_resource_limit_not_fail)
  \\ asm_exists_tac \\ simp[]
  \\ CONV_TAC(RAND_CONV SYM_CONV)
  \\ match_mp_tac (GEN_ALL extend_with_resource_limit_not_fail)
  \\ asm_exists_tac \\ simp[]);
  *)

val _ = export_theory();
