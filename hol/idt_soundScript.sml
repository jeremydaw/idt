(*
Intuitionistic Dual Tableaux
paper "Tableaus and Dual Tableaus", by Melvin Fitting, August 2016
*)

(* 
load "idt_soundTheory" ;
open idt_soundTheory ;

use "idt_soundScript.sml" ;
*)

open HolKernel boolLib bossLib ;

val _ = new_theory "idt_sound" ;

open pred_setTheory pairTheory relationTheory arithmeticTheory ;
open idt_lemmasTheory idt_genTheory idtLib ;

val _ = Datatype `formula = And formula formula 
                          | Or formula formula
			  | Imp formula formula
			  | Not formula
			  | Atom 'a` ;

val formula_size_def = definition "formula_size_def" ;

val formula_size_gt_0 = Q.store_thm ("formula_size_gt_0",
  `!f. 0 < formula_size (\x. 0) f`,
  Induct THEN ASM_SIMP_TAC arith_ss [formula_size_def]) ;

val formula_size_ne_0 = 
  REWRITE_RULE [GSYM NOT_ZERO_LT_ZERO] formula_size_gt_0 ;

val EX_EQ_LEM' = CONV_RULE (ONCE_DEPTH_CONV (LHS_CONV
  (ONCE_DEPTH_CONV (REWR_CONV EQ_SYM_EQ)))) EX_EQ_LEM ;

val formula_size_1_Atom = Q.store_thm ("formula_size_1_Atom",
  `{f | formula_size (\x. 0) f = 1} = IMAGE Atom UNIV`,
  Ho_Rewrite.REWRITE_TAC [EXTENSION, IN_IMAGE, BETA_THM, 
    GSPECIFICATION, PAIR_EQ, EX_EQ_LEM', IN_UNIV] THEN
  Cases THEN SRW_TAC [] [formula_size_def, formula_size_ne_0]) ;

val formula_size_n = Q.store_thm ("formula_size_n",
  `{f | formula_size (\x. 0) f = SUC (SUC n)} =
    IMAGE (UNCURRY And) 
      {(f,g) | formula_size (\x. 0) f + formula_size (\x. 0) g = SUC n} UNION 
    IMAGE (UNCURRY Or) 
      {(f,g) | formula_size (\x. 0) f + formula_size (\x. 0) g = SUC n} UNION 
    IMAGE (UNCURRY Imp) 
      {(f,g) | formula_size (\x. 0) f + formula_size (\x. 0) g = SUC n} UNION 
    IMAGE Not {f | formula_size (\x. 0) f = SUC n}`,
  Ho_Rewrite.REWRITE_TAC [EXTENSION, IN_IMAGE, IN_UNION, BETA_THM, 
    GSPECIFICATION, PAIR_EQ, IN_UNCURRY, EX_EQ_LEM'] THEN
  REPEAT (STRIP_TAC ORELSE REVERSE EQ_TAC) THEN
  TRY BasicProvers.VAR_EQ_TAC  THEN
  RULE_L_ASSUM_TAC (CONJUNCTS o
    Ho_Rewrite.REWRITE_RULE [BETA_THM, UNCURRY_VAR, PAIR_EQ]) THEN
  TRY BasicProvers.VAR_EQ_TAC  THEN
  REWRITE_TAC [UNCURRY_DEF, formula_size_def] THEN
  ASM_SIMP_TAC arith_ss [] THEN
  REVERSE (Cases_on `x`) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [formula_size_def, GSYM
    SUC_ONE_ADD, prim_recTheory.INV_SUC_EQ]) THEN
  SRW_TAC [] [UNCURRY_VAR] THEN
  TRY (Q.EXISTS_TAC `(f, f0)`) THEN
  ASM_REWRITE_TAC [FST, SND]) ;

val formula_n_countable = Q.store_thm ("formula_countable",
  `countable (UNIV : 'a set) ==>
    !n. countable {f | formula_size (\x : 'a. 0) f <= n}`,
  DISCH_TAC THEN Induct THEN1
  REWRITE_TAC [LESS_EQ_0, formula_size_ne_0, GSPEC_F, countable_EMPTY] THEN
  Ho_Rewrite.REWRITE_TAC [LE, GSPEC_OR, union_countable_IFF] THEN
  ASM_REWRITE_TAC [] THEN
  Cases_on `n` THEN1
    (REWRITE_TAC [GSYM ONE, formula_size_1_Atom] THEN
    irule image_countable THEN
    FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC [formula_size_n, union_countable_IFF] THEN
  REVERSE (REPEAT CONJ_TAC) THEN
  REPEAT (irule image_countable) THEN1
    (POP_ASSUM_LIST (ASSUME_TAC o hd) THEN
    IMP_RES_THEN MATCH_MP_TAC subset_countable THEN
    Ho_Rewrite.REWRITE_TAC [SUBSET_DEF, IN_GSPEC_IFF] THEN
    ASM_SIMP_TAC arith_ss []) THEN
  POP_ASSUM_LIST (fn th :: _ =>
    ASSUME_TAC (MATCH_MP cross_countable (CONJ th th))) THEN
  IMP_RES_THEN MATCH_MP_TAC subset_countable THEN
  Ho_Rewrite.REWRITE_TAC 
    [SUBSET_DEF, IN_CROSS, IN_GSPEC_IFF, IN_GSPEC_PAIR] THEN
  Cases THEN SIMP_TAC arith_ss []) ;

(* signed formula *)
val _ = Parse.type_abbrev ("sf", ``: (bool # 'a formula)``) ;

(* this for lists 
val mk_seq_def = Define 
  `mk_seq bfs = (MAP SND (FILTER ($= F o FST) bfs),
    MAP SND (FILTER ($= T o FST) bfs))` ; 

``mk_seq : (bool # 'a) list -> 'a list # 'a list`` ;
*)

(* set of signed items could be expressed either as a set of
  (bool # item) or as a sequent *)
val get_fs_def = Define `get_fs sfs = IMAGE SND (sfs INTER ($~ o FST))` ;
val get_ts_def = Define `get_ts sfs = IMAGE SND (sfs INTER FST)` ;

``get_fs : (bool # 'a) set -> 'a set`` ;
``get_ts : (bool # 'a) set -> 'a set`` ;

(*
val mk_seq_def = Define `mk_seq bfs =
    (IMAGE SND (bfs INTER ($~ o FST)), IMAGE SND (bfs INTER FST))` ; 
    *)
val mk_seq_def = Define `mk_seq bfs = (get_fs bfs, get_ts bfs)` ; 

val mk_seq_def' = REWRITE_RULE [get_fs_def, get_ts_def] mk_seq_def ;

``mk_seq : (bool # 'a) set -> 'a set # 'a set`` ;

val dest_seq_def = Define `dest_seq (fs, ts) = 
  IMAGE ($, F) fs UNION IMAGE ($, T) ts` ;
  
``dest_seq : 'a set # 'a set -> (bool # 'a) set`` ;

val lemT = Q.store_thm ("lemT", 
  `x IN IMAGE SND (bfs INTER FST) = (T, x) IN bfs`,
  REWRITE_TAC [IN_IMAGE] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) 
  THENL [ Cases_on `x'` THEN
    RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE
	[INTER_applied, IN_APP, combinTheory.o_THM, FST]) THEN
      FULL_SIMP_TAC std_ss [IN_APP, SND],
    Q.EXISTS_TAC `(T, x)` THEN
      ASM_REWRITE_TAC [INTER_applied, IN_APP, SND, FST]]);

val lemF = Q.store_thm ("lemF", 
  `x IN IMAGE SND (bfs INTER $~ o FST) = (F, x) IN bfs`,
  REWRITE_TAC [IN_IMAGE] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) 
  THENL [ Cases_on `x'` THEN
    RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE
	[INTER_applied, IN_APP, combinTheory.o_THM, FST]) THEN
      FULL_SIMP_TAC std_ss [IN_APP, SND],
    Q.EXISTS_TAC `(F, x)` THEN
      ASM_REWRITE_TAC [INTER_applied, 
	combinTheory.o_THM, IN_APP, SND, FST] ]) ;

val lemT' = REWRITE_RULE ([GSYM get_ts_def]) lemT ;
val lemF' = REWRITE_RULE ([GSYM get_fs_def]) lemF ;

(* maybe these easier defined as inductively defined sets *)

val (get_fsi_rules, get_fsi_ind, get_fsi_cases) = Hol_reln
  `!sfs x. sfs (F, x) ==> get_fsi sfs x` ;
val (get_tsi_rules, get_tsi_ind, get_tsi_cases) = Hol_reln
  `!sfs x. sfs (T, x) ==> get_tsi sfs x` ;

val get_ts_i = Q.store_thm ("get_ts_i", `get_tsi = get_ts`,
  REWRITE_TAC [FUN_EQ_THM,
    get_ts_def, get_tsi_cases, REWRITE_RULE [IN_APP] lemT]) ;

val get_fs_i = Q.store_thm ("get_fs_i", `get_fsi = get_fs`,
  REWRITE_TAC [FUN_EQ_THM,
    get_fs_def, get_fsi_cases, REWRITE_RULE [IN_APP] lemF]) ;

val [get_fs_rules, get_fs_ind, get_fs_cases] = 
  map (REWRITE_RULE [get_fs_i]) [get_fsi_rules, get_fsi_ind, get_fsi_cases] ;
val [get_ts_rules, get_ts_ind, get_ts_cases] = 
  map (REWRITE_RULE [get_ts_i]) [get_tsi_rules, get_tsi_ind, get_tsi_cases] ;

val lemc = Q.prove (`(b, x) IN IMAGE ($, y) q = (b = y) /\ x IN q`,
  REWRITE_TAC [IN_IMAGE] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
  FULL_SIMP_TAC std_ss []) ;

val tac13 = RES_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [IN_UNION, lemc]) THEN FIRST_ASSUM ACCEPT_TAC ;

val tac24 = RULE_ASSUM_TAC GSYM THEN ASM_REWRITE_TAC [IN_UNION, lemc] ;
  
val mk_dest_seq = Q.store_thm ("mk_dest_seq",
  `(dest_seq s = p) = (mk_seq p = s)`,
  Cases_on `s` THEN
  REWRITE_TAC [EXTENSION, dest_seq_def, mk_seq_def',
    PAIR_EQ, lemT, lemF] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) 
  THENL [ tac13, tac24, tac13, tac24,
    Cases_on `x` THEN FULL_SIMP_TAC std_ss [IN_UNION, lemc],
    Cases_on `x` THEN REWRITE_TAC [IN_UNION, lemc] THEN
      Cases_on `q'` THEN REV_FULL_SIMP_TAC std_ss [] ]) ;

val mk_seq_UNION = Q.store_thm ("mk_seq_UNION", `mk_seq (A UNION B) = 
  let (AF, AT) = mk_seq A in let (BF, BT) = mk_seq B in
  (AF UNION BF, AT UNION BT)`,
  Ho_Rewrite.REWRITE_TAC [mk_seq_def', LET_DEF, UNCURRY_DEF,
    BETA_THM, lemT, lemF, PAIR_EQ, EXTENSION, IN_UNION]) ;

(* a rule (in the sense of what happens to a single item)
  becomes a rule (in sense of what happens to a set of items),
  for tableaux, item is a signed formula, U is the context *)
val (is_tab_rule_rules, is_tab_rule_ind, is_tab_rule_cases) = Hol_reln
  `!s st U. is_tab_rule (s, st) (s INSERT U, IMAGE ($UNION U) st)` ;

(* same, but where only antecedent context is allowed in result,
  general context in top *)
val (is_ag_tab_rule_rules, is_ag_tab_rule_ind, is_ag_tab_rule_cases) =
  Hol_reln `!s st U. is_ag_tab_rule (s, st)
    (s INSERT U, IMAGE ($UNION (U INTER ($~ o FST))) st)` ;

(* same, but where only antecedent context is allowed in top and bottom *)
val (is_aa_tab_rule_rules, is_aa_tab_rule_ind, is_aa_tab_rule_cases) =
  Hol_reln `!s st U. is_aa_tab_rule (s, st)
    (s INSERT (U INTER ($~ o FST)), IMAGE ($UNION (U INTER ($~ o FST))) st)` ;

``is_tab_rule : 'a rule_sk -> 'a set rule -> bool`` ;
``is_ag_tab_rule : (bool # 'a) rule_sk -> (bool # 'a) set rule -> bool`` ;
``is_aa_tab_rule : (bool # 'a) rule_sk -> (bool # 'a) set rule -> bool`` ;

(* 
show_types := true ;
show_types := false ;
*)

(* now, specifically for intuitionistic dual tableaux, per Figure 6 *)
val (and_left_rules, and_left_ind, and_left_cases) =
  Hol_reln `!X Y. and_left ((F, And X Y), 
    {{(F, And X Y); (F, X); (F, Y)}})` ;

val (or_right_rules, or_right_ind, or_right_cases) =
  Hol_reln `!X Y. or_right ((T, Or X Y), 
    {{(T, Or X Y); (T, X); (T, Y)}})` ;

val (or_left_rules, or_left_ind, or_left_cases) =
  Hol_reln `!X Y. or_left ((F, Or X Y), 
    {{(F, Or X Y); (F, X)}; {(F, Or X Y); (F, Y)}})` ;

val (and_right_rules, and_right_ind, and_right_cases) =
  Hol_reln `!X Y. and_right ((T, And X Y), 
    {{(T, And X Y); (T, X)}; {(T, And X Y); (T, Y)}})` ;

``[and_left; and_right; or_left; or_right] : 'a sf rule_sk set list`` ;

val (imp_left_rules, imp_left_ind, imp_left_cases) =
  Hol_reln `!X Y. imp_left ((F, Imp X Y), 
    {{(F, Imp X Y); (T, X)}; {(F, Imp X Y); (F, Y)}})` ;

val (not_left_rules, not_left_ind, not_left_cases) =
  Hol_reln `!X. not_left ((F, Not X), {{(F, Not X); (T, X)}})` ;

(* these two only keep side-formulae on the left, don't keep principal fml *)
val (imp_right_rules, imp_right_ind, imp_right_cases) =
  Hol_reln `!X Y. imp_right ((T, Imp X Y), {{(F, X); (T, Y)}})` ;

val (not_right_rules, not_right_ind, not_right_cases) =
  Hol_reln `!X. not_right ((T, Not X), {{(F, X)}})` ;

``or_left : 'a sf rule_sk set`` ;
``or_left : ((bool # 'a formula) # ((bool # 'a formula) set set)) set`` ;

val rule_cases = [and_left_cases, or_right_cases, or_left_cases,
  and_right_cases, imp_left_cases, not_left_cases, 
  imp_right_cases, not_right_cases] ;

(* the rules which permit normal contexts *)
val (gen_idt_rule_rules, gen_idt_rule_ind, gen_idt_rule_cases) =
  Hol_reln `(!gr. and_left gr ==> gen_idt_rule gr) /\
    (!gr. or_left gr ==> gen_idt_rule gr) /\
    (!gr. imp_left gr ==> gen_idt_rule gr) /\
    (!gr. not_left gr ==> gen_idt_rule gr) /\
    (!gr. and_right gr ==> gen_idt_rule gr) /\
    (!gr. or_right gr ==> gen_idt_rule gr)` ;

val [and_left_gen_idt, or_left_gen_idt, imp_left_gen_idt, 
    not_left_gen_idt, and_right_gen_idt, or_right_gen_idt] =
  CONJUNCTS gen_idt_rule_rules ;

val and_left_gen_idt' = MATCH_MP and_left_gen_idt (SPEC_ALL and_left_rules) ;
val or_left_gen_idt' = MATCH_MP or_left_gen_idt (SPEC_ALL or_left_rules) ;
val imp_left_gen_idt' = MATCH_MP imp_left_gen_idt (SPEC_ALL imp_left_rules) ;
val not_left_gen_idt' = MATCH_MP not_left_gen_idt (SPEC_ALL not_left_rules) ;
val and_right_gen_idt' = MATCH_MP and_right_gen_idt (SPEC_ALL and_right_rules) ;
val or_right_gen_idt' = MATCH_MP or_right_gen_idt (SPEC_ALL or_right_rules) ;

val (ant_idt_rule_rules, ant_idt_rule_ind, ant_idt_rule_cases) =
  Hol_reln `(!gr. imp_right gr ==> ant_idt_rule gr) /\
    (!gr. not_right gr ==> ant_idt_rule gr)` ;

val [imp_right_ant_idt, not_right_ant_idt] = CONJUNCTS ant_idt_rule_rules ;

val imp_right_ant_idt' = MATCH_MP imp_right_ant_idt (SPEC_ALL imp_right_rules) ;
val not_right_ant_idt' = MATCH_MP not_right_ant_idt (SPEC_ALL not_right_rules) ;

val (idt_tab_rule_rules, idt_tab_rule_ind, idt_tab_rule_cases) = Hol_reln
  `(!gr rule. gen_idt_rule gr /\ is_tab_rule gr rule ==> idt_tab_rule rule) /\
  (!gr rule. ant_idt_rule gr /\ is_ag_tab_rule gr rule ==> idt_tab_rule rule)`;

``idt_tab_rule : 'a sf set rule set`` ;

val idt_tab_rule_cases' = CONV_RULE (ONCE_DEPTH_CONV 
  (LHS_CONV (REWR_CONV (GSYM IN_APP)))) idt_tab_rule_cases ;

val gen_rule_cases =
  [idt_tab_rule_cases, gen_idt_rule_cases, ant_idt_rule_cases,
  is_tab_rule_cases, is_ag_tab_rule_cases, is_aa_tab_rule_cases] ;

val [idt_tab_rule_rule1, idt_tab_rule_rule2] = CONJUNCTS idt_tab_rule_rules ;

val gen_idt_lem = Q.store_thm ("gen_idt_lem",
  `gen_idt_rule (sf, sfss) ==> sf IN esf ==> 
    idt_tab_rule (esf, IMAGE ($UNION esf) sfss)`,
  REPEAT STRIP_TAC THEN irule idt_tab_rule_rule1 THEN
  Q.EXISTS_TAC `(sf, sfss)` THEN
  ASM_REWRITE_TAC [is_tab_rule_cases, PAIR_EQ] THEN
  Q.EXISTS_TAC `sf` THEN Q.EXISTS_TAC `sfss` THEN
  Q.EXISTS_TAC `esf` THEN FULL_SIMP_TAC std_ss [ABSORPTION]) ;

val iirules = ListPair.map save_thm
  (["and_left_in_skel", "or_left_in_skel", "imp_left_in_skel",
    "not_left_in_skel", "and_right_in_skel", "or_right_in_skel"],
  map (MATCH_MP gen_idt_lem) 
    [and_left_gen_idt', or_left_gen_idt', imp_left_gen_idt',
      not_left_gen_idt', and_right_gen_idt', or_right_gen_idt']) ;

val ant_idt_lem = Q.store_thm ("ant_idt_lem",
  `ant_idt_rule (sf, sfss) ==> sf IN esf ==> 
    idt_tab_rule (esf, IMAGE ($UNION (esf INTER $~ o FST)) sfss)`,
  REPEAT STRIP_TAC THEN irule idt_tab_rule_rule2 THEN
  Q.EXISTS_TAC `(sf, sfss)` THEN
  ASM_REWRITE_TAC [is_ag_tab_rule_cases, PAIR_EQ] THEN
  Q.EXISTS_TAC `sf` THEN Q.EXISTS_TAC `sfss` THEN
  Q.EXISTS_TAC `esf` THEN FULL_SIMP_TAC std_ss [ABSORPTION]) ;

val imp_right_in_skel = save_thm ("imp_right_in_skel",
  MATCH_MP ant_idt_lem imp_right_ant_idt') ;
val not_right_in_skel = save_thm ("not_right_in_skel",
  MATCH_MP ant_idt_lem not_right_ant_idt') ;

val IDT_RULE_NON_EMPTY = Q.store_thm ("IDT_RULE_NON_EMPTY",
  `~ ((EMPTY, rb) IN idt_tab_rule)`,
  REWRITE_TAC (IN_APP :: gen_rule_cases @ rule_cases) THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [PAIR_EQ, NOT_EMPTY_INSERT]) THEN
  FIRST_ASSUM ACCEPT_TAC ) ;

(* useful properties of these rule sets *)
val IDT_RULE_SND_FINITE = Q.store_thm ("IDT_RULE_SND_FINITE",
  `(s, st) IN (gen_idt_rule UNION ant_idt_rule) ==> FINITE st`,
  REWRITE_TAC ([IN_APP, IN_UNION,
    gen_idt_rule_cases, ant_idt_rule_cases] @ rule_cases) THEN
  REPEAT STRIP_TAC THEN REPEAT BasicProvers.VAR_EQ_TAC THEN
  RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [PAIR_EQ]) THEN
  REPEAT BasicProvers.VAR_EQ_TAC THEN REWRITE_TAC [SND] THEN
  REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY]) ;
    
val IDT_FINITE_BRANCHING = Q.store_thm ("IDT_FINITE_BRANCHING",
  `IMAGE SND idt_tab_rule SUBSET FINITE`,
  REWRITE_TAC [SUBSET_DEF, IN_IMAGE, IN_APP, idt_tab_rule_cases,
    is_tab_rule_cases, is_ag_tab_rule_cases] THEN
  REPEAT STRIP_TAC THEN REPEAT BasicProvers.VAR_EQ_TAC THEN
  REWRITE_TAC [SND] THEN irule IMAGE_FINITE THEN
  IMP_RES_TAC (REWRITE_RULE [IN_APP, IN_UNION] IDT_RULE_SND_FINITE)) ;
    
val idt_mono = Q.store_thm ("idt_mono",
  `(s, bots) IN idt_tab_rule ==> s SUBSET t ==>
    ?bott.  (t, bott) IN idt_tab_rule /\ 
      !bt. bt IN bott ==> ?bs. bs IN bots /\ bs SUBSET bt`,
  REWRITE_TAC [idt_tab_rule_cases', is_tab_rule_cases, is_ag_tab_rule_cases,
    PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN REPEAT BasicProvers.VAR_EQ_TAC 
  THENL [
    Q.EXISTS_TAC `IMAGE ($UNION t) st` THEN CONJ_TAC  
    THENL [
      DISJ1_TAC THEN Q.EXISTS_TAC `(s', st)` THEN
	ASM_REWRITE_TAC [PAIR_EQ] THEN Q.EXISTS_TAC `s'` THEN
	Q.EXISTS_TAC `st` THEN Q.EXISTS_TAC `t` THEN REWRITE_TAC [] THEN
	irule (GSYM ABSORPTION_RWT) THEN
	FULL_SIMP_TAC std_ss [INSERT_SUBSET],
      REWRITE_TAC [IN_IMAGE] THEN REPEAT STRIP_TAC THEN
	Q.EXISTS_TAC `U UNION x` THEN
	CONJ_TAC THEN1 (Q.EXISTS_TAC `x` THEN ASM_REWRITE_TAC []) THEN
	BasicProvers.VAR_EQ_TAC THEN
	REWRITE_TAC [UNION_SUBSET, SUBSET_UNION] THEN
	RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [INSERT_SUBSET]) THEN
	FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP SUBSET_TRANS') THEN
	REWRITE_TAC [SUBSET_UNION] ],

    Q.EXISTS_TAC `IMAGE ($UNION (t INTER $~ o FST)) st` THEN CONJ_TAC  
    THENL [
      DISJ2_TAC THEN Q.EXISTS_TAC `(s', st)` THEN
	ASM_REWRITE_TAC [PAIR_EQ] THEN Q.EXISTS_TAC `s'` THEN
	Q.EXISTS_TAC `st` THEN Q.EXISTS_TAC `t` THEN REWRITE_TAC [] THEN
	irule (GSYM ABSORPTION_RWT) THEN
	FULL_SIMP_TAC std_ss [INSERT_SUBSET],
      REWRITE_TAC [IN_IMAGE] THEN REPEAT STRIP_TAC THEN
	Q.EXISTS_TAC `U INTER $~ o FST UNION x` THEN
	CONJ_TAC THEN1 (Q.EXISTS_TAC `x` THEN ASM_REWRITE_TAC []) THEN
	BasicProvers.VAR_EQ_TAC THEN
	REWRITE_TAC [UNION_SUBSET, SUBSET_UNION] THEN
	RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [INSERT_SUBSET]) THEN
	irule (MATCH_MP SUBSET_TRANS'' (SPEC_ALL (CONJUNCT1 SUBSET_UNION))) THEN
	REWRITE_TAC [INTER_SUBSET, SUBSET_INTER] THEN
	FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP SUBSET_TRANS'') THEN
	REWRITE_TAC [INTER_SUBSET] ]]) ;

(* now for the semantics,
  pval = valuation (forcing) for propositional letters *)

(* persistence of valuation *)
val persistent_def = Define 
  `persistent R pv = !v w a. R v w ==> pv v a ==> pv w a` ;

(* forcing - depends on R, valuation of propositions, and world *)
val forces_def = Define
  `(forces R pv w (And p q) = forces R pv w p /\ forces R pv w q) /\
  (forces R pv w (Or p q) = forces R pv w p \/ forces R pv w q) /\
  (forces R pv w (Atom a) = pv w a) /\
  (forces R pv w (Imp p q) = 
    !v. R w v ==> forces R pv v p ==> forces R pv v q) /\
  (forces R pv w (Not p) = !v. R w v ==> ~ forces R pv v p) ` ;

(* forces : 'w is world, 'p is atomic proposition *)
``forces : ('w -> 'w -> bool) -> ('w -> 'p -> bool) -> 
  'w -> 'p formula -> bool`` ;

(* note, first occurrence of "persistent" is about a function on atoms,
  second occurrence is about a function on formulae *)
val FORCES_PERSISTENT = Q.store_thm ("FORCES_PERSISTENT",
  `transitive R ==> persistent R pv ==> persistent R (forces R pv)`,
  REWRITE_TAC [persistent_def, transitive_def] THEN
  REPEAT DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN RES_TAC THEN
  Induct_on `a` THEN REWRITE_TAC [forces_def] THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN ASM_REWRITE_TAC [] THEN RES_TAC) ;

(* conditions for Kripke model *)
val Kripke_model_def = Define
  `Kripke_model R pv = transitive R /\ reflexive R /\ persistent R pv` ;

val FORCES_IF_ALL = Q.store_thm ("FORCES_IF_ALL",
  `Kripke_model R pv ==> ((!v. R w v ==> forces R pv v f) = forces R pv w f)`,
  Ho_Rewrite.REWRITE_TAC [Kripke_model_def] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) 
  THENL [ POP_ASSUM irule THEN
      IMP_RES_TAC reflexive_def THEN ASM_REWRITE_TAC [],
    IMP_RES_TAC FORCES_PERSISTENT THEN
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE [persistent_def]) THEN RES_TAC]) ;

(* dual tableau (branch) closed *)
val br_closed_def = 
  Define `br_closed sfs = ?p. (T, p) IN sfs /\ (F, p) IN sfs` ;

val dt_closed_def = 
  Define `dt_closed sfss = !sfs. sfs IN sfss ==> br_closed sfs` ;

(* and atomically *)
val at_closed_def = 
  Define `at_closed sfs = ?p. (T, Atom p) IN sfs /\ (F, Atom p) IN sfs` ;

``at_closed : 'a sf set -> bool`` ;
``br_closed : 'a sf set -> bool`` ;
``dt_closed : 'a sf set set -> bool`` ;

val br_closed_mono = Q.store_thm ("br_closed_mono",
  `br_closed s ==> s SUBSET t ==> br_closed t`,
  REWRITE_TAC [br_closed_def, SUBSET_DEF] THEN
  REPEAT STRIP_TAC THEN Q.EXISTS_TAC `p` THEN
  RES_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC) ;

val dt_closed_mono = Q.store_thm ("dt_closed_mono",
  `dt_closed s ==> t SUBSET s ==> dt_closed t`,
  REWRITE_TAC [dt_closed_def, SUBSET_DEF] THEN
  REPEAT STRIP_TAC THEN REPEAT RES_TAC) ;

(* operation of a tableau rule on a tableau, you apply the rule to one branch,
  here identifying the branch with the node at its end, and 
  identifying the tableau with its fringe, ie the nodes at ends of branches *)
(* but we use extend_fringe above, not r(s)2fps *)

val (r2fps_rules, r2fps_ind, r2fps_cases) = 
  Hol_reln `!br brs obs. r2fps (br, brs) (br INSERT obs, brs UNION obs)` ;

``r2fps : ('a rule) -> ('a set # 'a set) -> bool`` ;

(* r2fps turns one rule into a set of fringe pairs, 
  want to turn a set of rules to a set of fringe pairs,
  this is just set monad ext *)
val rs2fps_def = Define `rs2fps = BIGUNION o IMAGE r2fps` ;
``rs2fps : ('a rule set) -> ('a set # 'a set) -> bool`` ;

(* now we apply tableau rules repeatedly by taking transitive closure of this *)
``(CURRY o rs2fps) : ('a rule set) -> 'a set -> 'a set set`` ;

(* so the set of tableaux starting from a particular node is got by
  (CURRY o rs2fps) rules {node} *)

(* valuation, according to propositional valuation pv, 
  of a branch and a tableau (ie, fringe), at a world w *)
val sfs_val_aux_def = Define `sfs_val_aux R pv v sfs =  
  let (Fs, Ts) = mk_seq sfs 
  in (!f. f IN Fs ==> forces R pv v f) ==>
    (?t. t IN Ts /\ forces R pv v t)` ;

val sfs_val_def = Define `sfs_val R pv w sfs =  
  !v. R w v ==> sfs_val_aux R pv v sfs` ;

``sfs_val_aux : ('w -> 'w -> bool) -> ('w -> 'p -> bool) -> 
  'w -> 'p sf set -> bool`` ;
``sfs_val : ('w -> 'w -> bool) -> ('w -> 'p -> bool) -> 
  'w -> 'p sf set -> bool`` ;

val sfs_val_aux_alt = Q.store_thm ("sfs_val_aux_alt",
  `sfs_val_aux R pv v sfs = 
    (!f. (F,f) IN sfs ==> forces R pv v f) ==>
    (?t. (T,t) IN sfs /\ forces R pv v t)`,
  Ho_Rewrite.REWRITE_TAC [sfs_val_aux_def,
    mk_seq_def', BETA_THM, UNCURRY_DEF, LET_THM, lemF, lemT]) ;

val sfs_val_aux_UNION = Q.store_thm ("sfs_val_aux_UNION",
  `sfs_val_aux R pv w (A UNION B) = 
    sfs_val_aux R pv w A \/ sfs_val_aux R pv w B`,
  Cases_on `mk_seq A` THEN Cases_on `mk_seq B` THEN
  Ho_Rewrite.ASM_REWRITE_TAC [sfs_val_aux_def, mk_seq_UNION,
    LET_DEF, BETA_THM, UNCURRY_DEF] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
  RULE_ASSUM_TAC (Ho_Rewrite.REWRITE_RULE
    [IMP_DISJ_THM, NOT_FORALL_THM, DE_MORGAN_THM, IN_UNION]) THEN
  Ho_Rewrite.REWRITE_TAC 
    [IMP_DISJ_THM, NOT_FORALL_THM, DE_MORGAN_THM] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THEN
  FIRST_X_ASSUM CHOOSE_TAC THEN_LT
  TRYALL ( Q.EXISTS_TAC `t` THEN
    FIRST_X_ASSUM (DISJ_CASES_TAC o Q.SPEC `f`) THEN
    FULL_SIMP_TAC std_ss [IN_UNION]) THEN
  FIRST_X_ASSUM (DISJ_CASES_TAC o REWRITE_RULE [RIGHT_AND_OVER_OR]) THEN
  Ho_Rewrite.REWRITE_TAC [GSYM EXISTS_OR_THM] 
  THENL (map Q.EXISTS_TAC [`f`, `f`, `t`, `t`]) THEN
  ASM_REWRITE_TAC []) ;

val tab_val_aux_def = 
  Define `tab_val_aux R pv w fss = 
    (!sfs. sfs IN fss ==> sfs_val_aux R pv w sfs)` ;

``tab_val_aux : ('w -> 'w -> bool) -> ('w -> 'p -> bool) -> 
  'w -> 'p sf set set -> bool`` ;
``tab_val : ('w -> 'w -> bool) -> ('w -> 'p -> bool) -> 
  'w -> 'p sf set set -> bool`` ;

val tab_val_def = 
  Define `tab_val R pv w fss = (!sfs. sfs IN fss ==> sfs_val R pv w sfs)` ;

``tab_val : ('w -> 'w -> bool) -> ('w -> 'p -> bool) -> 
  'w -> 'p sf set set -> bool`` ;

val tab_val_alt = Q.store_thm ("tab_val_alt",
  `tab_val R pv w fss = !v. R w v ==> tab_val_aux R pv v fss`,
  REWRITE_TAC [tab_val_def, tab_val_aux_def, sfs_val_def] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN RES_TAC) ;
    

(** soundness **)
(* for a sf rule *)
``idt_tab_rule : 'a sf set rule set`` ;

(* 
show_types := true ;
show_types := false ;
*)

(* gen_idt_rules are simpler, in fact equivalences *)

val erwtac = REPEAT BasicProvers.VAR_EQ_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [forces_def]) THEN
  Ho_Rewrite.ASM_REWRITE_TAC [RIGHT_AND_OVER_OR, EXISTS_OR_THM, EX_EQ_LEM] ;

fun ntac q = 
  VALIDATE (FIRST_X_ASSUM (ASSUME_TAC o UNDISCH o Q.SPEC q))
  THENL [ RULE_ASSUM_TAC (REWRITE_RULE [reflexive_def]) THEN
	ASM_REWRITE_TAC [], 
    FULL_SIMP_TAC std_ss [] ] ;

val idt_rules_aux_eqv = Q.store_thm ("idt_rules_aux_eqv",
  `reflexive R ==> gen_idt_rule ((b, f), sfss) ==> 
    (tab_val_aux R pv w sfss = sfs_val_aux R pv w {(b,f)})`,
  REWRITE_TAC (PAIR_EQ :: gen_idt_rule_cases :: rule_cases) THEN
  REPEAT STRIP_TAC THEN
  Ho_Rewrite.ASM_REWRITE_TAC [forces_def, tab_val_aux_def, sfs_val_aux_alt,
    IN_INSERT, NOT_IN_EMPTY, ALL_EQ_LEM, DISJ_IMP_THM,
    FORALL_AND_THM, PAIR_EQ, EX_EQ_LEM] THEN 
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
  RES_TAC THEN erwtac THENL [ntac `w`, ntac `w`]) ;

val idt_rules_eqv = Q.store_thm ("idt_rules_eqv",
  `reflexive R ==> gen_idt_rule ((b, f), sfss) ==> 
    (tab_val R pv w sfss = sfs_val R pv w {(b,f)})`,
  REWRITE_TAC [tab_val_alt, sfs_val_def] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC idt_rules_aux_eqv THEN ASM_REWRITE_TAC []) ;

(* next, is_tab_rule preserves this property *)
val is_tab_rule_pres_eqv = Q.store_thm ("is_tab_rule_pres_eqv",
  `is_tab_rule (sf, sfss) (esf, esfss) ==> 
    (tab_val_aux R pv w sfss = sfs_val_aux R pv w {sf}) ==>
  (tab_val_aux R pv w esfss = sfs_val_aux R pv w esf)`,
  REWRITE_TAC [is_tab_rule_cases, tab_val_aux_def, PAIR_EQ,
    Once INSERT_SING_UNION, sfs_val_aux_UNION] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
  REPEAT BasicProvers.VAR_EQ_TAC 
  THENL [ RULE_ASSUM_TAC GSYM THEN
      ASM_REWRITE_TAC [sfs_val_aux_UNION, DISJ_NOT_IMP2] THEN
      REPEAT STRIP_TAC THEN
      VALIDATE (FIRST_X_ASSUM (ASSUME_TAC o UNDISCH o Q.SPEC `U UNION sfs`))
      THENL [ irule IMAGE_IN THEN FIRST_ASSUM ACCEPT_TAC,
	POP_ASSUM (DISJ_CASES_TAC o REWRITE_RULE [sfs_val_aux_UNION]) THEN
	  FULL_SIMP_TAC std_ss [] ],
    RULE_ASSUM_TAC GSYM THEN
    REV_FULL_SIMP_TAC std_ss [sfs_val_aux_UNION, IN_IMAGE] ]) ;

val ant_rules_eqv = Q.store_thm ("ant_rules_eqv",
  `transitive R ==> reflexive R ==> ant_idt_rule ((b, f), sfss) ==> 
    (tab_val R pv w sfss = sfs_val R pv w {(b,f)})`,
  REWRITE_TAC (PAIR_EQ :: ant_idt_rule_cases :: rule_cases) THEN
  REPEAT STRIP_TAC THEN
  Ho_Rewrite.ASM_REWRITE_TAC [forces_def, tab_val_def, sfs_val_def,
    sfs_val_aux_alt, IN_INSERT, NOT_IN_EMPTY, ALL_EQ_LEM, DISJ_IMP_THM,
    FORALL_AND_THM, PAIR_EQ, EX_EQ_LEM] THEN
  (REPEAT (STRIP_TAC ORELSE EQ_TAC) 
  THENL [ RULE_ASSUM_TAC (REWRITE_RULE [transitive_def]) THEN 
      RES_TAC THEN RES_TAC,
    RULE_ASSUM_TAC (REWRITE_RULE [reflexive_def]) THEN RES_TAC THEN
      POP_ASSUM irule THEN TRY (Q.EXISTS_TAC `v`) THEN ASM_REWRITE_TAC [] ])) ;

val lemf = Q.prove (`(a, b) IN f o FST = f a`, SIMP_TAC std_ss [IN_DEF]) ;

val ant_ctxt_eqv = Q.store_thm ("ant_ctxt_eqv",
  `Kripke_model R pv ==> (sfs_val R pv w ((U INTER $~ o FST) UNION sfs) = 
  !v. R w v ==> (!f. (F, f) IN U ==> forces R pv v f) ==> sfs_val R pv v sfs)`,
  Ho_Rewrite.REWRITE_TAC [mk_seq_def', sfs_val_def, sfs_val_aux_alt, lemf,
    IN_UNION, IN_INTER, FORALL_AND_THM, DISJ_IMP_THM, Kripke_model_def] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) 
  THENL [ FIRST_X_ASSUM (irule o Q.SPEC `v'`) 
      THENL [ IMP_RES_TAC FORCES_PERSISTENT THEN
	  POP_ASSUM (ASSUME_TAC o REWRITE_RULE [persistent_def]) THEN
	  REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC,
	FIRST_ASSUM ACCEPT_TAC,
	RULE_ASSUM_TAC (REWRITE_RULE [transitive_def]) THEN RES_TAC],
    RULE_ASSUM_TAC (REWRITE_RULE [reflexive_def]) THEN RES_TAC THEN
      POP_ASSUM irule THEN ASM_REWRITE_TAC [] ]) ;

(* next, is_aa_tab_rule preserves this property *)
val is_aa_tab_rule_pres_eqv = Q.store_thm ("is_aa_tab_rule_pres_eqv",
  `Kripke_model R pv ==> is_aa_tab_rule (sf, sfss) (esf, esfss) ==> 
    (!v. R w v ==> (tab_val R pv v sfss = sfs_val R pv v {sf})) ==>
    (tab_val R pv w esfss = sfs_val R pv w esf)`,
  REWRITE_TAC [is_aa_tab_rule_cases, tab_val_def, PAIR_EQ, 
    Once INSERT_SING_UNION'] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
  REPEAT BasicProvers.VAR_EQ_TAC 
  THENL [
    IMP_RES_THEN (fn th => REWRITE_TAC [th]) ant_ctxt_eqv THEN
    REPEAT STRIP_TAC THEN RULE_ASSUM_TAC GSYM THEN
    RES_TAC THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
    VALIDATE (FIRST_X_ASSUM 
      (ASSUME_TAC o UNDISCH o Q.SPEC `(U ∩ $~ ∘ FST) UNION sfs`))
    THENL [
      irule IMAGE_IN THEN FIRST_ASSUM ACCEPT_TAC, 
      IMP_RES_THEN (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) ant_ctxt_eqv
	THEN RES_TAC],
    IMP_RES_THEN (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) ant_ctxt_eqv
      THEN IMP_RES_THEN CHOOSE_TAC imageE THEN
      RULE_L_ASSUM_TAC CONJUNCTS THEN
      BasicProvers.VAR_EQ_TAC THEN 
      IMP_RES_THEN (fn th => REWRITE_TAC [th]) ant_ctxt_eqv THEN
      REPEAT STRIP_TAC THEN RES_TAC ]) ;

val aa_ag_tab_rule = Q.store_thm ("aa_ag_tab_rule",
  `is_ag_tab_rule (sf, sfss) (esf, esfss) ==> ?isf.
    is_aa_tab_rule (sf, sfss) (isf, esfss) /\ (isf SUBSET esf)`,
  REWRITE_TAC [is_ag_tab_rule_cases, PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN REPEAT BasicProvers.VAR_EQ_TAC THEN
  Q.EXISTS_TAC `(U INTER $~ ∘ FST) UNION {s}` THEN REPEAT STRIP_TAC 
  THENL [ MATCH_ACCEPT_TAC 
      (REWRITE_RULE [Once INSERT_SING_UNION'] is_aa_tab_rule_rules),
    REWRITE_TAC [SUBSET_DEF, IN_UNION, IN_INTER, IN_INSERT, NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] ]) ;

(* weakening *)
val sfs_val_wk = Q.store_thm ("sfs_val_wk",
  `sfs_val R pv v A ==> sfs_val R pv v (A UNION B)`,
  REWRITE_TAC [mk_seq_def', sfs_val_def, sfs_val_aux_UNION] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC []) ;

val sfs_val_wk_sub = Q.store_thm ("sfs_val_wk_sub",
  `A SUBSET C ==> sfs_val R pv v A ==> sfs_val R pv v C`,
  REPEAT STRIP_TAC THEN
  IMP_RES_THEN (ASSUME_TAC o Q.SPEC `C`) sfs_val_wk THEN
  REV_FULL_SIMP_TAC std_ss [SUBSET_UNION_ABSORPTION] ) ;

val (Kripke_model_imp, _) = EQ_IMP_RULE (SPEC_ALL Kripke_model_def) ;

val is_tab_rule_pres_eqv' = 
  MODIFY_CONS (#1 o EQ_IMP_RULE) is_tab_rule_pres_eqv ;

val idt_pres = Q.store_thm ("idt_pres",
  `Kripke_model R pv ==> idt_tab_rule (sfs, sfss) ==> 
    tab_val R pv w sfss ==> sfs_val R pv w sfs`,
  DISCH_TAC THEN IMP_RES_TAC Kripke_model_imp THEN
  Ho_Rewrite.REWRITE_TAC [EXISTS_PROD, idt_tab_rule_cases] THEN
  REPEAT STRIP_TAC
  THENL [
  (* gen_idt_rule *)
  REWRITE_TAC [sfs_val_def] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [tab_val_alt]) THEN
    REPEAT STRIP_TAC THEN RES_TAC THEN
    irule is_tab_rule_pres_eqv' THEN
    Q.EXISTS_TAC `sfss` THEN Q.EXISTS_TAC `(p_1, p_2)` THEN
    Q.EXISTS_TAC `p_2'` THEN ASM_REWRITE_TAC [] THEN
    irule idt_rules_aux_eqv THEN ASM_REWRITE_TAC [],
  (* ant_idt_rule *)
  IMP_RES_TAC aa_ag_tab_rule THEN
    rpt_irt (ASSUME_TAC o GEN_ALL) ant_rules_eqv THEN
    rpt_irt (ASSUME_TAC o GEN_ALL) is_aa_tab_rule_pres_eqv THEN
    irule sfs_val_wk_sub THEN Q.EXISTS_TAC `isf` THEN
    FULL_SIMP_TAC std_ss [] ]) ;

val idt_br_sound = Q.store_thm ("idt_br_sound",
  `br_closed br ==> sfs_val R pv w br`,
  Ho_Rewrite.REWRITE_TAC [br_closed_def, sfs_val_def, sfs_val_aux_alt ] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN Q.EXISTS_TAC `p` THEN ASM_REWRITE_TAC []) ;

val idt_dt_sound = Q.store_thm ("idt_dt_sound", 
  `dt_closed tab ==> tab_val R pv w tab`,
  REWRITE_TAC [dt_closed_def, tab_val_def] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN 
  IMP_RES_TAC idt_br_sound THEN ASM_REWRITE_TAC []) ;

(* "rules" to transform fringe of tableau *)
``extend_fringe idt_tab_rule : ('a sf set set # 'a sf set set) set`` ;

(* need idt_pres for fringe *)
val idt_pres_frg = Q.store_thm ("idt_pres_frg",
  `Kripke_model R pv ==> extend_fringe idt_tab_rule (prev, next) ==> 
    tab_val R pv w next ==> tab_val R pv w prev`,
  REWRITE_TAC [extend_fringe_cases, tab_val_def, PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN REPEAT BasicProvers.VAR_EQ_TAC THEN
  rpt_irt (ASSUME_TAC o REWRITE_RULE [tab_val_def]) idt_pres THEN
  RULE_ASSUM_TAC (Ho_Rewrite.REWRITE_RULE
    [IN_INSERT, IN_UNION, FORALL_AND_THM, DISJ_IMP_THM]) THEN
  FULL_SIMP_TAC std_ss []) ;

(* whole tableau, repeatedly transform fringe *)
``RTC (CURRY (extend_fringe idt_tab_rule)) :
  'a sf set set -> 'a sf set set -> bool`` ;

val tab_val_single = Q.store_thm ("tab_val_single",
  `Kripke_model R pv ==> (tab_val R pv w {{(T,f)}} = forces R pv w f)`,
  Ho_Rewrite.REWRITE_TAC [tab_val_def, sfs_val_def, sfs_val_aux_alt,
    IN_INSERT, NOT_IN_EMPTY, ALL_EQ_LEM, EX_EQ_LEM, PAIR_EQ] THEN
  MATCH_ACCEPT_TAC FORCES_IF_ALL) ;

val tvsr = MODIFY_CONS (#1 o EQ_IMP_RULE) tab_val_single ;

val idt_rtc_pres_frg = Q.store_thm ("idt_rtc_pres_frg",
  `Kripke_model R pv ==> 
  !bot. RTC (CURRY (extend_fringe idt_tab_rule)) top bot ==>
  tab_val R pv w bot ==> tab_val R pv w top`,
  DISCH_TAC THEN HO_MATCH_MP_TAC RTC_ALT_RIGHT_INDUCT THEN
  REWRITE_TAC [CURRY_DEF] THEN REPEAT STRIP_TAC THEN
  rpt_irt ASSUME_TAC idt_pres_frg THEN RES_TAC) ;

val idt_sound = Q.store_thm ("idt_sound",
  `Kripke_model R pv ==> 
  RTC (CURRY (extend_fringe idt_tab_rule)) {{(T,f)}} bot ==>
  dt_closed bot ==> forces R pv w f`,
  REPEAT STRIP_TAC THEN IMP_RES_THEN irule tvsr THEN
  rpt_irt irule idt_rtc_pres_frg THEN
  irule idt_dt_sound THEN FIRST_ASSUM ACCEPT_TAC) ;

(* 
show_assums := true ;
show_assums := false ;
show_types := true ;
show_types := false ;
*)

val _ = export_theory () ;

