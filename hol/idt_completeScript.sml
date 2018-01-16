(*
Intuitionistic Dual Tableaaux
paper "Tableaus and Dual Tableaus", by Melvin Fitting, August 2016
*)

(* 

load "idt_completeTheory" ;
open idt_completeTheory ;
load "idtLib" ;
val _ = set_trace "Unicode" 0;

use "idt_soundScript.sml" ;

open proofManagerLib ;
load "idt_soundTheory" ;
use "idt_completeScript.sml" ;
*)

open HolKernel boolLib bossLib ;

open pred_setTheory pairTheory relationTheory ;
open idt_soundTheory idt_genTheory idt_lemmasTheory idtLib ;

val _ = new_theory "idt_complete" ;

(* completeness *)

(* forget atomic, inactive, finite stipulations for the time being *)

val Itautss_def = Define `Itautss rs s =
  ?bot. RTC (CURRY (extend_fringe rs)) s bot /\ dt_closed bot` ;
``Itautss : 'a sf set rule set -> 'a sf set set -> bool`` ;

val Itauts_def = Define `Itauts rs s = Itautss rs {s}` ;
``Itauts : 'a sf set rule set -> 'a sf set -> bool`` ;

val fItauts_def = Define 
  `fItauts rs s = ?s'. FINITE s' /\ s' SUBSET s /\ Itauts rs s'` ;
``fItauts : 'a sf set rule set -> 'a sf set -> bool`` ;

val (Itauti_rules, Itauti_ind, Itauti_cases) = Hol_reln
  `(!top. br_closed top ==> Itauti rs top) /\
  (!top. (?rb. (top,rb) IN rs /\ !br. br IN rb ==> Itauti rs br) ==>
    Itauti rs top)` ;

val [Itauti_rule1, Itauti_rule2] = CONJUNCTS (SPEC_ALL Itauti_rules) ;
val Itauti_rule2' = Ho_Rewrite.REWRITE_RULE [GSYM LEFT_FORALL_IMP_THM, 
  GSYM AND_IMP_INTRO] Itauti_rule2 ;

(* to confirm the equivalence of the two formulations of Itauti,
  see paper above lemma Itauti_ind *)
val Itauti_rule_alt = Q.prove (
`(!top. br_closed top ==> Itautx rs top) /\
(!top. (?rb. (top,rb) IN rs /\ !br. br IN rb ==> Itautx rs br) ==>
  Itautx rs top) <=> 
!top.( (br_closed top) \/ 
 (?rb. (top,rb) IN rs /\ !br. br IN rb ==> Itautx rs br)) ==>
   Itautx rs top`,
  mesonLib.MESON_TAC []) ;

(* variation of Itauti which allows specifying the definition of closed *)
val (Itautg_rules, Itautg_ind, Itautg_cases) = Hol_reln
  `(!top. cl top ==> Itautg cl rs top) /\
  (!top. (?rb. (top,rb) IN rs /\ !br. br IN rb ==> Itautg cl rs br) ==>
    Itautg cl rs top)` ;
val [Itautg_rule1, Itautg_rule2] = CONJUNCTS (SPEC_ALL Itautg_rules) ;

val Itauti_ind' = REORDER_ANTS I Itauti_ind ;
val Itautg_ind' = REORDER_ANTS I Itautg_ind ;

val Itauti_g = Q.store_thm ("Itauti_g", 
  `Itauti = Itautg br_closed`,
  REWRITE_TAC [FUN_EQ_THM] THEN REPEAT GEN_TAC THEN EQ_TAC 
  THENL [HO_MATCH_MP_TAC Itauti_ind' THEN MATCH_ACCEPT_TAC Itautg_rules,
  HO_MATCH_MP_TAC Itautg_ind' THEN MATCH_ACCEPT_TAC Itauti_rules]) ;

(* to prove closure implies atomic closure *)
val iirules = [and_left_in_skel, or_left_in_skel, imp_left_in_skel,
    not_left_in_skel, and_right_in_skel, or_right_in_skel] ;

val iirules1 = map (REWRITE_RULE [IMAGE_INSERT, IMAGE_EMPTY]) iirules ;

val iiarules = [imp_right_in_skel, not_right_in_skel] ;

val iiarules1 = map (REWRITE_RULE [IMAGE_INSERT, IMAGE_EMPTY]) iiarules ;

val in_skels = iirules1 @ iiarules1 ;

val iuflem = Q.prove (`(br = sfs INTER $~ o FST UNION s) ==> 
  (F, f) IN sfs ==> (F, f) IN sfs INTER $~ o FST UNION s`,
  REWRITE_TAC [IN_UNION, IN_INTER] THEN
  REWRITE_TAC [IN_APP, o_THM] THEN DECIDE_TAC) ;

val iulem = Q.prove (`(br = sfs UNION s) ==> sf IN sfs ==> sf IN sfs UNION s`,
  REWRITE_TAC [IN_UNION] THEN DECIDE_TAC) ;

val fflem = Q.store_thm ("fflem", `X <=> (X ==> F) ==> F`, DECIDE_TAC) ;

fun NTH_CONV nums conv = 
  let val cnref = ref (0, nums) ; 
    fun nconv tm = 
      let val th = conv tm ;
        val (count, rem_nums) = !cnref ; 
	val nc = count + 1 ;
	fun test (n :: ns) =
	    if n = nc then (true, ns) 
	    (* numbers out of order or repeated, try to recover usefully *)
	    else if n < nc then test ns 
	    else (false, n :: ns) 
	  | test [] = (false, []) ;
	val (allow, nrn) = test rem_nums ;
        val _ = cnref := (nc, nrn) ; 
      in if allow then th else raise UNCHANGED end ;
  in nconv end ;

fun gitacs iir = [ irule Itautg_rule2, 
  MAP_FIRST (fn thi => FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP thi)) iir,
  fn g => CONV_TAC (DEPTH_CONV (NTH_CONV [1] (REWR_CONV IN_APP))) g,
  ONCE_REWRITE_TAC [fflem],
  Ho_Rewrite.REWRITE_TAC [GSYM LEFT_FORALL_IMP_THM, GSYM AND_IMP_INTRO],
  DISCH_THEN (IMP_RES_THEN irule), GEN_TAC,
  REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY], STRIP_TAC] ;

val atac = EVERY (gitacs iiarules1) THEN
  POP_ASSUM (fn th => rpt_irt ASSUME_TAC (MATCH_MP iuflem th) THEN
      REWRITE_TAC [th]) ;
val gtac = EVERY (gitacs iirules1) THEN
  POP_ASSUM (fn th => rpt_irt ASSUME_TAC (MATCH_MP iulem th) THEN
      REWRITE_TAC [th]) ;
fun ftac th = irule th THEN 
  REWRITE_TAC [IN_INTER, IN_UNION, IN_INSERT, NOT_IN_EMPTY] THEN 
  REWRITE_TAC [IN_APP, o_THM] THEN NO_TAC ;

val at_closed_lem = Q.store_thm ("at_closed_lem",
  `!p sfs. (T, p) IN sfs /\ (F, p) IN sfs ==>
  Itautg at_closed idt_tab_rule sfs`,
  REVERSE Induct THEN REPEAT STRIP_TAC THEN1 
  (irule Itautg_rule1 THEN
    REWRITE_TAC [at_closed_def] THEN Q.EXISTS_TAC `a` THEN
    ASM_REWRITE_TAC []) THEN_LT
  TACS_TO_LT [atac, atac, gtac, gtac] THEN
  EVERY (gitacs iirules1) THEN
  BasicProvers.VAR_EQ_TAC THEN FIRST_X_ASSUM ftac) ;

val Itautg_cmono = Q.store_thm ("Itautg_cmono",
  `cl1 SUBSET cl2 ==> !sfs. Itautg cl1 rs sfs ==> Itautg cl2 rs sfs`,
  DISCH_TAC THEN
  HO_MATCH_MP_TAC Itautg_ind THEN REPEAT STRIP_TAC THEN1
  (irule Itautg_rule1 THEN
    RULE_ASSUM_TAC (REWRITE_RULE [SUBSET_DEF, IN_APP]) THEN RES_TAC) THEN
  irule Itautg_rule2 THEN Q.EXISTS_TAC `rb` THEN ASM_REWRITE_TAC []) ;

val Itautg_comp = Q.store_thm ("Itautg_comp",
  `!sfs. Itautg (Itautg cl rs) rs sfs ==> Itautg cl rs sfs`,
  HO_MATCH_MP_TAC Itautg_ind THEN REPEAT STRIP_TAC THEN
  irule Itautg_rule2 THEN Q.EXISTS_TAC `rb` THEN ASM_REWRITE_TAC []) ;

val atomic_closure = Q.store_thm ("atomic_closure",
  `Itauti idt_tab_rule sfs = Itautg at_closed idt_tab_rule sfs`,
  REWRITE_TAC [Itauti_g] THEN EQ_TAC 
  THENL [ DISCH_TAC THEN
      irule Itautg_comp THEN POP_ASSUM MP_TAC THEN
      MATCH_MP_TAC Itautg_cmono THEN
      REWRITE_TAC [SUBSET_DEF, IN_APP, br_closed_def] THEN
      REPEAT STRIP_TAC THEN irule at_closed_lem THEN
      REWRITE_TAC [IN_APP] THEN Q.EXISTS_TAC `p` THEN ASM_REWRITE_TAC [],
    MATCH_MP_TAC Itautg_cmono THEN
      REWRITE_TAC [SUBSET_DEF, IN_APP, at_closed_def, br_closed_def] THEN
      REPEAT STRIP_TAC THEN Q.EXISTS_TAC `Atom p` THEN ASM_REWRITE_TAC []]) ;

val rtci = REORDER_ANTS rev 
  (REWRITE_RULE [GSYM AND_IMP_INTRO] (MODIFY_CONS CONJUNCT2 RTC_RULES)) ;

val idt_tab_rule_cases' = CONV_RULE (ONCE_DEPTH_CONV
  (LHS_CONV (REWR_CONV (GSYM IN_APP)))) idt_tab_rule_cases ;

val ITAUTSS_ALL = Q.store_thm ("ITAUTSS_ALL",
  `FINITE ss ==> (Itautss rs ss = !s. s IN ss ==> Itauts rs s)`,
  REWRITE_TAC [Itauts_def, Itautss_def, dt_closed_def] THEN 
  REPEAT (STRIP_TAC ORELSE EQ_TAC)
  THENL [
    IMP_RES_THEN (ASSUME_TAC o REWRITE_RULE [INSERT_SUBSET, EMPTY_SUBSET] o
	Q.SPEC `{s}`) SUB_TAB THEN
      RES_TAC  THEN Q.EXISTS_TAC `bs` THEN ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN IMP_RES_TAC subsetD THEN RES_TAC,
    RULE_ASSUM_TAC (Ho_Rewrite.REWRITE_RULE [SKOLEM_THM,
        GSYM RIGHT_EXISTS_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM]) THEN
      FIRST_X_ASSUM CHOOSE_TAC THEN RULE_L_ASSUM_TAC CONJUNCTS THEN
      IMP_RES_TAC FINITE_COMBINE_TABS_FUN THEN
      Q.EXISTS_TAC `BIGUNION (IMAGE f ss)` THEN 
      ASM_REWRITE_TAC [IN_BIGUNION, IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN BasicProvers.VAR_EQ_TAC THEN RES_TAC ]) ;

val cfrlem = Q.prove (`(top,rb) IN rs ==> CURRY (extend_fringe rs) {top} rb`,
  REWRITE_TAC [CURRY_DEF, extend_fringe_cases, PAIR_EQ,
    INSERT_EQ_SING', IN_APP] THEN
  DISCH_TAC THEN Q.EXISTS_TAC `rb` THEN Q.EXISTS_TAC `EMPTY` THEN
  Q.EXISTS_TAC `top` THEN ASM_REWRITE_TAC [EMPTY_SUBSET, UNION_EMPTY]) ;
  
val ITAUTI_S = Q.store_thm ("ITAUTI_S",
  `IMAGE SND rs SUBSET FINITE ==> !top. Itauti rs top ==> Itauts rs top`,
  DISCH_TAC THEN HO_MATCH_MP_TAC Itauti_ind THEN REPEAT STRIP_TAC THEN1
    (REWRITE_TAC [Itauts_def, Itautss_def] THEN
      Q.EXISTS_TAC `{top}` THEN
      ASM_REWRITE_TAC [RTC_REFL, dt_closed_def, IN_SING, ALL_EQ_LEM] ) THEN
  IMP_RES_TAC sflem THEN
  IMP_RES_THEN (fn th => 
    RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) ITAUTSS_ALL THEN  
  RULE_ASSUM_TAC (REWRITE_RULE [Itautss_def]) THEN
  REWRITE_TAC [Itauts_def, Itautss_def] THEN 
  FIRST_X_ASSUM CHOOSE_TAC THEN Q.EXISTS_TAC `bot` THEN 
  RULE_L_ASSUM_TAC CONJUNCTS THEN ASM_REWRITE_TAC [] THEN 
  IMP_RES_THEN irule rtci THEN IMP_RES_THEN ACCEPT_TAC cfrlem) ;

val ITAUTS_I' = Q.prove (`dt_closed bot ==>
  !top. (CURRY (extend_fringe rs))^* top bot ==> !t. t IN top ==> Itauti rs t`,
  DISCH_TAC THEN HO_MATCH_MP_TAC RTC_ALT_INDUCT THEN
  REPEAT STRIP_TAC THEN1
    (RULE_ASSUM_TAC (REWRITE_RULE [dt_closed_def]) THEN RES_TAC THEN
    IMP_RES_TAC Itauti_rule1 THEN ASM_REWRITE_TAC []) THEN
  RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE
    [CURRY_DEF, extend_fringe_cases, PAIR_EQ, INSERT_EQ_SING']) THEN
  REPEAT (FIRST_X_ASSUM CHOOSE_TAC) THEN
  RULE_L_ASSUM_TAC CONJUNCTS THEN
  REPEAT BasicProvers.VAR_EQ_TAC THEN
  RULE_L_ASSUM_TAC (CONJUNCTS o Ho_Rewrite.REWRITE_RULE 
    [IN_INSERT, IN_UNION, DISJ_IMP_THM, FORALL_AND_THM]) THEN
  REVERSE (FIRST_X_ASSUM DISJ_CASES_TAC) THEN1 RES_TAC THEN
  BasicProvers.VAR_EQ_TAC THEN irule Itauti_rule2 THEN
  Q.EXISTS_TAC `fr` THEN ASM_REWRITE_TAC [IN_APP] ) ;

val ITAUTS_I = Q.store_thm ("ITAUTS_I",
  `!top. Itauts rs top ==> Itauti rs top`,
  REWRITE_TAC [Itauts_def, Itautss_def] THEN REPEAT STRIP_TAC THEN
  rpt_irt (ACCEPT_TAC o REWRITE_RULE [IN_SING, ALL_EQ_LEM]) ITAUTS_I') ;

val ITAUTS_EQ_I = Q.store_thm ("ITAUTS_EQ_I",
  `IMAGE SND rs SUBSET FINITE ==> (Itauts rs = Itauti rs)`,
  REWRITE_TAC [FUN_EQ_THM] THEN 
  REPEAT STRIP_TAC THEN EQ_TAC THEN1 MATCH_ACCEPT_TAC ITAUTS_I THEN
  IMP_RES_THEN MATCH_ACCEPT_TAC ITAUTI_S) ;

val ITAUTS_EQ_I' = DISCH_ALL (Q.AP_THM (UNDISCH ITAUTS_EQ_I) `top`) ;

val ITAUTS_EQ_I_idt = save_thm ("ITAUTS_EQ_I_idt",
  MATCH_MP ITAUTS_EQ_I IDT_FINITE_BRANCHING) ;

val Itauti_idt_mono = Q.store_thm ("Itauti_idt_mono",
  `!s. Itauti idt_tab_rule s ==> !t. s SUBSET t ==> Itauti idt_tab_rule t`,
  HO_MATCH_MP_TAC Itauti_ind THEN
  REPEAT STRIP_TAC THEN1 (IMP_RES_TAC br_closed_mono THEN
    IMP_RES_TAC Itauti_rule1 THEN ASM_REWRITE_TAC []) THEN
  IMP_RES_TAC idt_mono THEN irule Itauti_rule2 THEN
  Q.EXISTS_TAC `bott` THEN ASM_REWRITE_TAC [] THEN
  REPEAT STRIP_TAC THEN REPEAT RES_TAC ) ;

val Itauts_idt_mono = Q.store_thm ("Itauts_idt_mono",
  `Itauts idt_tab_rule s ==> s SUBSET t ==> Itauts idt_tab_rule t`,
  REWRITE_TAC [MATCH_MP ITAUTS_EQ_I IDT_FINITE_BRANCHING] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC Itauti_idt_mono) ;

val DIFF_SUBSET_IFF_SUBSET_UNION' =
  ONCE_REWRITE_RULE [UNION_COMM] DIFF_SUBSET_IFF_SUBSET_UNION ;

val IDT_RULE_SND_FINITE' = 
  REWRITE_RULE [IN_APP, IN_UNION] IDT_RULE_SND_FINITE ;

(** to prove that I-tautologous is a property of finite character:
  true if a finite subset had the property **)
val EXT_FST_IS_AG = Q.store_thm ("EXT_FST_IS_AG",
  `U SUBSET $~ o FST ==> is_ag_tab_rule (s,st)
    (s INSERT U, IMAGE ($UNION U) st)`,
  REWRITE_TAC [is_ag_tab_rule_cases, PAIR_EQ] THEN
  DISCH_TAC THEN  Q.EXISTS_TAC `s` THEN 
  Q.EXISTS_TAC `st` THEN Q.EXISTS_TAC `U` THEN
  IMP_RES_TAC SUBSET_INTER_ABSORPTION THEN ASM_REWRITE_TAC []) ;

val tac1 = 
  REWRITE_TAC [FINITE_INSERT] THEN REVERSE (irule FINITE_BIGUNION) THEN1 
    (irule IMAGE_FINITE THEN FIRST_ASSUM ACCEPT_TAC) THEN
  Ho_Rewrite.REWRITE_TAC [IN_IMAGE, combinTheory.o_THM, BETA_THM] THEN
  REPEAT STRIP_TAC THEN BasicProvers.VAR_EQ_TAC THEN RES_TAC THEN
  irule FINITE_DIFF THEN ASM_REWRITE_TAC [] ;

val tac2 = 
  Ho_Rewrite.REWRITE_TAC [INSERT_SUBSET, IN_INSERT,
    BIGUNION_SUBSET, IN_IMAGE, combinTheory.o_THM, BETA_THM] THEN
  REPEAT STRIP_TAC THEN BasicProvers.VAR_EQ_TAC THEN 
  RES_TAC THEN irule SUBSET_INSERT_RIGHT THEN
  REWRITE_TAC [DIFF_SUBSET_IFF_SUBSET_UNION'] ;

fun tac3b tmq = 
  REWRITE_TAC [IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN BasicProvers.VAR_EQ_TAC THEN RES_TAC THEN
  FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP Itauti_idt_mono) THEN
  REWRITE_TAC [SUBSET_DEF] THEN GEN_TAC THEN
  Cases_on `x' IN x` THEN1
  (DISCH_THEN (K ALL_TAC) THEN
  FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (REORDER_ANTS rev subsetD)) THEN
  REWRITE_TAC [SUBSET_UNION]) THEN DISCH_TAC THEN
  REWRITE_TAC [IN_UNION, IN_BIGUNION] THEN
  DISJ1_TAC THEN Q.EXISTS_TAC tmq THEN
  ASM_REWRITE_TAC [IN_DIFF, IN_IMAGE] THEN
  Q.EXISTS_TAC `x` THEN ASM_SIMP_TAC std_ss [] ;

val tac0 = 
  HO_MATCH_MP_TAC Itauti_ind THEN
  REWRITE_TAC [br_closed_def] THEN
  REPEAT STRIP_TAC THEN1 (Q.EXISTS_TAC `{(T,p); (F,p)}` THEN
    ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY,
      INSERT_SUBSET, EMPTY_SUBSET] THEN
    irule Itauti_rule1 THEN REWRITE_TAC [br_closed_def] THEN
    Q.EXISTS_TAC `p` THEN REWRITE_TAC [IN_INSERT]) THEN
  RULE_ASSUM_TAC (Ho_Rewrite.REWRITE_RULE [SKOLEM_THM,
      GSYM RIGHT_EXISTS_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM]) THEN
  FIRST_X_ASSUM CHOOSE_TAC THEN 
  RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [idt_tab_rule_cases']) THEN
  FIRST_X_ASSUM (DISJ_CASES_THEN CHOOSE_TAC) THEN 
  RULE_L_ASSUM_TAC CONJUNCTS THEN 
  RULE_ASSUM_TAC (REWRITE_RULE 
    [is_tab_rule_cases, is_ag_tab_rule_cases, PAIR_EQ]) THEN
  REPEAT (POP_ASSUM CHOOSE_TAC) THEN 
  RULE_L_ASSUM_TAC CONJUNCTS THEN
  REPEAT BasicProvers.VAR_EQ_TAC THEN 
  RULE_ASSUM_TAC (Ho_Rewrite.REWRITE_RULE 
    [IN_IMAGE, GSYM LEFT_FORALL_IMP_THM, GSYM AND_IMP_INTRO]) THEN
  RULE_ASSUM_TAC (Ho_Rewrite.ONCE_REWRITE_RULE [SWAP_FORALL_THM]) THEN
  RULE_ASSUM_TAC (Ho_Rewrite.REWRITE_RULE [ALL_EQ_LEM]) THEN
  IMP_RES_TAC IDT_RULE_SND_FINITE' ;

val ITAUTI_IDT_FINITE = Q.store_thm ("ITAUTI_IDT_FINITE",
  `!s. Itauti idt_tab_rule s ==>
    ?t. FINITE t /\ t SUBSET s /\ Itauti idt_tab_rule t`,
  tac0 THENL [
    Q.EXISTS_TAC `s' INSERT BIGUNION (IMAGE (\x. f (U UNION x) DIFF x) st)` THEN
    REPEAT CONJ_TAC THENL [
      tac1,
      tac2 THEN FIRST_ASSUM ACCEPT_TAC,
      irule Itauti_rule2 THEN
	Q.EXISTS_TAC `IMAGE ($UNION (BIGUNION
	  (IMAGE (λx. f (U ∪ x) DIFF x) st))) st` THEN
	CONJ_TAC THEN1
	  (REWRITE_TAC [IN_APP] THEN
	  IMP_RES_THEN MATCH_MP_TAC (CONJUNCT1 idt_tab_rule_rules) THEN
	  irule is_tab_rule_rules) THEN
	tac3b `f (U ∪ x) DIFF x` ],
    Q.EXISTS_TAC `s' INSERT BIGUNION 
      (IMAGE (\x. f (U INTER $~ o FST UNION x) DIFF x) st)` THEN
    REPEAT CONJ_TAC THENL [
      tac1, 
      tac2 THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP SUBSET_TRANS') THEN
	irule UNION_MONO THEN REWRITE_TAC [SUBSET_REFL, INTER_SUBSET],
      irule Itauti_rule2 THEN
	Q.EXISTS_TAC `IMAGE ($UNION (BIGUNION
	  (IMAGE (\x. f (U INTER $~ o FST UNION x) DIFF x) st))) st` THEN
	CONJ_TAC THEN1
	  (REWRITE_TAC [IN_APP] THEN
	  IMP_RES_THEN MATCH_MP_TAC (CONJUNCT2 idt_tab_rule_rules) THEN
	  irule EXT_FST_IS_AG THEN
	  Ho_Rewrite.REWRITE_TAC [BIGUNION_SUBSET, IN_IMAGE, BETA_THM] THEN
	  REPEAT STRIP_TAC THEN BasicProvers.VAR_EQ_TAC THEN RES_TAC THEN
	  REWRITE_TAC [DIFF_SUBSET_IFF_SUBSET_UNION'] THEN
	  FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP SUBSET_TRANS') THEN
	  irule UNION_MONO THEN REWRITE_TAC [INTER_SUBSET, SUBSET_REFL]) THEN
	tac3b `f (U INTER $~ o FST UNION x) DIFF x` ] ]) ;

val FITAUTS_EQ_I = Q.store_thm ("FITAUTS_EQ_I",
  `fItauts idt_tab_rule = Itauti idt_tab_rule`,
  REWRITE_TAC [fItauts_def, FUN_EQ_THM, ITAUTS_EQ_I_idt] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC 
  THENL [ IMP_RES_TAC Itauti_idt_mono,
    MATCH_MP_TAC ITAUTI_IDT_FINITE THEN FIRST_ASSUM ACCEPT_TAC ]) ;

val fItauts_mono = store_thm ("fItauts_mono",
  ``fItauts rs s ==> s SUBSET t ==> fItauts rs t``,
  REWRITE_TAC [fItauts_def] THEN REPEAT STRIP_TAC THEN
  Q.EXISTS_TAC `s'` THEN
  ASM_REWRITE_TAC [] THEN rpt_irt ACCEPT_TAC SUBSET_TRANS') ;

val ITAUT_EX_RULE = Q.store_thm ("ITAUT_EX_RULE",
  `IMAGE SND rs SUBSET FINITE ==> (Itauts rs top = dt_closed {top} \/
    ?rb. (top, rb) IN rs /\ !br. br IN rb ==> Itauts rs br)`,
  DISCH_TAC THEN Ho_Rewrite.REWRITE_TAC
    [UNDISCH ITAUTS_EQ_I, dt_closed_def, IN_SING, ALL_EQ_LEM] THEN
  MATCH_ACCEPT_TAC Itauti_cases) ;

val nier = ONCE_REWRITE_RULE [GSYM NOT_EQ_NOT] (UNDISCH ITAUT_EX_RULE) ;

val NON_ITAUT_RULE = Q.store_thm ("NON_ITAUT_RULE",
  `IMAGE SND rs SUBSET FINITE ==> maxnon (Itauts rs) s ==>
    is_tab_rule (top, bot) SUBSET rs ==> top IN s ==>
    ?br. br IN bot /\ br SUBSET s`,
  DISCH_TAC THEN
  Ho_Rewrite.REWRITE_TAC [maxnon_def, SUBSET_DEF] THEN
  REPEAT STRIP_TAC THEN 
  VALIDATE (FIRST_X_ASSUM (ASSUME_TAC o UNDISCH o
      Q.SPEC `(top INSERT s, IMAGE ($UNION s) bot)`)) THEN1
    REWRITE_TAC [IN_APP, is_tab_rule_rules] THEN
  REV_FULL_SIMP_TAC std_ss [ABSORPTION_RWT] THEN
  RULE_ASSUM_TAC 
    (Ho_Rewrite.REWRITE_RULE [nier, DE_MORGAN_THM, NOT_EXISTS_THM,
      DISJ_IMP_THM, NOT_FORALL_THM, GSYM IMP_DISJ_THM]) THEN
  RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [NOT_IMP]) THEN
  RES_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `br`) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [IN_IMAGE]) THEN
  FIRST_X_ASSUM CHOOSE_TAC THEN
  Q.EXISTS_TAC `x` THEN ASM_REWRITE_TAC [] THEN
  REPEAT STRIP_TAC THEN CCONTR_TAC THEN
  REV_FULL_SIMP_TAC std_ss [] THEN
  REVERSE (Q.SUBGOAL_THEN `s PSUBSET br` ASSUME_TAC) THEN1 RES_TAC THEN
  REPEAT BasicProvers.VAR_EQ_TAC THEN
  REWRITE_TAC [PSUBSET_MEMBER, SUBSET_UNION] THEN
  Q.EXISTS_TAC `x'` THEN ASM_REWRITE_TAC [IN_UNION]) ;

val itrlem = Q.prove (`({top}, bot) IN is_tab_rule (top, bot)`,
  REWRITE_TAC [is_tab_rule_cases, IN_APP] THEN Q.EXISTS_TAC `top` THEN 
  Q.EXISTS_TAC `bot` THEN Q.EXISTS_TAC `EMPTY` THEN 
  REWRITE_TAC [PAIR_EQ, EXTENSION] THEN
  REWRITE_TAC [IN_IMAGE, UNION_EMPTY] THEN mesonLib.MESON_TAC []) ;
  
(* variant of NON_ITAUT_RULE for fItauts,
  now redundant, see NON_ITAUT_RULE_ALT below *)
val NON_FITAUT_RULE' = Q.store_thm ("NON_FITAUT_RULE'",
  `IMAGE SND (idt_tab_rule : 'a sf set rule set) SUBSET FINITE ==>
    maxnon (fItauts idt_tab_rule) (s : 'a sf set) ==>
    is_tab_rule (top, bot) SUBSET idt_tab_rule ==> top IN s ==>
    ?br. br IN bot /\ br SUBSET s`,
  DISCH_TAC THEN Ho_Rewrite.REWRITE_TAC [maxnon_def, SUBSET_DEF] THEN
  REPEAT STRIP_TAC THEN 
  VALIDATE (FIRST_ASSUM (ASSUME_TAC o UNDISCH o Q.SPEC `({top}, bot)`)) THEN1
  REWRITE_TAC [itrlem] THEN CCONTR_TAC THEN
  RULE_ASSUM_TAC 
    (Ho_Rewrite.REWRITE_RULE [DE_MORGAN_THM, NOT_EXISTS_THM,
      DISJ_IMP_THM, NOT_FORALL_THM, GSYM IMP_DISJ_THM, NOT_IMP,
      GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]) THEN
  POP_ASSUM CHOOSE_TAC THEN
  Q.SUBGOAL_THEN `!br. ?ts. br IN bot ==> FINITE ts /\ ts SUBSET s /\
    Itauts idt_tab_rule (f br INSERT ts)` ASSUME_TAC 
  THEN1 (
    Ho_Rewrite.REWRITE_TAC [RIGHT_EXISTS_IMP_THM] THEN
    GEN_TAC THEN DISCH_THEN (fn th => POP_ASSUM (fn thi => 
      ASSUME_TAC (MATCH_MP thi th))) THEN
    VALIDATE (FIRST_X_ASSUM (ASSUME_TAC o UNDISCH o
	Q.SPEC `f (br : 'a sf set) INSERT s`) ) THEN1
      (REWRITE_TAC [PSUBSET_MEMBER, SUBSET_OF_INSERT] THEN
      Q.EXISTS_TAC `f br` THEN
      ASM_REWRITE_TAC [IN_INSERT]) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [fItauts_def]) THEN
    POP_ASSUM CHOOSE_TAC THEN
    RULE_L_ASSUM_TAC CONJUNCTS THEN
    Q.EXISTS_TAC `s' DELETE f br` THEN
    ASM_REWRITE_TAC [GSYM SUBSET_INSERT_DELETE, FINITE_DELETE,
      INSERT_DELETE_SAME] THEN
    POP_ASSUM (MATCH_MP_TAC o MATCH_MP Itauts_idt_mono) THEN
    REWRITE_TAC [SUBSET_OF_INSERT]) THEN
  RULE_ASSUM_TAC (Ho_Rewrite.REWRITE_RULE [ SKOLEM_THM]) THEN
  POP_ASSUM CHOOSE_TAC THEN
  FIRST_X_ASSUM (ASSUME_TAC o REWRITE_RULE [IN_APP, is_tab_rule_rules] o
    Q.SPEC `(top INSERT BIGUNION (IMAGE f' bot),
      IMAGE ($UNION (BIGUNION (IMAGE f' bot))) bot)`) THEN
  VALIDATE (FIRST_X_ASSUM (ASSUME_TAC o UNDISCH o
    MATCH_MP Itauti_rule2' o CONV_RULE (REWR_CONV (GSYM IN_APP))) )
  THEN1 (
    REWRITE_TAC [IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    BasicProvers.VAR_EQ_TAC THEN RES_TAC THEN
    CONV_TAC (REWR_CONV_A (UNDISCH (GSYM ITAUTS_EQ_I'))) THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP Itauts_idt_mono) THEN
    ASM_REWRITE_TAC [INSERT_SUBSET, IN_UNION] THEN
    irule (MATCH_MP SUBSET_TRANS'' (SPEC_ALL (CONJUNCT1 SUBSET_UNION))) THEN
    irule SUBSET_BIGUNION_I THEN irule IMAGE_IN THEN
    FIRST_ASSUM ACCEPT_TAC) THEN
  IMP_RES_THEN irule F_IMP THEN
  REWRITE_TAC [fItauts_def] THEN
  Q.EXISTS_TAC `top INSERT BIGUNION (IMAGE f' bot)` THEN
  ASM_REWRITE_TAC [INSERT_SUBSET, BIGUNION_SUBSET, IN_IMAGE, FINITE_INSERT] THEN
  REPEAT STRIP_TAC  
  THENL [
    irule FINITE_BIGUNION 
    THENL [ REWRITE_TAC [IN_IMAGE] THEN REPEAT STRIP_TAC THEN
	BasicProvers.VAR_EQ_TAC THEN RES_TAC,
      irule IMAGE_FINITE THEN rpt_irt ACCEPT_TAC issflem], 
    BasicProvers.VAR_EQ_TAC THEN RES_TAC,
    irule ITAUTI_S THEN FIRST_ASSUM ACCEPT_TAC ]) ;

val NON_FITAUT_RULE = MATCH_MP NON_FITAUT_RULE' IDT_FINITE_BRANCHING ;

val NON_ITAUT_RULE_idt = MATCH_MP NON_ITAUT_RULE IDT_FINITE_BRANCHING ;
val NON_ITAUT_RULE_idt' = REWRITE_RULE [ITAUTS_EQ_I_idt,
  GSYM FITAUTS_EQ_I] NON_ITAUT_RULE_idt ;

(* the following result makes NON_FITAUT_RULE redundant, since
  it is the same result without the first assumption *)
val NON_FITAUT_RULE_ALT = Q.store_thm ("NON_FITAUT_RULE_ALT",
  `maxnon (fItauts idt_tab_rule) (s : 'a sf set) ==>
    is_tab_rule (top, bot) SUBSET idt_tab_rule ==> top IN s ==>
    ?br. br IN bot /\ br SUBSET s`,
  MATCH_ACCEPT_TAC NON_ITAUT_RULE_idt') ;

val Itaut_valid = Q.store_thm ("Itaut_valid",
  `Kripke_model R pv ==> Itautss idt_tab_rule s ==> tab_val R pv w s`,
  REWRITE_TAC [Itautss_def] THEN REPEAT STRIP_TAC THEN 
  IMP_RES_TAC idt_rtc_pres_frg THEN POP_ASSUM irule THEN
  irule idt_dt_sound THEN FIRST_ASSUM ACCEPT_TAC) ;
  
val biufs = Q.ISPEC `formula_size (\x. 0)` BIGUNION_IMAGE_UNIV ;

(* intuitionistic canonical model is:
set of worlds is ``maxnon (Itauts idt_tab_rule) : 'a sf set set`` where
relation is ``\gamma delta. gamma SUBSET (FST UNION delta)`` 
atom valuation is ``\w a. w (F, a)`` 
*)
val FORMULAE_COUNTABLE = store_thm ("FORMULAE_COUNTABLE", 
  ``countable (UNIV : 'a set) ==> countable (UNIV : 'a formula set)``,
  DISCH_THEN (ASSUME_TAC o MATCH_MP formula_countable) THEN
  REWRITE_TAC [GSYM biufs] THEN irule bigunion_countable THEN
  Ho_Rewrite.ASM_REWRITE_TAC [countable_image_nats, IN_IMAGE, BETA_THM] THEN
  REPEAT STRIP_TAC THEN BasicProvers.VAR_EQ_TAC THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC) ;

val SF_COUNTABLE = store_thm ("SF_COUNTABLE", 
  ``countable (UNIV : 'a set) ==> countable (UNIV : 'a sf set)``,
  REWRITE_TAC [CROSS_UNIV] THEN DISCH_TAC THEN
  irule cross_countable THEN
  REWRITE_TAC [UNIV_BOOL, countable_INSERT, countable_EMPTY] THEN
  irule FORMULAE_COUNTABLE THEN FIRST_ASSUM ACCEPT_TAC) ;

val ITAUTI_CTNS1_FINITE = Q.store_thm ("ITAUTI_CTNS1_FINITE",
  `Itauti idt_tab_rule = ctns1 (FINITE INTER Itauti idt_tab_rule)`,
  REWRITE_TAC [FUN_EQ_THM, ctns1_def] THEN
  REPEAT (EQ_TAC ORELSE STRIP_TAC) 
  THENL [
    IMP_RES_TAC ITAUTI_IDT_FINITE THEN
      Q.EXISTS_TAC `t` THEN ASM_REWRITE_TAC [IN_APP, IN_INTER],
    RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [IN_APP, IN_INTER]) THEN
      IMP_RES_TAC Itauti_idt_mono]) ;

val LINDENBAUM_I = Q.store_thm ("LINDENBAUM_I",
  `countable (UNIV : 'a sf set) ==> ~ (Itauti idt_tab_rule s) ==>
    ?M : 'a sf set. s SUBSET M /\ maxnon (Itauti idt_tab_rule) M`,
  ONCE_REWRITE_TAC [ITAUTI_CTNS1_FINITE] THEN
  REPEAT DISCH_TAC THEN irule MAXNON_CTNS1 THEN
  ASM_REWRITE_TAC [INTER_SUBSET] THEN irule FORMULAE_COUNTABLE) ;

val IDT_ITAUTS_EQ_I = MATCH_MP ITAUTS_EQ_I IDT_FINITE_BRANCHING ;

val LINDENBAUM_S = Q.store_thm ("LINDENBAUM_S",
  `countable (UNIV : 'a sf set) ==> ~ (Itauts idt_tab_rule s) ==>
    ?M : 'a sf set. s SUBSET M /\ maxnon (Itauts idt_tab_rule) M`,
  REWRITE_TAC [IDT_ITAUTS_EQ_I, LINDENBAUM_I]) ;

val LINDENBAUM = store_thm ("LINDENBAUM",
  ``~ (Itauts idt_tab_rule s) ==> 
    ?M : num sf set. s SUBSET M /\ maxnon (Itauts idt_tab_rule) M``,
    MATCH_MP_TAC LINDENBAUM_S THEN 
    MATCH_MP_TAC SF_COUNTABLE THEN ACCEPT_TAC num_countable) ;
  
val EMPTY_NON_TAUT = Q.store_thm ("EMPTY_NON_TAUT",
  `~ (Itauti idt_tab_rule EMPTY)`,
  ONCE_REWRITE_TAC [Itauti_cases] THEN
  Ho_Rewrite.REWRITE_TAC [br_closed_def, NOT_IN_EMPTY, IDT_RULE_NON_EMPTY]) ;

val EMPTY_NON_TAUT_S = REWRITE_RULE [GSYM IDT_ITAUTS_EQ_I] EMPTY_NON_TAUT ;

val EX_NON_TAUT = save_thm ("EX_NON_TAUT", REWRITE_RULE [EMPTY_SUBSET]
  (MATCH_MP LINDENBAUM (INST_TYPE [``:'a`` |-> ``:num``] EMPTY_NON_TAUT_S))) ;

(*
show_types := true ;
show_types := false ;
*)

val worlds_TY_DEF = new_type_definition ("worlds", EX_NON_TAUT) ;

val worlds_abs_rep = define_new_type_bijections
  {ABS = "w_abs", REP = "w_rep", tyax = worlds_TY_DEF, 
  name = "worlds_abs_rep"} ;

val at_val_def = Define `at_val w a = (F, Atom a) IN w_rep w` ;
val idt_R_def = Define 
  `idt_R gamma delta = w_rep gamma SUBSET (FST UNION w_rep delta)` ;

val idt_R_alt = Q.store_thm ("idt_R_alt", `idt_R gamma delta =
  (FST (mk_seq (w_rep gamma))) SUBSET (FST (mk_seq (w_rep delta)))`,
  REWRITE_TAC [idt_R_def, mk_seq_def, get_fs_def,
    SUBSET_DEF, IN_IMAGE, lemF, IN_UNION] THEN
  EQ_TAC THEN REPEAT STRIP_TAC 
  THENL [RES_TAC, Cases_on `x` THEN Cases_on `q`] THEN
  FULL_SIMP_TAC std_ss [IN_APP]) ;
    
val rule_cases = [and_left_cases, or_right_cases, or_left_cases,
  and_right_cases, imp_left_cases, not_left_cases,
  imp_right_cases, not_right_cases] ;

val idt_Itauts = MATCH_MP ITAUT_EX_RULE IDT_FINITE_BRANCHING ;
val idt_non_Itaut = MATCH_MP NON_ITAUT_RULE IDT_FINITE_BRANCHING ;

val triv_Itaut = Q.prove (
  `(T, f) IN gamma ==> (F, f) IN gamma ==> Itauts any gamma`, 
  REWRITE_TAC [Itauts_def, Itautss_def, dt_closed_def, br_closed_def] THEN 
  REPEAT STRIP_TAC THEN
  Q.EXISTS_TAC `{gamma}` THEN
  Ho_Rewrite.REWRITE_TAC [IN_SING, ALL_EQ_LEM, RTC_REFL] THEN 
  Q.EXISTS_TAC `f` THEN ASM_REWRITE_TAC []) ;

val triv_Itaut' = DISCH_ALL (REWRITE_RULE [IN_APP] (UNDISCH triv_Itaut)) ;

val gir_lem = Q.prove (`gen_idt_rule (top, bot) ==> top IN gamma ==>
  (gamma, IMAGE ($UNION gamma) bot) IN idt_tab_rule`,
  REWRITE_TAC [IN_APP, idt_tab_rule_cases, is_tab_rule_cases] THEN
  REPEAT STRIP_TAC THEN DISJ1_TAC THEN Q.EXISTS_TAC `(top,bot)` THEN
  ASM_REWRITE_TAC [PAIR_EQ] THEN Q.EXISTS_TAC `top` THEN
  Q.EXISTS_TAC `bot` THEN Q.EXISTS_TAC `gamma` THEN
  ASM_SIMP_TAC std_ss [REWRITE_RULE [IN_APP] ABSORPTION_RWT]) ; 

val gir_lem2 = Q.prove (
  `gen_idt_rule gr ==> is_tab_rule gr SUBSET idt_tab_rule`,
  REWRITE_TAC [SUBSET_DEF, IN_APP] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC (CONJUNCT1 idt_tab_rule_rules)) ;

val grs1 = map SPEC_ALL (CONJUNCTS 
  (Ho_Rewrite.REWRITE_RULE (PULL_EXISTS :: rule_cases) gen_idt_rule_rules)) ;
val grs2 = map (Q.GEN `gr`) grs1 ;
val grs3 = map (Ho_Rewrite.REWRITE_RULE [ALL_EQ_LEM]) grs2 ;
val grs_idt_rules = map (MATCH_MP gir_lem) grs3 ; 
val gitrs_idt_rules = map (MATCH_MP gir_lem2) grs3 ;

(* now similarly for ant_idt_rule_rules *)

val air_lem = Q.prove (`ant_idt_rule (top, bot) ==> top IN gamma ==>
  (gamma, IMAGE ($UNION (gamma INTER $~ o FST)) bot) IN idt_tab_rule`,
  REWRITE_TAC [IN_APP, idt_tab_rule_cases, is_ag_tab_rule_cases] THEN
  REPEAT STRIP_TAC THEN DISJ2_TAC THEN Q.EXISTS_TAC `(top,bot)` THEN
  ASM_REWRITE_TAC [PAIR_EQ] THEN Q.EXISTS_TAC `top` THEN
  Q.EXISTS_TAC `bot` THEN Q.EXISTS_TAC `gamma` THEN
  ASM_SIMP_TAC std_ss [REWRITE_RULE [IN_APP] ABSORPTION_RWT]) ; 

val air_lem2 = Q.prove (
  `ant_idt_rule gr ==> is_ag_tab_rule gr SUBSET idt_tab_rule`,
  REWRITE_TAC [SUBSET_DEF, IN_APP] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC (CONJUNCT2 idt_tab_rule_rules)) ;

val ars1 = map SPEC_ALL (CONJUNCTS 
  (Ho_Rewrite.REWRITE_RULE (PULL_EXISTS :: rule_cases) ant_idt_rule_rules)) ;
val ars2 = map (Q.GEN `gr`) ars1 ;
val ars3 = map (Ho_Rewrite.REWRITE_RULE [ALL_EQ_LEM]) ars2 ;
val ars_idt_rules = map (MATCH_MP air_lem) ars3 ;
val aitrs_idt_rules = map (MATCH_MP air_lem2) ars3 ;

val w_rep_sat = REWRITE_RULE [CONJUNCT1 worlds_abs_rep]
  (Q.SPEC `w_rep a` (CONJUNCT2 worlds_abs_rep)) ;

val w_rep_sat' = REWRITE_RULE [maxnon_def] w_rep_sat ;
val w_rep_sat1 = CONJUNCT1 w_rep_sat' ;
val w_rep_sat2 = CONJUNCT2 w_rep_sat' ;

(* Intuitionistic Truth Lemma *)
val idt_non_Itautw = MATCH_MP idt_non_Itaut w_rep_sat ;
val idt_non_Itautw_grs = map (GEN_ALL o MATCH_MP idt_non_Itautw o
    INST_TYPE [``:'a`` |-> ``:num``]) gitrs_idt_rules ;

val R_pres_F = Q.store_thm ("R_pres_F",  
  `idt_R gamma v ==> (F, f) IN w_rep gamma ==> (F, f) IN w_rep v`,
  REWRITE_TAC [idt_R_def, SUBSET_DEF, IN_UNION] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [flem]) THEN
  FIRST_ASSUM CONTR_TAC) ;

val th1 = REWRITE_RULE
  [Once idt_Itauts, DE_MORGAN_THM, NOT_EXISTS_THM] w_rep_sat1 ;
val th2 = Ho_Rewrite.REWRITE_RULE [NOT_EXISTS_THM,
  DE_MORGAN_THM, NOT_FORALL_THM, GSYM IMP_DISJ_THM, NOT_IMP] th1 ;
val PRES_NON_TAUT = save_thm ("PRES_NON_TAUT", CONJUNCT2 th2) ;

(* for (T,Imp X X') , (T,Not X) *)
val tatac = 
  EVERY (map IMP_RES_TAC ars_idt_rules) THEN
  IMP_RES_TAC PRES_NON_TAUT THEN
  RULE_ASSUM_TAC (REWRITE_RULE [IMAGE_INSERT, IMAGE_EMPTY,
    IN_INSERT, NOT_IN_EMPTY]) THEN
  BasicProvers.VAR_EQ_TAC THEN
  (* now have result Sf, FX, TY not Itaut *)
  IMP_RES_TAC LINDENBAUM THEN
  REPEAT (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `w_abs M`)) THEN
  RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [slem, idt_R_def,
    worlds_abs_rep, UNION_SUBSET, INSERT_SUBSET, EMPTY_SUBSET]) THEN
  REV_FULL_SIMP_TAC std_ss [] THEN
  FULL_SIMP_TAC std_ss [] ;

fun gtac th gir goal = CHOOSE_TAC (MATCH_MP gir th) goal ;

(* for (_,And X X'), (_, Or X X') *)
val tctac = 
  FIRST_X_ASSUM (fn th => FIRST (map (gtac th) idt_non_Itautw_grs)) THEN
  RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [IN_INSERT, NOT_IN_EMPTY]) THEN
  REPEAT (FIRST_X_ASSUM DISJ_CASES_TAC) THEN 
  BasicProvers.VAR_EQ_TAC THEN
  RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [INSERT_SUBSET, EMPTY_SUBSET]) THEN
  RES_TAC THEN ASM_REWRITE_TAC [] ;

val TRUTH_LEMMA = Q.store_thm ("TRUTH_LEMMA",
  `!X gamma. ((T, X) IN w_rep gamma ==> ~ (forces idt_R at_val gamma X)) /\
    ((F, X) IN w_rep gamma ==> forces idt_R at_val gamma X)`,
  REVERSE Induct THEN
  REWRITE_TAC [forces_def, at_val_def] THEN
  REPEAT STRIP_TAC THEN1 (* case Atom *)
  (IMP_RES_TAC triv_Itaut THEN 
    FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `idt_tab_rule`) THEN
    FULL_SIMP_TAC std_ss [w_rep_sat']) 
  THENL [ tatac, rpt_irt ASSUME_TAC R_pres_F THEN tctac,
    tatac, rpt_irt ASSUME_TAC R_pres_F THEN tctac,
    tctac, tctac, tctac, tctac, tctac, tctac]) ;

val TRUTH_LEMMA_T = MODIFY_CONS CONJUNCT1 TRUTH_LEMMA ;

val idt_complete = Q.store_thm ("idt_complete", 
  `(!w. forces idt_R at_val w f) ==> Itauts idt_tab_rule {(T,f)}`,
  REPEAT STRIP_TAC THEN CCONTR_TAC THEN
  IMP_RES_TAC LINDENBAUM THEN
  FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP 
    (REWRITE_RULE [] (CONTRAPOS TRUTH_LEMMA_T)) o Q.SPEC `w_abs M`) THEN
  RULE_ASSUM_TAC (REWRITE_RULE 
    [worlds_abs_rep, INSERT_SUBSET, EMPTY_SUBSET]) THEN
  REV_FULL_SIMP_TAC std_ss []) ;

val idt_complete' = REWRITE_RULE [Itauts_def, Itautss_def] idt_complete ;

(* contrapositive form *)
val idt_complete_cp = Q.store_thm ("idt_complete_cp",
  `~ Itauts idt_tab_rule {(T,f)} ==> ?w. ~ forces idt_R at_val w f`,
  DISCH_TAC THEN IMP_RES_TAC (CONTRAPOS idt_complete) THEN
  Ho_Rewrite.ASM_REWRITE_TAC [GSYM NOT_FORALL_THM]) ;

val Kripke_worlds = Q.store_thm ("Kripke_worlds",
  `Kripke_model idt_R at_val`,
  REWRITE_TAC [Kripke_model_def, transitive_def, reflexive_def,
    persistent_def, idt_R_def, at_val_def, SUBSET_DEF, IN_UNION, flem] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN FULL_SIMP_TAC std_ss [flem]) ;

(* soundness is
  if f provable ie ?bot. 
  CURRY (extend_fringe idt_tab_rule))^* {{(T,f)}} bot /\ dt_closed bot
  then f valid ie !(set of worlds) R pv w. Kripke_model R pv ==> forces R pv w f
  in idt_sound the quantification over possible sets of worlds, R, pv and w
  are implicit; the quantification over possible sets of worlds has to be
  implicit, because we made a type of the set of worlds
  (this also means we have proved the result only for non-empty sets of
  worlds);
  for completeness, we want 
  if f valid ie !(set of worlds) R pv w. Kripke_model R pv ==> forces R pv w f
  then f provable, ie ?bot. 
    CURRY (extend_fringe idt_tab_rule))^* {{(T,f)}} bot /\ dt_closed bot
    (which is exactly Itauts idt_tab_rule {(T,f)})
  so our proof of this is partly informal - if we assume
  !(set of worlds) R pv w. Kripke_model R pv ==> forces R pv w f
  then we can choose our set of worlds, R and pv to get
  !w. Kripke_model R pv ==> forces idt_R at_val w f
  then we just apply the result we have called idt_complete
  But it was only in detailing this informal argument that I realised
  I needed to prove that our worlds using idt_R and at_val is in fact
  a Kripke model (result Kripke_worlds)
  *)
(*
show_assums := true ;
show_assums := false ;
show_types := true ;
show_types := false ;
*)

val _ = export_theory () ;


