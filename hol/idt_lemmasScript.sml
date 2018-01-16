
(* lemmas useful for completeness,
  but not depending particularly on the actual rules *)

open HolKernel boolLib bossLib ;

open pred_setTheory pairTheory relationTheory set_relationTheory
  arithmeticTheory ;
open idtLib idt_genTheory ;
(*
open idt_soundTheory ;
*)

(* 
load "set_relationTheory" ;
use "idt_lemmasScript.sml" ;

load "idt_lemmasTheory" ;
open idt_lemmasTheory ;
*)

val _ = new_theory "idt_lemmas" ;

val _ = Parse.type_abbrev ("rule", ``: ('a # 'a set)``) ;
(* and-or rule *)
val _ = Parse.type_abbrev ("rule_sk", ``: ('a # 'a set set)``) ;

val im_lem = Q.prove (
  `IMAGE SND rs SUBSET FINITE <=> !t b. (t, b) IN rs ==> FINITE b`,
REWRITE_TAC [SUBSET_DEF, IN_IMAGE, IN_APP] THEN
EQ_TAC THEN REPEAT STRIP_TAC
THENL [ FIRST_X_ASSUM irule THEN Q.EXISTS_TAC `(t,b)`,
Cases_on `x'` THEN RES_TAC] THEN
ASM_REWRITE_TAC [SND]) ;

(* repeated application of a rule (as above),
  requires applying a rule to a tableau fringe,
  rf is the remainder of a tableau fringe *)
val (extend_fringe_rules, extend_fringe_ind, extend_fringe_cases) = 
  Hol_reln `rules (s, fr) ==> extend_fringe rules (s INSERT rf, fr UNION rf)` ;

``extend_fringe : 'a rule set -> ('a set # 'a set) set`` ;

val ctns1_def = Define `ctns1 cs p = ?c. c IN cs /\ c SUBSET p` ;
(* accumulate items using f so as not to contain any c *)
val accfnc_def = Define `(accfnc cs f init 0 = init) /\
  (accfnc cs f init (SUC n) = 
  let gn = accfnc cs f init n in
  if ctns1 cs (f n INSERT gn) then gn else f n INSERT gn)` ;

(* set of which all supersets satisfy a predicate *)
val supsat_def = Define `supsat f s = !t. s PSUBSET t ==> f t` ;
(* maximal set not satisfying a predicate *)
val maxnon_def = Define `maxnon f s = ~ f s /\ !t. s PSUBSET t ==> f t` ;

(* lemmas about accfnc *)
val CTNS1_ACC = Q.store_thm ("CTNS1_ACC",
  `!n. ctns1 cs (accfnc cs f init n) ==> ctns1 cs init`,
  Induct THEN Ho_Rewrite.REWRITE_TAC [accfnc_def, LET_THM, BETA_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC []) ;

val CTNS1_ACC' = Ho_Rewrite.REWRITE_RULE [GSYM PULL_EXISTS] CTNS1_ACC ;

val CTNS1_MONO = Q.store_thm ("CTNS1_MONO",
  `ctns1 cs s ==> s SUBSET t ==> ctns1 cs t`,
  REWRITE_TAC [ctns1_def] THEN
  REPEAT STRIP_TAC THEN Q.EXISTS_TAC `c` THEN
  ASM_REWRITE_TAC [] THEN rpt_irt ACCEPT_TAC SUBSET_TRANS') ;

val ACCFNC_MONO = Q.store_thm ("ACCFNC_MONO",
  `!n. m <= n ==> accfnc cs f init m SUBSET accfnc cs f init n`,
  Induct THEN REWRITE_TAC [LESS_EQ_0, LE] THEN
  REPEAT STRIP_TAC THEN TRY BasicProvers.VAR_EQ_TAC THEN
  TRY (MATCH_ACCEPT_TAC SUBSET_REFL) THEN RES_TAC THEN
  FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP SUBSET_TRANS') THEN
  Ho_Rewrite.REWRITE_TAC [accfnc_def, LET_THM, BETA_THM] THEN
  COND_CASES_TAC THEN REWRITE_TAC [SUBSET_REFL, SUBSET_OF_INSERT]) ;

val aths = REORDER_ANTS rev (REWRITE_RULE [SUBSET_DEF] ACCFNC_MONO) ;

val FIN_U_ACCFNC = Q.store_thm ("FIN_U_ACCFNC",
  `!c. c IN FINITE ==> c SUBSET BIGUNION (IMAGE (accfnc cs f init) UNIV) ==>
    ?n. c SUBSET accfnc cs f init n`,
  REWRITE_TAC [IN_APP] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC [EMPTY_SUBSET, INSERT_SUBSET, IN_BIGUNION, IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN
  Q.EXISTS_TAC `MAX x n` THEN BasicProvers.VAR_EQ_TAC THEN CONJ_TAC 
  THENL [ FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP aths),
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP SUBSET_TRANS') THEN
      irule ACCFNC_MONO] THEN
  REWRITE_TAC [MAX_LE, LESS_EQ_REFL]) ;

val CTNS1_U_ACCFNC = Q.store_thm ("CTNS1_U_ACCFNC",
  `cs SUBSET FINITE ==> ctns1 cs (BIGUNION (IMAGE (accfnc cs f init) UNIV)) ==>
    ?n. ctns1 cs (accfnc cs f init n)`,
  REWRITE_TAC [SUBSET_DEF] THEN REWRITE_TAC [ctns1_def] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN
  rpt_irt ASSUME_TAC FIN_U_ACCFNC THEN POP_ASSUM CHOOSE_TAC THEN
  Q.EXISTS_TAC `n` THEN Q.EXISTS_TAC `c` THEN ASM_REWRITE_TAC []) ;

val MAXNON_CTNS1 = Q.store_thm ("MAXNON_CTNS1",
  `countable (UNIV : 'a set) ==> (cs : 'a set set) SUBSET FINITE ==>
    ~ (ctns1 cs m) ==> ?s : 'a set. (m : 'a set) SUBSET s /\
      maxnon (ctns1 cs) s`,
  REWRITE_TAC [countable_surj, UNIV_NOT_EMPTY] THEN
  REPEAT STRIP_TAC THEN
  Q.EXISTS_TAC `BIGUNION (IMAGE (accfnc cs f m) UNIV)` THEN
  CONJ_TAC THEN1 (irule SUBSET_BIGUNION_I THEN
    REWRITE_TAC [IN_IMAGE, IN_UNIV] THEN
    Q.EXISTS_TAC `0` THEN ASM_REWRITE_TAC [accfnc_def]) THEN
  REWRITE_TAC [maxnon_def] THEN CONJ_TAC THEN1
    (CCONTR_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE []) THEN
    rpt_irt ASSUME_TAC CTNS1_U_ACCFNC THEN
    POP_ASSUM (ASSUME_TAC o MATCH_MP CTNS1_ACC') THEN RES_TAC) THEN
  REWRITE_TAC [PSUBSET_MEMBER] THEN
  REPEAT STRIP_TAC THEN
  RULE_L_ASSUM_TAC (CONJUNCTS o 
    REWRITE_RULE [SURJ_DEF, IN_UNIV, IN_BIGUNION]) THEN
  IMP_RES_TAC iulem THEN 
  FIRST_X_ASSUM (CHOOSE_TAC o Q.SPEC `y`) THEN
  FIRST_X_ASSUM (MP_TAC o Ho_Rewrite.REWRITE_RULE
    [accfnc_def, LET_THM, BETA_THM] o Q.SPEC `SUC y'`) THEN
  ASM_REWRITE_TAC [] THEN 
  REVERSE COND_CASES_TAC THEN1 ASM_REWRITE_TAC [IN_INSERT] THEN
  DISCH_TAC THEN IMP_RES_THEN MATCH_MP_TAC CTNS1_MONO THEN
  ASM_REWRITE_TAC [INSERT_SUBSET] THEN
  FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP SUBSET_TRANS'') THEN
  irule SUBSET_BIGUNION_I THEN irule IMAGE_IN THEN irule IN_UNIV) ;

(* version of the above via Zorn's Lemma *)

(* instantiate Zorn's Lemma *)
val zli = Q.ISPECL
  [`rrestrict (UNCURRY $SUBSET) ($SUBSET m INTER $~ o ctns1 cs)`,
  `$SUBSET m INTER $~ o ctns1 cs`] zorns_lemma ;
val rev_zli = REORDER_ANTS rev (REWRITE_RULE [GSYM AND_IMP_INTRO] zli) ;

val PO_SUBSET = Q.store_thm ("PO_SUBSET",
  `partial_order (UNCURRY $SUBSET) UNIV`,
  REWRITE_TAC [partial_order_def, SUBSET_DEF, in_domain, in_range, EXTENSION,
    transitive_def, reflexive_def, antisym_def, IN_UNCURRY, IN_UNIV] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN REPEAT RES_TAC) ;

val PO_RR_SUBSET = Q.store_thm ("PO_RR_SUBSET",
  `partial_order (rrestrict (UNCURRY $SUBSET) s) s`,
  irule partial_order_subset THEN Q.EXISTS_TAC `UNIV` THEN
  REWRITE_TAC [SUBSET_UNIV, PO_SUBSET]) ;

val chain_mono_r = Q.store_thm ("chain_mono_r",
  `chain s r ==> r SUBSET r' ==> chain s r'`,
  REWRITE_TAC [chain_def, SUBSET_DEF] THEN
  REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
  FIRST_X_ASSUM (fn th => FIRST_X_ASSUM (MP_TAC o MATCH_MP th)) THEN
  MATCH_MP_TAC MONO_OR THEN ASM_REWRITE_TAC []) ;

val chain_ctns_finite = Q.store_thm ("chain_ctns_finite",
  `chain s (UNCURRY $SUBSET) ==> ~ (s = EMPTY) ==> 
    !c. FINITE c ==> c SUBSET BIGUNION s ==> ?t. t IN s /\ c SUBSET t`,
  REWRITE_TAC [GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_TAC THEN DISCH_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC [EMPTY_SUBSET, INSERT_SUBSET] THEN
  REPEAT STRIP_TAC THEN1 FIRST_ASSUM ACCEPT_TAC THEN RES_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [IN_BIGUNION]) THEN
  FIRST_X_ASSUM CHOOSE_TAC THEN
  RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [chain_def, IN_UNCURRY]) THEN
  FIRST_X_ASSUM (ASSUME_TAC o Q.SPECL [`s'`, `t`]) THEN
  RES_TAC THENL map Q.EXISTS_TAC [`t`, `t`, `s'`, `s'`] THEN
  ASM_REWRITE_TAC [] THENL 
  map IMP_RES_TAC [subsetD, subsetD, SUBSET_TRANS', SUBSET_TRANS']) ;

val finite_forbidden_chain_ub = Q.store_thm ("finite_forbidden_chain_ub", 
  `cs SUBSET FINITE ==> ~ (ctns1 cs m) ==> 
    let r = rrestrict (UNCURRY $SUBSET) ($SUBSET m INTER $~ o ctns1 cs) in
    !t. chain t r ==> chain (m INSERT t) r /\ 
      BIGUNION (m INSERT t) IN upper_bounds t r`,
  Ho_Rewrite.REWRITE_TAC [LET_THM, BETA_THM] THEN
  REPEAT STRIP_TAC THEN_LT
  USE_SG_THEN ASSUME_TAC 1 2 
  THENL [
  REWRITE_TAC [chain_def, IN_INSERT] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [chain_def]) THEN
    REPEAT STRIP_TAC THEN
    REPEAT BasicProvers.VAR_EQ_TAC THENL
    [DISJ1_TAC, DISJ1_TAC THEN cctac, DISJ2_TAC THEN cctac, 
    FIRST_X_ASSUM irule THEN FIRST_ASSUM ACCEPT_TAC] THEN
    ASM_REWRITE_TAC [in_rrestrict, UNCURRY_DEF, INTER_applied,
      SUBSET_REFL, IN_APP, o_THM] THEN DECIDE_TAC,
  Ho_Rewrite.REWRITE_TAC [upper_bounds_def, IN_GSPEC_IFF, in_range] THEN
    CONJ_TAC THENL [Q.EXISTS_TAC `m`, REPEAT STRIP_TAC] THEN
    REWRITE_TAC [in_rrestrict, UNCURRY_DEF, INTER_applied,
	SUBSET_REFL, IN_APP, o_THM] THEN
    REPEAT CONJ_TAC THEN
    TRY (irule SUBSET_BIGUNION_I THEN ASM_REWRITE_TAC [IN_INSERT]) THEN
    TRY (rpt_irt_n 2 MP_TAC rrchain_lem THEN REWRITE_TAC
	[INTER_applied, IN_APP, o_THM] THEN DECIDE_TAC) THEN
    TRY (FIRST_ASSUM ACCEPT_TAC) THEN_LT
    USE_SG_THEN ACCEPT_TAC 1 2 THEN
    Ho_Rewrite.REWRITE_TAC [ctns1_def, NOT_EXISTS_THM] THEN GEN_TAC THEN
    DISCH_THEN (fn th =>
      MAP_EVERY ASSUME_TAC (CONJUNCTS th @ CONJUNCTS th)) THEN
    rpt_irt_n 2 (ASSUME_TAC o REWRITE_RULE [IN_APP]) subsetD THEN
    VALIDATE (rpt_irt (ASSUME_TAC o UNDISCH o REWRITE_RULE [NOT_INSERT_EMPTY])
      (REORDER_ANTS rev chain_ctns_finite)) THEN1
    (rpt_irt MATCH_MP_TAC chain_mono_r THEN irule rrestrict_SUBSET) THEN
    FIRST_X_ASSUM CHOOSE_TAC THEN RULE_L_ASSUM_TAC CONJUNCTS THEN
    rpt_irt ASSUME_TAC rrchain_lem THEN
    RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [IN_APP, IN_INTER,
      o_THM, ctns1_def]) THEN RES_TAC]) ;

val finite_forbidden_chain_ub' = 
  Ho_Rewrite.REWRITE_RULE [LET_THM, BETA_THM] finite_forbidden_chain_ub ;

val ex_max_zorn = Q.store_thm ("ex_max_zorn",
  `cs SUBSET FINITE ==> ~ (ctns1 cs m) ==> 
    ?M. M IN maximal_elements ($~ o ctns1 cs) (UNCURRY $SUBSET) /\ m SUBSET M`,
  REPEAT DISCH_TAC THEN VALIDATE (CHOOSE_TAC (UNDISCH zli)) THEN1
    (REWRITE_TAC [PO_RR_SUBSET] THEN REPEAT CONJ_TAC 
    THENL [
    REWRITE_TAC [GSYM EX_NOT_EMPTY, Once ex_eta_lem] THEN Q.EXISTS_TAC `m` THEN
      ASM_REWRITE_TAC [INTER_applied, o_THM, IN_APP, SUBSET_REFL],
    REPEAT STRIP_TAC THEN
    rpt_irt ASSUME_TAC finite_forbidden_chain_ub' THEN
    REV_FULL_SIMP_TAC std_ss [NOT_IN_EMPTY] ]) THEN
  REPEAT DISCH_TAC THEN Q.EXISTS_TAC `x` THEN
  Ho_Rewrite.REWRITE_TAC [IN_GSPEC_IFF, maximal_elements_def] THEN
  RULE_L_ASSUM_TAC (CONJUNCTS o Ho_Rewrite.REWRITE_RULE [IN_GSPEC_IFF,
    maximal_elements_def, IN_INTER, in_rrestrict]) THEN
  ASM_REWRITE_TAC [] THEN
  REVERSE CONJ_TAC THEN1 FULL_SIMP_TAC std_ss [IN_APP] THEN
  REPEAT STRIP_TAC THEN
  VALIDATE (FIRST_X_ASSUM (ASSUME_TAC o UNDISCH o Q.SPEC `x'`)) THEN
  ASM_REWRITE_TAC [] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [IN_APP, UNCURRY_DEF]) THEN
  REWRITE_TAC [IN_APP] THEN rpt_irt ACCEPT_TAC SUBSET_TRANS'') ; 

val MAXNON_CTNS1_ZORN = Q.store_thm ("MAXNON_CTNS1_ZORN",
  `cs SUBSET FINITE ==> ~ (ctns1 cs m) ==>
    ?s : 'a set. m SUBSET s /\ maxnon (ctns1 cs) s`,
  REPEAT STRIP_TAC THEN
  rpt_irt CHOOSE_TAC ex_max_zorn THEN
  Q.EXISTS_TAC `M` THEN
  RULE_L_ASSUM_TAC (CONJUNCTS o Ho_Rewrite.REWRITE_RULE 
    [maximal_elements_def, IN_GSPEC_IFF', IN_APP, UNCURRY_DEF, o_THM]) THEN
  ASM_REWRITE_TAC [maxnon_def, PSUBSET_DEF] THEN
  REPEAT STRIP_TAC THEN CCONTR_TAC THEN RES_TAC) ;

(* 
show_types := true ;
show_types := false ;
*)

(* now need to get that Itautss idt_tab_rule s is equiv to
  s contains one of a set of finite sets of signed formulae *)

(* finiteness of tableau *) 

val FRINGE_RULE_FB = Q.store_thm ("FRINGE_RULE_FB",
  `IMAGE SND rs SUBSET FINITE ==> (top, bot) IN extend_fringe rs ==> 
    (FINITE top = FINITE bot)`,
  REWRITE_TAC [extend_fringe_cases, IN_APP, PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN
  REPEAT BasicProvers.VAR_EQ_TAC THEN 
  REWRITE_TAC [FINITE_INSERT, FINITE_UNION] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [SUBSET_DEF, IN_APP, IMAGE_DEF]) THEN
  FIRST_X_ASSUM irule THEN
  ASM_SIMP_TAC std_ss [GSPECIFICATION_applied] THEN
  Q.EXISTS_TAC `(s, fr)` THEN ASM_REWRITE_TAC [SND]) ;

val RTC_FRINGE_RULE_FB = Q.store_thm ("RTC_FRINGE_RULE_FB",
  `IMAGE SND rs SUBSET FINITE ==> !top bot.
    (CURRY (extend_fringe rs))^* top bot ==> (FINITE top = FINITE bot)`,
  DISCH_TAC THEN HO_MATCH_MP_TAC RTC_INDUCT THEN
  REWRITE_TAC [CURRY_DEF] THEN
  REPEAT STRIP_TAC THEN
  rpt_irt ASSUME_TAC (REWRITE_RULE [IN_APP] FRINGE_RULE_FB) THEN
  ASM_REWRITE_TAC []) ;

(* rules preserving finiteness *)
val FR_PRES_FINITE = Q.store_thm ("FR_PRES_FINITE",
  `(!top bot. (top, bot) IN rs ==> top IN FINITE ==> bot SUBSET FINITE) ==>
    (!ftop fbot. (ftop, fbot) IN extend_fringe rs ==>
      ftop SUBSET FINITE ==> fbot SUBSET FINITE)`,
  REWRITE_TAC [IN_APP, extend_fringe_cases, PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN
  REPEAT BasicProvers.VAR_EQ_TAC THEN
  RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [INSERT_SUBSET, IN_APP]) THEN
  RES_TAC THEN ASM_REWRITE_TAC [UNION_SUBSET]) ;

(* fringe rule lemmas *)
val EXTEND_FRINGE_RULE = Q.store_thm ("EXTEND_FRINGE_RULE",
  `(top, bot) IN extend_fringe rs ==>
    (top UNION ctxt, bot UNION ctxt) IN extend_fringe rs`,
  REWRITE_TAC [IN_APP, extend_fringe_cases, PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN Q.EXISTS_TAC `fr` THEN
  Q.EXISTS_TAC `rf UNION ctxt` THEN Q.EXISTS_TAC `s` THEN
  ASM_REWRITE_TAC [UNION_ASSOC, INSERT_UNION_EQ]) ;

val rtci = REORDER_ANTS rev 
  (REWRITE_RULE [GSYM AND_IMP_INTRO] (MODIFY_CONS CONJUNCT2 RTC_RULES)) ;

val EXTEND_RTC_FRINGE_RULE = Q.store_thm ("EXTEND_RTC_FRINGE_RULE",
  `!top. RTC (CURRY (extend_fringe rs)) top bot ==> 
    RTC (CURRY (extend_fringe rs)) (top UNION ctxt) (bot UNION ctxt)`,
  HO_MATCH_MP_TAC RTC_ALT_INDUCT THEN
  REPEAT STRIP_TAC THEN1 MATCH_ACCEPT_TAC RTC_REFL THEN
  FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP rtci) THEN
  FULL_SIMP_TAC std_ss [CURRY_DEF] THEN
  FIRST_X_ASSUM (MATCH_ACCEPT_TAC o MATCH_MP 
   (REWRITE_RULE [IN_APP] EXTEND_FRINGE_RULE))) ;

val FINITE_COMBINE_TABS_FUN = Q.store_thm ("FINITE_COMBINE_TABS_FUN",
  `!fr. FINITE fr ==> (!t. t IN fr ==>
    (CURRY (extend_fringe rs))^* {t} (f t)) ==>
     (CURRY (extend_fringe rs))^* fr (BIGUNION (IMAGE f fr))`,
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC [NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN1 
    REWRITE_TAC [IMAGE_EMPTY, BIGUNION_EMPTY, RTC_REFL] THEN
  RULE_L_ASSUM_TAC (CONJUNCTS o Ho_Rewrite.REWRITE_RULE
    [ALL_EQ_LEM, IN_INSERT, DISJ_IMP_THM, FORALL_AND_THM]) THEN
  POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC) THEN
  VALIDATE (FIRST_X_ASSUM (ASSUME_TAC o UNDISCH)) THEN
  ASM_REWRITE_TAC [IMAGE_INSERT, BIGUNION_INSERT] THEN
  ONCE_REWRITE_TAC [INSERT_SING_UNION] THEN
  irule RTC_RTC THEN Q.EXISTS_TAC `f e UNION fr` THEN CONJ_TAC THEN1 
    FIRST_X_ASSUM (MATCH_ACCEPT_TAC o MATCH_MP EXTEND_RTC_FRINGE_RULE) THEN
  ONCE_REWRITE_TAC [UNION_COMM] THEN
  FIRST_X_ASSUM (MATCH_ACCEPT_TAC o MATCH_MP EXTEND_RTC_FRINGE_RULE)) ;
    
val FINITE_COMBINE_TABS = Q.store_thm ("FINITE_COMBINE_TABS",
  `FINITE fr ==> (!t. t IN fr ==>
    ?bs. bs SUBSET bot /\ (CURRY (extend_fringe rs))^* {t} bs) ==>
	?bs. bs SUBSET bot /\ (CURRY (extend_fringe rs))^* fr bs`,
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC (Ho_Rewrite.REWRITE_RULE
    [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM, IMP_CONJ_THM, FORALL_AND_THM]) THEN
  FIRST_X_ASSUM CHOOSE_TAC THEN
  RULE_L_ASSUM_TAC CONJUNCTS THEN
  rpt_irt ASSUME_TAC FINITE_COMBINE_TABS_FUN THEN
  Q.EXISTS_TAC `BIGUNION (IMAGE f fr)` THEN
  ASM_REWRITE_TAC [BIGUNION_SUBSET, IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC []) ;

val issflem = Q.store_thm ("issflem", 
  `IMAGE SND rs SUBSET FINITE ==> (s, fr) IN rs ==> FINITE fr`,
  REWRITE_TAC [IMAGE_IS_SUBSET] THEN
  REWRITE_TAC [SUBSET_DEF, IN_APP, o_THM] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN FULL_SIMP_TAC std_ss []) ;

val issflem' = REWRITE_RULE [IN_APP] issflem ;

(* why should you need finitely branching rules for this result? *)
val SPLIT_TAB = Q.store_thm ("SPLIT_TAB",
  `IMAGE SND rs SUBSET FINITE ==> !top.(CURRY (extend_fringe rs))^* top bot ==> 
    !t. t IN top ==> ?bs. bs SUBSET bot /\ (CURRY (extend_fringe rs))^* {t} bs`,
  DISCH_TAC THEN HO_MATCH_MP_TAC RTC_ALT_INDUCT THEN
  REPEAT STRIP_TAC THEN1 
    (Q.EXISTS_TAC `{t}` THEN
    ASM_REWRITE_TAC [INSERT_SUBSET, RTC_REFL, EMPTY_SUBSET]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [CURRY_DEF, extend_fringe_cases, PAIR_EQ]) THEN
  REPEAT (FIRST_X_ASSUM CHOOSE_TAC) THEN
  RULE_L_ASSUM_TAC CONJUNCTS THEN
  REPEAT BasicProvers.VAR_EQ_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [IN_INSERT]) THEN
  REVERSE (FIRST_X_ASSUM DISJ_CASES_TAC) THEN1
   (FIRST_X_ASSUM irule THEN ASM_REWRITE_TAC [IN_UNION]) THEN
  REPEAT BasicProvers.VAR_EQ_TAC THEN
  IMP_RES_TAC extend_fringe_rules THEN
  rpt_irt ASSUME_TAC issflem' THEN
  RULE_L_ASSUM_TAC (CONJUNCTS o Ho_Rewrite.REWRITE_RULE
  [IN_UNION, DISJ_IMP_THM, FORALL_AND_THM]) THEN
  rpt_irt ASSUME_TAC FINITE_COMBINE_TABS THEN
  POP_ASSUM CHOOSE_TAC THEN Q.EXISTS_TAC `bs` THEN
  RULE_L_ASSUM_TAC CONJUNCTS THEN
  CONJ_TAC THEN1 FIRST_ASSUM ACCEPT_TAC THEN
  FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP rtci) THEN
  FIRST_X_ASSUM (ASSUME_TAC o REWRITE_RULE [UNION_EMPTY] o Q.SPEC `EMPTY`) THEN
  ASM_REWRITE_TAC [CURRY_DEF]) ;

(* this is better than SPLIT_TAB because it doesn't have the 
  requirement for finitely branching rules *)
val SUB_TAB = Q.store_thm ("SUB_TAB",
  `!top. (CURRY (extend_fringe rs))^* top bot ==> 
    !stop. stop SUBSET top ==> 
      ?bs. bs SUBSET bot /\ (CURRY (extend_fringe rs))^* stop bs`,
  HO_MATCH_MP_TAC RTC_ALT_INDUCT THEN
  REPEAT STRIP_TAC THEN1 
    (Q.EXISTS_TAC `stop` THEN ASM_REWRITE_TAC [RTC_REFL]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [CURRY_DEF, extend_fringe_cases, PAIR_EQ]) THEN
  REPEAT (FIRST_X_ASSUM CHOOSE_TAC) THEN
  RULE_L_ASSUM_TAC CONJUNCTS THEN
  REPEAT BasicProvers.VAR_EQ_TAC THEN
  Cases_on `stop SUBSET rf` THEN1 
    (FIRST_X_ASSUM irule THEN 
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP SUBSET_TRANS') THEN
    REWRITE_TAC [SUBSET_UNION]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [SUBSET_INSERT_DELETE]) THEN
  VALIDATE (FIRST_X_ASSUM
    (ASSUME_TAC o UNDISCH o Q.SPEC `fr UNION (stop DELETE s)`)) THEN1 
    (ASM_REWRITE_TAC [UNION_SUBSET, SUBSET_UNION] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP SUBSET_TRANS') THEN
    REWRITE_TAC [SUBSET_UNION]) THEN
  REPEAT (FIRST_X_ASSUM CHOOSE_TAC) THEN
  RULE_L_ASSUM_TAC CONJUNCTS THEN
  Q.EXISTS_TAC `bs` THEN ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP rtci) THEN
  REWRITE_TAC [CURRY_DEF, extend_fringe_cases, PAIR_EQ] THEN
  Q.EXISTS_TAC `fr` THEN Q.EXISTS_TAC `stop DELETE s` THEN
  Q.EXISTS_TAC `s` THEN ASM_REWRITE_TAC [] THEN
  irule (GSYM INSERT_DELETE) THEN CCONTR_TAC THEN
  FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]) ;

val FRINGE_RULE_FB = Q.store_thm ("FRINGE_RULE_FB",
  `IMAGE SND rs SUBSET FINITE ==> (top, bot) IN extend_fringe rs ==>
    (FINITE top = FINITE bot)`,
  REWRITE_TAC [extend_fringe_cases, IN_APP, PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN
  REPEAT BasicProvers.VAR_EQ_TAC THEN
  REWRITE_TAC [FINITE_INSERT, FINITE_UNION] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [SUBSET_DEF, IN_APP, IMAGE_DEF]) THEN
  FIRST_X_ASSUM irule THEN
  ASM_SIMP_TAC std_ss [GSPECIFICATION_applied] THEN
  Q.EXISTS_TAC `(s, fr)` THEN ASM_REWRITE_TAC [SND]) ;

val RTC_FRINGE_RULE_FB = Q.store_thm ("RTC_FRINGE_RULE_FB",
  `IMAGE SND rs SUBSET FINITE ==> !top bot. 
    (CURRY (extend_fringe rs))^* top bot ==> (FINITE top = FINITE bot)`,
  DISCH_TAC THEN HO_MATCH_MP_TAC RTC_INDUCT THEN
  REWRITE_TAC [CURRY_DEF] THEN
  REPEAT STRIP_TAC THEN
  rpt_irt ASSUME_TAC (REWRITE_RULE [IN_APP] FRINGE_RULE_FB) THEN
  ASM_REWRITE_TAC []) ;

  

(*
show_assums := true ;
show_assums := false ;
show_types := true ;
show_types := false ;
*)

val _ = export_theory () ;

