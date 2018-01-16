
(* general lemmas for idt work, possibly to include in HOL *)

open HolKernel boolLib bossLib ;

open pred_setTheory pairTheory relationTheory set_relationTheory
  arithmeticTheory idtLib ;

val _ = new_theory "idt_gen" ;

val EX_EQ_LEM' = Q.store_thm ("EX_EQ_LEM'",
  `(?x. (y = x) /\ f x) = f y`, SIMP_TAC std_ss []) ;

val ALL_EQ_LEM' = Q.store_thm ("ALL_EQ_LEM'",
  `(!x. (y = x) ==> f x) = f y`, SIMP_TAC std_ss []) ;

val EX_EQ_LEM = Q.store_thm ("EX_EQ_LEM",
  `(?x. (x = y) /\ f x) = f y`, SIMP_TAC std_ss []) ;

val ALL_EQ_LEM = Q.store_thm ("ALL_EQ_LEM",
  `(!x. (x = y) ==> f x) = f y`, SIMP_TAC std_ss []) ;

val EX_NOT_EMPTY = Q.store_thm ("EX_NOT_EMPTY",
  `$? s = ~ (s = EMPTY)`,
  Ho_Rewrite.REWRITE_TAC [EMPTY_DEF, EXTENSION, IN_DEF, BETA_THM,
    NOT_FORALL_THM] THEN
  Ho_Rewrite.REWRITE_TAC [ETA_THM]) ;

val ALL_IS_UNIV = Q.store_thm ("ALL_IS_UNIV",
  `$! s = (s = UNIV)`,
  Ho_Rewrite.REWRITE_TAC [UNIV_DEF, FORALL_DEF, BETA_THM]) ;
  
val ALL_EX_UNIV_EMPTY = Q.store_thm ("ALL_EX_UNIV_EMPTY",
  `($? EMPTY = F) /\ ($? UNIV = T) /\ ($! EMPTY = F) /\ ($! UNIV = T)`,
  Ho_Rewrite.REWRITE_TAC [FORALL_DEF, EMPTY_DEF, UNIV_DEF, BETA_THM ] THEN
  Ho_Rewrite.REWRITE_TAC [EXTENSION, IN_DEF, BETA_THM]) ;

val IN_UNCURRY = Q.store_thm ("IN_UNCURRY",
  `(x,y) ∈ UNCURRY s = s x y`,
  REWRITE_TAC [IN_APP, UNCURRY_DEF]) ;

val IN_UNCURRY_VAR = Q.store_thm ("IN_UNCURRY_VAR",
  `p ∈ UNCURRY s = s (FST p) (SND p)`,
  REWRITE_TAC [IN_APP, UNCURRY_VAR]) ;

val IN_GSPEC_PAIR = Q.store_thm ("IN_GSPEC_PAIR",
  `p IN {(x,y) | P x y} = P (FST p) (SND p)`,
  REWRITE_TAC [GSPEC_PAIR_ETA, IN_UNCURRY_VAR]) ;

val BIGUNION_IMAGE_UNIV = Q.store_thm ("BIGUNION_IMAGE_UNIV",
  `!g. BIGUNION (IMAGE (\n. {f | g f ≤ n}) UNIV) = UNIV`,
  REWRITE_TAC [IN_BIGUNION, EXTENSION, IN_UNIV] THEN
  Ho_Rewrite.REWRITE_TAC [IN_IMAGE, BETA_THM, IN_UNIV] THEN 
  REPEAT GEN_TAC THEN Q.EXISTS_TAC `{f | g f <= g x}` THEN CONJ_TAC
  THENL [
    Ho_Rewrite.REWRITE_TAC [IN_GSPEC_IFF, arithmeticTheory.LESS_EQ_REFL],
    Q.EXISTS_TAC `g x` THEN REFL_TAC]) ;

val IMAGE_IS_SUBSET = Q.store_thm ("IMAGE_IS_SUBSET",
  `IMAGE f xs SUBSET ys = xs SUBSET ys o f`,
  REWRITE_TAC [SUBSET_DEF, IN_IMAGE, IN_APP, o_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) 
  THENL [ FIRST_X_ASSUM irule THEN Q.EXISTS_TAC `x`, RES_TAC] THEN 
  ASM_REWRITE_TAC []) ;

val INSERT_DELETE_SAME = Q.store_thm ("INSERT_DELETE_SAME",
  `(f INSERT s DELETE f = f INSERT s) /\
    ((f INSERT s) DELETE f = s DELETE f)`,
  REWRITE_TAC [EXTENSION, IN_INSERT, IN_DELETE] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
  ASM_REWRITE_TAC [] THEN DECIDE_TAC) ; 

val NOT_EQ_NOT = 
  Q.store_thm ("NOT_EQ_NOT", `(~ x = ~ y) = (x = y)`, DECIDE_TAC) ;
val NOT_EQ = 
  Q.store_thm ("NOT_EQ", `~ (x = y) = (x = ~ y)`, DECIDE_TAC) ;

val UNION_MONO = Q.store_thm ("UNION_MONO",
  `A SUBSET A' /\ B SUBSET B' ==> A UNION B SUBSET A' UNION B'`,
  REWRITE_TAC [SUBSET_DEF, IN_UNION] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC []) ;
 
val INTER_MONO = Q.store_thm ("INTER_MONO",
  `A SUBSET A' /\ B SUBSET B' ==> A INTER B SUBSET A' INTER B'`,
  REWRITE_TAC [SUBSET_DEF, IN_INTER] THEN
  REPEAT STRIP_TAC THEN RES_TAC) ;

val DIFF_SUBSET_IFF_SUBSET_UNION = Q.store_thm ("DIFF_SUBSET_IFF_SUBSET_UNION",
  `A DIFF B SUBSET C = A SUBSET B UNION C`,
  REWRITE_TAC [SUBSET_DEF, IN_UNION, IN_DIFF] THEN
  HO_MATCH_MP_TAC ConseqConvTheory.forall_eq_thm THEN
  GEN_TAC THEN DECIDE_TAC) ;

val DISJ_NOT_IMP1 = Q.store_thm ("DISJ_NOT_IMP1", `(A \/ B) = ~ A ==> B`,
  REWRITE_TAC [IMP_DISJ_THM]) ;
val DISJ_NOT_IMP2 = Q.store_thm ("DISJ_NOT_IMP2", `(A \/ B) = ~ B ==> A`,
  REWRITE_TAC [IMP_DISJ_THM] THEN MATCH_ACCEPT_TAC DISJ_COMM) ;

val _ = export_theory () ;

