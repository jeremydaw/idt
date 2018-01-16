
structure idtLib = struct 

local open bossLib boolTheory Thm Rewrite Drule Tactic Tactical Conv Thm_cont
pred_setTheory pairTheory relationTheory set_relationTheory ;
in

(* much more than this needed for kananaskis-11
(* following needed when using kananaskis-11 (in src/1/Drule.sml in latest) *)

fun REORDER_ANTS_MOD f g th =
  let val (ants, uth) = strip_gen_left (UNDISCH_TM o SPEC_ALL) th ;
  in Lib.itlist DISCH (f ants) (g (SPEC_ALL uth)) end ;

fun REORDER_ANTS f th = REORDER_ANTS_MOD f (fn c => c) th ;
fun MODIFY_CONS g th = REORDER_ANTS_MOD (fn hs => hs) g th ;

(* following needed when using kananaskis-11
  (in src/pred_set/src/pred_setScript.sml in latest) *)

val IN_APP = Tactical.store_thm (
  "IN_APP",
  ``!x P. (x IN P) = P x``,
  SIMP_TAC bool_ss [IN_DEF]);

val IN_GSPEC_IFF = store_thm ("IN_GSPEC_IFF",
  ``y IN {x | P x} = P y``,
  REWRITE_TAC [GSPEC_ETA, SPECIFICATION]) ;

(* end of stuff added for kananaskis-11 *)
*)

val sflem = Q.prove (`IMAGE SND rs SUBSET FINITE ==> 
  (top, rb) IN rs ==> FINITE rb`,
  mesonLib.MESON_TAC [SUBSET_DEF, IN_IMAGE, combinTheory.o_THM, IN_APP, SND]) ;

val INSERT_EQ_SING' = 
  CONV_RULE (ONCE_DEPTH_CONV (LHS_CONV SYM_CONV)) INSERT_EQ_SING ;

val INSERT_SING_UNION' = ONCE_REWRITE_RULE [UNION_COMM] INSERT_SING_UNION ;
  
val SUBSET_TRANS' = REWRITE_RULE [GSYM AND_IMP_INTRO] SUBSET_TRANS ;
val SUBSET_TRANS'' = REORDER_ANTS rev SUBSET_TRANS' ;
val subsetD = MODIFY_CONS (#1 o EQ_IMP_RULE) SUBSET_DEF ;

val SUBSET_OF_INSERT = REWRITE_RULE [DELETE_SUBSET_INSERT] DELETE_SUBSET ;

val flem = Q.prove (`~ ((F,a) IN FST)`, REWRITE_TAC [IN_APP]) ;

val slem = Q.prove (`A SUBSET B UNION C = A INTER $~ o B SUBSET C`,
  REWRITE_TAC [SUBSET_DEF, IN_UNION, IN_INTER] THEN
  REWRITE_TAC [IN_APP, combinTheory.o_THM] THEN
  HO_MATCH_MP_TAC ConseqConvTheory.forall_eq_thm THEN
  GEN_TAC THEN DECIDE_TAC) ;

val o_THM = combinTheory.o_THM ;

(* MATCH_MP2 delays raising an exception until second argument is seen,
  and we also need to do this for f *)
fun MATCH_MP2 th1 th2 = MATCH_MP th1 th2 ;

(* controlled repeat IMP_RES_TAC *)
(* f must not raise an exception when passed the first argument *)
fun rpt_irt' f th g = 
  (FIRST_X_ASSUM (rpt_irt' f o MATCH_MP2 th) ORELSE f th) g ;
 
fun rpt_irt f th g = let fun f2 th g = f th g in rpt_irt' f2 th g end ;

(* exactly n times *)
fun rpt_irt_n' 0 f th g = f th g
  | rpt_irt_n' n f th g = FIRST_X_ASSUM (rpt_irt_n' (n-1) f o MATCH_MP2 th) g ;

fun rpt_irt_n n f th g = let fun f2 th g = f th g in rpt_irt_n' n f2 th g end ;

val _ = rpt_irt : thm_tactical ;
val _ = rpt_irt_n : int -> thm_tactical ;

val iulem = Q.prove (`(~ ?s. y IN s ∧ s IN IMAGE g UNIV) = !n. ~ (y IN g n)`,
  mesonLib.MESON_TAC [IN_IMAGE, IN_UNIV]) ;
  
val cctac = FIRST_X_ASSUM (fn th => FIRST_X_ASSUM 
    (fn thi => MP_TAC (MATCH_MP thi (CONJ th th)))) THEN REWRITE_TAC [] ;

val rrchain_lem = Q.prove (`y IN t ==> chain t (rrestrict r s) ==> y IN s`,
  REWRITE_TAC [chain_def] THEN REPEAT STRIP_TAC THEN cctac THEN 
  ASM_REWRITE_TAC [in_rrestrict] THEN DECIDE_TAC) ;

val ex_eta_lem = Q.prove (`$? s = ?x. s x`,
  AP_TERM_TAC THEN
  Ho_Rewrite.REWRITE_TAC [FUN_EQ_THM, BETA_THM]) ;

val IN_GSPEC_IFF' = REWRITE_RULE [IN_APP] IN_GSPEC_IFF ;

val (imageE, imageI') = EQ_IMP_RULE (SPEC_ALL IN_IMAGE) ;

end ; (* local *)
end ; (* structure idtLib *)
