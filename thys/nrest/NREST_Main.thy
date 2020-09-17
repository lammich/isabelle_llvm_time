theory NREST_Main                                                  
imports NREST NREST_Type_Classes NREST_Backwards_Reasoning Time_Refinement Data_Refinement
begin


(* TODO: Move *)
lemma top_acost_absorbs: "top + (x::(_,enat)acost) = top"
  apply(cases x) by (auto simp: top_acost_def plus_acost_alt top_enat_def)



class nrest_cost = complete_lattice + needname_zero + nonneg + ordered_semiring + semiring_no_zero_divisors

 

abbreviation (do_notation) bind_doN where "bind_doN \<equiv> NREST.bindT"

notation (output) bind_doN (infixr "\<bind>" 54)
notation (ASCII output) bind_doN (infixr ">>=" 54)

nonterminal doN_binds and doN_bind
syntax
  "_doN_block" :: "doN_binds \<Rightarrow> 'a" ("doN {//(2  _)//}" [12] 62)
  "_doN_bind"  :: "[pttrn, 'a] \<Rightarrow> doN_bind" ("(2_ \<leftarrow>/ _)" 13)
  "_doN_let" :: "[pttrn, 'a] \<Rightarrow> doN_bind" ("(2let _ =/ _)" [1000, 13] 13)
  "_doN_then" :: "'a \<Rightarrow> doN_bind" ("_" [14] 13)
  "_doN_final" :: "'a \<Rightarrow> doN_binds" ("_")
  "_doN_cons" :: "[doN_bind, doN_binds] \<Rightarrow> doN_binds" ("_;//_" [13, 12] 12)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr "\<then>" 54)

syntax (ASCII)
  "_doN_bind" :: "[pttrn, 'a] \<Rightarrow> doN_bind" ("(2_ <-/ _)" 13)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr ">>" 54)

translations
  "_doN_block (_doN_cons (_doN_then t) (_doN_final e))"
    \<rightleftharpoons> "CONST bind_doN t (\<lambda>_. e)"
  "_doN_block (_doN_cons (_doN_bind p t) (_doN_final e))"
    \<rightleftharpoons> "CONST bind_doN t (\<lambda>p. e)"
  "_doN_block (_doN_cons (_doN_let p t) bs)"
    \<rightleftharpoons> "let p = t in _doN_block bs"
  "_doN_block (_doN_cons b (_doN_cons c cs))"
    \<rightleftharpoons> "_doN_block (_doN_cons b (_doN_final (_doN_block (_doN_cons c cs))))"
  "_doN_cons (_doN_let p t) (_doN_final s)"
    \<rightleftharpoons> "_doN_final (let p = t in s)"
  "_doN_block (_doN_final e)" \<rightharpoonup> "e"
(*  "(m \<then> n)" \<rightharpoonup> "(m \<bind> (\<lambda>_. n))"*)

(* TODO: move *)
abbreviation RETURNTecost :: "'a \<Rightarrow> ('a, (string,enat) acost) nrest"
  where "RETURNTecost \<equiv> RETURNT"


subsection \<open>Setup for refinement condition generator\<close>




lemma consume_refine:
  fixes M :: "('e, ('b, enat) acost) nrest"
  assumes "wfR'' E"
  shows "\<lbrakk>t \<le> timerefineA E t'; M \<le> \<Down> R (timerefine E M')\<rbrakk> \<Longrightarrow> NREST.consume M t \<le> \<Down>R (timerefine E (NREST.consume M' t'))"
  apply(subst timerefine_consume)
  subgoal using assms .
  apply(subst conc_fun_consume)
  apply(rule consume_mono) by auto

lemma MIf_refine:
  fixes f :: "(_,(string, enat) acost) nrest"
  shows "struct_preserving E \<Longrightarrow> wfR'' E \<Longrightarrow> (b,b')\<in>bool_rel \<Longrightarrow> (b \<Longrightarrow> f \<le> \<Down>R (timerefine E f'))
           \<Longrightarrow> (\<not>b \<Longrightarrow> g \<le> \<Down>R (timerefine E g')) \<Longrightarrow>  MIf b f g  \<le> \<Down>R (timerefine E (MIf b' f' g' ))"
  by(auto simp: MIf_def timerefineA_update_apply_same_cost dest: struct_preservingD intro!: consume_refine)



thm refine

thm ASSERT_leI_f
lemma ASSERT_D_leI[refine,refine0]: 
  fixes M :: "(_,(_,enat)acost) nrest"
  shows "\<Phi> \<Longrightarrow> (\<Phi> \<Longrightarrow> M \<le> \<Down>R M') \<Longrightarrow> ASSERT \<Phi> \<bind> (\<lambda>_. M) \<le> \<Down>R M'"
  by (auto)

lemma ASSERT_D2_leI[refine0]: 
  fixes S' :: "(_,(_,enat)acost) nrest"
  shows "(\<Phi> \<Longrightarrow> S \<le> \<Down> R S') \<Longrightarrow> S \<le> \<Down> R (do {
                                     _ \<leftarrow> ASSERT \<Phi>;
                                     S'
                                   })"
  by (auto simp: pw_acost_le_iff refine_pw_simps)


lemma ASSERT_D3_leI[refine0]: 
  fixes S' :: "(_,(_,enat)acost) nrest"
  shows "(\<Phi> \<Longrightarrow> S \<le> \<Down> R (timerefine E S')) \<Longrightarrow> S \<le> \<Down> R (timerefine E (do {
                                     _ \<leftarrow> ASSERT \<Phi>;
                                     S'
                                   }))"
  by (auto simp: pw_acost_le_iff refine_pw_simps)


lemma ASSERT_D4_leI[refine0]: 
  fixes S' :: "(_,(_,enat)acost) nrest"
  shows "(\<Phi> \<Longrightarrow> S \<le> \<Down> R (timerefine E S')) \<Longrightarrow> do { _ \<leftarrow> ASSERT \<Phi>; S } \<le> \<Down> R (timerefine E (do {
                                     _ \<leftarrow> ASSERT \<Phi>;
                                     S'
                                   }))"
  by (auto simp: pw_acost_le_iff refine_pw_simps)


lemma refine_Id[refine0]: "S \<le> \<Down> Id S"
  by auto


lemma refine_TId[refine0]:
  fixes S :: "(_,(_,enat)acost) nrest"
  shows  "S \<le> \<Down> Id (timerefine TId S)"
  unfolding timerefine_id
  by auto





lemma SPEC_refine[refine]:
  fixes T :: "_ \<Rightarrow> ((_,enat)acost)"
  assumes *: "\<And>x. \<Phi> x \<Longrightarrow> \<exists>s'. \<Phi>' s' \<and> (x, s') \<in> R \<and> T x \<le> T' s'"
  shows "SPEC \<Phi> T \<le> \<Down>R (SPEC \<Phi>' T')"
  unfolding SPEC_def
  by (auto simp: pw_acost_le_iff refine_pw_simps dest!: * intro: order.trans[OF _ the_acost_mono])

    
thm SPEC_timerefine SPEC_refine
lemma SPEC_both_refine:
  fixes T :: "_ \<Rightarrow> ((_,enat)acost)"
  assumes "\<And>x. \<Phi> x \<Longrightarrow> \<exists>s'. \<Phi>' s' \<and> (x, s') \<in> R \<and> T x \<le> timerefineA TR (T' s')"
  shows "SPEC \<Phi> T \<le> \<Down> R (timerefine TR (SPEC \<Phi>' T'))"
  apply(rule order.trans) 
  defer
   apply(rule nrest_Rel_mono)
   apply(rule SPEC_timerefine[where A=\<Phi>'])
    prefer 3 apply(rule SPEC_refine[where T=T])
    defer apply simp apply(rule order_refl)
  by (fact assms)




lemma build_rel_SPEC_conv:
  fixes T :: "_ \<Rightarrow> ((_,enat)acost)"
  assumes "\<And>x. T (\<alpha> x) = T' x"
  shows "\<Down>(br \<alpha> I) (SPEC \<Phi> T) = SPEC (\<lambda>x. I x \<and> \<Phi> (\<alpha> x)) T'"  
  using assms by (auto simp: br_def pw_acost_eq_iff refine_pw_simps SPEC_def)

lemma SPEC_cong: "\<Phi>=\<Phi>' \<Longrightarrow> T=T' \<Longrightarrow> SPEC \<Phi> T = SPEC \<Phi>' T'"
  by simp



lemma le_acost_ASSERTI:
  fixes M :: "(_,(_,enat) acost) nrest"
  shows "(\<Phi> \<Longrightarrow> M \<le> M') \<Longrightarrow> M \<le> ASSERT \<Phi> \<bind> (\<lambda>_. M')"
  by(auto simp: pw_acost_le_iff refine_pw_simps)

lemma consume_RETURNT: "consume (RETURNT x) T = SPECT [x \<mapsto> T]"
  by(auto simp: RETURNT_def consume_def)

  lemma gwp_specifies_acr_I: 
    fixes m :: "(_,(_,enat) acost) nrest"
    shows "(\<Phi> \<Longrightarrow> gwp m [x \<mapsto> T] \<ge> Some 0) \<Longrightarrow> (m \<le> doN { ASSERT \<Phi>; consume (RETURNT x) T })"
    apply(rule le_acost_ASSERTI)
    unfolding consume_RETURNT
    apply(rule gwp_specifies_I) by simp
thm refine
thm refine0


thm consume_mono[refine0]



lemma ASSERT_D5_leI[refine0]: 
  fixes S' :: "(_,(_,enat)acost) nrest"
  shows "(\<Phi> \<Longrightarrow> \<Down> R (timerefine F S) \<le> \<Down> R (timerefine E S')) \<Longrightarrow> \<Down> R (timerefine F ( do { _ \<leftarrow> ASSERT \<Phi>; S })) \<le> \<Down> R (timerefine E (do {
                                     _ \<leftarrow> ASSERT \<Phi>;
                                     S'
                                   }))"
  by (auto simp: pw_acost_le_iff refine_pw_simps)



thm consume_mono[where M="M::(_,(_,enat)acost) nrest"]

declare consume_refine[refine0]


lemma timerefine_RETURNT: "timerefine E (RETURNT x') = RETURNT x'"
  by (auto simp: timerefine_def RETURNT_def zero_acost_def)

lemma RETURNT_refine_t[refine]:
  assumes "(x,x')\<in>R"
  shows "RETURNT x \<le> \<Down>R (timerefine E (RETURNT x'))"
  apply(subst timerefine_RETURNT)
  apply(rule RETURNT_refine) by (fact assms)


declare RETURNT_refine_t[refine0]
declare timerefineA_TId[refine0]


(* TODO: move *)

lemma timerefine_SPECT_map: "timerefine E (SPECT [x'\<mapsto>t]) = SPECT [x'\<mapsto>timerefineA E t]"
  by (auto simp: timerefine_def timerefineA_def intro!: ext)

lemma SPECT_refine_t[refine]:
  fixes t :: "(_,enat) acost"
  assumes "(x,x')\<in>R"
    and "t\<le> timerefineA E t'"
  shows "SPECT [x\<mapsto>t] \<le> \<Down>R (timerefine E (SPECT [x'\<mapsto>t']))"
  apply(subst timerefine_SPECT_map)
  using assms apply(auto simp: pw_acost_le_iff refine_pw_simps)
  apply(cases t) apply (auto simp: less_eq_acost_def)
  subgoal for b ta xa apply(rule order.trans[where b="xa b"]) by auto
  done
lemma consume_refine_easy:
  fixes M :: "('e, ('b, enat) acost) nrest"
  shows "\<lbrakk>t \<le> t'; M \<le> \<Down> R (   M')\<rbrakk> \<Longrightarrow> NREST.consume M t \<le> \<Down>R (  (NREST.consume M' t'))" 
  apply(subst conc_fun_consume)
  apply(rule consume_mono) by auto



lemma RECT_refine_t:
  assumes M: "mono2 body"
  assumes R0: "(x,x')\<in>R"
  assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le>\<Down>S (timerefine E (f' x')); (x,x')\<in>R \<rbrakk> 
    \<Longrightarrow> body f x \<le>\<Down>S (timerefine E (body' f' x'))"
  shows "RECT (\<lambda>f x. body f x) x \<le>\<Down>S (timerefine E (RECT (\<lambda>f' x'. body' f' x') x'))"
  unfolding RECT_flat_gfp_def
  apply (clarsimp simp add: M) 
  apply (rule flatf_fixp_transfer[where 
        fp'="flatf_gfp body" 
    and B'=body 
    and P="\<lambda>x x'. (x',x)\<in>R", 
    OF _ _ flatf_ord.fixp_unfold[OF M[THEN trimonoD_flatf_ge]] R0])
  apply simp
  apply (simp add: trimonoD_flatf_ge)
  by (rule RS)



lemma RECT'_refine_t:
  fixes body :: "('b \<Rightarrow> ('c, (char list, enat) acost) nrest)
   \<Rightarrow> 'b \<Rightarrow> ('c, (char list, enat) acost) nrest"
  assumes M: "mono2 body"
  assumes wfRE: "wfR'' E"
  assumes spE: "struct_preserving E"
  assumes R0: "(x,x')\<in>R"
  assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le>\<Down>S (timerefine E (f' x')); (x,x')\<in>R \<rbrakk> 
    \<Longrightarrow> body f x \<le>\<Down>S (timerefine E (body' f' x'))"
  shows "RECT' (\<lambda>f x. body f x) x \<le>\<Down>S (timerefine E (RECT' (\<lambda>f' x'. body' f' x') x'))"
  unfolding RECT'_def
  apply(rule consume_refine[OF wfRE])
  subgoal using spE[THEN struct_preservingD(1)] by simp
  unfolding RECT_flat_gfp_def
  apply (clarsimp simp add: M[THEN RECT'_unfold_aux])
  apply (rule flatf_fixp_transfer[where 
        fp'="flatf_gfp ((\<lambda>D. body (\<lambda>x. NREST.consume (D x) (cost ''call'' 1))))" 
    and B'="(\<lambda>D. body (\<lambda>x. NREST.consume (D x) (cost ''call'' 1)))" 
    and P="\<lambda>x x'. (x',x)\<in>R", 
    OF _ _ flatf_ord.fixp_unfold[OF M[THEN RECT'_unfold_aux, THEN trimonoD_flatf_ge]] R0])
  apply simp
  apply (simp add: trimonoD_flatf_ge)
  apply (rule RS)
   apply(rule consume_refine[OF wfRE])
  subgoal using spE[THEN struct_preservingD(1)] by simp
   apply simp apply simp
  done



lemma monadic_WHILEIT_refine_t[refine]:  
  fixes b :: "'c \<Rightarrow> (bool, (char list, enat) acost) nrest"
  assumes wfR[simp]:  "wfR'' E"
  assumes sp_E: "struct_preserving E"
  assumes [refine]: "(s',s) \<in> R"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s \<rbrakk> \<Longrightarrow> I' s'"  
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s' \<rbrakk> \<Longrightarrow> b' s' \<le>\<Down>bool_rel (timerefine E (b s))"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s'; nofailT (b s);  \<exists>t e. inresT (project_acost  e (b s)) True t \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (timerefine E (f s))"
  shows "monadic_WHILEIT I' b' f' s' \<le> \<Down>R (timerefine E (monadic_WHILEIT I b f s))"
  unfolding monadic_WHILEIT_def unfolding MIf_def 
  apply (refine_rcg bindT_refine_conc_time2 RECT_refine_t IdI wfR struct_preservingD[OF sp_E]) 
  apply simp  
  subgoal by refine_mono
  apply (assumption?; auto)+
  apply (refine_rcg consume_refine_easy bindT_refine_conc_time2 wfR struct_preservingD[OF sp_E] RETURNT_refine_t )
       apply (assumption?; auto)+
  apply(rule RETURNT_refine_t) 
  apply (assumption?; auto)+ 
  done



lemma monadic_WHILEIT_refine':  
  fixes b :: "'c \<Rightarrow> (bool, (char list, enat) acost) nrest"
  assumes wfR[simp]:  "wfR'' E"
  assumes sp_E: "struct_preserving E"
  assumes [refine]: "(s',s) \<in> R"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s \<rbrakk> \<Longrightarrow> I' s'"  
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s' \<rbrakk> \<Longrightarrow> b' s' \<le>\<Down>bool_rel (timerefine E (b s))"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s'; inres (b s) True \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (timerefine E (f s))"
  shows "monadic_WHILEIT I' b' f' s' \<le> \<Down>R (timerefine E (monadic_WHILEIT I b f s))"
  apply(rule monadic_WHILEIT_refine_t[OF assms(1-5)])
  by(auto intro: assms(6) inres_if_inresT_acost)

subsection \<open>mop call\<close>


definition mop_call where
  "mop_call m = consume m (cost ''call'' 1)"



lemma gwp_call[vcg_rules']:
  fixes m :: "(_,(_,enat) acost) nrest"
  assumes "Some (cost ''call'' 1 + t) \<le> gwp m Q"
  shows  "Some t \<le> gwp (mop_call m) Q"
  unfolding mop_call_def
  apply(rule gwp_consume) by(rule assms)


lemma mop_call_refine:
  fixes M :: "('e, (string, enat) acost) nrest"
  assumes "wfR'' E"
    "struct_preserving E"
  shows "\<lbrakk> M \<le> \<Down> R (timerefine E M')\<rbrakk> \<Longrightarrow> mop_call M \<le> \<Down>R (timerefine E (mop_call M'))"
  unfolding mop_call_def
  apply(subst timerefine_consume)
  subgoal using assms(1) .
  apply(subst conc_fun_consume)
  apply(rule consume_mono) 
  using assms(2)[THEN struct_preservingD(1)]  
  by auto                                    
 



subsection \<open>Shortcuts for specifications of operations\<close>

  definition "SPECc1' c aop == (\<lambda>a. SPECT ( [(aop a)\<mapsto>c]))"
  definition "SPECc1 name aop == (\<lambda>a. SPECT ( [(aop a)\<mapsto>(cost name 1)]))"
  definition "SPECc2 name aop == ( (\<lambda>a b. SPECT ( [(aop a b)\<mapsto>(cost name 1)])))"




lemma inres_SPECc2: "inres (SPECc2 n op a b) t \<longleftrightarrow> (op a b = t)"
  by(auto simp: inres_def SPECc2_def)


lemma SPECc2_alt: "SPECc2 name aop = ( (\<lambda>a b. consume (RETURNT (aop a b)) (cost name 1)))"
  unfolding SPECc2_def consume_def by(auto simp: RETURNT_def intro!: ext)




lemma SPECc2_refine':
  fixes TR :: "'h \<Rightarrow> ('h, enat) acost"
  shows "(op x y, op' x' y')\<in>R \<Longrightarrow> preserves_curr TR n  \<Longrightarrow> SPECc2 n op x y \<le> \<Down> R (timerefine TR (SPECc2 n op' x' y'))"
  unfolding SPECc2_def    
  apply(subst SPECT_refine_t) by (auto simp: preserves_curr_def timerefineA_cost_apply) 
  


lemma SPECc2_refine:
  "(op x y, op' x' y')\<in>R \<Longrightarrow> cost n (1::enat) \<le> TR n'  \<Longrightarrow> SPECc2 n op x y \<le> \<Down> R (timerefine TR (SPECc2 n' op' x' y'))"
  unfolding SPECc2_def    
  apply(subst SPECT_refine_t) apply auto
  apply(rule order.trans) apply (simp add: )
  apply(subst timerefineA_cost) by simp


subsection "normalize blocks"

text \<open>The idea of the following tactic is to normalize all straight line blocks,
      such that they have the form (doN { [ASSUMEs]; consumea T; [RETURNs]; FURTHER }.      
      To that end, it assumes that most operations are unfolded and only contain consumea, RETURN
      or consume (RETURN _) _. The RETURNs will be propagated with @{thm nres_bind_left_identity},
      ASSERTIONs will be pulled to the front, consumeas will be shrinked and assoc rule is applied.

      It then is assumed, that FURTHER statements in the concrete and abstract are in lock step.

      [ Then refine_block will split products, collect and discharge ASSUME statements, 
      pay for the consumea; and then stop at a FURTHER statement.
      One can then give "rules" that process the FURTHER statements. ]
      This process is way better done by refine_rcg!
      
      This allows that not only lockstep refinement is possible, but that by unfolding certain
      operations, their effects get 
        \<close>

lemma consumea_refine:
  fixes t :: "(_,enat) acost"
  shows "((), ()) \<in> R \<Longrightarrow> t \<le> timerefineA F t' \<Longrightarrow> consumea t \<le> \<Down> R (timerefine F (consumea t'))"
  unfolding consumea_def
  apply(rule SPECT_refine_t) by auto

lemma consumea_Id_refine:
  fixes t :: "(_,enat) acost"
  shows "t \<le> timerefineA F t' \<Longrightarrow> consumea t \<le> \<Down> Id (timerefine F (consumea t'))"
  unfolding consumea_def
  apply(rule SPECT_refine_t) by auto
    

lemma swap_consumea_ASSERT: "do { consumea t; ASSERT P; M:: ('c, ('d, enat) acost) nrest} = do {ASSERT P; consumea t; M}"
  apply(auto simp: pw_acost_eq_iff refine_pw_simps consumea_def)
  apply (metis zero_enat_def zero_le)
  using le_Suc_ex zero_enat_def by force


lemma consumea_0_noop:
  fixes m :: "('b,'c::{complete_lattice,zero,monoid_add}) nrest"
  shows "do { consumea 0; m } = m"
  apply(auto simp: consumea_def bindT_def split: nrest.splits intro!: ext) 
  subgoal for x2 x apply(cases "x2 x") by auto
  done

thm refine0              

lemma forget_inresT_project_acos: "\<exists>t b. inresT (project_acost b (consumea tt)) x' t \<Longrightarrow> True"
  by simp

lemma forget_nofailT_consumea: "nofailT (consumea tt) \<Longrightarrow> True"
  by simp

lemmas normalize_inres_precond = forget_nofailT_consumea forget_inresT_project_acos
                                  inresT_consumea_D EX_inresT_SPECTONE_D

method normalize_blocks = (simp only: swap_consumea_ASSERT nres_acost_bind_assoc consume_alt consumea_shrink nres_bind_left_identity)
method refine_block uses rules = (drule normalize_inres_precond |split prod.splits | intro allI impI
                                    | rule refine0 consumea_Id_refine SPECT_refine_t bindT_refine_conc_time_my rules)
method refine_blocks uses rules = repeat_all_new \<open>refine_block rules: rules\<close>


subsection \<open>Simple bind rule with inres\<close>


lemma bindT_refine_conc_time_my_inres:
  fixes m :: "('e1,('c1,enat)acost) nrest"
  fixes m' :: "('e2,('c2,enat)acost) nrest"
  assumes "wfR'' E" " m \<le> \<Down>R' (timerefine E m')"
  "(\<And>x x'. \<lbrakk>(x,x')\<in>R'; inres m' x'\<rbrakk>
         \<Longrightarrow> f x \<le> \<Down> R (timerefine E (f' x') ))"
shows "bindT m f \<le>  \<Down> R (timerefine E (bindT m' f'))"
  apply(rule bindT_refine_conc_time2) using assms
  by (auto dest: inres_if_inresT_acost)

term consume
lemma bindT_refine_conc_time_easy:
  fixes m :: "('e1,('c1,enat)acost) nrest"
  fixes m' :: "('e2,('c2,enat)acost) nrest"
  assumes "wfR E" " m \<le> \<Down>R' (timerefine E m')"
  "(\<And>x x'. \<lbrakk>(x,x')\<in>R' \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (timerefine E (f' x') ))"
shows "bindT m f \<le>  \<Down> R (timerefine E (bindT m' f'))"
  apply(rule bindT_refine_conc_time)
    apply fact
   apply fact
  apply(rule assms(3)) apply simp
  done

lemma bindT_refine_easy:
  fixes m :: "('e1,('c1,enat)acost) nrest"
  fixes m' :: "('e2,('c2,enat)acost) nrest"
  assumes "wfR'' E" " m \<le> \<Down>R' (timerefine E m')"
  "(\<And>x x'. \<lbrakk>(x,x')\<in>R'\<rbrakk>
         \<Longrightarrow> f x \<le> \<Down> R (timerefine E (f' x') ))"
shows "bindT m f \<le>  \<Down> R (timerefine E (bindT m' f'))"
  apply(rule bindT_refine_conc_time2) using assms
  by (auto dest: inres_if_inresT_acost)


end