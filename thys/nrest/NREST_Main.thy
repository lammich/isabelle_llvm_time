theory NREST_Main                                                  
imports NREST NREST_Type_Classes NREST_Backwards_Reasoning Time_Refinement Data_Refinement
begin


class nrest_cost = complete_lattice + needname_zero + nonneg + ordered_semiring + semiring_no_zero_divisors

 
notepad
begin
  fix R :: "_ \<Rightarrow> (_,'b::nrest_cost) acost"
  fix Q :: "'c \<Rightarrow> ('a, 'b) acost option"
  fix m :: "('c, ('a, 'b) acost) nrest"
  have "Some 0 \<le> gwp (timerefine R m) Q"
    sorry

end


notepad
begin
  fix R :: "'b \<Rightarrow> ('a,enat) acost"
  fix m :: "('c, ('a, enat) acost) nrest"
  fix Q :: "'c \<Rightarrow> ('b, enat) acost option"
  have "m \<le> timerefine R (SPECT Q)"
    apply(simp add: timerefine_SPECT)
    apply(rule gwp_specifies_I)
    sorry

  have "Some 0 \<le> gwp m (timerefineF R Q)"
    sorry

end







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


definition "TId = (\<lambda>x. acostC (\<lambda>y. (if x=y then 1 else 0)))"

lemma timerefine_id:
  fixes M :: "(_,(_,enat)acost) nrest"
  shows "timerefine TId M = M"
  apply(cases M; auto simp: timerefine_def TId_def)
  apply(rule ext) apply(auto split: option.splits)
  subgoal for x2 r x2a apply(cases x2a) apply simp
    apply(rule ext) apply(simp add: if_distrib)
    apply(subst mult_zero_right)
    apply(subst Sum_any.delta) by simp
  done


lemma refine_TId[refine0]:
  fixes S :: "(_,(_,enat)acost) nrest"
  shows  "S \<le> \<Down> Id (timerefine TId S)"
  unfolding timerefine_id
  by auto



lemma the_acost_mono: "T \<le> T' \<Longrightarrow> the_acost T b \<le> the_acost T' b"
  apply(cases T; cases T') by (auto simp: le_fun_def less_eq_acost_def)




lemma SPEC_refine[refine]:
  fixes T :: "_ \<Rightarrow> ((_,enat)acost)"
  assumes *: "\<And>x. \<Phi> x \<Longrightarrow> \<exists>s'. \<Phi>' s' \<and> (x, s') \<in> R \<and> T x \<le> T' s'"
  shows "SPEC \<Phi> T \<le> \<Down>R (SPEC \<Phi>' T')"
  unfolding SPEC_def
  by (auto simp: pw_acost_le_iff refine_pw_simps dest!: * intro: order.trans[OF _ the_acost_mono])



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


thm consume_mono[where M="M::(_,(_,enat)acost) nrest"]

lemma consume_refine[refine0]:
  fixes M :: "('e, ('b, enat) acost) nrest"
  shows "\<lbrakk>t \<le> timerefineA E t'; M \<le> \<Down> R (timerefine E M')\<rbrakk> \<Longrightarrow> NREST.consume M t \<le> \<Down>R (timerefine E (NREST.consume M' t'))"
  apply(subst timerefine_consume)
  apply(subst conc_fun_consume)
  apply(rule consume_mono) by auto

lemma timerefine_RETURNT: "timerefine E (RETURNT x') = RETURNT x'"
  by (auto simp: timerefine_def RETURNT_def zero_acost_def)

lemma RETURNT_refine_t[refine]:
  assumes "(x,x')\<in>R"
  shows "RETURNT x \<le> \<Down>R (timerefine E (RETURNT x'))"
  apply(subst timerefine_RETURNT)
  apply(rule RETURNT_refine) by (fact assms)


declare RETURNT_refine_t[refine0]


lemma timerefineA_TId[refine0]:
  fixes T :: "(_,enat) acost"
  shows "T \<le> T' \<Longrightarrow> T \<le> timerefineA TId T'"
  unfolding timerefineA_def TId_def
    apply(simp add: if_distrib)
    apply(subst mult_zero_right)
    apply(subst Sum_any.delta) by(cases T; cases T'; auto)


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

(* TODO: move *)
definition "struct_preserving E \<equiv> (\<forall>t. cost ''call'' t \<le> timerefineA E (cost ''call'' t))
                                   \<and> (\<forall>t. cost ''if'' t \<le> timerefineA E (cost ''if'' t))"

lemma struct_preservingI:
  assumes "\<And>t. cost ''call'' t \<le> timerefineA E (cost ''call'' t)"
     "\<And>t. cost ''if'' t \<le> timerefineA E (cost ''if'' t)"
  shows "struct_preserving E"
  using assms unfolding struct_preserving_def by auto

lemma struct_preservingD:
  assumes "struct_preserving E"
  shows "\<And>t. cost ''call'' t \<le> timerefineA E (cost ''call'' t)"
     "\<And>t. cost ''if'' t \<le> timerefineA E (cost ''if'' t)"
  using assms unfolding struct_preserving_def by auto

lemma "(a,a)\<in>Id" unfolding Id_def by simp


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





lemma timerefineA_upd_aux: "(if a = m then x else (0::enat)) * b = (if a = m then x * b else 0)"
  by auto

lemma timerefineA_upd:
  fixes R :: "'b \<Rightarrow> ('c, enat) acost"
  shows "timerefineA (R(n:=y)) (cost m x) = (if n=m then acostC (\<lambda>z. x * the_acost y z) else timerefineA R (cost m x))"
  unfolding timerefineA_def
  by (auto simp: cost_def zero_acost_def timerefineA_upd_aux)

lemma timerefineA_TId_aux: "the_acost x a * (if b then (1::enat) else 0)
    = (if b then the_acost x a  else 0)"
  apply(cases b) by auto

lemma timerefineA_TId_eq:
  shows "timerefineA TId x = (x:: ('b, enat) acost)"
  unfolding timerefineA_def TId_def 
  by (simp add: timerefineA_TId_aux)

lemma wfR_TId: "wfR TId"
  unfolding TId_def wfR_def apply simp
  sorry

lemma "wfR' TId"
  unfolding TId_def wfR'_def by simp
lemma wfR''_TId: "wfR'' TId"
  unfolding TId_def wfR''_def by simp


lemma sp_TId: "struct_preserving (TId::_\<Rightarrow>(string, enat) acost)" 
  by (auto intro!: struct_preservingI simp: timerefineA_upd timerefineA_TId)



end