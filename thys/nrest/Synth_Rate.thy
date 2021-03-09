theory Synth_Rate
  imports Currs_Of
begin




lemma wfR''_supI:
  fixes R:: "'b \<Rightarrow> ('c, enat) acost"
  shows "wfR'' R \<Longrightarrow> wfR'' R' \<Longrightarrow> wfR'' (sup R R')"
  unfolding wfR''_def
  apply auto
  subgoal premises prems for f
    apply(rule finite_subset[where B="{s. the_acost (R s) f \<noteq> 0 \<or> the_acost (R' s) f \<noteq> 0}"])
    subgoal apply auto  
      by (simp add: sup_acost_def)    
    subgoal
      using prems[rule_format, of f]  
      using finite_Collect_disjI by fastforce   
    done
  done



lemma bindT_refine_conc_time_my_inres_sup:
  fixes m :: "('e1,('c1,enat)acost) nrest"
  fixes m' :: "('e2,('c2,enat)acost) nrest"
  assumes  " m \<le> \<Down>R' (timerefine Em m')"
  "(\<And>x x'. \<lbrakk>(x,x')\<in>R'; inres m' x'\<rbrakk>
         \<Longrightarrow> f x \<le> \<Down> R (timerefine Ef (f' x') ))"
  and E: "E = sup Em Ef"
  and "wfR'' Em"
      "wfR'' Ef"
shows "bindT m f \<le>  \<Down> R (timerefine E (bindT m' f'))"
  apply(rule bindT_refine_conc_time2[where R=R])
  subgoal unfolding E apply(rule wfR''_supI) using assms by auto
   apply(rule order.trans)
    apply(rule assms(1))
   apply(rule nrest_Rel_mono)
  apply(rule timerefine_R_mono_wfR'')
  subgoal unfolding E apply(rule wfR''_supI) using assms by auto
  subgoal unfolding E by auto
   apply(rule order.trans)
   apply(rule assms(2))
    apply simp 
  subgoal by(auto dest: inres_if_inresT_acost)
   apply(rule nrest_Rel_mono)
  apply(rule timerefine_R_mono_wfR'')
  subgoal unfolding E apply(rule wfR''_supI) using assms by auto
  subgoal unfolding E by auto
  done



lemma SPECc2_refine_exch:
  shows  "(op x y, op' x' y')\<in>R  \<Longrightarrow> (SPECc2 n op x y :: (_,(_,enat) acost)nrest) \<le> \<Down> R (timerefine ((\<lambda>_. 0)(n':=cost n 1)) (SPECc2 n' op' x' y'))"
  unfolding SPECc2_def
  supply [[unify_trace_failure]]
  apply(subst SPECT_refine_t) apply auto 
  apply(subst timerefineA_cost) by simp


end