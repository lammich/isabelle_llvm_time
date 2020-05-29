theory Data_Refinement
imports NREST Time_Refinement 
begin


subsection \<open>Data Refinement\<close>


definition conc_fun  ("\<Down>") where
  "conc_fun R m \<equiv> case m of FAILi \<Rightarrow> FAILT | REST X \<Rightarrow> REST (\<lambda>c. Sup {X a| a. (c,a)\<in>R})"

definition abs_fun ("\<Up>") where
  "abs_fun R m \<equiv> case m of FAILi \<Rightarrow> FAILT 
    | REST X \<Rightarrow> if dom X\<subseteq>Domain R then REST (\<lambda>a. Sup {X c| c. (c,a)\<in>R}) else FAILT"

lemma 
  conc_fun_FAIL[simp]: "\<Down>R FAILT = FAILT" and
  conc_fun_RES: "\<Down>R (REST X) = REST (\<lambda>c. Sup {X a| a. (c,a)\<in>R})"
  unfolding conc_fun_def by (auto split: nrest.split)

lemma 
  abs_fun_FAIL[simp]: "\<Up>R FAILT = FAILT" and
  abs_fun_RES: "\<Up>R (REST X) = (if dom X\<subseteq>Domain R then REST (\<lambda>a. Sup {X c| c. (c,a)\<in>R}) else FAILT)"
  unfolding abs_fun_def by (auto split: nrest.split)


lemma conc_fun_spec_ne_FAIL[simp]: "\<Down>R (SPECT M) \<noteq> FAILT" by (simp add: conc_fun_RES)   

notepad begin
  fix m m' :: "bool \<Rightarrow> ( (string,enat) acost) option" and R co x
  assume m: "m = [ True \<mapsto> acostC ((\<lambda>_. 0)(''a'':=2,''b'':=2)) ]"
  
  assume m': "m' = [ True \<mapsto> acostC ((\<lambda>_. 0)(''a'':=1,''b'':=2)), False \<mapsto> acostC ((\<lambda>_. 0)(''a'':=2,''b'':=1))]"
  assume "m \<le> (\<lambda>c. Sup {m' a |a. (c, a) \<in> R})"
        "m x = Some co"
  assume R_def: "R = {(True,False), (True,True)}"
  have i: "(\<lambda>c. Sup {m' a |a. (c, a) \<in> R}) = [ True \<mapsto> acostC ((\<lambda>_. 0)(''a'':=2,''b'':=2)) ]"
    apply (rule ext)
    subgoal for c
      apply(cases c)
      subgoal unfolding R_def m' apply auto unfolding Sup_option_def apply auto
        unfolding Sup_acost_def apply auto apply(rule ext) sorry         
      subgoal unfolding R_def by (simp add: bot_option_def) 
      done
    done
  have "m \<le> (\<lambda>c. Sup {m' a |a. (c, a) \<in> R})"
    unfolding i m by simp
  have "\<exists>x'. (x, x') \<in> R \<and> (\<exists>c'\<ge>co. m' x' = Some c')" 
    sorry

end
    


lemma SupSup_2: "Sup {m a |a. (c, a) \<in> R O S} =  Sup {m a |a b. (b,a)\<in>S \<and> (c,b)\<in>R }"
proof -
  have i: "\<And>a. (c,a) \<in> R O S \<longleftrightarrow> (\<exists>b. (b,a)\<in>S \<and> (c,b)\<in>R)" by auto
  have "Sup {m a |a. (c, a) \<in> R O S} = Sup {m a |a. (\<exists>b. (b,a)\<in>S \<and> (c,b)\<in>R)}" 
      unfolding i by auto
    also have "...  = Sup {m a |a b. (b,a)\<in>S \<and> (c,b)\<in>R}" by auto
    finally show ?thesis .
  qed


lemma 
  fixes m :: "'a \<Rightarrow> ('c::complete_lattice) option"
  shows SupSup: "Sup {Sup {m aa |aa. P a aa c} |a. Q a c} = Sup {m aa |a aa. P a aa c \<and> Q a c}"
  apply(rule antisym)
   subgoal apply(rule Sup_least)
     by (auto intro: Sup_subset_mono)
   subgoal 
     unfolding Sup_le_iff apply auto
     by (smt Sup_upper Sup_upper2 mem_Collect_eq)
   done 


lemma 
  fixes m :: "'a \<Rightarrow> ('c::complete_lattice) option"
  shows 
    SupSup_1: "Sup {Sup {m aa |aa. (a, aa) \<in> S} |a. (c, a) \<in> R} = Sup {m aa |a aa. (a,aa)\<in>S \<and> (c,a)\<in>R}"
  by(rule SupSup)



lemma project_acost_conc_fun_commute[refine_pw_simps]: "project_acost b (\<Down>R m) = \<Down>R (project_acost b m)"
  unfolding project_acost_def conc_fun_def
  apply(cases m)
  subgoal by simp
  subgoal
    supply *[simp] = continuous_option'[OF continuous_the_acost, THEN continuousD]
    apply simp
    apply(rule ext)
    apply(rule arg_cong[where f=Sup])
    by auto
  done
 


(* 
lemma conc_fun_RES_sv: "single_valued R \<Longrightarrow> 
  \<Down>R (REST X) = REST (\<lambda>c. if c\<in>Dom R then Some (X Sup {X a| a. (c,a)\<in>R})"
*)

lemma nrest_Rel_mono:
  fixes A :: "('a,'b::complete_lattice) nrest"
  shows "A \<le> B \<Longrightarrow> \<Down> R A \<le> \<Down> R B"
  unfolding conc_fun_def
  apply (auto split: nrest.split simp: le_fun_def)  
  by (smt complete_lattice_class.Sup_mono mem_Collect_eq)   




lemma pw_conc_nofail[refine_pw_simps]: 
  "nofailT (\<Down>R S) = nofailT S"
  by (cases S) (auto simp: conc_fun_RES)

lemma "single_valued A \<Longrightarrow> single_valued B \<Longrightarrow> single_valued (A O B)"
  by (simp add: single_valued_relcomp)

lemma Sup_enatoption_less2: " Sup X = Some \<infinity> \<Longrightarrow> (\<exists>x. Some x \<in> X \<and> enat t < x)"
  using Sup_enat_less2
  by (metis Sup_option_def in_these_eq option.distinct(1) option.sel)

lemma pw_conc_inres[refine_pw_simps]:
  "inresT (\<Down>R S') s t = (nofailT S' 
  \<longrightarrow> ((\<exists>s'. (s,s')\<in>R \<and> inresT S' s' t) \<comment> \<open> \<and> (\<forall>s' t'. (s,s')\<in>R \<longrightarrow> inresT S' s' t' \<longrightarrow> t' \<le> t )\<close> ))"
  apply (cases S')
  subgoal by simp
  subgoal  for m'
    apply rule
    subgoal 
      apply (auto simp: conc_fun_RES  )
      subgoal for t' 
        apply(cases t')
         apply auto
        subgoal for n apply(auto dest!: Sup_finite_enat) 
          subgoal for a apply(rule exI[where x=a]) apply auto
            apply(rule exI[where x="enat n"]) by auto  
          done
        subgoal apply(drule Sup_enatoption_less2[where t=t])
          apply auto subgoal for x a apply(rule exI[where x=a]) apply auto
            apply(rule exI[where x=x]) by auto 
          done
        done
      done
    subgoal 
      apply (auto simp: conc_fun_RES)
      by (smt Sup_upper dual_order.trans le_some_optE mem_Collect_eq)
    done
  done 

lemma bindT_conc_refine':
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x' t . \<lbrakk> (x,x')\<in>R'; inresT M x t; inresT M' x' t;
    nofailT M; nofailT M'
  \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bindT M (\<lambda>x. f x) \<le> \<Down> R (bindT M' (\<lambda>x'. f' x'))"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  by blast 




lemma bindT_conc_acost_refine:
  fixes M :: "(_,(_,enat)acost) nrest"
    and R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x' t . \<lbrakk> (x,x')\<in>R'; 
    nofailT M; nofailT M'
  \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bindT M (\<lambda>x. f x) \<le> \<Down> R (bindT M' (\<lambda>x'. f' x'))"
  using assms
  apply (simp add: pw_acost_le_iff refine_pw_simps)
  by metis



lemma bindT_conc_acost_refine':
  fixes M :: "(_,(_,enat)acost) nrest"
    and R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x' t b. \<lbrakk> (x,x')\<in>R'; \<exists>t b. inresT (project_acost b M) x t; \<exists>t b. inresT (project_acost b M') x' t;
    nofailT M; nofailT M'
  \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bindT M (\<lambda>x. f x) \<le> \<Down> R (bindT M' (\<lambda>x'. f' x'))"
  using assms
  apply (simp add: pw_acost_le_iff refine_pw_simps)
  by metis


lemma inresT_project_acost_timerefine: "inresT (project_acost b (timerefine E m')) x' t 
       \<Longrightarrow> \<exists>t b. inresT (project_acost b m') x' t"
  unfolding inresT_def project_acost_def timerefine_def
  apply(cases m'; auto simp: le_fun_def split: if_splits option.splits)
  by (metis zero_enat_def zero_le)  


lemma bindT_refine_conc_time:
  fixes m :: "('e1,('c1,enat)acost) nrest"
  fixes m' :: "('e2,('c2,enat)acost) nrest"
  assumes "wfR E" " m \<le> \<Down>R' (timerefine E m')"
  "(\<And>x x'. \<lbrakk>(x,x')\<in>R';  \<exists>t b. inresT (project_acost b m) x t;  \<exists>t b. inresT (project_acost b m') x' t;
    nofailT m; nofailT m'\<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (timerefine E (f' x') ))"
shows "bindT m f \<le>  \<Down> R (timerefine E (bindT m' f'))"
  using assms
proof -
  term "(timerefine E m')"
  term timerefine
  have "bindT m (\<lambda>x.  (f x)) \<le>  \<Down> R (bindT (timerefine E m') (\<lambda>x. timerefine E (f' x)))"
    apply(rule bindT_conc_acost_refine') apply(rule assms(2)) 
    apply(rule assms(3))  
    by (auto simp: refine_pw_simps dest: inresT_project_acost_timerefine) 
  also have "\<dots> \<le> \<Down> R (timerefine E (bindT m' f'))"
    apply(rule nrest_Rel_mono)
    apply(rule timerefine_bindT_ge) by(fact assms(1))
  finally show ?thesis .
qed


lemma "(x,x')\<in>R \<Longrightarrow> (RETURNT x ::(_,'a::{nonneg,order,complete_lattice,zero}) nrest ) \<le> \<Down>R (RETURNT x')"
  unfolding conc_fun_def RETURNT_def apply (auto simp: le_fun_def) 
proof -
  consider "{uu:: 'a option. \<exists>a. (a = x' \<longrightarrow> uu = Some 0) \<and> (a \<noteq> x' \<longrightarrow> uu = None \<and> (x, a) \<in> R)} = { Some 0, None}"
    | "{uu:: 'a option. \<exists>a. (a = x' \<longrightarrow> uu = Some 0) \<and> (a \<noteq> x' \<longrightarrow> uu = None \<and> (x, a) \<in> R)} = { Some 0}"
    by auto
  then show " Sup {uu:: 'a option. \<exists>a. (a = x' \<longrightarrow> uu = Some 0) \<and> (a \<noteq> x' \<longrightarrow> uu = None \<and> (x, a) \<in> R)} \<ge> Some 0"
    apply cases by simp_all
qed



(*
experiment
begin




lemma bindT_refine'':
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x' t . \<lbrakk> (x,x')\<in>R'    
  \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bindT M (\<lambda>x. f x) \<le> \<Down> R (bindT M' (\<lambda>x'. f' x'))" 
  sorry


lemma bindT_mono_under_timerefine:
  fixes R :: "('a \<Rightarrow> ('a, enat) acost)"
  assumes wfR: "wfR R"
  shows "m \<le> timerefine R m' \<Longrightarrow> (\<And>x. f x \<le> timerefine R (f' x)) \<Longrightarrow> bindT m f \<le> timerefine R (bindT m' f')"
  apply(rule order.trans) defer apply(subst timerefine_bindT_ge) using assms apply simp apply simp
  apply(rule bindT_mono_f2) by simp_all

thm bindT_refine'' bindT_mono_under_timerefine

lemma 
  assumes "wfR tR" and sv: "single_valued R" and sv: "single_valued R'"
  assumes R1: "M \<le> (timerefine tR (\<Down> R'  M'))"
  assumes R2: "\<And>x x' t . \<lbrakk> (x,x')\<in>R' \<rbrakk> \<Longrightarrow> f x \<le> (timerefine tR ( \<Down> R  (f' x')))"
  shows "bindT M (\<lambda>x. f x) \<le> (timerefine tR (\<Down> R  (bindT M' (\<lambda>x'. f' x'))))"
  apply(subst datarefine_timerefine_commute[symmetric, OF assms(1,2)])

  apply(rule order.trans)
   defer apply(rule nrest_Rel_mono) apply(subst timerefine_bindT_ge[OF assms(1)]) apply simp
  apply(rule bindT_refine''[where R'=R'])
  apply(rule order.trans[OF R1])
   apply(subst datarefine_timerefine_commute[  OF assms(1,3)]) apply simp
  apply(rule order.trans[OF R2]) apply simp
  apply(subst datarefine_timerefine_commute[  OF assms(1,2)]) apply simp
  done


lemma 
  assumes "wfR tR" 
  assumes R1: "M \<le> (\<Down> R'(timerefine tR   M'))"
  assumes R2: "\<And>x x' t . \<lbrakk> (x,x')\<in>R' \<rbrakk> \<Longrightarrow> f x \<le> ( \<Down> R (timerefine tR  (f' x')))"
  shows "bindT M (\<lambda>x. f x) \<le> (\<Down> R (timerefine tR   (bindT M' (\<lambda>x'. f' x'))))" 
  apply(rule order.trans)
   defer apply(rule nrest_Rel_mono) apply(subst timerefine_bindT_ge[OF assms(1)]) apply simp
  apply(rule bindT_refine''[where R'=R'])
  apply(rule R1) 
  apply(rule R2) by simp 



    
  

                     


end *)





subsubsection \<open>Examples\<close>

definition Rset where "Rset = { (c,a)| c a. set c = a}"
                                     
lemma "RETURNT [1,2,3] \<le> \<Down>Rset (RETURNT {1,2,3})"
  unfolding conc_fun_def RETURNT_def Rset_def
  apply simp unfolding le_fun_def by auto

lemma "RETURNT [1,2,3] \<le> \<Down>Rset (RETURNT {1,2,3})"
  unfolding conc_fun_def RETURNT_def Rset_def
  apply simp unfolding le_fun_def by auto


definition Reven where "Reven = { (c,a)| c a. even c = a}"

lemma "RETURNT 3 \<le> \<Down>Reven (RETURNT False)"
  unfolding conc_fun_def RETURNT_def Reven_def
  apply simp unfolding le_fun_def by auto

lemma "m \<le> \<Down>Id m"
  unfolding conc_fun_def RETURNT_def 
  apply (cases m) by auto


lemma "m \<le> \<Down>{} m \<longleftrightarrow> (m=FAILT \<or> m = SPECT bot)"
  unfolding conc_fun_def RETURNT_def 
  apply (cases m) apply auto by (metis bot.extremum dual_order.antisym le_funI)


lemma abs_fun_simps[simp]: 
  "\<Up>R FAILT = FAILT"
  "dom X\<subseteq>Domain R \<Longrightarrow> \<Up>R (REST X) = REST (\<lambda>a. Sup {X c| c. (c,a)\<in>R})"
  "\<not>(dom X\<subseteq>Domain R) \<Longrightarrow> \<Up>R (REST X) = FAILT"
  unfolding abs_fun_def by (auto  split: nrest.split)

term single_valued
 
context fixes R assumes SV: "single_valued R" begin


lemma 
  fixes m :: "'b \<Rightarrow> enat option"
  shows
  Sup_sv: "(c, a') \<in> R \<Longrightarrow>  Sup {m a| a. (c,a) \<in> R} = m a'"
proof -
  assume "(c,a') \<in> R"
  with SV have singleton: "{m a| a. (c,a) \<in> R} = {m a'}" by(auto dest: single_valuedD) 
  show ?thesis unfolding singleton by simp
qed 

lemma indomD: " M c = Some y \<Longrightarrow> dom M \<subseteq> Domain R \<Longrightarrow> (\<exists>a. (c,a)\<in>R)"
  by auto
(*
lemma conc_abs_swap: "m' \<le> \<Down>R m \<longleftrightarrow> \<Up>R m' \<le> m"
  apply rule
  subgoal (* <-- *)
  unfolding conc_fun_def abs_fun_def using SV
  apply (auto split: nrest.splits) 
  subgoal for M M'
    apply (auto simp add: le_fun_def)  
    sorry (* by (smt Sup_least antisym le_cases mem_Collect_eq single_valuedD)  *)
  subgoal 
    by (smt Collect_cong Domain.DomainI domI domIff empty_Sup empty_def le_map_dom_mono set_rev_mp)    
  done

  subgoal (* \<longrightarrow> *)
    unfolding conc_fun_def abs_fun_def using SV
    apply(auto split: nrest.splits if_splits)
    apply (auto simp add: le_fun_def)
    subgoal for M M' c
      apply(cases "M c = None")
       apply auto apply(frule indomD) apply simp
      apply(auto) sorry(*
      apply(simp only: Sup_sv)
       
      by (me tis (mono_tags, lifting) Sup_le_iff mem_Collect_eq) *)
    done
  done

lemma 
  fixes m :: "'b \<Rightarrow> enat option"
  shows
  Inf_sv: "(c, a') \<in> R \<Longrightarrow>  Inf {m a| a. (c,a) \<in> R} = m a'"
proof -
  assume "(c,a') \<in> R"
  with SV have singleton: "{m a| a. (c,a) \<in> R} = {m a'}" by(auto dest: single_valuedD) 
  show ?thesis unfolding singleton by simp
qed 

lemma ac_galois: "galois_connection (\<Up>R) (\<Down>R)"
  apply (unfold_locales)
  by (rule conc_abs_swap)
*)

lemma 
  fixes m :: "'b \<Rightarrow> enat option"
  shows 
  Sup_some_svD: "Sup {m a |a. (c, a) \<in> R} = Some t' \<Longrightarrow> (\<exists>a. (c,a)\<in>R \<and> m a = Some t')"
  using SV by (smt Sup_le_iff dual_order.antisym less_eq_option_Some_None mem_Collect_eq order_refl single_valued_def)
 

end 


lemma pw_abs_nofail[refine_pw_simps]: 
  "nofailT (\<Up>R M) \<longleftrightarrow> (nofailT M \<and> (\<forall>x. (\<exists>t. inresT M x t) \<longrightarrow> x\<in>Domain R))"
  apply (cases M)
  apply simp
  apply (auto simp: abs_fun_simps abs_fun_def)
  by (metis zero_enat_def zero_le)



(*
lemma pw_abs_inre: 
  "inresT (\<Up>R M) a t \<longleftrightarrow> (nofailT (\<Up>R M) \<longrightarrow> (\<exists>c. inresT M c t \<and> (c,a)\<in>R))"
  apply (cases M)
  apply simp
  apply (auto simp: abs_fun_def)
  done*)

(*
lemma pw_conc_inres:
  "inresT (\<Down>R S') s t = (nofailT S' 
  \<longrightarrow> (\<exists>s'. (s,s')\<in>R \<and> inresT S' s' t))"
  apply (cases S')
  subgoal by simp
  subgoal  for m'
    apply rule
    subgoal 
      apply (auto simp: conc_fun_RES) sorry
    subgoal 
      apply (auto simp: conc_fun_RES) sorry
    done
  oops *)

lemma sv_the: "single_valued R \<Longrightarrow> (c,a) \<in> R \<Longrightarrow> (THE a. (c, a) \<in> R) = a"
  by (simp add: single_valued_def the_equality)

lemma conc_fun_RES_sv:
  fixes X :: "'b \<Rightarrow> enat option"
  assumes SV: "single_valued R"
  shows "\<Down>R (REST X) = REST (\<lambda>c. if c\<in>Domain R then X (THE a. (c,a)\<in>R) else None )"
  unfolding conc_fun_def
  apply(auto split: nrest.split)
  apply(rule ext)
  apply auto
  subgoal using  SV  by (auto simp: Sup_sv sv_the)
  subgoal by (smt Collect_cong Domain.DomainI empty_Sup empty_def)
  done

lemma conc_fun_mono[simp, intro!]: 
  shows "mono ((\<Down>R)::('b, enat) nrest \<Rightarrow> ('a, enat) nrest)"
  apply rule 
  apply (simp add: pw_le_iff)
  by (auto simp: refine_pw_simps) 


lemma conc_fun_R_mono:
  fixes M :: "(_,enat) nrest"
  assumes "R \<subseteq> R'" 
  shows "\<Down>R M \<le> \<Down>R' M"
  using assms
  by (auto simp: pw_le_iff refine_pw_simps)


lemma conc_fun_chain:
  fixes M :: "(_,enat) nrest"
  shows "\<Down>R (\<Down>S M) = \<Down>(R O S) M"
  apply(cases M)
  subgoal by simp
  apply simp
  apply(simp only: conc_fun_RES)
  apply auto apply (rule ext)  unfolding SupSup_1 SupSup_2 by meson 


lemma conc_fun_complete_lattice_chain:
  fixes M :: "(_,'b::complete_lattice) nrest"
  shows "\<Down>R (\<Down>S M) = \<Down>(R O S) M"
  apply(cases M)
  subgoal by simp
  apply simp
  apply(simp only: conc_fun_RES)
  apply auto apply (rule ext)  unfolding SupSup_1 SupSup_2 by meson 


lemma conc_fun_chain_sv:
  fixes M :: "(_,enat) nrest"
  assumes SVR: "single_valued R" and SVS: "single_valued S"
  shows "\<Down>R (\<Down>S M) = \<Down>(R O S) M"
  apply(cases M)
  subgoal by simp
  apply simp
  using SVS apply(simp only: conc_fun_RES_sv)
  using SVR apply(simp only: conc_fun_RES_sv)
  using single_valued_relcomp[OF SVR SVS] apply(simp only: conc_fun_RES_sv)
  apply (auto split: nrest.split)
  apply (rule ext) apply auto
    apply(auto simp add: sv_the)  
  apply(subst sv_the) by auto


lemma conc_Id[simp]: "\<Down>Id = id"
  unfolding conc_fun_def [abs_def] by (auto split: nrest.split)

                                 
lemma conc_fun_fail_iff[simp]: 
  fixes S :: "(_,enat) nrest"
  shows
  "\<Down>R S = FAILT \<longleftrightarrow> S=FAILT"
  "FAILT = \<Down>R S \<longleftrightarrow> S=FAILT"
  by (auto simp add: pw_eq_iff refine_pw_simps)


lemma conc_trans[trans]:
  fixes B :: "(_,'a::complete_lattice) nrest"
  assumes A: "C \<le> \<Down>R B" and B: "B \<le> \<Down>R' A" 
  shows "C \<le> \<Down>R (\<Down>R' A)"
  apply(rule order.trans)
  apply(rule A)
  apply(rule nrest_Rel_mono)    
  apply(rule B)
  done 
(*
lemma conc_trans[trans]:
  fixes B :: "(_,enat) nrest"
  assumes A: "C \<le> \<Down>R B" and B: "B \<le> \<Down>R' A" 
  shows "C \<le> \<Down>R (\<Down>R' A)"
  using assms by (fastforce simp: pw_le_iff refine_pw_simps)

lemma conc_acost_trans[trans]:
  fixes B :: "(_,(_,enat) acost) nrest"
  assumes A: "C \<le> \<Down>R B" and B: "B \<le> \<Down>R' A" 
  shows "C \<le> \<Down>R (\<Down>R' A)"
  using assms by (fastforce simp: pw_acost_le_iff refine_pw_simps)
*)

lemma conc_trans_sv:
  fixes B :: "(_,enat) nrest"
  assumes SV: "single_valued R" "single_valued R'"
    and A: "C \<le> \<Down>R B" and B: "B \<le> \<Down>R' A" 
  shows "C \<le> \<Down>R (\<Down>R' A)"
  using assms by (fastforce simp: pw_le_iff refine_pw_simps)

text \<open>WARNING: The order of the single statements is important here!\<close>
lemma conc_trans_additional[trans]: 
  assumes "single_valued R"
  shows
  "\<And>(A::(_,enat) nrest) B C. A\<le>\<Down>R  B \<Longrightarrow> B\<le>    C \<Longrightarrow> A\<le>\<Down>R  C"
  "\<And>(A::(_,enat) nrest) B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>\<Down>R  C \<Longrightarrow> A\<le>\<Down>R  C"
  "\<And>(A::(_,enat) nrest) B C. A\<le>\<Down>R  B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>\<Down>R  C"

  "\<And>(A::(_,enat) nrest) B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>    C"
  "\<And>(A::(_,enat) nrest) B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>    C \<Longrightarrow> A\<le>    C"
  "\<And>(A::(_,enat) nrest) B C. A\<le>    B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>    C"
  using assms conc_trans[where R=R and R'=Id]
  by (auto intro: order_trans)



lemma RETURNT_refine:
  assumes "(x,x')\<in>R"
  shows "RETURNT x \<le> \<Down>R (RETURNT x')"
  using assms
  by (auto simp: RETURNT_def conc_fun_RES le_fun_def Sup_upper)  

(*
thm bindT_refine'
lemma bindT_refine'2:
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x' t . \<lbrakk> (x,x')\<in>R'; inresT M x t; inresT M' x' t;
    nofailT M; nofailT M'
  \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bindT M (\<lambda>x. f x) \<le> \<Down> R (bindT M' (\<lambda>x'. f' x'))"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)  
  by blast*)

lemma bindT_refine:
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set" and M :: "(_,enat) nrest"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x'. \<lbrakk> (x,x')\<in>R' \<rbrakk> 
    \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bindT M (\<lambda>x. f x) \<le> \<Down> R (bind M' (\<lambda>x'. f' x'))"
  apply (rule bindT_conc_refine') using assms by auto

subsection \<open>WHILET refine\<close>

lemma RECT_refine:
  assumes M: "mono2 body"
  assumes R0: "(x,x')\<in>R"
  assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le>\<Down>S (f' x'); (x,x')\<in>R \<rbrakk> 
    \<Longrightarrow> body f x \<le>\<Down>S (body' f' x')"
  shows "RECT (\<lambda>f x. body f x) x \<le>\<Down>S (RECT (\<lambda>f' x'. body' f' x') x')"
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

                                         
lemma WHILET_refine:
  fixes f :: "_ \<Rightarrow> (_,enat) nrest"
  assumes R0: "(x,x')\<in>R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "whileT b f x \<le> \<Down>R (whileT b' f' x')"
  unfolding whileT_def apply(rule RECT_refine)
    subgoal by(refine_mono)  
     apply (fact R0)
    by(auto simp: COND_REF STEP_REF RETURNT_refine intro: bindT_refine[where R'=R])  

lemma 
  assumes a: "\<And>m n c a. c\<in>Domain R \<Longrightarrow> \<exists>a. SPECT (n c) \<le>  SPECT (m a)"
  shows "(SPECT n) \<le> \<Down> R (SPECT m)"
  using a  apply auto  
    unfolding conc_fun_def apply (auto split: nrest.split) 
      unfolding le_fun_def apply auto
    proof -
      fix c 
      assume "(\<And>c n m. c \<in> Domain R \<Longrightarrow> \<exists>a. \<forall>x. n c x \<le> m a x)"
      oops

lemma SPECT_refines_conc_fun':
  assumes a: "\<And>m c.  M = SPECT m
          \<Longrightarrow> c \<in> dom n \<Longrightarrow> (\<exists>a. (c,a)\<in>R \<and> n c \<le> m a)"
  shows "SPECT n \<le> \<Down> R M"
proof - 
  show ?thesis
    unfolding conc_fun_def apply (auto split: nrest.split) 
    subgoal for m unfolding le_fun_def apply auto
    proof -
      fix c
      assume m: "M = SPECT m"
      show "n c \<le> Sup {m a |a. (c, a) \<in> R} "
      proof (cases "c \<in> dom n")
        case True
        with m a obtain a where k: "(c,a)\<in>R" "n c \<le> m a" by blast 
        show ?thesis apply(rule  Sup_upper2) using k by auto
      next
        case False
        then show ?thesis 
          by (simp add: domIff)
      qed 
    qed
    done
qed

lemma SPECT_refines_conc_fun:
  assumes a: "\<And>m c. (\<exists>a. (c,a)\<in>R \<and> n c \<le> m a)"
  shows "SPECT n \<le> \<Down> R (SPECT m)"
  apply(rule SPECT_refines_conc_fun') using a by auto


lemma SPECT_refines_conc_fun_sv:
  assumes "single_valued R" 
    and a: "dom n \<subseteq> Domain R"
    and "\<And>c. c \<in> dom n \<Longrightarrow> n c \<le> (THE a. (c,a)\<in>R)"
  shows "SPECT n \<le> \<Down> R (SPECT m)"
  apply(rule SPECT_refines_conc_fun') using a
  using indomD[OF assms(1) _ a] domIff
  oops




lemma conc_fun_br: "\<Down> (br \<alpha> I1) (SPECT (emb I2 t))
        = (SPECT (emb (\<lambda>x. I1 x \<and> I2 (\<alpha> x)) t))"
  unfolding conc_fun_RES  apply auto apply(rule ext)    
      by (auto simp: emb'_def br_def bot_option_def Sup_option_def) 


subsection \<open>Relators\<close>


definition nrest_rel where 
  nrest_rel_def_internal: "nrest_rel R \<equiv> {(c,a).  c \<le> \<Down>R  a}"

lemma nrest_rel_def: "\<langle>R\<rangle>nrest_rel \<equiv> {(c,a). c \<le> \<Down>R  a}"
  by (simp add: nrest_rel_def_internal relAPP_def)

lemma nrest_relD: "(c,a)\<in>\<langle>R\<rangle>nrest_rel \<Longrightarrow> c \<le> \<Down>R  a" by (simp add: nrest_rel_def)
lemma nrest_relI: "c \<le>\<Down>R a \<Longrightarrow> (c,a)\<in>\<langle>R\<rangle>nrest_rel" by (simp add: nrest_rel_def)


lemma nrest_rel_comp: 
 "\<langle>A\<rangle>nrest_rel O \<langle>B\<rangle>nrest_rel = \<langle>A O B\<rangle>nrest_rel"
  by (auto simp: nrest_rel_def conc_fun_complete_lattice_chain[symmetric] conc_trans)

lemma pw_nrest_rel_iff: "(a,b)\<in>\<langle>A\<rangle>nrest_rel \<longleftrightarrow> nofailT (\<Down> A b)\<longrightarrow>  nofailT a \<and> (\<forall>x t. inresT a x t \<longrightarrow> inresT (\<Down> A b) x t)"
  by (simp add: pw_le_iff nrest_rel_def)

find_theorems project_acost abs_fun

lemma pw_acost_nrest_rel_iff: "(a,b)\<in>\<langle>A\<rangle>nrest_rel \<longleftrightarrow> nofailT (\<Down> A b) \<longrightarrow> nofailT a
         \<and> (\<forall>x c t. inresT (project_acost c a) x t \<longrightarrow> inresT (\<Down> A (project_acost c b)) x t)"
  by (auto simp add: pw_acost_le_iff nrest_rel_def project_acost_conc_fun_commute)


lemma param_RETURNT[param]: 
  "(RETURNT,RETURNT) \<in> R \<rightarrow> \<langle>R\<rangle>nrest_rel"
  by (auto simp: nrest_rel_def RETURNT_refine)

end