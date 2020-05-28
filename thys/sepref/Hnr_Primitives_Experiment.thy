theory Hnr_Primitives_Experiment
imports Sepref_Basic "../ds/LLVM_DS_Dflt"
begin
  hide_const (open) LLVM_DS_Array.array_assn

  subsubsection \<open>Composition\<close>
  definition hr_comp :: "('b \<Rightarrow> 'c \<Rightarrow> assn) \<Rightarrow> ('b \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> assn"
    \<comment> \<open>Compose refinement assertion with refinement relation\<close>
    where "hr_comp R1 R2 a c \<equiv> EXS b. R1 b c ** \<up>((b,a)\<in>R2)"

  lemma hr_compI: "(b,a)\<in>R2 \<Longrightarrow> R1 b c \<turnstile> hr_comp R1 R2 a c"  
    unfolding hr_comp_def
    by (auto simp: sep_algebra_simps entails_def pred_lift_extract_simps)

  lemma hr_comp_Id1[simp]: "hr_comp (pure Id) R = pure R"  
    unfolding hr_comp_def[abs_def] pure_def
    apply (intro ext)
    by (auto simp: pred_lift_extract_simps)

  lemma hr_comp_Id2[simp]: "hr_comp R Id = R"  
    unfolding hr_comp_def[abs_def]
    apply (intro ext)
    by (auto simp: sep_algebra_simps pred_lift_extract_simps)
    
  lemma hr_comp_emp[simp]: "hr_comp (\<lambda>a c. \<box>) R a c = \<up>(\<exists>b. (b,a)\<in>R)"
    unfolding hr_comp_def[abs_def]
    apply (intro ext)
    by (auto simp: sep_algebra_simps pred_lift_extract_simps)

  lemma hr_comp_prod_conv[simp]:
    "hr_comp (prod_assn Ra Rb) (Ra' \<times>\<^sub>r Rb') 
    = prod_assn (hr_comp Ra Ra') (hr_comp Rb Rb')"  
    unfolding hr_comp_def[abs_def] prod_assn_def[abs_def]
    apply (intro ext)
    apply (auto 0 3 simp: sep_algebra_simps pred_lift_extract_simps)
    done

  lemma hr_comp_pure: "hr_comp (pure R) S = pure (R O S)"  
    apply (intro ext)
    unfolding hr_comp_def[abs_def] pure_def
    by (auto simp: sep_algebra_simps pred_lift_extract_simps)

  lemma hr_comp_is_pure: "is_pure A \<Longrightarrow> is_pure (hr_comp A B)"
    by (auto simp: hr_comp_pure is_pure_conv)

  lemma hr_comp_the_pure: "is_pure A \<Longrightarrow> the_pure (hr_comp A B) = the_pure A O B"
    unfolding is_pure_conv
    by (clarsimp simp: hr_comp_pure)

  lemma rdomp_hrcomp_conv[simp]: "rdomp (hr_comp A R) x \<longleftrightarrow> (\<exists>y. rdomp A y \<and> (y,x)\<in>R)"
    by (auto simp: rdomp_def hr_comp_def sep_algebra_simps pred_lift_extract_simps)

  lemma hr_comp_assoc: "hr_comp (hr_comp R S) T = hr_comp R (S O T)"
    apply (intro ext)
    unfolding hr_comp_def
    by (auto simp: sep_algebra_simps pred_lift_extract_simps)


lemma conc_fun_spec_ne_FAIL[simp]: "\<Down>R (SPECT M) \<noteq> FAILT" by (simp add: conc_fun_RES)   
    
(*lemma project_acost_conc_fun[refine_pw_simps]: "project_acost b (\<Down>R m) = \<Down>R (project_acost b m)" sorry*)


lemma aux_abs_help:
  fixes M :: "_ \<rightharpoonup> ecost" 
  assumes "\<Up> RR (SPECT M) \<le>  (SPECT M')"
  shows "\<forall>r\<in>dom M. (\<exists>r'. (r,r')\<in>RR) \<and> (\<forall>r'. (r,r')\<in>RR \<longrightarrow> M r \<le> M' r')"
  using assms
  (* with single_valued RR *)
  apply (auto simp: abs_fun_RES split: if_splits simp: le_fun_def) 
  subgoal premises prems for r y r'
    using prems(2)[rule_format, of r'] prems(3,4)  
    by (metis (mono_tags, lifting) Sup_le_iff mem_Collect_eq)  
  done

lemma aux_abs:
  fixes M :: "_ \<rightharpoonup> ecost" 
  assumes "\<Up> RR (SPECT M) \<le>  (SPECT M')"
  shows "\<forall>r\<in>dom M. \<exists>r'. (r,r')\<in>RR \<and> M r \<le> M' r'"
  using aux_abs_help[OF assms] by blast

lemma aux_abs':
  fixes M :: "_ \<rightharpoonup> ecost" 
  assumes "\<Up> RR (SPECT M) \<le> (SPECT M')"
  assumes "Some cr \<le> M r"
  shows "\<exists>r'. (r,r')\<in>RR \<and> M r \<le> M' r'"
  using assms aux_abs[of RR M M']
  by fastforce




lemma aux:
  fixes M :: "_ \<rightharpoonup> ecost"
  assumes "single_valued RR"
  assumes "SPECT M \<le> \<Down> RR (SPECT M')"
  shows "\<forall>r\<in>dom M. \<exists>r'. (r,r')\<in>RR \<and> M r \<le> M' r'"
  using assms
  (* with single_valued RR *)
  apply (auto simp: conc_fun_RES)
  by (smt Sup_Some cSup_eq_maximum dual_order.refl le_fun_def le_some_optE mem_Collect_eq sv_the)
  
lemma aux':
  fixes M :: "_ \<rightharpoonup> ecost"
  assumes "single_valued RR"
  assumes "SPECT M \<le> \<Down> RR (SPECT M')"
  assumes "Some cr \<le> M r"
  shows "\<exists>r'. (r,r')\<in>RR \<and> M r \<le> M' r'"
  using assms aux[of RR M M']
  by fastforce
  
  lemma hn_refine_result':
  assumes R: "hn_refine P c Q R m"
  assumes LE: "\<Up>RR m\<le>m'" 
  shows "hn_refine P c Q (hr_comp R RR) m'"
  unfolding hn_refine_def
  apply clarify
  using LE apply (cases m; simp)
  apply (frule (1) R[unfolded hn_refine_def, rule_format, rotated], simp)
  apply (elim exE conjE)
  apply (drule (1) aux_abs')
  apply (elim exE conjE)
  
  apply (intro exI conjI)
  apply (rule order_trans, assumption+)  

  apply (erule wp_post_cons)
  unfolding hr_comp_def
  apply (rule ENTAILSD)
  apply fri
  done

lemma SomeSup_D: "Some y \<le> Sup {M' a |a. (r, a) \<in> RR} \<Longrightarrow> (\<exists>a. (r, a) \<in> RR)"
  unfolding Sup_option_def by (auto split: if_splits)

lemma aux_loose:
  fixes M :: "_ \<rightharpoonup> ecost"
  assumes "\<And>r. r\<in>dom M \<Longrightarrow> (\<exists>a. (r,a)\<in>RR) \<Longrightarrow> Sup {M' a| a. (r,a)\<in>RR} \<in> {M' a| a. (r,a)\<in>RR}"
  assumes "SPECT M \<le> \<Down> RR (SPECT M')"
  shows "\<forall>r\<in>dom M. \<exists>r'. (r,r')\<in>RR \<and> M r \<le> M' r'"
  using assms
  (* with single_valued RR *)
  apply (auto simp: conc_fun_RES)
  unfolding le_fun_def 
  subgoal premises p for r y using p(2)[rule_format, of r] p(1)[of r, OF _ SomeSup_D] p(3)
    by force
  done

lemma aux_loose':
  fixes M :: "_ \<rightharpoonup> ecost"
  assumes "\<And>r. r\<in>dom M \<Longrightarrow> (\<exists>a. (r,a)\<in>RR) \<Longrightarrow> Sup {M' a| a. (r,a)\<in>RR} \<in> {M' a| a. (r,a)\<in>RR}"
  assumes "SPECT M \<le> \<Down> RR (SPECT M')"
  assumes "Some cr \<le> M r"
  shows "\<exists>r'. (r,r')\<in>RR \<and> M r \<le> M' r'"
  using assms aux_loose[of M RR M']
  by fastforce


lemma single_valued_SupinSup:
  fixes M' :: "_ \<Rightarrow> (_::complete_lattice) option"
  shows "single_valued RR \<Longrightarrow> (\<exists>a. (r,a)\<in>RR) \<Longrightarrow> Sup {M' a| a. (r,a)\<in>RR} \<in> {M' a| a. (r,a)\<in>RR}"
proof -
  assume SV: "single_valued RR" and "(\<exists>a. (r,a)\<in>RR)"
  then obtain a where "(r,a)\<in>RR" by auto
  then have "{M' a| a. (r,a)\<in>RR} = {M' a}"
    apply auto using SV[THEN single_valuedD] by auto
  then show ?thesis by auto
qed
  

lemma conc_fun_inRR: "SPECT x2 \<le> \<Down> RR (SPECT M) \<Longrightarrow> r \<in> dom x2 \<Longrightarrow> (\<exists>a. (r,a)\<in>RR)"
  unfolding conc_fun_def apply auto unfolding le_fun_def 
  subgoal premises p for y apply(rule SomeSup_D)
    using p(1)[rule_format, of r] p(2) by simp
  done

lemma domx2:
  fixes f :: "'d \<Rightarrow> (char list, enat) acost option"
  shows "Some y \<le> f r \<Longrightarrow> r \<in> dom f"  
  using ndomIff by fastforce

  
definition "attains_sup m m' RR \<equiv> 
  \<forall>r M' M. m=SPECT M \<longrightarrow> m'=SPECT M' \<longrightarrow> r\<in>dom M \<longrightarrow> (\<exists>a. (r,a)\<in>RR) \<longrightarrow> Sup {M' a| a. (r,a)\<in>RR} \<in> {M' a| a. (r,a)\<in>RR}"  

lemma sv_attains_sup: "single_valued RR \<Longrightarrow> attains_sup m m' RR"  
  unfolding attains_sup_def
  using single_valued_SupinSup by fastforce  
  
lemma hn_refine_result_loose:
  assumes R: "hn_refine P c Q R m"
  assumes LE: "m\<le>\<Down>RR m'"
  assumes WB: "attains_sup m m' RR"
  shows "hn_refine P c Q (hr_comp R RR) m'"
  supply WB' = WB[unfolded attains_sup_def, rule_format]
  unfolding hn_refine_def
  apply clarify
  using LE apply (cases m; simp)
  apply (frule (1) R[unfolded hn_refine_def, rule_format, rotated], simp)
  apply (elim exE conjE)
  subgoal premises p for F s cr M x2 ra Ca
    using aux_loose'[OF WB'[OF p(4,1)], simplified, OF _ p(3,5), simplified] p(5,6)
    apply -
    apply (elim exE conjE)

    apply (intro exI conjI)
     apply (rule order_trans, assumption+)  

    apply (erule wp_post_cons)
    unfolding hr_comp_def
    apply (rule ENTAILSD)
    apply fri
    done
  done


lemma hn_refine_result_loose_SV:
  assumes R: "hn_refine P c Q R m"
  assumes LE: "m\<le>\<Down>RR m'"
  assumes SV: "single_valued RR"
  shows "hn_refine P c Q (hr_comp R RR) m'"
  apply(rule hn_refine_result_loose)
    apply fact
   apply fact
  apply(rule sv_attains_sup)
   apply (rule SV)
  done


lemma hn_refine_result:
  assumes R: "hn_refine P c Q R m"
  assumes LE: "m\<le>\<Down>RR m'"
  assumes SV: "single_valued RR"
  shows "hn_refine P c Q (hr_comp R RR) m'"
  unfolding hn_refine_def
  apply clarify
  using LE apply (cases m; simp)
  apply (frule (1) R[unfolded hn_refine_def, rule_format, rotated], simp)
  apply (elim exE conjE)
  apply (drule (1) aux'[OF SV])
  apply (elim exE conjE)
  
  apply (intro exI conjI)
  apply (rule order_trans, assumption+)  

  apply (erule wp_post_cons)
  unfolding hr_comp_def
  apply (rule ENTAILSD)
  apply fri
  done
    
lemma hn_refine_cons_res_complete:
  assumes R: "hn_refine P' c Q R m"
  assumes I: "P\<turnstile>P'"
  assumes I': "Q\<turnstile>Q'"
  assumes R': "\<And>x y. R x y \<turnstile> R' x y"
  assumes LE: "m\<le>\<Down>RR m'"
  assumes SV: "single_valued RR"
  shows "hn_refine P c Q' (hr_comp R RR) m'"
  apply (rule hn_refine_result)
  apply (rule hn_refine_cons)
  by (fact|simp)+

lemma hn_refine_cons_res_complete_loose:
  assumes R: "hn_refine P' c Q R m"
  assumes I: "P\<turnstile>P'"
  assumes I': "Q\<turnstile>Q'"
  assumes R': "\<And>x y. R x y \<turnstile> R' x y"
  assumes LE: "m\<le>\<Down>RR m'"
  assumes AS: "attains_sup m m' RR"
  shows "hn_refine P c Q' (hr_comp R RR) m'"
  apply (rule hn_refine_result_loose)
  apply (rule hn_refine_cons)
  by (fact|simp)+
  
  
  
  
  
  
  
  
    

  abbreviation "raw_array_assn \<equiv> \<upharpoonleft>LLVM_DS_NArray.narray_assn"

lemma satminus_lift_acost: "satminus ta (the_acost (lift_acost t) b) = 0 \<longleftrightarrow> ta \<le> the_acost t b"
  unfolding satminus_def lift_acost_def by auto

term lift_acost
lemma hnr_SPECT_D:
  fixes \<Phi> :: "_ \<Rightarrow> ((_,enat) acost) option"
  shows
      "do { ASSERT P; consume (RETURNT x) (lift_acost t) } = SPECT \<Phi>
      \<Longrightarrow> P \<and> Some (lift_acost t) \<le> \<Phi> x"
  apply(simp add: pw_acost_eq_iff)
  apply(simp add: refine_pw_simps)
  apply(auto simp: satminus_lift_acost)
  apply(cases "\<Phi> x")
  subgoal    
    by force  
  subgoal  premises prems for e
    apply(rule acost_componentwise_leI[where e=e] )
    subgoal using prems by simp  
    subgoal for b
      using prems(2)[rule_format, where x=x and t="the_acost t b" and b=b]
      using prems(3)      
      by (auto simp: lift_acost_def)
    done
  done

lemma lift_acost_plus_distrib[named_ss fri_prepare_simps]:
  "$lift_acost (a + b) = ($lift_acost a ** $lift_acost b)"
  unfolding time_credits_assn_def lift_acost_def SND_def EXACT_def
  apply (cases a; cases b)
  apply (auto simp add: sep_algebra_simps fun_eq_iff sep_conj_def sep_disj_acost_def sep_disj_enat_def)
  done

abbreviation "id_assn \<equiv> pure Id"  
abbreviation "snat_assn \<equiv> \<upharpoonleft>snat.assn"
 
lemma DECOMP_HNR[vcg_decomp_rules]: "DECOMP_HTRIPLE (hn_refine \<Gamma> c \<Gamma>' R a) \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R a" by (simp add: vcg_tag_defs)

lemma hn_refine_pre_pureI:
  assumes "pure_part \<Gamma> \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R a"
  shows "hn_refine \<Gamma> c \<Gamma>' R a"
  using assms unfolding hn_refine_def
  apply auto
  using prep_ext_state pure_part_split_conj by blast


lemma hnr_mop_vcgI[htriple_vcg_intros]: 
  assumes "\<And>F s cr. \<lbrakk>\<Phi>; pure_part \<Gamma>; llSTATE (\<Gamma>**F**$(lift_acost t)) (s,cr+(lift_acost t))\<rbrakk> \<Longrightarrow> 
                     EXTRACT (wp c (\<lambda>ri. POSTCOND ll_\<alpha> (\<Gamma>' ** R r ri ** F ** GC)) (s,cr+lift_acost t))"
  shows "hn_refine \<Gamma> c \<Gamma>' R (do {ASSERT \<Phi>; consume (RETURNT r) (lift_acost t)})"  
  apply (rule hn_refine_pre_pureI)
  apply (rule hnr_vcgI)
  apply(drule hnr_SPECT_D, clarify)
  apply (rule exI[where x="r"])
  apply (rule exI[where x="t"])
  using assms by blast

lemmas hnr_mop_vcgI_nopre[htriple_vcg_intros] = hnr_mop_vcgI[where \<Phi>=True, simplified]  
  
abbreviation "cost'_narray_new n \<equiv> cost ''malloc'' n + cost ''free'' 1 + cost ''if'' 1 + cost ''if'' 1 + cost ''icmp_eq'' 1 + cost ''ptrcmp_eq'' 1"


definition "mop_array_nth xs i \<equiv> do { ASSERT (i<length xs); consume (RETURNT (xs!i)) (lift_acost (cost ''load'' (Suc 0)+cost ''ofs_ptr'' (Suc 0))) }"
definition "mop_array_upd xs i x \<equiv> do { ASSERT (i<length xs); consume (RETURNT (xs[i:=x])) (lift_acost (cost ''store'' (Suc 0)+cost ''ofs_ptr'' (Suc 0))) }"
definition "mop_array_new n x \<equiv> do { ASSERT (PROTECT True); consume (RETURNT (replicate n x)) (lift_acost (cost'_narray_new n)) }"


lemma hnr_raw_array_nth: "hn_refine 
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn i ii)
  (array_nth xsi ii)
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn i ii)
  id_assn
  (mop_array_nth xs i)" 
  unfolding hn_ctxt_def pure_def mop_array_nth_def
  by vcg

lemma hnr_raw_array_upd: "hn_refine 
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn i ii ** hn_ctxt id_assn x xi)
  (array_upd xsi ii xi)
  (hn_invalid raw_array_assn xs xsi ** hn_ctxt snat_assn i ii  ** hn_ctxt id_assn x xi)
  raw_array_assn
  (mop_array_upd xs i x)" 
  unfolding hn_ctxt_def pure_def invalid_assn_def mop_array_upd_def
  by vcg
  
  

lemma hnr_raw_array_new: "hn_refine 
  (hn_ctxt snat_assn i ii)
  (narray_new TYPE('a::llvm_rep) ii)
  (hn_ctxt snat_assn i ii)
  raw_array_assn
  (mop_array_new i init)" 
  unfolding hn_ctxt_def pure_def invalid_assn_def mop_array_new_def
  by vcg
  
lemma FREE_raw_array_assn: "MK_FREE raw_array_assn narray_free"  
  apply rule
  by vcg


  
  
  
  
text \<open>Assertion that adds constraint on concrete value. Used to carry through concrete equalities.\<close>
definition "cnc_assn \<phi> A a c \<equiv> \<up>(\<phi> c) ** A a c"
  
lemma norm_ceq_assn(*[named_ss sepref_frame_normrel]*): "hn_ctxt (cnc_assn \<phi> A) a c = (\<up>(\<phi> c) ** hn_ctxt A a c)"
  unfolding hn_ctxt_def cnc_assn_def by simp
  

definition "mop_oarray_nth xs i \<equiv> do { ASSERT (i<length xs \<and> xs!i\<noteq>None); consume (RETURNT (the (xs!i), xs[i:=None])) (lift_acost (cost ''load'' (Suc 0)+cost ''ofs_ptr'' (Suc 0))) }"
definition "mop_oarray_upd xs i x \<equiv> do { ASSERT (i<length xs \<and> xs!i=None); consume (RETURNT (xs[i:=Some x])) (lift_acost (cost ''store'' (Suc 0)+cost ''ofs_ptr'' (Suc 0))) }"
definition "mop_oarray_new n \<equiv> consume (RETURNT (replicate n None)) (lift_acost (cost'_narray_new n))"

      
  
definition "eoarray_assn A \<equiv> \<upharpoonleft>(nao_assn (mk_assn A))"

definition "eoarray_nth_impl xsi ii \<equiv> doM {
  r \<leftarrow> array_nth xsi ii;
  return (r,xsi)
}"  
  
lemma hnr_eoarray_nth: "hn_refine 
  (hn_ctxt (eoarray_assn A) xs xsi ** hn_ctxt snat_assn i ii)
  (eoarray_nth_impl xsi ii)
  (hn_invalid (eoarray_assn A) xs xsi ** hn_ctxt snat_assn i ii)
  (cnc_assn (\<lambda>(_,xsi'). xsi'=xsi) (A \<times>\<^sub>a eoarray_assn A))
  (mop_oarray_nth xs i)"  
  unfolding hn_ctxt_def pure_def invalid_assn_def cnc_assn_def eoarray_assn_def mop_oarray_nth_def eoarray_nth_impl_def
  by vcg
  
lemma hnr_eoarray_upd: "hn_refine 
  (hn_ctxt (eoarray_assn A) xs xsi ** hn_ctxt snat_assn i ii ** hn_ctxt A x xi)
  (array_upd xsi ii xi)
  (hn_invalid (eoarray_assn A) xs xsi ** hn_ctxt snat_assn i ii ** hn_invalid A x xi)
  (cnc_assn (\<lambda>ri. ri=xsi) (eoarray_assn A))
  (mop_oarray_upd xs i x)"  
  unfolding hn_ctxt_def pure_def invalid_assn_def cnc_assn_def eoarray_assn_def mop_oarray_upd_def
  by vcg
  
lemma hnr_eoarray_new: "hn_refine 
  (hn_ctxt snat_assn i ii)
  (narrayo_new TYPE('a::llvm_rep) ii)
  (hn_ctxt snat_assn i ii)
  (eoarray_assn A)
  (mop_oarray_new i)" 
  unfolding hn_ctxt_def pure_def invalid_assn_def eoarray_assn_def mop_oarray_new_def
  by vcg
    
definition "mop_oarray_free xs \<equiv> do { ASSERT (set xs \<subseteq> {None}); consume (RETURNT ()) (lift_acost 0) }"
  
lemma hnr_eoarray_free: "hn_refine 
  (hn_ctxt (eoarray_assn A) xs xsi)
  (narray_free xsi)
  (hn_invalid (eoarray_assn A) xs xsi)
  (id_assn)
  (mop_oarray_free xs)"
  unfolding hn_ctxt_def pure_def invalid_assn_def eoarray_assn_def mop_oarray_free_def
  by vcg
  
  
(* Conversions between plain array and explicit ownership array*)  
definition "mop_to_eo_conv xs \<equiv> do { consume (RETURNT (map Some xs)) (lift_acost 0) }"  
definition "mop_to_wo_conv xs \<equiv> do { ASSERT (None\<notin>set xs); consume (RETURNT (map the xs)) (lift_acost 0) }"  

(* XXX: Need "array_assn A" first for this to be meaningful! ra-comp! *)  
  
definition "some_rel \<equiv> br the (Not o is_None)"
definition "array_assn A \<equiv> hr_comp (eoarray_assn A) (\<langle>some_rel\<rangle>list_rel)"

lemma map_the_some_rel_list_rel_iff: "(xs, map the xs) \<in> \<langle>some_rel\<rangle>list_rel \<longleftrightarrow> None \<notin> set xs"
  unfolding some_rel_def
  apply (auto simp: map_in_list_rel_conv split: option.splits)
  by (metis option.exhaust)

  
lemma map_in_list_rel_br_iff: "(map f xs, xs) \<in> \<langle>br \<alpha> I\<rangle>list_rel \<longleftrightarrow> (\<forall>x\<in>set xs. I (f x) \<and> \<alpha> (f x) = x)"  
  apply (induction xs)
  apply (auto simp: in_br_conv)
  done
  
lemma in_br_list_rel_conv: "(xs,ys) \<in> \<langle>br \<alpha> I\<rangle>list_rel \<longleftrightarrow> (\<forall>x\<in>set xs. I x) \<and> ys = map \<alpha> xs"  
  apply (rule)
  subgoal premises prems
    using prems
    apply (induction rule: list_rel_induct)
    by (auto simp: in_br_conv)
  subgoal by (auto simp: map_in_list_rel_conv)
  done
  
lemma in_some_rel_list_rel_conv: "(x,xi) \<in>\<langle>some_rel\<rangle>list_rel \<longleftrightarrow> x = map Some xi"
  unfolding some_rel_def
  by (auto simp: in_br_list_rel_conv map_idI split: option.splits)
  
  
(* Conversion between implicit and explicit ownership array *)
  
lemma hnr_to_wo_conv: "hn_refine 
  (hn_ctxt (eoarray_assn A) xs xsi)
  (return xsi)
  (hn_invalid (eoarray_assn A) xs xsi)
  (array_assn A)
  (mop_to_wo_conv xs)"
  unfolding hn_ctxt_def pure_def invalid_assn_def eoarray_assn_def mop_to_wo_conv_def
    array_assn_def hr_comp_def
  apply Basic_VCG.vcg'
  apply (simp add: map_the_some_rel_list_rel_iff)
  done

lemma hnr_to_eo_conv: "hn_refine 
  (hn_ctxt (array_assn A) xs xsi)
  (return xsi)
  (hn_invalid (array_assn A) xs xsi)
  (eoarray_assn A)
  (mop_to_eo_conv xs)"
  unfolding hn_ctxt_def pure_def invalid_assn_def eoarray_assn_def mop_to_eo_conv_def
    array_assn_def hr_comp_def
  supply [simp] = in_some_rel_list_rel_conv
  by vcg
  
(* Array operations for pure content, backed by eoarray *)  

lemma the_pure_pure_part_conv: "is_pure A \<Longrightarrow> the_pure A = {(c,a). pure_part (A a c)}"
  apply safe
  subgoal by (metis Sepref_Basic.pure_part_pure pure_the_pure)
  subgoal by (metis Sepref_Basic.pure_part_pure pure_the_pure)
  done

lemma is_pure_assn_pred_lift: "is_pure A \<Longrightarrow> A a c = \<up>((c,a)\<in>the_pure A)"
  by (metis Sepref_Basic.pure_def pure_the_pure)

lemma pure_list_assn_list_rel_conv: "is_pure A \<Longrightarrow> \<upharpoonleft>(list_assn (mk_assn A)) xs xsi = \<up>((xsi,xs)\<in>\<langle>the_pure A\<rangle>list_rel)"
proof (induction xs arbitrary: xsi)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case 
    apply (cases xsi; simp)
    by (auto simp add: sep_algebra_simps pred_lift_extract_simps fun_eq_iff is_pure_assn_pred_lift)
  
qed

definition [to_relAPP]: "oelem_rel A \<equiv> {(c,a) . case a of None \<Rightarrow> True | Some b \<Rightarrow> (c,b)\<in>A}"

lemma oelem_pure_assn_conv: "oelem_assn (mk_assn (pure A)) = mk_assn (pure (\<langle>A\<rangle>oelem_rel))"
  unfolding oelem_assn_def sel_mk_assn oelem_rel_def
  apply (rule arg_cong[where f=mk_assn])
  by (auto simp: fun_eq_iff pure_def sep_algebra_simps split: option.split )

  
lemma map_some_oelem_list_rel_conv: "(xs, map Some ys) \<in> \<langle>\<langle>R\<rangle>oelem_rel\<rangle>list_rel \<longleftrightarrow> (xs,ys) \<in> \<langle>R\<rangle>list_rel"  
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case 
    apply (cases ys)
    by (auto simp: oelem_rel_def)
    
qed


  
lemma pure_array_assn_alt:
  assumes "is_pure A"  
  shows "array_assn A = hr_comp raw_array_assn (\<langle>the_pure A\<rangle>list_rel)"  
  apply (rewrite pure_the_pure[of A, symmetric, OF assms])
  unfolding array_assn_def eoarray_assn_def nao_assn_def hr_comp_def
  apply (auto 
    simp: fun_eq_iff sep_algebra_simps pred_lift_extract_simps oelem_pure_assn_conv 
    simp: pure_list_assn_list_rel_conv in_some_rel_list_rel_conv map_some_oelem_list_rel_conv
  )
  done

(* TODO: Move *)  
lemma hn_ctxt_hr_comp_extract: "hn_ctxt (hr_comp A R) a c = (EXS b. \<up>((b,a)\<in>R) ** hn_ctxt A b c)"  
  unfolding hn_ctxt_def hr_comp_def
  by (simp add: sep_algebra_simps)

(* TODO: Move *)  
lemma invalid_hr_comp_ctxt: "hn_invalid (hr_comp A R) a c = hn_ctxt (hr_comp (invalid_assn A) R) a c"  
  unfolding invalid_assn_def hr_comp_def hn_ctxt_def
  by (auto simp: sep_algebra_simps fun_eq_iff pred_lift_extract_simps pure_part_def)
    
lemma hn_refine_extract_pre_ex: "hn_refine (EXS x. \<Gamma> x) c \<Gamma>' R a = (\<forall>x. hn_refine (\<Gamma> x) c \<Gamma>' R a)"  
  unfolding hn_refine_def
  by (auto simp: sep_algebra_simps STATE_extract; blast)
  
lemma hn_refine_extract_pre_pure: "hn_refine (\<up>\<phi> ** \<Gamma>) c \<Gamma>' R a = (\<phi> \<longrightarrow> hn_refine \<Gamma> c \<Gamma>' R a)"
  unfolding hn_refine_def
  by (auto simp: sep_algebra_simps STATE_extract)
  
(* TODO: Use FCOMP and parametricity lemma for this! Currently, it's FCOMP done manually! *)  
lemma hnr_array_nth: 
  assumes PURE: "is_pure A"
  assumes SV: "single_valued (the_pure A)"
  shows "hn_refine 
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn i ii)
    (array_nth xsi ii)
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn i ii)
    A
    (mop_array_nth xs i)" 
proof -
  have AR: "A = hr_comp id_assn (the_pure A)"
    by (simp add: \<open>is_pure A\<close>)

    
  show ?thesis  
    apply (rewrite in \<open>hn_refine _ _ _ \<hole> _\<close> AR)
    apply (rewrite in \<open>hn_refine \<hole> _ _ _ _\<close> pure_array_assn_alt[OF PURE])
    apply (rewrite hn_ctxt_hr_comp_extract)
    apply (clarsimp simp only: hn_refine_extract_pre_ex hn_refine_extract_pre_pure sep_algebra_simps sep_conj_assoc)
    apply (rule hn_refine_cons_res_complete)
    apply (rule hnr_raw_array_nth)
    apply (rule)
    apply (rewrite pure_array_assn_alt[OF PURE])
    apply (rewrite hn_ctxt_hr_comp_extract)
    apply (auto simp add: sep_algebra_simps pred_lift_extract_simps entails_def) []
    apply (rule)
    subgoal
      unfolding mop_array_nth_def
      apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
      apply parametricity
      by simp
    apply (rule SV)
    done
qed

definition "one_time m \<equiv> \<forall>M. m=SPECT M \<longrightarrow> (\<forall>x y s t. M x = Some s \<and> M y = Some t \<longrightarrow> s=t)"

lemma one_time_attains_sup:
  assumes one_time: "one_time m'"
  shows "attains_sup m m' RR"
  unfolding attains_sup_def 
  apply clarify
proof -
  fix r M' M y aa
  assume [simp]: "m' = SPECT M'" and "(r, aa) \<in> RR"
  show "\<exists>aa. Sup {M' a |a. (r, a) \<in> RR} = M' aa \<and> (r, aa) \<in> RR" (is "\<exists>_. Sup ?MM = _ \<and> _")
  proof (cases "\<exists>a c. (r,a)\<in>RR \<and> M' a = Some c")
    case True
    then obtain a c where 1: "(r,a)\<in>RR" "M' a = Some c" by blast
    with one_time have "Some c \<in> ?MM" "?MM \<subseteq> {None,Some c}"
      unfolding one_time_def
      by (auto) metis
    thus ?thesis using 1
      by (smt Sup_insert Sup_le_iff Sup_subset_mono cSup_eq_maximum ccpo_Sup_singleton empty_Sup insert_commute) 
  next
    case False   
    hence "?MM = {None}" using \<open>(r,aa)\<in>RR\<close> by force
    thus ?thesis using False \<open>(r,aa)\<in>RR\<close> by auto
  qed      
qed  


definition "one_time' t m \<equiv> \<forall>M. m=SPECT M \<longrightarrow> (\<forall>x s. M x = Some s \<longrightarrow> s=t)"


lemma one_time_to': "one_time m \<longleftrightarrow> (\<exists>t. one_time' t m)"
  unfolding one_time_def one_time'_def
  apply auto
  subgoal by (metis nrest.inject)
  by auto


definition "lift_ctime t P \<equiv> case P of None \<Rightarrow> FAILT | Some P \<Rightarrow> SPEC P (\<lambda>_. t)"

lemma one_time'_alt: "one_time' t m \<longleftrightarrow> (\<exists>P. m = lift_ctime t P)"
  unfolding one_time'_def lift_ctime_def SPEC_def 
  apply (cases m) apply (auto 0 0 split: if_splits option.splits)
  subgoal for M
    apply (rule exI[where x="Some (\<lambda>x. x\<in>dom M)"])
    by fastforce
  done


(*
lemma one_time'_alt: "one_time' t m \<longleftrightarrow> m\<noteq>FAILT \<longrightarrow> (\<exists>P. m = SPEC P (\<lambda>_. t))"
  unfolding one_time'_def SPEC_def apply (cases m) apply (auto split: if_splits simp: )
  subgoal for M
    apply (rule exI[where x="\<lambda>x. x\<in>dom M"])
    by fastforce
  done
*)  

lemma one_time'_attains_sup: "one_time' t m' \<Longrightarrow> attains_sup m m' R"
  using one_time_attains_sup one_time_to' by blast


named_theorems one_timeI
lemma [one_timeI]: "one_time' 0 (RETURNT x)"
  unfolding one_time'_def by auto
  
lemma [one_timeI]: "one_time' cc m \<Longrightarrow> one_time' (c+cc) (consume m c)"  
  unfolding one_time'_def consume_def
  by (auto split: nrest.splits; blast)
  
lemma [one_timeI]: "one_time' 0 (ASSERT \<Phi>)"  
  unfolding one_time'_def 
  by (cases \<Phi>) auto
  
lemma [one_timeI,simp]: "one_time' t FAILT"
  unfolding one_time'_def by auto
  
  
lemma OT'_Spec: "one_time' t (SPECT M) \<Longrightarrow> M x = Some t' \<longleftrightarrow> (t'=t \<and> M x = Some t)"  
  unfolding one_time'_def by auto
  
lemma OT'_fun_eq:
  assumes "\<forall>x. one_time' cc (f x)"  
  obtains F where "f = (\<lambda>x. lift_ctime cc (F x))"
  using assms unfolding one_time'_alt
  by metis
  
  
lemma lift_ctime_eq_spec: "lift_ctime c P = SPECT M \<Longrightarrow> SPECT M = SPEC (the P) (\<lambda>_. c)"  
  unfolding lift_ctime_def
  by (auto split: option.splits)
  
lemma [simp]: "lift_ctime c None = FAILT"
  unfolding lift_ctime_def by auto
  
lemma [simp]: "lift_ctime c (Some P) = SPEC P (\<lambda>_. c)"  
  unfolding lift_ctime_def by auto
  
lemma consume_lift_ctime: "consume (lift_ctime c P) cc = lift_ctime (cc+c) P"
  unfolding lift_ctime_def consume_def SPEC_def
  by (auto split: option.splits simp: fun_eq_iff) 
  
  
  
  
lemma [one_timeI]:
  assumes "one_time' c m"
  assumes "\<And>x. one_time' cc (f x)"
  shows "one_time' (c+cc) (bindT m f)"
proof -
  from assms(2) obtain F where 1[simp]: "f = (\<lambda>x. lift_ctime cc (F x))"
    using OT'_fun_eq by blast
  
  from assms(1) obtain P where [simp]: "m = lift_ctime c P"  
    unfolding one_time'_alt
    by auto
    
    
    
  show ?thesis proof (cases P) 
    case None thus ?thesis by simp
  next
    case (Some PP)
    show ?thesis sorry
  qed
qed

(*    
    have "{uu. \<exists>x. PP x \<and> uu = lift_ctime (c + cc) (F x)} = lift_ctime"  
  
  
    apply (cases P)
    apply simp_all
    unfolding bindT_alt
    apply (auto split: nrest.splits simp: SPEC_def consume_lift_ctime)
    
    
    apply (drule lift_ctime_eq_spec)
    apply
    
  apply (rule assms(2)[THEN OT'_fun_eq])
  
  
  
  using assms
  unfolding bindT_alt one_time'_alt
  apply (auto split: nrest.splits simp: )
  apply (rewrite OT'_Spec, assumption)
  apply simp
*)  
  
(*
  With loose rule, and syntactic check that time does not depend on result
*)
lemma hnr_array_nth_loose: 
  assumes PURE: "is_pure A"
  shows "hn_refine 
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn i ii)
    (array_nth xsi ii)
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn i ii)
    A
    (mop_array_nth xs i)" 
proof -
  have AR: "A = hr_comp id_assn (the_pure A)"
    by (simp add: \<open>is_pure A\<close>)

    
  show ?thesis  
    apply (rewrite in \<open>hn_refine _ _ _ \<hole> _\<close> AR)
    apply (rewrite in \<open>hn_refine \<hole> _ _ _ _\<close> pure_array_assn_alt[OF PURE])
    apply (rewrite hn_ctxt_hr_comp_extract)
    apply (clarsimp simp only: hn_refine_extract_pre_ex hn_refine_extract_pre_pure sep_algebra_simps sep_conj_assoc)
    apply (rule hn_refine_cons_res_complete_loose)
    apply (rule hnr_raw_array_nth)
    apply (rule)
    apply (rewrite pure_array_assn_alt[OF PURE])
    apply (rewrite hn_ctxt_hr_comp_extract)
    apply (auto simp add: sep_algebra_simps pred_lift_extract_simps entails_def) []
    apply (rule)
    subgoal
      unfolding mop_array_nth_def
      apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
      apply parametricity
      by simp
    subgoal  
      apply (rule one_time'_attains_sup)
      unfolding mop_array_nth_def
      apply (rule one_timeI)+
      done
    done
qed




(* Without single-valued! Re-doing the proof on the low-level. *)  
lemma hnr_array_nth': 
  assumes PURE: "is_pure A"
  shows "hn_refine 
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn i ii)
    (array_nth xsi ii)
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn i ii)
    A
    (mop_array_nth xs i)" 
proof -
  have AR: "A = pure (the_pure A)"
    by (simp add: \<open>is_pure A\<close>)

  note [is_pure_rule] = PURE  
    
  show ?thesis  
    unfolding pure_array_assn_alt[OF PURE]
    apply (rewrite in \<open>hn_refine _ _ _ \<hole> _\<close> AR)
    unfolding hn_ctxt_def pure_def mop_array_nth_def hr_comp_def
    supply [simp] = list_rel_imp_same_length
    apply vcg'
    apply parametricity
    by simp

qed


(* TODO: Use FCOMP and parametricity lemma for mop_list_nth! *)  
lemma hnr_array_upd: 
  assumes PURE: "is_pure A"
  assumes SV: "single_valued (the_pure A)"
  shows "hn_refine 
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn i ii ** hn_ctxt A x xi)
    (array_upd xsi ii xi)
    (hn_invalid (array_assn A) xs xsi ** hn_ctxt snat_assn i ii  ** hn_ctxt A x xi)
    (array_assn A)
    (mop_array_upd xs i x)" 
proof -
  have AR: "A = hr_comp id_assn (the_pure A)"
    by (simp add: \<open>is_pure A\<close>)

    
  show ?thesis  
    apply (rewrite in \<open>hn_refine _ _ _ \<hole> _\<close> pure_array_assn_alt[OF PURE])
    apply (rewrite in \<open>hn_refine \<hole> _ _ _ _\<close> pure_array_assn_alt[OF PURE])
    apply (rewrite in \<open>hn_refine _ _ \<hole> _ _\<close> pure_array_assn_alt[OF PURE])
    apply (rewrite in \<open>hn_ctxt A\<close> in \<open>hn_refine \<hole> _ _ _ _\<close> AR)
    apply (rewrite in \<open>hn_ctxt A\<close> in \<open>hn_refine _ _ \<hole> _ _\<close> AR)
    
    apply (simp only: hn_ctxt_hr_comp_extract invalid_hr_comp_ctxt)
    apply (clarsimp simp: hn_refine_extract_pre_ex hn_refine_extract_pre_pure hn_ctxt_def pure_def sep_algebra_simps)
    apply (rule hn_refine_cons_res_complete)
    applyS (rule hnr_raw_array_upd[where x=xi and xi=xi])
    
    apply1 (clarsimp simp: hn_ctxt_def pure_def sep_algebra_simps entails_lift_extract_simps)
    applyS rule
    
    apply1 (clarsimp simp: hn_ctxt_def pure_def sep_algebra_simps entails_lift_extract_simps)
    apply1 (rule ENTAILSD) 
    applyS fri
    
    applyS rule
    
    subgoal
      unfolding mop_array_upd_def
      apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
      apply parametricity
      by simp
    
    applyS (simp add: list_rel_sv_iff SV)
    done
qed    
    

lemma hnr_array_new: 
  assumes PURE: "is_pure A"
  assumes SV: "single_valued (the_pure A)"
  assumes INIT: "(init,x) \<in> the_pure A"
  shows "hn_refine 
    (hn_ctxt snat_assn i ii)
    (narray_new TYPE('a::llvm_rep) ii)
    (hn_ctxt snat_assn i ii)
    (array_assn A)
    (mop_array_new i x)" 
proof -
  have AR: "A = hr_comp id_assn (the_pure A)"
    by (simp add: \<open>is_pure A\<close>)

  show ?thesis  
    apply (rewrite in \<open>hn_refine _ _ _ \<hole> _\<close> pure_array_assn_alt[OF PURE])
    apply (rule hn_refine_cons_res_complete)
    applyS (rule hnr_raw_array_new)
    applyS rule
    applyS rule
    applyS rule
    subgoal     
      unfolding mop_array_new_def
      apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
      apply (parametricity add: INIT)
      by simp
    applyS (simp add: list_rel_sv_iff SV)
    done
qed

(* TODO: Move *)
lemma FREE_hrcompI:
  assumes "MK_FREE (A) f"  
  shows "MK_FREE (hr_comp A R) f"  
  supply [vcg_rules] = MK_FREED[OF assms]
  apply (rule)
  unfolding hr_comp_def
  by vcg


lemma FREE_array_assn:
  assumes PURE: "is_pure A"
  shows "MK_FREE (array_assn A) narray_free"  
  apply (rewrite pure_array_assn_alt[OF PURE])
  apply (rule FREE_hrcompI)
  apply (rule FREE_raw_array_assn)
  done


  
  
lemma "(xs,xsi)\<in>\<langle>A\<rangle>list_rel \<Longrightarrow> i<length xs \<Longrightarrow> mop_array_nth xs i \<le>\<Down>A (mop_array_nth xsi i)"  
  apply (auto simp: mop_array_nth_def pw_acost_le_iff refine_pw_simps)
  apply parametricity by simp
  
    
  
end


