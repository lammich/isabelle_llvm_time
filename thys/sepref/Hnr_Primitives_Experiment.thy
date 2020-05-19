theory Hnr_Primitives_Experiment
imports Sepref_Basic "../ds/LLVM_DS_Dflt"
begin
  
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
definition "mop_array_new n \<equiv> do { ASSERT (PROTECT True); consume (RETURNT (replicate n (init))) (lift_acost (cost'_narray_new n)) }"


lemma "hn_refine 
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn i ii)
  (array_nth xsi ii)
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn i ii)
  id_assn
  (mop_array_nth xs i)" 
  unfolding hn_ctxt_def pure_def mop_array_nth_def
  by vcg

lemma "hn_refine 
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn i ii ** hn_ctxt id_assn x xi)
  (array_upd xsi ii xi)
  (hn_invalid raw_array_assn xs xsi ** hn_ctxt snat_assn i ii  ** hn_ctxt id_assn x xi)
  raw_array_assn
  (mop_array_upd xs i x)" 
  unfolding hn_ctxt_def pure_def invalid_assn_def mop_array_upd_def
  by vcg
  
  

lemma "hn_refine 
  (hn_ctxt snat_assn i ii)
  (narray_new TYPE('a::llvm_rep) ii)
  (hn_ctxt snat_assn i ii)
  raw_array_assn
  (mop_array_new i)" 
  unfolding hn_ctxt_def pure_def invalid_assn_def mop_array_new_def
  by vcg
  
lemma "MK_FREE raw_array_assn narray_free"  
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
  
lemma "hn_refine 
  (hn_ctxt (eoarray_assn A) xs xsi ** hn_ctxt snat_assn i ii)
  (eoarray_nth_impl xsi ii)
  (hn_invalid (eoarray_assn A) xs xsi ** hn_ctxt snat_assn i ii)
  (cnc_assn (\<lambda>(_,xsi'). xsi'=xsi) (A \<times>\<^sub>a eoarray_assn A))
  (mop_oarray_nth xs i)"  
  unfolding hn_ctxt_def pure_def invalid_assn_def cnc_assn_def eoarray_assn_def mop_oarray_nth_def eoarray_nth_impl_def
  by vcg
  
lemma "hn_refine 
  (hn_ctxt (eoarray_assn A) xs xsi ** hn_ctxt snat_assn i ii ** hn_ctxt A x xi)
  (array_upd xsi ii xi)
  (hn_invalid (eoarray_assn A) xs xsi ** hn_ctxt snat_assn i ii ** hn_invalid A x xi)
  (cnc_assn (\<lambda>ri. ri=xsi) (eoarray_assn A))
  (mop_oarray_upd xs i x)"  
  unfolding hn_ctxt_def pure_def invalid_assn_def cnc_assn_def eoarray_assn_def mop_oarray_upd_def
  by vcg
  
lemma "hn_refine 
  (hn_ctxt snat_assn i ii)
  (narrayo_new TYPE('a::llvm_rep) ii)
  (hn_ctxt snat_assn i ii)
  (eoarray_assn A)
  (mop_oarray_new i)" 
  unfolding hn_ctxt_def pure_def invalid_assn_def eoarray_assn_def mop_oarray_new_def
  by vcg
    
definition "mop_oarray_free xs \<equiv> do { ASSERT (set xs \<subseteq> {None}); consume (RETURNT ()) (lift_acost 0) }"
  
lemma "hn_refine 
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
  

  
  
  
end


