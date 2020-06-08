theory Hnr_Primitives_Experiment
imports Sepref "../ds/LLVM_DS_Dflt"
begin
  hide_const (open) LLVM_DS_Array.array_assn

experiment
begin

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

end
   

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

(* BEWARE, conflicting abbreviation snat_assn *)
abbreviation "snat_assn2 \<equiv> \<upharpoonleft>snat.assn"
lemma "snat_assn2 = snat_assn" 
  by (simp add: snat.assn_is_rel snat_rel_def)  
                                     
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

abbreviation "mop_array_nth_cost \<equiv> (lift_acost (cost ''load'' (Suc 0)+cost ''ofs_ptr'' (Suc 0)))"
definition "mop_array_nth xs i \<equiv> do { ASSERT (i<length xs); consume (RETURNT (xs!i)) mop_array_nth_cost }"
definition "mop_array_upd xs i x \<equiv> do { ASSERT (i<length xs); consume (RETURNT (xs[i:=x])) (lift_acost (cost ''store'' (Suc 0)+cost ''ofs_ptr'' (Suc 0))) }"
definition "mop_array_new n x \<equiv> do { ASSERT (PROTECT True); consume (RETURNT (replicate n x)) (lift_acost (cost'_narray_new n)) }"

thm vcg_rules
lemma hnr_raw_array_nth: "hn_refine 
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn2 i ii)
  (array_nth xsi ii)
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn2 i ii)
  id_assn
  (mop_array_nth xs i)" 
  unfolding hn_ctxt_def pure_def mop_array_nth_def
  apply vcg_step
  apply vcg_step
  by vcg

lemma hnr_raw_array_upd: "hn_refine 
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn2 i ii ** hn_ctxt id_assn x xi)
  (array_upd xsi ii xi)
  (hn_invalid raw_array_assn xs xsi ** hn_ctxt snat_assn2 i ii  ** hn_ctxt id_assn x xi)
  raw_array_assn
  (mop_array_upd xs i x)" 
  unfolding hn_ctxt_def pure_def invalid_assn_def mop_array_upd_def
  by vcg
  
  

lemma hnr_raw_array_new: "hn_refine 
  (hn_ctxt snat_assn2 i ii)
  (narray_new TYPE('a::llvm_rep) ii)
  (hn_ctxt snat_assn2 i ii)
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
  (hn_ctxt (eoarray_assn A) xs xsi ** hn_ctxt snat_assn2 i ii)
  (eoarray_nth_impl xsi ii)
  (hn_invalid (eoarray_assn A) xs xsi ** hn_ctxt snat_assn2 i ii)
  (cnc_assn (\<lambda>(_,xsi'). xsi'=xsi) (A \<times>\<^sub>a eoarray_assn A))
  (mop_oarray_nth $ xs $ i)"  
  unfolding hn_ctxt_def pure_def invalid_assn_def cnc_assn_def eoarray_assn_def mop_oarray_nth_def eoarray_nth_impl_def
  by vcg 
\<comment> \<open>thm hnr_eoarray_nth[sepref_fr_rules] (* BEWARE: needs $ for APP *) \<close>



(* hn_refine
   (hn_ctxt (eoarray_assn ?A) ?a ?ai \<and>* hn_val snat_rel ?b ?bi)
   (eo_extract_impl $ ?ai $ ?bi)
   (hn_invalid (eoarray_assn ?A) ?a ?ai \<and>* hn_val snat_rel ?b ?bi)
 (?A \<times>\<^sub>a eoarray_assn ?A) (mop_eo_extract $ ?a $ ?b) *)
term eoarray_assn
lemma hnr_eoarray_nth'[sepref_fr_rules]: "(uncurry eoarray_nth_impl, uncurry mop_oarray_nth)
       \<in> (eoarray_assn A)\<^sup>d *\<^sub>a snat_assn2\<^sup>k \<rightarrow>\<^sub>a\<^sub>d (\<lambda>x (ai, _). A \<times>\<^sub>a cnc_assn (\<lambda>x. x = ai) (eoarray_assn A))"
  apply(rule hfrefI)
  unfolding to_hnr_prod_fst_snd keep_drop_sels hf_pres_fst hn_ctxt_def pure_def invalid_assn_def cnc_assn_def eoarray_assn_def mop_oarray_nth_def eoarray_nth_impl_def
  by vcg

lemma hnr_eoarray_upd: "hn_refine 
  (hn_ctxt (eoarray_assn A) xs xsi ** hn_ctxt snat_assn2 i ii ** hn_ctxt A x xi)
  (array_upd xsi ii xi)
  (hn_invalid (eoarray_assn A) xs xsi ** hn_ctxt snat_assn2 i ii ** hn_invalid A x xi)
  (cnc_assn (\<lambda>ri. ri=xsi) (eoarray_assn A))
  (mop_oarray_upd $ xs $ i $ x)"  
  unfolding hn_ctxt_def pure_def invalid_assn_def cnc_assn_def eoarray_assn_def mop_oarray_upd_def
  by vcg

(* TODO: write in higher order form *)
thm hnr_eoarray_upd[sepref_fr_rules]
  
lemma hnr_eoarray_new: "hn_refine 
  (hn_ctxt snat_assn2 i ii)
  (narrayo_new TYPE('a::llvm_rep) ii)
  (hn_ctxt snat_assn2 i ii)
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
lemma deprecated_hnr_array_nth: 
  assumes PURE: "is_pure A"
  assumes SV: "single_valued (the_pure A)"
  shows "hn_refine 
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn2 i ii)
    (array_nth xsi ii)
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn2 i ii)
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

context
  fixes  T :: "(char list, enat) acost"
begin
  definition mop_list_get  :: "'a list \<Rightarrow> nat \<Rightarrow> ('a, _) nrest"
    where [simp]: "mop_list_get xs i \<equiv> do { ASSERT (i<length xs); consume (RETURNT (xs!i)) T }"

  sepref_register "mop_list_get"
  print_theorems
end


lemma hnr_raw_array_nth': "hn_refine 
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn2 i ii)
  (array_nth xsi ii)
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn2 i ii)
  id_assn
  (mop_list_get mop_array_nth_cost xs i)" 
  unfolding hn_ctxt_def pure_def mop_list_get_def
  apply vcg_step
  apply vcg_step
  by vcg

thm mop_list_get.mcomb
thm mop_list_get_def

lemma param_mop_list_get:
  "(mop_list_get T, mop_list_get T) \<in> \<langle>the_pure A\<rangle> list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>the_pure A\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI)
  unfolding mop_list_get_def
  apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
  apply parametricity
  by simp 

lemma param_mop_array_nth:
  "(mop_array_nth, mop_array_nth) \<in> \<langle>the_pure A\<rangle> list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>the_pure A\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI)
  unfolding mop_array_nth_def
  apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
  apply parametricity
  by simp 

thm hnr_raw_array_nth
thm fcomp_norm_unfold 
thm fcomp_norm_simps
lemmas pure_array_assn_alt[symmetric, fcomp_norm_unfold]
thm fcomp_norm_unfold
context
  fixes A :: "'a  \<Rightarrow> 'b:: llvm_rep \<Rightarrow> assn"
  assumes [fcomp_norm_simps]: "is_pure A"
begin
thm param_mop_array_nth[of A] hnr_raw_array_nth
thm param_mop_array_nth[of A, simplified pure_array_assn_alt[of A, symmetric] fcomp_norm_simps]
(* TODO: FCOMP bug ? hr_comp triggers error here instead of in sepref_decl_impl *)
thm hnr_raw_array_nth[FCOMP param_mop_array_nth[of A], simplified pure_array_assn_alt[symmetric] fcomp_norm_simps]
thm hnr_raw_array_nth[FCOMP param_mop_array_nth[of A]]


thm hnr_raw_array_nth'[FCOMP param_mop_list_get[of _ A]] (* still raw! *)
end



(*
  With loose rule, and syntactic check that time does not depend on result
*)
lemma hnr_array_nth: 
  assumes PURE: "is_pure A"
  shows "hn_refine 
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn2 i ii)
    (array_nth xsi ii)
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn2 i ii)
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
      unfolding mop_array_nth_def
      apply (rule attains_sup_mop_return)
      done
    done
qed




(* Without single-valued! Re-doing the proof on the low-level. *)  
lemma deprecated_hnr_array_nth': 
  assumes PURE: "is_pure A"
  shows "hn_refine 
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn2 i ii)
    (array_nth xsi ii)
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn2 i ii)
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


(* TODO: Use FCOMP and parametricity lemma for mop_list_get! *)  
lemma deprecated_hnr_array_upd_SV: 
  assumes PURE: "is_pure A"
  assumes SV: "single_valued (the_pure A)"
  shows "hn_refine 
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn2 i ii ** hn_ctxt A x xi)
    (array_upd xsi ii xi)
    (hn_invalid (array_assn A) xs xsi ** hn_ctxt snat_assn2 i ii  ** hn_ctxt A x xi)
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


lemma hnr_array_upd: 
  assumes PURE: "is_pure A"
  shows "hn_refine 
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn2 i ii ** hn_ctxt A x xi)
    (array_upd xsi ii xi)
    (hn_invalid (array_assn A) xs xsi ** hn_ctxt snat_assn2 i ii  ** hn_ctxt A x xi)
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
    apply (rule hn_refine_cons_res_complete_loose)
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
    
    subgoal
      unfolding mop_array_upd_def  
      by (rule attains_sup_mop_return)
      
    done
qed    


    

lemma hnr_array_new: 
  assumes PURE: "is_pure A"
  assumes INIT: "(init,x) \<in> the_pure A"
  shows "hn_refine 
    (hn_ctxt snat_assn2 i ii)
    (narray_new TYPE('a::llvm_rep) ii)
    (hn_ctxt snat_assn2 i ii)
    (array_assn A)
    (mop_array_new i x)" 
proof -
  have AR: "A = hr_comp id_assn (the_pure A)"
    by (simp add: \<open>is_pure A\<close>)

  show ?thesis  
    apply (rewrite in \<open>hn_refine _ _ _ \<hole> _\<close> pure_array_assn_alt[OF PURE])
    apply (rule hn_refine_cons_res_complete_loose)
    applyS (rule hnr_raw_array_new)
    applyS rule
    applyS rule
    applyS rule
    subgoal     
      unfolding mop_array_new_def
      apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
      apply (parametricity add: INIT)
      by simp
    subgoal
      unfolding mop_array_new_def
      by (rule attains_sup_mop_return)
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
  
     
(* TODO

* für list mops und tmops definieren:
- replicate
- nth ( mop_list_get T )
- update

* HNR implementierungen mit arrays [sepref_fr_rules]
- nth ( hnr (...) array_nth (...) R  (mop_list_get mop_array_nth_cost) )
    @{thm hnr_raw_array_nth'[FCOMP param_mop_list_get[of _ A]]}
- replicate
- update


* 



*)





end
