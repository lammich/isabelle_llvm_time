theory Sorting_Quicksort_Partition
imports Sorting_Quicksort_Scheme
begin

(* TODO: move *)

definition costmult :: "_ \<Rightarrow> ('b, _ ) acost \<Rightarrow> ('b, _ ) acost" (infixl "*m" 80)
  where  "costmult s c \<equiv> acostC (\<lambda>x. s * the_acost c x)"

lemma costmult_1_absorb[simp]: "(1::('b::comm_semiring_1)) *m c = c"
  "(Suc 0) *m d = d"
  by(simp_all add: costmult_def)



hide_const pi
  
(* TODO: Move. Found useful for ATPs *)
lemma strict_itrans: "a < c \<Longrightarrow> a < b \<or> b < c" for a b c :: "_::linorder"
  by auto


context weak_ordering begin
  
subsection \<open>Find Median\<close>


definition "move_median_to_first ri ai bi ci (xs::'a list) \<equiv> doN {
    ASSERT (ai\<noteq>bi \<and> ai\<noteq>ci \<and> bi\<noteq>ci \<and> ri\<noteq>ai \<and> ri\<noteq>bi \<and> ri\<noteq>ci);
    
    ab \<leftarrow> mop_cmp_idxs (cost ''cmp_idxs'' 1) xs ai bi;
    MIf ab
      (doN {    
        bc \<leftarrow> mop_cmp_idxs (cost ''cmp_idxs'' 1) xs bi ci;
        MIf bc
          (mop_list_swapN xs ri bi)
          (doN {
            ac \<leftarrow> mop_cmp_idxs (cost ''cmp_idxs'' 1) xs ai ci;
            MIf ac 
              (mop_list_swapN xs ri ci)
              (mop_list_swapN xs ri ai)
            })
      }) 
      (doN {
        ac \<leftarrow> mop_cmp_idxs (cost ''cmp_idxs'' 1) xs ai ci;
        MIf ac
          (mop_list_swapN xs ri ai)
          (doN {
            bc \<leftarrow> mop_cmp_idxs (cost ''cmp_idxs'' 1) xs bi ci;
            MIf bc
              (mop_list_swapN xs ri ci)
              (mop_list_swapN xs ri bi)
          })
      })
  }"

definition "move_median_to_first_cost =  cost ''cmp_idxs'' 3 + cost ''if'' 3 + cost ''list_swap'' 1"


lemma if_rule2: "(c \<Longrightarrow> x \<le> a) \<Longrightarrow> c \<Longrightarrow> Some x \<le> (if c then Some a else None)"
  by auto

lemma move_median_to_first_correct:
  "\<lbrakk> ri<ai; ai<bi; bi<ci; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. \<exists>i\<in>{ai,bi,ci}. 
        xs' = swap xs ri i
      \<and> (\<exists>j\<in>{ai,bi,ci}-{i}. xs!i\<^bold>\<le>xs!j)   
      \<and> (\<exists>j\<in>{ai,bi,ci}-{i}. xs!i\<^bold>\<ge>xs!j)   
      ) (\<lambda>_. move_median_to_first_cost)"
  unfolding move_median_to_first_def move_median_to_first_cost_def
  unfolding SPEC_def mop_cmp_idxs_def SPECc2_def mop_list_swap_def
  apply(rule gwp_specifies_I)
  apply (refine_vcg \<open>-\<close> rules: if_rule2) 
  apply (all \<open>(sc_solve,simp;fail)?\<close>)
  supply aux = bexI[where P="\<lambda>x. _=_ x \<and> _ x", OF conjI[OF refl]]
  apply ((rule aux)?; insert connex,auto simp: unfold_lt_to_le)+
  done
  
    
lemma move_median_to_first_correct':
  "\<lbrakk> ri<ai; ai<bi; bi<ci; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. slice_eq_mset ri (ci+1) xs' xs 
      \<and> (\<exists>i\<in>{ai,bi,ci}. xs'!i\<^bold>\<le>xs'!ri)
      \<and> (\<exists>i\<in>{ai,bi,ci}. xs'!i\<^bold>\<ge>xs'!ri)
      ) (\<lambda>_. move_median_to_first_cost)"
  apply (rule order_trans[OF move_median_to_first_correct])    
  by (auto simp: SPEC_def le_fun_def)
  
(* TODO: Clean up prove below, to use more concise aux-lemma! *)  
lemma move_median_to_first_correct'':
  "\<lbrakk> ri<ai; ai<bi; bi<ci; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. slice_eq_mset ri (ci+1) xs' xs 
      \<and> (\<exists>i\<in>{ai..ci}. xs'!i\<^bold>\<le>xs'!ri)
      \<and> (\<exists>i\<in>{ai..ci}. xs'!i\<^bold>\<ge>xs'!ri)
      ) (\<lambda>_. move_median_to_first_cost)"
  apply (rule order_trans[OF move_median_to_first_correct'])  
  by (auto simp: SPEC_def le_fun_def)
  
end

context sort_impl_context begin 

definition "aa = lift_acost mop_array_nth_cost + (lift_acost mop_array_nth_cost
                 + (cost lt_curr_name 1 + (lift_acost mop_array_upd_cost
                 + lift_acost mop_array_upd_cost)))"
  


definition cc :: ecost where "cc = lift_acost mop_array_nth_cost + lift_acost mop_array_nth_cost + lift_acost mop_array_upd_cost + lift_acost mop_array_upd_cost "
abbreviation "E_mmtf == TId(''cmp_idxs'':=aa, ''list_swap'':= cc)"
lemma wfR''E_mmtf[simp]: " wfR'' E_mmtf" by (auto intro!: wfR''_upd)

lemma cmp_idxs2'_refines_mop_cmp_idxs_with_E:
  "b'\<noteq>c' \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (c,c')\<in>Id \<Longrightarrow>
    cmp_idxs2' a b c \<le> \<Down> bool_rel (timerefine E_mmtf (mop_cmp_idxs (cost ''cmp_idxs'' 1) a' b' c'))"
  supply conc_Id[simp del]
    unfolding cmp_idxs2'_def cmpo_idxs2'_def  mop_cmp_idxs_def
    unfolding  mop_oarray_extract_def mop_eo_extract_def unborrow_def SPECc2_alt
          mop_oarray_upd_def mop_eo_set_def consume_alt
    unfolding mop_to_eo_conv_def mop_to_wo_conv_def
    apply normalize_blocks apply(split prod.splits)+
    apply normalize_blocks
    apply simp
    apply(intro refine0 consumea_refine bindT_refine_easy)
            apply refine_dref_type
    subgoal by auto  
    subgoal by auto  
    subgoal by auto  
    subgoal by auto   
    subgoal by (metis list_update_id list_update_overwrite list_update_swap option.sel)
    subgoal by simp
    subgoal by simp
    subgoal by(simp add: lift_acost_zero timerefineA_update_apply_same_cost  aa_def)
    subgoal by simp
    done



definition "move_median_to_first2 ri ai bi ci (xs::'a list) \<equiv> doN {
    ASSERT (ai\<noteq>bi \<and> ai\<noteq>ci \<and> bi\<noteq>ci \<and> ri\<noteq>ai \<and> ri\<noteq>bi \<and> ri\<noteq>ci);
    
    ab \<leftarrow> cmp_idxs2' xs ai bi;
    MIf ab
      (doN {    
        bc \<leftarrow> cmp_idxs2' xs bi ci;
        MIf bc
          (myswap xs ri bi)
          (doN {
            ac \<leftarrow> cmp_idxs2' xs ai ci;
            MIf ac 
              (myswap xs ri ci)
              (myswap xs ri ai)
            })
      }) 
      (doN {
        ac \<leftarrow> cmp_idxs2' xs ai ci;
        MIf ac
          (myswap xs ri ai)
          (doN {
            bc \<leftarrow> cmp_idxs2' xs bi ci;
            MIf bc
              (myswap xs ri ci)
              (myswap xs ri bi)
          })
      })
  }"

lemma myswap_refine':
  shows 
   "l\<noteq>h \<Longrightarrow> (xs,xs')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> (h,h')\<in>Id
       \<Longrightarrow> myswap xs l h \<le> \<Down> (\<langle>Id\<rangle>list_rel) (timerefine E_mmtf (mop_list_swapN xs' l' h'))"
  apply(rule myswap_refine)
  apply (auto simp: timerefineA_update_apply_same_cost   lift_acost_zero)
  by(simp add: add.assoc  cc_def)
 
lemma move_median_to_first2_refine':
  shows "move_median_to_first2 ri ai bi ci xs \<le> \<Down> (\<langle>Id\<rangle>list_rel) (timerefine E_mmtf (move_median_to_first ri ai bi ci xs))"
  unfolding move_median_to_first2_def move_median_to_first_def
  supply cmp_idxs2'_refines_mop_cmp_idxs_with_E[refine]
  supply SPECc2_refine[refine]
  supply myswap_refine'[refine]
  apply(refine_rcg bindT_refine_conc_time_my_inres MIf_refine)
  by(auto intro: struct_preservingI)

definition "move_median_to_first2_cost = 3 *m aa + cc + cost ''if'' 3"




lemma 
  SPEC_timerefine_eq_arh:
  "(\<And>x. B x = timerefineA R (B' x)) \<Longrightarrow>  timerefine R (SPEC A B') = SPEC A (\<lambda>x. timerefineA R (B' x))"
  apply(auto simp: SPEC_def)
  unfolding timerefine_SPECT 
  apply auto
  unfolding timerefineF_def timerefineA_def
  by auto


thm timerefineA_update_apply_same_cost

lemma timerefineA_update_apply_same_cost': 
  "timerefineA (F(n := y)) (cost n (t::enat)) = t *m y"
  by (auto simp: costmult_def timerefineA_def cost_def zero_acost_def timerefineA_upd_aux ) 

print_classes

lemma move_median_to_first2_correct: 
  "\<lbrakk> ri<ai; ai<bi; bi<ci; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first2 ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. \<exists>i\<in>{ai,bi,ci}. 
        xs' = swap xs ri i
      \<and> (\<exists>j\<in>{ai,bi,ci}-{i}. xs!i\<^bold>\<le>xs!j)   
      \<and> (\<exists>j\<in>{ai,bi,ci}-{i}. xs!i\<^bold>\<ge>xs!j)   
      ) (\<lambda>_. move_median_to_first2_cost)"
  apply(rule order.trans[OF move_median_to_first2_refine'])
  apply simp 
  apply(rule order.trans)
   apply(rule timerefine_mono2[OF _ move_median_to_first_correct])
       prefer 6
  subgoal apply(simp add: SPEC_timerefine_eq_arh)
    apply(rule SPEC_leq_SPEC_I) apply simp
    by(auto simp: move_median_to_first_cost_def move_median_to_first2_cost_def
            timerefineA_update_apply_same_cost' timerefineA_propagate add.assoc add.commute) 
  by auto  


  thm move_median_to_first_correct

sepref_register move_median_to_first2

find_in_thms mop_array_nth in sepref_fr_rules

sepref_def move_median_to_first_impl [llvm_inline] is "uncurry4 (PR_CONST move_median_to_first2)" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d \<rightarrow>\<^sub>a arr_assn"
  unfolding move_median_to_first2_def PR_CONST_def
  unfolding myswap_def
  by sepref 
                    
end

context weak_ordering begin  
  
subsection \<open>Hoare Partitioning Scheme\<close>  


definition "ungrd_qsp_next_l_spec T xs pi li hi0 \<equiv> 
  doN {
    ASSERT (pi<li \<and> pi<hi0 \<and> hi0\<le>length xs);
    ASSERT (\<exists>i\<in>{li..<hi0}. xs!i \<^bold>\<ge> xs!pi); 
    SPEC (\<lambda>li'. li\<le>li' \<and> li'<hi0 \<and> (\<forall>i\<in>{li..<li'}. xs!i\<^bold><xs!pi) \<and> xs!li'\<^bold>\<ge>xs!pi) (\<lambda>li'. T li li')
  }"

definition "ungrd_qsp_next_h_spec T xs pi li0 hi \<equiv> 
  doN {
    ASSERT (pi<li0 \<and> pi<length xs \<and> hi\<le>length xs \<and> (\<exists>i\<in>{li0..<hi}. (xs!i) \<^bold>\<le> xs!pi)); 
    SPEC (\<lambda>hi'. li0\<le>hi' \<and> hi'<hi \<and> (\<forall>i\<in>{hi'<..<hi}. xs!i\<^bold>>xs!pi) \<and> xs!hi'\<^bold>\<le>xs!pi) (\<lambda>hi'. T hi hi')
  }"


lemma "\<lbrakk>\<exists>i\<in>{li0..<hi}. xs ! i \<^bold>\<le> xs!pi; (\<forall>i\<in>{xa'<..<hi}. xs ! pi \<^bold>< xs! i) \<rbrakk> \<Longrightarrow> li0 \<le> xa'" 
    by (meson atLeastLessThan_iff greaterThanLessThan_iff leI less_le_trans wo_leD)

  
  
definition qsp_next_l :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, ecost) nrest" where            
  "qsp_next_l xs pi li hi \<equiv> doN {
    monadic_WHILEIT (\<lambda>li'. (\<exists>i\<in>{li'..<hi}. xs!i\<^bold>\<ge>xs!pi) \<and> li\<le>li' \<and> (\<forall>i\<in>{li..<li'}. xs!i\<^bold><xs!pi)) 
      (\<lambda>li. doN {ASSERT (li\<noteq>pi); mop_cmp_idxs (cost ''cmp_idxs'' 1) xs li pi}) (\<lambda>li. SPECc2 ''add'' (+) li 1) li
  }"  


lemma if_rule: "(c \<Longrightarrow> x \<le> a) \<Longrightarrow> (~c \<Longrightarrow> x \<le> b) \<Longrightarrow> x \<le> (if c then a else b)"
  by auto

definition uqnl_body 
  where "uqnl_body \<equiv> (cost ''if'' (1) + cost ''call'' 1
                                                            + cost ''cmp_idxs'' 1)"
definition "ungrd_qsp_next_l_cost li li' = (enat(li'-li+1)) *m uqnl_body + cost ''add'' (enat(li'-li))"


lemma costmult_add_distrib:
  fixes a :: "'b::semiring"
  shows "a *m (c + d) = a *m c + a *m d"
  apply(cases c; cases d) by (auto simp: costmult_def plus_acost_alt ring_distribs)

lemma costmult_minus_distrib2:
  fixes a :: nat
  shows "a *m c - a *m d = a *m (c - d)"
  apply(cases c; cases d) by (auto simp: costmult_def plus_acost_alt diff_mult_distrib2)

lemma costmult_minus_distrib:
  fixes a :: nat
  shows "a *m c - b *m c = (a-b) *m c"
  apply(cases c) by (auto simp: costmult_def plus_acost_alt diff_mult_distrib)

lemma costmult_cost:
  fixes x :: "'b::comm_semiring_1"
  shows "x *m (cost n y) = cost n (x*y)"
  by(auto simp: costmult_def cost_def zero_acost_def)

(*
lemma fixes a :: enat
  shows "b\<le>a \<Longrightarrow> a *m x - b *m x = (a-b) *m x"
  apply(auto simp: costmult_def minus_acost_alt intro!: ext)
  done *)

lemma qsp_next_l_refine: "(qsp_next_l,PR_CONST (ungrd_qsp_next_l_spec ungrd_qsp_next_l_cost))\<in>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>\<langle>Id\<rangle>nrest_rel"
  unfolding qsp_next_l_def ungrd_qsp_next_l_spec_def ungrd_qsp_next_l_cost_def PR_CONST_def
  apply (intro fun_relI nrest_relI; clarsimp)
  apply(rule le_acost_ASSERTI)+
  unfolding SPEC_def mop_cmp_idxs_def SPECc2_def
  subgoal for xs p li hi
    apply(subst monadic_WHILEIET_def[symmetric, where E="\<lambda>li'. (hi-li') *m (uqnl_body + cost ''add'' 1)"])
    apply(rule gwp_specifies_I) 
    apply (refine_vcg \<open>-\<close>  rules: gwp_monadic_WHILEIET if_rule)
    subgoal 
      unfolding wfR2_def apply (auto simp: uqnl_body_def costmult_add_distrib costmult_cost the_acost_propagate zero_acost_def)
      by(auto simp: cost_def zero_acost_def) 
    subgoal for li'
      apply(rule loop_body_conditionI)
      subgoal apply(simp add: uqnl_body_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost)
        apply sc_solve 
        by auto
      subgoal apply(simp add: uqnl_body_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost)
        apply sc_solve 
        apply safe
        subgoal apply auto  
          by (metis Suc_eq_plus1 Suc_n_not_le_n add.commute le_diff_iff' le_trans lift_ord lt_by_le_def lt_by_linorder not_less_eq_eq one_enat_def plus_enat_simps(1))  
        subgoal apply auto  
          by (simp add: one_enat_def)  
        subgoal apply auto  
          by (simp add: one_enat_def)  
        subgoal apply (auto simp add: one_enat_def)
          done
        done
      subgoal 
        by (metis One_nat_def add.commute atLeastLessThan_iff less_Suc_eq less_Suc_eq_le linorder_not_le plus_1_eq_Suc wo_leD)
      done
    subgoal for li'
      apply(rule loop_exit_conditionI)
      apply(rule if_rule2)
      subgoal apply(subst costmult_minus_distrib) apply simp
        unfolding uqnl_body_def apply(simp add: costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost)
        apply sc_solve
        apply safe
        subgoal apply auto
          by (metis Suc_diff_le add.commute eq_iff one_enat_def plus_1_eq_Suc plus_enat_simps(1))
        subgoal apply auto
          by (metis Suc_diff_le eq_iff one_enat_def plus_1_eq_Suc plus_enat_simps(1))
        subgoal apply auto
          by (metis Suc_diff_le add.commute eq_iff one_enat_def plus_1_eq_Suc plus_enat_simps(1))
        subgoal by auto
        done
      subgoal by (auto simp: unfold_le_to_lt)
      done
    subgoal apply auto done
    subgoal apply auto done
    subgoal apply auto done
    done
  done

(*
    oops
    apply simp_all
    subgoal by auto
    apply safe
    subgoal by (metis atLeastLessThan_iff leI le_less_Suc_eq wo_leD)
    subgoal by (metis atLeastLessThan_iff leI le_less_Suc_eq)
    subgoal using less_eq_Suc_le by force
    subgoal by auto
    subgoal by (auto simp: unfold_le_to_lt)
    done  
  done
*)

definition qsp_next_h :: "'a list \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, ecost) nrest" where
  "qsp_next_h xs pi li0 hi \<equiv> doN {
    ASSERT (hi>0);
    hi \<leftarrow> SPECc2 ''sub'' (-) hi 1;
    ASSERT (hi<length xs);
    monadic_WHILEIT (\<lambda>hi'. hi'\<le>hi \<and> (\<exists>i\<le>hi'. xs!i\<^bold>\<le>xs!pi) \<and> (\<forall>i\<in>{hi'<..hi}. xs!i\<^bold>>xs!pi))
      (\<lambda>hi. doN {ASSERT(pi\<noteq>hi); mop_cmp_idxs (cost ''cmp_idxs'' 1) xs pi hi})
      (\<lambda>hi. doN { ASSERT(hi>0); SPECc2 ''sub'' (-) hi 1}) hi
  }"  

definition uqnr_body 
  where "uqnr_body \<equiv> (cost ''if'' (1) + cost ''call'' 1
                                                           + cost ''sub'' 1 + cost ''cmp_idxs'' 1)"
definition "ungrd_qsp_next_r_cost hi hi' =  (enat(hi-hi')) *m uqnr_body"
  
lemma tt: "hi>0 \<Longrightarrow> {hi'<..hi - Suc 0} = {hi'<..<hi}" by auto

lemma qsp_next_h_refine: "(qsp_next_h,PR_CONST (ungrd_qsp_next_h_spec ungrd_qsp_next_r_cost)) \<in> Id  \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nrest_rel"
  unfolding qsp_next_h_def ungrd_qsp_next_h_spec_def ungrd_qsp_next_r_cost_def PR_CONST_def 
  apply (intro fun_relI nrest_relI; clarsimp)
  apply(rule le_acost_ASSERTI)+
  unfolding SPEC_def SPECc2_def mop_cmp_idxs_def
  subgoal for xs pi li0 hi
    apply(subst monadic_WHILEIET_def[symmetric, where E="\<lambda>hi'. (hi'-li0) *m uqnr_body"])
    apply(rule gwp_specifies_I) 
    apply (refine_vcg \<open>-\<close> rules: gwp_monadic_WHILEIET if_rule split_ifI)
    subgoal
      unfolding wfR2_def apply (auto simp: uqnr_body_def costmult_add_distrib costmult_cost the_acost_propagate zero_acost_def)
      by(auto simp: cost_def zero_acost_def) 
    subgoal 
      apply(rule loop_body_conditionI)
      subgoal 
        apply(simp add: uqnr_body_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost)
        apply sc_solve 
        apply safe by auto
      subgoal apply(simp add: uqnr_body_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost)
        apply sc_solve 
        apply safe
        subgoal apply auto
          by (metis Suc_diff_Suc eq_iff greaterThanAtMost_iff less_le_trans nat_le_Suc_less_imp nat_neq_iff one_enat_def plus_1_eq_Suc plus_enat_simps(1) wo_leD) 
        subgoal apply auto 
          by (metis Suc_diff_Suc add.commute diff_is_0_eq eq_iff greaterThanAtMost_iff le_less_trans nat_le_Suc_less_imp not_gr_zero one_enat_def plus_1_eq_Suc plus_enat_simps(1) wo_leD zero_less_diff)
        subgoal apply auto 
          by (metis Suc_diff_Suc diff_is_0_eq eq_iff greaterThanAtMost_iff le_less_trans nat_le_Suc_less_imp not_gr_zero one_enat_def plus_1_eq_Suc plus_enat_simps(1) wo_leD zero_less_diff)
        subgoal apply auto 
          by (metis Suc_diff_Suc add.commute diff_is_0_eq eq_iff greaterThanAtMost_iff le_less_trans nat_le_Suc_less_imp not_gr_zero one_enat_def plus_1_eq_Suc plus_enat_simps(1) wo_leD zero_less_diff)
        done
      subgoal apply auto 
        subgoal by (metis One_nat_def le_step_down_nat wo_leD)
        subgoal by (metis Suc_lessI Suc_pred greaterThanAtMost_iff)  
        done
      done
    subgoal apply auto  
      by (metis gr0I leD wo_leD)  
    subgoal for hi'
      apply(rule loop_exit_conditionI)
      apply(rule if_rule2)
      subgoal  apply(subst costmult_minus_distrib) apply simp
        unfolding uqnr_body_def apply(simp add:  costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost)
        apply sc_solve
        apply(simp add: zero_enat_def one_enat_def) (*
        apply safe
        subgoal by linarith
        subgoal by linarith 
        subgoal
          using \<open>\<And>ia i. \<lbrakk>hi - Suc 0 < length xs; pi \<noteq> hi'; pi < length xs; \<not> xs ! pi \<^bold>< xs ! hi'; cost ''if'' (hi' - pi) + (cost ''call'' (hi' - pi) + (cost ''sub'' (hi' - pi) + cost ''cmp_idxs'' (hi' - pi))) \<le> cost ''if'' (hi - Suc pi) + (cost ''call'' (hi - Suc pi) + (cost ''sub'' (hi - Suc pi) + cost ''cmp_idxs'' (hi - Suc pi))); hi \<le> length xs; i \<in> {pi<..<hi}; xs ! i \<^bold>\<le> xs ! pi; hi' \<le> hi - Suc 0; hi' < hi; \<forall>i\<in>{hi'<..hi - Suc 0}. xs ! pi \<^bold>< xs ! i; \<forall>i\<in>{hi'<..<hi}. xs ! pi \<^bold>< xs ! i; xs ! hi' \<^bold>\<le> xs ! pi; ia \<le> hi'; xs ! ia \<^bold>\<le> xs ! pi\<rbrakk> \<Longrightarrow> Suc (hi - Suc (pi + (hi' - pi))) \<le> hi - hi'\<close> by blast
        *) done
      subgoal
        apply (intro conjI) 
        subgoal unfolding tt  by (meson atLeastLessThan_iff greaterThanLessThan_iff leI less_le_trans wo_leD)  
        subgoal using nat_le_Suc_less by blast
        subgoal by (simp add: nat_le_Suc_less_imp)
        subgoal using wo_leI by blast
        done
      done
    subgoal by auto 
    subgoal by (meson atLeastLessThan_iff dual_order.strict_trans1 greaterThanAtMost_iff nat_le_Suc_less_imp wo_leD) 
    subgoal apply auto
      using nat_le_Suc_less_imp by blast  
    subgoal          
      using nz_le_conv_less by blast  
    subgoal  
      by auto  
    done
  done


  (*

  apply (all \<open>(determ \<open>elim conjE exE\<close>)?\<close>)
  apply simp_all
  subgoal by force
  subgoal by (meson greaterThanLessThan_iff nat_le_Suc_less_imp)
  subgoal by (meson greaterThanAtMost_iff greaterThanLessThan_iff nat_le_Suc_less_imp wo_leD)
  subgoal by (metis gr0I le_zero_eq unfold_lt_to_le)
  subgoal by (metis One_nat_def le_step_down_nat wo_leD)
  subgoal by (metis Suc_pred greaterThanAtMost_iff linorder_neqE_nat not_less_eq)
  subgoal by (meson greaterThanAtMost_iff greaterThanLessThan_iff nat_le_Suc_less_imp)
  subgoal using wo_leI by blast
  done  *)

definition "guard x = x"
definition "qs_partition li\<^sub>0 hi\<^sub>0 pi xs\<^sub>0 \<equiv> doN {
  ASSERT (pi < li\<^sub>0 \<and> li\<^sub>0<hi\<^sub>0 \<and> hi\<^sub>0\<le>length xs\<^sub>0);
  
  \<comment> \<open>Initialize\<close>
  li \<leftarrow> ungrd_qsp_next_l_spec ungrd_qsp_next_l_cost xs\<^sub>0 pi li\<^sub>0 hi\<^sub>0;
  hi \<leftarrow> ungrd_qsp_next_h_spec ungrd_qsp_next_r_cost xs\<^sub>0 pi li\<^sub>0 hi\<^sub>0;
  
  ASSERT (li\<^sub>0\<le>hi);
  
  (xs,li,hi) \<leftarrow> monadic_WHILEIT 
    (\<lambda>(xs,li,hi). 
        li\<^sub>0\<le>li \<and> hi<hi\<^sub>0
      \<and> li<hi\<^sub>0 \<and> hi\<ge>li\<^sub>0  
      \<and> slice_eq_mset li\<^sub>0 hi\<^sub>0 xs xs\<^sub>0
      \<and> xs!pi = xs\<^sub>0!pi
      \<and> (\<forall>i\<in>{li\<^sub>0..<li}. xs!i \<^bold>\<le> xs\<^sub>0!pi)
      \<and> xs!li \<^bold>\<ge> xs\<^sub>0!pi
      \<and> (\<forall>i\<in>{hi<..<hi\<^sub>0}. xs!i \<^bold>\<ge> xs\<^sub>0!pi)
      \<and> xs!hi \<^bold>\<le> xs\<^sub>0!pi  
    )
    (\<lambda>(xs,li,hi). SPECc2 ''lt'' (<) li hi) 
    (\<lambda>(xs,li,hi). doN {
      ASSERT(li<hi \<and> li<length xs \<and> hi<length xs \<and> li\<noteq>hi);
      xs \<leftarrow> mop_list_swapN xs li hi;
      li \<leftarrow> SPECc2 ''add'' (+) li 1;
      li \<leftarrow> ungrd_qsp_next_l_spec ungrd_qsp_next_l_cost xs pi li hi\<^sub>0;
      hi \<leftarrow> ungrd_qsp_next_h_spec ungrd_qsp_next_r_cost xs pi li\<^sub>0 hi;
      RETURN (xs,li,hi)
    }) 
    (xs\<^sub>0,li,hi);
  
  RETURN (xs,li)
}"  


definition uqnlr_body 
  where "uqnlr_body \<equiv> (cost ''list_swap'' 1 + cost ''add'' 1 + cost ''if'' 3 + cost ''call'' 3
                         + cost ''sub'' 1 + cost ''cmp_idxs'' 2)"

abbreviation "qs_body_cost \<equiv> (cost ''add'' (1::enat) + cost ''sub'' 1
      + cost ''list_swap'' 1 + cost ''if'' 3 + cost ''call'' 3 + cost ''lt'' 1 + cost ''cmp_idxs'' 2)"
definition "qs_partition_cost xs\<^sub>0 li hi = (enat (hi-li)) *m qs_body_cost"

lemma qs_partition_correct_aux1:
  fixes hi'' :: nat
  assumes "hi''\<ge>li''" and "hi'\<ge>li'"
  shows "hi'' - li'' + hi' + li'' - (hi'' + li') \<le> hi' - li'"
proof -
  have "hi'' - li'' + hi' + li'' - (hi'' + li')
        = hi' + (hi'' - li'' +  li'') - (hi'' + li')"
    by auto
  also have  "\<dots> = hi' + hi'' - (hi'' + li')"
    using assms(1) by simp
  also have "\<dots> = hi' - li'"
    using assms(2) by simp
  finally show ?thesis by simp    
qed

lemma pff:
  assumes "hi''<hi'" "li'<li''"
  shows "( (hi''::int) - li'') * 2 + hi' + li'' - (hi'' + li') \<le> (hi' - li') * 2"
  using assms(1) assms(2) by auto

lemma
  assumes   "li'<li''"  "hi''<hi'" (* "li<li'" "hi'<hi" "li<hi" "li'<hi'" *)
  shows "(1::int) + (hi'' - li'' + (hi'' - li + (hi + hi'))) - (hi'' + li') \<le> hi' + hi' + hi - (li' + li + li')"
  using assms by simp

lemma woaleack:
  assumes A: "li'<li''" "li''<hi" and B: "hi''<hi'" "li<hi''" and C: "hi''<hi'" "li'<li''" "li'<hi'"
  shows "(hi''::nat) - li'' + (hi'' - li) + (hi - li'') + (hi' - hi'') + (li'' - li') + 1 \<le> 0 + (hi' - li') + (hi' - li) + (hi - li')"
proof -
  have *: "((hi - li'') + (li'' - li')) = hi - li'"
    using A by auto
  have **: "(hi' - hi'') + (hi'' - li) = hi' - li"
    using B by auto
  have ***: "((hi'' - li'') + 1) \<le> (hi' - li')"
    using C by auto    
  have "hi'' - li'' + (hi'' - li) + (hi - li'') + (hi' - hi'') + (li'' - li') + 1 
      = ((hi - li'') + (li'' - li')) + ((hi' - hi'') + (hi'' - li)) + ((hi'' - li'') + 1)"
    by simp
  also have "\<dots> = ((hi - li') + (hi' - li)) + ((hi'' - li'') + 1)" using * ** by simp
  also have "\<dots> \<le> ((hi - li') + (hi' - li)) + (hi' - li')"
    apply(rule add_left_mono) apply(subst ***) by simp 
  also have "\<dots> = 0 + (hi' - li') + (hi' - li) + (hi - li')" by simp
  finally show ?thesis .
qed
 
lemma qs_partition_correct:
  fixes xs\<^sub>0 :: "'a list"
  shows 
  "\<lbrakk> pi<li; li<hi; hi\<le>length xs\<^sub>0; \<exists>i\<in>{li..<hi}. xs\<^sub>0!pi\<^bold>\<le>xs\<^sub>0!i; \<exists>i\<in>{li..<hi}. xs\<^sub>0!i\<^bold>\<le>xs\<^sub>0!pi \<rbrakk> \<Longrightarrow> qs_partition li hi pi xs\<^sub>0 
  \<le> SPEC (\<lambda>(xs,i). slice_eq_mset li hi xs xs\<^sub>0 \<and> li\<le>i \<and> i<hi \<and> (\<forall>i\<in>{li..<i}. xs!i\<^bold>\<le>xs\<^sub>0!pi) \<and> (\<forall>i\<in>{i..<hi}. xs!i\<^bold>\<ge>xs\<^sub>0!pi) ) (\<lambda>_. qs_partition_cost xs\<^sub>0 li hi )"  
  unfolding qs_partition_def ungrd_qsp_next_l_spec_def ungrd_qsp_next_h_spec_def
  unfolding SPEC_REST_emb'_conv  SPECc2_def mop_list_swap_def
  
  apply(rule gwp_specifies_I)

  apply(subst monadic_WHILEIET_def[symmetric, where E="\<lambda>(xs::'a list,li'::nat,hi'::nat).
             (hi-li') *m (uqnl_body+ cost ''add'' 1) + (hi'-li) *m uqnr_body + (hi'-li') *m (cost ''list_swap'' 1 + cost ''call'' 1 + cost ''lt'' 1 + cost ''if'' 1) "])
  apply (refine_vcg \<open>-\<close> rules: gwp_RETURNT_I gwp_monadic_WHILEIET if_rule split_ifI)  
 
  subgoal unfolding wfR2_def 
    apply safe
    apply (auto simp add: uqnl_body_def uqnr_body_def costmult_add_distrib costmult_cost   the_acost_propagate)
    apply (simp_all add: cost_def zero_acost_def)
    done  
  subgoal  for _ _ _ xs li' hi' li'' hi'' 
    apply(rule loop_body_conditionI)
    subgoal 
      unfolding ungrd_qsp_next_l_cost_def ungrd_qsp_next_r_cost_def 
            uqnlr_body_def uqnl_body_def uqnr_body_def
      apply(simp add: costmult_add_distrib costmult_cost lift_acost_cost lift_acost_propagate)
      apply sc_solve  by auto   
    subgoal apply simp
      unfolding ungrd_qsp_next_l_cost_def ungrd_qsp_next_r_cost_def 
            uqnlr_body_def uqnl_body_def uqnr_body_def
      apply(simp add: costmult_add_distrib costmult_cost lift_acost_cost lift_acost_propagate)
      apply sc_solve_debug
      apply safe
      subgoal (* ''list_swap'' *) unfolding sc_solve_debug_def by (simp add: zero_enat_def one_enat_def)
      subgoal (* ''if'' *) unfolding sc_solve_debug_def
        apply(simp only: zero_enat_def one_enat_def plus_enat_simps lift_ord) done
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def)
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def)
      subgoal (* ''add'' *) unfolding sc_solve_debug_def 
        by(simp only: zero_enat_def one_enat_def plus_enat_simps lift_ord) 
      subgoal (* ''cmp_idxs'' *) unfolding sc_solve_debug_def 
        by(simp only: zero_enat_def one_enat_def plus_enat_simps lift_ord) 
      subgoal (* ''sub'' *) unfolding sc_solve_debug_def 
        by (simp only: zero_enat_def one_enat_def plus_enat_simps lift_ord) 
      done
    subgoal 
      apply safe
      subgoal by linarith
      subgoal by linarith
      subgoal by (metis atLeastLessThan_iff slice_eq_mset_swap(2) swap_length)
      subgoal by (metis leD swap_indep)
      subgoal apply(simp only: unfold_lt_to_le) apply clarsimp
        apply (smt Suc_leI atLeastLessThan_iff le_def less_le_trans less_Suc_eq swap_indep swap_length swap_nth1)
        done
      subgoal by (metis (full_types) linorder_not_le swap_indep)
      subgoal
          (* this proof is even more crazy *)
        apply(use [[put_named_ss HOL_ss]] in \<open>clarsimp\<close>) 
        apply(use [[put_named_ss Main_ss]] in \<open>simp_all add: slice_eq_mset_eq_length unfold_lt_to_le\<close>)   
        apply clarsimp 
        by (metis greaterThanLessThan_iff less_le_trans linorder_neqE_nat swap_indep swap_nth2) 
      subgoal by (metis (full_types) linorder_not_le swap_indep)
      done
    done
  subgoal apply safe
    subgoal by linarith
    subgoal by linarith
    subgoal by (metis atLeastLessThan_iff linwo swap_indep swap_nth1 weak_ordering.unfold_lt_to_le)
    done
  subgoal by (metis atLeastLessThan_iff discrete less_not_refl linwo swap_indep swap_nth2 weak_ordering.wo_less_le_trans)
  subgoal apply safe
    subgoal by linarith
    subgoal by (simp add: slice_eq_mset_eq_length) 
    done
  subgoal by safe
  subgoal apply safe
    subgoal by (metis (full_types) less_le_trans slice_eq_mset_eq_length)
    subgoal by (metis (full_types) less_le_trans slice_eq_mset_eq_length)
    done
  subgoal
    apply(rule loop_exit_conditionI)
    apply(rule gwp_RETURNT_I)
    unfolding emb'_def
    apply(rule if_rule2)
    subgoal 
      apply(subst lift_acost_diff_to_the_right) subgoal 
        by(simp add: cost_zero costmult_add_distrib costmult_cost lift_acost_cost lift_acost_propagate)
      unfolding ungrd_qsp_next_r_cost_def ungrd_qsp_next_l_cost_def
      unfolding    uqnlr_body_def uqnl_body_def uqnr_body_def
      apply simp
      unfolding qs_partition_cost_def
      apply(simp add: cost_zero costmult_add_distrib costmult_cost lift_acost_cost lift_acost_propagate)
      apply sc_solve_debug
      apply safe
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def numeral_eq_enat)
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def numeral_eq_enat)
      subgoal (* ''cmp_idxs'' *) unfolding sc_solve_debug_def by (simp add: one_enat_def numeral_eq_enat)
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def numeral_eq_enat)
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def numeral_eq_enat)
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def numeral_eq_enat)
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def numeral_eq_enat)
      done
    subgoal 
      apply safe
      by (metis atLeastLessThan_iff greaterThanLessThan_iff le_eq_less_or_eq strict_itrans)
    done
  subgoal apply simp
    apply safe
    subgoal using unfold_lt_to_le by blast
    subgoal using unfold_lt_to_le by blast
    done

  subgoal (* this one is a central argument, I didn't see this in the beginning - nice one *)
    by (meson atLeastLessThan_iff greaterThanLessThan_iff leI less_le_trans wo_leD)
  subgoal
    apply safe 
    subgoal by linarith
    subgoal by auto
    done
  subgoal by blast
  subgoal 
        using less_trans by blast    
  subgoal apply simp done
  done

(*
  oops 
  supply [[put_named_ss HOL_ss]]
  apply (all \<open>(clarsimp;fail)?\<close>)
  apply clarsimp_all
  supply [[put_named_ss Main_ss]]
  apply (simp_all add: slice_eq_mset_eq_length unfold_lt_to_le)
  
  subgoal by fastforce
  subgoal by auto
  subgoal
    by (metis le_trans order.strict_implies_order slice_eq_mset_eq_length swap_length) 
  subgoal apply (clarsimp simp: swap_def)
    by (metis (full_types) More_List.swap_def atLeastSucLessThan_greaterThanLessThan greaterThanLessThan_iff less_le_trans swap_nth2) 
  subgoal
    by (metis (mono_tags) greaterThanLessThan_iff leD le_less_trans less_le_trans nat_le_linear not_less_eq_eq slice_eq_mset_eq_length swap_indep swap_nth1) 
  subgoal 
    by (smt Suc_le_lessD dual_order.trans greaterThanLessThan_iff leI less_imp_le_nat swap_indep swap_length swap_nth1) 
  subgoal
    by (smt Suc_le_lessD atLeastLessThan_iff le_less_trans less_imp_le_nat slice_eq_mset_eq_length slice_eq_mset_swap(2)) 
    
  subgoal apply clarsimp
    by (metis less_irrefl less_imp_not_less less_le_trans swap_indep)
    
  subgoal apply clarsimp
    by (smt Suc_leI atLeastLessThan_iff le_def less_le_trans less_Suc_eq swap_indep swap_length swap_nth1)
  subgoal apply clarsimp
    by (metis le_def less_trans swap_indep)
      
  subgoal apply clarsimp
    by (smt greaterThanLessThan_iff le_def less_le_trans le_neq_implies_less less_imp_le_nat slice_eq_mset_eq_length swap_indep swap_nth2)
    
  subgoal
    by (metis le_def less_trans swap_indep)
  subgoal
    by (metis greaterThanLessThan_iff strict_itrans le_neq_implies_less)
  done    
    *)

definition "partition_pivot xs\<^sub>0 l h \<equiv> doN {
  ASSERT (l\<le>h \<and> h\<le>length xs\<^sub>0 \<and> h-l\<ge>4);
  hl \<leftarrow> SPECc2 ''sub'' (-) h l;
  d \<leftarrow> SPECc2 ''div'' (div) hl 2;
  m \<leftarrow> SPECc2 ''add'' (+) l d;
  l' \<leftarrow> SPECc2 ''add'' (+) l 1;
  h' \<leftarrow> SPECc2 ''sub'' (-) h 1;
  xs\<^sub>1 \<leftarrow> move_median_to_first l l' m h' xs\<^sub>0;
  ASSERT (l<length xs\<^sub>1 \<and> length xs\<^sub>1 = length xs\<^sub>0);
  (xs,m) \<leftarrow> qs_partition l' h l xs\<^sub>1;

  \<comment> \<open>TODO: Use an auxiliary lemma, instead of this assertion chain! \<close>
  ASSERT (l<m \<and> m<h);
  ASSERT ((\<forall>i\<in>{l+1..<m}. xs!i\<^bold>\<le>xs\<^sub>1!l) \<and> xs!l\<^bold>\<le>xs\<^sub>1!l);
  ASSERT (\<forall>i\<in>{l..<m}. xs!i\<^bold>\<le>xs\<^sub>1!l);
  ASSERT (\<forall>i\<in>{m..<h}. xs\<^sub>1!l\<^bold>\<le>xs!i);
  
  
  RETURN (xs,m)
}"

lemma slice_LT_I_aux:
  assumes B: "l<m" "m<h" "h\<le>length xs"
  assumes BND: "\<forall>i\<in>{l..<m}. xs!i\<^bold>\<le>p" "\<forall>i\<in>{m..<h}. p\<^bold>\<le>xs!i"
  shows "slice_LT (\<^bold>\<le>) (slice l m xs) (slice m h xs)"
  unfolding slice_LT_def
  using B apply (clarsimp simp: in_set_conv_nth slice_nth)
  subgoal for i j
    apply (rule trans[OF BND(1)[THEN bspec, of "l+i"] BND(2)[THEN bspec, of "m+j"]])
    by auto
  done
  

lemma (in -)
  SPEC_timerefine_eq_arh:
  "timerefine R (SPEC A B') = SPEC A (\<lambda>x. timerefineA R (B' x))"
  apply(auto simp: SPEC_def)
  unfolding timerefine_SPECT 
  apply auto
  unfolding timerefineF_def timerefineA_def
  by auto

lemma (in -) timerefineA_update_apply_same_cost': 
  "timerefineA (F(n := y)) (cost n (t::enat)) = t *m y"
  by (auto simp: costmult_def timerefineA_def cost_def zero_acost_def timerefineA_upd_aux ) 


lemma tt2: "hi>0 \<Longrightarrow> {hi'..hi - Suc 0} = {hi'..<hi}" by auto

lemma partition_pivot_correct: "\<lbrakk>(xs,xs')\<in>Id; (l,l')\<in>Id; (h,h')\<in>Id\<rbrakk> 
  \<Longrightarrow> partition_pivot xs l h \<le> \<Down>Id (timerefine (TId(''partition'':=qs_body_cost + move_median_to_first_cost + cost ''sub'' 2 + cost ''add'' 2 + cost ''div'' 1)) (partition3_spec xs' l' h'))"
  unfolding partition_pivot_def partition3_spec_def
  apply(intro ASSERT_D3_leI)
  apply(subst SPEC_timerefine_eq_arh)
  unfolding SPEC_def SPECc2_def
  apply simp
  apply(rule gwp_specifies_I)
  supply mmtf = move_median_to_first_correct''[unfolded SPEC_def, THEN gwp_specifies_rev_I, THEN gwp_conseq_0]
  supply qsp = qs_partition_correct[unfolded SPEC_def, THEN gwp_specifies_rev_I, THEN gwp_conseq_0]
  apply (refine_vcg \<open>-\<close> rules: mmtf qsp if_rule2)

  apply(simp_all only: handy_if_lemma)

  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  apply clarsimp
  subgoal by auto
  subgoal by (metis le_less_trans less_imp_diff_less linorder_not_less tt2 zero_less_numeral)
  subgoal apply auto
    unfolding move_median_to_first_cost_def qs_partition_cost_def
      apply(auto simp: timerefineA_update_apply_same_cost' costmult_add_distrib costmult_cost lift_acost_cost lift_acost_propagate) 
    apply sc_solve
    apply safe
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    done
  subgoal
    apply safe
    subgoal 
      apply simp
      by (metis Suc_le_eq le_add2 le_refl order.strict_trans plus_1_eq_Suc slice_eq_mset_subslice slice_eq_mset_trans)
    subgoal by (auto dest: slice_eq_mset_eq_length intro!: slice_LT_I_aux)
    done
  subgoal 
    by clarsimp
  subgoal apply clarsimp by (metis (full_types) Suc_leI atLeastLessThan_iff le_neq_implies_less)
  subgoal 
    apply clarsimp 
    apply (subst slice_eq_mset_nth_outside, assumption)
      apply (auto dest: slice_eq_mset_eq_length)
    done 
  subgoal by auto
  subgoal by (metis diff_is_0_eq' le_trans nat_less_le not_numeral_le_zero slice_eq_mset_eq_length)
  subgoal by auto
  done
  
    
end  
  
context sort_impl_context begin
  
sepref_register ungrd_qsp_next_l_spec ungrd_qsp_next_h_spec 

(* TODO: We can get rid of the length xs restriction: the stopper element will always lie within <h, which is size_t representable! *)
sepref_definition qsp_next_l_impl [llvm_inline] is "uncurry3 (qsp_next_l)" :: "(arr_assn)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding qsp_next_l_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref

lemmas [sepref_fr_rules] = qsp_next_l_impl.refine[FCOMP qsp_next_l_refine]  
  
sepref_definition qsp_next_h_impl [llvm_inline] is "uncurry2 (qsp_next_h)" :: "(arr_assn)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding qsp_next_h_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
  
lemmas [sepref_fr_rules] = qsp_next_h_impl.refine[FCOMP qsp_next_h_refine]  
  
                        
sepref_register qs_partition  
sepref_def qs_partition_impl (*[llvm_inline]*) is "uncurry3 (PR_CONST qs_partition)" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d \<rightarrow>\<^sub>a arr_assn \<times>\<^sub>a size_assn"
  unfolding qs_partition_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [dest] = slice_eq_mset_eq_length
  by sepref

(*sepref_register qs_partitionXXX  
sepref_def qs_partitionXXX_impl (*[llvm_inline]*) is "uncurry3 (PR_CONST qs_partitionXXX)" :: "[\<lambda>(((l,h),p),xs). length xs < max_snat LENGTH(size_t)]\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d \<rightarrow> arr_assn \<times>\<^sub>a size_assn"
  unfolding qs_partitionXXX_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [dest] = slice_eq_mset_eq_length
  by sepref
*)  

sepref_register partition_pivot  
sepref_def partition_pivot_impl [llvm_inline] is "uncurry2 (PR_CONST partition_pivot)" :: "arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn \<times>\<^sub>a size_assn"
  unfolding partition_pivot_def PR_CONST_def    
  apply (annot_snat_const "TYPE(size_t)")
  by sepref

  

end

(*
subsection \<open>Parameterization\<close>

context parameterized_weak_ordering begin
  thm WO.qsp_next_l_def

  definition qsp_next_l_param :: "'cparam \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where            
    "qsp_next_l_param cparam xs pi li hi \<equiv> doN {
      monadic_WHILEIT (\<lambda>_. True) 
        (\<lambda>li. doN {ASSERT (li\<noteq>pi); pcmp_idxs2 cparam xs li pi}) 
        (\<lambda>li. doN {ASSERT (li<hi); RETURN (li + 1)}) li
    }"  
  
  lemma qsp_next_l_param_refine[refine]: "\<lbrakk>
    (xs',xs)\<in>cdom_list_rel cparam; (p',p)\<in>Id; (i',i)\<in>Id; (h',h)\<in>Id
  \<rbrakk> \<Longrightarrow> qsp_next_l_param cparam xs' p' i' h' \<le>\<Down>nat_rel (WO.ungrd_qsp_next_l_spec cparam xs p i h)"
  proof (goal_cases)
    case 1
    then have "qsp_next_l_param cparam xs' p' i' h' \<le>\<Down>nat_rel (WO.qsp_next_l cparam xs p i h)" 
      unfolding qsp_next_l_param_def WO.qsp_next_l_def
      apply refine_rcg
      by auto
    also note WO.qsp_next_l_refine[param_fo, OF IdI IdI IdI IdI, of cparam xs p i h, THEN nres_relD]
    finally show ?case unfolding PR_CONST_def .
  qed 
  
    
  definition qsp_next_h_param :: "'cparam \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where
    "qsp_next_h_param cparam xs pi hi \<equiv> doN {
      ASSERT (hi>0);
      let hi = hi - 1;
      ASSERT (hi<length xs);
      monadic_WHILEIT (\<lambda>_. True)
        (\<lambda>hi. doN {ASSERT(pi\<noteq>hi); pcmp_idxs2 cparam xs pi hi}) 
        (\<lambda>hi. doN { ASSERT(hi>0); RETURN (hi - 1)}) hi
    }"  

  lemma qsp_next_h_param_refine[refine]: "\<lbrakk>
    (xs',xs)\<in>cdom_list_rel cparam; (p',p)\<in>Id; (h',h)\<in>Id
  \<rbrakk> \<Longrightarrow> qsp_next_h_param cparam xs' p' h' \<le>\<Down>nat_rel (WO.ungrd_qsp_next_h_spec cparam xs p h)"      
  proof goal_cases
    case 1
    then have "qsp_next_h_param cparam xs' p' h' \<le>\<Down>nat_rel (WO.qsp_next_h cparam xs p h)"
      unfolding qsp_next_h_param_def WO.qsp_next_h_def
      apply refine_rcg
      by (auto simp: cdom_list_rel_alt in_br_conv)
    also note WO.qsp_next_h_refine[param_fo, THEN nres_relD]
    finally show ?thesis by simp 
  qed    
    
  definition "qs_partition_param cparam li\<^sub>0 hi\<^sub>0 pi xs\<^sub>0 \<equiv> doN {
    ASSERT (pi < li\<^sub>0 \<and> li\<^sub>0<hi\<^sub>0 \<and> hi\<^sub>0\<le>length xs\<^sub>0);
    
    \<comment> \<open>Initialize\<close>
    li \<leftarrow> qsp_next_l_param cparam xs\<^sub>0 pi li\<^sub>0 hi\<^sub>0;
    hi \<leftarrow> qsp_next_h_param cparam xs\<^sub>0 pi hi\<^sub>0;
    
    ASSERT (li\<^sub>0\<le>hi);
    
    (xs,li,hi) \<leftarrow> WHILEIT 
      (\<lambda>_. True)
      (\<lambda>(xs,li,hi). li<hi) 
      (\<lambda>(xs,li,hi). doN {
        ASSERT(li<hi \<and> li<length xs \<and> hi<length xs \<and> li\<noteq>hi);
        xs \<leftarrow> mop_list_swap xs li hi;
        let li = li + 1;
        li \<leftarrow> qsp_next_l_param cparam xs pi li hi\<^sub>0;
        hi \<leftarrow> qsp_next_h_param cparam xs pi hi;
        RETURN (xs,li,hi)
      }) 
      (xs\<^sub>0,li,hi);
    
    RETURN (xs,li)
  }"  

  lemma qs_partition_param_refine[refine]: "\<lbrakk>
    (li',li)\<in>Id; (hi',hi)\<in>Id; (pi',pi)\<in>Id; (xs',xs)\<in>cdom_list_rel cparam
  \<rbrakk> \<Longrightarrow> qs_partition_param cparam li' hi' pi' xs' 
    \<le> \<Down>(cdom_list_rel cparam \<times>\<^sub>r nat_rel) (WO.qs_partition cparam li hi pi xs)" 
    unfolding qs_partition_param_def WO.qs_partition_def
    supply [refine_dref_RELATES] = RELATESI[of "cdom_list_rel cparam"]
    apply refine_rcg
    apply refine_dref_type
    apply (auto simp: cdom_list_rel_alt in_br_conv)
    done

 definition "move_median_to_first_param cparam ri ai bi ci (xs::'a list) = doN {
    ASSERT (ai \<noteq> bi \<and> ai \<noteq> ci \<and> bi \<noteq> ci \<and> ri \<noteq> ai \<and> ri \<noteq> bi \<and> ri \<noteq> ci);
    if\<^sub>N pcmp_idxs2 cparam xs ai bi then (
      if\<^sub>N pcmp_idxs2 cparam xs bi ci then
        mop_list_swap xs ri bi
      else if\<^sub>N pcmp_idxs2 cparam xs ai ci then
        mop_list_swap xs ri ci
      else 
        mop_list_swap xs ri ai
    ) 
    else if\<^sub>N pcmp_idxs2 cparam xs ai ci then
      mop_list_swap xs ri ai
    else if\<^sub>N pcmp_idxs2 cparam xs bi ci then 
      mop_list_swap xs ri ci
    else 
      mop_list_swap xs ri bi
  }"

  
  (* TODO:Move *)
  lemma mop_list_swap_cdom_refine[refine]: "\<lbrakk>
    (xs',xs)\<in>cdom_list_rel cparam; (i',i)\<in>Id; (j',j)\<in>Id
  \<rbrakk> \<Longrightarrow> mop_list_swap xs' i' j' \<le> \<Down> (cdom_list_rel cparam) (mop_list_swap xs i j)"
    apply simp
    apply refine_rcg
    apply (clarsimp_all simp: cdom_list_rel_def list_rel_imp_same_length)
    apply (parametricity)
    by auto
  
  lemma move_median_to_first_param_refine[refine]: "\<lbrakk>
    (ri',ri)\<in>Id; (ai',ai)\<in>Id; (bi',bi)\<in>Id; (ci',ci)\<in>Id; (xs',xs)\<in>cdom_list_rel cparam 
  \<rbrakk> \<Longrightarrow> move_median_to_first_param cparam ri' ai' bi' ci' xs' 
    \<le> \<Down>(cdom_list_rel cparam) (WO.move_median_to_first cparam ri ai bi ci xs)"
    unfolding move_median_to_first_param_def WO.move_median_to_first_alt
    apply refine_rcg  
    by auto  
    
  definition "partition_pivot_param cparam xs\<^sub>0 l h \<equiv> doN {
    ASSERT (l\<le>h \<and> h\<le>length xs\<^sub>0 \<and> h-l\<ge>4);
    let m = l + (h-l) div 2;
    xs\<^sub>1 \<leftarrow> move_median_to_first_param cparam l (l+1) m (h-1) xs\<^sub>0;
    ASSERT (l<length xs\<^sub>1 \<and> length xs\<^sub>1 = length xs\<^sub>0);
    (xs,m) \<leftarrow> qs_partition_param cparam (l+1) h l xs\<^sub>1;
  
    RETURN (xs,m)
  }"

  lemma partition_pivot_param_refine[refine]: "\<lbrakk> (xs',xs)\<in>cdom_list_rel cparam; (l',l)\<in>Id; (h',h)\<in>Id
    \<rbrakk> \<Longrightarrow> partition_pivot_param cparam xs' l' h' 
        \<le> \<Down>(cdom_list_rel cparam \<times>\<^sub>r nat_rel) (WO.partition_pivot cparam xs l h)"
    unfolding partition_pivot_param_def WO.partition_pivot_def   
    apply refine_rcg
    apply (auto simp: cdom_list_rel_alt in_br_conv)
    done    
        
end


context parameterized_sort_impl_context begin

  (* TODO: Move *)
  abbreviation "arr_assn \<equiv> wo_assn"

  
sepref_register qsp_next_l_param qsp_next_h_param

(* TODO: We can get rid of the length xs restriction: the stopper element will always lie within <h, which is size_t representable! *)
sepref_def qsp_next_l_impl [llvm_inline] is "uncurry4 (PR_CONST qsp_next_l_param)" 
  :: "cparam_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding qsp_next_l_param_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
 
sepref_def qsp_next_h_impl [llvm_inline] is "uncurry3 (PR_CONST qsp_next_h_param)" :: "cparam_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding qsp_next_h_param_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
  
                        
sepref_register qs_partition_param  
sepref_def qs_partition_impl is "uncurry4 (PR_CONST qs_partition_param)" :: "cparam_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d \<rightarrow>\<^sub>a arr_assn \<times>\<^sub>a size_assn"
  unfolding qs_partition_param_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [dest] = slice_eq_mset_eq_length
  by sepref

sepref_register move_median_to_first_param

sepref_def move_median_to_first_param_impl (*[llvm_inline] *)
  is "uncurry5 (PR_CONST move_median_to_first_param)" 
  :: "cparam_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d \<rightarrow>\<^sub>a arr_assn"
  unfolding move_median_to_first_param_def PR_CONST_def
  by sepref  
  
  
sepref_register partition_pivot_param  
sepref_def partition_pivot_impl (*[llvm_inline] *)
  is "uncurry3 (PR_CONST partition_pivot_param)" 
  :: "cparam_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn \<times>\<^sub>a size_assn"
  unfolding partition_pivot_param_def PR_CONST_def    
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
  

end
*)
end                           

