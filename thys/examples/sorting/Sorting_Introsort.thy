section \<open>Introsort (roughly libstdc++ version)\<close>
theory Sorting_Introsort
imports 
  Sorting_Final_insertion_Sort Sorting_Heapsort Sorting_Log2
  Sorting_Quicksort_Partition
 (* Sorting_Strings *)
begin


context weak_ordering begin


  (* Assemble an introsort loop, using the partitioner and heap-sort *)  
  
  definition introsort_aux4 :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list, ecost) nrest"
    where "introsort_aux4 xs l h d \<equiv> RECT' (\<lambda>introsort_aux (xs,l,h,d). doN {
    ASSERT (l\<le>h);
    lxs \<leftarrow> SPECc2 ''sub'' (-) h l; 
    if\<^sub>N SPECc2 ''icmp_slt'' (<) is_threshold lxs then doN {
      if\<^sub>N SPECc2 ''icmp_eq'' (=) d 0 then
        heapsort2 xs l h
      else doN {
        (xs,m)\<leftarrow>partition_pivot xs l h;
        d' \<leftarrow> SPECc2 ''sub'' (-) d 1;
        xs \<leftarrow> introsort_aux (xs,l,m,d');
        xs \<leftarrow> introsort_aux (xs,m,h,d');
        RETURN xs
      }
    }
    else
      RETURN xs
  }) (xs,l,h,d)"


  definition heapsort_time' :: "_  \<Rightarrow> ecost" where
    "heapsort_time' s = lift_acost (heapsort_lbc (s)) 
          + cost ''add'' 1 + cost ''call'' (enat (s) + 2)
          + cost ''icmp_slt'' (enat (s) + 1 + 1 + 1) + cost ''if'' (enat (s) + 1 + 3)
          + cost ''sub'' (enat (s) + 2) + cost ''sift_down'' (enat (s))"

  
lemma heapsort_correct_h:
  fixes xs\<^sub>0 :: "'a list"
    assumes "l\<le>h\<^sub>0" "h\<^sub>0\<le>length xs\<^sub>0"
    shows "heapsort xs\<^sub>0 l h\<^sub>0 \<le> SPEC (\<lambda>xs. slice_eq_mset l h\<^sub>0 xs xs\<^sub>0 \<and> sorted_wrt_lt (\<^bold><) (slice l h\<^sub>0 xs)) (\<lambda>_. heapsort_time' (h\<^sub>0-l))"
  apply(rule order.trans[OF heapsort_correct[OF assms]])
  apply(rule SPEC_leq_SPEC_I) apply simp
  apply(auto simp: heapsort_time_def heapsort_time'_def heapsort_lbc_def lift_acost_propagate
        lift_acost_cost)
  apply sc_solve
  apply safe by auto

lemma wfR''_Rsd_a[simp]: "wfR'' (Rsd_a x)"
  unfolding Rsd_a_def by auto

  

thm heapsort_correct' partition_pivot_correct

text \<open>Here we assemble a Timerefinement from @{term heapsort_TR} and @{term TR_pp}.\<close>

(* TODO: find the right Tia43 *)
definition "Tia43 \<equiv> TId(''eq'':=cost ''icmp_eq'' 1,
          ''lt'':=cost ''icmp_slt'' 1,
        ''partition'':=TR_pp ''partition'',
        ''slice_sort_p'':=
        cost ''call'' (enat 10)
         + cost ''if'' (enat 24) \<^cancel>\<open>
         + cost ''sub'' c
         + cost ''cmpo_v_idx'' d
         + cost ''mul'' e
         + cost ''ofs_ptr'' f
         + cost ''add'' g
         + cost ''cmpo_idxs'' i
         + cost ''udiv'' j
         + cost ''add'' k
         + cost ''icmp_slt'' m
         + cost ''add'' n\<close>)"
 

lemma cost_n_eq_TId_n: "cost n (1::enat) = TId n"
  by(auto simp:  TId_def cost_def zero_acost_def less_eq_acost_def)

lemma wfR''Tia43[simp]: "wfR'' (Tia43)"
  by(auto simp: Tia43_def intro!: wfR''_upd)
lemma spTia43[simp]: "struct_preserving (Tia43)"
  by(auto simp: Tia43_def intro!: struct_preserving_upd_I) 
lemma pcTia43[simp]: 
  "preserves_curr (Tia43) ''sub''"
  "preserves_curr (Tia43) ''icmp_slt''"
  "preserves_curr (Tia43) ''icmp_eq''"
  by(auto simp: Tia43_def preserves_curr_def cost_n_eq_TId_n) 


lemma yeah:
  assumes "Discrete.log (h - l) \<ge> 1" "h-l \<ge> 1"
  shows 
  "timerefineA (heapsort_TR l h)  (cost ''slice_sort'' 1)
      \<le> timerefineA (Tia43)
       (cost ''slice_sort_p'' (enat ((h-l) * Discrete.log (h-l))))"
  unfolding Tia43_def
    unfolding heapsort_TR_def  singleton_heap_context.sift_down3_cost_def heapsort_time_def
  unfolding pp_fun_upd pp_TId_absorbs_right 
  apply(auto simp add: timerefineA_propagate)
  unfolding Rsd_a_def heapsort_lbc_def 
  apply(auto simp:   timerefineA_update_apply_same_cost' lift_acost_cost costmult_cost
                lift_acost_propagate timerefineA_update_cost wfR''_TId intro!: wfR''_upd)
  apply(subst timerefineA_propagate, auto)+
  unfolding singleton_heap_context.sift_down3_cost_def  singleton_heap_context.E_sd3_l_def
  apply(auto simp: costmult_cost costmult_add_distrib lift_acost_propagate lift_acost_cost)
  apply(simp only: add.left_commute add.assoc cost_same_curr_left_add plus_enat_simps)
  apply(simp add: timerefineA_update_apply_same_cost' costmult_cost costmult_add_distrib)
  apply(simp only: add.left_commute)
  apply sc_solve_debug
  apply safe
  subgoal (*if*)  apply(simp add: add_mult_distrib2 add_mult_distrib 
              sc_solve_debug_def numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
    apply(rule order.trans)
     apply(rule add_mono[where b="7 * (h - l) * Discrete.log (h - l)"])
    subgoal using assms by simp
     apply(rule add_mono[where b="7 * (h - l) * Discrete.log (h - l)"])
    subgoal apply simp apply(rule order.trans[where b="h-l"]) apply simp using assms by simp
     apply(rule add_mono[where b="3 * (h - l) * Discrete.log (h - l)" and d="4 * (h - l) * Discrete.log (h - l)"])
    subgoal   using assms by simp
    subgoal using assms by simp
    by linarith
  subgoal (*call*) apply(simp add: add_mult_distrib2 add_mult_distrib 
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
    apply(rule order.trans)
    apply(subst Suc_eq_plus1_left)
     apply(subst Suc_eq_plus1_left)
     apply(rule add_mono[where b="1 * (h - l) * Discrete.log (h - l)"])
    subgoal using assms by simp
     apply(rule add_mono[where b="1 * (h - l) * Discrete.log (h - l)"])
    subgoal using assms by simp
     apply(rule add_mono[where b="1 * (h - l) * Discrete.log (h - l)"])
    subgoal apply simp apply(rule order.trans[where b="h-l"]) apply simp using assms by simp
     apply(rule add_mono[where b="1 * (h - l) * Discrete.log (h - l)"])
    subgoal using assms by simp
     apply(rule add_mono[where b="1 * (h - l) * Discrete.log (h - l)"])
    subgoal using assms by simp
     apply(rule add_mono[where b="1 * (h - l) * Discrete.log (h - l)"])
    subgoal using assms by simp
     apply(rule add_mono[where b="1 * (h - l) * Discrete.log (h - l)"])
    subgoal apply simp apply(rule order.trans[where b="h-l"]) apply simp using assms by simp
     apply(rule add_mono[where b="1 * (h - l) * Discrete.log (h - l)" and d="1 * (h - l) * Discrete.log (h - l)"])
    subgoal apply simp apply(rule order.trans[where b="h-l"]) apply simp using assms by simp
    subgoal   using assms by simp 
    by linarith
  sorry
   
  
lemma yeah': (* i guess h-l must be \<ge> 2 *)
  shows 
  "(h-l)>1 \<Longrightarrow> timerefineA (heapsort_TR l h)  (cost ''slice_sort'' 1)
      \<le> timerefineA (Tia43)
       (cost ''slice_sort_p'' (enat ((h-l) * Discrete.log (h-l))))"
  apply(rule yeah)
  apply auto  
  using Discrete.log.simps by auto  


lemma heapsort_correct'': 
  "\<lbrakk>(xs,xs')\<in>Id; (l,l')\<in>Id; (h,h')\<in>Id; lxs=(h'-l'); h'-l'>1\<rbrakk> \<Longrightarrow> heapsort2 xs l h \<le>
      \<Down>Id (timerefine (Tia43) (slice_sort_specT (cost ''slice_sort_p'' (enat ((\<lambda>n. n * Discrete.log n) lxs))) (\<^bold><) xs' l' h'))"
  apply(rule order.trans)
   apply(rule heapsort_correct') apply auto [3] 
  unfolding slice_sort_spec_def slice_sort_specT_def
  apply(rule ASSERT_D3_leI)
  apply(simp add: SPEC_timerefine_conv)
  apply(rule SPEC_leq_SPEC_I)
   apply simp 
  apply(rule yeah') apply simp
  done


lemma
  fixes R :: "_ \<Rightarrow> ('a, enat) acost"
  assumes "x \<le> timerefine R y"
    "R \<le> R'" "wfR'' R'"
  shows "x \<le> timerefine R' y"
  apply(rule order.trans)
   apply(rule assms)
  apply(rule timerefine_R_mono_wfR'') 
   apply fact+ done

lemma
  fixes R :: "_ \<Rightarrow> ('a, enat) acost"
  shows "R' \<le> sup R' R"
  by simp


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

lemma timerefine_supI:
  fixes R :: "_ \<Rightarrow> ('a, enat) acost"
  assumes "x \<le> timerefine R y"
    "R \<le> R'" "wfR'' R'" "wfR'' R"
  shows "x \<le> timerefine (sup R' R) y"
  apply(rule order.trans)
   apply(rule assms)
  apply(rule timerefine_R_mono_wfR'') 
  apply(rule wfR''_supI)
   apply fact+ apply(rule sup_ge2) done


lemma
  fixes R :: "_ \<Rightarrow> ('a, enat) acost"
  shows "sup TId R = R"
  apply(rule ext)
  apply simp
  subgoal for x apply(cases "R x") unfolding TId_def sup_acost_def apply simp 
    apply(rule ext) apply auto
    oops


lemma
  fixes R :: "_ \<Rightarrow> ('b, enat) acost"
  shows "sup (R(m:=x)) TId = (sup R TId)(m:=sup x (acostC (\<lambda>y. (if m=y then 1 else 0))))"
  unfolding TId_def  by auto
lemma
  fixes R :: "_ \<Rightarrow> ('b, enat) acost"
  shows "sup (R(m:=x)) TId = (sup R TId)(m:=sup x (acostC (\<lambda>y. (if m=y then 1 else 0))))"
  unfolding TId_def  by auto

lemma pullin_left:
  fixes R :: "_ \<Rightarrow> ('b, enat) acost"
  shows "sup (R(m:=x)) R' = (sup R R')(m:=sup x (R' m))"
  apply(rule ext) by auto


lemma "sup (TId(''a'':=cost ''n'' (2::enat))) (TId(''a'':=cost ''n'' 3, ''b'':=cost ''b'' 3)) = g"
  apply(auto simp: pullin_left)
  oops



thm partition_pivot_correct_flexible 
lemma partition_pivot_correct':
  "\<lbrakk>(xs,xs')\<in>Id; (l,l')\<in>Id; (h,h')\<in>Id\<rbrakk> 
  \<Longrightarrow> partition_pivot xs l h \<le> \<Down>Id (timerefine (Tia43) (partition3_spec xs' l' h'))"
  apply(rule partition_pivot_correct_flexible)
  unfolding Tia43_def
  apply (auto )
  done


thm slice_sort_specT_def slice_sort_spec_def

  lemma introsort_aux4_refine: "introsort_aux4 xs l h d \<le> \<Down>Id (timerefine (Tia43) ((introsort_aux3 (\<lambda>n. n * Discrete.log n) xs l h d)))"
    unfolding introsort_aux4_def introsort_aux3_def 
    supply conc_Id[simp del]
    apply (refine_rcg RECT'_refine_t bindT_refine_conc_time_my_inres SPECc2_refine' SPECc2_refine MIf_refine
            heapsort_correct'' partition_pivot_correct')
    apply refine_mono
    apply refine_dref_type
    apply (simp_all add: inres_SPECc2) 
    apply(auto simp: Tia43_def )
    done

lemma nlogn_mono:
  "\<And>x y. x \<le> y \<Longrightarrow> x * Discrete.log x \<le> y * Discrete.log y"
    apply(rule mult_mono) apply simp apply (rule log_mono[THEN monoD]) apply simp apply simp apply simp done
lemma nlogn_sums: 
  "a + b \<le> c \<Longrightarrow> a * Discrete.log a + b * Discrete.log b \<le> c * Discrete.log c"
  apply(rule order.trans)
   apply(rule add_mono[where b="a * Discrete.log c" and d="b * Discrete.log c"])
  subgoal using log_mono[THEN monoD] by simp
  subgoal using log_mono[THEN monoD] by simp
  apply(subst add_mult_distrib[symmetric])
  by simp
 
thm introsort_aux3_correct 

definition "bla d lxs = (pp (pp Tia43 (TId(''list_append'' := 0, ''list_length'' := cost ''sub'' 1))) (TId(''slice_part_sorted'' := introsort_aux_cost (\<lambda>n. n * Discrete.log n) (lxs, d))))"

lemma "bla d lxs = gg"
  unfolding bla_def 
  apply(simp add: pp_fun_upd pp_TId_absorbs_right)
  oops

lemma introsort_aux4_correct: "introsort_aux4 xs l h d \<le> \<Down> Id (timerefine (bla d (h-l)) (slice_part_sorted_spec xs l h))"
  apply(rule order.trans)
   apply(rule introsort_aux4_refine)
  apply(rule order.trans)
   apply simp apply(rule timerefine_mono2)
  apply simp
   apply(rule introsort_aux3_correct)
  subgoal apply(intro nlogn_mono) by simp
  subgoal apply(intro nlogn_sums) by simp
  apply (simp add: timerefine_iter2)
  apply(subst timerefine_iter2)
  subgoal
    apply(simp add: pp_fun_upd pp_TId_absorbs_right)
    apply(intro wfR''_upd)
    by simp
  subgoal by auto
  unfolding bla_def apply simp
  done

lemma TR_sps_important2:
  assumes "TR ''slice_part_sorted'' = bla d (h - l) ''slice_part_sorted''"
  shows "timerefine TR (slice_part_sorted_spec xs l h) = (timerefine (bla d (h-l)) (slice_part_sorted_spec xs l h))"
  unfolding slice_part_sorted_spec_def
  apply(cases "l \<le> h \<and> h \<le> length xs"; auto)
  apply(simp only: SPEC_timerefine_conv)
  apply(rule SPEC_cong, simp)
  apply(rule ext)
  apply(simp add: norm_tr)
  apply(subst assms(1))
  apply simp
  done

lemma introsort_aux4_correct_flexible:
  assumes "TR ''slice_part_sorted'' = bla d (h - l) ''slice_part_sorted''"
  shows "introsort_aux4 xs l h d \<le> \<Down> Id (timerefine TR (slice_part_sorted_spec xs l h))"
  apply(subst TR_sps_important2[where TR=TR, OF assms])
  apply(rule introsort_aux4_correct)
  done
  

  definition "introsort4 xs l h \<equiv> doN {
    ASSERT(l\<le>h);
    hml \<leftarrow> SPECc2 ''sub'' (-) h l;
    if\<^sub>N SPECc2 ''icmp_slt'' (<) 1 hml then doN {
      xs \<leftarrow> introsort_aux4 xs l h (Discrete.log (h-l)*2);
      xs \<leftarrow> final_insertion_sort2 xs l h;
      RETURN xs
    } else RETURN xs
  }"  

lemma wfR''_bla[simp]: " wfR'' (bla d xs)"
  unfolding bla_def
  by(auto simp add:  pp_fun_upd pp_TId_absorbs_right intro!: wfR''_upd) 

thm introsort_aux4_correct

lemmas final_insertion_sort2_correct_flexible = final_insertion_sort2_correct

thm introsort_aux4_correct_flexible
thm final_insertion_sort2_correct_flexible

abbreviation "TR_is d s == TId(''lt'':=cost ''icmp_slt'' 1, ''slice_part_sorted'':= bla d s ''slice_part_sorted'',''slice_sort'' := fi2_cost s)"

lemma pc_bla[simp]:
  "preserves_curr (bla d hl) ''sub''"
  "preserves_curr (bla d hl) ''icmp_slt''"
  by(auto simp: pcTia43[unfolded preserves_curr_def] pp_fun_upd pp_TId_absorbs_right  bla_def preserves_curr_def cost_n_eq_TId_n) 

lemma pc_TR_is[simp]:
  "preserves_curr (TR_is d hl) ''sub''"
  "preserves_curr (TR_is d hl) ''icmp_slt''"
  by(auto simp: preserves_curr_def cost_n_eq_TId_n) 


lemma wfR''_TR_is[simp]: "wfR'' (TR_is d hl)"
  by (auto intro!: wfR''_upd)

lemma sp_TR_is[simp]:
  "struct_preserving (TR_is d hl)"
  by (auto intro!: struct_preserving_upd_I) 


lemma sp_bla[simp]:
  "struct_preserving (bla d hl)"
  by (auto simp: pp_fun_upd pp_TId_absorbs_right  bla_def intro!: struct_preserving_upd_I)  

  lemma introsort4_refine: "introsort4 xs l h \<le> \<Down>Id (timerefine (TR_is (Discrete.log (h-l)*2) (h-l)) (introsort3 xs l h))"
    unfolding introsort4_def introsort3_def 
    supply conc_Id[simp del]
    apply (refine_rcg SPECc2_refine' SPECc2_refine bindT_refine_conc_time_my_inres MIf_refine
                introsort_aux4_correct_flexible final_insertion_sort2_correct_flexible )
    apply refine_dref_type                                          
    by auto 

  thm introsort4_refine introsort3_correct

  (* lemmas introsort4_correct = order_trans[OF introsort4_refine introsort3_correct] *)

end

lemma introsort_depth_limit_in_bounds_aux: (* TODO: Move depth-computation into own (inline) function *)
  assumes "n < max_snat N" "1<N" shows "Discrete.log (n) * 2 < max_snat N"
proof (cases "n=0")
  case True thus ?thesis using assms by auto
next
  case [simp]: False  
  have ?thesis if "Discrete.log (n) < max_snat (N-1)"
    using that \<open>1<N\<close> unfolding max_snat_def
    by (metis nat_mult_power_less_eq pos2 semiring_normalization_rules(33))
  moreover have "Discrete.log (n) < max_snat (N-1)"
    apply (rule discrete_log_ltI)
    using assms apply (auto simp: max_snat_def)
    by (smt Suc_diff_Suc leI le_less_trans n_less_equal_power_2 nat_power_less_imp_less not_less_eq numeral_2_eq_2 numeral_2_eq_2 zero_order(3))
  ultimately show ?thesis .
qed  
  


context sort_impl_context begin


thm partition_pivot2_refines heapsort3_refine


lemma TR_sup_Tid: "sup TId TId = TId"
  by simp


lemma pullin_right:
  fixes R :: "_ \<Rightarrow> ('b, enat) acost"
  shows "sup R' (R(m:=x)) = (sup R' R)(m:=sup (R' m) x)"
  apply(rule ext) by auto


  definition introsort_aux5 :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list, ecost) nrest"
    where "introsort_aux5 xs l h d \<equiv> RECT' (\<lambda>introsort_aux (xs,l,h,d). doN {
    ASSERT (l\<le>h);
    lxs \<leftarrow> SPECc2 ''sub'' (-) h l; 
    if\<^sub>N SPECc2 ''icmp_slt'' (<) is_threshold lxs then doN {
      if\<^sub>N SPECc2 ''icmp_eq'' (=) d 0 then
        heapsort3 xs l h
      else doN {
        (xs,m)\<leftarrow>partition_pivot2 xs l h;
        d' \<leftarrow> SPECc2 ''sub'' (-) d 1;
        xs \<leftarrow> introsort_aux (xs,l,m,d');
        xs \<leftarrow> introsort_aux (xs,m,h,d');
        RETURN xs
      }
    }
    else
      RETURN xs
  }) (xs,l,h,d)"


lemma pc_TR_cmp_swap: "x\<noteq>''cmp_idxs'' \<Longrightarrow> x\<noteq>''cmpo_idxs'' \<Longrightarrow> x\<noteq>''cmpo_v_idx'' \<Longrightarrow> x\<noteq>''list_swap''
  \<Longrightarrow> preserves_curr TR_cmp_swap x"
  apply(intro preserves_curr_other_updI)
  by auto


  lemma introsort_aux5_refine: "introsort_aux5 xs l h d \<le> \<Down>Id (timerefine (TR_cmp_swap) ((introsort_aux4 xs l h d)))"
    unfolding introsort_aux4_def introsort_aux5_def 
    supply conc_Id[simp del]
    apply (refine_rcg RECT'_refine_t bindT_refine_conc_time_my_inres SPECc2_refine' MIf_refine
            heapsort3_refine partition_pivot2_refines)
    apply refine_mono
    apply refine_dref_type
    apply (auto simp add: inres_SPECc2 intro!: pc_TR_cmp_swap) 
    done





sepref_register introsort_aux5
sepref_def introsort_aux_impl is "uncurry3 (PR_CONST introsort_aux5)" :: "(arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  unfolding introsort_aux5_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [[goals_limit = 1]]
  apply sepref_dbg_preproc
     apply sepref_dbg_cons_init
     apply sepref_dbg_id
  apply sepref_dbg_monadify
     apply sepref_dbg_opt_init

  using hn_RECT_wiewirshabenwollen

      apply sepref_dbg_trans_keep

  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints 
  done
  
  
  
sepref_register introsort4
sepref_def introsort_impl is "uncurry2 (PR_CONST introsort4)" :: "(arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  unfolding introsort4_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [intro!] = introsort_depth_limit_in_bounds_aux 
  by sepref

  
lemma introsort4_refine_ss_spec: "(PR_CONST introsort4, slice_sort_spec (\<^bold><))\<in>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>\<langle>Id\<rangle>nres_rel"  
  using introsort4_correct by (auto intro: nres_relI)
  
theorem introsort_impl_correct: "(uncurry2 introsort_impl, uncurry2 (slice_sort_spec (\<^bold><))) \<in> arr_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"  
  using introsort_impl.refine[FCOMP introsort4_refine_ss_spec] .
  
  
end


(*
context parameterized_weak_ordering begin
  (* TODO: Move *)
  lemmas heapsort_param_refine'[refine] = heapsort_param_refine[unfolded heapsort1.refine[OF WO.weak_ordering_axioms, symmetric]]
  
  
  definition introsort_aux_param :: "'cparam \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list nres" where 
    "introsort_aux_param cparam xs l h d \<equiv> RECT (\<lambda>introsort_aux (xs,l,h,d). doN {
    ASSERT (l\<le>h);
    if h-l > is_threshold then doN {
      if d=0 then
        heapsort_param cparam xs l h
      else doN {
        (xs,m)\<leftarrow>partition_pivot_param cparam xs l h;
        xs \<leftarrow> introsort_aux (xs,l,m,d-1);
        xs \<leftarrow> introsort_aux (xs,m,h,d-1);
        RETURN xs
      }
    }
    else
      RETURN xs
  }) (xs,l,h,d)"


  lemma introsort_aux_param_refine[refine]: 
    "\<lbrakk> (xs',xs)\<in>cdom_list_rel cparam; (l',l)\<in>Id; (h',h)\<in>Id; (d',d)\<in>Id
    \<rbrakk> \<Longrightarrow> introsort_aux_param cparam xs' l' h' d' \<le>\<Down>(cdom_list_rel cparam) (WO.introsort_aux4 cparam xs l h d)"
    unfolding introsort_aux_param_def WO.introsort_aux4_def 
    supply [refine_dref_RELATES] = RELATESI[of "cdom_list_rel cparam"]
    apply (refine_rcg)
    apply refine_dref_type
    apply simp_all 
    done

  definition "introsort_param cparam xs l h \<equiv> doN {
    ASSERT(l\<le>h);
    if h-l>1 then doN {
      xs \<leftarrow> introsort_aux_param cparam xs l h (Discrete.log (h-l)*2);
      xs \<leftarrow> final_insertion_sort_param cparam xs l h;
      RETURN xs
    } else RETURN xs
  }"  

  lemma introsort_param_refine: 
    "\<lbrakk> (xs',xs)\<in>cdom_list_rel cparam; (l',l)\<in>Id; (h',h)\<in>Id
    \<rbrakk> \<Longrightarrow> introsort_param cparam xs' l' h' \<le> \<Down>(cdom_list_rel cparam) (WO.introsort4 cparam xs l h)"
    unfolding introsort_param_def WO.introsort4_def
    apply (refine_rcg)
    by auto

      
  lemma introsort_param_correct: 
    assumes "(xs',xs)\<in>Id" "(l',l)\<in>Id" "(h',h)\<in>Id"
    shows "introsort_param cparam xs' l' h' \<le> pslice_sort_spec cdom pless cparam xs l h"
  proof -
    note introsort_param_refine
    also note WO.introsort4_correct
    also note slice_sort_spec_xfer
    finally show ?thesis 
      unfolding pslice_sort_spec_def
      apply refine_vcg
      using assms unfolding cdom_list_rel_alt
      by (simp add: in_br_conv)
    
  qed
  
  lemma introsort_param_correct': 
    shows "(PR_CONST introsort_param, PR_CONST (pslice_sort_spec cdom pless)) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    using introsort_param_correct 
    apply (intro fun_relI nres_relI) 
    by simp
  
    
    
    
end

context parameterized_sort_impl_context begin


sepref_register introsort_aux_param
sepref_def introsort_aux_param_impl is "uncurry4 (PR_CONST introsort_aux_param)" 
  :: "cparam_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  unfolding introsort_aux_param_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
  
  
sepref_register introsort_param
sepref_def introsort_param_impl is "uncurry3 (PR_CONST introsort_param)" :: "cparam_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  unfolding introsort_param_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [intro!] = introsort_depth_limit_in_bounds_aux 
  by sepref


lemma introsort_param_impl_correct: "(uncurry3 introsort_param_impl, uncurry3 (PR_CONST (pslice_sort_spec cdom pless)))
        \<in> cparam_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  using introsort_param_impl.refine[FCOMP introsort_param_correct'] .
  
end
*)


end

