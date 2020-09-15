section \<open>Introsort (roughly libstdc++ version)\<close>
theory Sorting_Introsort
imports 
  Sorting_Final_insertion_Sort Sorting_Heapsort Sorting_Log2
   "Imperative_HOL_Time.Asymptotics_1D"
   "HOL-Real_Asymp.Real_Asymp"
  Sorting_Quicksort_Partition
 (* Sorting_Strings *)
begin



lemma wfR''_Rsd_a[simp]: "wfR'' (Rsd_a x)"
  unfolding Rsd_a_def by auto
context weak_ordering begin


  (* Assemble an introsort loop, using the partitioner and heap-sort *)  
  
  definition introsort_aux4 :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list, ecost) nrest"
    where "introsort_aux4 xs l h d \<equiv> RECT' (\<lambda>introsort_aux (xs,l,h,d). doN {
    ASSERT (l\<le>h);
    lxs \<leftarrow> SPECc2 ''sub'' (-) h l; 
    if\<^sub>N SPECc2 ''icmp_slt'' (<) is_threshold lxs then doN {
      if\<^sub>N SPECc2 ''icmp_eq'' (=) d 0 then
        mop_call (heapsort2 xs l h)
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


  

thm heapsort_correct' partition_pivot_correct

text \<open>Here we assemble a Timerefinement from @{term heapsort_TR} and @{term TR_pp}.\<close>

definition "Tia43 \<equiv> TId(''eq'':=cost ''icmp_eq'' 1,
          ''lt'':=cost ''icmp_slt'' 1,
        ''partition'':=TR_pp ''partition'',
        ''slice_sort_p'':=
        cost ''call'' (enat 10)
         + cost ''if'' (enat 24) 
         + cost ''sub'' (enat 34)
         + cost ''ofs_ptr'' (enat 20) 
         + cost ''mul'' (enat 14) 
         + cost ''cmpo_v_idx'' (enat 6)
         + cost ''add'' (enat 42)
         + cost ''cmpo_idxs'' (enat 4)
         + cost ''udiv'' (enat 16)
         + cost ''and'' (enat 6)
         + cost ''icmp_slt'' (enat 21)
         + cost ''list_swap'' (enat 1)
         + cost ''load'' (enat 10)
         + cost ''store'' (enat 10))"
 

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


lemma 
  assumes "1 \<le> Discrete.log (h - l)" "1 \<le> h - l"
  shows 
    yeah_aux1: "x \<le> y \<Longrightarrow> (h - l) + x \<le> (h - l) * Discrete.log (h - l) + y"
  and  yeah_aux2: "x \<le> y \<Longrightarrow> p * (h - l) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  yeah_aux3: "x \<le> y \<Longrightarrow> (h - (1+l)) + x \<le> (h - l) * Discrete.log (h - l) + y"
  and  yeah_aux4: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow> p * (h - (1+l)) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  yeah_aux5: "x \<le> y \<Longrightarrow> (Discrete.log (h - l) * (h - (1+l))) + x \<le> (h - l) * Discrete.log (h - l) + y"
  and  yeah_aux6: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow> p * (Discrete.log (h - l) * (h - (1+l))) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  yeah_aux13: "x \<le> y \<Longrightarrow> ((h - l) * Discrete.log (h - l)) + x \<le> (h - l) * Discrete.log (h - l) + y"
  and  yeah_aux14: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow> p * ((h - l) * Discrete.log (h - l)) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  yeah_aux15: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow> (h - l) * (p *  Discrete.log (h - l)) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  yeah_aux7: "x \<le> y \<Longrightarrow> ((h - (1+l)) * Discrete.log (h - l)) + x \<le> (h - l) * Discrete.log (h - l) + y"
  and  yeah_aux8: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow> p * ((h - (1+l)) * Discrete.log (h - l)) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  yeah_aux9: "x \<le> y \<Longrightarrow> (Discrete.log (h - l)) + x \<le> (h - l) * Discrete.log (h - l) + y"
  and  yeah_aux10: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow> p * ( Discrete.log (h - l)) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  yeah_aux11: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow>(h - (1+l)) * ( p * Discrete.log (h - l)) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  yeah_aux12: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow>(h - l) * ( p * Discrete.log (h - l)) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  yeah_aux_end: "x \<le> y \<Longrightarrow> q>0 \<Longrightarrow> q + x \<le> q * (h - l) * Discrete.log (h - l) + y"
  subgoal
    apply(rule add_mono)
    subgoal using assms by simp 
    by simp
  subgoal
    apply(rule add_mono)
    subgoal using assms by simp 
    by simp
  subgoal
    apply(rule add_mono)
    subgoal apply(rule order.trans[where b="h-l"]) apply simp using assms by simp
    by simp
  subgoal
    apply(rule add_mono)
    subgoal apply simp apply(rule order.trans[where b="h-l"]) apply simp using assms by simp
    by simp
  subgoal
    apply(rule add_mono)
    subgoal using assms by auto
    by simp
  subgoal
    apply(rule add_mono)
    subgoal using assms by auto
    by simp
  subgoal
    apply(rule add_mono)
    subgoal using assms by auto
    by simp
  subgoal
    apply(rule add_mono)
    subgoal using assms by auto
    by simp
  subgoal
    apply(rule add_mono)
    subgoal using assms by auto
    by simp
  subgoal
    apply(rule add_mono)
    subgoal using assms by auto
    by simp
  subgoal
    apply(rule add_mono)
    subgoal using assms by auto
    by simp
  subgoal
    apply(rule add_mono)
    subgoal using assms by auto
    by simp
  subgoal
    apply(rule add_mono)
    subgoal using assms by auto
    by simp
  subgoal
    apply(rule add_mono)
    subgoal using assms by auto
    by simp
  subgoal
    apply(rule add_mono)
    subgoal using assms by auto
    by simp
  subgoal
    apply(rule add_mono)
    subgoal using assms by auto
    by simp
  done

definition "STOP = (0::nat)"
lemma yeah_aux0: "a+(STOP::nat)\<le> b\<Longrightarrow> a \<le> b"
  by simp

lemma yeah_stop: "STOP \<le> 0"
  unfolding STOP_def by simp

lemmas yeah_aux = yeah_aux1 yeah_aux2 yeah_aux3 yeah_aux4 yeah_aux5 yeah_aux6
      yeah_aux13 yeah_aux14 yeah_aux15
      yeah_aux7 yeah_aux8
       yeah_aux9 yeah_aux10 yeah_aux11 yeah_aux12 
      yeah_aux_end

method yeah_solver uses assms  = (simp only: Suc_eq_plus1_left,
                    rule yeah_aux0,
                    simp only: add.assoc,
                    rule order.trans,
                    (rule yeah_aux[OF assms])+,
                    rule yeah_stop,
                    (simp_all, linarith?))

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
    apply(simp only: Suc_eq_plus1_left)
    apply(rule yeah_aux0)
    apply(simp only: add.assoc)
    apply(rule order.trans)
     apply(rule yeah_aux[OF assms])+
        apply(rule yeah_stop)
    by (simp_all, linarith?)
  subgoal (*call*) apply(simp add: add_mult_distrib2 add_mult_distrib 
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
    apply(simp only: Suc_eq_plus1_left)
    apply(rule yeah_aux0)
    apply(simp only: add.assoc)
    apply(rule order.trans)
     apply(rule yeah_aux[OF assms])+
        apply(rule yeah_stop)
    by (simp_all, linarith?)
  subgoal (* sub *) apply(simp add: add_mult_distrib2 add_mult_distrib 
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
    apply(simp only: Suc_eq_plus1_left)
    apply(rule yeah_aux0)
    apply(simp only: add.assoc)
    apply(rule order.trans)
     apply(rule yeah_aux[OF assms])+
        apply(rule yeah_stop)
    by (simp_all, linarith?)
  subgoal (* ''ofs_ptr'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
    apply(simp only: Suc_eq_plus1_left)
    apply(rule yeah_aux0)
    apply(simp only: add.assoc)
    apply(rule order.trans)
     apply(rule yeah_aux[OF assms])+
        apply(rule yeah_stop)
    by (simp_all, linarith?)
  subgoal (* ''mul'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
    apply(simp only: Suc_eq_plus1_left)
    apply(rule yeah_aux0)
    apply(simp only: add.assoc)
    apply(rule order.trans)
     apply(rule yeah_aux[OF assms])+
        apply(rule yeah_stop)
    by (simp_all, linarith?)
  subgoal (* ''cmpo_v_idx'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
    apply(simp only: Suc_eq_plus1_left)
    apply(rule yeah_aux0)
    apply(simp only: add.assoc)
    apply(rule order.trans)
     apply(rule yeah_aux[OF assms])+
        apply(rule yeah_stop)
    by (simp_all, linarith?)
  subgoal (* ''add'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
    apply(simp only: Suc_eq_plus1_left)
    apply(rule yeah_aux0)
    apply(simp only: add.assoc)
    apply(rule order.trans)
     apply(rule yeah_aux[OF assms])+
        apply(rule yeah_stop)
    by (simp_all, linarith?)
  subgoal (* ''cmpo_idxs'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
    apply(simp only: Suc_eq_plus1_left)
    apply(rule yeah_aux0)
    apply(simp only: add.assoc)
    apply(rule order.trans)
     apply(rule yeah_aux[OF assms])+
        apply(rule yeah_stop)
    by (simp_all, linarith?)
  subgoal (* ''udiv'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
    apply(simp only: Suc_eq_plus1_left)
    apply(rule yeah_aux0)
    apply(simp only: add.assoc)
    apply(rule order.trans)
     apply(rule yeah_aux[OF assms])+
        apply(rule yeah_stop)
    by (simp_all, linarith?)
  subgoal (* ''icmp_slt'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
    apply(simp only: Suc_eq_plus1_left)
    apply(rule yeah_aux0)
    apply(simp only: add.assoc)
    apply(rule order.trans)
     apply(rule yeah_aux[OF assms])+
        apply(rule yeah_stop)
    by (simp_all, linarith?)
  subgoal (* ''and'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
    apply(simp only: Suc_eq_plus1_left)
    apply(rule yeah_aux0)
    apply(simp only: add.assoc)
    apply(rule order.trans)
     apply(rule yeah_aux[OF assms])+
        apply(rule yeah_stop)
    by (simp_all, linarith?)
  subgoal (* ''store'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
    apply(simp only: Suc_eq_plus1_left)
    apply(rule yeah_aux0)
    apply(simp only: add.assoc)
    apply(rule order.trans)
     apply(rule yeah_aux[OF assms])+
        apply(rule yeah_stop)
    by (simp_all, linarith?)
  subgoal (* ''load'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
    apply(simp only: Suc_eq_plus1_left)
    apply(rule yeah_aux0)
    apply(simp only: add.assoc)
    apply(rule order.trans)
     apply(rule yeah_aux[OF assms])+
        apply(rule yeah_stop)
    by (simp_all, linarith?)
  subgoal (* ''list_swap'' *)
      using assms apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
      done
  done
   
  
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
    supply [refine] = mop_call_refine
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
  apply(cases "l < h \<and> h \<le> length xs"; auto)
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
      loghml \<leftarrow> mop_call (SPECT [Discrete.log hml \<mapsto> log2_iter_cost hml]);
      d \<leftarrow> SPECc2 ''mul'' (*) loghml 2;
      xs \<leftarrow> introsort_aux4 xs l h d;
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

abbreviation "TR_is d s == TId(''prepare_cost'':=log2_iter_cost s+cost ''call'' 1 +cost ''mul'' 1,
            ''lt'':=cost ''icmp_slt'' 1,''slice_sort'' := fi2_cost s, 
            ''slice_part_sorted'':= bla d s ''slice_part_sorted'')"

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

(*TODO: move*)

lemma SPECc1_alt: "SPECc1 name aop = ( (\<lambda>a. consume (RETURNT (aop a)) (cost name 1)))"
  unfolding SPECc1_def consume_def by(auto simp: RETURNT_def intro!: ext)

  lemma introsort4_refine: "introsort4 xs l h \<le> \<Down>Id (timerefine (TR_is (Discrete.log (h-l)*2) (h-l)) (introsort3 xs l h))"
    unfolding introsort4_def introsort3_def 
    supply conc_Id[simp del]
    apply(subst (3) SPECc2_alt) 
    unfolding mop_call_def
    apply(subst consume_RETURNT[symmetric])
    apply normalize_blocks
    apply (refine_rcg SPECc2_refine' SPECc2_refine bindT_refine_conc_time_my_inres MIf_refine
                introsort_aux4_correct_flexible final_insertion_sort2_correct_flexible
               consumea_refine   )
    apply refine_dref_type                                          
    by (auto simp: norm_cost inres_SPECc2)

  thm introsort4_refine introsort3_correct

abbreviation "TR_is4 lmh \<equiv> pp (TR_is (Discrete.log (lmh)*2) (lmh)) (TId(''slice_sort'' := introsort3_cost))" 

lemma "introsort4 xs l h \<le> \<Down> Id (timerefine (TR_is4 (h-l)) (slice_sort_spec (\<^bold><) xs l h))"
  apply(rule order.trans)
   apply(rule introsort4_refine)
  apply simp
      apply(subst timerefine_iter2[symmetric])
      subgoal by(auto intro!: wfR''_upd)
      subgoal by(auto simp: norm_pp intro!: wfR''_upd)
      apply(rule timerefine_mono2)
      subgoal by(auto intro!: wfR''_upd)
      apply(rule order.trans)
      apply(rule introsort3_correct)
      apply simp
      done

lemma "\<Down> Id (timerefine (TR_is4 (h-l)) (slice_sort_spec (\<^bold><) xs l h))
    = slice_sort_specT G (\<^bold><) xs l h"
  apply(cases "l \<le> h \<and> h \<le> length xs")
   apply (auto simp: slice_sort_spec_def slice_sort_specT_def SPEC_timerefine_conv )
  apply(rule SPEC_cong)
   apply simp
  apply(rule ext)
  apply (simp add: norm_cost norm_pp)
  unfolding introsort3_cost_def bla_def TR_is_insert3_def Tia43_def
    cost_insert_guarded_def cost_insert_def
    cost_is_insert_step_def cost_is_insert_guarded_step_def
    introsort_aux_cost_def
  apply (simp add: norm_cost norm_pp)
  apply(subst timerefineA_propagate, intro wfR''_upd wfR''_TId)+
  apply (simp add: norm_cost norm_pp)
  unfolding move_median_to_first_cost_def
  apply (simp add: norm_cost norm_pp)
  oops
  (* TODO: the cost of insort contains a term
        2 ^ (Discrete.log (h - l) * 2)
       This means it is (h-l)^2 ?
      why do we choose d := log (h-l) * 2 actually?
    In wikipedia they say:
      "The factor 2 in the maximum depth is arbitrary; it can be tuned for practical performance."

      Either my proof is not detailed enough, or the latter statement is wrong.
  
      If we only look for comparisons then, this term does not occur.
      But building together the results in the quicksort scheme does incurr costs dependent on that.

    *)
    
    

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
        mop_call (heapsort3 xs l h)
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


lemma introsort_aux5_refine: "(xs,xs')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> (h,h')\<in>Id \<Longrightarrow> (d,d')\<in>Id 
    \<Longrightarrow> introsort_aux5 xs l h d \<le> \<Down>Id (timerefine (TR_cmp_swap) ((introsort_aux4 xs' l' h' d')))"
    unfolding introsort_aux4_def introsort_aux5_def 
    supply conc_Id[simp del]
    apply (refine_rcg RECT'_refine_t bindT_refine_conc_time_my_inres SPECc2_refine' MIf_refine
            heapsort3_refine partition_pivot2_refines  mop_call_refine)
    apply refine_mono
    apply refine_dref_type
    apply (auto simp add: inres_SPECc2 intro!: pc_TR_cmp_swap) 
    done





sepref_register introsort_aux5
sepref_def introsort_aux_impl is "uncurry3 (PR_CONST introsort_aux5)" :: "(arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  unfolding introsort_aux5_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [[goals_limit = 1]]
  by sepref


  definition "introsort5 xs l h \<equiv> doN {
    ASSERT(l\<le>h);
    hml \<leftarrow> SPECc2 ''sub'' (-) h l;
    if\<^sub>N SPECc2 ''icmp_slt'' (<) 1 hml then doN {
      loghml \<leftarrow> mop_call (log2_iter hml);
      d \<leftarrow> SPECc2 ''mul'' (*) loghml 2;
      xs \<leftarrow> introsort_aux5 xs l h d;
      xs \<leftarrow> final_insertion_sort3 xs l h;
      RETURN xs
    } else RETURN xs
  }"  



  lemma introsort5_refine: "introsort5 xs l h \<le> \<Down>Id (timerefine (TR_cmp_swap) ((introsort4 xs l h )))"
    unfolding introsort4_def introsort5_def 
    supply conc_Id[simp del]
    apply (refine_rcg bindT_refine_conc_time_my_inres SPECc2_refine' MIf_refine
            introsort_aux5_refine final_insertion_sort3_refines
              log2_iter_refine_TR_cmp_swap mop_call_refine )
    apply refine_dref_type
    apply (auto simp add: inres_SPECc2 intro!: pc_TR_cmp_swap) 
    done
 
  thm sepref_fr_rules

lemma mop_call_same_result:
  fixes m :: "(_,(_,enat) acost)nrest"
  shows "RETURN x \<le> mop_call m \<Longrightarrow> RETURN x \<le> m"
  unfolding mop_call_def consume_def RETURNT_def
  apply(auto split: if_splits nrest.splits simp: le_fun_def)
  subgoal for x2 apply(cases "x2 x") apply auto 
    by (simp add: ecost_nneg)
  done

lemma AAA: (* TODO: Move depth-computation into own (inline) function *)
  assumes "hml < max_snat N" "RETURNTecost xb \<le> mop_call (log2_iter hml)" "1<N" shows "xb * 2 < max_snat N"
proof -
  from order_trans[OF mop_call_same_result[OF assms(2)] log2_iter_refine]
  have xb: "xb = Discrete.log hml"
    unfolding  RETURNT_def
    by (auto split: if_splits simp: le_fun_def)

  show ?thesis
    unfolding xb
    apply(rule introsort_depth_limit_in_bounds_aux)
    using assms by auto
qed
 


sepref_register introsort5
sepref_def introsort_impl is "uncurry2 (PR_CONST introsort5)" :: "(arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  unfolding introsort5_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [intro!] = AAA 
  by sepref

  (*
lemma introsort4_refine_ss_spec: "(PR_CONST introsort4, slice_sort_spec (\<^bold><))\<in>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>\<langle>Id\<rangle>nres_rel"  
  using introsort4_correct by (auto intro: nres_relI)
  
theorem introsort_impl_correct: "(uncurry2 introsort_impl, uncurry2 (slice_sort_spec (\<^bold><))) \<in> arr_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"  
  using introsort_impl.refine[FCOMP introsort4_refine_ss_spec] .
  
  *)

                                   
thm introsort5_refine introsort4_refine introsort3_correct

schematic_goal introsort5_correct:
  "introsort5 xs l h \<le> \<Down> Id (timerefine ?TR (slice_sort_spec (\<^bold><) xs l h))"
  apply(rule order.trans)
  apply(rule introsort5_refine)
  apply (rule nrest_Rel_mono)
  
  apply(rule order.trans)
  apply(rule timerefine_mono2) apply(rule wfR''E)
   apply(rule introsort4_refine)
                       
  apply(rule order.trans)
  apply(rule timerefine_mono2) apply(rule wfR''E)
  apply (rule nrest_Rel_mono)
  apply(rule timerefine_mono2) apply(rule wfR''_TR_is)
   apply(rule introsort3_correct)

  apply(simp add: conc_Id)
  apply (subst timerefine_iter2)  
    apply(rule wfR''E)
   apply(rule wfR''_TR_is)

  apply (subst timerefine_iter2)  
  apply(rule wfR''_ppI)
    apply(rule wfR''E)
    apply(rule wfR''_TR_is)
  subgoal apply auto done
  apply(rule order.refl)
  done 


concrete_definition introsort5_TR is introsort5_correct uses "_ \<le> \<Down> Id (timerefine \<hole> _) "
print_theorems

thm introsort5_TR.refine
lemma argh_foo: "(timerefine (introsort5_TR l h) (slice_sort_spec (\<^bold><) xs l h))
    = slice_sort_specT (introsort5_TR l h ''slice_sort'') (\<^bold><) xs l h"
  unfolding slice_sort_spec_def slice_sort_specT_def
  apply(cases "l \<le> h \<and> h \<le> length xs")
   apply(auto simp: SPEC_timerefine_conv)
  apply(rule SPEC_cong) apply simp
  by (auto simp: timerefineA_cost)


thm introsort5_TR.refine[unfolded argh]

lemma leq_sc_l_TERMINATE_special:
  "P \<Longrightarrow> leq_sidecon (cost n x) 0 0 0 0 (cost n x + 0) P"
   
  unfolding leq_sidecon_def by (simp add: cost_zero)

lemma leq_sc_l_DONE_special:
  "leq_sidecon 0 l 0 0 0 (bs3+0) P \<Longrightarrow> leq_sidecon (cost n x) l 0 0 0 ((cost n x + bs3) + 0) P"
   
  unfolding leq_sidecon_def apply (simp add: cost_zero)
  apply(rule add_mono) by auto

lemma leq_sc_l_NEXT_ROW_special:
  "leq_sidecon (cost n x) 0 ls 0 0 bs P \<Longrightarrow> leq_sidecon 0 ((cost n x)+ls) 0 0 0 bs P"
  unfolding leq_sidecon_def by (simp add: cost_zero) 


schematic_goal ub_introsort5: "timerefineA (introsort5_TR l h) (cost ''slice_sort'' 1) \<le> ?x"
  unfolding introsort5_TR_def introsort3_cost_def
  apply(simp add: norm_pp norm_cost )
  apply(subst timerefineA_propagate, (auto intro!: wfR''_upd)[1])+ 
  apply(simp add: norm_pp norm_cost )
  unfolding log2_iter_cost_def TR_is_insert3_def bla_def Tia43_def introsort_aux_cost_def
      cost_insert_guarded_def cost_is_insert_guarded_step_def
      cost_insert_def cost_is_insert_step_def move_median_to_first_cost_def
  apply(simp add: norm_pp norm_cost )
  apply(subst timerefineA_propagate, (auto intro!: wfR''_upd)[1])+ 
  apply(simp add: norm_pp norm_cost )
  unfolding cmpo_v_idx2'_cost_def cmp_idxs2'_cost_def myswap_cost_def cmpo_idxs2'_cost_def
  apply(simp add: norm_pp norm_cost )
  apply(simp add: add.commute add.left_commute)
  apply(simp add: cost_same_curr_left_add cost_same_curr_add) 
  apply(simp add: add.assoc add.commute add.left_commute)
  apply(simp add: cost_same_curr_left_add cost_same_curr_add) 
  apply(simp add: add.assoc add.commute add.left_commute)
  
  apply ( (simp only: add.assoc)?; rule leq_sc_init, (simp only: add.assoc)?)
  apply ( ((rule leq_sc_l_SUCC leq_sc_l_FAIL )+)?,
            ((rule leq_sc_l_DONE_special, rule leq_sc_l_NEXT_ROW_special)
              | (rule  leq_sc_l_TERMINATE_special))  )+ 
  by simp


concrete_definition introsort5_acost is ub_introsort5 uses "_ \<le> \<hole>"
print_theorems

schematic_goal iii: "introsort5_acost x y = lift_acost ?y"
  unfolding introsort5_acost_def
  apply(simp add: numeral_eq_enat one_enat_def)
  unfolding lift_acost_cost[symmetric]  lift_acost_propagate[symmetric]
  apply(rule refl)
  done
concrete_definition introsort5_cost is iii uses "_ = lift_acost \<hole>"
print_theorems
  

lemmas introsort_rule' = hn_refine_result[OF introsort_impl.refine[to_hnr], unfolded PR_CONST_def APP_def, OF 
      introsort5_TR.refine ]
lemma intro_rule: "hn_refine (hn_ctxt arr_assn a ai \<and>* hn_val snat_rel ba bia \<and>* hn_val snat_rel b bi)
       (introsort_impl ai bia bi)
       (hn_invalid arr_assn a ai \<and>* hn_val snat_rel ba bia \<and>* hn_val snat_rel b bi) (hr_comp arr_assn Id)
 (timerefine (introsort5_TR ba b) (slice_sort_spec (\<^bold><) a ba b))"
  apply(rule introsort_rule')
  apply(rule attains_sup_sv) by simp

lemmas pff = intro_rule[unfolded slice_sort_spec_def SPEC_REST_emb'_conv,  THEN ht_from_hnr]

thm llvm_htriple_more_time[OF introsort5_acost.refine pff, unfolded introsort5_cost.refine  ]



lemma Sum_any_cost2: "Sum_any (the_acost (cost n x)) = x"
  unfolding cost_def by (simp add: zero_acost_def)

definition "Padad a b = (a=b)"

thm introsort5_cost_def[no_vars]

definition "introsort_cost3 s \<equiv>
cost ''mul'' (Suc (s * Discrete.log s * 14)) +
(cost ''ofs_ptr'' (1241 + (108 * (s * Discrete.log s) + 68 * s)) +
 (cost ''add'' (48 * (s * Discrete.log s) + (21 + (s + Discrete.log s))) +
  (cost ''store'' (612 + (34 * s + 54 * (s * Discrete.log s))) +
   (cost ''sub'' (35 * s + (596 + 44 * (s * Discrete.log s))) +
    (cost ''load'' (629 + (34 * s + 54 * (s * Discrete.log s))) +
     (cost ''if'' (40 * (s * Discrete.log s) + (633 + (Discrete.log s + 20 * s))) +
      (cost lt_curr_name (306 + (17 * s + 20 * (s * Discrete.log s))) +
       (cost ''and'' (s * Discrete.log s * 6) +
        (cost ''icmp_slt'' (20 + (2 * s + (25 * (s * Discrete.log s) + Discrete.log s))) +
         (cost ''udiv'' (Suc (18 * (s * Discrete.log s) + Discrete.log s)) +
          (cost ''call'' (343 + (22 * (s * Discrete.log s) + (19 * s + Discrete.log s))) + (cost ''icmp_eq'' (289 + (s + Discrete.log s * 2 * s)) + cost ''icmp_sle'' (Suc 0)))))))))))))" 
 
lemma 35: "introsort_cost3 (h-l) = introsort5_cost l h" 
  unfolding introsort_cost3_def introsort5_cost_def by (auto simp: algebra_simps)


lemma "ba \<le> b \<and> b \<le> length a \<Longrightarrow>
llvm_htriple ($lift_acost (introsort_cost3 (b-ba)) \<and>* hn_ctxt arr_assn a ai \<and>* hn_val snat_rel ba bia \<and>* hn_val snat_rel b bi) (introsort_impl ai bia bi)
 (\<lambda>r. (\<lambda>s. \<exists>x. (\<up>(length x = length a \<and> take ba x = take ba a \<and> drop b x = drop b a \<and> sort_spec (\<^bold><) (slice ba b a) (slice ba b x)) \<and>* hr_comp arr_assn Id x r) s) \<and>*
      hn_invalid arr_assn a ai \<and>* hn_val snat_rel ba bia \<and>* hn_val snat_rel b bi)"
  apply(rule llvm_htriple_more_time[OF introsort5_acost.refine pff, unfolded introsort5_cost.refine 35[symmetric] ])
  by simp

lemma PadadI: "Padad a a"
  unfolding Padad_def
  by simp

schematic_goal Sum_any_calc: "Sum_any (the_acost (introsort_cost3 s)) = ?x"
  unfolding Padad_def[symmetric]
  unfolding introsort_cost3_def 
  apply(simp add: the_acost_propagate add.assoc) 
  apply(subst Sum_any.distrib;  ( auto simp only: Sum_any_cost 
          intro!: finite_sum_nonzero_cost finite_sum_nonzero_if_summands_finite_nonzero))+
  apply(rule PadadI)
  done


end 

(* TODO: there is a problem with auto2 in a context *)
concrete_definition blubb is sort_impl_context.Sum_any_calc uses "_ = \<hole>"

lemma "blubb n = 4693 + 5 *  Discrete.log n + 231 * n + 455 * (n * Discrete.log n)"
  unfolding blubb_def
  apply (simp add: algebra_simps)
  done

(* by Manuel Eberl *)
lemma dlog[asym_bound]:  "(\<lambda>x. real (Discrete.log x)) \<in> \<Theta>(\<lambda>x. ln (real x))"
proof -
  have "(\<lambda>x. real (Discrete.log x))  \<in> \<Theta>(\<lambda>n. real (nat \<lfloor>log 2 (real n)\<rfloor>))"
    by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of 0]])
       (auto simp: Discrete.log_altdef)
  also have "(\<lambda>n. real (nat \<lfloor>log 2 (real n)\<rfloor>)) \<in> \<Theta>(\<lambda>x. ln (real x))"
    by real_asymp
  finally show ?thesis .
qed
 

lemma "(\<lambda>n. real (n* Discrete.log n)) \<in> \<Theta>(\<lambda>n. (real n)* (ln (real n)))"
  apply auto2
  done

lemma "(\<lambda>x. real (x + Suc (x * 14) + 10) ) \<in> \<Theta>(\<lambda>n. (real n))"
  unfolding Suc_eq_plus1_left
  apply simp
  apply auto2 done

lemma "(\<lambda>x. real (blubb x)) \<in> \<Theta>(\<lambda>n. (real n)*(ln (real n)))"
  unfolding blubb_def
  unfolding Suc_eq_plus1_left
  apply simp
  by auto2


thm Sum_any.distrib

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




