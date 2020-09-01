theory Sorting_Final_insertion_Sort
imports Sorting_Quicksort_Scheme Sorting_Unguarded_Insertion_Sort
begin

context weak_ordering begin

  definition "final_insertion_sort xs \<equiv> doN {
    ASSERT (1 < length xs);
    if length xs \<le> is_threshold then
      gen_insertion_sort_guarded 1 (length xs) xs
    else doN {
      xs \<leftarrow> gen_insertion_sort_guarded 1 is_threshold xs;
      gen_insertion_sort_unguarded is_threshold is_threshold (length xs) xs
    }
  }"  


  lemma has_stopperI:
    assumes "i<length xs" "j'<i" "i-j'\<le>N" "\<forall>j\<le>j'. \<not>xs!i\<^bold><xs!j"
    shows "has_stopper N xs i"
    using assms unfolding has_stopper_def by blast
  
  
  lemma part_sorted_guardedI:
    assumes S: "part_sorted_wrt (le_by_lt (\<^bold><)) N xs" and B: "N\<le>i" "i<length xs"  
    shows "has_stopper N xs i"  
  proof -  
    from S have "N\<noteq>0" \<open>i\<noteq>0\<close> using B by (cases N; auto)+
    
    
    from S obtain ss where SL: "is_slicing N xs ss" and SORTED: "sorted_wrt (slice_LT (le_by_lt (\<^bold><))) ss" unfolding part_sorted_wrt_def by auto

    have XS_EQ: "xs = concat ss" using SL unfolding is_slicing_def by auto
    
    define xi where "xi = xs!i"
    
    obtain xs1 xs2 where XSEQ2: "xs=xs1@xi#xs2" and LEN_XS1: "length xs1 = i"
      unfolding xi_def using id_take_nth_drop[OF \<open>i<length xs\<close>] B by simp
    
    have [simp]: "ss\<noteq>[]"
      using XS_EQ assms(3) by auto
    have "concat ss = xs1@xi#xs2" by (simp add: XS_EQ[symmetric] XSEQ2)
    then obtain ss1 ssi1 ssi2 ss2 where 1: "ss = ss1 @ (ssi1 @ ssi2) # ss2" "xs1 = concat ss1 @ ssi1" "xi # xs2 = ssi2 @ concat ss2"
      by (auto dest: concat_eq_appendD)

    have SS1_NGT: "\<forall>x\<in>set (concat ss1). \<forall>y\<in>set (ssi1@ssi2). \<not>x \<^bold>> y"  
      using SORTED by (auto simp add: "1"(1) sorted_wrt_append slice_LT_def le_by_lt_def)
      
    have XS1_NGT: "\<forall>x\<in>set xs1. \<forall>y\<in>set (concat ss2). \<not>x \<^bold>> y"  
      using SORTED by (auto simp add: "1" sorted_wrt_append slice_LT_def le_by_lt_def)
      
      
    from SL 1 have SLI_BND: "length (ssi1@ssi2) \<le> N" unfolding is_slicing_def by auto
          
    show ?thesis proof (cases ssi2)  
      case [simp]: Nil 
      
      obtain ssi2' ss2' where [simp]: "ss2 = (xi#ssi2') # ss2'" using 1 
        apply simp
        apply (cases ss2; simp)
        subgoal for ss2_1 ss2_r 
          using SL unfolding is_slicing_def
          apply (cases ss2_1; simp)
          done
        done
      
      show ?thesis 
        apply (rule has_stopperI[where j'="length xs1 - 1"])
        subgoal by fact
        subgoal using \<open>i \<noteq> 0\<close> \<open>length xs1 = i\<close> by auto
        subgoal
          using LEN_XS1 \<open>N \<noteq> 0\<close> by linarith
        subgoal
          apply (auto simp add: XS_EQ 1 simp flip: LEN_XS1)
          apply (simp add: nth_append split: if_splits)
          subgoal for j using XS1_NGT nth_mem unfolding 1(2) by fastforce
          subgoal for j using XS1_NGT nth_mem unfolding 1(2) by fastforce
          done
        done
        
    next
      case (Cons _ ssi2') hence [simp]: "ssi2 = xi#ssi2'" using 1 by auto
      
      have "ss1\<noteq>[]" proof
        assume [simp]: "ss1=[]" 
        from 1 have "xs1 = ssi1" by simp
        hence "length ssi1 = i" using \<open>length xs1 = i\<close> by simp
        hence "length (ssi1@ssi2) > i" by simp
        moreover note SLI_BND
        ultimately show False using \<open>N\<le>i\<close> by auto
      qed
      
      have 11: "length (concat ss1) \<le> i" using \<open>length xs1 = i\<close> by (simp add: 1)
      
      have 12: "i < N + length (concat ss1)"
        by (metis "1"(2) "11" SLI_BND \<open>length xs1 = i\<close> add_diff_cancel_left' add_lessD1 le_eq_less_or_eq length_append length_greater_0_conv less_add_same_cancel1 less_diff_conv2 list.simps(3) local.Cons)
      
      show ?thesis 
        apply (rule has_stopperI[where j'="length (concat ss1) - 1"])  
        subgoal using assms(3) by auto
        subgoal using "1"(2) \<open>i \<noteq> 0\<close> \<open>length xs1 = i\<close> by auto
        subgoal using 12 by linarith
        subgoal 
          apply (auto simp add: XS_EQ 1 simp flip: LEN_XS1)
          apply (simp add: nth_append split: if_splits)
          subgoal for j using SS1_NGT using nth_mem by fastforce
          subgoal using "12" assms(2) by linarith
          done
        done
    qed
  qed        
      
  lemma mset_slice_eq_xform_aux:
    assumes "mset (slice 0 N xs') = mset (slice 0 N xs)"
    assumes "j < N" "N < length xs" "length xs' = length xs"
    obtains jj where "jj<N" "xs'!j = xs!jj"
    using assms by (auto simp: list_eq_iff_nth_eq set_slice_conv dest!: mset_eq_setD; auto) 
  
  lemma transfer_stopper_over_initial_sorting:
    assumes "has_stopper N xs i"
    assumes B: "length xs' = length xs" "0<N" "N \<le> i" "i < length xs"
    assumes DEQ: "drop N xs' = drop N xs" 
    assumes SORTED: "sort_spec (\<^bold><) (slice 0 N xs) (slice 0 N xs')" 
    shows "has_stopper N xs' i"
    using assms[unfolded sort_spec_def has_stopper_def]
    apply clarify
    subgoal for j'
      apply (cases "j'<N")
      subgoal
        Idee: Das Segment xs[0..<N] enthaelt mindestens j' Stopper. (Alles \<le> j' sind Stopper)
        Nach dem Sortieren: Der 'letzte' Stopper muss an Index \<ge>j' kommen, alles davor auch Stopper da sortiert.
        \<longrightarrow> Index j' immernoch ein Stopper
        
        
      
       sorry
      subgoal
        apply (rule has_stopperI[where j'=j'])
        apply auto
        subgoal for j
          apply (subgoal_tac "xs'!i = xs!i")
          subgoal
            apply (cases "j<N")
            subgoal by (erule (1) mset_slice_eq_xform_aux[where j=j]; simp)
            subgoal by (smt assms(6) drop_eq_mono hd_drop_conv_nth leI le_eq_less_or_eq le_less_trans)
            done 
          subgoal by (metis assms(4) drop_eq_mono hd_drop_conv_nth)
          done
        done
      done
    done  
      
        apply (cases "j<N")
        apply (auto simp: list_eq_iff_nth_eq)
        subgoal sorry
        
        by (smt assms(6) drop_eq_mono hd_drop_conv_nth leI le_eq_less_or_eq le_less_trans)
    
  
  
  
  lemma transfer_guard_over_initial_sorting:
    assumes PS: "part_sorted_wrt (le_by_lt (\<^bold><)) N xs"
    assumes B: "0<N" "N \<le> i" "i < length xs"
    shows "has_stopper N xs i"
    using assms unfolding has_stopper_def part_sorted_wrt_def is_slicing_def 
  
    
  
  lemma transfer_guard_over_initial_sorting:
    assumes PS: "part_sorted_wrt (le_by_lt (\<^bold><)) N xs"
    assumes B: "length xs' = length xs" "0<N" "N \<le> i" "i < length xs"
    assumes DEQ: "drop N xs' = drop N xs" 
    assumes SORTED: "sort_spec (\<^bold><) (slice 0 N xs) (slice 0 N xs')" 
    shows "has_stopper N xs' i"
  proof -
  
  
  
  
    
  lemma transfer_guard_over_initial_sorting:
    assumes PS: "part_sorted_wrt (le_by_lt (\<^bold><)) n xs"
    assumes B: "length xs' = length xs" "0<n" "n \<le> i" "i < length xs"
    assumes DEQ: "drop n xs' = drop n xs" 
    assumes SORTED: "sort_spec (\<^bold><) (slice 0 n xs) (slice 0 n xs')" 
    assumes LT: "xs' ! i \<^bold>< xs' ! 0" 
    shows False
  proof -
    from part_sorted_guardedI[OF PS \<open>n\<le>i\<close> \<open>i < length xs\<close>] have GUARD: "xs!0 \<^bold>\<le> xs!i"
      by (auto simp: le_by_lt)
  
    have [simp]: "xs!i = xs'!i" using B DEQ by (metis atLeastLessThan_iff conv_idxs_to_drop_eq)
      
    have "xs!0 \<in># mset (slice 0 n xs)" using B
      apply (auto simp: Misc.slice_def)
      by (metis atLeast0LessThan image_eqI le_less_trans lessThan_iff less_imp_le_nat nth_image)
    hence "xs!0 \<in># mset (slice 0 n xs')" using SORTED unfolding sort_spec_def by auto 
    then obtain j where "j<n" and [simp]: "xs!0=xs'!j" using B by (auto simp: in_set_conv_nth slice_nth)
    have "xs'!0 \<^bold>\<le> xs'!j" using SORTED B \<open>j<n\<close>
      apply (cases "j=0")
      apply simp
      unfolding sort_spec_def by (auto simp: le_by_lt sorted_wrt_iff_nth_less slice_nth)
    then show False using LT GUARD
      apply simp
      using local.trans wo_leD by blast
      
  qed
   

  lemma final_insertion_sort_correct: 
    "\<lbrakk>part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold xs; 1 < length xs\<rbrakk> \<Longrightarrow> final_insertion_sort xs \<le> SPEC (sort_spec (\<^bold><) xs)"
    unfolding final_insertion_sort_def
    apply (refine_vcg gen_insertion_sort_correct[THEN order_trans])
    apply simp_all
    subgoal apply (rule sorted_wrt01) by auto  
    subgoal
      unfolding slice_sort_spec_def apply refine_vcg
      apply (auto simp: ) using slice_complete by metis
    subgoal apply (rule sorted_wrt01) by auto  
    subgoal
      unfolding slice_sort_spec_def 
      apply (refine_vcg gen_insertion_sort_correct[THEN order_trans])
      apply (simp_all)
      subgoal by (simp add: Misc.slice_def sort_spec_def) 
      subgoal for xs'
        apply (clarsimp)
        by (auto intro!: transfer_guard_over_initial_sorting)
      subgoal unfolding slice_sort_spec_def apply refine_vcg
        apply (auto simp: sort_spec_def)
        apply (metis Misc.slice_def append_take_drop_id drop0 drop_take slice_complete union_code)
        by (metis slice_complete)
      done                
    done    
  *)
  definition "final_insertion_sort2 xs l h \<equiv> undefined"
   (* doN {
    ASSERT (l<h);
    if h-l \<le> is_threshold then
      gen_insertion_sort2 True l (l+1) h xs
    else doN {
      xs \<leftarrow> gen_insertion_sort2 True l (l+1) (l+is_threshold) xs;
      gen_insertion_sort2 False l (l+is_threshold) h xs
    }
  }"  
    
  lemma final_insertion_sort2_refine: "\<lbrakk>(xsi,xs) \<in> slicep_rel l h\<rbrakk> 
    \<Longrightarrow> final_insertion_sort2 xsi l h \<le> \<Down>(slice_rel xsi l h) (final_insertion_sort xs)"  
    unfolding final_insertion_sort2_def final_insertion_sort_def
    apply (refine_rcg gen_insertion_sort2_refine)
    apply clarsimp_all
    apply (auto simp: slicep_rel_def idx_shift_rel_def) [7]
    apply (subst slice_rel_rebase, assumption)
    apply (refine_rcg gen_insertion_sort2_refine)
    apply (auto simp: slice_rel_alt idx_shift_rel_def slicep_rel_def)
    done
  
    
    *)
    
  lemma final_insertion_sort2_correct: 
    assumes [simplified, simp]: "(xs',xs)\<in>Id" "(l',l)\<in>Id" "(h',h)\<in>Id"   
    shows "final_insertion_sort2 xs' l' h' \<le> \<Down>Id (timerefine (TId(''slice_sort'':=(enat (h-l+1)) *m cost ''call'' 1)) (final_sort_spec xs l h))"
    sorry
  (*
  proof (simp,rule le_nofailI)
    assume "nofail (final_sort_spec xs l h)"
    hence PS: "part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold (slice l h xs)"
      and LB: "h-l>1" "h \<le> length xs"
      unfolding final_sort_spec_def slice_sort_spec_def by (auto simp add: refine_pw_simps)
  
    from LB have LENGT1: "1 < length (slice l h xs)" by auto
      
    
    have SLR: "(xs, slice l h xs) \<in> slicep_rel l h" using LB
      by (auto simp: slicep_rel_def)
    
    note final_insertion_sort2_refine[OF SLR]
    also note final_insertion_sort_correct[OF PS LENGT1]
    also note slice_sort_spec_refine_sort'_sym[OF SLR refl refl refl] 
    also have "slice_sort_spec (\<^bold><) xs l h \<le> final_sort_spec xs l h"
      unfolding final_sort_spec_def using PS LB by simp
    finally show "final_insertion_sort2 xs l h \<le> final_sort_spec xs l h" .
  qed
  *)
  
end
  (*
context sort_impl_context begin
  sepref_register final_insertion_sort2  
  sepref_def final_insertion_sort_impl is "uncurry2 (PR_CONST final_insertion_sort2)" 
    :: "(woarray_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a woarray_assn elem_assn"
    unfolding final_insertion_sort2_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref

end *)
(*
context parameterized_weak_ordering begin  
  definition "final_insertion_sort_param cparam xs l h \<equiv> doN {
    ASSERT (l<h);
    if h-l \<le> is_threshold then
      gen_insertion_sort_param True cparam l (l+1) h xs
    else doN {
      xs \<leftarrow> gen_insertion_sort_param True cparam l (l+1) (l+is_threshold) xs;
      gen_insertion_sort_param False cparam l (l+is_threshold) h xs
    }
  }"  

  lemma final_insertion_sort_param_refine[refine]: "\<lbrakk>
    (l',l)\<in>Id; (h',h)\<in>Id; (xs',xs)\<in>cdom_list_rel cparam
  \<rbrakk> \<Longrightarrow> final_insertion_sort_param cparam xs' l' h' 
    \<le> \<Down>(cdom_list_rel cparam) (WO.final_insertion_sort2 cparam xs l h)"  
    unfolding final_insertion_sort_param_def WO.final_insertion_sort2_def
    apply refine_rcg
    apply auto
    done
  
end

context parameterized_sort_impl_context begin

  sepref_register final_insertion_sort_param
  sepref_def final_insertion_sort_param_impl is "uncurry3 (PR_CONST final_insertion_sort_param)" 
    :: "cparam_assn\<^sup>k *\<^sub>a wo_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a wo_assn"
    unfolding final_insertion_sort_param_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref

end
*)

end
