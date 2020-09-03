theory Sorting_Unguarded_Insertion_Sort
imports Sorting_Setup Sorting_Partially_Sorted
begin


(* TODO: Move *)


text \<open>the time bound T needs to be agnostic of the length of the array.\<close>
lemma mop_eo_extract_slice_refine: 
  shows "\<lbrakk> (i, i') \<in> idx_shift_rel l; (xs, xs') \<in> slice_rel xs\<^sub>0 l h\<rbrakk>
       \<Longrightarrow> mop_eo_extract (\<lambda>_. T) xs i \<le> \<Down> (Id \<times>\<^sub>r slice_rel xs\<^sub>0 l h) (timerefine TId (mop_eo_extract (\<lambda>_. T) xs' i'))"  
  by (auto intro!: refine0 simp: idx_shift_rel_def slice_rel_def in_br_conv take_map drop_map slice_nth slice_upd_sym algebra_simps)
  
lemma mop_eo_set_slice_refine: "\<lbrakk>(i, i') \<in> idx_shift_rel l; (xs, xs') \<in> slice_rel xs\<^sub>0 l h; (v,v')\<in>Id\<rbrakk> 
      \<Longrightarrow> mop_eo_set (\<lambda>_. T) xs i v \<le> \<Down> (slice_rel xs\<^sub>0 l h) (timerefine TId (mop_eo_set (\<lambda>_. T) xs' i' v'))"  
  by (auto intro!: refine0 simp: idx_shift_rel_def slice_rel_def in_br_conv take_map drop_map slice_nth slice_upd_sym algebra_simps)
  
lemma mop_to_eo_conv_slice_refine: "\<lbrakk>(xs, xs') \<in> slice_rel xs\<^sub>0 l h; (i, i') \<in> idx_shift_rel l\<rbrakk>
    \<Longrightarrow> mop_to_eo_conv xs \<le> \<Down> (slice_rel (map Some xs\<^sub>0) l h) (timerefine TId (mop_to_eo_conv xs'))"  
  by (auto intro!: refine0 simp: mop_to_eo_conv_def idx_shift_rel_def slice_rel_def in_br_conv slice_map take_map drop_map)  
  
lemma mop_to_wo_conv_slice_refine: "\<lbrakk>wfR'' E; (xs, xs') \<in> slice_rel (map Some xs\<^sub>0) l h\<rbrakk> \<Longrightarrow> mop_to_wo_conv xs \<le> \<Down> (slice_rel xs\<^sub>0 l h) (timerefine E (mop_to_wo_conv xs'))"
  apply (simp add: mop_to_wo_conv_def)
  apply (intro refine0)
  subgoal
    apply (simp add: slice_rel_def in_br_conv)
    apply (auto simp: in_set_conv_nth slice_nth list_eq_iff_nth_eq algebra_simps)
    by (metis Groups.add_ac(2) add_diff_inverse_nat less_diff_conv)
  subgoal by simp
  subgoal by (simp add: lift_acost_zero)
  subgoal  
    by (auto simp: slice_rel_def in_br_conv drop_map take_map slice_map)
  done


context weak_ordering begin
  lemma mop_cmp_v_idx_slice_refine: "\<lbrakk> (xs, xs') \<in> slice_rel xs\<^sub>0 l h; (i, i') \<in> idx_shift_rel l; (v,v')\<in>Id \<rbrakk>
    \<Longrightarrow> mop_cmpo_v_idx T xs v i \<le> \<Down> bool_rel (timerefine TId (mop_cmpo_v_idx T xs' v' i'))"
    supply [simp del] = conc_Id
    by (auto intro!: refine0 simp: idx_shift_rel_def slice_rel_def in_br_conv slice_nth algebra_simps)
end  



  context weak_ordering begin

  
    definition "is_insert_spec_aux xs i xs' \<equiv> 
      \<exists>i'\<le>i.
        i<length xs
      \<and> (length xs' = length xs) 
      \<and> (\<forall>j\<in>{0..<i'}. xs'!j=xs!j)
      \<and> (xs'!i' = xs!i)
      \<and> (\<forall>j\<in>{i'<..i}. xs'!j = xs!(j-1) \<and> xs!i\<^bold><xs'!j)
      \<and> (\<forall>j\<in>{i<..<length xs}. xs'!j = xs!j)
      \<and> (i'>0 \<longrightarrow> \<not>(xs!i \<^bold>< xs'!(i'-1)) )
      "
      
    lemma is_insert_spec_aux_imp_sorted:
      "\<lbrakk>is_insert_spec_aux xs i xs'; sorted_wrt_lt (\<^bold><) (take i xs)\<rbrakk> 
        \<Longrightarrow> sorted_wrt_lt (\<^bold><) (take (i+1) xs')"  
      (* TODO: Clean up this mess! *)
      apply (subgoal_tac "i<length xs")
      unfolding sorted_wrt_iff_nth_less le_by_lt_def
      subgoal
        apply clarsimp
        unfolding is_insert_spec_aux_def
        apply (clarsimp;safe)
        apply (smt greaterThanAtMost_iff less_trans linorder_neqE_nat nat_Suc_less_le_imp nat_le_Suc_less_imp nz_le_conv_less unfold_lt_to_le zero_order(3))
        by (smt One_nat_def add_diff_cancel_left' atLeast0LessThan greaterThanAtMost_iff itrans le_less lessThan_iff less_Suc_eq_0_disj less_trans linorder_neqE_nat not_less_eq plus_1_eq_Suc unfold_lt_to_le wo_leI)
      subgoal
        using is_insert_spec_aux_def by blast
      done    
    
    (* TODO: Add type constraint to definition *)  
    abbreviation monadic_WHILEIET :: 
      "('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> (char list, nat) acost) \<Rightarrow> ('b \<Rightarrow> (bool, (char list, enat) acost) nrest) \<Rightarrow> ('b \<Rightarrow> ('b, (char list, enat) acost) nrest) \<Rightarrow> 'b \<Rightarrow> ('b, (char list, enat) acost) nrest"
      where "monadic_WHILEIET I E b f s \<equiv> NREST.monadic_WHILEIET I E b f s"
      
    definition "cost_is_insert_step :: (char list, nat) acost \<equiv> cost ''list_set'' 1 + (cost ''list_get'' 1 + (cost ''call'' 1 + (cost ''mop_cmp_v_idx'' 1 + cost ''sub'' 1 + cost ''if'' 1) + cost ''sub'' 1))"  
      
    definition is_insert_unguarded :: "nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "is_insert_unguarded N xs i \<equiv> doN {
      \<^cancel>\<open>(*ASSERT (\<exists>guard_idx. guard_idx<i \<and> \<not>xs!i\<^bold><xs!guard_idx);*)\<close>
      ASSERT (i<length xs);
      x \<leftarrow> mop_list_getN xs i;
    
      (xs,i)\<leftarrow>monadic_WHILEIET
        (\<lambda>(xs',i'). 
          i'>0 \<and> i-i'\<le>N \<and> i'\<le>i \<and> length xs'=length xs
        \<and> (\<forall>j\<in>{0..i'}. xs'!j = xs!j)  
        \<and> (\<forall>j\<in>{i'<..i}. xs'!j = xs!(j-1) \<and> x\<^bold><xs'!j)  
        \<and> (\<forall>j\<in>{i<..<length xs}. xs'!j=xs!j)
        )
        (\<lambda>(xs,i'). (N - (i-i')) *m cost_is_insert_step) 
        (\<lambda>(xs,i). (doN { 
          t\<^sub>2 \<leftarrow> SPECc2 ''sub'' (-) i 1; mop_cmp_v_idx (cost ''mop_cmp_v_idx'' 1) xs x t\<^sub>2
        }))
        (\<lambda>(xs,i). doN {
          ASSERT (i>0 \<and> i<length xs);
          i' \<leftarrow> SPECc2 ''sub'' (-) i 1;
          x \<leftarrow> mop_list_getN xs i';
          xs \<leftarrow> mop_list_setN xs i x;
          RETURNT (xs,i')
        }) (xs,i);
    
      xs \<leftarrow> mop_list_setN xs i x;  
      
      RETURN xs
    }"

    
    definition "has_stopper N xs i \<equiv> i<length xs \<and> (\<exists>j'<i. i-j'\<le>N \<and> (\<forall>j\<le>j'. \<not>xs!i\<^bold><xs!j))"
    
    definition "is_insert_spec_unguarded N xs i \<equiv> doN {
      ASSERT (has_stopper N xs i);
      SPEC (is_insert_spec_aux xs i) (\<lambda>_. cost ''is_insert'' 1)
    }"  
    
    (* TODO: Move. DUP! *)
    lemma if_rule: "(c \<Longrightarrow> x \<le> a) \<Longrightarrow> (~c \<Longrightarrow> x \<le> b) \<Longrightarrow> x \<le> (if c then a else b)"
      by auto        

  lemma lift_acost_propagate_minus: "lift_acost (t-t') = lift_acost t - lift_acost t' "
    unfolding lift_acost_def by (cases t; cases t'; auto)
      
  (* TODO: N \<rightarrow> N-1 ?*)  
  definition "cost_insert N \<equiv> 
    (lift_acost (N *m cost_is_insert_step) +
      cost ''list_set'' 1 + (cost ''mop_cmp_v_idx'' 1 + cost ''sub'' 1 + cost ''if'' 1 + (cost ''list_get'' 1 + cost ''call'' 1)))"
    
      
    definition "cost_is_insert_guarded_step :: (char list, nat) acost \<equiv>
      cost ''list_set'' 1 + (cost ''list_get'' 1 + (cost ''call'' 1 + (cost ''mop_cmp_v_idx'' 1 + (cost ''if'' 1 + (0 + cost ''icmp_eq'' 1) + cost ''sub'' 1) + cost ''if'' 1) + cost ''sub'' 1))"
    
    definition "cost_insert_guarded N \<equiv> 
      lift_acost (N *m cost_is_insert_guarded_step) +
        cost ''list_set'' 1 + cost ''mop_cmp_v_idx'' 1 + cost ''sub'' 1 + cost ''if'' 1 + cost ''list_get'' 1 + cost ''call'' 1
        + cost ''if'' 1 + cost ''icmp_eq'' 1 + cost ''if'' 1 + cost ''list_get'' 1 + cost ''call'' 1"
    

lemma finite_sum_gtzero_nat_cost:
  "finite {a. the_acost (cost n m) a > (0::nat)}"
  unfolding cost_def by (auto simp: zero_acost_def)

    lemma is_insert_unguarded_correct: "is_insert_unguarded N xs i \<le> \<Down>Id (timerefine (TId (''is_insert'' := cost_insert N,   ''is_insert_g'' := cost_insert_guarded N)) (is_insert_spec_unguarded N xs i))"
      unfolding is_insert_unguarded_def is_insert_spec_unguarded_def
      apply (rule refine0)
      apply (simp add: SPEC_timerefine_conv)
      thm timerefine_SPECT
      unfolding SPEC_def
      unfolding SPECc2_def
      unfolding has_stopper_def
      apply(rule gwp_specifies_I)
      apply (refine_vcg \<open>simp\<close> rules: gwp_monadic_WHILEIET if_rule)
      subgoal
        apply(auto simp:  wfR2_def the_acost_zero_app) 
        unfolding cost_is_insert_step_def
        apply(auto simp: norm_cost ) 
        by(auto simp: finite_sum_gtzero_nat_cost)
      subgoal for s a b
        apply (rule loop_body_conditionI)
        subgoal
          unfolding cost_is_insert_step_def
          apply(simp add: norm_cost)
          apply sc_solve by auto 
        subgoal 
          apply (clarsimp simp: cost_is_insert_step_def norm_cost)
          apply sc_solve
          apply (simp add: one_enat_def algebra_simps)
          apply (intro conjI)
          apply (metis Suc_diff_Suc diff_diff_cancel diff_le_self diff_zero le_diff_conv le_trans nat_add_left_cancel_le neq0_conv zero_less_diff)
          subgoal 
            apply (subgoal_tac "1 + (N+b-Suc i) = N+b-i")
            apply simp 
            apply (simp)
            apply (metis Suc_diff_Suc diff_diff_cancel diff_le_self diff_zero le_diff_conv le_trans nat_add_left_cancel_le neq0_conv zero_less_diff)
            done
          subgoal 
            by (metis Suc_diff_Suc Suc_pred add_diff_cancel_left' le_diff_conv le_eq_less_or_eq le_simps(3) linorder_not_le)
          done
        subgoal
          apply simp  
          apply (intro conjI)
          subgoal by (metis (full_types) diff_is_0_eq' not_less zero_le)
          subgoal by (metis Suc_le_eq Suc_pred le_diff_conv le_eq_less_or_eq nat_add_left_cancel_le)
          subgoal by linarith
          subgoal by (metis atLeastAtMost_iff diff_Suc_less diff_le_self le_trans linorder_not_le nth_list_update')
          subgoal by (smt Suc_diff_Suc diff_zero greaterThanAtMost_iff le_eq_less_or_eq le_less_trans le_simps(3) nth_list_update_eq nth_list_update_neq)
        done
      done  
      subgoal for _ _ i'
        apply (rule loop_exit_conditionI)
        apply (refine_vcg \<open>simp\<close>)
        apply simp
        apply (intro conjI)
        subgoal
          unfolding is_insert_spec_aux_def
          apply (rule exI[where x=i']) 
          by auto
        subgoal
          apply (simp add: algebra_simps lift_acost_diff_to_the_right)
          apply (simp add: cost_insert_def)
          apply (clarsimp simp: cost_is_insert_step_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost timerefineA_update_apply_same_cost')
          apply sc_solve
          by auto
        done
          
      subgoal by auto
      subgoal by auto
      done
    
    
    (*    
        
    definition "is_insert_spec N GUARDED xs i \<equiv> doN {
      ASSERT (i<length xs \<and> (\<not>GUARDED \<longrightarrow> 0<i \<and> \<not>xs!i\<^bold><xs!0));
      SPEC (is_insert_spec_aux xs i) (\<lambda>_. N)
    }"  

    text \<open>When unguarded, the first element of the list cannot change\<close>
    lemma is_insert_spec_alt: "is_insert_spec GUARDED xs i = doN {
      ASSERT (i<length xs \<and> (\<not>GUARDED \<longrightarrow> 0<i \<and> \<not>xs!i\<^bold><xs!0));
      SPEC (\<lambda>xs'. is_insert_spec_aux xs i xs' \<and> (\<not>GUARDED \<longrightarrow> xs'!0 = xs!0))
    }"
      unfolding is_insert_spec_def 
      apply (simp only: pw_eq_iff refine_pw_simps; clarsimp; safe)
      unfolding is_insert_spec_aux_def
      apply clarsimp
      by (metis Suc_leI Suc_to_right atLeast0LessThan greaterThanAtMost_iff lessThan_iff not_less_eq)
    
    lemma is_insert_correct: "is_insert GUARDED xs i \<le> is_insert_spec GUARDED xs i"
      unfolding is_insert_def is_insert_spec_def
      apply (refine_vcg WHILEIT_rule[where R="measure snd"])
      apply clarsimp_all
      subgoal by (metis Suc_lessI Suc_to_right)
      subgoal by linarith
      subgoal by (metis Suc_lessI Suc_pred greaterThanAtMost_iff le_less_trans nth_list_update')
    
      subgoal for xs' i'
        unfolding is_insert_spec_aux_def
        apply (rule exI[where x=i']) 
        by auto
        
      done
      
    definition is_insert2 :: "bool \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list nres" where "is_insert2 GUARDED xs i \<equiv> doN {
      ASSERT ((\<not>GUARDED\<longrightarrow>0<i) \<and> i<length xs);
      
      xs \<leftarrow> mop_to_eo_conv xs;
      
      (x,xs) \<leftarrow> mop_eo_extract xs i;
    
      (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i'). True) 
        (\<lambda>(xs,i). if \<not>GUARDED \<or> i>0 then doN { ASSERT (i>0); mop_cmpo_v_idx xs x (i-1)} else RETURN False) (\<lambda>(xs,i). doN {
          ASSERT (i>0);
          (t,xs) \<leftarrow> mop_eo_extract xs (i-1);
          xs \<leftarrow> mop_eo_set xs i t;
          let i = i-1;
          RETURN (xs,i)
        }) (xs,i);
    
      xs \<leftarrow> mop_eo_set xs i x;  
      
      xs \<leftarrow> mop_to_wo_conv xs;
      
      RETURN xs
    }"
    *)
    
    (*abbreviation "mop_eo_extract' \<equiv> mop_eo_extract (\<lambda>_. lift_acost mop_array_nth_cost)"
    abbreviation "mop_eo_set' \<equiv> mop_eo_set (\<lambda>_. lift_acost mop_array_upd_cost)"
    *)
    
    definition is_insert2_unguarded :: "nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "is_insert2_unguarded N xs i \<equiv> doN {
      \<^cancel>\<open>(*ASSERT (\<exists>guard_idx. guard_idx<i \<and> \<not>xs!i\<^bold><xs!guard_idx);*)\<close>
      ASSERT (i<length xs);
      
      xs \<leftarrow> mop_to_eo_conv xs;
      (x,xs) \<leftarrow> mop_oarray_extract xs i;
    
      (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>_. True)
        (\<lambda>(xs,i). (doN { 
          ASSERT (i>0);
          t\<^sub>2 \<leftarrow> SPECc2 ''sub'' (-) i 1; mop_cmpo_v_idx (cost ''cmpo_v_idx'' 1) xs x t\<^sub>2
        }))
        (\<lambda>(xs,i). doN {
          ASSERT (i>0 \<and> i<length xs);
          i' \<leftarrow> SPECc2 ''sub'' (-) i 1;
          (x,xs) \<leftarrow> mop_oarray_extract xs i';
          xs \<leftarrow> mop_oarray_upd xs i x;
          RETURNT (xs,i')
        }) (xs,i);

      xs \<leftarrow> mop_oarray_upd xs i x;  
      
      xs \<leftarrow> mop_to_wo_conv xs;
      
      RETURN xs
    }"

    
    
    definition "ii2_loop_rel \<equiv> {((xs',i'), (xs,i)). i'=i \<and> length xs' = length xs \<and> i<length xs \<and> (\<forall>j\<in>{0..<length xs}-{i}. xs'!j = Some (xs!j)) \<and> xs'!i=None}"
    
    abbreviation "TR_ii2 \<equiv> TId(
      ''list_get'' := lift_acost mop_array_nth_cost,
      ''list_set'' := lift_acost mop_array_upd_cost,
      ''mop_cmp_v_idx'' := cost ''cmpo_v_idx'' 1
    )"
    
    lemma is_insert2_unguarded_refine: "is_insert2_unguarded N xs i \<le>\<Down>(\<langle>Id\<rangle>list_rel) (timerefine TR_ii2 (is_insert_unguarded N xs i))"
      unfolding is_insert2_unguarded_def is_insert_unguarded_def
      supply [simp del] = conc_Id
      
      unfolding mop_oarray_extract_def mop_oarray_upd_def
      apply simp
      unfolding mop_to_eo_conv_def
      apply normalize_blocks
      
      apply (intro refine0 bindT_refine_easy consumea_refine; simp)
      apply force
      apply (rule IdI)
      subgoal
        by(simp add: norm_cost)  
      apply (rule bindT_refine_easy)
      apply force
      
      unfolding monadic_WHILEIET_def
      apply (rule monadic_WHILEIT_refine'[where R=ii2_loop_rel])
      apply force
      apply force
      subgoal by (auto simp: ii2_loop_rel_def)
      subgoal by simp
      subgoal
        apply (clarsimp split: prod.splits simp: ii2_loop_rel_def)
        apply (refine_rcg bindT_refine_conc_time_my_inres SPECc2_refine' consumea_refine)
        apply refine_dref_type
        subgoal apply(intro wfR''_upd) by simp
        subgoal by (simp (no_asm))
        subgoal by(auto intro!: preserves_curr_other_updI)
        subgoal by (simp add: inres_SPECc2)
        subgoal apply(intro wfR''_upd) by simp
        subgoal by (simp (no_asm))
        subgoal by (simp (no_asm) add: timerefineA_update_apply_same_cost')
        subgoal by (auto simp: inres_SPECc2)
        done
      subgoal  
        apply clarsimp
        apply normalize_blocks
        apply (refine_rcg bindT_refine_conc_time_my_inres SPECc2_refine' consumea_refine)
        apply refine_dref_type
        unfolding ii2_loop_rel_def
        apply (auto simp: nth_list_update split: if_splits) []
        subgoal  apply(intro wfR''_upd) by simp
        apply simp
        subgoal  by(auto intro!: preserves_curr_other_updI)
        subgoal by (auto simp: inres_SPECc2)
        subgoal by (auto simp: inres_SPECc2)
        subgoal  apply(intro wfR''_upd) by simp
        subgoal by (simp (no_asm))
        subgoal 
          apply (subst timerefineA_propagate)
          apply force
          apply (auto simp add: timerefineA_propagate timerefineA_update_apply_same_cost' )
          done
        subgoal
          by (auto simp: nth_list_update split: if_splits) []
        done
      subgoal
        unfolding mop_to_wo_conv_def
        apply normalize_blocks
        apply clarsimp
        apply (refine_rcg bindT_refine_conc_time_my_inres SPECc2_refine' consumea_refine)
        apply refine_dref_type
        unfolding ii2_loop_rel_def
        subgoal by auto
        subgoal by (auto simp: in_set_conv_nth nth_list_update intro: list_eq_iff_nth_eq[THEN iffD2])
        subgoal by force
        subgoal by simp
        subgoal by (auto simp add: timerefineA_propagate timerefineA_update_apply_same_cost' lift_acost_zero)
        subgoal by (auto simp: ii2_loop_rel_def nth_list_update in_set_conv_nth intro: list_eq_iff_nth_eq[THEN iffD2])
        done
      done
      
      
    lemma is_insert3_unguarded_refine': "\<lbrakk> (xs,xs')\<in>slicep_rel l h; (i,i')\<in>idx_shift_rel l; i<h \<rbrakk> 
      \<Longrightarrow> is_insert2_unguarded N xs i \<le>\<Down>(slice_rel xs l h) (timerefine TId (is_insert2_unguarded N xs' i'))"
      unfolding is_insert2_unguarded_def 
      unfolding mop_oarray_extract_def mop_oarray_upd_def
      
      supply [simp del] = conc_Id
      (*apply (simp cong: if_cong)*)
      supply [refine_dref_RELATES] = 
        RELATESI[of "slicep_rel l h"] 
        RELATESI[of "idx_shift_rel l"] 
        RELATESI[of "slice_rel (map Some xs) l h"] 
        RELATESI[of "slice_rel (map Some xs) l h \<times>\<^sub>r idx_shift_rel l"] 
      apply (refine_rcg 
        bindT_refine_conc_time_my_inres SPECc2_refine' consumea_refine
        slice_nth_refine' slice_upd_refine' 
        mop_eo_extract_slice_refine mop_eo_set_slice_refine mop_to_eo_conv_slice_refine
        mop_cmp_v_idx_slice_refine mop_to_wo_conv_slice_refine
      )
      supply [[goals_limit=20]]
      apply refine_dref_type
      apply (all \<open>(assumption|simp (no_asm);fail|simp add: idx_shift_rel_def;simp add: slice_map slice_rel_def slicep_rel_def in_br_conv)?\<close>)
      subgoal by linarith
      done
      
        

    (* TODO: Move. Side-conditions? @Max *)          
    lemma timerefine_comm_concfun:
      fixes C :: "('f, ('b, enat) acost) nrest"
      assumes "wfR'' E"
      shows "timerefine E (\<Down> R C) = \<Down>R (timerefine E C)"
      sorry
      
    lemma conc_tr_trans[trans]:
      fixes m\<^sub>1 m\<^sub>2 m\<^sub>3 :: "(_,(_,enat) acost)nrest"
      assumes "m\<^sub>1 \<le> \<Down>R\<^sub>1 (timerefine TR\<^sub>1 m\<^sub>2)"  
      assumes "m\<^sub>2 \<le> \<Down>R\<^sub>2 (timerefine TR\<^sub>2 m\<^sub>3)"
      assumes WF1: "wfR'' TR\<^sub>1" 
      assumes WF2: "wfR'' TR\<^sub>2"
      shows "m\<^sub>1 \<le> \<Down>(R\<^sub>1 O R\<^sub>2) (timerefine (pp TR\<^sub>1 TR\<^sub>2) m\<^sub>3)"
      apply (rule order_trans[OF assms(1)])
      apply (simp add: conc_fun_complete_lattice_chain[symmetric] timerefine_iter2[OF WF1 WF2, symmetric]) (* TODO: Why the special version conc_fun_chain for enat? *)
      apply (rule nrest_Rel_mono)
      apply (subst timerefine_comm_concfun[symmetric])
      apply fact
      apply (rule timerefine_mono2[OF WF1])
      by fact
      
        
    find_theorems pp fun_upd
    find_theorems timerefineA fun_upd  
      
    abbreviation "TR_ii3 N \<equiv> pp TR_ii2 (TId(''is_insert'' := cost_insert N,  ''is_insert_g'' := cost_insert_guarded N))" (* @Max: what's a good format here? *)

    (* TODO: enable this! by fixing timerefine_comm_concfun *)
    lemma is_insert3_unguarded_correct'_right: 
      assumes "(xs,xs')\<in>slicep_rel l h" "(i,i')\<in>idx_shift_rel l" "i<h"
      shows "is_insert2_unguarded N xs i \<le>\<Down>(slice_rel xs l h) (timerefine (TR_ii3 N) (is_insert_spec_unguarded N xs' i'))"
    proof -
      note is_insert3_unguarded_refine'[OF assms]
      also note is_insert2_unguarded_refine
      also note is_insert_unguarded_correct
      finally show ?thesis
        apply (simp add: pp_TId_absorbs_left pp_TId_absorbs_right)
        apply rprems
        apply force+
        done
    qed


  
    lemma is_insert3_unguarded_correct': 
      assumes "(xs,xs')\<in>slicep_rel l h" "(i,i')\<in>idx_shift_rel l" "i<h"
      shows "is_insert2_unguarded N xs i \<le>\<Down>(slice_rel xs l h) (timerefine (TR_ii3 N) (is_insert_spec_unguarded N xs' i'))"
      apply(rule order.trans)
      apply(rule is_insert3_unguarded_refine'[OF assms])
      apply(rule nrest_Rel_mono)
      apply (simp add: timerefine_id)
      apply(rule order.trans)
       apply(rule is_insert2_unguarded_refine)
      apply simp
      apply(subst timerefine_iter2[symmetric])
      subgoal by(auto intro!: wfR''_upd)
      subgoal by(auto intro!: wfR''_upd)
      apply(rule timerefine_mono2)
      subgoal by(auto intro!: wfR''_upd)
      apply(rule order.trans)      
       apply(rule is_insert_unguarded_correct)
      by simp 
        

    definition is_insert_guarded :: "'a list \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "is_insert_guarded xs i \<equiv> doN {
      \<^cancel>\<open>(*ASSERT (\<exists>guard_idx. guard_idx<i \<and> \<not>xs!i\<^bold><xs!guard_idx);*)\<close>
      ASSERT (i<length xs);
      x \<leftarrow> mop_list_getN xs i;
    
      (xs,i)\<leftarrow>monadic_WHILEIET
        (\<lambda>(xs',i'). 
          i'\<le>i \<and> length xs'=length xs
        \<and> (\<forall>j\<in>{0..i'}. xs'!j = xs!j)  
        \<and> (\<forall>j\<in>{i'<..i}. xs'!j = xs!(j-1) \<and> x\<^bold><xs'!j)  
        \<and> (\<forall>j\<in>{i<..<length xs}. xs'!j=xs!j)
        )
        (\<lambda>(xs,i'). i' *m cost_is_insert_guarded_step) 
        (\<lambda>(xs,i). (doN { 
          if\<^sub>N SPECc2 ''icmp_eq'' (=) i 0 then RETURNT False
          else doN {
            ASSERT(i>0);
            t\<^sub>2 \<leftarrow> SPECc2 ''sub'' (-) i 1; 
            mop_cmp_v_idx (cost ''mop_cmp_v_idx'' 1) xs x t\<^sub>2
          }
        }))
        (\<lambda>(xs,i). doN {
          ASSERT (i>0 \<and> i<length xs);
          i' \<leftarrow> SPECc2 ''sub'' (-) i 1;
          x \<leftarrow> mop_list_getN xs i';
          xs \<leftarrow> mop_list_setN xs i x;
          RETURNT (xs,i')
        }) (xs,i);
    
      xs \<leftarrow> mop_list_setN xs i x;  
      
      RETURN xs
    }"
    
    definition "is_insert_spec_guarded xs i \<equiv> doN {
      ASSERT (i<length xs);
      SPEC (is_insert_spec_aux xs i) (\<lambda>_. cost ''is_insert_g'' 1)
    }"  
    
    
    
    lemma is_insert_guarded_correct: "is_insert_guarded xs i \<le> \<Down>Id (timerefine (TId (''is_insert'' := cost_insert N, ''is_insert_g'' := cost_insert_guarded i)) (is_insert_spec_guarded xs i))"
      unfolding is_insert_guarded_def is_insert_spec_guarded_def
      apply (rule refine0)
      apply (simp add: SPEC_timerefine_conv)
      unfolding SPEC_def
      unfolding SPECc2_def
      apply(rule gwp_specifies_I)
      apply (refine_vcg \<open>simp\<close> rules: gwp_monadic_WHILEIET if_rule)
      subgoal
        apply(auto simp:  wfR2_def the_acost_zero_app) 
        unfolding cost_is_insert_guarded_step_def
        apply(auto simp: costmult_cost costmult_add_distrib the_acost_propagate ) 
        by(auto simp: finite_sum_gtzero_nat_cost)
      subgoal 
        apply (rule loop_exit_conditionI)
        apply (refine_vcg \<open>simp\<close>)
        
        subgoal
          apply clarsimp
          apply (rule conjI)
          apply (fastforce simp: is_insert_spec_aux_def)
          
          apply (clarsimp simp: 
            cost_is_insert_guarded_step_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost algebra_simps cost_zero
            cost_insert_guarded_def timerefineA_cost
            )
        
          apply sc_solve
          apply (auto simp flip: plus_enat_simps)
          
          
          done
      done 
      subgoal for s a b
        apply (rule loop_body_conditionI)
        subgoal
          unfolding cost_is_insert_guarded_step_def
          apply(simp add: norm_cost)
          apply sc_solve by auto 
        subgoal 
          apply (clarsimp simp: cost_is_insert_guarded_step_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost)
          apply sc_solve
          apply (simp add: one_enat_def algebra_simps)
          done
        subgoal
          apply simp  
          apply (intro conjI)
          apply linarith
          apply clarsimp
          by (metis Suc_lessI Suc_pred greaterThanAtMost_iff le_less_trans nth_list_update_eq nth_list_update_neq)
      done  
      subgoal for _ _ i'
        apply (rule loop_exit_conditionI)
        apply (refine_vcg \<open>simp\<close>)
        apply simp
        apply (intro conjI)
        subgoal
          unfolding is_insert_spec_aux_def
          apply (rule exI[where x=i']) 
          by auto
        subgoal
          apply (simp add: algebra_simps lift_acost_diff_to_the_right)
          apply (simp add: cost_insert_guarded_def)
          apply (clarsimp simp: cost_is_insert_guarded_step_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost timerefineA_update_apply_same_cost')
          apply sc_solve
          apply (auto simp flip: plus_enat_simps simp: algebra_simps)
          done
        done
          
      subgoal by auto
      done
    
    definition is_insert2_guarded :: "'a list \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "is_insert2_guarded xs i \<equiv> doN {
      \<^cancel>\<open>(*ASSERT (\<exists>guard_idx. guard_idx<i \<and> \<not>xs!i\<^bold><xs!guard_idx);*)\<close>
      ASSERT (i<length xs);
      
      xs \<leftarrow> mop_to_eo_conv xs;
      (x,xs) \<leftarrow> mop_oarray_extract xs i;
    
      (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>_. True)
        (\<lambda>(xs,i). (doN { 
          if\<^sub>N SPECc2 ''icmp_eq'' (=) i 0 then RETURNT False
          else doN {
            ASSERT(i>0);
            t\<^sub>2 \<leftarrow> SPECc2 ''sub'' (-) i 1; 
            mop_cmpo_v_idx (cost ''cmpo_v_idx'' 1) xs x t\<^sub>2
          }
        }))
        (\<lambda>(xs,i). doN {
          ASSERT (i>0 \<and> i<length xs);
          i' \<leftarrow> SPECc2 ''sub'' (-) i 1;
          (x,xs) \<leftarrow> mop_oarray_extract xs i';
          xs \<leftarrow> mop_oarray_upd xs i x;
          RETURNT (xs,i')
        }) (xs,i);

      xs \<leftarrow> mop_oarray_upd xs i x;  
      
      xs \<leftarrow> mop_to_wo_conv xs;
      
      RETURN xs
    }"
    
    
    lemma is_insert2_guarded_refine: "is_insert2_guarded xs i \<le>\<Down>(\<langle>Id\<rangle>list_rel) (timerefine TR_ii2 (is_insert_guarded xs i))"
      unfolding is_insert2_guarded_def is_insert_guarded_def
      unfolding mop_oarray_upd_def mop_oarray_extract_def
      supply [simp del] = conc_Id
      
      apply simp
      unfolding mop_to_eo_conv_def
      apply normalize_blocks
      
      apply (intro refine0 bindT_refine_easy consumea_refine; simp)
      apply force
      apply (rule IdI)
      subgoal by (simp add: norm_cost) 
      apply (rule bindT_refine_easy)
      apply force
      
      unfolding monadic_WHILEIET_def
      apply (rule monadic_WHILEIT_refine'[where R=ii2_loop_rel])
      apply force
      apply force
      subgoal by (auto simp: ii2_loop_rel_def)
      subgoal by simp
      subgoal
        apply (clarsimp split: prod.splits simp: ii2_loop_rel_def)
        apply (refine_rcg bindT_refine_conc_time_my_inres SPECc2_refine' consumea_refine MIf_refine)
        apply refine_dref_type
        
        apply (simp_all (no_asm))
        
        subgoal apply(intro wfR''_upd) by simp
        subgoal  by(auto intro!: preserves_curr_other_updI)
        subgoal  by(auto intro!: struct_preserving_upd_I)
        subgoal apply(intro wfR''_upd) by simp
        subgoal apply(intro wfR''_upd) by simp
        subgoal  by(auto intro!: preserves_curr_other_updI)
        subgoal by (simp add: inres_SPECc2)
        subgoal apply(intro wfR''_upd) by simp
        subgoal by (simp (no_asm) add: timerefineA_update_apply_same_cost')
        subgoal by (auto simp: inres_SPECc2)
        done
      subgoal  
        apply clarsimp
        apply normalize_blocks
        apply (refine_rcg bindT_refine_conc_time_my_inres SPECc2_refine' consumea_refine)
        apply refine_dref_type
        unfolding ii2_loop_rel_def
        apply (auto simp: nth_list_update split: if_splits) []
        subgoal apply(intro wfR''_upd) by simp
        apply simp
        subgoal  by(auto intro!: preserves_curr_other_updI)
        subgoal by (auto simp: inres_SPECc2)
        subgoal by (auto simp: inres_SPECc2)
        subgoal apply(intro wfR''_upd) by simp
        subgoal by (simp (no_asm))
        subgoal 
          apply (subst timerefineA_propagate)
          apply force
          apply (auto simp add: timerefineA_propagate timerefineA_update_apply_same_cost' )
          done
        subgoal
          by (auto simp: nth_list_update split: if_splits) []
        done
      subgoal
        unfolding mop_to_wo_conv_def
        apply normalize_blocks
        apply clarsimp
        apply (refine_rcg bindT_refine_conc_time_my_inres SPECc2_refine' consumea_refine)
        apply refine_dref_type
        unfolding ii2_loop_rel_def
        subgoal by auto
        subgoal by (auto simp: in_set_conv_nth nth_list_update intro: list_eq_iff_nth_eq[THEN iffD2])
        subgoal by force
        subgoal by simp
        subgoal by (auto simp add: timerefineA_propagate timerefineA_update_apply_same_cost' lift_acost_zero)
        subgoal by (auto simp: ii2_loop_rel_def nth_list_update in_set_conv_nth intro: list_eq_iff_nth_eq[THEN iffD2])
        done
      done
    
    
    definition is_insert3_guarded :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "is_insert3_guarded xs l i \<equiv> doN {
      \<^cancel>\<open>(*ASSERT (\<exists>guard_idx. guard_idx<i \<and> \<not>xs!i\<^bold><xs!guard_idx);*)\<close>
      ASSERT (i<length xs);
      
      xs \<leftarrow> mop_to_eo_conv xs;
      (x,xs) \<leftarrow> mop_oarray_extract xs i;
    
      (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>_. True)
        (\<lambda>(xs,i). (doN { 
          if\<^sub>N SPECc2 ''icmp_eq'' (=) i l then RETURNT False
          else doN {
            ASSERT(i>0);
            t\<^sub>2 \<leftarrow> SPECc2 ''sub'' (-) i 1; 
            mop_cmpo_v_idx (cost ''cmpo_v_idx'' 1) xs x t\<^sub>2
          }
        }))
        (\<lambda>(xs,i). doN {
          ASSERT (i>0 \<and> i<length xs);
          i' \<leftarrow> SPECc2 ''sub'' (-) i 1;
          (x,xs) \<leftarrow> mop_oarray_extract xs i';
          xs \<leftarrow> mop_oarray_upd xs i x;
          RETURNT (xs,i')
        }) (xs,i);

      xs \<leftarrow> mop_oarray_upd xs i x;  
      
      xs \<leftarrow> mop_to_wo_conv xs;
      
      RETURN xs
    }"
    
  
    lemma is_insert3_guarded_refine': "\<lbrakk> (xs,xs')\<in>slicep_rel l h; (i,i')\<in>idx_shift_rel l; i<h \<rbrakk> 
      \<Longrightarrow> is_insert3_guarded xs l i \<le>\<Down>(slice_rel xs l h) (timerefine TId (is_insert2_guarded xs' i'))"
      unfolding is_insert2_guarded_def is_insert3_guarded_def
      unfolding mop_oarray_upd_def mop_oarray_extract_def
      
      supply [simp del] = conc_Id
      (*apply (simp cong: if_cong)*)
      supply [refine_dref_RELATES] = 
        RELATESI[of "slicep_rel l h"] 
        RELATESI[of "idx_shift_rel l"] 
        RELATESI[of "slice_rel (map Some xs) l h"] 
        RELATESI[of "slice_rel (map Some xs) l h \<times>\<^sub>r idx_shift_rel l"] 
      apply (refine_rcg 
        bindT_refine_conc_time_my_inres SPECc2_refine' consumea_refine
        slice_nth_refine' slice_upd_refine' 
        mop_eo_extract_slice_refine mop_eo_set_slice_refine mop_to_eo_conv_slice_refine
        mop_cmp_v_idx_slice_refine mop_to_wo_conv_slice_refine
        MIf_refine
      )
      supply [[goals_limit=20]]
      apply refine_dref_type
      apply (all \<open>(assumption|simp (no_asm);fail|simp add: idx_shift_rel_def;simp add: slice_map slice_rel_def slicep_rel_def in_br_conv)?\<close>)
      subgoal by linarith
      done
    
    abbreviation "TR_ii3_guarded N \<equiv> pp TR_ii2 (TId(''is_insert'' := cost_insert N, ''is_insert_g'' := cost_insert_guarded N))" (* @Max: what's a good format here? *)
      
    (* TODO: enable this! by fixing timerefine_comm_concfun *)
    lemma is_insert3_guarded_correct'_right: 
      assumes "(xs,xs')\<in>slicep_rel l h" "(i,i')\<in>idx_shift_rel l" "i<h"
      shows "is_insert3_guarded xs l i \<le>\<Down>(slice_rel xs l h) (timerefine (TR_ii3_guarded (i-l)) (is_insert_spec_guarded xs' i'))"
    proof -
      from assms(2) have [simp]: "i' = i-l" by (auto simp: idx_shift_rel_def)
    
      note is_insert3_guarded_refine'[OF assms]
      also note is_insert2_guarded_refine
      also note is_insert_guarded_correct
      finally show ?thesis
        apply (simp add: pp_TId_absorbs_left pp_TId_absorbs_right)
        apply rprems
        apply force+
        done
    qed

    lemma is_insert3_guarded_correct': 
      assumes "(xs,xs')\<in>slicep_rel l h" "(i,i')\<in>idx_shift_rel l" "i<h"
      shows "is_insert3_guarded xs l i \<le>\<Down>(slice_rel xs l h) (timerefine (TR_ii3_guarded (i-l)) (is_insert_spec_guarded xs' i'))"
    proof -
      from assms(2) have [simp]: "i' = i-l" by (auto simp: idx_shift_rel_def)
      show ?thesis
          apply(rule order.trans)
      apply(rule is_insert3_guarded_refine'[OF assms])
      apply(rule nrest_Rel_mono)
      apply (simp add: timerefine_id)
      apply(rule order.trans)
       apply(rule is_insert2_guarded_refine)
      apply simp
      apply(subst timerefine_iter2[symmetric])
      subgoal by(auto intro!: wfR''_upd)
      subgoal by(auto intro!: wfR''_upd)
      apply(rule timerefine_mono2)
      subgoal by(auto intro!: wfR''_upd)
      apply(rule order.trans)      
       apply(rule is_insert_guarded_correct[where N="(i - l)"])
      by simp 
  qed
        
end
  
find_theorems mop_oarray_extract mop_eo_extract

context sort_impl_context begin


    definition is_insert_unguarded4 :: "nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "is_insert_unguarded4 N xs i \<equiv> doN {
      \<^cancel>\<open>(*ASSERT (\<exists>guard_idx. guard_idx<i \<and> \<not>xs!i\<^bold><xs!guard_idx);*)\<close>
      ASSERT (i<length xs);
      
      xs \<leftarrow> mop_to_eo_conv xs;
      (x,xs) \<leftarrow> mop_oarray_extract xs i;
    
      (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>_. True)
        (\<lambda>(xs,i). (doN { 
          ASSERT (i>0);
          t\<^sub>2 \<leftarrow> SPECc2 ''sub'' (-) i 1;
          cmpo_v_idx2' xs x t\<^sub>2
        }))
        (\<lambda>(xs,i). doN {
          ASSERT (i>0 \<and> i<length xs);
          i' \<leftarrow> SPECc2 ''sub'' (-) i 1;
          (x,xs) \<leftarrow> mop_oarray_extract xs i';
          xs \<leftarrow> mop_oarray_upd xs i x;
          RETURNT (xs,i')
        }) (xs,i);

      xs \<leftarrow> mop_oarray_upd xs i x;  
      
      xs \<leftarrow> mop_to_wo_conv xs;
      
      RETURN xs
    }"


  lemma is_insert_unguarded4_refines:
    "(xs,xs')\<in>Id \<Longrightarrow> (i,i')\<in>Id \<Longrightarrow> 
      is_insert_unguarded4 N xs i \<le> \<Down>Id (timerefine TR_cmp_swap (is_insert2_unguarded N xs' i'))"
    supply conc_Id[simp del] mop_cmpo_v_idx_def[simp del]
    unfolding is_insert_unguarded4_def is_insert2_unguarded_def
    supply [refine] = mop_to_eo_conv_refine  mop_to_wo_conv_refines
          cmpo_v_idx2'_refines_mop_cmpo_v_idx_with_E
          mop_oarray_extract_refines mop_oarray_upd_refines
    apply(refine_rcg MIf_refine SPECc2_refine' bindT_refine_conc_time_my_inres monadic_WHILEIT_refine' )
                        apply refine_dref_type
  apply(all \<open>(intro  preserves_curr_other_updI wfR''_upd wfR''_TId preserves_curr_TId)?\<close>)
  apply (simp_all (no_asm))
  apply (auto simp: timerefineA_cost)  
    done

  context 
    fixes N :: nat
  begin
        sepref_register "is_insert_unguarded4 N"
  end


  sepref_def is_unguarded_insert_impl is "uncurry (PR_CONST (is_insert_unguarded4 N))" 
    :: "(array_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a array_assn elem_assn"
    unfolding is_insert_unguarded4_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    

  

  definition is_insert_guarded4 :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest"
    where "is_insert_guarded4 xs l i \<equiv> doN {
      \<^cancel>\<open>(*ASSERT (\<exists>guard_idx. guard_idx<i \<and> \<not>xs!i\<^bold><xs!guard_idx);*)\<close>
      ASSERT (i<length xs);
      
      xs \<leftarrow> mop_to_eo_conv xs;
      (x,xs) \<leftarrow> mop_oarray_extract xs i;
    
      (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>_. True)
        (\<lambda>(xs,i). (doN { 
          if\<^sub>N SPECc2 ''icmp_eq'' (=) i l then RETURNT False
          else doN {
            ASSERT(i>0);
            t\<^sub>2 \<leftarrow> SPECc2 ''sub'' (-) i 1; 
            cmpo_v_idx2' xs x t\<^sub>2
          }
        }))
        (\<lambda>(xs,i). doN {
          ASSERT (i>0 \<and> i<length xs);
          i' \<leftarrow> SPECc2 ''sub'' (-) i 1;
          (x,xs) \<leftarrow> mop_oarray_extract xs i';
          xs \<leftarrow> mop_oarray_upd xs i x;
          RETURNT (xs,i')
        }) (xs,i);

      xs \<leftarrow> mop_oarray_upd xs i x;  
      
      xs \<leftarrow> mop_to_wo_conv xs;
      
      RETURN xs
    }"


  lemma is_insert_guarded4_refines:
    "(xs,xs')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> (i,i')\<in>Id
       \<Longrightarrow> is_insert_guarded4 xs l i \<le> \<Down>Id (timerefine TR_cmp_swap (is_insert3_guarded xs' l' i'))"
    supply conc_Id[simp del] mop_cmpo_v_idx_def[simp del]
    unfolding is_insert_guarded4_def is_insert3_guarded_def
    supply [refine] = mop_to_eo_conv_refine  mop_to_wo_conv_refines
          cmpo_v_idx2'_refines_mop_cmpo_v_idx_with_E
          mop_oarray_extract_refines mop_oarray_upd_refines
    apply(refine_rcg MIf_refine SPECc2_refine' bindT_refine_conc_time_my_inres monadic_WHILEIT_refine' )
                        apply refine_dref_type
  apply(all \<open>(intro  preserves_curr_other_updI wfR''_upd wfR''_TId preserves_curr_TId)?\<close>)
  apply (simp_all (no_asm))
  apply (auto simp: timerefineA_cost)  
  done
    

  sepref_register is_insert_guarded4

  sepref_def is_guarded_insert_impl is "uncurry2 (PR_CONST (is_insert_guarded4))" 
    :: "(array_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a array_assn elem_assn"
    unfolding is_insert_guarded4_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref 
    
end    



context weak_ordering begin

  lemma is_insert_spec_aux_split: "is_insert_spec_aux xs i xs' \<Longrightarrow> (\<exists>i'\<le>i. 
    xs' = take i' xs @ xs!i # drop i' (take i xs) @ drop (i+1) xs \<and> i<length xs)"
    unfolding is_insert_spec_aux_def
    apply clarify
    subgoal for i'
      apply (rule exI[where x=i'])
      apply (simp add: list_eq_iff_nth_eq)
      apply (clarsimp simp: nth_append nth_Cons split: nat.splits)
      apply (safe; clarsimp?)
      subgoal for j k
        by (metis One_nat_def Suc_le_eq add.commute add_Suc_right add_diff_cancel_left' add_diff_inverse_nat greaterThanAtMost_iff less_diff_conv plus_1_eq_Suc zero_less_Suc)
      subgoal by (metis add_Suc leI le_add_diff_inverse2)
      done
    done
    
    
  lemma is_insert_spec_aux_imp_mset_eq:
    assumes A: "is_insert_spec_aux xs i xs'"  
    shows "mset xs' = mset xs"
  proof -
    from A have L: "i<length xs"
      unfolding is_insert_spec_aux_def by blast
  
    from is_insert_spec_aux_split[OF A] obtain i' where
      I': "i'\<le>i" 
      and XS'_EQ: "xs' = take i' xs @ xs ! i # drop i' (take i xs) @ drop (i + 1) xs"
      by blast  
    
    have XS_EQ: "xs = take i' xs @ drop i' (take i xs) @ xs!i # drop (i + 1) xs"  
      using L I'
      apply auto 
      by (metis atd_lem drop_Suc_nth drop_take_drop_unsplit)  
    
    show ?thesis
      apply (rewrite in "\<hole> = _" XS'_EQ)
      apply (rewrite in "_ = \<hole>" XS_EQ)
      by (auto)  
      
  qed    

  
  lemma is_insert_spec_aux_imp_mset_eq':
    assumes A: "is_insert_spec_aux xs i xs'"  
    shows "mset (take (i+1) xs') = mset (take (i+1) xs)"
    using A
  proof -
    from A have L: "i<length xs"
      unfolding is_insert_spec_aux_def by blast
  
    from is_insert_spec_aux_split[OF A] obtain i' where
      I': "i'\<le>i" 
      and "xs' = take i' xs @ xs ! i # drop i' (take i xs) @ drop (i + 1) xs"
      by blast  
    hence XS'_EQ: "take (i+1) xs' = take i' xs @ xs ! i # drop i' (take i xs)" using L
      by (auto simp: take_Cons split: nat.splits)   
      
    have XS_EQ: "take (i+1) xs = take i' xs @ drop i' (take i xs) @ [xs!i]" using L I'
      using L I'
      apply auto
      by (metis append.assoc drop_take le_add_diff_inverse take_Suc_conv_app_nth take_add)        
    
    show ?thesis
      apply (rewrite in "\<hole> = _" XS'_EQ)
      apply (rewrite in "_ = \<hole>" XS_EQ)
      by (auto)  
      
  qed    
  
    
  lemma is_insert_spec_aux_imp_rest_eq:
    assumes A: "is_insert_spec_aux xs i xs'"  
    shows "drop (i+1) xs' = drop (i+1) xs"
    using A unfolding is_insert_spec_aux_def 
    apply (simp add: list_eq_iff_nth_eq)
    by force 

  lemma is_insert_spec_aux_imp_length_eq:
    assumes A: "is_insert_spec_aux xs i xs'"  
    shows "length xs' = length xs"
    using A unfolding is_insert_spec_aux_def 
    by force 
    
    
  lemma insert_spec_aux_preserves_stoppers:
    assumes "i<j" "has_stopper N xs j" 
    (*assumes "has_stopper N xs i"*)
    assumes "is_insert_spec_aux xs i xs'" (*"sorted_wrt_lt (\<^bold><) (take i xs)"*)
    shows "has_stopper N xs' j"
    using assms
    unfolding has_stopper_def is_insert_spec_aux_def
    apply clarsimp
    subgoal for i' j'
      apply (cases "i'>j'")
      subgoal
        apply (rule exI[where x=j'])
        apply (clarsimp)
        done
      subgoal
        apply (rule exI[where x=j'])
        apply (simp add: sorted_wrt_iff_nth_less le_by_lt_def)
        apply rule
        subgoal for ja
          apply (cases "ja < i'")
          subgoal by auto
          apply (cases "ja\<in>{i'<..i}"; simp)
          apply (cases "ja\<in>{i<..<length xs}"; simp)
          apply (intro impI)
          apply (subgoal_tac "ja < length xs")
          apply simp
          apply (metis Suc_to_right asym greaterThanAtMost_iff itrans leI le_eq_less_or_eq less_Suc_eq_le)
          apply linarith
          done
        done
      done  
    done (* TODO: Understand this proof! *)
    
    
        
    
      
    
  definition "sort_one_more_spec_unguarded N xs i h \<equiv> doN {
      ASSERT (i<length xs \<and> sorted_wrt_lt (\<^bold><) (take i xs) \<and> h\<le>length xs);
      ASSERT (\<forall>j\<in>{i..<h}. has_stopper N xs j); 
      SPEC (\<lambda>xs'. 
          mset (take (i+1) xs') = mset (take (i+1) xs) 
        \<and> drop (i+1) xs' = drop (i+1) xs 
        \<and> length xs'=length xs 
        \<and> sorted_wrt_lt (\<^bold><) (take (i+1) xs') 
        \<and> (\<forall>j\<in>{i<..<h}. has_stopper N xs' j)) (\<lambda>_. cost ''is_insert'' (1::enat))
    }"  
    
    
  (*  
  lemma is_insert_unguarded_sorts_one_more: 
    "(is_insert_spec_unguarded N, sort_one_more_spec_unguarded N) 
        \<in> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>nrest_rel"
  *)
  
  lemma is_insert_unguarded_sorts_one_more: 
    "i<h \<Longrightarrow> is_insert_spec_unguarded N xs i \<le> \<Down>Id (timerefine TId (sort_one_more_spec_unguarded N xs i h))"
  
    (*apply (intro fun_relI nrest_relI')    *)
    
    find_theorems TId
    
    using is_insert_spec_aux_imp_sorted is_insert_spec_aux_imp_mset_eq' 
      is_insert_spec_aux_imp_rest_eq is_insert_spec_aux_imp_length_eq
      insert_spec_aux_preserves_stoppers
    unfolding sort_one_more_spec_unguarded_def is_insert_spec_unguarded_def
    apply (refine_rcg SPEC_both_refine)
    by auto fastforce
    
    
  abbreviation "insort_step_cost \<equiv> cost ''icmp_slt'' 1 + cost ''add'' 1 + cost ''is_insert'' 1 + cost ''call'' 1
     + cost ''if'' 1"  
    
  definition "gen_insertion_sort_unguarded N i\<^sub>0 h xs \<equiv> doN {
    ASSERT ((\<forall>i\<in>{i\<^sub>0..<h}. has_stopper N xs i) \<and> h\<le>length xs);
    (xs,_)\<leftarrow>monadic_WHILEIET (\<lambda>(xs',i). 
          i\<^sub>0\<le>i \<and> i\<le>h \<and> length xs'=length xs 
        \<and> mset (take i xs') = mset (take i xs) 
        \<and> drop i xs' = drop i xs 
        \<and> sorted_wrt_lt (\<^bold><) (take i xs')
        \<and> (\<forall>j\<in>{i..<h}. has_stopper N xs' j)
      ) 
      (\<lambda>(xs,i). (h-i) *m insort_step_cost)
      (\<lambda>(xs,i). SPECc2 ''icmp_slt'' (<) i h) 
      (\<lambda>(xs,i). doN {
        xs \<leftarrow> sort_one_more_spec_unguarded N xs i h;
        ASSERT (i<h);
        i \<leftarrow> SPECc2 ''add'' (+) i 1;
        RETURN (xs,i)
      }) (xs,i\<^sub>0);
    RETURN xs
  }"  
  
    
  lemma gen_insertion_sort_unguarded_correct: 
    "\<lbrakk>sorted_wrt_lt (\<^bold><) (take i\<^sub>0 xs); (\<forall>i\<in>{i\<^sub>0..<h}. has_stopper N xs i) \<and> h\<le>length xs ; i\<^sub>0<h; h\<le>length xs \<rbrakk> 
      \<Longrightarrow> gen_insertion_sort_unguarded N i\<^sub>0 h xs 
        \<le> \<Down>Id (timerefine (TId(''slice_sort'' := enat (h-i\<^sub>0+1) *m insort_step_cost)) (
          slice_sort_spec (\<^bold><) xs 0 h))"
    unfolding gen_insertion_sort_unguarded_def sort_one_more_spec_unguarded_def slice_sort_spec_def sort_spec_def sorted_sorted_wrt
    
    apply (intro refine0)
    subgoal by simp
    apply (simp add: SPEC_timerefine_conv)
    
    thm SPEC_REST_emb'_conv
    
    unfolding SPEC_REST_emb'_conv SPECc2_def
    apply(rule gwp_specifies_I)
    apply (refine_vcg \<open>simp\<close> rules: gwp_monadic_WHILEIET if_rule)
      subgoal
        apply(auto simp:  wfR2_def the_acost_zero_app) 
        unfolding cost_is_insert_step_def
        apply(auto simp: costmult_cost costmult_add_distrib the_acost_propagate ) 
        by(auto simp: finite_sum_gtzero_nat_cost)
    subgoal
      apply (rule loop_body_conditionI)
        subgoal
          unfolding cost_is_insert_guarded_step_def
          apply(simp add: norm_cost)
          apply sc_solve by auto 
      subgoal 
        apply (clarsimp simp: cost_is_insert_guarded_step_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost)
        apply sc_solve
        apply (simp add: one_enat_def algebra_simps)
        done
        
      subgoal
        apply (clarsimp; safe)
        apply (simp add: take_Suc_conv_app_nth)
        apply (metis drop_Suc_nth less_le_trans nth_via_drop)
        by (meson drop_eq_mono dual_order.refl le_SucI)

      done
    subgoal 
      apply (rule loop_exit_conditionI)
      apply (refine_vcg \<open>simp\<close>)
      unfolding emb_le_Some_conv
      apply (rule conjI)
      subgoal
        apply (simp add: lift_acost_diff_to_the_right)
        apply (clarsimp simp: cost_is_insert_guarded_step_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost timerefineA_update_apply_same_cost')
        apply sc_solve
        apply (auto simp flip: plus_enat_simps simp: algebra_simps one_enat_def plus_enat_simps)
        done
        
      subgoal by (clarsimp simp: Misc.slice_def)    
      done
    done
        
  definition "gen_insertion_sort_unguarded2 N i h xs \<equiv> doN {
    (xs,_)\<leftarrow>monadic_WHILEIT (\<lambda>_. True)
      (\<lambda>(xs,i). SPECc2 ''icmp_slt'' (<) i h) 
      (\<lambda>(xs,i). doN {
        xs \<leftarrow> is_insert2_unguarded N xs i;
        ASSERT (i<h);
        i \<leftarrow> SPECc2 ''add'' (+) i 1;
        RETURN (xs,i)
      }) (xs,i);
    RETURN xs
  }"  
  
  definition "TR_is_insert3 N \<equiv> (
                   (pp (pp (TId(''list_get'' := lift_acost mop_array_nth_cost, ''list_set'' := lift_acost mop_array_upd_cost, ''mop_cmp_v_idx'' := cost ''cmpo_v_idx'' 1))
                         (TId(''is_insert'' := cost_insert N, ''is_insert_g'' := cost_insert_guarded N)))
                     TId))"

  (* TODO: enable this kind of reasoning! by fixing timerefine_comm_concfun *)
  lemma is_insert3_sorts_one_more_right: 
    assumes "(xs,xs')\<in>slicep_rel l h" "(i,i')\<in>idx_shift_rel l" "i<h" "i'<j'"
    shows "is_insert2_unguarded N xs i \<le>\<Down>(slice_rel xs l h) (timerefine (TR_is_insert3 N) (sort_one_more_spec_unguarded N xs' i' j'))"
  proof -
    note is_insert3_unguarded_correct'
    also note is_insert_unguarded_sorts_one_more
    finally show ?thesis using assms unfolding TR_is_insert3_def 
      apply simp
      apply rprems
      apply simp_all
      apply (simp add: idx_shift_rel_def)
      subgoal apply(simp add: norm_pp ) apply(intro wfR''_upd) by simp
      done
  qed
 
lemma timerefine_mono3: 
  fixes R :: "_ \<Rightarrow> ('a, enat) acost"
  assumes "wfR'' R"
  shows "c\<le>c' \<Longrightarrow> R=R' \<Longrightarrow> timerefine R c \<le> timerefine R' c'"
  apply simp
  apply(rule timerefine_mono2)
  using assms by auto

thm is_insert3_unguarded_correct'
thm is_insert_unguarded_sorts_one_more

  lemma is_insert3_sorts_one_more: 
    assumes "(xs,xs')\<in>slicep_rel l h" "(i,i')\<in>idx_shift_rel l" "i<h" "i'<j'"
    shows "is_insert2_unguarded N xs i \<le>\<Down>(slice_rel xs l h) (timerefine (TR_is_insert3 N) (sort_one_more_spec_unguarded N xs' i' j'))"
    using assms apply -
      apply(rule order_trans)
     apply(rule is_insert3_unguarded_correct'[OF assms(1-3)])
    apply(rule nrest_Rel_mono)
    unfolding TR_is_insert3_def
      apply(subst (2) timerefine_iter2[symmetric])
      subgoal by(auto simp: norm_pp intro!: wfR''_upd)
      subgoal by(auto intro!: wfR''_upd)
      apply(rule timerefine_mono2)
      subgoal by(auto simp: norm_pp intro!: wfR''_upd)
      apply(rule order_trans)
       apply(rule is_insert_unguarded_sorts_one_more)
       apply simp
      apply simp
      done


lemma wfR''_TR_is_insert3[simp]: "wfR'' (TR_is_insert3 N)"
  unfolding TR_is_insert3_def
  apply(simp add: norm_pp )
  apply(intro wfR''_upd) by simp


lemma sp_TR_is_insert3[simp]:"struct_preserving (TR_is_insert3 N)"
  unfolding TR_is_insert3_def
  apply(simp add: norm_pp )  by(auto intro!: struct_preserving_upd_I)
  

  lemma gen_insertion_sort_unguarded2_refine: 
    "\<lbrakk> (xsi,xs) \<in> slicep_rel l h; (ii,i)\<in>idx_shift_rel l; (ji,j)\<in>idx_shift_rel l \<rbrakk> 
      \<Longrightarrow> gen_insertion_sort_unguarded2 N ii ji xsi \<le>\<Down>(slice_rel xsi l h) (timerefine (TR_is_insert3 N) (gen_insertion_sort_unguarded N i j xs))"
    unfolding gen_insertion_sort_unguarded2_def gen_insertion_sort_unguarded_def monadic_WHILEIET_def
    apply (refine_rcg is_insert3_sorts_one_more monadic_WHILEIT_refine' bindT_refine_conc_time_my_inres SPECc2_refine')
    supply [refine_dref_RELATES] = RELATESI[of "slice_rel xsi l h \<times>\<^sub>r idx_shift_rel l"] RELATESI[of "idx_shift_rel l"] 
    apply refine_dref_type
    apply (clarsimp_all simp: inres_SPECc2)
    
    applyS (auto simp: idx_shift_rel_def slice_rel_alt eq_outside_range_triv slicep_rel_def)[]
    applyS (auto simp: idx_shift_rel_def slicep_rel_def)[]
    subgoal unfolding TR_is_insert3_def  by(auto simp: norm_pp intro!: preserves_curr_other_updI)
    applyS (auto simp: idx_shift_rel_def slice_rel_alt) []
    applyS (auto simp: idx_shift_rel_def slicep_rel_def)[]
    applyS (auto simp: idx_shift_rel_def slicep_rel_def)[]
    applyS (auto simp: idx_shift_rel_def slicep_rel_def)[]
    subgoal unfolding TR_is_insert3_def  by(auto simp: norm_pp intro!: preserves_curr_other_updI)
    
    subgoal
      apply (clarsimp simp: idx_shift_rel_def slice_rel_alt) []
      by (erule (1) eq_outside_range_gen_trans; auto)
    done
    
    
    
    
end
    
context sort_impl_context begin


  definition "gen_insertion_sort_unguarded3 N i h xs \<equiv> doN {
    (xs,_)\<leftarrow>monadic_WHILEIT (\<lambda>_. True)
      (\<lambda>(xs,i). SPECc2 ''icmp_slt'' (<) i h) 
      (\<lambda>(xs,i). doN {
        xs \<leftarrow> is_insert_unguarded4 N xs i;
        ASSERT (i<h);
        i \<leftarrow> SPECc2 ''add'' (+) i 1;
        RETURN (xs,i)
      }) (xs,i);
    RETURN xs
  }"  


  lemma gen_insertion_sort_unguarded3_refines:
    "(i,i')\<in>Id \<Longrightarrow> (h,h')\<in>Id \<Longrightarrow> (xs,xs')\<in>Id
      \<Longrightarrow> gen_insertion_sort_unguarded3 N i h xs \<le> \<Down>Id (timerefine TR_cmp_swap (gen_insertion_sort_unguarded2 N i' h' xs'))"
    supply conc_Id[simp del]
    unfolding gen_insertion_sort_unguarded3_def gen_insertion_sort_unguarded2_def
    supply [refine] = is_insert_unguarded4_refines
    apply(refine_rcg MIf_refine SPECc2_refine' bindT_refine_conc_time_my_inres monadic_WHILEIT_refine' )
                        apply refine_dref_type
  apply(all \<open>(intro  preserves_curr_other_updI wfR''_upd wfR''_TId preserves_curr_TId)?\<close>)
  apply (simp_all (no_asm))
  apply (auto simp: timerefineA_cost)  
  done



  context fixes N :: nat begin
  sepref_register 
    unguarded_insertion_sort2: "gen_insertion_sort_unguarded3 N"
  end
    
  sepref_def unguarded_insertion_sort_impl is "uncurry2 (PR_CONST (gen_insertion_sort_unguarded3 N))" 
    :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (array_assn elem_assn)\<^sup>d \<rightarrow>\<^sub>a array_assn elem_assn"
    unfolding gen_insertion_sort_unguarded3_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref 
    
end    
    
    
    
    
    
    
    
    
    

context weak_ordering begin
    
    
  definition "sort_one_more_spec_guarded xs i \<equiv> doN {
      ASSERT (i<length xs \<and> sorted_wrt_lt (\<^bold><) (take i xs));
      SPEC (\<lambda>xs'. 
          mset (take (i+1) xs') = mset (take (i+1) xs) 
        \<and> drop (i+1) xs' = drop (i+1) xs 
        \<and> length xs'=length xs 
        \<and> sorted_wrt_lt (\<^bold><) (take (i+1) xs') 
        ) (\<lambda>_. cost ''is_insert_g'' (1::enat))
    }"  
    
    
  (*  
  lemma is_insert_unguarded_sorts_one_more: 
    "(is_insert_spec_unguarded N, sort_one_more_spec_unguarded N) 
        \<in> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>nrest_rel"
  *)
  
  lemma is_insert_guarded_sorts_one_more: 
    "is_insert_spec_guarded xs i \<le> \<Down>Id (timerefine TId (sort_one_more_spec_guarded xs i))"
  
    using is_insert_spec_aux_imp_sorted is_insert_spec_aux_imp_mset_eq' 
      is_insert_spec_aux_imp_rest_eq is_insert_spec_aux_imp_length_eq
    unfolding sort_one_more_spec_guarded_def is_insert_spec_guarded_def
    apply (refine_rcg SPEC_both_refine)
    apply auto
    done
    
    
  abbreviation "insort_guarded_step_cost \<equiv> cost ''icmp_slt'' 1 + cost ''add'' 1 + cost ''is_insert_g'' 1 + cost ''call'' 1
     + cost ''if'' 1"  
  
    
  definition "gen_insertion_sort_guarded i\<^sub>0 h xs \<equiv> doN {
    ASSERT (h\<le>length xs);
    (xs,_)\<leftarrow>monadic_WHILEIET (\<lambda>(xs',i). 
          i\<^sub>0\<le>i \<and> i\<le>h \<and> length xs'=length xs 
        \<and> mset (take i xs') = mset (take i xs) 
        \<and> drop i xs' = drop i xs 
        \<and> sorted_wrt_lt (\<^bold><) (take i xs')
      ) 
      (\<lambda>(xs,i). (h-i) *m insort_guarded_step_cost)
      (\<lambda>(xs,i). SPECc2 ''icmp_slt'' (<) i h) 
      (\<lambda>(xs,i). doN {
        xs \<leftarrow> sort_one_more_spec_guarded xs i;
        ASSERT (i<h);
        i \<leftarrow> SPECc2 ''add'' (+) i 1;
        RETURN (xs,i)
      }) (xs,i\<^sub>0);
    RETURN xs
  }"  
  
    
  lemma gen_insertion_sort_guarded_correct: 
    "\<lbrakk>sorted_wrt_lt (\<^bold><) (take i\<^sub>0 xs); h\<le>length xs ; i\<^sub>0<h; h\<le>length xs \<rbrakk> 
      \<Longrightarrow> gen_insertion_sort_guarded i\<^sub>0 h xs 
        \<le> \<Down>Id (timerefine (TId(''slice_sort'' := enat (h-i\<^sub>0+1) *m insort_guarded_step_cost)) (
          slice_sort_spec (\<^bold><) xs 0 h))"
    unfolding gen_insertion_sort_guarded_def sort_one_more_spec_guarded_def slice_sort_spec_def sort_spec_def sorted_sorted_wrt
    
    apply (intro refine0)
    subgoal by simp
    apply (simp add: SPEC_timerefine_conv)
    
    thm SPEC_REST_emb'_conv
    
    unfolding SPEC_REST_emb'_conv SPECc2_def
    apply(rule gwp_specifies_I)
    apply (refine_vcg \<open>simp\<close> rules: gwp_monadic_WHILEIET if_rule)
      subgoal
        apply(auto simp:  wfR2_def the_acost_zero_app) 
        unfolding cost_is_insert_step_def
        apply(auto simp: costmult_cost costmult_add_distrib the_acost_propagate ) 
        by(auto simp: finite_sum_gtzero_nat_cost)
    subgoal
      apply (rule loop_body_conditionI)
      subgoal
        apply(simp add: norm_cost)
        apply sc_solve by auto 
      subgoal 
        apply (clarsimp simp: cost_is_insert_guarded_step_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost)
        apply sc_solve
        apply (simp add: one_enat_def algebra_simps)
        done
        
      subgoal
        apply (clarsimp; safe)
        apply (simp add: take_Suc_conv_app_nth)
        apply (metis drop_Suc_nth less_le_trans nth_via_drop)
        by (meson drop_eq_mono dual_order.refl le_SucI)

      done
    subgoal 
      apply (rule loop_exit_conditionI)
      apply (refine_vcg \<open>simp\<close>)
      unfolding emb_le_Some_conv
      apply (rule conjI)
      subgoal
        apply (simp add: lift_acost_diff_to_the_right)
        apply (clarsimp simp: cost_is_insert_guarded_step_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost timerefineA_update_apply_same_cost')
        apply sc_solve
        apply (auto simp flip: plus_enat_simps simp: algebra_simps one_enat_def plus_enat_simps)
        done
        
      subgoal by (clarsimp simp: Misc.slice_def)    
      done
    done
        
    
    
    
  definition "gen_insertion_sort_guarded2 l i h xs \<equiv> doN {
    ASSERT (l \<le> i);
    (xs,_)\<leftarrow>monadic_WHILEIT (\<lambda>_. True)
      (\<lambda>(xs,i). SPECc2 ''icmp_slt'' (<) i h) 
      (\<lambda>(xs,i). doN {
        xs \<leftarrow> is_insert3_guarded xs l i;
        ASSERT (i<h);
        i \<leftarrow> SPECc2 ''add'' (+) i 1;
        RETURN (xs,i)
      }) (xs,i);
    RETURN xs
  }"  
   
 

 
  
  (* TODO: Move, better name *)                     
  lemma timerefine_R_cf_mono:
    fixes R :: "_ \<Rightarrow> (_, enat) acost"
    assumes "wfR'' R'"
    shows "R\<le>R' \<Longrightarrow> \<Down> S (timerefine R c) \<le> \<Down> S (timerefine R' c)"
    by (simp add: assms nrest_Rel_mono timerefine_R_mono_wfR'')

  (* TODO: enable this kind of reasoning! by fixing timerefine_comm_concfun *)
  lemma is_insert3_guarded_sorts_one_more_right: 
    assumes "(xs,xs')\<in>slicep_rel l h" "(i,i')\<in>idx_shift_rel l" "i<h" "N\<ge>i-l"
    shows "is_insert3_guarded xs l i \<le>\<Down>(slice_rel xs l h) (timerefine (TR_is_insert3 N) (sort_one_more_spec_guarded xs' i'))"
  proof -
    note is_insert3_guarded_correct'
    also note is_insert_guarded_sorts_one_more
    finally show ?thesis using assms unfolding TR_is_insert3_def 
      apply (simp add: idx_shift_rel_def)
      
      apply (rule order_trans[OF _ ])
      
      apply rprems
      apply simp_all
      subgoal apply(simp add: norm_pp ) apply(intro wfR''_upd) by simp
      apply(rule nrest_Rel_mono)
      unfolding sort_one_more_spec_guarded_def 
      apply(cases "i' < length xs' \<and> sorted_wrt_lt (\<^bold><) (take i' xs')", auto)
      apply(simp add: SPEC_timerefine_conv)
      apply(rule SPEC_leq_SPEC_I, simp)
      subgoal premises prems
        unfolding cost_insert_guarded_def cost_is_insert_guarded_step_def
        apply(auto simp add: norm_pp norm_cost intro!: wfR''_upd )
        apply(subst timerefineA_propagate, intro wfR''_upd, simp)+
        apply (simp add: norm_cost )
        apply sc_solve 
        using \<open>i' \<le> N\<close> by auto
      done
  qed

  thm timerefine_mono2 timerefine_R_mono_wfR''

lemma timerefine_mono_both: 
  fixes R :: "_ \<Rightarrow> ('c, 'd::{complete_lattice,nonneg,mult_zero,ordered_semiring}) acost"
  assumes "wfR'' R'"
    and "R\<le>R'"
  shows "c\<le>c' \<Longrightarrow> timerefine R c \<le> timerefine R' c'"
  apply(cases c) apply simp
  apply(cases c') apply (auto simp: less_eq_acost_def timerefine_def split: nrest.splits option.splits simp: le_fun_def)
  subgoal  by (metis le_some_optE) 
  proof (goal_cases)
    case (1 x2 x2a x x2b x2c xa)
    then have l: "\<And>ac. the_acost x2b ac \<le>  the_acost x2c ac"
      apply(cases x2b; cases x2c) unfolding less_eq_acost_def  
      apply auto
      by (metis acost.sel less_eq_acost_def less_eq_option_Some)
    show ?case
      apply(rule Sum_any_mono)
      subgoal using l apply(rule ordered_semiring_class.mult_mono)
        subgoal using assms(2) unfolding le_fun_def
          by (simp add: the_acost_mono)
        subgoal by (simp add: needname_nonneg)
        subgoal
          by (simp add: needname_nonneg)
        done
      apply(rule wfR_finite_mult_left2) by fact
  qed 


lemma fun_upd_parallel_I: "f\<le>f' \<Longrightarrow> y\<le>y' \<Longrightarrow> f(x:=y) \<le> f'(x:=y')"
  unfolding fun_upd_def le_fun_def  
  by auto

lemma cost_insert_guarded_mono: "a \<le> b \<Longrightarrow> cost_insert_guarded a \<le> cost_insert_guarded b"
  unfolding cost_insert_guarded_def 
          unfolding cost_insert_guarded_def cost_is_insert_guarded_step_def
          apply(auto simp add: norm_pp norm_cost intro!: wfR''_upd )
          apply sc_solve by auto

lemma cost_insert_mono: "a \<le> b \<Longrightarrow> cost_insert a \<le> cost_insert b"
  unfolding cost_insert_def 
          unfolding cost_is_insert_step_def
        apply(auto simp add: norm_pp norm_cost intro!: wfR''_upd )
          apply sc_solve by auto


  lemma is_insert3_guarded_sorts_one_more: 
    assumes "(xs,xs')\<in>slicep_rel l h" "(i,i')\<in>idx_shift_rel l" "i<h" "N\<ge>i-l"
    shows "is_insert3_guarded xs l i \<le>\<Down>(slice_rel xs l h) (timerefine (TR_is_insert3 N) (sort_one_more_spec_guarded xs' i'))"
    using assms apply -
      apply(rule order_trans)
     apply(rule is_insert3_guarded_correct'[OF assms(1-3)])
    apply(rule nrest_Rel_mono)
    unfolding TR_is_insert3_def
      apply(subst (2) timerefine_iter2[symmetric])
      subgoal by(auto simp: norm_pp intro!: wfR''_upd)
      subgoal by(auto intro!: wfR''_upd)
      apply(subst timerefine_iter2[symmetric])
      subgoal by(auto simp: norm_pp intro!: wfR''_upd)
      subgoal by(auto intro!: wfR''_upd)
      apply(subst timerefine_iter2[symmetric])
      subgoal by(auto simp: norm_pp intro!: wfR''_upd)
      subgoal by(auto intro!: wfR''_upd)
      apply(rule timerefine_mono2)
      subgoal by(auto simp: norm_pp intro!: wfR''_upd)
      apply(rule timerefine_mono_both)
      subgoal by(auto simp: norm_pp intro!: wfR''_upd)
      subgoal premises prems
        apply(intro fun_upd_parallel_I cost_insert_guarded_mono cost_insert_mono)
        using assms(4)  by simp_all
      apply(rule order.trans) 
       apply(rule is_insert_guarded_sorts_one_more)
      apply simp
      done




  lemma gen_insertion_sort_guarded2_refine: 
    "\<lbrakk> (xsi,xs) \<in> slicep_rel l h; (ii,i)\<in>idx_shift_rel l; (ji,j)\<in>idx_shift_rel l; j\<le>N \<rbrakk> 
      \<Longrightarrow> gen_insertion_sort_guarded2 l ii ji xsi \<le>\<Down>(slice_rel xsi l h) (timerefine (TR_is_insert3 N) (gen_insertion_sort_guarded i j xs))"
    unfolding gen_insertion_sort_guarded2_def gen_insertion_sort_guarded_def monadic_WHILEIET_def
    apply (refine_rcg is_insert3_guarded_sorts_one_more monadic_WHILEIT_refine' bindT_refine_conc_time_my_inres SPECc2_refine')
    supply [refine_dref_RELATES] = 
      RELATESI[of "slice_rel xsi l h \<times>\<^sub>r idx_shift_rel l"] RELATESI[of "idx_shift_rel l"]
    apply refine_dref_type
    apply (clarsimp_all simp: inres_SPECc2)
    applyS (auto simp: idx_shift_rel_def slicep_rel_def)[]
    
    applyS (auto simp: idx_shift_rel_def slice_rel_alt eq_outside_range_triv slicep_rel_def)[]
    applyS (auto simp: idx_shift_rel_def slicep_rel_def)[]
    subgoal unfolding TR_is_insert3_def apply(simp add: norm_pp )   by(auto intro!: preserves_curr_other_updI)
    applyS (auto simp: idx_shift_rel_def slice_rel_alt) []
    applyS (auto simp: idx_shift_rel_def slicep_rel_def)[]
    applyS (auto simp: idx_shift_rel_def slice_rel_alt) []
    applyS (auto simp: idx_shift_rel_def slice_rel_alt) []
    
    applyS (auto simp: idx_shift_rel_def slicep_rel_def)[]
    subgoal unfolding TR_is_insert3_def apply(simp add: norm_pp )   by(auto intro!: preserves_curr_other_updI)
    
    subgoal
      apply (clarsimp simp: idx_shift_rel_def slice_rel_alt) []
      by (erule (1) eq_outside_range_gen_trans; auto)
    done
    
end    
    
    
     
context sort_impl_context begin

  
    
  definition "gen_insertion_sort_guarded3 l i h xs \<equiv> doN {
    ASSERT (l \<le> i);
    (xs,_)\<leftarrow>monadic_WHILEIT (\<lambda>_. True)
      (\<lambda>(xs,i). SPECc2 ''icmp_slt'' (<) i h) 
      (\<lambda>(xs,i). doN {
        xs \<leftarrow> is_insert_guarded4 xs l i;
        ASSERT (i<h);
        i \<leftarrow> SPECc2 ''add'' (+) i 1;
        RETURN (xs,i)
      }) (xs,i);
    RETURN xs
  }"  


  lemma gen_insertion_sort_guarded3_refines:
    "(l,l')\<in>Id \<Longrightarrow> (i,i')\<in>Id \<Longrightarrow> (h,h')\<in>Id \<Longrightarrow> (xs,xs')\<in>Id
      \<Longrightarrow> gen_insertion_sort_guarded3 l i h xs \<le> \<Down>Id (timerefine TR_cmp_swap (gen_insertion_sort_guarded2 l' i' h' xs'))"
    supply conc_Id[simp del]
    unfolding gen_insertion_sort_guarded3_def gen_insertion_sort_guarded2_def
    supply [refine] = is_insert_guarded4_refines
    apply(refine_rcg MIf_refine SPECc2_refine' bindT_refine_conc_time_my_inres monadic_WHILEIT_refine' )
                        apply refine_dref_type
  apply(all \<open>(intro  preserves_curr_other_updI wfR''_upd wfR''_TId preserves_curr_TId)?\<close>)
  apply (simp_all (no_asm))
  apply (auto simp: timerefineA_cost)  
  done



  




  sepref_register    
    guarded_insertion_sort3: "gen_insertion_sort_guarded3"

  sepref_def guarded_insertion_sort_impl is "uncurry3 (PR_CONST (gen_insertion_sort_guarded3))" 
    :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (array_assn elem_assn)\<^sup>d \<rightarrow>\<^sub>a array_assn elem_assn"
    unfolding gen_insertion_sort_guarded3_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref    

end 
    
    
    
    
    
    
(*    
    
  definition "sort_one_more_spec GUARDED xs i \<equiv> doN {
      ASSERT (i<length xs \<and> sorted_wrt_lt (\<^bold><) (take i xs));
      ASSERT (\<not>GUARDED \<longrightarrow> 0<i \<and> \<not>xs!i\<^bold><xs!0); 
      SPEC (\<lambda>xs'. mset (take (i+1) xs') = mset (take (i+1) xs) \<and> drop (i+1) xs' = drop (i+1) xs \<and> length xs'=length xs \<and> sorted_wrt_lt (\<^bold><) (take (i+1) xs') \<and> (\<not>GUARDED \<longrightarrow> xs'!0 = xs!0))
    }"  
    
  (* For presentation in paper *)  
  lemma "sort_one_more_spec G xs i = doN {
      ASSERT (i<length xs \<and> sorted_wrt_lt (\<^bold><) (slice 0 i xs));
      ASSERT (G \<or> 0<i \<and> \<not>(xs!i\<^bold><xs!0));
      SPEC (\<lambda>xs'. inres (slice_sort_spec (\<^bold><) xs 0 (i+1)) xs' \<and> (\<not>G \<longrightarrow> xs'!0 = xs!0))
    }"
    unfolding slice_sort_spec_def sort_one_more_spec_def
    apply (simp only: pw_eq_iff refine_pw_simps; safe)
    apply (simp_all add: Misc.slice_def sort_spec_def)
    done
    
  lemma "sort_one_more_spec G xs i = doN {
      ASSERT (i<length xs \<and> sorted_wrt_lt (\<^bold><) (slice 0 i xs));
      ASSERT (G \<or> 0<i \<and> \<not>(xs!i\<^bold><xs!0));
      SPEC (\<lambda>xs'. sort_spec (\<^bold><) (slice 0 (i+1) xs) (slice 0 (i+1) xs') 
          \<and> length xs'=length xs 
          \<and> slice (i+1) (length xs) xs' = slice (i+1) (length xs) xs 
          \<and> (\<not>G \<longrightarrow> xs'!0 = xs!0))
    }"
    unfolding slice_sort_spec_def sort_one_more_spec_def
    apply (simp only: pw_eq_iff refine_pw_simps; safe)
    apply (simp_all add: Misc.slice_def sort_spec_def)
    done
    
    
    
  lemma conv_idxs_to_drop_eq: "length xs = length ys \<Longrightarrow> (\<forall>j\<in>{n..<length ys}. xs ! j = ys ! j) \<longleftrightarrow> drop n xs = drop n ys"
    apply (simp add: list_eq_iff_nth_eq)
    apply (safe;clarsimp)
    by (metis add_diff_cancel_left' diff_less_mono le_iff_add)

    (*
  lemma is_insert_sorts_one_more[param_fo, THEN nres_relD,refine]: 
    "(is_insert_spec GUARDED, sort_one_more_spec GUARDED) 
        \<in> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel"
    apply (intro fun_relI nres_relI; auto)    
    unfolding sort_one_more_spec_def is_insert_spec_alt is_insert_spec_aux_def
    apply (clarsimp simp: pw_le_iff refine_pw_simps)
    apply (intro conjI)
    subgoal sledgehammer sorry
    subgoal apply (simp add: list_eq_iff_nth_eq)
    *)
    
        
  lemma is_insert_sorts_one_more[param_fo, THEN nres_relD,refine]: 
    "(is_insert_spec GUARDED, sort_one_more_spec GUARDED) 
        \<in> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel"
    apply (intro fun_relI nres_relI)    
    using is_insert_spec_aux_imp_sorted is_insert_spec_aux_imp_mset_eq' 
      is_insert_spec_aux_imp_rest_eq is_insert_spec_aux_imp_length_eq
    unfolding sort_one_more_spec_def is_insert_spec_alt
    apply (simp add: pw_le_iff refine_pw_simps)
    apply (auto simp: )
    done

      
  definition "gen_insertion_sort GUARDED i\<^sub>0 h xs \<equiv> doN {
    ASSERT ((\<not>GUARDED \<longrightarrow> 0<i\<^sub>0) \<and> h\<le>length xs);
    (xs,_)\<leftarrow>WHILEIT (\<lambda>(xs',i). 
        i\<^sub>0\<le>i \<and> i\<le>h \<and> length xs'=length xs \<and> mset (take i xs') = mset (take i xs) \<and> drop i xs' = drop i xs \<and> sorted_wrt_lt (\<^bold><) (take i xs')
      \<and> (\<not>GUARDED \<longrightarrow> xs'!0 = xs!0)
      ) 
      (\<lambda>(xs,i). i<h) 
      (\<lambda>(xs,i). doN {
        xs \<leftarrow> sort_one_more_spec GUARDED xs i;
        ASSERT (i<h);
        let i=i+1;
        RETURN (xs,i)
      }) (xs,i\<^sub>0);
    RETURN xs
  }"  
  
    
  lemma gen_insertion_sort_correct: 
    "\<lbrakk>sorted_wrt_lt (\<^bold><) (take i\<^sub>0 xs); \<not>GUARDED \<longrightarrow> 0<i\<^sub>0; i\<^sub>0<h; h\<le>length xs; \<not>GUARDED \<longrightarrow> (\<forall>i\<in>{i\<^sub>0..<h}. \<exists>j<i. i-j<N \<and> \<not>xs!i \<^bold>< xs!j) \<rbrakk> 
      \<Longrightarrow> gen_insertion_sort GUARDED i\<^sub>0 h xs \<le> slice_sort_spec (\<^bold><) xs 0 h"
    unfolding gen_insertion_sort_def sort_one_more_spec_def slice_sort_spec_def sort_spec_def sorted_sorted_wrt
    apply (refine_vcg 
      WHILEIT_rule[where R="measure (\<lambda>(_,i). length xs - i)"])       
      
    apply (all \<open>(clarsimp;fail)?\<close>) 
    subgoal by clarsimp (metis atLeastLessThan_iff hd_drop_conv_nth less_le_trans)
    subgoal by clarsimp (metis hd_drop_conv_nth less_le_trans take_Suc_conv_app_nth union_code)
    subgoal apply clarsimp by (metis drop_Suc tl_drop)
    subgoal apply simp by force
    subgoal apply simp by (metis Misc.slice_def drop0 drop_take)
    subgoal by (clarsimp simp: Misc.slice_def)    
    done

(*
  
  lemma "\<lbrakk>part_sorted_wrt (le_by_lt (\<^bold><)) n xs; sort_spec (\<^bold><) (slice 0 n xs) (slice 0 n xs'); drop n xs' = drop n xs\<rbrakk> 
    \<Longrightarrow> part_sorted_wrt (le_by_lt (\<^bold><)) n xs'"
    unfolding sort_spec_def
    apply auto
  proof -
    define xs\<^sub>1 where "xs\<^sub>1 = slice 0 n xs"
    define xs\<^sub>2 where "xs\<^sub>2 = drop n xs"
    have "xs = xs\<^sub>1@xs\<^sub>2" unfolding xs\<^sub>1_def xs\<^sub>2_def Misc.slice_def by auto
    thm part_sorted_concatI
  
    
    
    unfolding sort_spec_def
    apply auto
    
    
  oops end end
*)  


      
  definition "gen_insertion_sort2 GUARDED l i h xs \<equiv> doN {
    (xs,_)\<leftarrow>WHILET
      (\<lambda>(xs,i). i<h) 
      (\<lambda>(xs,i). doN {
        xs \<leftarrow> is_insert3 GUARDED xs l i;
        ASSERT (i<h);
        let i=i+1;
        RETURN (xs,i)
      }) (xs,i);
    RETURN xs
  }"  
    
  lemma is_insert3_sorts_one_more: 
    assumes "(xs,xs')\<in>slicep_rel l h" "(i,i')\<in>idx_shift_rel l" "i<h"
    shows "is_insert3 GUARDED xs l i \<le>\<Down>(slice_rel xs l h) (sort_one_more_spec GUARDED xs' i')"
  proof -
    note is_insert3_correct' 
    also note is_insert_sorts_one_more
    finally show ?thesis using assms by simp
  qed

  
  lemma gen_insertion_sort2_refine: 
    "\<lbrakk> (xsi,xs) \<in> slicep_rel l h; (ii,i)\<in>idx_shift_rel l; (ji,j)\<in>idx_shift_rel l \<rbrakk> 
      \<Longrightarrow> gen_insertion_sort2 GUARDED l ii ji xsi \<le>\<Down>(slice_rel xsi l h) (gen_insertion_sort GUARDED i j xs)"
    unfolding gen_insertion_sort_def gen_insertion_sort2_def
    apply (refine_rcg is_insert3_sorts_one_more)
    supply [refine_dref_RELATES] = RELATESI[of "slice_rel xsi l h \<times>\<^sub>r idx_shift_rel l"] 
    apply refine_dref_type
    apply clarsimp_all
    applyS (auto simp: idx_shift_rel_def slice_rel_alt eq_outside_range_triv slicep_rel_def)[]
    applyS (auto simp: idx_shift_rel_def slicep_rel_def)[]
    applyS (auto simp: idx_shift_rel_def slice_rel_alt) []
    applyS (auto simp: idx_shift_rel_def slicep_rel_def)[]
    subgoal
      apply (clarsimp simp: idx_shift_rel_def slice_rel_alt) []
      by (erule (1) eq_outside_range_gen_trans; auto)
    done
  
        
end
    
context sort_impl_context begin
  
  sepref_register 
    unguarded_insertion_sort2: "gen_insertion_sort2 False"
    guarded_insertion_sort2: "gen_insertion_sort2 True"
    
  sepref_def unguarded_insertion_sort_impl is "uncurry3 (PR_CONST (gen_insertion_sort2 False))" 
    :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (woarray_assn elem_assn)\<^sup>d \<rightarrow>\<^sub>a woarray_assn elem_assn"
    unfolding gen_insertion_sort2_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    
  sepref_def guarded_insertion_sort_impl is "uncurry3 (PR_CONST (gen_insertion_sort2 True))" 
    :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (woarray_assn elem_assn)\<^sup>d \<rightarrow>\<^sub>a woarray_assn elem_assn"
    unfolding gen_insertion_sort2_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    
end    

(*
context parameterized_weak_ordering begin  

  definition "is_insert_param GUARDED cparam xs l i \<equiv> doN {
  
    ASSERT (i<length xs);
    
    \<^cancel>\<open>ASSERT (set xs \<subseteq> cdom);\<close>
    
    xs \<leftarrow> mop_to_eo_conv xs;
    
    (x,xs) \<leftarrow> mop_eo_extract xs i;

    \<^cancel>\<open>
    ASSERT (x \<in> cdom);
    ASSERT (\<forall>x. Some x \<in> set xs \<longrightarrow> x\<in>cdom);
    \<close>
      
    (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i'). True) 
      (\<lambda>(xs,i). if \<not>GUARDED \<or> i>l then doN {ASSERT (i>0); pcmpo_v_idx2 cparam xs x (i-1)} else RETURN False) (\<lambda>(xs,i). doN {
        ASSERT (i>0);
        (t,xs) \<leftarrow> mop_eo_extract xs (i-1);
        xs \<leftarrow> mop_eo_set xs i t;
        let i = i-1;
        RETURN (xs,i)
      }) (xs,i);
  
    xs \<leftarrow> mop_eo_set xs i x;  
    
    xs \<leftarrow> mop_to_wo_conv xs;
    
    RETURN xs
  }"
  

  term is_insert4
      
  lemma is_insert_param_refine[refine]:
    assumes "(xs',xs)\<in>cdom_list_rel cparam"
    assumes "(l',l)\<in>Id"
    assumes "(i',i)\<in>Id"
    shows "is_insert_param GUARDED cparam xs' l' i' \<le>\<Down>(cdom_list_rel cparam) (WO.is_insert3 cparam GUARDED xs l i)"
    supply [refine_dref_RELATES] = RELATESI[of "cdom_list_rel cparam"] RELATESI[of "cdom_olist_rel cparam"]
    unfolding is_insert_param_def WO.is_insert3_def
    apply refine_rcg
    apply (refine_dref_type)
    using assms
    by (auto simp: cdom_list_rel_alt cdom_olist_rel_alt in_br_conv)
      
  definition "gen_insertion_sort_param GUARDED cparam l i h xs \<equiv> doN {
    (xs,_)\<leftarrow>WHILET
      (\<lambda>(xs,i). i<h) 
      (\<lambda>(xs,i). doN {
        xs \<leftarrow> is_insert_param GUARDED cparam xs l i;
        ASSERT (i<h);
        let i=i+1;
        RETURN (xs,i)
      }) (xs,i);
    RETURN xs
  }"  

  lemma gen_insertion_sort_param_refinep[refine]:
    "\<lbrakk>
      (l',l)\<in>Id; (i',i)\<in>Id; (h',h)\<in>Id; (xs',xs)\<in>cdom_list_rel cparam
    \<rbrakk> \<Longrightarrow> gen_insertion_sort_param GUARDED cparam l' i' h' xs' 
    \<le> \<Down>(cdom_list_rel cparam) (WO.gen_insertion_sort2 cparam GUARDED l i h xs)"
    unfolding gen_insertion_sort_param_def WO.gen_insertion_sort2_def
    supply [refine_dref_RELATES] = RELATESI[of "cdom_list_rel cparam"]
    apply refine_rcg
    apply refine_dref_type
    apply auto
    done

  

end

    
context parameterized_sort_impl_context begin
    
  sepref_register 
    is_guarded_param_insert3: "is_insert_param True"
    is_unguarded_param_insert3: "is_insert_param False"
  
  sepref_def is_guarded_param_insert_impl is "uncurry3 (PR_CONST (is_insert_param True))" 
    :: "cparam_assn\<^sup>k *\<^sub>a wo_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a wo_assn"
    unfolding is_insert_param_def PR_CONST_def
    apply (simp named_ss HOL_ss:)
    supply [[goals_limit = 1]]
    apply (annot_snat_const "TYPE(size_t)")
    by sepref

  sepref_def is_unguarded_param_insert_impl is "uncurry3 (PR_CONST (is_insert_param False))" 
    :: "cparam_assn\<^sup>k *\<^sub>a wo_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a wo_assn"
    unfolding is_insert_param_def PR_CONST_def
    apply (simp named_ss HOL_ss:)
    supply [[goals_limit = 1]]
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
  

    
  sepref_register 
    unguarded_insertion_sort_param: "gen_insertion_sort_param False"
    guarded_insertion_sort_param: "gen_insertion_sort_param True"
    
  sepref_def unguarded_insertion_sort_param_impl is "uncurry4 (PR_CONST (gen_insertion_sort_param False))" 
    :: "cparam_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a wo_assn\<^sup>d \<rightarrow>\<^sub>a wo_assn"
    unfolding gen_insertion_sort_param_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    
  sepref_def guarded_insertion_sort_param_impl is "uncurry4 (PR_CONST (gen_insertion_sort_param True))" 
    :: "cparam_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a wo_assn\<^sup>d \<rightarrow>\<^sub>a wo_assn"
    unfolding gen_insertion_sort_param_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    
end
*)
*)

end
