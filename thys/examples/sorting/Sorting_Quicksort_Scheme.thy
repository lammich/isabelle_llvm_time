theory Sorting_Quicksort_Scheme
imports Sorting_Setup Sorting_Partially_Sorted
begin

  




  abbreviation "is_threshold \<equiv> 16::nat"

  context weak_ordering begin

    definition "partition1_spec xs \<equiv> doN { 
      ASSERT (length xs \<ge> 4); 
      SPEC (\<lambda>(xs1,xs2). mset xs = mset xs1 + mset xs2 \<and> xs1\<noteq>[] \<and> xs2\<noteq>[] \<and> slice_LT (\<^bold>\<le>) xs1 xs2) (\<lambda>_. cost ''partition'' (enat (length xs)))
    }"
definition introsort_aux1 :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "introsort_aux1 tf xs d \<equiv> RECT' (\<lambda>introsort_aux1 (xs,d). doN {
      lxs \<leftarrow> SPECT [length xs \<mapsto> cost ''list_length'' 1];
      b \<leftarrow> SPECc2 ''lt'' (<) is_threshold (length xs);
      MIf b (doN {
        b2 \<leftarrow> SPECc2 ''eq'' (=) d 0;
        MIf b2 (
          SPEC (sort_spec (\<^bold><) xs) (\<lambda>_. cost ''slice_sort_p'' (enat (tf (length xs))))
        )( doN {
          (xs1,xs2)\<leftarrow>partition1_spec xs;
          d' \<leftarrow> SPECc2 ''sub'' (-) d 1;
          xs1 \<leftarrow> introsort_aux1 (xs1,d');
          xs2 \<leftarrow> introsort_aux1 (xs2,d');
          SPECc2 ''list_append'' (@) xs1 xs2
        })
      }
      ) (
        RETURN xs )
    }) (xs,d)"
    
    lemma slice_strict_LT_imp_LE: "slice_LT (\<^bold><) xs ys \<Longrightarrow> slice_LT (le_by_lt (\<^bold><)) xs ys"  
      apply (erule slice_LT_mono)
      by (meson le_by_lt_def wo_less_asym)



definition introsort_aux_cost :: "_ \<Rightarrow> nat * nat \<Rightarrow> (char list, enat) acost"
  where "introsort_aux_cost tf = (\<lambda>(lxs, d). lift_acost (
        cost ''if'' (2^(d+1)-1) + cost ''eq'' (2^(d+1)-1) + cost ''if'' (2^(d+1)-1)
         + cost ''lt'' (2^(d+1)-1) + cost ''call'' ((2^(d+1)-1)) 
        + cost ''list_length'' (2^(d+1)-1) 
        + cost ''sub'' (2^(d+1)-1) 
        + cost ''list_append'' (2^(d+1)-1) 
        +   cost ''slice_sort_p'' (tf (lxs)) + cost ''partition'' (d*(lxs))
         )
        )"
 

lemma haha: "b>0 \<Longrightarrow> Suc (Suc (4 * 2 ^ (b - Suc 0) - Suc (Suc 0))) \<le> 2 * 2 ^ b"
proof -
  assume "b>0"
  then obtain b' where b: "b=b'+1"  
    by (metis Groups.add_ac(2) Suc_eq_plus1_left Suc_pred)  
  have ge2: "4 * (2::nat) ^ (b') \<ge> 2" by auto
  have "Suc (Suc (4 * 2 ^ (b - Suc 0) - Suc (Suc 0)))
      = Suc (Suc (4 * 2 ^ (b') - Suc (Suc 0)))" using b by simp
  also have "\<dots> =  2 + (4*2^b' - 2)" by presburger
  also have "\<dots> = 4*2^b'" using ge2 by auto
  also have "\<dots> = 2*2^(b'+1)" by simp
  also have "\<dots> = 2*2^(b)" using b by simp
  finally
    show ?thesis by simp
  qed

lemma ha: "b>0 \<Longrightarrow> Suc (Suc (8 * 2 ^ (b - Suc 0) - Suc (Suc 0))) \<le> 4 * 2 ^ b"
proof -
  assume "b>0"
  then obtain b' where b: "b=b'+1"  
    by (metis Groups.add_ac(2) Suc_eq_plus1_left Suc_pred)  
  have ge2: "4 * (2::nat) ^ (b') \<ge> 2" by auto
  have "Suc (Suc (4 * 2 ^ (b - Suc 0) - Suc (Suc 0)))
      = Suc (Suc (4 * 2 ^ (b') - Suc (Suc 0)))" using b by simp
  also have "\<dots> =  2 + (4*2^b' - 2)" by presburger
  also have "\<dots> = 4*2^b'" using ge2 by auto
  also have "\<dots> = 2*2^(b'+1)" by simp
  also have "\<dots> = 2*2^(b)" using b by simp
  finally
    show ?thesis by simp
  qed
 

lemma argh: "b>0 \<Longrightarrow> 4 * 2 ^ (b - Suc 0) - Suc 0 \<le> 2 * 2 ^ b - Suc 0"
proof -
  assume "b>0"
  then obtain b' where b: "b=b'+1"  
    by (metis Groups.add_ac(2) Suc_eq_plus1_left Suc_pred)  
  then have "4 * 2 ^ (b - Suc 0) - Suc 0 = 4 * 2 ^ ((b'+1) - Suc 0) - Suc 0 "
    by auto
  also have "\<dots> = 2 * (2*2^b') - Suc 0" apply simp done
  also have "\<dots> = 2 * (2^(b'+1)) - Suc 0" apply simp done
  also have "\<dots> = 2 * 2 ^ b - Suc 0" using b apply simp done
  finally show ?thesis by simp
qed

lemma argh2: "b>0 \<Longrightarrow> Suc (4 * 2 ^ (b - Suc 0) - Suc (Suc 0)) \<le> 2 * 2 ^ b - Suc 0"
proof -
  assume "b>0"
  then obtain b' where b: "b=b'+1"  
    by (metis Groups.add_ac(2) Suc_eq_plus1_left Suc_pred)  
  then have "Suc (4 * 2 ^ (b - Suc 0) - Suc (Suc 0)) = Suc (4 * 2 ^ ((b'+1) - Suc 0) - Suc (Suc 0) )"
    by auto
  also have "\<dots> = Suc (2 * (2*2^b') - Suc (Suc 0))" apply simp done
  also have "\<dots> = (2 * (2*2^b') - Suc 0)" apply(subst Suc_diff_Suc) apply auto
    by (simp add: Suc_lessI)
  also have "\<dots> = 2 * (2^(b'+1)) - Suc 0" apply simp done
  also have "\<dots> = 2 * 2 ^ b - Suc 0" using b apply simp done
  finally show ?thesis by simp
qed

lemma z: "b>0 \<Longrightarrow> (b - Suc 0) * A + (b - Suc 0) * B + (B + A) = b*(A+B)"
proof -
  assume "b>0"
  then obtain b' where b: "b=b'+1"  
    by (metis Groups.add_ac(2) Suc_eq_plus1_left Suc_pred)  
  then have "(b - Suc 0) * A + (b - Suc 0) * B + (B + A)
      = (b') * A + (b') * B + (B + A)" by simp
  also have "\<dots> = (b'+1) * (B+A)" by (auto simp: ring_distribs)
  also have "\<dots> = b * (B+A)" using b by simp
  finally show ?thesis by simp
qed

lemma lengths_sums_if_msets_do: "mset a = mset b + mset c \<Longrightarrow> length a = length b + length c"
    by (metis add.commute length_append less_or_eq_imp_le mset_append mset_eq_length)  

lemma zz: "Suc 0 \<le> 4 * 2 ^ b - Suc (Suc 0)"
proof -
  show ?thesis 
    apply(rule add_le_imp_le_diff)  apply simp
    apply(rule order.trans[where b="4 * 2 ^ 0"])
     apply simp
    apply  simp
    done      
qed

definition "introsort_aux_cost' tf  = (\<lambda>(xs,d). introsort_aux_cost tf (length xs,d) )"


  lemma introsort_aux1_correct':
    assumes tf_suplinear: "\<And>a b c. a+b\<le>c \<Longrightarrow> tf a + tf b \<le> tf c"
    shows 
   "introsort_aux1 tf xs d \<le> SPEC (\<lambda>xs'. mset xs' = mset xs \<and> part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold xs') (\<lambda>_. introsort_aux_cost' tf (xs, d))"
    
      unfolding introsort_aux1_def partition1_spec_def sort_spec_def
 

      apply (rule RECT'_rule_arb[where V="measure (\<lambda>(xs,d). d+1)" and pre="\<lambda>xss (xs',d). xss=xs'"])
      apply refine_mono
      apply (all \<open>(auto intro: sorted_wrt_imp_part_sorted part_sorted_wrt_init; fail)?\<close>)

      unfolding SPEC_REST_emb'_conv SPECc2_alt
      subgoal premises prems for f xss x
      apply(rule gwp_specifies_I) 
        apply(refine_vcg \<open>-\<close> rules: prems(1)[THEN gwp_specifies_rev_I, THEN gwp_conseq_0])
        thm prems(1)[THEN gwp_specifies_rev_I, THEN gwp_conseq_0]
        using  prems(2)
      subgoal unfolding emb'_def apply auto
        subgoal  by (simp add: sorted_wrt_imp_part_sorted)
        subgoal unfolding introsort_aux_cost_def introsort_aux_cost'_def
            apply (simp add: lift_acost_propagate lift_acost_cost)
          apply sc_solve by (auto simp: one_enat_def)
        done
            apply simp apply simp
          apply simp apply simp
      subgoal
        apply (auto simp add: emb'_def handy_if_lemma)
        
        subgoal  using prems(2) by simp  
        subgoal 
          apply (rule part_sorted_concatI; assumption?) 
          apply (subst slice_LT_mset_eq1, assumption)
          apply (subst slice_LT_mset_eq2, assumption)
          using le_by_lt by blast
        subgoal premises p
          unfolding introsort_aux_cost_def introsort_aux_cost'_def
          using p(3,8)
          apply (simp add: lift_acost_propagate lift_acost_cost)
          apply sc_solve_debug apply safe apply(all \<open>((auto simp: sc_solve_debug_def),fail)?\<close>)
          subgoal (* append *) unfolding sc_solve_debug_def by (simp add: one_enat_def argh) 
          subgoal (* partition *)
            unfolding sc_solve_debug_def
            apply(drule lengths_sums_if_msets_do)
            apply auto apply(simp only: z) apply simp done
          subgoal (* sub *) unfolding sc_solve_debug_def by (simp add: one_enat_def argh) 
          subgoal (* ''slice_sort_p'' *) unfolding sc_solve_debug_def
            apply (simp add: one_enat_def)
            apply(rule tf_suplinear)
            by (metis add.commute length_append less_or_eq_imp_le mset_append mset_eq_length) 
          subgoal  (* if *) unfolding sc_solve_debug_def apply (simp add: one_enat_def argh) 
            apply(rule add_le_imp_le_diff) apply simp apply(rule ha) by simp 
          subgoal  (* list_length *) unfolding sc_solve_debug_def apply (simp add: one_enat_def argh) 
            apply(rule add_le_imp_le_diff) apply simp apply(rule haha) by simp 
          subgoal (* eq *) unfolding sc_solve_debug_def by (simp add: one_enat_def argh) 
          subgoal (* call *) unfolding sc_solve_debug_def apply (simp add: one_enat_def ) 
            apply(rule argh2) by simp 
          subgoal  (* lt *) unfolding sc_solve_debug_def by (simp add: one_enat_def argh)
          done
        done
      subgoal by auto
      subgoal
        using prems(2) apply (auto simp add: emb'_def handy_if_lemma)
        subgoal by (simp add: part_sorted_wrt_init)
        subgoal unfolding introsort_aux_cost_def introsort_aux_cost'_def apply (simp add: lift_acost_propagate lift_acost_cost)
          apply sc_solve apply (auto simp: one_enat_def)
          subgoal 
            by(rule zz)
          subgoal  
            by (smt Suc_leI Suc_pred le_SucE mult_pos_pos n_not_Suc_n numeral_2_eq_2 one_eq_mult_iff pos2 zero_less_power)  
          done
        done
      done
    done

  lemma introsort_aux1_correct:
    assumes tf_suplinear: "\<And>a b c. a+b\<le>c \<Longrightarrow> tf a + tf b \<le> tf c" "lxs = length xs"
    shows 
   "introsort_aux1 tf xs d \<le> SPEC (\<lambda>xs'. mset xs' = mset xs \<and> part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold xs') (\<lambda>_. introsort_aux_cost tf (lxs, d))"
    unfolding assms(2)
    apply(rule  introsort_aux1_correct'[OF assms(1), unfolded introsort_aux_cost'_def, simplified])
    by simp

      
    definition "partition2_spec xs \<equiv> doN { 
      ASSERT (length xs \<ge> 4); 
      SPEC (\<lambda>(xs',i). mset xs' = mset xs \<and> 0<i \<and> i<length xs \<and> slice_LT (\<^bold>\<le>) (take i xs') (drop i xs')) (\<lambda>_. cost ''partition'' (enat (length xs)))
    }"
      
    lemma partition2_spec_refine: "(xs,xs')\<in>Id \<Longrightarrow> partition2_spec xs \<le>\<Down>(br (\<lambda>(xs,i). (take i xs, drop i xs)) (\<lambda>(xs,i). 0<i \<and> i<length xs)) (timerefine TId (partition1_spec xs'))"
      unfolding partition1_spec_def partition2_spec_def
      apply (intro refine0 SPEC_both_refine)
       apply (auto dest: mset_eq_length simp: in_br_conv simp flip: mset_append)
      subgoal
        using mset_eq_length by fastforce
      subgoal
        using mset_eq_length by force
      done
      
    definition introsort_aux2 :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "introsort_aux2 tf xs d \<equiv> RECT' (\<lambda>introsort_aux (xs,d). doN {
      lxs \<leftarrow> SPECT [length xs \<mapsto> cost ''list_length'' 1];
      b \<leftarrow> SPECc2 ''lt'' (<) is_threshold lxs;
      MIf b (doN {
        b2 \<leftarrow> SPECc2 ''eq'' (=) d 0;
        MIf b2 (
          SPEC (sort_spec (\<^bold><) xs) (\<lambda>_. cost ''slice_sort_p'' (enat (tf (length xs))))
        )( doN {
          (xs,m)\<leftarrow>partition2_spec xs;
          ASSERT (m\<le>length xs);
          d' \<leftarrow> SPECc2 ''sub'' (-) d 1;
          xs1 \<leftarrow> introsort_aux (take m xs,d');
          xs2 \<leftarrow> introsort_aux (drop m xs,d');
          SPECc2 ''list_append'' (@) xs1 xs2
        })
      }
      ) (
        RETURN xs )
    }) (xs,d)"
                                                                                       
    lemma introsort_aux2_refine: "introsort_aux2 tf xs d \<le>\<Down>Id (timerefine TId (introsort_aux1 tf xs d))"  
      unfolding introsort_aux2_def introsort_aux1_def
      apply (refine_rcg partition2_spec_refine SPEC_both_refine MIf_refine SPECc2_refine RECT'_refine_t bindT_refine_conc_time_my_inres)
      apply refine_dref_type
      apply refine_mono
      apply (auto simp: in_br_conv cost_n_leq_TId_n)
      done
      
    
    definition "partition3_spec xs l h \<equiv> doN { 
      ASSERT (h-l\<ge>4 \<and> h\<le>length xs); 
      SPEC (\<lambda>(xs',i). slice_eq_mset l h xs' xs \<and> l<i \<and> i<h \<and> slice_LT (\<^bold>\<le>) (slice l i xs') (slice i h xs')) (\<lambda>_. cost ''partition'' (enat (h-l)))
    }"
 
abbreviation "TR_i_aux \<equiv> (TId(''list_append'':=0,''list_length'':=cost ''sub'' 1))"

    lemma partition3_spec_refine: "(xsi,xs) \<in> slice_rel xs\<^sub>0 l h \<Longrightarrow> partition3_spec xsi l h  \<le>\<Down>(slice_rel xs\<^sub>0 l h \<times>\<^sub>r idx_shift_rel l) (timerefine TR_i_aux (partition2_spec xs))"
      unfolding partition3_spec_def partition2_spec_def
      apply (intro refine0 SPEC_both_refine)
       apply (auto simp: slice_rel_def in_br_conv) [2]
      subgoal for xs'i ii
        apply (rule exI[where x="slice l h xs'i"])
        apply (rule conjI)
        subgoal by (auto simp: slice_eq_mset_def)
        apply (simp add: idx_shift_rel_alt)
        by (auto simp: slice_eq_mset_def take_slice drop_slice intro!: cost_mono)
      done

      
    lemma partition3_spec_refine': "\<lbrakk>(xsi,xs) \<in> slicep_rel l h; xsi'=xsi; l'=l; h'=h\<rbrakk> 
      \<Longrightarrow> partition3_spec xsi l h  \<le>\<Down>(slice_rel xsi' l' h' \<times>\<^sub>r idx_shift_rel l') (timerefine TR_i_aux (partition2_spec xs))"
      unfolding partition3_spec_def partition2_spec_def
      apply (intro refine0 SPEC_both_refine )
      apply (auto simp: slicep_rel_def in_br_conv) [2] 
      subgoal for xs'i ii
        apply (rule exI[where x="slice l h xs'i"])
        apply (rule conjI)
        subgoal by (auto simp: slice_eq_mset_def)
        apply (simp add: idx_shift_rel_alt)
        apply (auto simp: slice_eq_mset_def take_slice drop_slice intro!: cost_mono)
        by (smt less_or_eq_imp_le less_trans slice_eq_mset_alt slice_eq_mset_def slice_in_slice_rel slice_rel_alt)
      done
      
definition "slice_sort_specT T lt xs\<^sub>0 l h \<equiv> doN {
    ASSERT (l\<le>h \<and> h\<le>length xs\<^sub>0);
    SPEC (\<lambda>xs. length xs = length xs\<^sub>0 \<and> take l xs = take l xs\<^sub>0 \<and> drop h xs = drop h xs\<^sub>0 \<and> sort_spec lt (Misc.slice l h xs\<^sub>0) (Misc.slice l h xs))
         (\<lambda>_. T)
  }"
      
    definition introsort_aux3 :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "introsort_aux3 tf xs l h d 
    \<equiv> RECT' (\<lambda>introsort_aux (xs,l,h,d). doN {
        ASSERT (l\<le>h);
        lxs \<leftarrow> SPECc2 ''sub'' (-) h l;
        b \<leftarrow> SPECc2 ''lt'' (<) is_threshold lxs;
        MIf b (doN {
          b2 \<leftarrow> SPECc2 ''eq'' (=) d 0;
          MIf b2 (
            slice_sort_specT (cost ''slice_sort_p'' (enat (tf lxs))) (\<^bold><) xs l h
          )( doN {
            (xs,m)\<leftarrow>partition3_spec xs l h;
            d' \<leftarrow> SPECc2 ''sub'' (-) d 1;
            xs \<leftarrow> introsort_aux (xs,l,m,d');
            xs \<leftarrow> introsort_aux (xs,m,h,d');
            RETURN xs
          })
        }
        ) (
          RETURN xs )
      }) (xs,l,h,d)"




corollary my_slice_sort_spec_refine_sort':
  fixes T :: "nat \<Rightarrow> ecost"
  assumes "\<And>x. T x \<le> timerefineA (TId(''list_append'' := 0, ''list_length'' := cost ''sub'' 1)) (T x)"
  shows 
 "\<lbrakk>(xsi,xs) \<in> slicep_rel l h; xsi'=xsi; l'=l; h'=h; xa=length xs\<rbrakk>
\<Longrightarrow> slice_sort_specT (T xa) lt xsi l h \<le>\<Down>(slice_rel xsi' l' h') (timerefine TR_i_aux (SPEC (sort_spec lt xs) (\<lambda>_. T (length xs))))"
  unfolding slice_sort_specT_def sort_spec_def
  apply(intro refine0 SPEC_both_refine)
  subgoal by (auto simp: slicep_rel_def)
  subgoal for x apply (auto simp: slice_rel_alt)
    apply(rule exI[where x="slice l h x"]) apply (auto simp: eq_outside_range_def slicep_rel_def)
    using assms by blast
  done  

lemma introsort_aux3_refine: "(xsi,xs)\<in>slicep_rel l h
       \<Longrightarrow> introsort_aux3 tf xsi l h d \<le> \<Down>(slice_rel xsi l h) (timerefine TR_i_aux (introsort_aux2 tf xs d))"  
      unfolding introsort_aux3_def introsort_aux2_def
      
      supply recref = RECT'_dep_refine[where 
          R="\<lambda>_. {((xsi::'a list, l, h, di::nat), (xs, d)). (xsi, xs) \<in> slicep_rel l h \<and> di=d}" and
          S="\<lambda>_ (xsi::'a list, l, h, di::nat). slice_rel xsi l h" and
          arb\<^sub>0 = "()"
          ]
      thm recref
      unfolding SPECc2_def
      apply (refine_rcg bindT_refine_conc_time_my_inres MIf_refine
        recref 
        partition3_spec_refine'
        my_slice_sort_spec_refine_sort'
        ; (intro refl)?; (intro wfR''_TId wfR''_upd sp_TId struct_preserving_upd_I )?
        )
            apply refine_mono 

      apply(all \<open>(simp add: timerefineA_update_cost timerefineA_update_apply_same_cost;fail)?\<close>)

     focus  apply (auto simp: slicep_rel_def)    solved
     focus apply refine_dref_type apply (auto simp: slicep_rel_def)    solved
     focus apply refine_dref_type apply (auto simp: slicep_rel_def)   solved
     focus apply simp   solved
     focus apply refine_dref_type apply simp   solved
     focus   apply simp   solved
     focus apply simp solved
     focus apply simp apply (rule IdI) solved
     focus (* first recursive call *)
      apply(rprems)
      apply(auto simp: slice_rel_alt idx_shift_rel_def slicep_rel_take)
      solved
     focus (* second recursive call *) 
      apply(rprems)
      apply(auto simp: slice_rel_alt idx_shift_rel_def slicep_rel_eq_outside_range slicep_rel_drop)
      solved
     focus
      unfolding RETURNT_alt
      apply(rule SPECT_refine_t) 
      subgoal
        apply (clarsimp simp: slice_rel_alt idx_shift_rel_def)
        apply (rule conjI)
        subgoal
          apply (rule slicep_rel_append)
          apply (subst slicep_rel_eq_outside_range; assumption?) 
          by auto 
        subgoal 
          apply (drule (1) eq_outside_range_gen_trans[OF _ _ refl refl])
          apply (erule (1) eq_outside_range_gen_trans)
          apply (auto simp: max_def algebra_simps slicep_rel_def split: if_splits)
          done 
        done
      apply (simp add: timerefineA_update_apply_same_cost)
      solved
     focus
      subgoal by (auto simp: slicep_rel_def)
      solved
      done


    definition "slice_part_sorted_spec xsi l h \<equiv> doN { ASSERT (l\<le>h \<and> h\<le>length xsi); SPEC (\<lambda>xsi'. 
        eq_outside_range xsi' xsi l h 
      \<and> mset (slice l h xsi') = mset (slice l h xsi) 
      \<and> part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold (slice l h xsi')) (\<lambda>_. cost ''slice_part_sorted'' 1)}"
    

    term introsort_aux_cost

declare nrest_Rel_mono[trans]


definition introsort_aux_cost2 :: "_ \<Rightarrow> 'a list * nat \<Rightarrow> (char list, enat) acost"
  where "introsort_aux_cost2 tf = (\<lambda>(xs, d). lift_acost (
        cost ''if'' (2^(d+1)-1) + cost ''eq'' (2^(d+1)-1) + cost ''if'' (2^(d+1)-1)
         + cost ''lt'' (2^(d+1)-1) + cost ''call'' ((2^(d+1)-1)) 
        + cost ''sub'' (2^(d+1)-1)  
        +   cost ''slice_sort_p'' (tf (length xs)) + cost ''partition'' (d*(length xs))
         )
        )"

lemma wfR''TR_i_aux[simp]: "wfR'' TR_i_aux"
  by (auto intro!: wfR''_upd)

lemma costmult_zero_is_zero_enat[simp]: "(x::enat) *m 0 = 0"
  unfolding costmult_def zero_acost_def by auto





lemma 
  SPEC_leq_SPEC_I_strong:
  "A \<le> A' \<Longrightarrow> (\<And>x. A' x \<Longrightarrow> B x \<le> (B' x)) \<Longrightarrow> SPEC A B \<le> (SPEC A' B')"
  apply(auto simp: SPEC_def)
  by (simp add: le_fun_def)  


lemma introsort_aux3_correct:
  assumes tf_mono: "\<And>x y. x \<le> y \<Longrightarrow> tf x \<le> tf y"
    and   tf_sums: "\<And>a b c. a + b \<le> c \<Longrightarrow> tf a + tf b \<le> tf c"    
  shows 
    "introsort_aux3 tf xsi l h d \<le> \<Down>Id (timerefine TR_i_aux (timerefine (TId(''slice_part_sorted'':=introsort_aux_cost tf (h-l,d))) (slice_part_sorted_spec xsi l h)))"
  apply(subst timerefine_iter2)
  subgoal by simp
  subgoal by (auto intro!: wfR''_upd)
  unfolding slice_part_sorted_spec_def
  apply(rule refine0)
  apply(rule order.trans)
   apply(rule introsort_aux3_refine[of xsi "slice l h xsi" l h tf d])
  subgoal by (auto simp: slicep_rel_def)
  apply(rule order.trans)
  apply(rule nrest_Rel_mono)
  apply(rule timerefine_mono2)
  subgoal by (auto intro!: wfR''_upd)
  apply(rule introsort_aux2_refine)
  apply(rule order.trans)
  apply(rule nrest_Rel_mono)
  apply(rule timerefine_mono2)
  subgoal by (auto intro!: wfR''_upd)
  apply(rule order.trans)
  apply(rule nrest_Rel_mono)
  apply(rule timerefine_mono2)
  subgoal by (auto intro!: wfR''_upd)
    apply(rule introsort_aux1_correct)
  subgoal using tf_sums by blast
   apply (simp add: timerefine_id)
   apply(rule order.refl)
  apply(simp add: SPEC_timerefine_conv introsort_aux_cost_def timerefineA_propagate lift_acost_propagate lift_acost_cost
          timerefineA_update_apply_same_cost' costmult_cost pp_fun_upd )
  unfolding slice_rel_def
  apply(subst build_rel_SPEC_conv) apply simp
  apply(rule SPEC_leq_SPEC_I_strong)
  subgoal apply auto  
    using eq_outside_range_def by blast  
  subgoal by(sc_solve) 
  done


lemmas norm_tr = timerefineA_update_apply_same_cost' timerefineA_update_cost timerefineA_cost

lemma TR_sps_important:
  assumes "TR ''slice_part_sorted'' = timerefineA TR_i_aux (introsort_aux_cost tf (h-l,d))"
  shows "(timerefine TR_i_aux (timerefine (TId(''slice_part_sorted'':=introsort_aux_cost tf (h-l,d))) (slice_part_sorted_spec xsi l h)))
    = timerefine TR (slice_part_sorted_spec xsi l h)"
  unfolding slice_part_sorted_spec_def 
  apply(cases "l \<le> h \<and> h \<le> length xsi") apply auto
  apply(simp only: SPEC_timerefine_conv)
  apply(rule SPEC_cong, simp)
  apply(rule ext)
  apply(simp add: norm_tr)
  apply(subst assms(1))
  apply simp
  done


lemma introsort_aux3_correct_flexible:
  assumes tf_mono: "\<And>x y. x \<le> y \<Longrightarrow> tf x \<le> tf y"
    and   tf_sums: "\<And>a b c. a + b \<le> c \<Longrightarrow> tf a + tf b \<le> tf c"    
   and  "TR ''slice_part_sorted'' = timerefineA TR_i_aux (introsort_aux_cost tf (h-l,d))"
  shows 
    "introsort_aux3 tf xsi l h d \<le> \<Down>Id (timerefine TR (slice_part_sorted_spec xsi l h))"
  apply(subst TR_sps_important[symmetric, where TR=TR, OF assms(3)])
  apply(rule introsort_aux3_correct) by fact+


  \<^cancel>\<open>

    proof -
    
(*      have "(xsi, slice l h xsi) \<in> slicep_rel l h"
        unfolding slicep_rel_def apply auto
        *)
    
      have A: "\<Down> (slice_rel xsi l h) (SPEC (\<lambda>xs'. mset xs' = mset (slice l h xsi) \<and> part_sorted_wrt (le_by_lt (\<^bold><)) 16 xs')  (\<lambda>_. cost ''slice_part_sorted'' 1))
        \<le> slice_part_sorted_spec xsi l h"
        apply (clarsimp simp: slice_part_sorted_spec_def pw_le_iff refine_pw_simps)
        (* apply (auto simp: slice_rel_alt  slicep_rel_def) *)
        sorry
      
      note introsort_aux3_refine[of xsi "slice l h xsi" l h tf d]
      also note introsort_aux2_refine (* TODO: enable rules like nrest_Rel_mono here *)
      also note introsort_aux1_correct
      also note A
      fin ally *) show ?thesis (*
        apply (clarsimp simp: slicep_rel_def slice_part_sorted_spec_def)
        apply (auto simp: pw_le_iff refine_pw_simps) *)
        sorry
    qed    \<close>
      
(*
    text \<open>In the paper, we summarized steps 2 and 3. Here are the relevant lemmas: \<close>        
    lemma partition3_spec_alt: "partition3_spec xs l h = \<Down>(slice_rel xs l h \<times>\<^sub>r Id) (doN { ASSERT (l\<le>h \<and> h\<le>length xs); (xs\<^sub>1,xs\<^sub>2) \<leftarrow> partition1_spec (slice l h xs); RETURN (xs\<^sub>1@xs\<^sub>2, l+length xs\<^sub>1) })"  
      unfolding partition3_spec_def partition1_spec_def
      apply (auto simp: pw_eq_iff refine_pw_simps)
      apply (auto simp: slice_eq_mset_def slice_rel_def in_br_conv)
      subgoal
        by (smt Sorting_Misc.slice_len diff_is_0_eq leD le_add_diff_inverse less_imp_le_nat less_le_trans list.size(3) mset_append slice_append)
      subgoal by (metis mset_append)
      subgoal
        by (metis Misc.slice_len add_le_cancel_left drop_all drop_append_miracle leI le_add_diff_inverse)
      subgoal
        by (metis Misc.slice_def add_diff_cancel_left' append_assoc append_eq_conv_conj drop_slice drop_take drop_take_drop_unsplit)
      done

    corollary partition3_spec_alt': "partition3_spec xs l h = \<Down>({((xsi',m),(xs\<^sub>1,xs\<^sub>2)). (xsi',xs\<^sub>1@xs\<^sub>2)\<in>slice_rel xs l h \<and> m=l + length xs\<^sub>1 }) (doN { ASSERT (l\<le>h \<and> h\<le>length xs); partition1_spec (slice l h xs)})"  
      unfolding partition3_spec_alt
      apply (auto simp: pw_eq_iff refine_pw_simps)
      done
      
    corollary partition3_spec_direct_refine: "\<lbrakk> h-l\<ge>4; (xsi,xs)\<in>slicep_rel l h \<rbrakk> \<Longrightarrow> partition3_spec xsi l h \<le> \<Down>({((xsi',m),(xs\<^sub>1,xs\<^sub>2)). (xsi',xs\<^sub>1@xs\<^sub>2)\<in>slice_rel xsi l h \<and> m=l + length xs\<^sub>1 }) (partition1_spec xs)"  
      unfolding partition3_spec_alt'
      apply (auto simp: pw_le_iff refine_pw_simps)
      apply (auto simp: slicep_rel_def)
      done
      
          
    lemma slice_part_sorted_spec_alt: "slice_part_sorted_spec xsi l h = \<Down> (slice_rel xsi l h) (doN { ASSERT(l\<le>h \<and> h\<le>length xsi); SPEC (\<lambda>xs'. mset xs' = mset (slice l h xsi) \<and> part_sorted_wrt (le_by_lt (\<^bold><)) 16 xs') })"
      apply (clarsimp simp: slice_part_sorted_spec_def pw_eq_iff refine_pw_simps)
      apply (auto simp: slice_rel_alt  slicep_rel_def eq_outside_rane_lenD)
      done

    (* Extracted this subgoal to present it in paper *)      
    lemma introsort_aux3_direct_refine_aux1': "(xs', xs\<^sub>1 @ xs\<^sub>2) \<in> slice_rel xs l h \<Longrightarrow> xs\<^sub>1 = slice l (l + length xs\<^sub>1) xs'"
      apply (clarsimp simp: slice_rel_def in_br_conv)
      by (metis Misc.slice_def add_diff_cancel_left' append.assoc append_eq_conv_conj append_take_drop_id)
      
    lemma introsort_aux3_direct_refine_aux1: "\<lbrakk>(xsi', xs\<^sub>1 @ xs\<^sub>2) \<in> slice_rel xsi l' h'\<rbrakk> \<Longrightarrow> (xsi', xs\<^sub>1) \<in> slicep_rel l' (l' + length xs\<^sub>1)"  
      apply (simp add: slicep_rel_def introsort_aux3_direct_refine_aux1')
      apply (auto simp: slice_rel_alt slicep_rel_def)
      by (metis Misc.slice_len ab_semigroup_add_class.add_ac(1) le_add1 length_append ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
    
    lemma introsort_aux3_direct_refine: "(xsi,xs)\<in>slicep_rel l h \<Longrightarrow> introsort_aux3 xsi l h d \<le> \<Down>(slice_rel xsi l h) (introsort_aux1 xs d)"  
      unfolding introsort_aux3_def introsort_aux1_def
      
      supply [refine del] = RECT_refine
      
      supply recref = RECT_dep_refine[where 
          R="\<lambda>_. {((xsi::'a list, l, h, di::nat), (xs, d)). (xsi, xs) \<in> slicep_rel l h \<and> di=d}" and
          S="\<lambda>_ (xsi::'a list, l, h, di::nat). slice_rel xsi l h" and
          arb\<^sub>0 = "()"
          ]

      apply (refine_rcg 
        recref
        slice_sort_spec_refine_sort'
        partition3_spec_direct_refine
        ; (rule refl)?
        )

      subgoal by auto
      subgoal by auto
      subgoal by (auto simp: slicep_rel_def)
      subgoal by (auto simp: slicep_rel_def)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      apply (rprems)
      subgoal by (clarsimp simp: introsort_aux3_direct_refine_aux1)
      apply rprems  
      subgoal
        apply (auto simp: slice_rel_alt slicep_rel_def)
        subgoal by (metis Misc.slice_def drop_append_miracle drop_slice eq_outside_range_def)
        subgoal by (metis Nat.add_diff_assoc Sorting_Misc.slice_len add_diff_cancel_left' add_le_cancel_left diff_add_zero diff_is_0_eq length_append)
        subgoal by (simp add: eq_outside_rane_lenD)
        done
      subgoal
        apply (clarsimp simp: slice_rel_alt idx_shift_rel_def)
        apply (rule conjI)
        subgoal
          apply (rule slicep_rel_append)
          apply (subst slicep_rel_eq_outside_range; assumption?) 
          by auto 
        subgoal 
          apply (drule (1) eq_outside_range_gen_trans[OF _ _ refl refl])
          apply (erule (1) eq_outside_range_gen_trans)
          apply (auto simp: max_def algebra_simps slicep_rel_def split: if_splits)
          done 
        done
      subgoal by (auto simp: slice_rel_alt eq_outside_range_triv slicep_rel_def)
      done
      
      *)
      
      
      
      
      
    
    definition "final_sort_spec xs l h \<equiv> doN {
      ASSERT (h-l>1 \<and> part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold (slice l h xs));
      slice_sort_spec (\<^bold><) xs l h
      }"
    
    definition "introsort3 xs l h \<equiv> doN {
      ASSERT(l\<le>h);
      hml \<leftarrow> SPECc2 ''sub'' (-) h l;
      if\<^sub>N SPECc2 ''lt'' (<) 1 hml then doN {
        consume (RETURN ()) (cost ''prepare_cost'' 1);
        xs \<leftarrow> slice_part_sorted_spec xs l h;
        xs \<leftarrow> final_sort_spec xs l h;
        RETURN xs
      } else RETURN xs
    }"  

definition "introsort3_cost = cost ''prepare_cost'' 1 + cost ''sub'' 1 + cost ''lt'' 1 + cost ''if'' 1
                               + cost ''slice_sort'' 1 +  cost ''slice_part_sorted'' (1::enat)"
    
    
lemma if_rule2: "(c \<Longrightarrow> Some x \<le> a) \<Longrightarrow> c \<Longrightarrow> Some x \<le> (if c then a else None)"
  by auto

lemma introsort3_correct: "introsort3 xs l h \<le> \<Down>Id (timerefine (TId(''slice_sort'':=introsort3_cost)) (slice_sort_spec (\<^bold><) xs l h))"
  apply (cases "l\<le>h \<and> h\<le>length xs")
  subgoal
    apply (cases "1<h-l")
    subgoal
      unfolding introsort3_def slice_part_sorted_spec_def final_sort_spec_def slice_sort_spec_alt
      apply(auto intro: refine0 simp: SPEC_timerefine_conv)
      unfolding SPEC_REST_emb'_conv SPECc2_def
      apply(rule gwp_specifies_I) 
      apply(refine_vcg \<open>-\<close> rules: )
      subgoal unfolding emb'_def apply(rule if_rule2)
         apply (auto simp: introsort3_cost_def timerefineA_update_apply_same_cost' add.commute)
        subgoal apply sc_solve  apply safe by auto  
        by (auto elim: eq_outside_range_gen_trans[of _ _ l h _ l h l h, simplified])
      subgoal using eq_outside_range_list_rel_on_conv by blast  
      subgoal by blast
      subgoal by(auto simp: emb'_def)
      done
    subgoal
      unfolding introsort3_def slice_sort_spec_alt slice_part_sorted_spec_def final_sort_spec_def
      apply(auto intro: refine0 simp: SPEC_timerefine_conv)
      unfolding SPEC_REST_emb'_conv SPECc2_def
      apply(rule gwp_specifies_I) 
      apply(refine_vcg \<open>-\<close> rules: )
      apply (auto simp add: emb'_def eq_outside_range_triv sorted_wrt01 le_fun_def ecost_nneg) 
      apply (auto simp: introsort3_cost_def timerefineA_update_apply_same_cost' add.commute)
      apply sc_solve apply auto    
      done
    done
  subgoal            
    unfolding slice_sort_spec_alt
    by(auto intro: refine0)
  done 


  end  




end
