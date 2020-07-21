theory NREST_Automation
imports NREST_Main "../cost/Enat_Cost"
begin


section \<open>Solver for Time Side conditions\<close>

lemma lift_acost_propagate: "lift_acost (t+t') = lift_acost t + lift_acost t' "
  unfolding lift_acost_def by (cases t; cases t'; auto)

lemma ecost_add_commute: "a + b = b + (a::(string,enat) acost)"
  by (simp add: add.commute)

lemma ecost_add_left_commute: "b + (a + c) = a + ((b::(string,enat) acost) + c)"
  by (simp add: add.left_commute)

lemma cost_same_curr_add: "cost n x + cost n y = cost n (x+y)"
  by (simp add: cost_same_curr_add)

lemma cost_same_curr_left_add: "cost n x + (cost n y + c) = cost n (x+y) + c"
  by (simp add: add.assoc[symmetric] cost_same_curr_add)

definition "leq_sidecon (a::(string,enat) acost) as1 as2 b bs1 bs2 T \<equiv> a + as1 + as2 \<le> b + bs1 + bs2 \<and> T"

lemma leq_sc_init: 
    "leq_sidecon a 0 (as + 0) 0 0 (bs + 0) True \<Longrightarrow> a + as \<le> bs"
    "leq_sidecon a 0 0 0 0 bs True \<Longrightarrow> a \<le> bs"
  unfolding leq_sidecon_def by simp_all

lemma leq_sc_l_SUCC:
  "leq_sidecon (cost n (x+y)) ar as 0 0 bs P \<Longrightarrow> leq_sidecon (cost n x) ar (cost n y + as) 0 0 bs P"
  unfolding leq_sidecon_def apply (subst add.commute) apply (subst add.assoc) apply (subst cost_same_curr_left_add)
  apply (subst add.assoc[symmetric]) apply (subst add.commute) by simp

lemma leq_sc_l_FAIL:
 (* "leq_sidecon (cost n x) c as 0 0 bs2 P \<Longrightarrow> leq_sidecon (cost n x) 0 (c + as) 0 0 bs2 P" *)
  "leq_sidecon (cost n x) (c + ar) as 0 0 bs2 P \<Longrightarrow> leq_sidecon (cost n x) ar (c + as) 0 0 bs2 P"
  unfolding leq_sidecon_def by(simp_all add: add.commute add.left_commute)

lemma leq_sc_l_DONE:
  "leq_sidecon (cost n x) l 0 (cost n 0) 0 bs2 P \<Longrightarrow> leq_sidecon (cost n x) l 0 0 0 bs2 P"
  unfolding leq_sidecon_def by (simp add: cost_zero)

lemma leq_sc_r_SUCC:
  "leq_sidecon (cost n x) l 0 (cost n (y+z)) bs1 bs2 P \<Longrightarrow> leq_sidecon (cost n x) l 0 (cost n y) bs1 (cost n z + bs2) P"
  unfolding leq_sidecon_def apply (subst (3) add.commute) apply (subst (2) add.assoc) apply (subst cost_same_curr_left_add)
  apply (subst add.assoc[symmetric]) apply (subst (3) add.commute) by simp

lemma leq_sc_r_FAIL:
(*  "leq_sidecon (cost n x) l 0 (cost n y) c bs2 P \<Longrightarrow> leq_sidecon (cost n x) l 0 (cost n y) 0 (c + bs2) P" *)
  "leq_sidecon (cost n x) l 0 (cost n y) (c + bs1) bs2 P \<Longrightarrow> leq_sidecon (cost n x) l 0 (cost n y) bs1 (c + bs2) P"
  unfolding leq_sidecon_def by(simp_all add: add.commute add.left_commute)

lemma cost_mono: "(x::enat)\<le>y \<Longrightarrow> cost n x \<le> cost n y"
  by(auto simp: cost_def less_eq_acost_def)
lemma ecost_nneg: "0 \<le> (r::(string,enat) acost)"
  by (rule needname_nonneg)
  
lemma leq_sc_r_DONE_ALL:
  "(P \<and> x\<le>y) \<Longrightarrow> leq_sidecon (cost n x) 0 0 (cost n y) r 0 P"
  unfolding leq_sidecon_def by (auto intro: add_increasing2 cost_mono ecost_nneg )

lemma leq_sc_r_DONE1:
  "leq_sidecon l 0 ls 0 0 r (P \<and> x\<le>y) \<Longrightarrow> leq_sidecon (cost n x) (l + ls) 0 (cost n y) r 0 P"
  unfolding leq_sidecon_def by (auto intro: add_mono cost_mono ecost_nneg)


lemma "cost ''a'' 1 + cost ''b'' (1::enat) + cost ''b'' 1 + cost ''b'' 1 + cost ''a'' 2 \<le> cost ''a'' 3 + cost ''b'' 3"
  apply(simp only: add.assoc)
  apply(rule leq_sc_init)
  apply(simp only: add.assoc)
  apply(rule leq_sc_l_SUCC leq_sc_l_FAIL)+
  apply(rule  leq_sc_l_DONE)
  apply(rule leq_sc_r_SUCC leq_sc_r_FAIL )+
  apply(rule leq_sc_r_DONE_ALL leq_sc_r_DONE1) 
  oops

method sc_solve' =  ( simp only: add.assoc, rule leq_sc_init, simp only: add.assoc,
         ( (rule leq_sc_l_SUCC leq_sc_l_FAIL leq_sc_l_DONE)+,
           (rule leq_sc_r_SUCC leq_sc_r_FAIL leq_sc_r_DONE_ALL leq_sc_r_DONE1)+ )+ )
method sc_solve =  ( (simp add: lift_acost_propagate lift_acost_cost)?, sc_solve' )

lemma
  lift_acost_diff_to_the_front:
   "a + (lift_acost (b - c) + d) = (lift_acost (b - c) + (a + d))"
    "(a + lift_acost (b - c)) = (lift_acost (b - c) + a)"
  by(simp_all add: add_ac)


lemma lift_acost_diff_to_the_right:
  assumes "b\<le>a"
  shows "(lift_acost (a-b) + c) \<le> d \<longleftrightarrow> (lift_acost a + c) \<le>  d + (lift_acost b)"
  using assms
  apply(auto simp: lift_acost_def less_eq_acost_def minus_acost_alt plus_acost_alt split: acost.splits)
  subgoal by (smt add.assoc add.commute add_left_mono le_add_diff_inverse plus_enat_simps(1)) 
  subgoal by (smt add.assoc add.commute add_diff_cancel_enat enat.simps(3) le_add_diff_inverse2 needname_adjoint of_nat_add of_nat_eq_enat)
 done

lemma lift_acost_diff_to_the_right_Some:
  assumes "b\<le>a"
  shows "Some (lift_acost (a-b) + c) \<le> d \<longleftrightarrow> Some (lift_acost a + c) \<le> Someplus d (Some (lift_acost b))"
  using assms
  by (cases d; auto simp: lift_acost_diff_to_the_right) 

lemma "b \<le> a \<Longrightarrow> Some
         (cost ''list_set'' 1 +
          (lift_acost (a - b) +
           (cost ''list_cmp_v'' 1 + (cost ''if'' 1 + cost ''i_gt'' 1 + cost ''i_sub'' 1) + cost ''if'' 1 +
            (cost ''list_get'' 1 + cost ''call'' 1))))
        \<le> (if I then Some (lift_acost (E_u (length xs)) + cost ''list_get'' 1) else None)"
  apply(simp add: lift_acost_diff_to_the_front lift_acost_diff_to_the_right) oops


lemma "cost ''a'' 1 + cost ''b'' (1::enat) + cost ''b'' 1 + cost ''b'' 1 + cost ''a'' 2 \<le> cost ''a'' 3 + cost ''b'' 3"
  apply sc_solve
  by simp

lemma "cost ''a'' 1 + cost ''b'' (1::enat) + cost ''b'' 1 + cost ''a'' 2  + cost ''aa'' (enat (Suc i)) + cost ''c'' 1
           \<le> cost ''aa'' 1 + cost ''a'' 3 + cost ''b'' 3 + cost ''aa'' (enat i)  + cost ''c'' 3"
  apply sc_solve
  apply simp
  oops


(* TODO: Move *)
lemma MIf_refine: "struct_preserving E \<Longrightarrow> (b,b')\<in>bool_rel \<Longrightarrow> (b \<Longrightarrow> f \<le> \<Down>R (timerefine E f'))
           \<Longrightarrow> (\<not>b \<Longrightarrow> g \<le> \<Down>R (timerefine E g')) \<Longrightarrow>  MIf b f g  \<le> \<Down>R (timerefine E (MIf b' f' g' ))"
  sorry


end