theory Abstract_Cost
imports Main
begin



  datatype ('a, 'b) acost = acostC (the_acost: "'a \<Rightarrow> 'b") 
  type_synonym cost = "(string, nat) acost"

  \<comment> \<open>TODO: warning! will clash with another definition of plus lifted to function,
          from "../../lib/Sep_Algebra_Add"
        maybe hide @{type cost} behind a new type and define + for it? \<close>


  lemma acost_eq_I: "(\<And>x. the_acost P x = the_acost Q x) \<Longrightarrow> P=Q"
    by (cases P; cases Q; auto)

  instantiation acost :: (type, zero) zero
  begin
    definition "zero_acost = acostC (\<lambda>_. 0)"
    instance ..
  end

  instantiation acost :: (type, plus) plus
  begin
    fun plus_acost where "plus_acost (acostC a) (acostC b) = acostC (\<lambda>x. a x + b x)"
    instance ..
  end

  instantiation acost :: (type, minus) minus
  begin
    fun minus_acost where "minus_acost (acostC a) (acostC b) = acostC (\<lambda>x. a x - b x)"
    instance ..
  end

  instantiation acost :: (type, ord) ord
  begin 
    definition "less_eq_acost a b = (\<forall>x. the_acost a x \<le> the_acost b x)"
    definition "less_acost a b \<equiv> (\<forall>x. the_acost a x \<le> the_acost b x) \<and> (\<exists>x. the_acost a x < the_acost b x)"

    instance ..
  end

  instantiation acost :: (type, monoid_add) monoid_add
  begin
  
    instance (* TODO refactor *)
      apply standard
      subgoal for a b c apply(cases a; cases b; cases c) by (auto simp: add.assoc)
          apply (auto simp: zero_acost_def add.assoc diff_diff_add)  
      subgoal for a     apply(cases a) by auto
      subgoal for a     apply(cases a) by auto
      done
  end
  
  lemma plus_acost_alt: "a+b = (case (a,b) of (acostC a,acostC b) \<Rightarrow> acostC (\<lambda>x. a x+b x))"
    by (cases a; cases b; auto)
  
  lemma minus_acost_alt: "a-b = (case (a,b) of (acostC a,acostC b) \<Rightarrow> acostC (\<lambda>x. a x-b x))"
    by (cases a; cases b; auto)
  
(*
  instantiation acost :: (type, ab_semigroup_add) ab_semigroup_add
  begin
  
    instance (* TODO refactor *)
      apply standard 
      subgoal for a b c apply(cases a; cases b; cases c) by (auto simp: add.assoc)
      subgoal for a b   apply(cases a; cases b) by (auto simp: add.commute) 
      done
  end
*)
  
  instantiation acost :: (type, comm_monoid_add) comm_monoid_add
  begin
  
    instance (* TODO refactor *)
      apply standard
          apply (auto simp: zero_acost_def add.assoc diff_diff_add)  
      subgoal for a b   apply(cases a; cases b) by (auto simp: add.commute) 
      subgoal for a     apply(cases a) by auto
      done
  end

 

  instantiation acost :: (type, cancel_comm_monoid_add) cancel_comm_monoid_add
  begin
  
    instance (* TODO refactor *)
      apply standard
      subgoal for a b   apply(cases a; cases b) by (auto simp: add.commute) 
      subgoal for a b c apply(cases a; cases b; cases c) by (auto simp: diff_diff_add) 
      done
  end


  term "(a::cost) + b"
  term "(0::cost)"

  definition cost :: "'a \<Rightarrow> 'b::{comm_monoid_add} \<Rightarrow> ('a,'b) acost" where
    "cost n x = acostC ((the_acost 0)(n:=x))"

  lemma cost_same_curr_add: "cost n x + cost n y = cost n (x+y)" by (auto simp: cost_def fun_eq_iff zero_acost_def)
  lemma cost_same_curr_minus:
    "cost n (x::_::{cancel_comm_monoid_add}) - cost n y = cost n (x-y)" by (auto simp: cost_def fun_eq_iff zero_acost_def)
  lemma cost_zero: "cost n 0 = 0" by(auto simp: cost_def zero_acost_def)

  lemmas c_simps = cost_same_curr_add cost_same_curr_minus cost_zero add_ac[where a="_::(_,_) acost"]
      \<comment> \<open>strange: thm  add_ac[where ?'a="(_,_) acost"] \<close>


  
  
  instantiation acost :: (type, Sup) Sup
  begin                                                   
    definition "Sup A = acostC (\<lambda>x. SUP f\<in>A. the_acost f x)"
  
    instance ..
  
  end
  
  instantiation acost :: (type, Inf) Inf
  begin                                                   
  
    definition "Inf A = acostC (\<lambda>x. INF f\<in>A. the_acost f x)"
  
    instance ..
  
end

  instantiation acost :: (type, complete_lattice) complete_lattice
  begin                                                   
    definition "bot_acost = acostC (\<lambda>x. bot)"             
    definition "top_acost = acostC (\<lambda>x. top)"
    definition "sup_acost c c' = acostC (\<lambda>x. sup (the_acost c x) (the_acost c' x))"
    definition "inf_acost c c' = acostC (\<lambda>x. inf (the_acost c x) (the_acost c' x))"

    instance 
      apply standard
     apply(auto simp add: le_fun_def less_eq_acost_def less_acost_def split: acost.split)
      subgoal for x y apply(cases x; cases y) apply (auto simp: le_less less_fun_def le_fun_def)  
        using less_not_sym by fastforce
      subgoal for x y apply(cases x; cases y) apply (auto simp: le_less less_fun_def le_fun_def)  
        by metis
      subgoal for x y z apply(cases x; cases y; cases z) apply (auto simp: less_fun_def le_fun_def)
        using order_trans by blast
      subgoal for x y  apply(cases x; cases y) apply (auto simp: less_fun_def le_fun_def)
        using antisym_conv by fastforce  
      subgoal for x y  apply(cases x; cases y) by (auto simp: inf.strict_order_iff inf_acost_def inf_commute) 
      subgoal for x y  apply(cases x; cases y) by (auto simp: inf.strict_order_iff inf_acost_def)  
      subgoal for x y z apply(cases x; cases y; cases z) by (auto simp: inf_acost_def)
      subgoal for x y  apply(cases x; cases y) by (simp add: sup.strict_order_iff sup_acost_def sup_commute)  
      subgoal for x y  apply(cases x; cases y) by (simp add: sup.strict_order_iff sup_acost_def)  
      subgoal for x y z  apply(cases x; cases y; cases z) apply (auto simp: le_less less_fun_def le_fun_def)  
        by (smt acost.sel dual_order.strict_implies_order le_sup_iff order.not_eq_order_implies_strict order_refl sup_acost_def)
      subgoal for x  apply(cases x) apply (auto simp: Inf_acost_def)  
        by (metis acost.sel le_INF_iff order_refl)  
      subgoal for A z x apply(cases z) by (auto simp add: Inf_acost_def le_INF_iff)
      subgoal for x A y apply(cases x) apply (simp add: Sup_acost_def) by (metis Sup_upper acost.sel image_iff)
      subgoal for A z x apply(cases z) apply (simp add: Sup_acost_def) by (simp add: SUP_least)
      subgoal unfolding Inf_acost_def top_acost_def by simp 
      subgoal unfolding Sup_acost_def bot_acost_def by simp 
      done
end




lemma the_acost_mono: "T \<le> T' \<Longrightarrow> the_acost T b \<le> the_acost T' b"
  apply(cases T; cases T') by (auto simp: le_fun_def less_eq_acost_def)

lemma the_acost_propagate:  
  shows "the_acost (a + b) = (\<lambda>x. the_acost a x + the_acost b x)"
  apply(cases a; cases b) by auto



end