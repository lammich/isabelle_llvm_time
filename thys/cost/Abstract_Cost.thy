theory Abstract_Cost
imports Main "HOL-Library.Extended_Nat"
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


lemma the_acost_costs_distrib_left:
  "the_acost (cost n x + (r:: ('c, nat) acost)) m * p
     = the_acost (cost n x) m * p + the_acost r m * p"
  apply(cases r) by(auto simp: cost_def zero_acost_def ring_distribs )
lemma the_acost_costs_distrib_right:
  "the_acost ((r:: ('c, nat) acost) + cost n x ) m * p
     = the_acost (cost n x) m * p + the_acost r m * p"
  apply(cases r) by(auto simp: cost_def zero_acost_def ring_distribs )
lemmas the_acost_costs_distrib = the_acost_costs_distrib_left the_acost_costs_distrib_right
lemma the_acost_cost_mult: "the_acost (cost n c) x * (p::nat) = the_acost (cost n (c*p)) x"
  by(auto simp: cost_def zero_acost_def)
lemma acostC_the_acost_cost: "acostC (\<lambda>x. the_acost (cost n t) x + r x) = cost n t + acostC r"
  by (auto simp: cost_def)
lemma "acostC (\<lambda>x. the_acost (cost n t) x + r x) = cost n t + acostC r"
  by (auto simp: cost_def)

  
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




lemma top_acost_absorbs: "top + (x::(_,enat)acost) = top"
  apply(cases x) by (auto simp: top_acost_def plus_acost_alt top_enat_def)


lemma the_acost_mono: "T \<le> T' \<Longrightarrow> the_acost T b \<le> the_acost T' b"
  apply(cases T; cases T') by (auto simp: le_fun_def less_eq_acost_def)

lemma the_acost_propagate:  
  shows "the_acost (a + b) = (\<lambda>x. the_acost a x + the_acost b x)"
  apply(cases a; cases b) by auto


subsection \<open>skalar multiplication with acost\<close>
definition costmult :: "_ \<Rightarrow> ('b, _ ) acost \<Rightarrow> ('b, _ ) acost" (infixl "*m" 80)
  where  "costmult s c \<equiv> acostC (\<lambda>x. s * the_acost c x)"

lemma costmult_1_absorb[simp]: "(1::('b::comm_semiring_1)) *m c = c"
  "(Suc 0) *m d = d"
  by(simp_all add: costmult_def) 

lemma costmult_right_mono:
  fixes a :: enat
  shows "a \<le> a' \<Longrightarrow> a *m c \<le> a' *m c"
  unfolding costmult_def less_eq_acost_def
  by (auto simp add: mult_right_mono)  


lemma costmult_zero_is_zero_enat[simp]: "(x::enat) *m 0 = 0"
  unfolding costmult_def zero_acost_def by auto

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




end