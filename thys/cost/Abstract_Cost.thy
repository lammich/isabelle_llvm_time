theory Abstract_Cost
imports Main
begin



  datatype ('a, 'b) acost = acostC (the_acost: "'a \<Rightarrow> 'b") 
  type_synonym cost = "(string, nat) acost"

  \<comment> \<open>TODO: warning! will clash with another definition of plus lifted to function,
          from "../../lib/Sep_Algebra_Add"
        maybe hide @{type cost} behind a new type and define + for it? \<close>


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

    instance 
      apply standard
     apply(auto simp add: le_fun_def less_eq_acost_def less_acost_def split: acost.split)
      subgoal for x y apply(cases x; cases y) apply (auto simp: le_less less_fun_def le_fun_def)  
        using less_not_sym by fastforce
      sorry (* TODO *)
  end


end