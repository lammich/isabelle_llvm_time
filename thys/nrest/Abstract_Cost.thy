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

  definition cost :: "'a \<Rightarrow> 'b::{cancel_comm_monoid_add} \<Rightarrow> ('a,'b) acost" where
    "cost n x = acostC ((the_acost 0)(n:=x))"

  lemma cost_same_curr_add: "cost n x + cost n y = cost n (x+y)" by (auto simp: cost_def fun_eq_iff zero_acost_def)
  lemma cost_same_curr_minus: "cost n x - cost n y = cost n (x-y)" by (auto simp: cost_def fun_eq_iff zero_acost_def)
  lemma cost_zero: "cost n 0 = 0" by(auto simp: cost_def zero_acost_def)

  lemmas c_simps = cost_same_curr_add cost_same_curr_minus cost_zero add_ac[where a="_::(_,_) acost"]
      \<comment> \<open>strange: thm  add_ac[where ?'a="(_,_) acost"] \<close>

end