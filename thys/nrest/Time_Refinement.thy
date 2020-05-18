theory Time_Refinement
imports NREST NREST_Type_Classes
begin




section "time refine" 

(* mult_zero for wfR_finite_mult_left *)
definition timerefine ::"('b \<Rightarrow> ('c,'d::{complete_lattice,comm_monoid_add,times,mult_zero}) acost)
                             \<Rightarrow> ('a, ('b,'d) acost) nrest \<Rightarrow> ('a, ('c,'d) acost) nrest"
  where "timerefine R m = (case m of FAILi \<Rightarrow> FAILi |
                REST M \<Rightarrow> REST (\<lambda>r. case M r of None \<Rightarrow> None |
                  Some cm \<Rightarrow> Some (acostC (\<lambda>cc. Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) cc)))))"


definition timerefineF ::"('b \<Rightarrow> ('c,'d::{complete_lattice,comm_monoid_add,times,mult_zero}) acost)
                             \<Rightarrow> ('a \<Rightarrow> ('b,'d) acost option) \<Rightarrow> ('a \<Rightarrow> ('c,'d) acost option)"
  where "timerefineF R M = (\<lambda>r. case M r of None \<Rightarrow> None |
                  Some cm \<Rightarrow> Some (acostC (\<lambda>cc. Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) cc))))"

lemma timerefine_alt: "timerefine R m = case_nrest FAILi (\<lambda>M. SPECT (timerefineF R M)) m"
  unfolding timerefine_def timerefineF_def ..

lemma timerefine_SPECT: "timerefine R (SPECT Q) = SPECT (timerefineF R Q)" 
  unfolding timerefine_alt by simp


definition wfn :: "('a, ('c,'d::{complete_lattice,comm_monoid_add,times,mult_zero}) acost) nrest \<Rightarrow> bool" where
  "wfn m = (case m of FAILi \<Rightarrow> True |
                REST M \<Rightarrow> \<forall>r\<in>dom M. (case M r of None \<Rightarrow> True | Some cm \<Rightarrow> finite {x. the_acost cm x \<noteq> 0}))"

definition wfR :: "('b \<Rightarrow> ('c, _::mult_zero) acost) \<Rightarrow> bool" where
  "wfR R = (finite {(s,f). the_acost (R s) f \<noteq> 0})"


lemma wfR_fst: "\<And>y. wfR R \<Longrightarrow> finite {x. the_acost (R x) y \<noteq> 0}"
  unfolding wfR_def apply(rule finite_subset[where B="fst ` {(s, f). the_acost (R s) f \<noteq> 0}"])
  subgoal by auto
  apply(rule finite_imageI) by simp

lemma wfR_snd: "\<And>s. wfR R \<Longrightarrow> finite {y. the_acost (R s) y \<noteq> 0}"
  unfolding wfR_def apply(rule finite_subset[where B="snd ` {(s, f). the_acost (R s) f \<noteq> 0}"])
  subgoal by auto
  apply(rule finite_imageI) by simp

(*
lemma finite_same_support:
  "\<And>f. finite {(x,y). R x y \<noteq> 0} \<Longrightarrow> (\<And>x.  f (R x) = 0 \<longleftrightarrow> R x = 0) \<Longrightarrow> finite {x. f (R x) \<noteq> 0}"
  oops*)

lemma 
  finite_wfR_middle_mult:
  fixes R1 :: "_ \<Rightarrow> ('a, 'b::{semiring_no_zero_divisors}) acost"
  assumes "wfR R1" "wfR R2"
  shows "finite {a. the_acost (R2 x) a * the_acost (R1 a) y \<noteq> 0}"
proof -
  have "{a. the_acost (R2 x) a * the_acost (R1 a) y \<noteq> 0} = {a. the_acost (R2 x) a \<noteq> 0 \<and> the_acost (R1 a) y \<noteq> 0}" by simp
  also have "\<dots> \<subseteq> fst ` {(a,a)| a. the_acost (R2 x) a \<noteq> 0 \<and> the_acost (R1 a) y \<noteq> 0}" by auto
  also have "\<dots> \<subseteq> fst ` ({a. the_acost (R2 x) a \<noteq> 0} \<times> {a. the_acost (R1 a) y \<noteq> 0})"
    apply(rule image_mono) by auto
  finally
  show ?thesis apply(rule finite_subset)
    apply(rule finite_imageI)
    apply(rule finite_cartesian_product)
    apply(rule wfR_snd[where R=R2]) apply fact
    apply(rule wfR_fst) by fact
qed

lemma wfR_finite_mult_left:
  fixes R2 :: "('b \<Rightarrow> ('c, 'd::mult_zero) acost)"
  assumes "wfR R2"
  shows "finite {a. the_acost Mc a * the_acost (R2 a) ac \<noteq> 0}"
proof -

  have "{a. the_acost Mc a * the_acost (R2 a) ac \<noteq> 0} \<subseteq> {a. the_acost (R2 a) ac \<noteq> 0}"
    apply(cases Mc) by (auto simp: zero_acost_def)
  then
  show ?thesis
    apply(rule finite_subset)
    apply(rule wfR_fst) by fact
qed




lemma 
  wfR_finite_crossprod:
  assumes "wfR R2"
  shows "finite ({a. \<exists>b. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0} \<times> {b. \<exists>a. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0})"
proof -
  have i: "{a. \<exists>b. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0} \<subseteq> fst ` ({(a,b).  the_acost (R2 a) b \<noteq> 0} \<inter> {(a,b). the_acost (R1 b) cc \<noteq> 0})"
    apply safe 
    by (metis (mono_tags, lifting) Int_iff arith_simps(62) arith_simps(63) case_prodI image_eqI mem_Collect_eq prod.sel(1))  
  have ii: "{b. \<exists>a. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0} \<subseteq> snd ` ({(a,b).  the_acost (R2 a) b \<noteq> 0} \<inter> {(a,b). the_acost (R1 b) cc \<noteq> 0})"
    apply safe  
    by (metis (mono_tags, lifting) Int_iff arith_simps(62) arith_simps(63) case_prodI image_eqI mem_Collect_eq prod.sel(2))  
  

  show ?thesis 
    apply(rule finite_cartesian_product)
    subgoal  apply(rule finite_subset[OF i]) apply(rule finite_imageI)
      apply(rule finite_Int)   using assms wfR_def by auto
    subgoal  apply(rule finite_subset[OF ii]) apply(rule finite_imageI)
      apply(rule finite_Int)   using assms wfR_def by auto
    done    
qed

lemma wfR_finite_Sum_any: 
  assumes *: "wfR R"
  shows "finite {x. ((Sum_any (\<lambda>ac. (the_acost Mc ac * (the_acost (R ac) x)))) \<noteq> 0)}"
proof - 
  {fix x
    have "((Sum_any (\<lambda>ac. ((the_acost Mc ac) * (the_acost (R ac) x)))) \<noteq> 0)
      \<Longrightarrow> \<exists>ac. (the_acost Mc ac) * (the_acost (R ac) x) \<noteq> 0"
      using Sum_any.not_neutral_obtains_not_neutral by blast 
  } then 
  have "{x. ((Sum_any (\<lambda>ac. ((the_acost Mc ac) * (the_acost (R ac) x)))) \<noteq> 0)}
          \<subseteq> {x. \<exists>ac. ((the_acost Mc ac) * (the_acost (R ac) x)) \<noteq> 0}" by blast
  also have "\<dots> \<subseteq> snd ` {(ac,x). ((the_acost Mc ac) * (the_acost (R ac) x)) \<noteq> 0}" by auto 
  also have "\<dots> \<subseteq> snd ` {(ac,x).  (the_acost (R ac) x) \<noteq> 0}" by auto

  finally  show ?thesis 
    apply(rule finite_subset )
    apply(rule finite_imageI) using * unfolding wfR_def by auto
qed 


(*
lemma assumes "R' \<le> R" "wfR R" shows "wfR R'"
proof -                                    
  from assms(1) have *: "\<And> a b. the_acost (R' a) b\<le> the_acost (R a) b"
  unfolding less_eq_acost_def le_fun_def   by auto
  {fix  a b have "the_acost (R a) b  = 0 \<Longrightarrow> the_acost (R' a) b = 0 "   
      using * [of a b] by (auto simp: zero_acost_def less_eq_acost_def)}
  note f=this
  show "wfR R'"
    using \<open>wfR R\<close> unfolding wfR_def apply(rule rev_finite_subset)
    apply safe using f by simp
qed
*)

lemma wfn_timerefine: "wfn m \<Longrightarrow> wfR R \<Longrightarrow> wfn (timerefine R m)"
proof -
  assume "wfR R"
  then show "wfn (timerefine R m)"
    unfolding wfn_def timerefine_def 
    apply(auto split: nrest.splits option.splits)
    apply(rule wfR_finite_Sum_any) by simp
qed


lemma [simp]: "timerefine R FAILT = FAILT" by(auto simp: timerefine_def)

definition pp where
  "pp R2 R1 = (\<lambda>a. acostC (\<lambda>c. Sum_any (%b. the_acost (R1 a) b * the_acost (R2 b) c  ) ))"

lemma Sum_any_mono:
  fixes f :: "('a \<Rightarrow> 'b::{nonneg,comm_monoid_add,order,ordered_comm_monoid_add})"
  assumes fg: "\<And>x. f x \<le> g x" (* can one relax that and say the norm is mono, for integer domains ? *)
    and finG: "finite {x. g x \<noteq> 0}"
shows "Sum_any f \<le> Sum_any g"
proof -
  have "{x. f x \<noteq> 0} \<subseteq> {x. g x \<noteq> 0}"
    apply auto
    subgoal for x using fg[of x] needname_nonneg[of " f x"] by auto 
    done
  with finG have "finite {x. f x \<noteq> 0}"  
    using finite_subset by blast   

  thm sum_mono sum_mono2
  thm sum_mono2
  have "sum f {x. f x \<noteq> 0} \<le> sum f {x. g x \<noteq> 0}"
    apply(rule sum_mono2) apply fact apply fact
    by simp
  also have "\<dots> \<le> sum g {x. g x \<noteq> 0}"
    apply(rule sum_mono) using fg by simp
  finally show ?thesis unfolding Sum_any.expand_set .
qed

lemma finite_support_mult:  
  fixes R1 :: "('a, 'b::{semiring_no_zero_divisors}) acost"
  assumes "finite {xa.  the_acost R1 xa \<noteq> 0}"
  and "finite {xa. the_acost R2 xa \<noteq> 0}"
shows "finite {xa. the_acost R2 xa * the_acost R1 xa \<noteq> 0}"
proof -
 
  have "{(xa,xa)|xa. the_acost R2 xa * the_acost R1 xa \<noteq> 0} = {(xa,xa)|xa. the_acost R2 xa \<noteq> 0 \<and> the_acost R1 xa \<noteq> 0}" by auto
  also have "\<dots> \<subseteq> {(xa,xb)|xa xb. the_acost R2 xa \<noteq> 0 \<and> the_acost R1 xb \<noteq> 0}" by auto
  also have "\<dots> = {xa. the_acost R2 xa \<noteq> 0} \<times> {xb. the_acost R1 xb \<noteq> 0}" by auto 
  finally have k: "{xa. the_acost R2 xa * the_acost R1 xa \<noteq> 0} \<subseteq> fst ` ({xa. the_acost R2 xa \<noteq> 0} \<times> {xb. the_acost R1 xb \<noteq> 0})" by blast

  show ?thesis
    apply(rule finite_subset[OF k])
    apply(rule finite_imageI) 
    apply(rule finite_cartesian_product) by fact+
qed


lemma timerefine_mono: 
  fixes R :: "_ \<Rightarrow> ('a, 'b::{complete_lattice,nonneg,mult_zero,ordered_semiring}) acost"
  assumes "wfR R"
  shows "c\<le>c' \<Longrightarrow> timerefine R c \<le> timerefine R c'"
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
      subgoal using l apply(rule ordered_semiring_class.mult_right_mono) by (simp add: needname_nonneg)
      apply(rule wfR_finite_mult_left) by fact
  qed 


lemma
  fixes R1 :: "_ \<Rightarrow> ('a, 'b::{complete_lattice,nonneg,ordered_semiring,semiring_no_zero_divisors}) acost"
  assumes "wfR R1" "wfR R2"
  shows timerefine_iter: "timerefine R1 (timerefine R2 c) =  timerefine (pp R1 R2) c"
  unfolding timerefine_def 
  apply(cases c)
  subgoal by simp 
  apply (auto simp: le_fun_def pp_def split: option.splits) apply (rule ext)
  apply (auto simp: le_fun_def pp_def split: option.splits)
  apply(subst Sum_any_right_distrib)
  subgoal apply(rule finite_wfR_middle_mult[of R1 R2]) using assms by simp_all
  apply (rule ext)
  subgoal for mc r Mc cc
    apply (subst Sum_any.swap[where C="{a. \<exists>b. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0} \<times> {b. \<exists>a. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0}"])
    subgoal apply(rule wfR_finite_crossprod) using assms by simp
    subgoal by simp 
    apply(subst Sum_any_left_distrib)
    subgoal apply(rule wfR_finite_mult_left) using assms by simp 
    apply(rule Sum_any.cong)
    by (meson mult.assoc)
  done 

lemma timerefine_trans: 
  fixes R1 :: "_ \<Rightarrow> ('a, 'b::{complete_lattice,nonneg,ordered_semiring,semiring_no_zero_divisors}) acost"
  assumes "wfR R1" "wfR R2" shows 
  "a \<le> timerefine R1 b \<Longrightarrow> b \<le> timerefine R2 c \<Longrightarrow> a \<le> timerefine (pp R1 R2) c"
  apply(subst timerefine_iter[symmetric, OF assms])
    apply(rule order.trans) apply simp
    apply(rule timerefine_mono) using assms by auto

   
section \<open>enum setup\<close>

 

lemma (in enum) sum_to_foldr: "sum f UNIV  
      = foldr (\<lambda>x a. a + f x) enum 0"
  (*= sum_list (map f enum_class.enum)"  *)
  unfolding UNIV_enum using enum_distinct
  apply(simp add: sum.distinct_set_conv_list  )
  apply(simp only: sum_list.eq_foldr foldr_map)  
  by (metis add.commute comp_apply)  

lemma (in enum) Sum_any_to_foldr: "Sum_any f  
      = foldr (\<lambda>x a. a + f x) enum 0"
  apply(subst Sum_any.expand_superset[where A=UNIV])
  by (simp_all add: sum_to_foldr)


end