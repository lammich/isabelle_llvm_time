theory Time_Refinement
imports NREST
begin




section "time refine"


definition timerefine ::"('b \<Rightarrow> 'c \<Rightarrow> enat)  \<Rightarrow> ('a, 'b \<Rightarrow> enat) nrest \<Rightarrow> ('a, 'c \<Rightarrow> enat) nrest"  where
  "timerefine R m = (case m of FAILi \<Rightarrow> FAILi |
                REST M \<Rightarrow> REST (\<lambda>r. case M r of None \<Rightarrow> None |
                  Some cm \<Rightarrow> Some (\<lambda>cc. Sum_any (\<lambda>ac. cm ac * R ac cc))))"

definition wfn :: "('a, 'b \<Rightarrow> enat) nrest \<Rightarrow> bool" where
  "wfn m = (case m of FAILi \<Rightarrow> True |
                REST M \<Rightarrow> \<forall>r\<in>dom M. (case M r of None \<Rightarrow> True | Some cm \<Rightarrow> finite {x. cm x \<noteq> 0}))"

definition wfR :: "('b \<Rightarrow> 'c \<Rightarrow> enat) \<Rightarrow> bool" where
  "wfR R = (finite {(s,f). R s f \<noteq> 0})"





lemma wfR_fst: "\<And>y. wfR R \<Longrightarrow> finite {x. R x y \<noteq> 0}"
  unfolding wfR_def apply(rule finite_subset[where B="fst ` {(s, f). R s f \<noteq> 0}"])
  subgoal by auto
  apply(rule finite_imageI) by simp

lemma wfR_snd: "\<And>x. wfR R \<Longrightarrow> finite {y. R x y \<noteq> 0}"
  unfolding wfR_def apply(rule finite_subset[where B="snd ` {(s, f). R s f \<noteq> 0}"])
  subgoal by auto
  apply(rule finite_imageI) by simp

(*
lemma finite_same_support:
  "\<And>f. finite {(x,y). R x y \<noteq> 0} \<Longrightarrow> (\<And>x.  f (R x) = 0 \<longleftrightarrow> R x = 0) \<Longrightarrow> finite {x. f (R x) \<noteq> 0}"
  oops*)

lemma 
  finite_wfR_middle_mult:
  assumes "wfR R1" "wfR R2"
  shows "finite {a. R2 x a * R1 a y \<noteq> (0::enat)}"
proof -
  have "{a. R2 x a * R1 a y \<noteq> 0} = {a. R2 x a \<noteq> 0 \<and> R1 a y \<noteq> 0}" by simp
  also have "\<dots> \<subseteq> fst ` {(a,a)| a. R2 x a \<noteq> 0 \<and> R1 a y \<noteq> 0}" by auto
  also have "\<dots> \<subseteq> fst ` ({a. R2 x a \<noteq> 0} \<times> {a. R1 a y \<noteq> 0})"
    apply(rule image_mono) by auto
  finally
  show ?thesis apply(rule finite_subset)
    apply(rule finite_imageI)
    apply(rule finite_cartesian_product)
    apply(rule wfR_snd) apply fact
    apply(rule wfR_fst) by fact
qed



lemma wfR_finite_mult_left:
  assumes "wfR R2"
  shows "finite {a. Mc a * R2 a ac \<noteq> (0::enat)}"
proof -

  have "{a. Mc a * R2 a ac \<noteq> 0} \<subseteq> {a. R2 a ac \<noteq> 0}"
    by auto
  then
  show ?thesis
    apply(rule finite_subset)
    apply(rule wfR_fst) by fact
qed




lemma 
  wfR_finite_crossprod:
  assumes "wfR R2"
  shows "finite ({a. \<exists>b. Mc a * (R2 a b * R1 b cc) \<noteq> (0::enat)} \<times> {b. \<exists>a. Mc a * (R2 a b * R1 b cc) \<noteq> 0})"
proof -
  have i: "{a. \<exists>b. Mc a * (R2 a b * R1 b cc) \<noteq> 0} \<subseteq> fst ` ({(a,b).  R2 a b \<noteq> 0} \<inter> {(a,b). R1 b cc \<noteq> 0})" by auto
  have ii: "{b. \<exists>a. Mc a * (R2 a b * R1 b cc) \<noteq> 0} \<subseteq> snd ` ({(a,b).  R2 a b \<noteq> 0} \<inter> {(a,b). R1 b cc \<noteq> 0})" by auto
  

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
  shows "finite {x. ((Sum_any (\<lambda>ac. ((Mc ac) * (R ac x)))) \<noteq> (0::enat))}"
proof - 
  {fix x
    have "((Sum_any (\<lambda>ac. ((Mc ac) * (R ac x)))) \<noteq> 0)
      \<Longrightarrow> \<exists>ac. (Mc ac) * (R ac x) \<noteq> 0"
      using Sum_any.not_neutral_obtains_not_neutral by blast 
  } then 
  have "{x. ((Sum_any (\<lambda>ac. ((Mc ac) * (R ac x)))) \<noteq> 0)}
          \<subseteq> {x. \<exists>ac. ((Mc ac) * (R ac x)) \<noteq> 0}" by blast
  also have "\<dots> \<subseteq> snd ` {(ac,x). ((Mc ac) * (R ac x)) \<noteq> 0}" by auto 
  also have "\<dots> \<subseteq> snd ` {(ac,x).  (R ac x) \<noteq> 0}" by auto

  finally  show ?thesis 
    apply(rule finite_subset )
    apply(rule finite_imageI) using * unfolding wfR_def by auto
qed 



lemma assumes "R' \<le> R" "wfR R" shows "wfR R'"
proof -                                    
  from assms(1) have *: "\<And> a b. R' a b\<le> R a b"
  unfolding le_fun_def   by auto
  {fix  a b have "R a b  = 0 ==> R' a b = 0 "   
      using * [of a b] by auto}
  note f=this
  show "wfR R'"
    using \<open>wfR R\<close> unfolding wfR_def apply(rule rev_finite_subset)
    apply safe using f by simp
qed

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
  "pp R2 R1 = (\<lambda>a c. Sum_any (%b. R1 a b * R2 b c  ) )"

lemma Sum_any_mono:
  assumes fg: "\<And>x.    f x \<le> g x"
    and finG: "finite {x. g x \<noteq> (0::enat)}"
shows "Sum_any f \<le> Sum_any g"
proof -
  have "{x. f x \<noteq> (0::enat)} \<subseteq> {x. g x \<noteq> (0::enat)}"
    apply auto using fg   
    by (metis ile0_eq)  
  with finG have "finite {x. f x \<noteq> (0::enat)}"  
    using finite_subset by blast   

  thm sum_mono sum_mono2
  
  have "sum f {x. f x \<noteq> (0::enat)} \<le> sum f {x. g x \<noteq> (0::enat)}"
    apply(rule sum_mono2) apply fact apply fact
    by simp
  also have "\<dots> \<le> sum g {x. g x \<noteq> (0::enat)}"
    apply(rule sum_mono) using fg by simp
  finally show ?thesis unfolding Sum_any.expand_set .
qed

lemma finite_support_mult:  
  assumes "finite {xa.  R1 xa \<noteq> (0::enat)}"
  and "finite {xa. R2 xa \<noteq> 0}"
shows "finite {xa. R2 xa * R1 xa \<noteq> 0}"
proof -
 
  have "{(xa,xa)|xa. R2 xa * R1 xa \<noteq> 0} = {(xa,xa)|xa. R2 xa \<noteq> 0 \<and> R1 xa \<noteq> 0}" by auto
  also have "\<dots> \<subseteq> {(xa,xb)|xa xb. R2 xa \<noteq> 0 \<and> R1 xb \<noteq> 0}" by auto
  also have "\<dots> = {xa. R2 xa \<noteq> 0} \<times> {xb. R1 xb \<noteq> 0}" by auto 
  finally have k: "{xa. R2 xa * R1 xa \<noteq> 0} \<subseteq> fst ` ({xa. R2 xa \<noteq> 0} \<times> {xb. R1 xb \<noteq> 0})" by blast

  show ?thesis
    apply(rule finite_subset[OF k])
    apply(rule finite_imageI) 
    apply(rule finite_cartesian_product) by fact+
qed


lemma timerefine_mono: 
  assumes "wfR R"
  shows "c\<le>c' \<Longrightarrow> timerefine R c \<le> timerefine R c'"
  apply(cases c) apply simp
  apply(cases c') apply (auto simp: timerefine_def split: nrest.splits option.splits simp: le_fun_def)
  subgoal  by (metis le_some_optE) 
  proof (goal_cases)
    case (1 x2 x2a x x2b x2c xa)
    then have l: "\<And>ac. x2b ac \<le> x2c ac"  
      by (metis le_funD less_eq_option_Some)    
    show ?case 
      apply(rule Sum_any_mono)
      subgoal using l apply(rule mult_right_mono) by simp
      apply(rule wfR_finite_mult_left) by fact
  qed 


lemma assumes "wfR R1" "wfR R2"
  shows timerefine_iter: "timerefine R1 (timerefine R2 c) =  timerefine (pp R1 R2) c"
  unfolding timerefine_def 
  apply(cases c) apply simp 
  apply (auto simp: le_fun_def pp_def split: option.splits) apply (rule ext)
  apply (auto simp: le_fun_def pp_def split: option.splits) 
    apply(subst Sum_any_right_distrib)
  subgoal apply(rule finite_wfR_middle_mult) using assms by simp_all
    apply (rule ext)
  subgoal for mc r Mc cc
        apply (subst Sum_any.swap[where C="{a. \<exists>b. Mc a * (R2 a b * R1 b cc) \<noteq> 0} \<times> {b. \<exists>a. Mc a * (R2 a b * R1 b cc) \<noteq> 0}"])
        subgoal apply(rule wfR_finite_crossprod) using assms by simp
        subgoal by simp 
        apply(subst Sum_any_left_distrib)
        subgoal apply(rule wfR_finite_mult_left) using assms by simp 
        by (meson Sum_any.cong ab_semigroup_mult_class.mult_ac(1))  
      done 

lemma timerefine_trans: 
  assumes "wfR R1" "wfR R2" shows 
  "a \<le> timerefine R1 b \<Longrightarrow> b \<le> timerefine R2 c \<Longrightarrow> a \<le> timerefine (pp R1 R2) c"
  apply(subst timerefine_iter[symmetric, OF assms])
    apply(rule order.trans) apply simp
    apply(rule timerefine_mono) using assms by auto

   



end