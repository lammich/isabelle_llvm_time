theory Time_Refinement
imports NREST NREST_Type_Classes
begin

section \<open>Misc about enat\<close>


lemma apff: "n\<noteq>0 \<Longrightarrow> xa * enat n = y * enat n \<Longrightarrow> xa = y"
  apply(cases xa; cases y) by auto
 

lemma mult_Max_commute:
  fixes k :: enat
  assumes "finite N" and "N \<noteq> {}"
  shows "k * Max N = Max {k * m | m. m \<in> N}"
proof -
  have "\<And>x y. k * max x y = max (k * x) (k * y)"
    apply (simp add: max_def not_le)
    apply(cases k) apply auto
    subgoal  
      by (metis distrib_left leD le_iff_add)  
    subgoal  
      using \<open>\<And>y x nat. \<lbrakk>k = enat nat; x \<le> y; enat nat * y < enat nat * x\<rbrakk> \<Longrightarrow> enat nat * y = enat nat * x\<close> le_less by blast  
    subgoal  
      by (simp add: leD mult_left_mono)  
    subgoal  
      by (metis antisym enat_ord_code(3) imult_is_infinity not_le zero_le)  
    done
  with assms show ?thesis
    using hom_Max_commute [of "times k" N]
    by simp (blast intro: arg_cong [where f = Max])
qed



(* inspired by Sup_image_eadd1 *)
lemma Sup_image_emult1:
  assumes "Y \<noteq> {}"
  shows "Sup ((\<lambda>y :: enat. x * y) ` Y) = x * Sup Y"
proof(cases "finite Y")
  case True
  have "(*) x ` Y = {x * m |m. m \<in> Y}" by auto
  thus ?thesis using True by(simp add: Sup_enat_def mult_Max_commute assms)
next
  case False
  thus ?thesis
  proof(cases x)
    case (enat x')
    show ?thesis
      proof (cases "x'=0")
        case True
        then show ?thesis using enat apply (auto simp add: zero_enat_def[symmetric] )  
          by (metis SUP_bot bot_enat_def)  
      next
        case f: False
        with enat have "\<not> finite ((*) x ` Y)" using False
            apply(auto dest!: finite_imageD intro!: inj_onI)  
            by (simp add: mult.commute apff)  
        with False f enat show ?thesis by(simp add: Sup_enat_def assms) 
      qed       
  next
    case infinity
    from False have i: "Sup Y \<noteq> 0"  
      by (simp add: Sup_enat_def assms) 
    from infinity False have "(*) x ` Y = {\<infinity>} \<or> (*) x ` Y = {\<infinity>,0}" using assms  
      by (smt aux11 finite.simps image_insert imult_is_infinity insert_commute mk_disjoint_insert mult_zero_right)  
    thus ?thesis using i infinity assms
      apply auto
      subgoal by (metis imult_is_infinity) 
      subgoal  
        by (metis Sup_enat_def ccSup_empty imult_is_infinity sup_bot.right_neutral)   
      done
  qed
qed



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


lemma wfR_sup:
  fixes A :: "('b \<Rightarrow> ('c, enat) acost)"
  shows "wfR A \<Longrightarrow> wfR B \<Longrightarrow> wfR (sup A B)"
  unfolding wfR_def sup_fun_def sup_acost_def sup_enat_def
  apply(rule finite_subset[where B="{(s, f). the_acost (A s) f \<noteq> 0}\<union>{(s, f). the_acost (B s) f \<noteq> 0}"])
  by auto

(* I think this is better. It captures "finitely branching" *)
definition wfR' :: "('b \<Rightarrow> ('c, _::mult_zero) acost) \<Rightarrow> bool" where
  "wfR' R = (\<forall>s. finite {f. the_acost (R s) f \<noteq> 0})"


definition wfR2 :: "(('c, _::mult_zero) acost) \<Rightarrow> bool" where
  "wfR2 R = (finite {f. the_acost R f \<noteq> 0})"


lemma wfR2_enum:
  fixes R :: "(('c::enum, _) acost)"
  shows "wfR2 R"
  unfolding wfR2_def by simp

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




section \<open>Time Refinement and bind\<close>

lemma nofailT_timerefine[refine_pw_simps]: "nofailT (timerefine R m) \<longleftrightarrow> nofailT m" 
  unfolding nofailT_def timerefine_def by (auto split: nrest.splits)



definition inresTf' :: "('a,('b,enat)acost) nrest \<Rightarrow> 'a \<Rightarrow> (('b,enat)acost) \<Rightarrow> bool" where 
  "inresTf' S x t \<equiv> (\<forall>b. (case S of FAILi \<Rightarrow> True | REST X \<Rightarrow> (\<exists>t'. X x = Some t' \<and>  (the_acost t b) \<le> the_acost t' b)) )"

lemma pw_bindT_nofailTf' : "nofailT (bindT M f) \<longleftrightarrow> (nofailT M \<and> (\<forall>x t. inresTf' M x t \<longrightarrow> nofailT (f x)))"
  unfolding bindT_def   
  apply (auto elim: no_FAILTE simp: refine_pw_simps  split: nrest.splits )  
  subgoal  
    by (smt inresTf'_def nofailT_simps(2) nrest.simps(5))  
  subgoal for M x t unfolding inresTf'_def apply auto
  proof (goal_cases)
    case 1
    then have "\<And>t. \<forall>b. \<exists>t'. M x = Some t' \<and>  (the_acost t b) \<le> the_acost t' b \<Longrightarrow> nofailT (f x)" by blast
    with 1(1,3,4) show ?case  
      by auto 
  qed   
  done

         
lemmas limit_bindT = project_acost_bindT


definition "limRef b R m = (case m of FAILi \<Rightarrow> FAILi | REST M \<Rightarrow> SPECT (\<lambda>r. case M r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) b))))"
 
lemma limRef_limit_timerefine: "(project_acost b (timerefine R m)) = limRef b R m"  
  unfolding limRef_def project_acost_def timerefine_def apply(cases m)  by (auto split: option.splits)
 

lemma inresTf'_timerefine: "inresTf' (timerefine R m) x t \<Longrightarrow> \<exists>t'. inresTf' m x t'"
  unfolding inresTf'_def timerefine_def by (auto split: nrest.splits option.splits)

lemma ff: "c\<le>a \<Longrightarrow> inresT c  x t \<Longrightarrow> inresT a x t"
  unfolding inresT_def by (auto split: nrest.splits)    


lemma enat_mult_cont: "Sup A * (c::enat) = Sup ((\<lambda>x. x*c)`A)"
  apply(cases "A={}")
  subgoal unfolding Sup_enat_def by simp
  using Sup_image_emult1
  by (metis mult_commute_abs)

lemma enat_mult_cont':
  fixes f :: "'a \<Rightarrow> enat"
  shows 
  "(Sup (f ` A)) * c = Sup ((\<lambda>x. f x * c) ` A)"
  using enat_mult_cont[of "f`A" c] 
  by (metis (mono_tags, lifting) SUP_cong   image_image)


lemma enat_add_cont':
  fixes f g :: "'a \<Rightarrow> enat"
  shows "(SUP b\<in>B. f b) + (SUP b\<in>B. g b) \<ge> (SUP b\<in>B. f b + g b)"  
  by (auto intro: Sup_least add_mono Sup_upper) 

lemma enat_Sum_any_cont:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> enat"
  assumes f: "finite {x. \<exists>y. f x y \<noteq> 0}"
  shows 
  "SUPREMUM B (\<lambda>y. Sum_any (\<lambda>x. f x y)) \<le> Sum_any (\<lambda>x. (SUPREMUM B (f x)))"
proof - 
  have "{a. SUPREMUM B (f a) \<noteq> 0} \<subseteq> {x. \<exists>y. f x y \<noteq> 0}"
    apply auto by (metis SUP_eqI i0_lb le_zero_eq) 


  { fix S :: "'a set"
    assume "finite S"
    then have "(SUP y\<in>B. \<Sum>x\<in>S. f x y) \<le> (\<Sum>x\<in>S. SUPREMUM B (f x))"
    proof (induct rule: finite_induct)
      case empty
      then show ?case apply auto  
      by (metis SUP_bot_conv(2) bot_enat_def) 
    next
      case (insert a A) 
      have "(SUP y\<in>B. (\<Sum>x\<in>insert a A. f x y)) =  (SUP y\<in>B. f a y + (\<Sum>x\<in>A. f x y))"
        using sum.insert insert by auto   
      also have "\<dots> \<le> (SUP b\<in>B. f a b) + (SUP y\<in>B. \<Sum>x\<in>A. f x y)"
        apply(subst enat_add_cont') by simp
      also have "\<dots> \<le> (SUP b\<in>B. f a b) + (\<Sum>x\<in>A. SUP b\<in>B. f x b)" using insert by auto
      also have "\<dots> = (\<Sum>x\<in>insert a A. SUP a\<in>B. f x a)" 
        using sum.insert insert by auto                          
      finally show ?case .
    qed
  } note finite_SUP_sum = this

  thm Sum_any.expand_set
  show ?thesis
    apply(subst (1) Sum_any.expand_superset[of "{x. \<exists>y. f x y \<noteq> 0}"])
    subgoal by fact subgoal apply auto done
    apply(subst (1) Sum_any.expand_superset[of "{x. \<exists>y. f x y \<noteq> 0}"])
    subgoal by fact subgoal apply fact done
    using f by(rule finite_SUP_sum)
  qed 


lemma pl:
  fixes R ::"_ \<Rightarrow> ('a, enat) acost"
  assumes "Ra \<noteq> {}" and "wfR R"
  shows  " Sup { Some (Sum_any (\<lambda>ac. the_acost x ac * the_acost  (R ac) b)) |x. x \<in> Ra}
             \<le> Some (Sum_any (\<lambda>ac. (SUP f\<in>Ra. the_acost f ac) * the_acost  (R ac) b))"
proof -
  have *: "{ Some (Sum_any (\<lambda>ac. the_acost x ac * the_acost  (R ac) b)) |x. x \<in> Ra} =
Some ` {  (Sum_any (\<lambda>ac. the_acost x ac * the_acost (R ac) b)) |x. x \<in> Ra}" by blast
  have *: "Sup { Some (Sum_any (\<lambda>ac. the_acost x ac * the_acost (R ac) b)) |x. x \<in> Ra}
          = SUPREMUM { (Sum_any (\<lambda>ac. the_acost x ac * the_acost (R ac) b)) |x. x \<in> Ra} Some " 
    unfolding * by simp
 
  have a: "\<And>ac. (SUP f\<in>Ra. the_acost f ac) * the_acost (R ac) b = (SUP f\<in>Ra. the_acost f ac * the_acost  (R ac) b)" 
    apply(subst enat_mult_cont') by simp

  have e: "finite {x.  the_acost (R x) b \<noteq> 0}" apply(rule wfR_fst) by fact

  show ?thesis unfolding *
    apply(subst Some_Sup[symmetric]) using assms apply simp
    apply simp  
    unfolding a apply(rule order.trans[OF _ enat_Sum_any_cont]) 
    subgoal by (simp add: setcompr_eq_image)
    subgoal apply(rule finite_subset[OF _ e]) by auto    
    done
qed

lemma oo: "Option.these (Ra - {None}) = Option.these (Ra)" 
  by (metis insert_Diff_single these_insert_None) 
lemma Sup_wo_None: "Ra \<noteq> {} \<and> Ra \<noteq> {None} \<Longrightarrow> Sup Ra = Sup (Ra-{None})"
  unfolding Sup_option_def apply auto unfolding oo by simp
lemma kkk:
  fixes R ::"_ \<Rightarrow> ('a,enat) acost"
  assumes "wfR R"
shows 
" (case SUP x\<in>Ra. x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost  (R ac) b)))
   \<ge> Sup {case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost  (R ac) b)) |x. x \<in>  Ra}"
  apply(cases "Ra={} \<or> Ra = {None}")
  subgoal by (auto split: option.splits simp: bot_option_def)
  subgoal apply(subst (2) Sup_option_def) apply simp unfolding Sup_acost_def apply simp
    

  proof -
    assume r: "Ra \<noteq> {} \<and> Ra \<noteq> {None}"
    then  obtain x where x: "Some x \<in> Ra"  
      by (metis everywhereNone not_None_eq)  

    have kl: "Sup {case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost  (R ac) b) |x. x \<in> Ra}
      = Sup ({case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost (R ac) b) |x. x \<in> Ra}-{None})"
      apply(subst Sup_wo_None) 
      subgoal apply safe subgoal using x by auto subgoal using x by force
      done by simp
  also have "({case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost  (R ac) b) |x. x \<in> Ra}-{None})
            = ({case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost  (R ac) b) |x. x \<in> Ra \<and> x\<noteq>None})"
    by (auto split: option.splits)
  also have "\<dots> = ({  Some (\<Sum>ac. the_acost x ac * the_acost (R ac) b) |x. x\<in>Option.these Ra})"
    by (force split: option.splits simp: Option.these_def) 
  finally have rrr: "Sup {case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost (R ac) b) |x. x \<in> Ra}
      = Sup ({  Some (\<Sum>ac. the_acost x ac * the_acost (R ac) b) |x. x\<in>Option.these Ra})" .


  show "Sup {case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost  (R ac) b) |x. x \<in> Ra}
         \<le> Some (\<Sum>ac. (SUP f\<in>Option.these Ra. the_acost f ac) * the_acost  (R ac) b)"
      unfolding rrr apply(subst pl)
      subgoal using x unfolding Option.these_def by auto
      subgoal by fact
      apply simp done
  qed
  done

lemma 
  ***: fixes R ::"_ \<Rightarrow> ('a,enat) acost"
assumes "wfR R"
shows 
"(case SUP x\<in>Ra. x r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) b)))
    \<ge> Sup {case x r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) b)) |x. x\<in>Ra}"
proof -
  have *: "{case x r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost (R ac) b) |x. x \<in> Ra}
      = {case x  of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost (R ac) b) |x. x \<in> (\<lambda>f. f r) ` Ra}"
    by auto
  have **: "\<And>f. (case SUP x\<in>Ra. x r of None \<Rightarrow> None | Some cm \<Rightarrow> f cm)
      = (case SUP x\<in>(\<lambda>f. f r) ` Ra. x of None \<Rightarrow> None | Some cm \<Rightarrow> f cm)"    
    by auto       

  show ?thesis unfolding * ** apply(rule kkk) by fact
qed



lemma nofail'': "x \<noteq> FAILT  \<longleftrightarrow> (\<exists>m. x=SPECT m)"
  unfolding nofailT_def  
  using nrest_noREST_FAILT by blast  

lemma limRef_bindT_le:
fixes R ::"_ \<Rightarrow> ('a,enat) acost" assumes "wfR R"
shows "limRef b R (bindT m f) \<ge> (case m of FAILi \<Rightarrow> FAILT | REST X \<Rightarrow> Sup {case f x of FAILi \<Rightarrow> FAILT | REST m2 \<Rightarrow> SPECT (\<lambda>r. case (map_option ((+) t1) \<circ> m2) r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) b))) |x t1. X x = Some t1})"
    unfolding limRef_def bindT_def apply(cases m) apply auto
  unfolding Sup_nrest_def apply (auto split: nrest.splits)
  apply(rule le_funI)   apply simp unfolding Sup_fun_def     
  subgoal 
    apply(rule order.trans) defer 
    apply(subst ***[OF assms]) apply simp   
    apply(rule Sup_least)
    apply auto
      apply(subst (asm) nofail'') apply (auto split: option.splits)
    apply(rule Sup_upper)
    apply auto
    subgoal for xa t1 ma x2
    apply(rule exI[where x="map_option ((+) t1) \<circ> ma"])
      apply safe subgoal apply simp done
      subgoal by auto   
      apply(rule exI[where x=xa])
      by simp 
    done
  done

lemma nofailT_limRef: "nofailT (limRef b R m) \<longleftrightarrow> nofailT m"
  unfolding limRef_def nofailT_def by (auto split: nrest.splits)

lemma inresT_limRef_D: "inresT (limRef b R (SPECT x2)) r' t' \<Longrightarrow> (\<exists>x2a. x2 r' = Some x2a \<and> enat t' \<le> (Sum_any (\<lambda>ac. the_acost x2a ac * the_acost (R ac) b)))"
  unfolding limRef_def apply simp
   by (auto split: option.splits)

lemma zzz: fixes A B :: "('a, enat) acost"
  shows "the_acost (case A of acostC a \<Rightarrow> case B of acostC b \<Rightarrow> acostC (\<lambda>x. a x + b x)) a *
                    the_acost (R a) b =
        the_acost A a * the_acost (R a) b + the_acost B a * the_acost (R a) b"
  apply(cases A; cases B) apply auto
  by (simp add: comm_semiring_class.distrib)
 
lemma timerefine_bindT_ge:
  fixes R :: "_ \<Rightarrow> ('a,enat) acost"
  assumes wfR: "wfR R"
  shows "bindT (timerefine R m) (\<lambda>x. timerefine R (f x)) \<le> timerefine R (bindT m f)"    
  unfolding  pw_acost_le_iff'
  apply safe
  subgoal apply (simp add: nofailT_timerefine nofailT_project_acost pw_bindT_nofailTf')
          apply auto apply(frule inresTf'_timerefine) by simp 
  subgoal for b x t
    unfolding limit_bindT 
    unfolding pw_inresT_bindT
    unfolding limRef_limit_timerefine
    apply(rule ff[OF limRef_bindT_le]) using assms apply simp
  apply(simp add: nofailT_limRef)
      apply(cases m) subgoal by auto
      apply simp 
      unfolding pw_inresT_Sup apply auto
      apply(drule inresT_limRef_D) apply auto
      subgoal for x2 r' t' t'' x2a
      apply(rule exI[where x="(case f r' of FAILi \<Rightarrow> FAILT | REST m2 \<Rightarrow> SPECT (\<lambda>r. case (map_option ((+) x2a) \<circ> m2) r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) b))))"])
      apply safe
       apply(rule exI[where x=r'])
       apply(rule exI[where x=x2a])
         apply simp
        apply (cases "f r'") subgoal by auto
        apply simp
        apply(drule inresT_limRef_D) apply auto
        apply(rule exI[where x="t' + t''"]) apply (simp add: zzz comm_semiring_class.distrib plus_acost_alt ) 
        apply(subst Sum_any.distrib)
        subgoal apply(rule wfR_finite_mult_left) using wfR by simp
        subgoal apply(rule wfR_finite_mult_left) using wfR by simp
        subgoal  
          using add_mono by fastforce  
        done
    done
  done

 
end