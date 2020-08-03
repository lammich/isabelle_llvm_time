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



definition timerefineA ::"('b \<Rightarrow> ('c,'d::{complete_lattice,comm_monoid_add,times,mult_zero}) acost)
                             \<Rightarrow> ( ('b,'d) acost) \<Rightarrow> ( ('c,'d) acost)"
  where "timerefineA R cm =  (acostC (\<lambda>cc. Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) cc)))"

lemma timerefine_consume: "timerefine E (consume M t) = consume (timerefine E M) (timerefineA E t)"
  apply(auto simp: timerefine_def consume_def timerefineA_def split: nrest.splits option.splits intro!: ext)
  sorry

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

definition wfR'' :: "('b \<Rightarrow> ('c, _::mult_zero) acost) \<Rightarrow> bool" where
  "wfR'' R = (\<forall>f. finite {s. the_acost (R s) f \<noteq> 0})"


lemma "wfR R \<Longrightarrow> wfR'' R"
  unfolding wfR_def wfR''_def apply safe
  subgoal for f
    apply(rule finite_cartesian_productD1[where B="{f}"])
     apply(rule finite_subset[rotated]) by auto
  done

lemma "wfR R \<Longrightarrow> wfR' R"
  unfolding wfR_def wfR'_def apply safe
  subgoal for s
    apply(rule finite_cartesian_productD2[where A="{s}"])
     apply(rule finite_subset) by auto
  done


lemma assumes "wfn m"
  assumes "m = SPECT M" "M r = Some cm"
  shows "finite {ac. the_acost cm ac * the_acost (R ac) cc \<noteq> 0}"
proof -
  from assms have "finite {x. the_acost cm x \<noteq> 0}" unfolding wfn_def by force
  show ?thesis
    apply(rule finite_subset[where B="{ac. the_acost cm ac \<noteq> 0}"])
    subgoal by auto
    subgoal apply fact done
    done
qed 


lemma "wfR'' (\<lambda>x. acostC (\<lambda>y. if x = y then 1 else 0))"
  unfolding wfR''_def 
  by auto

lemma wfR''_finite_mult_left:
  assumes "wfR'' R"
  shows "finite {ac. the_acost cm ac * the_acost (R ac) cc \<noteq> 0}"
proof - 
  from assms have "finite {s. the_acost (R s) cc \<noteq> 0}" unfolding wfR''_def by auto
  show ?thesis
    apply(rule finite_subset[where B="{ac. the_acost (R ac) cc \<noteq> 0}"])
    subgoal by auto
    subgoal apply fact done
    done
qed 



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

lemma wfR_finite_mult_left2:
  fixes R2 :: "('b \<Rightarrow> ('c, 'd::mult_zero) acost)"
  assumes "wfR'' R2"
  shows "finite {a. the_acost Mc a * the_acost (R2 a) ac \<noteq> 0}"
proof -

  have "{a. the_acost Mc a * the_acost (R2 a) ac \<noteq> 0} \<subseteq> {a. the_acost (R2 a) ac \<noteq> 0}"
    apply(cases Mc) by (auto simp: zero_acost_def)
  then
  show ?thesis
    apply(rule finite_subset)
    using assms unfolding wfR''_def by simp
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

lemma timerefine_mono2: 
  fixes R :: "_ \<Rightarrow> ('a, 'b::{complete_lattice,nonneg,mult_zero,ordered_semiring}) acost"
  assumes "wfR'' R"
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
      apply(rule wfR_finite_mult_left2) by fact
  qed 
  thm wfR''_def

lemma "finite A \<Longrightarrow> (\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0) \<Longrightarrow> x\<in>A \<Longrightarrow> f x > 0 \<Longrightarrow> sum f A > (0::enat)"
  using sum_pos2 sorry

lemma yeah: "(\<And>s. finite {b. f s b \<noteq> 0}) \<Longrightarrow> {s. Sum_any (f s) \<noteq> (0::enat)} = {s. (\<exists>b. f s b \<noteq> 0)}"
  apply auto  
  subgoal using Sum_any.not_neutral_obtains_not_neutral by blast
  subgoal  
    by (simp add: Sum_any.expand_set) 
  done

thm Sum_any.not_neutral_obtains_not_neutral

lemma z: "(a::enat) * b \<noteq> 0 \<longleftrightarrow> a \<noteq> 0 \<and> b \<noteq> 0"
  by auto

  

lemma wfR''D: "wfR'' R \<Longrightarrow> finite {s. the_acost (R s) f \<noteq> 0}"
  by (auto simp: wfR''_def)

lemma 
  wfR_finite_crossprod2:
  fixes Mc :: "('a, enat) acost"
  assumes "wfR'' R1"  "wfR'' R2"
  shows "finite ({a. \<exists>b. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0} \<times> {b. \<exists>a. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0})"
proof -

  have **: "{a. \<exists>b. the_acost Mc a \<noteq> 0 \<and> the_acost (R2 a) b \<noteq> 0 \<and> the_acost (R1 b) cc \<noteq> 0}
      \<subseteq> (\<Union>b\<in>{b. the_acost (R1 b) cc \<noteq> 0}. {a. the_acost Mc a \<noteq> 0 \<and> the_acost (R2 a) b \<noteq> 0 })"
    by auto 
  show ?thesis 
    apply(rule finite_cartesian_product)
    subgoal 
      apply(subst z)
      apply(subst z)
      apply(rule finite_subset[OF **])
      apply(rule finite_Union)
      subgoal apply(rule finite_imageI) using assms(1)[THEN wfR''D] by simp
      subgoal apply auto subgoal for b apply(rule finite_subset[where B="{s. the_acost (R2 s) b \<noteq> 0}"])
        using assms(2)[THEN wfR''D] by auto
      done
    done
    subgoal 
      apply(subst z)
      apply(subst z)   
      apply(rule finite_subset[where B="{b. the_acost (R1 b) cc \<noteq> 0}"])
      subgoal by auto
      subgoal using  assms(1)[THEN wfR''D] by simp 
      done
    done
  qed 

lemma pf: "(x, z) \<in> (R O S) \<longleftrightarrow> (\<exists>y. (x, y) \<in> R \<and> (y,z) \<in> S)"
  by auto

lemma assumes "finite ({y. (x, y) \<in> R })"
        and "\<And>y. finite ({z. (y, z) \<in> S })"
      shows "finite ({z. (x, z) \<in> (R O S) })"
proof -
  have *: "{z. (x, z) \<in> (R O S) } = (\<Union>y. {z. (x, y) \<in> R \<and> (y,z) \<in> S})"
    unfolding pf by auto
  have **: "{z. (x, z) \<in> (R O S) } \<subseteq> (\<Union>y\<in>{y. (x, y) \<in> R }. {z. (y,z) \<in> S})"
    unfolding pf by auto

  show "finite ({z. (x, z) \<in> (R O S) })"
    apply(rule finite_subset[OF **]) 
    apply(rule finite_Union)
    subgoal
      apply(rule finite_imageI) apply fact done
    subgoal for A apply auto
      subgoal for y
        apply(rule finite_subset[where B="{z. (y, z) \<in> S }"])
         apply blast 
        apply(rule assms(2)) done
      done
    done
qed


lemma wfR''_ppI:
  fixes R1 :: "'a \<Rightarrow> ('b, enat) acost"
  assumes R1: "wfR'' R1" and R2: "wfR'' R2"
  shows "wfR'' (pp R1 R2)"
  unfolding pp_def wfR''_def
  apply simp apply safe
proof -
  fix f  
  have "\<And>s. finite {b. the_acost (R2 s) b * the_acost (R1 b) f \<noteq> 0}"
    apply(rule wfR_finite_mult_left2) by fact

  have l: "{s. \<exists>b. the_acost (R2 s) b \<noteq> 0 \<and> the_acost (R1 b) f \<noteq> 0}
      = (\<Union>b\<in>{b. the_acost (R1 b) f \<noteq> 0}. {s. the_acost (R2 s) b \<noteq> 0 })"
    by auto

  show "finite {s. (\<Sum>b. the_acost (R2 s) b * the_acost (R1 b) f) \<noteq> 0}"
    apply(subst yeah) apply fact
    apply(subst z)
    apply(subst l)
    apply(rule finite_Union) 
    subgoal  apply(rule finite_imageI) by (rule R1[THEN wfR''D])
    subgoal       
      using R2
      by (auto simp: wfR''_def)
    done
qed

lemma
  fixes R1 :: "_ \<Rightarrow> ('a, enat) acost"
  assumes "wfR'' R1" "wfR'' R2"
  shows timerefine_iter2: "timerefine R1 (timerefine R2 c) =  timerefine (pp R1 R2) c"
  unfolding timerefine_def 
  apply(cases c)
  subgoal by simp 
  apply (auto simp: le_fun_def pp_def split: option.splits) apply (rule ext)
  apply (auto simp: le_fun_def pp_def split: option.splits)
  apply(subst Sum_any_right_distrib)
  subgoal apply(rule wfR''_finite_mult_left[of R1]) using assms by simp_all
  apply (rule ext)
  subgoal for mc r Mc cc
    apply (subst Sum_any.swap[where C="{a. \<exists>b. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0} \<times> {b. \<exists>a. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0}"])
    subgoal      
      apply(rule wfR_finite_crossprod2) using assms by auto
    subgoal by simp 
    apply(subst Sum_any_left_distrib)
    subgoal apply(rule wfR_finite_mult_left2) using assms by simp 
    apply(rule Sum_any.cong)
    by (meson mult.assoc)
  done 


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

lemma pl2:
  fixes R ::"_ \<Rightarrow> ('a, enat) acost"
  assumes "Ra \<noteq> {}" and "wfR'' R"
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

  have e: "finite {x.  the_acost (R x) b \<noteq> 0}" using assms(2) unfolding wfR''_def by simp

  show ?thesis unfolding *
    apply(subst Some_Sup[symmetric]) using assms apply simp
    apply simp  
    unfolding a apply(rule order.trans[OF _ enat_Sum_any_cont]) 
    subgoal by (simp add: setcompr_eq_image)
    subgoal apply(rule finite_subset[OF _ e]) by auto    
    done
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

term continuous

thm continuous_option

lemma kkk2:
  fixes R ::"_ \<Rightarrow> ('a,enat) acost"
  assumes "wfR'' R"
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
      unfolding rrr apply(subst pl2)
      subgoal using x unfolding Option.these_def by auto
      subgoal by fact
      apply simp done
  qed
  done

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
  aaa: fixes R ::"_ \<Rightarrow> ('a,enat) acost"
assumes "wfR'' R"
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

  show ?thesis unfolding * ** apply(rule kkk2) by fact
qed

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

lemma limRef_bindT_le2:
fixes R ::"_ \<Rightarrow> ('a,enat) acost" assumes "wfR'' R"
shows "limRef b R (bindT m f) \<ge> (case m of FAILi \<Rightarrow> FAILT | REST X \<Rightarrow> Sup {case f x of FAILi \<Rightarrow> FAILT | REST m2 \<Rightarrow> SPECT (\<lambda>r. case (map_option ((+) t1) \<circ> m2) r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) b))) |x t1. X x = Some t1})"
    unfolding limRef_def bindT_def apply(cases m) apply auto
  unfolding Sup_nrest_def apply (auto split: nrest.splits)
  apply(rule le_funI)   apply simp unfolding Sup_fun_def     
  subgoal 
    apply(rule order.trans) defer 
    apply(subst aaa[OF assms]) apply simp   
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


lemma timerefine_bindT_ge2:
  fixes R :: "_ \<Rightarrow> ('a,enat) acost"
  assumes wfR'': "wfR'' R"
  shows "bindT (timerefine R m) (\<lambda>x. timerefine R (f x)) \<le> timerefine R (bindT m f)"    
  unfolding  pw_acost_le_iff'
  apply safe
  subgoal apply (simp add: nofailT_timerefine nofailT_project_acost pw_bindT_nofailTf')
          apply auto apply(frule inresTf'_timerefine) by simp 
  subgoal for b x t
    unfolding limit_bindT 
    unfolding pw_inresT_bindT
    unfolding limRef_limit_timerefine
    apply(rule ff[OF limRef_bindT_le2])
    using assms
     apply simp
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
        subgoal apply(rule wfR''_finite_mult_left) using wfR'' by simp
        subgoal apply(rule wfR''_finite_mult_left) using wfR'' by simp
        subgoal  
          using add_mono by fastforce  
        done
    done
  done


lemma timerefine_R_mono: 
  fixes R :: "_ \<Rightarrow> ('a, enat) acost"
  assumes "wfR R'"
  shows "R\<le>R' \<Longrightarrow> timerefine R c \<le> timerefine R' c"
  unfolding timerefine_def apply(cases c)
   apply (auto intro!: le_funI simp: less_eq_acost_def split: option.splits)
  apply(rule Sum_any_mono)
   apply(rule mult_left_mono) apply(auto simp: le_fun_def)
  subgoal premises prems for x2 x x2a xa xb 
    using prems(1)[rule_format, of xb] apply(cases "R xb"; cases "R' xb") apply auto 
    unfolding less_eq_acost_def by auto
  subgoal for x2 x x2a xa using assms(1) unfolding wfR_def
    apply -
    apply(rule finite_subset[where B="{x. the_acost (R' x) xa \<noteq> 0}"]) apply auto
    apply(rule wfR_fst) apply (rule assms) done
  done


lemma timerefine_R_mono_wfR'': 
  fixes R :: "_ \<Rightarrow> ('a, enat) acost"
  assumes "wfR'' R'"
  shows "R\<le>R' \<Longrightarrow> timerefine R c \<le> timerefine R' c"
  unfolding timerefine_def apply(cases c)
   apply (auto intro!: le_funI simp: less_eq_acost_def split: option.splits)
  apply(rule Sum_any_mono)
   apply(rule mult_left_mono) apply(auto simp: le_fun_def)
  subgoal premises prems for x2 x x2a xa xb 
    using prems(1)[rule_format, of xb] apply(cases "R xb"; cases "R' xb") apply auto 
    unfolding less_eq_acost_def by auto
  subgoal for x2 x x2a xa using assms(1) unfolding wfR_def
    apply -
    apply(rule finite_subset[where B="{x. the_acost (R' x) xa \<noteq> 0}"]) apply auto
    using assms[unfolded wfR''_def] apply simp done
  done

subsection \<open>TId\<close>


definition "TId = (\<lambda>x. acostC (\<lambda>y. (if x=y then 1 else 0)))"

lemma timerefine_id:
  fixes M :: "(_,(_,enat)acost) nrest"
  shows "timerefine TId M = M"
  apply(cases M; auto simp: timerefine_def TId_def)
  apply(rule ext) apply(auto split: option.splits)
  subgoal for x2 r x2a apply(cases x2a) apply simp
    apply(rule ext) apply(simp add: if_distrib)
    apply(subst mult_zero_right)
    apply(subst Sum_any.delta) by simp
  done


lemma timerefineA_upd_aux: "(if a = m then x else (0::enat)) * b = (if a = m then x * b else 0)"
  by auto

lemma timerefineA_upd:
  fixes R :: "'b \<Rightarrow> ('c, enat) acost"
  shows "timerefineA (R(n:=y)) (cost m x) = (if n=m then acostC (\<lambda>z. x * the_acost y z) else timerefineA R (cost m x))"
  unfolding timerefineA_def
  by (auto simp: cost_def zero_acost_def timerefineA_upd_aux)

lemma timerefineA_TId_aux: "the_acost x a * (if b then (1::enat) else 0)
    = (if b then the_acost x a  else 0)"
  apply(cases b) by auto

lemma timerefineA_TId_eq:
  shows "timerefineA TId x = (x:: ('b, enat) acost)"
  unfolding timerefineA_def TId_def 
  by (simp add: timerefineA_TId_aux)

lemma wfR_TId: "wfR TId"
  unfolding TId_def wfR_def apply simp
  sorry

lemma "wfR' TId"
  unfolding TId_def wfR'_def by simp
lemma wfR''_TId: "wfR'' TId"
  unfolding TId_def wfR''_def by simp





subsection \<open>Stuff about integrating functional Specification (with top time)\<close>


lemma getDiff: assumes "A \<subseteq> C"
  shows "\<exists>B. C = A \<union> B \<and> A \<inter> B = {}"
  using assms 
  by (metis Diff_disjoint Diff_partition)  

lemma assumes "finite B" "{x. f x\<noteq>0} \<subseteq> B"
  shows sum_extend_zeros: "sum f B = sum f {x. f x\<noteq>0}"
proof -
  from assms(2) obtain A where B: "B = A \<union> {x. f x\<noteq>0}" and disj[simp]: "A \<inter> {x. f x\<noteq>0} = {}"    
    by (metis Int_commute getDiff sup_commute)  
  from assms(1) B have [simp]: "finite A" "finite {x. f x\<noteq>0}" by auto

  have *: "sum f A = 0"
    apply(rule sum.neutral)
    using disj by blast    

  show ?thesis
    unfolding B
    by(simp add: * sum.union_disjoint)
qed



lemma inf_acost: "inf (acostC a) (acostC b) = acostC (inf a b)"
  unfolding inf_acost_def by auto
  
lemma z1: "\<And>a. a \<noteq> 0 \<Longrightarrow> a * top = (top::enat)" 
    unfolding top_enat_def  
    by (simp add: imult_is_infinity)

lemma z2: "\<And>a. a \<noteq> 0 \<Longrightarrow> top * a = (top::enat)" 
    unfolding top_enat_def  
    by (simp add: imult_is_infinity) 

lemma fixes a b :: enat
  shows inf_absorbs_top2: "inf (b * a) (top * a) = b * a"
    apply(cases "a=0"; cases "b=0") by (auto simp: z2)
lemma fixes a b :: enat
  shows inf_absorbs_top: "inf (a * b) (a * top) = a * b"
    apply(cases "a=0"; cases "b=0") by (auto simp: z1)
                                 

lemma blatop:
  fixes f :: "_ \<Rightarrow> enat"
  assumes F: "finite {x. f x \<noteq> 0}"
  shows " Sum_any (inf (\<lambda>x. f x * g x) (\<lambda>x. f x * top))
     = inf (Sum_any (\<lambda>x. f x * g x)) (Sum_any (\<lambda>x. f x * top))"
proof (cases "{x. f x \<noteq> 0} = {}")
  case True
  then show ?thesis
    unfolding Sum_any.expand_set by simp
next
  case False 
  with F have cn0: "card {x. f x \<noteq> 0} \<noteq> 0" by simp
  
  have 1: "{a. inf (\<lambda>x.   (f x * g x)) (\<lambda>x.   (f x) * top) a \<noteq> 0}
      \<subseteq> {x. f x \<noteq> 0}" by auto
  have 2: "{a. f a * g a \<noteq> 0} \<subseteq> {x. f x \<noteq> 0}" by auto
  have 3: "{a. f a * top \<noteq> 0} \<subseteq> {x. f x \<noteq> 0}" by auto
 

  { fix a b :: enat
  have "inf (a * b) (a * top) = a * b"
    apply(cases "a=0"; cases "b=0") by (auto simp: z1)
  } note * = this

  have "(\<Sum>a\<in>{x. f x \<noteq> 0}. f a * top) = (\<Sum>a\<in>{x. f x \<noteq> 0}. top)"
    apply(rule sum.cong) apply simp by (auto simp: top_enat_def imult_is_infinity)
  also have "\<dots> = top" 
    using False cn0 by (simp add: top_enat_def imult_is_infinity)
  finally have i: "(\<Sum>a\<in>{x. f x \<noteq> 0}. f a * top) = top" .
    

  show ?thesis
    unfolding Sum_any.expand_set
    apply(subst sum_extend_zeros[symmetric, OF _ 1]) apply fact
    apply(subst sum_extend_zeros[symmetric, OF _ 2]) apply fact
    apply(subst sum_extend_zeros[symmetric, OF _ 3]) apply fact
    by (simp add: * i)
qed

lemma blatop2:
  fixes f :: "_ \<Rightarrow> enat"
  assumes F: "finite {x. f x \<noteq> 0}"
  shows "inf (Sum_any (\<lambda>x. g x * f x)) (Sum_any (\<lambda>x. top * f x))
    = Sum_any (inf (\<lambda>x. g x * f x) (\<lambda>x. top * f x))"
  apply(subst (1) mult.commute) 
  apply(subst (2) mult.commute)  
  apply(subst blatop[symmetric]) apply fact
  by(simp add: mult.commute)

lemma timerefine_inf_top_distrib:
  fixes m :: "('a, ('d, enat) acost) nrest"
  assumes a: "\<And>cc. finite {x. the_acost (R x) cc \<noteq> 0}"
  shows "timerefine R (inf m (SPEC P (\<lambda>_. top)))
        = inf (timerefine R m) (timerefine R (SPEC P (\<lambda>_. top)))"
  unfolding timerefine_def SPEC_def 
  apply(cases m) apply simp apply simp apply(rule ext)
  apply auto
  subgoal for x2 r
    apply(cases "x2 r") apply simp
    apply simp
    unfolding inf_acost apply simp apply(rule ext)
    apply (simp add: top_acost_def) 
    apply(subst blatop2) apply (rule a)
    apply(subst inf_fun_def)
    using inf_absorbs_top2
    apply(subst inf_absorbs_top2) by simp
  done


lemma 
  SPEC_timerefine:
  "A \<le> A' \<Longrightarrow> (\<And>x. B x \<le> timerefineA R (B' x)) \<Longrightarrow> SPEC A B \<le> timerefine R (SPEC A' B')"
  apply(auto simp: SPEC_def)
  unfolding timerefine_SPECT
  apply (simp add: le_fun_def) apply auto
  unfolding timerefineF_def timerefineA_def
  by auto

lemma 
  SPEC_timerefine_eq:
  "(\<And>x. B x = timerefineA R (B' x)) \<Longrightarrow> SPEC A B = timerefine R (SPEC A B')"
  apply(auto simp: SPEC_def)
  unfolding timerefine_SPECT 
  apply auto
  unfolding timerefineF_def timerefineA_def
  by auto


experiment
begin
definition sift_down :: "('a, (char list, enat) acost) nrest"
  where "sift_down = undefined"
definition sift_down1  :: "('a, (char list, enat) acost) nrest"
  where "sift_down1 = undefined"
definition sift_down_spec ::  "'a \<Rightarrow> bool" 
  where "sift_down_spec = undefined"
definition sift_down_cost :: "(_,enat) acost"
    where "sift_down_cost = undefined"

lemma "sift_down \<le> SPEC sift_down_spec (\<lambda>_. top)" 
  sorry

lemma "sift_down1 \<le> sift_down"
  sorry

lemma F: "sift_down1 \<le> SPEC (sift_down_spec) top"
  sorry

lemma T: "sift_down1 \<le>\<^sub>n SPEC (\<lambda>_. True) (\<lambda>_. sift_down_cost)"
  sorry

lemma FT: "sift_down1 \<le> SPEC sift_down_spec (\<lambda>_. sift_down_cost)"
  sorry
 
definition "sift_down_spec_sd = SPEC sift_down_spec (\<lambda>_. cost ''sift_down'' (1::enat))"

definition "RR = TId(''sift_down'' :=sift_down_cost)"



 
lemma tAtop: "wfR'' R \<Longrightarrow> timerefineA R top = top"
  sorry

lemma *: "SPEC sift_down_spec (\<lambda>_. sift_down_cost)
      = timerefine RR (SPEC sift_down_spec (\<lambda>_. cost ''sift_down'' 1))"
  unfolding RR_def 
  apply(rule SPEC_timerefine_eq)
  by (simp add: timerefineA_upd)
  
lemma "sift_down1 \<le> timerefine RR sift_down_spec_sd"
  apply(rule order.trans[OF FT])
  by (simp add: * sift_down_spec_sd_def)

term "timerefine RR sift_down_spec_sd"
lemma "sift_down1 \<le> timerefine RR sift_down_spec_sd"
proof -
  have "sift_down1 <= SPEC sift_down_spec (\<lambda>_. sift_down_cost)"
    by (rule FT)
  also have "\<dots> = inf (SPEC sift_down_spec (\<lambda>_. top)) (SPEC (\<lambda>_. True)  (\<lambda>_. sift_down_cost))"
    by (auto simp add: SPEC_def)
  also have "\<dots> \<le> inf (timerefine RR (SPEC sift_down_spec top)) (timerefine RR (SPEC (\<lambda>_. True) (\<lambda>_. cost ''sift_down'' 1)))"
    apply(rule inf_mono)
    subgoal
      apply(rule SPEC_timerefine)
       apply simp
      unfolding RR_def
      apply(simp add: top_fun_def)
      apply(subst tAtop) subgoal sorry
      apply simp
      done
    subgoal 
      apply(rule SPEC_timerefine)
      apply simp term "sift_down_cost"
      unfolding RR_def using timerefineA_upd
      apply(subst timerefineA_upd)
      by(simp add: )
    done
  also have "\<dots> = timerefine RR (SPEC sift_down_spec (\<lambda>_. cost ''sift_down'' 1))"
    unfolding top_fun_def
    apply(subst inf.commute)
    apply(subst timerefine_inf_top_distrib[symmetric])
    subgoal sorry
    unfolding SPEC_def apply simp
    apply(rule arg_cong[where f="timerefine RR"])
    by auto
  also have "\<dots> = timerefine RR sift_down_spec_sd" 
    unfolding sift_down_spec_sd_def by simp
  finally show ?thesis .
qed
end


(*

in heap_sort
use
sift_down_spec_sd



in heap_sort'
use
 *) 


end