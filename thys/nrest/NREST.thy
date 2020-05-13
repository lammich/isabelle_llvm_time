theory NREST
  imports "HOL-Library.Extended_Nat" "Refine_Monadic.RefineG_Domain"  Refine_Monadic.Refine_Misc  
  "HOL-Library.Monad_Syntax"   "HOL-Library.Groups_Big_Fun"
  Complex_Main 

(* "HOL-Library.Function_Algebras" *)
 "Abstract_Cost"
begin





section "Auxiliaries"

subsection "Auxiliaries for option"

lemma less_eq_option_None_is_None': "x \<le> None \<longleftrightarrow> x = None" by(auto simp: less_eq_option_None_is_None)

lemma everywhereNone: "(\<forall>x\<in>X. x = None) \<longleftrightarrow> X = {} \<or> X = {None}"
  by auto

subsection "Auxiliaries for enat"


lemma helper: "x2 \<le> x2a \<Longrightarrow> \<not> x2 < a \<Longrightarrow> \<not> x2a < a \<Longrightarrow>  x2 - (a::enat) \<le> x2a - a"
  apply(cases x2; cases x2a) apply auto apply(cases a) by auto

lemma helper2: "x2b \<le> x2 \<Longrightarrow> \<not> x2a < x2  \<Longrightarrow> \<not> x2a < x2b \<Longrightarrow> x2a - (x2::enat) \<le> x2a - x2b"
  apply(cases x2; cases x2a) apply auto apply(cases x2b) by auto

lemma Sup_finite_enat: "Sup X = Some (enat a) \<Longrightarrow> Some (enat a) \<in> X"
  by (auto simp: Sup_option_def Sup_enat_def these_empty_eq Max_eq_iff in_these_eq split: if_splits)

lemma Sup_enat_less2: " Sup X = \<infinity> \<Longrightarrow> (\<exists>x\<in>X. enat t < x)"
  unfolding  Sup_enat_def using    finite_enat_bounded linear 
  apply(auto split: if_splits)  
   apply (smt Max_in empty_iff enat_ord_code(4))
  by (smt not_less)  


lemma [simp]: "t \<le> Some (\<infinity>::enat)"
  by (cases t, auto)

subsection "Auxiliary (for Sup and Inf)"



lemma aux11: "f`X={y} \<longleftrightarrow> (X\<noteq>{} \<and> (\<forall>x\<in>X. f x = y))" by auto
 
lemma aux2: "(\<lambda>f. f x) ` {[x \<mapsto> t1] |x t1. M x = Some t1} = {None} \<longleftrightarrow> (M x = None \<and> M\<noteq>Map.empty)"
  apply (cases "M x"; auto simp: aux11)
  by force

lemma aux3: "(\<lambda>f. f x) ` {[x \<mapsto> t1] |x t1. M x = Some t1} = {Some t1 | t1. M x = Some t1} \<union> ({None | y. y\<noteq>x \<and> M y \<noteq> None })"
  by (fastforce split: if_splits simp: image_iff) 

lemma Sup_pointwise_eq_fun: "(SUP f\<in>{[x \<mapsto> t1] |x t1. M x = Some t1}. f x) = M x"
  unfolding Sup_option_def  
  apply (simp add: aux2) 
  apply (auto simp: aux3)
  by (metis (mono_tags, lifting) Some_image_these_eq Sup_least in_these_eq mem_Collect_eq sup_absorb1 these_image_Some_eq)


lemma SUP_eq_None_iff: "(SUP f\<in>X. f x) = None \<longleftrightarrow> X={} \<or> (\<forall>f\<in>X. f x = None)"
  by (smt SUP_bot_conv(2) SUP_empty Sup_empty empty_Sup)

lemma SUP_eq_Some_iff: "(SUP f\<in>X. f x) = Some t \<longleftrightarrow> (\<exists>f\<in>X. f x \<noteq> None) \<and> (t=Sup {t' | f t'. f\<in>X \<and> f x = Some t' })"
  apply auto
  subgoal 
    by (smt Sup_bot_conv(1) Sup_empty Sup_option_def Sup_pointwise_eq_fun imageE option.distinct(1))
  subgoal 
    unfolding Sup_option_def
    apply (clarsimp split: if_splits)
    apply (fo_rule arg_cong)
    apply (auto simp: Option.these_def)
    apply (metis (mono_tags, lifting) image_iff mem_Collect_eq option.sel)
    apply (metis (mono_tags, lifting) image_iff mem_Collect_eq option.sel)
    done
  subgoal 
    unfolding Sup_option_def
    apply (clarsimp split: if_splits; safe)
    subgoal by (force simp: image_iff)
    apply (fo_rule arg_cong)
    apply (auto simp: Option.these_def)
    apply (metis (mono_tags, lifting) image_iff mem_Collect_eq option.sel)
    done
  done  



lemma Sup_enat_less: "X \<noteq> {} \<Longrightarrow> enat t \<le> Sup X \<longleftrightarrow> (\<exists>x\<in>X. enat t \<le> x)"
  apply rule
  subgoal 
  by (metis Max_in Sup_enat_def finite_enat_bounded linear) 
  subgoal apply auto
    by (simp add: Sup_upper2)
  done


(* 
  This is how implication can be phrased with an Inf operation.
  Generalization from boolean to enat can be explained this way.
 *)

lemma fixes Q P  shows
    "Inf { P x \<le> Q x |x. True}  \<longleftrightarrow> P \<le> Q" unfolding le_fun_def by simp


subsection \<open>continuous\<close>
term sup_continuous  

text \<open>That might by Scott continuity;
      
     https://en.wikipedia.org/wiki/Scott_continuity \<close>


text \<open>There is scott_continuous in Complete_Non_Orders.Fixed_Points\<close>

definition continuous :: "('a::{Sup} \<Rightarrow> 'b::{Sup}) \<Rightarrow> bool"  where
  "continuous f \<longleftrightarrow> (\<forall>A. Sup (f ` A) = f (Sup A) )"


term sup_continuous
thm continuous_at_Sup_mono

lemma "continuous (f::'a::{complete_lattice}\<Rightarrow>'b::{complete_lattice})
         \<longleftrightarrow> (\<forall>A. Inf (f ` A) = f (Inf A) )" (* wrong conjecture *) oops
  
lemma continuousI: "(\<And>A. f (Sup A) = Sup (f ` A)) \<Longrightarrow> continuous f" by (auto simp: continuous_def)
lemma continuousD: "continuous f \<Longrightarrow> f (Sup A) = Sup (f ` A)" by (auto simp: continuous_def)


lemma continuous_Domain: "continuous Domain"
  apply(rule continuousI) by (fact Domain_Union)

lemma continuous_Range: "continuous Range"
  apply(rule continuousI) by (fact Range_Union)
  


subsubsection \<open>combinations are continuous\<close>


lemma continuous_app: "continuous (\<lambda>f. f x)"
  apply(rule continuousI)
  by simp


lemma 
  continuous_fun:
  assumes *: "continuous f" shows "continuous  (\<lambda>X x. (f (X x)))"
  apply(rule continuousI)
  unfolding Sup_fun_def  apply(rule ext) 
  apply(subst continuousD[OF *]) apply(subst image_image) apply(subst image_image) ..



lemma SupD: "Sup A = Some f \<Longrightarrow> A \<noteq> {} \<and> A\<noteq>{None}"
  unfolding Sup_option_def by auto


lemma ffF: "Option.these (case_option None (\<lambda>e. Some (f e)) ` A)
        = f `(Option.these A)"
  unfolding Option.these_def apply (auto split: option.splits)
   apply force   
  using image_iff by fastforce 

lemma zzz: "Option.these A \<noteq> {}
 \<Longrightarrow> Sup ( (\<lambda>x. case x of None \<Rightarrow> None | Some e \<Rightarrow> Some (f e)) ` A)
        = Some (Sup ( f ` Option.these A))"
  apply(subst Sup_option_def)
  apply simp
  apply safe
  subgoal  
    by simp  
  subgoal  
    by (metis SupD aux11 empty_Sup in_these_eq option.simps(5))  
  subgoal apply(subst ffF) by simp 
  done


lemma assumes "continuous f"
  shows "continuous (case_option None (Some o f))" (* TODO: generalize to adding top/bottom element *)
  apply(rule continuousI)
  apply(auto split: option.splits)
  subgoal unfolding Sup_option_def by (auto split: if_splits)
proof -
  fix A   and a :: "'a::{complete_lattice}"
  assume a: "Sup A = Some a"
  with SupD have A: "A \<noteq> {} \<and> A \<noteq> {None}" by auto

  then have a': "a= Sup (Option.these A)"  
    by (metis Sup_option_def a option.inject)

  from A have oA: "Option.these A \<noteq> {}" unfolding Option.these_def by auto

  have *: "\<And>x. Some (f x) = (Some o f) x" by simp
  have "(SUP x\<in>A. case x of None \<Rightarrow> None | Some x \<Rightarrow> (Some \<circ> f) x)
        = (SUP x\<in>A. case x of None \<Rightarrow> None | Some s \<Rightarrow> Some (f s))"
    by(simp only: *) 
  also have "\<dots> = Some (SUP s\<in>(Option.these A). (f s))"
   using oA zzz by metis 
        
  also have "(SUP s\<in>(Option.these A). (f s)) = f a"
    using a' assms(1)[THEN continuousD] by metis 

  finally show "Some (f a) = (SUP x\<in>A. case x of None \<Rightarrow> None | Some x \<Rightarrow> (Some \<circ> f) x)"  by simp
qed  
  
text \<open>a shorter proof\<close>

lemma my_these_def: "Option.these M = {f. Some f \<in> M}"
  unfolding  Option.these_def by (auto intro: rev_image_eqI)  

lemma option_Some_image: 
    "A \<noteq> {} \<Longrightarrow> A \<noteq> {None} \<Longrightarrow> case_option None (Some \<circ> f) ` A \<noteq> {None}" 
  by (metis (mono_tags, hide_lams) comp_apply empty_iff everywhereNone
                  imageI in_these_eq option.exhaust option.simps(5) these_insert_None)

lemma continuous_option: (* or generally, adding a bottom element *)
  assumes *: "continuous f"
  shows "continuous (case_option None (Some o f))"
  apply(rule continuousI)
  unfolding Sup_option_def[unfolded my_these_def] 
  apply (simp add: option_Some_image continuousD[OF *])
  apply rule+
  apply(rule arg_cong[where f=Sup]) 
    by  (auto split: option.splits  intro: rev_image_eqI)   


abbreviation (input) "SUPREMUM S f \<equiv> Sup (f ` S)" 

definition myminus where "myminus x y = (if x=\<infinity> \<and> y=\<infinity> then 0 else x - y)"
lemma "(a::enat) + x \<ge> b  \<longleftrightarrow> x \<ge> myminus b a "
  unfolding myminus_def
  apply(cases a; cases b; cases x) apply auto oops




section "NREST"

datatype ('a,'b) nrest = FAILi | REST "'a \<Rightarrow> ('b::complete_lattice) option"


                   
instantiation nrest :: (type,complete_lattice) complete_lattice
begin

fun less_eq_nrest where
  "_ \<le> FAILi \<longleftrightarrow> True" |
  "(REST a) \<le> (REST b) \<longleftrightarrow> a \<le> b" |
  "FAILi \<le> (REST _) \<longleftrightarrow> False"

fun less_nrest where
  "FAILi < _ \<longleftrightarrow> False" |
  "(REST _) < FAILi \<longleftrightarrow> True" |
  "(REST a) < (REST b) \<longleftrightarrow> a < b"

fun sup_nrest where
  "sup _ FAILi = FAILi" |
  "sup FAILi _ = FAILi" |
  "sup (REST a) (REST b) = REST (\<lambda>x. sup (a x) (b x))"

fun inf_nrest where 
  "inf x FAILi = x" |
  "inf FAILi x = x" |
  "inf (REST a) (REST b) = REST (\<lambda>x. inf (a x) (b x))"

lemma "min (None) (Some (1::enat)) = None" by simp
lemma "max (None) (Some (1::enat)) = Some 1" by eval

definition "Sup X \<equiv> if FAILi\<in>X then FAILi else REST (Sup {f . REST f \<in> X})"
definition "Inf X \<equiv> if \<exists>f. REST f\<in>X then REST (Inf {f . REST f \<in> X}) else FAILi"

definition "bot \<equiv> REST (Map.empty)"
definition "top \<equiv> FAILi"

instance
  apply(intro_classes)
  unfolding Sup_nrest_def  Inf_nrest_def  bot_nrest_def top_nrest_def
  apply (case_tac x, case_tac [!] y, auto) []
  apply (case_tac x, auto) []
  apply (case_tac x, case_tac [!] y, case_tac [!] z, auto) []
  apply (case_tac x, (case_tac [!] y)?, auto) []
  apply (case_tac x, (case_tac [!] y)?, simp_all  add: le_fun_def) []
  apply (case_tac x, (case_tac [!] y)?, auto   simp: le_fun_def) []
  apply (case_tac x, case_tac [!] y, case_tac [!] z, auto   simp: le_fun_def) []
  apply (case_tac x, (case_tac [!] y)?, auto   simp: le_fun_def) []
  apply (case_tac x, (case_tac [!] y)?, auto   simp: le_fun_def) []
  apply (case_tac x, case_tac [!] y, case_tac [!] z, auto   simp: le_fun_def) []
  apply (case_tac x, auto simp add: Inf_lower ) [] 
  apply (case_tac z, fastforce+) [] using le_Inf_iff apply fastforce
  apply (case_tac x, auto simp add: Sup_upper) []
  apply (case_tac z, fastforce+) []  using Sup_le_iff less_eq_nrest.simps(2) apply fastforce
  apply auto []
  apply (auto simp: bot_option_def) []
  done   
end


definition RETURNT :: "'a \<Rightarrow> ('a, 'b::{complete_lattice, zero}) nrest" where
  "RETURNT x \<equiv> REST (\<lambda>e. if e=x then Some 0 else None)"
abbreviation "FAILT \<equiv> top::(_,_) nrest"
abbreviation "SUCCEEDT \<equiv> bot::(_,_) nrest"
abbreviation SPECT where "SPECT \<equiv> REST"


definition "consume M t \<equiv> case M of 
          FAILi \<Rightarrow> FAILT |
          REST X \<Rightarrow> REST (map_option ((+) t) o (X))"


definition "SPEC P t = REST (\<lambda>v. if P v then Some (t v) else None)"


lemma consume_mono:
  fixes  t :: "'a::{ordered_ab_semigroup_add,complete_lattice}"
  shows "t\<le>t' \<Longrightarrow> M \<le> M' \<Longrightarrow> consume M t \<le> consume M' t'"
  unfolding consume_def apply (auto split: nrest.splits )
  unfolding le_fun_def apply auto
  subgoal for m m' x apply(cases "m' x";cases "m x" ) apply auto
     apply (metis less_eq_option_Some_None)        
    by (metis add_mono less_eq_option_Some)  
  done

instantiation unit :: plus
begin
fun plus_unit where "() + () = ()"
instance
  apply(intro_classes) .
end

instantiation unit :: zero
begin
definition zero_unit where "0 = ()"
instance
  apply(intro_classes) .
end
(*
instantiation "fun" :: (type, zero) zero
begin 
fun zero_fun where "zero_fun x = 0"
instance
  apply(intro_classes) .
end
*)

instantiation unit :: ordered_ab_semigroup_add
begin 
instance
  apply(intro_classes) by auto
end 


(*
instantiation "fun" :: (type, ordered_ab_semigroup_add) ordered_ab_semigroup_add
begin 

fun plus_fun where "plus_fun a b x= a x + b x"

term "a::('f::ab_semigroup_add)"

thm ab_semigroup_add.add_commute

instance
  apply(intro_classes)
  subgoal apply (rule ext) by (simp add: add.assoc)
  subgoal apply (rule ext) by (simp add: add.commute)
  subgoal by (simp add: add_left_mono le_fun_def)  
  done
end 
*)
lemma RETURNT_alt: "RETURNT x = REST [x\<mapsto>0]"
  unfolding RETURNT_def by auto

lemma nrest_inequalities[simp]: 
  "FAILT \<noteq> REST X"
  "FAILT \<noteq> SUCCEEDT" 
  "FAILT \<noteq> RETURNT x"
  "SUCCEEDT \<noteq> FAILT"
  "SUCCEEDT \<noteq> RETURNT x"
  "REST X \<noteq> FAILT"
  "RETURNT x \<noteq> FAILT"
  "RETURNT x \<noteq> SUCCEEDT"
  unfolding top_nrest_def bot_nrest_def RETURNT_def  
  apply (auto) by (metis option.distinct(1))+


lemma nrest_more_simps[simp]:
  "SUCCEEDT = REST X \<longleftrightarrow> X=Map.empty" 
  "REST X = SUCCEEDT \<longleftrightarrow> X=Map.empty" 
  "REST X = RETURNT x \<longleftrightarrow> X=[x\<mapsto>0]" 
  "REST X = REST Y \<longleftrightarrow> X=Y"
  "RETURNT x = REST X \<longleftrightarrow> X=[x\<mapsto>0]"
  "RETURNT x = RETURNT y \<longleftrightarrow> x=y" 
  unfolding top_nrest_def bot_nrest_def RETURNT_def apply (auto split: if_splits)
  by (metis option.distinct(1)) 


lemma nres_simp_internals: 
  "REST Map.empty = SUCCEEDT"
   "FAILi = FAILT" 
  unfolding top_nrest_def bot_nrest_def by simp_all


lemma nres_order_simps[simp]:
  "\<not> FAILT \<le> REST M" 
  "REST M \<le> REST M' \<longleftrightarrow> (M\<le>M')"
  by (auto simp: nres_simp_internals[symmetric])   

lemma nres_top_unique[simp]:" FAILT \<le> S' \<longleftrightarrow> S' = FAILT"
  by (rule top_unique) 

lemma FAILT_cases[simp]: "(case FAILT of FAILi \<Rightarrow> P | REST x \<Rightarrow> Q x) = P"
  by (auto simp: nres_simp_internals[symmetric])  

lemma nrest_Sup_FAILT: 
  "Sup X = FAILT \<longleftrightarrow> FAILT \<in> X"
  "FAILT = Sup X \<longleftrightarrow> FAILT \<in> X"
  by (auto simp: nres_simp_internals Sup_nrest_def)


lemma nrest_Sup_SPECT_D: "Sup X = SPECT m \<Longrightarrow> m x = Sup {f x | f. REST f \<in> X}"
  unfolding Sup_nrest_def apply(auto split: if_splits) unfolding Sup_fun_def  
  apply(fo_rule arg_cong) by blast

declare nres_simp_internals(2)[simp]

lemma nrest_noREST_FAILT[simp]: "(\<forall>x2. m \<noteq> REST x2) \<longleftrightarrow> m=FAILT"
  apply (cases m) apply auto done

lemma   no_FAILTE:  
  assumes "g xa \<noteq> FAILT" 
  obtains X where "g xa = REST X" using assms by (cases "g xa") auto


lemma case_prod_refine:
  fixes P Q :: "'a \<Rightarrow> 'b \<Rightarrow> ('c,_) nrest"
  assumes
    "\<And>a b. P a b \<le> Q a b"
  shows
 "(case x of (a,b) \<Rightarrow> P a b) \<le> (case x of (a,b) \<Rightarrow> Q a b)"
  using assms 
  by (simp add: split_def)

lemma case_option_refine: (* obsolete ? *)
  fixes P Q :: "'a \<Rightarrow> 'b \<Rightarrow> ('c,_) nrest"
  assumes
    "PN \<le> QN"
    "\<And>a. PS a \<le> QS a"
  shows
 "(case x of None \<Rightarrow> PN | Some a \<Rightarrow> PS a ) \<le> (case x of None \<Rightarrow> QN | Some a \<Rightarrow> QS a )"
  using assms 
  by (auto split: option.splits)


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

   



section "pointwise reasoning"

named_theorems refine_pw_simps 
ML \<open>
  structure refine_pw_simps = Named_Thms
    ( val name = @{binding refine_pw_simps}
      val description = "Refinement Framework: " ^
        "Simplifier rules for pointwise reasoning" )
\<close>    
  
definition nofailT :: "('a,_) nrest \<Rightarrow> bool" where "nofailT S \<equiv> S\<noteq>FAILT"


lemma nofailT_simps[simp]:
  "nofailT FAILT \<longleftrightarrow> False"
  "nofailT (REST X) \<longleftrightarrow> True"
  "nofailT (RETURNT x) \<longleftrightarrow> True"
  "nofailT SUCCEEDT \<longleftrightarrow> True"
  unfolding nofailT_def
  by (simp_all add: RETURNT_def)


lemma pw_Sup_nofail[refine_pw_simps]: "nofailT (Sup X) \<longleftrightarrow> (\<forall>x\<in>X. nofailT x)"
  apply (cases "Sup X")  
   apply auto unfolding Sup_nrest_def apply (auto split: if_splits)
  apply force unfolding nofailT_def apply(force simp add: nres_simp_internals)
  done

lemma nofailT_SPEC[refine_pw_simps]: "nofailT (SPEC a b)"
  unfolding SPEC_def by auto


subsection "pw reasoning for enat"
(*
definition inresT :: "('a,enat) nrest \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where 
  "inresT S x t \<equiv> REST ([x\<mapsto>enat t]) \<le> S"
*)

locale pointwise_reasoning_defs =
  fixes  lift :: "'cc::{ord,zero} \<Rightarrow> 'ac::{complete_lattice,ord,zero}"
begin
  definition inresT :: "(_,'ac) nrest \<Rightarrow> _ \<Rightarrow> 'cc \<Rightarrow> bool"
    where "inresT S x t \<equiv> REST ([x\<mapsto>lift t]) \<le> S"
end


locale pointwise_reasoning = pointwise_reasoning_defs lift for lift :: "'cc::{ord,zero} \<Rightarrow> 'ac::{complete_lattice,ord,zero}" +
  assumes 
      lift_ord: "\<And>m n. (lift m \<le> lift n) = (m \<le> n)"
    and lift_le_zero: "lift t \<le> 0 \<longleftrightarrow> t \<le> 0"
    and lift_zero: "lift 0 = 0"
    and lift_Sup: "\<lbrakk>X \<noteq> {}; lift t \<le> Sup X\<rbrakk> \<Longrightarrow> \<exists>x\<in>X. lift t \<le> x" 
    and blab: "\<And>t t'. (\<And>tt. lift tt \<le> t \<Longrightarrow> lift tt \<le> t') \<Longrightarrow> t\<le>t'"
    and my_zero_le: "\<And>x. (x::'ac) \<ge> 0" "\<And>x. (x::'cc) \<ge> 0"
    
begin

lemma inresT_alt: "inresT S x t = (case S of FAILi \<Rightarrow> True | REST X \<Rightarrow> (\<exists>t'. X x = Some t' \<and>  lift t\<le>t'))"
  unfolding inresT_def apply(cases S)  
  by (auto dest!: le_funD[where x=x] simp: le_funI less_eq_option_def split: option.splits )

lemma inresT_mono: "inresT S x t \<Longrightarrow> t' \<le> t \<Longrightarrow> inresT S x t'"
  unfolding inresT_def apply(cases S) apply auto
      apply(auto simp: le_fun_def split: if_splits)
  using order_trans lift_ord  
  by (metis less_eq_option_Some)  

lemma inresT_RETURNT[simp]: "inresT (RETURNT x) y t \<longleftrightarrow> t \<le> 0 \<and> y = x"
  by (auto simp: inresT_def RETURNT_def lift_le_zero le_fun_def split: if_splits nrest.splits)

lemma inresT_FAILT[simp]: "inresT FAILT r t"
  by(simp add: inresT_def)

lemma fail_inresT[refine_pw_simps]: "\<not> nofailT M \<Longrightarrow> inresT M x t"
  unfolding nofailT_def by simp



lemma Sup_lift_less: "X \<noteq> {} \<Longrightarrow> lift t \<le> Sup X \<longleftrightarrow> (\<exists>x\<in>X. lift t \<le> x)"
  apply rule
  subgoal 
    apply(rule lift_Sup) by simp_all
  subgoal apply auto
    by (simp add: Sup_upper2)
  done


lemma pw_inresT_Sup[refine_pw_simps]: "inresT (Sup X) r t \<longleftrightarrow> (\<exists>M\<in>X. \<exists>t'\<ge>t.  inresT M r t')"
  apply(rule)
  subgoal (* \<rightarrow> *)
    apply(cases "Sup X")
    subgoal apply  (auto simp: nrest_Sup_FAILT )  
      using inresT_FAILT lift_ord by force
    subgoal 
      apply(auto simp: inresT_alt  Sup_nrest_def split: if_splits)
      apply(auto simp: SUP_eq_Some_iff split: nrest.splits)  
      apply(subst (asm) Sup_lift_less)
       apply auto []  
      apply auto   
      using lift_ord by fastforce
    done
  subgoal (* <- *)
    apply(cases "Sup X")
    subgoal by (auto simp: nrest_Sup_FAILT top_Sup)
    subgoal 
      apply(auto simp: inresT_alt  Sup_nrest_def split: if_splits)
      apply(auto simp: SUP_eq_Some_iff split: nrest.splits)  
      apply(subst Sup_lift_less)
       apply auto []
      apply auto
      using dual_order.trans lift_ord by fastforce
    done                        
  done
         
lemma inresT_REST[simp]:
  "inresT (REST X) x t \<longleftrightarrow> (\<exists>t'\<ge>lift t. X x = Some t')" 
  unfolding inresT_alt 
  by (auto simp: lift_ord )



lemma inres_simps[simp]:
  "inresT FAILT = (\<lambda>_ _. True)" 
  "inresT SUCCEEDT = (\<lambda>_ _ . False)"
  unfolding inresT_def [abs_def]
   apply (auto split: nrest.splits simp add: RETURNT_def bot_nrest_def)   
  by (metis antisym fun_upd_same le_funI less_eq_option_None option.distinct(1)) (* TODO: refactor *)


lemma pw_le_iff: 
  "S \<le> S' \<longleftrightarrow> (nofailT S'\<longrightarrow> (nofailT S \<and> (\<forall>x t. inresT S x t \<longrightarrow> inresT S' x t)))"
  apply (cases S; cases S', simp_all)
  unfolding nofailT_def inresT_def apply (auto split: nrest.splits) 
  subgoal 
    using le_fun_def le_some_optE order.trans  
    by (smt lift_ord)  
  subgoal for s s'
    apply(auto intro!: le_funI simp: less_eq_option_def split: option.splits)
    subgoal using option.distinct(1) lift_zero my_zero_le  
      by metis  
    subgoal premises prems for x t t'
      apply(rule blab)
      using prems(3)[rule_format, of _ x, unfolded prems(4,5), simplified]
      .
    done
  done

lemma pw_eq_iff:
  "S=S' \<longleftrightarrow> (nofailT S = nofailT S' \<and> (\<forall>x t. inresT S x t \<longleftrightarrow> inresT S' x t))"
  apply (rule iffI)
  apply simp
  apply (rule antisym)
  apply (auto simp add: pw_le_iff)
  done

lemma pw_flat_ge_iff: "flat_ge S S' \<longleftrightarrow> 
  (nofailT S) \<longrightarrow> nofailT S' \<and> (\<forall>x t. inresT S x t \<longleftrightarrow> inresT S' x t)"
  apply (simp add: flat_ord_def)
  apply(simp add: pw_eq_iff) apply safe
  by (auto simp add: nofailT_def)   



lemma pw_eqI: 
  assumes "nofailT S = nofailT S'" 
  assumes "\<And>x t. inresT S x t \<longleftrightarrow> inresT S' x t" 
  shows "S=S'"
  using assms by (simp add: pw_eq_iff)


lemma inresT_SPEC[refine_pw_simps]: "inresT (SPEC a b) = (\<lambda>x t. a x \<and>  b x \<ge> lift t)"
  unfolding SPEC_def inresT_REST apply(rule ext) by(auto split: if_splits)    

end


context pointwise_reasoning
begin               

  abbreviation "lift_fun f \<equiv> acostC (\<lambda>x. lift (the_acost f x))"

 
lemma "pointwise_reasoning lift_fun"
  apply unfold_locales 
  subgoal for m n apply(cases m, cases n) by (auto simp: less_eq_acost_def le_fun_def lift_ord )
  subgoal for t apply(cases t) by (auto simp: less_eq_acost_def zero_acost_def le_fun_def lift_le_zero)
  subgoal by (auto simp: zero_acost_def lift_zero)
  subgoal using lift_Sup Sup_acost_def   sorry
  subgoal for t t' apply(cases t; cases t') unfolding less_eq_acost_def apply(auto)
    apply(rule blab)
    subgoal premises prems for ta t'a x tt
      using prems(1)[rule_format, where x=x and tt="ttt"] prems sorry
    done
  subgoal sorry
  subgoal sorry
  done

end

interpretation pointwise_reasoning enat
  apply unfold_locales 
  subgoal by auto
  subgoal by (auto simp: zero_enat_def)
  subgoal by (auto simp: zero_enat_def)
  subgoal by(simp add: Sup_enat_less[symmetric])
  subgoal for t t' apply(cases t'; cases t) apply auto 
    using not_le by blast
   apply auto 
  done 

subsection "pw reasoning for acost" 





end
