theory NREST
  imports
 "HOL-Library.Extended_Nat" "Refine_Monadic.RefineG_Domain"  Refine_Monadic.Refine_Misc  
  "HOL-Library.Monad_Syntax"   "HOL-Library.Groups_Big_Fun"
  Complex_Main 

(* "HOL-Library.Function_Algebras" *)
 "../cost/Abstract_Cost"

begin


declare [[coercion_enabled = false]]


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

definition continuousInf :: "('a::{Inf} \<Rightarrow> 'b::{Inf}) \<Rightarrow> bool"  where
  "continuousInf f \<longleftrightarrow> (\<forall>A. A\<noteq>{} \<longrightarrow> Inf (f ` A) = f (Inf A) )"


term sup_continuous
thm continuous_at_Sup_mono

lemma "continuous (f::'a::{complete_lattice}\<Rightarrow>'b::{complete_lattice})
         \<longleftrightarrow> (\<forall>A. Inf (f ` A) = f (Inf A) )" (* wrong conjecture *) oops
  
lemma continuousI: "(\<And>A. f (Sup A) = Sup (f ` A)) \<Longrightarrow> continuous f" by (auto simp: continuous_def)
lemma continuousD: "continuous f \<Longrightarrow> f (Sup A) = Sup (f ` A)" by (auto simp: continuous_def)


lemma continuousInfI: "(\<And>A. A\<noteq>{} \<Longrightarrow> f (Inf A) = Inf (f ` A)) \<Longrightarrow> continuousInf f" by (auto simp: continuousInf_def)
lemma continuousInfD: "continuousInf f \<Longrightarrow> A\<noteq>{} \<Longrightarrow> f (Inf A) = Inf (f ` A)" by (auto simp: continuousInf_def)


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



lemma 
  continuousInf_fun:
  assumes *: "continuousInf f" shows "continuousInf  (\<lambda>X x. (f (X x)))"
  apply(rule continuousInfI)
  unfolding Inf_fun_def  apply(rule ext) 
  apply(subst continuousInfD[OF *]) subgoal apply simp done
    apply(subst image_image) apply(subst image_image) ..


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

lemma continuous_option': 
  assumes *: "continuous f"
  shows "continuous (case_option None (\<lambda>x. Some (f x)))"
  using continuous_option[OF *, unfolded comp_def]  .


lemma continuousInf_option: (* or generally, adding a bottom element *)
  assumes *: "continuousInf f"
  shows "continuousInf (case_option None (\<lambda>x. Some (f x)))"
  apply(rule continuousInfI)
  unfolding Inf_option_def[unfolded my_these_def] 
  apply (simp add: option_Some_image )
  apply safe
  subgoal by force
  subgoal by(auto split: option.splits) 
  subgoal apply(subst continuousInfD[OF *]) subgoal  
    by (metis Collect_empty_eq Inf_lower \<open>\<And>A. Inf A = (if None \<in> A then None else Some (Inf {f. Some f \<in> A}))\<close> le_some_optE)  
    apply(rule arg_cong[where f=Inf]) 
    by  (auto split: option.splits  intro: rev_image_eqI)  
  done


abbreviation (input) "SUPREMUM S f \<equiv> Sup (f ` S)" 

definition myminus where "myminus x y = (if x=\<infinity> \<and> y=\<infinity> then 0 else x - y)"
lemma "(a::enat) + x \<ge> b  \<longleftrightarrow> x \<ge> myminus b a "
  unfolding myminus_def
  apply(cases a; cases b; cases x) apply auto oops




section "NREST"

datatype ('a,'b) nrest = FAILi | REST "'a \<Rightarrow> ('b::{complete_lattice,monoid_add}) option"
(*abbreviation "REST \<equiv> REST :: ('a \<Rightarrow> ('b::{complete_lattice,monoid_add}) option) \<Rightarrow> _"*)

                   
instantiation nrest :: (type,"{complete_lattice,monoid_add}") complete_lattice
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


definition RETURNT :: "'a \<Rightarrow> ('a, 'b::{complete_lattice, monoid_add}) nrest" where
  "RETURNT x \<equiv> REST (\<lambda>e. if e=x then Some 0 else None)"
abbreviation "FAILT \<equiv> top::(_,_::{complete_lattice, monoid_add}) nrest"
abbreviation "SUCCEEDT \<equiv> bot::(_,_::{complete_lattice, monoid_add}) nrest"
abbreviation SPECT where "SPECT \<equiv> REST"


definition consume where "consume M t \<equiv> case M of 
          FAILi \<Rightarrow> FAILT |
          REST X \<Rightarrow> REST (map_option ((+) t) o (X))"


definition "SPEC P t = REST (\<lambda>v. if P v then Some (t v) else None)"


lemma consume_mono:
  fixes  t :: "'a::{ordered_ab_semigroup_add,complete_lattice,monoid_add}"
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




lemma consume_FAIL:
    "(FAILT = consume m t1 ) \<longleftrightarrow> m = FAILT"
    "(consume m t1 = FAILT ) \<longleftrightarrow> m = FAILT"
  unfolding consume_def by (auto split: nrest.splits)
lemma consume_Fails[simp]: "consume FAILT t = FAILT" by(auto simp: consume_def)




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

locale pointwise_reasoning_defs =
  fixes  lift :: "'cc::{ord,zero} \<Rightarrow> 'ac::{complete_lattice,ord,zero,monoid_add}"
begin
  definition inresT :: "(_,'ac) nrest \<Rightarrow> _ \<Rightarrow> 'cc \<Rightarrow> bool"
    where "inresT S x t \<equiv> REST ([x\<mapsto>lift t]) \<le> S"
end

locale pointwise_reasoning = pointwise_reasoning_defs lift for lift :: "'cc::{ord,zero} \<Rightarrow> 'ac::{complete_lattice,ord,zero,monoid_add}" +
  assumes 
      lift_ord: "\<And>m n. (lift m \<le> lift n) = (m \<le> n)"
    and lift_le_zero: "lift t \<le> 0 \<longleftrightarrow> t \<le> 0"
    and lift_zero: "lift 0 = 0"
    and lift_Sup: "X \<noteq> {} \<Longrightarrow> (\<lambda>x. lift t \<le> x) (Sup X)
                         \<Longrightarrow> Sup ((\<lambda>x. lift t \<le> x)`X)"
    and blab: "\<And>t t'. (\<And>tt. lift tt \<le> t \<Longrightarrow> lift tt \<le> t') \<Longrightarrow> t\<le>t'"
    and my_zero_le: "\<And>x. (x::'ac) \<ge> 0" "\<And>x. (x::'cc) \<ge> 0"    
begin

lemma inresT_alt: "inresT S x t = (case S of FAILi \<Rightarrow> True
                       | REST X \<Rightarrow> (\<exists>t'. X x = Some t' \<and>  lift t\<le>t'))"
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
 

lemma lift_ex_Sup_iff: "(\<exists>x\<in>X. lift t \<le> x) \<longleftrightarrow> Sup ((\<lambda>x. lift t \<le> x)`X)"
  by auto 

lemma Sup_lift_less: "X \<noteq> {} \<Longrightarrow> lift t \<le> Sup X \<longleftrightarrow> (\<exists>x\<in>X. lift t \<le> x)"
  apply rule
  subgoal 
    apply(simp only: lift_ex_Sup_iff)
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

lemma fixes a b :: nat
  shows" (\<forall>t. t \<le> a \<longrightarrow> t \<le> b) \<longleftrightarrow> a \<le> b"  
  by auto


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


subsubsection \<open>Why does lifting to function or acost not work wit pointwise reasoning?\<close>

(* instantiation "fun" :: (type, zero) zero
begin
definition "0 = (\<lambda>_. 0)"
instance by standard
end

experiment
begin

lemma fixes f:: "_ \<Rightarrow> enat"
  shows  "\<lbrakk>X \<noteq> {}\<rbrakk> \<Longrightarrow> f (Sup X) \<le> Sup (f ` X)"
  oops

lemma "pointwise_reasoning (\<lambda>f. (\<lambda>y. enat ((f::'c\<Rightarrow>nat) y) ))"
  apply standard
  prefer 4
  subgoal for X using lift_Sup   unfolding Sup_fun_def    oops
  \<comment> \<open>Just does not hold. consider Sup { [a:=2,b:=1], [a:=1,b:=2]}\<close>

end *)


subsection \<open>pw reasoning for lifting to functions\<close>
(*
definition project_fun :: " 'b \<Rightarrow> ('a,'b\<Rightarrow>_) nrest \<Rightarrow>('a,_) nrest" where
  "project_fun b S  \<equiv> (case S of FAILi \<Rightarrow> FAILi | REST X \<Rightarrow> REST (\<lambda>x. case X x of None \<Rightarrow> None | Some m \<Rightarrow> Some (m b)))"

lemma nofailT_project_fun: "nofailT (project_fun b S) = nofailT S"
  by(auto simp add: nofailT_def project_fun_def split: nrest.splits)

context pointwise_reasoning
begin


lemma inresT_limit_SPECT[refine_pw_simps]: "inresT (project_fun b (SPECT M) ) x t = (\<exists>t'. t' b \<ge> lift t \<and> M x = Some t')"
  unfolding inresT_def project_fun_def by (auto simp: le_fun_def split: option.splits)  

lemma pw_fun_le_project: "(S \<le> S') \<longleftrightarrow> (\<forall>b. (project_fun b S) \<le> (project_fun b S'))"               
  apply(cases S; cases S'; auto simp: project_fun_def le_fun_def less_eq_option_def split: option.splits)
  by force

lemma pw_fun_le_iff': 
  fixes S:: "('a,'b\<Rightarrow>'ac) nrest"
  shows 
  "S \<le> S' \<longleftrightarrow> (\<forall>b. (nofailT (project_fun b S')\<longrightarrow> (nofailT (project_fun b S)
                   \<and> (\<forall> x t. inresT (project_fun b S) x t \<longrightarrow> inresT (project_fun b S') x t))))"
  unfolding pw_fun_le_project pw_le_iff ..


lemma pw_fun_le_iff:  
  "S \<le> S' \<longleftrightarrow> (nofailT S'\<longrightarrow> (nofailT S \<and> (\<forall>b x t. inresT (project_fun b S) x t \<longrightarrow> inresT (project_fun b S') x t)))"
  using pw_fun_le_iff'  by (simp add: nofailT_project_fun)


lemma pw_fun_eq_iff':
  "S=S' \<longleftrightarrow> (\<forall>b. nofailT (project_fun b S) = nofailT (project_fun b S') \<and> (\<forall> x t. inresT (project_fun b S) x t \<longleftrightarrow> inresT (project_fun b S') x t))"
  apply (rule iffI)
  apply simp
  apply (rule antisym)
  apply (auto simp add: pw_fun_le_iff')
  done

lemma pw_fun_eq_iff:
  "S=S' \<longleftrightarrow> (nofailT S = nofailT S' \<and> (\<forall>b x t. inresT (project_fun b S) x t \<longleftrightarrow> inresT (project_fun b S') x t))"
  apply (rule iffI)
  apply simp
  apply (rule antisym)
  apply (auto simp add: pw_fun_le_iff)
  done

lemma pw_fun_flat_ge_iff: "flat_ge S S' \<longleftrightarrow> 
  (nofailT S) \<longrightarrow> nofailT S' \<and> (\<forall>b x t. inresT (project_fun b S) x t \<longleftrightarrow> inresT (project_fun b S') x t)"
  apply (simp add: flat_ord_def)
  apply(simp add: pw_fun_eq_iff) apply safe
  by (auto simp add: nofailT_def)   


lemma pw_fun_eqI: 
  assumes "nofailT S = nofailT S'" 
  assumes "\<And>b x t. inresT (project_fun b S) x t \<longleftrightarrow> inresT (project_fun b S') x t" 
  shows "S=S'"
  using assms by (simp add: pw_fun_eq_iff)

lemma pw_fun_eqI': 
  assumes "\<And>b. nofailT (project_fun b S) = nofailT (project_fun b S')" 
  assumes "\<And>b x t. inresT (project_fun b S) x t \<longleftrightarrow> inresT (project_fun b S') x t" 
  shows "S=S'"
  using assms by (simp add: pw_fun_eq_iff')


end
*)
 
subsection \<open>pw reasoning for lifting to acost\<close>

definition project_acost :: " 'b \<Rightarrow> ('a,(_,_) acost) nrest \<Rightarrow>('a,_) nrest" where
  "project_acost b S  \<equiv> (case S of FAILi \<Rightarrow> FAILi | REST X \<Rightarrow> REST (\<lambda>x. case X x of None \<Rightarrow> None | Some m \<Rightarrow> Some (the_acost m b)))"

lemma nofailT_project_acost[refine_pw_simps]: "nofailT (project_acost b S) = nofailT S"
  by(auto simp add: nofailT_def project_acost_def split: nrest.splits)


lemma nofailT_project_all: "nofailT S \<longleftrightarrow> (\<forall>b. nofailT (project_acost b S))"
  by(auto simp add: nofailT_def project_acost_def split: nrest.splits)

lemma project_acost_SPECT': "project_acost b (SPECT M) = SPECT (\<lambda>x. case_option None (\<lambda>m. Some (the_acost m b)) (M x))"
  unfolding project_acost_def by auto


context pointwise_reasoning
begin


lemma "pointwise_reasoning (\<lambda>x. acostC (\<lambda>y. lift (the_acost x y) ))"
  apply standard
  oops

lemma pw_acost_le_project: "(S \<le> S') \<longleftrightarrow> (\<forall>b. (project_acost b S) \<le> (project_acost b S'))"               
  apply(cases S; cases S')
     apply(auto simp: project_acost_def less_eq_acost_def le_fun_def less_eq_option_def
                split: option.splits)
  by force

lemma pw_acost_le_iff': 
  fixes S:: "('a,('b,'ac) acost) nrest"
  shows 
  "S \<le> S' \<longleftrightarrow> (\<forall>b. (nofailT (project_acost b S')\<longrightarrow> (nofailT (project_acost b S) \<and> (\<forall> x t. inresT (project_acost b S) x t \<longrightarrow> inresT (project_acost b S') x t))))"
  unfolding pw_acost_le_project pw_le_iff .. 


lemma pw_acost_le_iff:   
  "S \<le> S' \<longleftrightarrow> (nofailT S'\<longrightarrow> (nofailT S \<and> (\<forall>b x t. inresT (project_acost b S) x t \<longrightarrow> inresT (project_acost b S') x t)))"
  using pw_acost_le_iff'  by (simp add: nofailT_project_acost)


lemma pw_acost_eq_iff':
  "S=S' \<longleftrightarrow> (\<forall>b. nofailT (project_acost b S) = nofailT (project_acost b S') \<and> (\<forall> x t. inresT (project_acost b S) x t \<longleftrightarrow> inresT (project_acost b S') x t))"
  apply (rule iffI)
  apply simp
  apply (rule antisym)
  apply (auto simp add: pw_acost_le_iff')
  done

lemma pw_acost_eq_iff:
  "S=S' \<longleftrightarrow> (nofailT S = nofailT S' \<and> (\<forall>b x t. inresT (project_acost b S) x t \<longleftrightarrow> inresT (project_acost b S') x t))"
  apply (rule iffI)
  apply simp
  apply (rule antisym)
  apply (auto simp add: pw_acost_le_iff)
  done

lemma pw_acost_flat_ge_iff: "flat_ge S S' \<longleftrightarrow> 
  (nofailT S) \<longrightarrow> nofailT S' \<and> (\<forall>b x t. inresT (project_acost b S) x t \<longleftrightarrow> inresT (project_acost b S') x t)"
  apply (simp add: flat_ord_def)
  apply(simp add: pw_acost_eq_iff) apply safe
  by (auto simp add: nofailT_def)   


lemma pw_acost_eqI: 
  assumes "nofailT S = nofailT S'" 
  assumes "\<And>b x t. inresT (project_acost b S) x t \<longleftrightarrow> inresT (project_acost b S') x t" 
  shows "S=S'"
  using assms by (simp add: pw_acost_eq_iff)

lemma pw_acost_eqI': 
  assumes "\<And>b. nofailT (project_acost b S) = nofailT (project_acost b S')" 
  assumes "\<And>b x t. inresT (project_acost b S) x t \<longleftrightarrow> inresT (project_acost b S') x t" 
  shows "S=S'"
  using assms by (simp add: pw_acost_eq_iff')


end

subsection \<open> le_or_fail \<close>
  definition le_or_fail :: "('a,_) nrest \<Rightarrow> ('a,_) nrest \<Rightarrow> bool" (infix "\<le>\<^sub>n" 50) where
    "m \<le>\<^sub>n m' \<equiv> nofailT m \<longrightarrow> m \<le> m'"

section \<open> Monad Operators \<close>


subsection \<open>bind\<close>

definition bindT :: "('b,'c::{complete_lattice, plus,zero,monoid_add}) nrest \<Rightarrow> ('b \<Rightarrow> ('a,'c) nrest) \<Rightarrow> ('a,'c) nrest" where
  "bindT M f \<equiv> case M of 
  FAILi \<Rightarrow> FAILT |
  REST X \<Rightarrow> Sup { (case f x of FAILi \<Rightarrow> FAILT 
                | REST m2 \<Rightarrow> REST (map_option ((+) t1) o (m2) ))
                    |x t1. X x = Some t1}"

lemma bindT_alt: "bindT M f = (case M of 
  FAILi \<Rightarrow> FAILT | 
  REST X \<Rightarrow> Sup { consume (f x) t1 |x t1. X x = Some t1})"
  unfolding bindT_def consume_def by simp


adhoc_overloading
  Monad_Syntax.bind NREST.bindT


lemma bindT_FAIL[simp]: "bindT FAILT g = FAILT"
  by (auto simp: bindT_def)     

lemma "bindT SUCCEEDT f = SUCCEEDT"
  unfolding bindT_def by(auto split: nrest.split simp add: bot_nrest_def)

subsection \<open>Pointwise reasoning for bindT\<close>

lemma pw_inresT_bindT_aux: "inresT (bindT m f) r t \<longleftrightarrow>
     (nofailT m \<longrightarrow> (\<exists>r' t' t''. inresT m r' t' \<and> inresT (f r') r t'' \<and> t \<le> t' + t''))"
  apply(rule)
  subgoal (* \<rightarrow> *)
    apply(cases m)
    subgoal by auto
    subgoal apply(auto simp: bindT_def pw_inresT_Sup split: nrest.splits) 
      subgoal for M x t' t1 
        apply(rule exI[where x=x])
        apply(cases "f x") apply auto  
        subgoal for x2 z apply(cases t1)
           apply auto
          subgoal for n apply(rule exI[where x=n]) apply auto
            by (smt dual_order.trans enat_ile enat_ord_simps(1) le_add2 linear order_mono_setup.refl plus_enat_simps(1)) 
          subgoal
            by (metis le_add1 zero_enat_def zero_le) 
          done
        done
      subgoal for x t' t1
        apply(rule exI[where x=x]) apply auto
        apply(cases t1) apply auto
        subgoal for n apply(rule exI[where x=n]) apply auto
          apply(rule exI[where x=t]) by auto
        subgoal 
          by presburger
        done 
      done
    done
  subgoal (* <- *)
    apply(cases m)
    subgoal by auto
    subgoal for x2
      apply (auto simp: bindT_def  split: nrest.splits)
      apply(auto simp: pw_inresT_Sup )
      subgoal for r' t' t'a t''
        apply(cases "f r'")
        subgoal apply auto apply(force) done
        subgoal for x2a
          apply(rule exI[where x="REST (map_option ((+) t'a) \<circ> x2a)"]) 
          apply auto
           apply(rule exI[where x=r'])
           apply auto
          using add_mono by fastforce
        done
      done
    done
  done

lemma pw_inresT_bindT[refine_pw_simps]: "inresT (bindT m f) r t \<longleftrightarrow>
     (nofailT m \<longrightarrow> (\<exists>r' t' t''. inresT m r' t' \<and> inresT (f r') r t'' \<and> t = t' + t''))"
  apply (auto simp: pw_inresT_bindT_aux) 
  by (metis (full_types) inresT_mono le_iff_add linear nat_add_left_cancel_le) 


subsection \<open>project_acost on bindT\<close>

lemma continuous_nrest: (* or generally, adding a top element *)
  assumes *: "continuous f"
  shows "continuous (case_nrest FAILi (\<lambda>x. REST (f x)))"
  apply(rule continuousI)
  unfolding Sup_nrest_def apply (auto split: nrest.splits)
  apply(subst continuousD[OF *])
  apply(rule arg_cong[where f=Sup]) 
  apply  (auto split: nrest.splits)
  using image_iff by fastforce



lemma continuousInf_nrest: (* or generally, adding a top element *)
  assumes *: "continuousInf f"
  shows "continuousInf (case_nrest FAILi (\<lambda>x. REST (f x)))"
  apply(rule continuousInfI)
  unfolding Inf_nrest_def apply (auto split: nrest.splits)
  subgoal  
    by force   
  subgoal 
    apply(subst continuousInfD[OF *]) subgoal by auto
    apply(rule arg_cong[where f=Inf]) 
    apply  (auto split: nrest.splits)    
    using image_iff by fastforce
  done

 



lemma continuous_the_acost: "continuous (\<lambda>x. the_acost x b)"
  apply(rule continuousI)  
  by (simp add: Sup_acost_def) 
  

lemma continuous_project_acost: "continuous (project_acost b)"
  unfolding project_acost_def
  by (intro continuous_nrest continuous_fun continuous_option' continuous_the_acost) 


lemma project_acost_Sup: "project_acost b (Sup A) = Sup (project_acost b ` A)"
  using continuous_project_acost[THEN continuousD] .

lemma project_acost_FAIL[simp]: "project_acost b FAILT = FAILT"
  by(auto simp: project_acost_def)

lemma the_acost_plus: "the_acost (t + t') b = the_acost t b + the_acost t' b"
  apply(cases t; cases t') by auto

lemma project_acost_consume[refine_pw_simps]: "project_acost b (consume M t) = consume (project_acost b M) (the_acost t b)"
  unfolding consume_def project_acost_def
  by(auto simp: the_acost_plus split: option.splits nrest.splits)

lemma project_acost_bindT[refine_pw_simps]: "(project_acost b (bindT m f)) = bindT (project_acost b m) (\<lambda>x. project_acost b (f x))"
  unfolding bindT_alt
  apply (auto split: nrest.splits simp: project_acost_Sup project_acost_SPECT') 
  apply(rule arg_cong[where f="Sup"])
  by (auto split: option.splits simp: project_acost_consume[symmetric]) 

subsubsection \<open>NofailT\<close>

lemma pw_bindT_nofailT[refine_pw_simps]: "nofailT (bindT M f) \<longleftrightarrow> (nofailT M \<and> (\<forall>x t. inresT M x t \<longrightarrow> nofailT (f x)))"
  unfolding bindT_def   
  apply (auto elim: no_FAILTE simp: refine_pw_simps  split: nrest.splits )  
   apply force
  by (metis enat_ile le_cases nofailT_def)

lemma g_pw_bindT_nofailT[refine_pw_simps]:
  "nofailT (bindT M f) \<longleftrightarrow> (nofailT M \<and> (\<forall>b x t. inresT (project_acost b M) x t \<longrightarrow> nofailT (f x)))"
  unfolding bindT_def   
  apply (auto elim: no_FAILTE simp: project_acost_SPECT' refine_pw_simps split: nrest.splits option.splits) 
  subgoal by force
  subgoal  
    by (metis enat_0_iff(1) i0_lb nofailT_simps(1))  
  done



section \<open>Monad Rules\<close>


lemma nres_bind_left_identity[simp]:
  fixes f :: "'a \<Rightarrow> ('b,'c::{complete_lattice,zero,monoid_add}) nrest"
  shows  "bindT (RETURNT x) f = f x"
  unfolding bindT_def RETURNT_def 
  apply (auto split: nrest.split)  
  apply(rule ext) apply simp subgoal for x2 xa apply(cases "x2 xa") apply simp by simp
  done


lemma nres_bind_right_identity[simp]:
  fixes M :: "('b,enat) nrest"
  shows "bindT M RETURNT = M"
  by(auto intro!: pw_eqI simp: refine_pw_simps) 

thm refine_pw_simps

lemma the_acost_zero_app: "the_acost 0 b = 0" by(auto simp: zero_acost_def)

lemma project_acost_RETURNT[refine_pw_simps]:
  "project_acost b (RETURNT r) = RETURNT r"
  unfolding RETURNT_def project_acost_def
  by (auto simp: the_acost_zero_app)


lemma f_nres_bind_right_identity[simp]:
  fixes M :: "('b,(_,enat) acost) nrest" 
  shows "bindT M RETURNT = M"
  apply(rule pw_acost_eqI)
  subgoal by(simp add: refine_pw_simps)
  by (auto intro!:   simp: refine_pw_simps project_acost_bindT) 

term consume

lemma g_nres_bind_right_identity[simp]:
  fixes M :: "('b,'c::{complete_lattice,zero,monoid_add}) nrest"
  shows "bindT M RETURNT = M"
proof -
  have kk: "\<And>y g P. (\<lambda>f. f y) ` {g x t1 |x t1. P x t1}
  = {g x t1 y |x t1. P x t1}" by auto
  show ?thesis
  apply (auto simp: bindT_alt Sup_nrest_def consume_FAIL split: nrest.splits)
  apply(auto simp: consume_def RETURNT_def )
  apply(rule ext)  
  apply(rule antisym)
  subgoal apply simp apply(rule Sup_least) unfolding kk by auto  
  subgoal for x2 x apply simp
    apply(cases "x2 x") apply simp
    apply simp
    apply(rule Sup_upper)
    unfolding kk by auto 
  done
qed


lemma nres_bind_assoc[simp]:
  fixes M :: "('a,enat) nrest"
  shows "bindT (bindT M (\<lambda>x. f x)) g = bindT M (%x. bindT (f x) g)"
  apply(auto intro!: pw_eqI simp:  refine_pw_simps)  
  using inresT_mono by fastforce+

thm refine_pw_simps project_acost_bindT

lemma nres_acost_bind_assoc[simp]:
  fixes M :: "('a,(_,enat) acost) nrest"
  shows "bindT (bindT M (\<lambda>x. f x)) g = bindT M (%x. bindT (f x) g)"
  by (auto intro!: pw_acost_eqI' simp: refine_pw_simps)   

thm pw_inresT_Sup
thm refine_pw_simps
 

section \<open>Monotonicity lemmas\<close>


lemma bindT_mono: 
  "m \<le> m' \<Longrightarrow> (\<And>x. (\<exists>t. inresT m x t) \<Longrightarrow> nofailT m' \<Longrightarrow>  f x \<le> f' x)
 \<Longrightarrow> bindT m f \<le> bindT  m' f'"
  apply(auto simp: pw_le_iff refine_pw_simps) 
  by fastforce+      

lemma bindT_acost_mono: 
  fixes m :: "('a, ('b, enat) acost) nrest"
  shows "m \<le> m' \<Longrightarrow> (\<And>x. (\<exists>b t. inresT (project_acost b m) x t) \<Longrightarrow> nofailT m' \<Longrightarrow>  f x \<le> f' x)
 \<Longrightarrow> bindT m f \<le> bindT  m' f'"
  apply(auto simp: pw_acost_le_iff refine_pw_simps nofailT_project_acost) 
  by force+


lemma bindT_mono'[refine_mono]: 
  fixes m :: "('a,enat) nrest"
  shows "m \<le> m' \<Longrightarrow> (\<And>x.   f x \<le> f' x)
 \<Longrightarrow> bindT m f \<le> bindT  m' f'"
  apply(rule bindT_mono) by auto

lemma bindT_acost_mono'[refine_mono]: 
  fixes m :: "('a,(_,enat)acost) nrest"
  shows "m \<le> m' \<Longrightarrow> (\<And>x.   f x \<le> f' x)
 \<Longrightarrow> bindT m f \<le> bindT  m' f'"
  apply(rule bindT_acost_mono) by auto 

 
lemma bindT_flat_mono[refine_mono]:  
  fixes M :: "('a,enat) nrest"
  shows 
  "\<lbrakk> flat_ge M M'; \<And>x. flat_ge (f x) (f' x) \<rbrakk> \<Longrightarrow> flat_ge (bindT M f) (bindT M' f')" 
  apply (auto simp: refine_pw_simps pw_flat_ge_iff) []
  by fastforce+      

lemma g_bindT_flat_mono[refine_mono]:  
  fixes M :: "('a,(_,enat)acost) nrest"
  shows 
  "\<lbrakk> flat_ge M M'; \<And>x. flat_ge (f x) (f' x) \<rbrakk> \<Longrightarrow> flat_ge (bindT M f) (bindT M' f')"
  apply (auto simp: refine_pw_simps pw_acost_flat_ge_iff nofailT_project_acost) 
  by blast+  


subsection \<open>Derived Program Constructs\<close>


subsubsection \<open>Assertion\<close> 

definition "iASSERT ret \<Phi> \<equiv> if \<Phi> then ret () else top"

definition ASSERT where "ASSERT \<equiv> iASSERT RETURNT"

lemma ASSERT_True[simp]: "ASSERT True = RETURNT ()" 
  by (auto simp: ASSERT_def iASSERT_def)
lemma ASSERT_False[simp]: "ASSERT False = FAILT" 
  by (auto simp: ASSERT_def iASSERT_def) 

lemma bind_ASSERT_eq_if:
  fixes m :: "(_,'a::{complete_lattice,zero,monoid_add}) nrest"
  shows "do { ASSERT \<Phi>; m } = (if \<Phi> then m else FAILT)"
  unfolding ASSERT_def iASSERT_def by simp

lemma pw_ASSERT[refine_pw_simps]:
  "nofailT (ASSERT \<Phi>) \<longleftrightarrow> \<Phi>"
  "inresT (ASSERT \<Phi>) x t \<longleftrightarrow> (\<Phi> \<longrightarrow> t = 0)"
  by (cases \<Phi>, simp_all)+

lemma ASSERT_refine:
  shows "(Q \<Longrightarrow> P) \<Longrightarrow> (ASSERT P::(_,enat)nrest) \<le> ASSERT Q"
  by(auto simp: pw_le_iff refine_pw_simps)

lemma ASSERT_leI: 
  fixes M :: "(_,enat) nrest"
  shows "\<Phi> \<Longrightarrow> (\<Phi> \<Longrightarrow> M \<le> M') \<Longrightarrow> ASSERT \<Phi> \<bind> (\<lambda>_. M) \<le> M'"
  by(auto simp: pw_le_iff refine_pw_simps)

lemma ASSERT_leI_f: 
  fixes M :: "(_,(_,enat)acost) nrest"
  shows "\<Phi> \<Longrightarrow> (\<Phi> \<Longrightarrow> M \<le> M') \<Longrightarrow> ASSERT \<Phi> \<bind> (\<lambda>_. M) \<le> M'"
  by(auto simp: pw_le_iff refine_pw_simps)

lemma le_ASSERTI:
  fixes M :: "(_,enat) nrest"
  shows "(\<Phi> \<Longrightarrow> M \<le> M') \<Longrightarrow> M \<le> ASSERT \<Phi> \<bind> (\<lambda>_. M')"
  by(auto simp: pw_le_iff refine_pw_simps)

lemma inresT_ASSERT: "inresT (ASSERT Q \<bind> (\<lambda>_. M)) x ta = (Q \<longrightarrow> inresT M x ta)"
  unfolding ASSERT_def iASSERT_def by auto


lemma nofailT_ASSERT_bind:
  fixes M :: "(_,enat) nrest"
  shows "nofailT (ASSERT P \<bind> (\<lambda>_. M)) \<longleftrightarrow> (P \<and> nofailT M)"
  by(auto simp: pw_bindT_nofailT pw_ASSERT)

subsection \<open>SELECT\<close>


 
definition emb' where "\<And>Q T. emb' Q (T::'a \<Rightarrow> _) = (\<lambda>x. if Q x then Some (T x) else None)"

abbreviation "emb Q t \<equiv> emb' Q (\<lambda>_. t)" 

lemma emb_eq_Some_conv: "\<And>T. emb' Q T x = Some t' \<longleftrightarrow> (t'=T x \<and> Q x)"
  by (auto simp: emb'_def)

lemma emb_le_Some_conv: "\<And>T. Some t' \<le> emb' Q T x \<longleftrightarrow> ( t'\<le>T x \<and> Q x)"
  by (auto simp: emb'_def)


lemma SPEC_REST_emb'_conv: "SPEC P t = REST (emb' P t)"
  unfolding SPEC_def emb'_def by auto


text \<open>Select some value with given property, or \<open>None\<close> if there is none.\<close>  
definition SELECT :: "('a \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> ('a option,'c::{complete_lattice,monoid_add}) nrest"
  where "SELECT P tf \<equiv> if \<exists>x. P x then REST (emb (\<lambda>r. case r of Some p \<Rightarrow> P p | None \<Rightarrow> False) tf)
               else REST [None \<mapsto> tf]"

                    
lemma inresT_SELECT_Some: "inresT (SELECT Q tt) (Some x) t' \<longleftrightarrow> (Q x  \<and> (enat t' \<le> tt))"
  by(auto simp: inresT_alt SELECT_def emb'_def) 

lemma inresT_SELECT_None: "inresT (SELECT Q tt) None t' \<longleftrightarrow> (\<not>(\<exists>x. Q x) \<and> (enat t' \<le> tt))"
  by(auto simp: inresT_alt SELECT_def emb'_def) 

lemma inresT_SELECT[refine_pw_simps]:
 "inresT (SELECT Q tt) x t' \<longleftrightarrow> ((case x of None \<Rightarrow> \<not>(\<exists>x. Q x) | Some x \<Rightarrow> Q x)  \<and> (enat t' \<le> tt))"
  by(auto simp: inresT_alt SELECT_def emb'_def) 


lemma nofailT_SELECT[refine_pw_simps]: "nofailT (SELECT Q tt)"
  by(auto simp: nofailT_def SELECT_def)

lemma s1:
  fixes T::enat
  shows "SELECT P T \<le> (SELECT P T') \<longleftrightarrow> T \<le> T'"
  apply(cases "\<exists>x. P x") 
   apply(auto simp: pw_le_iff refine_pw_simps split: option.splits)
  subgoal 
    by (metis (full_types) enat_ord_code(3) enat_ord_simps(1) lessI not_infinity_eq not_le order_mono_setup.refl) 
  subgoal 
    by (metis (full_types) enat_ord_code(3) enat_ord_simps(1) lessI not_enat_eq not_le order_mono_setup.refl) 
  done
     
lemma s2:
  fixes T::enat
  shows  "SELECT P T \<le> (SELECT P' T) \<longleftrightarrow> (
    (Ex P' \<longrightarrow> Ex P)  \<and> (\<forall>x. P x \<longrightarrow> P' x)) "
  apply(auto simp: pw_le_iff refine_pw_simps split: option.splits)
  subgoal 
    by (metis enat_ile linear)                                          
  subgoal 
    by (metis enat_ile linear) 
  done
 
lemma SELECT_refine:
  fixes T::enat
    
  assumes "\<And>x'. P' x' \<Longrightarrow> \<exists>x. P x"
  assumes "\<And>x. P x \<Longrightarrow>   P' x"
  assumes "T \<le> T'"
  shows "SELECT P T \<le> (SELECT P' T')"
proof -
  have "SELECT P T \<le> SELECT P T'"
    using s1 assms(3) by auto
  also have "\<dots> \<le> SELECT P' T'"
    unfolding s2 apply safe
    using assms(1,2) by auto  
  finally show ?thesis .
qed



section \<open>RECT\<close>

definition "mono2 B \<equiv> flatf_mono_ge B \<and>  mono B"


lemma trimonoD_flatf_ge: "mono2 B \<Longrightarrow> flatf_mono_ge B"
  unfolding mono2_def by auto

lemma trimonoD_mono: "mono2 B \<Longrightarrow> mono B"
  unfolding mono2_def by auto

definition "RECT B x = 
  (if mono2 B then (gfp B x) else (top::'a::complete_lattice))"


thm gfp_eq_flatf_gfp

lemma RECT_flat_gfp_def: "RECT B x = 
  (if mono2 B then (flatf_gfp B x) else (top::'a::complete_lattice))"
  unfolding RECT_def
  by (auto simp: gfp_eq_flatf_gfp[OF trimonoD_flatf_ge trimonoD_mono])

lemma RECT_unfold: "\<lbrakk>mono2 B\<rbrakk> \<Longrightarrow> RECT B = B (RECT B)"
  unfolding RECT_def [abs_def]  
  by (auto dest: trimonoD_mono simp: gfp_unfold[ symmetric])


definition whileT :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('a,_) nrest) \<Rightarrow> 'a \<Rightarrow> ('a,_) nrest" where
  "whileT b c = RECT (\<lambda>whileT s. (if b s then bindT (c s) whileT else RETURNT s))"

lemma trimonoI[refine_mono]: 
  "\<lbrakk>flatf_mono_ge B; mono B\<rbrakk> \<Longrightarrow> mono2 B"
  unfolding mono2_def by auto

lemma [refine_mono]: "(\<And>f g x. (\<And>x. f x \<le> g x) \<Longrightarrow> B f x \<le> B g x) \<Longrightarrow> mono B"
  apply(rule monoI) apply(rule le_funI)
  by (simp add: le_funD)
    
thm refine_mono

lemma whileT_unfold_enat:
  fixes c :: "_\<Rightarrow>(_,enat) nrest"
  shows
   "whileT b c = (\<lambda>s. (if b s then bindT (c s) (whileT b c) else RETURNT s))"
  unfolding whileT_def
  apply(rule RECT_unfold) 
  by ( refine_mono)    

lemma whileT_unfold_acost:
  fixes c :: "_\<Rightarrow>(_,(_,enat)acost) nrest"
  shows
   "whileT b c = (\<lambda>s. (if b s then bindT (c s) (whileT b c) else RETURNT s))"
  unfolding whileT_def
  apply(rule RECT_unfold) 
  by ( refine_mono)    

lemma RECT_mono[refine_mono]:
  assumes [simp]: "mono2 B'"
  assumes LE: "\<And>F x. (B' F x) \<le> (B F x) "
  shows " (RECT B' x) \<le> (RECT B x)"
  unfolding RECT_def
  apply clarsimp  
  by (meson LE gfp_mono le_fun_def)  

lemma whileT_mono: 
  assumes "\<And>x. b x \<Longrightarrow> c x \<le> c' x"
  shows " (whileT b c x) \<le> (whileT b c' x)"
  oops

lemma whileT_mono_enat: 
  fixes c :: "_\<Rightarrow>(_,enat) nrest"
  assumes "\<And>x. b x \<Longrightarrow> c x \<le> c' x"
  shows " (whileT b c x) \<le> (whileT b c' x)"
  unfolding whileT_def apply(rule RECT_mono)
    subgoal by(refine_mono)  
    apply auto apply(rule bindT_mono) using assms by auto

lemma whileT_mono_fenat: 
  fixes c :: "_\<Rightarrow>(_,(_,enat)acost) nrest"
  assumes "\<And>x. b x \<Longrightarrow> c x \<le> c' x"
  shows " (whileT b c x) \<le> (whileT b c' x)"
  unfolding whileT_def apply(rule RECT_mono)
    subgoal by(refine_mono)  
  apply auto apply(rule bindT_acost_mono) using assms by auto


find_theorems RECT
lemma wf_fp_induct:
  assumes fp: "\<And>x. f x = B (f) x"
  assumes wf: "wf R"
  assumes "\<And>x D. \<lbrakk>\<And>y. (y,x)\<in>R \<Longrightarrow> P y (D y)\<rbrakk> \<Longrightarrow> P x (B D x)"
  shows "P x (f x)"
  using wf
  apply induction
  apply (subst fp)
  apply fact  
  done

thm wf_fp_induct[where f="RECT B" and B=B] RECT_unfold


lemma RECT_wf_induct_aux:
  assumes wf: "wf R"
  assumes mono: "mono2 B"
  assumes "(\<And>x D. (\<And>y. (y, x) \<in> R \<Longrightarrow> P y (D y)) \<Longrightarrow> P x (B D x))"
  shows "P x (RECT B x)"
  using wf_fp_induct[where f="RECT B" and B=B] RECT_unfold assms 
     by metis 

theorem RECT_wf_induct[consumes 1]:
  assumes "RECT B x = r"
  assumes "wf R"
    and "mono2 B"
    and "\<And>x D r. (\<And>y r. (y, x) \<in> R \<Longrightarrow> D y = r \<Longrightarrow> P y r) \<Longrightarrow> B D x = r \<Longrightarrow> P x r"
  shows "P x r"
 (* using RECT_wf_induct_aux[where P = "\<lambda>x fx. \<forall>r. fx=r \<longrightarrow> P x fx"] assms by metis *)
  using RECT_wf_induct_aux[where P = "\<lambda>x fx.  P x fx"] assms by metis



definition "monadic_WHILEIT I b f s \<equiv> do {
  RECT (\<lambda>D s. do {
    ASSERT (I s);
    bv \<leftarrow> b s;
    if bv then do {
      s \<leftarrow> f s;
      D s
    } else do {RETURNT s}
  }) s
}"


definition  whileIET :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> _) \<Rightarrow> ('a \<Rightarrow> bool)
                           \<Rightarrow> ('a \<Rightarrow> ('a,'c::{complete_lattice,plus,zero,monoid_add}) nrest)
                           \<Rightarrow> 'a \<Rightarrow> ('a,'c) nrest" where
  "\<And>E c. whileIET I E b c = whileT b c"




subsection \<open>More Pw reasoning setup\<close>


term bindT

declare nofailT_project_acost[refine_pw_simps]

thm refine_pw_simps
lemma pac_ASSERT[refine_pw_simps]:
  "project_acost b (ASSERT P) = (ASSERT P)"
  by (auto simp: zero_acost_def project_acost_def iASSERT_def ASSERT_def RETURNT_def
          split: nrest.splits) 
 
lemma nofailT_consume[refine_pw_simps]: "nofailT (consume M t) \<longleftrightarrow> nofailT M"
  by(auto simp: consume_def split: nrest.splits)
 
definition "satminus a b \<equiv> (if b=\<infinity> then 0 else a - the_enat b)"

lemma satminus_the_acost: "satminus ta (the_acost t b) = 0 \<longleftrightarrow> the_acost t b = \<infinity> \<or> ta \<le> the_enat (the_acost t b)"
  unfolding satminus_def
  by auto

lemma inresT_consume[refine_pw_simps]:
 "inresT (consume M t) x t' \<longleftrightarrow> (inresT M x (satminus t' t))"
  unfolding satminus_def
  apply(cases t)
  apply(auto simp: consume_def  split: nrest.splits )
  subgoal for n x2 z apply(cases z) by auto  
  subgoal for n x2 z apply(cases z) by auto  
  subgoal for x2 z apply(cases z) by auto   
  done

lemma project_acost_SPECT[refine_pw_simps]: 
  "project_acost b (SPECT \<Phi>) = SPECT (\<lambda>x. map_option (\<lambda>m. the_acost m b) (\<Phi> x))"
  unfolding project_acost_def by(auto simp: fun_eq_iff split: nrest.splits option.split)

lemma project_acost_SPECT_map:
  "project_acost b (SPECT [x' \<mapsto> t']) = (SPECT [x' \<mapsto> the_acost t' b])"
  by(auto simp add: project_acost_SPECT) 
 
lemma acost_componentwise_leI:
  fixes \<Phi> :: "'c \<Rightarrow> ('d, enat) acost option"
  assumes "\<Phi> x = Some e"
  shows "(\<And>b. the_acost t b \<le> the_acost e b ) \<Longrightarrow> Some t \<le> \<Phi> x"
  using assms apply(cases "\<Phi> x")
   apply simp
  by (auto simp: less_eq_acost_def)



section "some Monadic Refinement Automation"


ML \<open>
structure Refine = struct

  structure vcg = Named_Thms
    ( val name = @{binding refine_vcg}
      val description = "Refinement Framework: " ^ 
        "Verification condition generation rules (intro)" )

  structure vcg_cons = Named_Thms
    ( val name = @{binding refine_vcg_cons}
      val description = "Refinement Framework: " ^
        "Consequence rules tried by VCG" )

  structure refine0 = Named_Thms
    ( val name = @{binding refine0}
      val description = "Refinement Framework: " ^
        "Refinement rules applied first (intro)" )

  structure refine = Named_Thms
    ( val name = @{binding refine}
      val description = "Refinement Framework: Refinement rules (intro)" )

  structure refine2 = Named_Thms
    ( val name = @{binding refine2}
      val description = "Refinement Framework: " ^
        "Refinement rules 2nd stage (intro)" )

  (* If set to true, the product splitter of refine_rcg is disabled. *)
  val no_prod_split = 
    Attrib.setup_config_bool @{binding refine_no_prod_split} (K false);

  fun rcg_tac add_thms ctxt = 
    let 
      val cons_thms = vcg_cons.get ctxt
      val ref_thms = (refine0.get ctxt 
        @ add_thms @ refine.get ctxt @ refine2.get ctxt);
      val prod_ss = (Splitter.add_split @{thm prod.split} 
        (put_simpset HOL_basic_ss ctxt));
      val prod_simp_tac = 
        if Config.get ctxt no_prod_split then 
          K no_tac
        else
          (simp_tac prod_ss THEN' 
            REPEAT_ALL_NEW (resolve_tac ctxt @{thms impI allI}));
    in
      REPEAT_ALL_NEW_FWD (DETERM o FIRST' [
        resolve_tac ctxt ref_thms,
        resolve_tac ctxt cons_thms THEN' resolve_tac ctxt ref_thms,
        prod_simp_tac
      ])
    end;

  fun post_tac ctxt = REPEAT_ALL_NEW_FWD (FIRST' [
    eq_assume_tac,
    (*match_tac ctxt thms,*)
    SOLVED' (Tagged_Solver.solve_tac ctxt)]) 
         

end;
\<close>
setup \<open>Refine.vcg.setup\<close>
setup \<open>Refine.vcg_cons.setup\<close>
setup \<open>Refine.refine0.setup\<close>
setup \<open>Refine.refine.setup\<close>
setup \<open>Refine.refine2.setup\<close>
(*setup {* Refine.refine_post.setup *}*)

method_setup refine_rcg = 
  \<open>Attrib.thms >> (fn add_thms => fn ctxt => SIMPLE_METHOD' (
    Refine.rcg_tac add_thms ctxt THEN_ALL_NEW_FWD (TRY o Refine.post_tac ctxt)
  ))\<close> 
  "Refinement framework: Generate refinement conditions"     

method_setup refine_vcg = 
  \<open>Attrib.thms >> (fn add_thms => fn ctxt => SIMPLE_METHOD' (
    Refine.rcg_tac (add_thms @ Refine.vcg.get ctxt) ctxt THEN_ALL_NEW_FWD (TRY o Refine.post_tac ctxt)
  ))\<close> 
  "Refinement framework: Generate refinement and verification conditions"


end
