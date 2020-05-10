theory Sep_Generic_Wp
imports 
  "../lib/Sep_Algebra_Add" 
  "../lib/Frame_Infer"
  "../lib/Monad"
  "HOL-Library.Extended_Nat"
begin

section \<open>General VCG Setup for Separation Logic\<close>

(* TODO: Move to Library *)

locale generic_wp_defs =
  fixes wp :: "'c \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool"
begin
  definition "htripleF \<alpha> F P c Q \<equiv> (\<forall>s. (P**F) (\<alpha> s) \<longrightarrow>
      wp c (\<lambda>r s'. (Q r ** F) (\<alpha> s')) s)"

  definition "htriple \<alpha> P c Q \<equiv> (\<forall>F s. (P**F) (\<alpha> s) \<longrightarrow>
      wp c (\<lambda>r s'. (Q r ** F) (\<alpha> s')) s)"

  lemma htriple_as_F_eq: "htriple \<alpha> P c Q = (\<forall>F. htripleF \<alpha> F P c Q)"    
    unfolding htriple_def htripleF_def by blast
      
end


locale generic_wp = generic_wp_defs wp
  for wp :: "'c \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" +
  assumes wp_comm_inf: "inf (wp c Q) (wp c Q') = wp c (inf Q Q')"
begin

  lemma wp_comm_conj: "wp c (\<lambda>r. Q r and Q' r) s \<longleftrightarrow> wp c Q s \<and> wp c Q' s"
    using wp_comm_inf[of c Q Q']
    unfolding inf_fun_def inf_bool_def by metis

  lemma wp_comm_conjI: "\<lbrakk> wp c Q s; wp c Q' s \<rbrakk> \<Longrightarrow> wp c (\<lambda>r s. Q r s \<and> Q' r s) s"
    using wp_comm_inf[of c Q Q']
    unfolding inf_fun_def inf_bool_def by metis


  lemma wp_mono: "Q\<le>Q' \<Longrightarrow> wp c Q \<le> wp c Q'"
    by (metis (mono_tags) antisym_conv le_inf_iff order_refl wp_comm_inf)

  lemma wp_monoI:
    assumes "wp c Q s"
    assumes "\<And>r x. Q r x \<Longrightarrow> Q' r x"
    shows "wp c Q' s"
    using assms wp_mono[of Q Q' c] by auto
      
  lemma htripleI:     
    assumes "\<And>F s. (P**F) (\<alpha> s) \<Longrightarrow> wp c (\<lambda>r s'. (Q r ** F) (\<alpha> s')) s"
    shows "htriple \<alpha> P c Q"
    using assms by (auto simp: htriple_def)

  lemma htripleFI:     
    assumes "\<And>s. (P**F) (\<alpha> s) \<Longrightarrow> wp c (\<lambda>r s'. (Q r ** F) (\<alpha> s')) s"
    shows "htripleF \<alpha> F P c Q"
    using assms by (auto simp: htripleF_def)
        
  lemma htripleD:  
    assumes "htriple \<alpha> P c Q"
    assumes "(P**F) (\<alpha> s)"
    shows "wp c (\<lambda>r s'. (Q r ** F) (\<alpha> s')) s"
    using assms by (auto simp: htriple_def)
    
  lemma htriple_triv[simp, intro!]: "htriple \<alpha> sep_false c Q"
    by (auto simp: htriple_def)
      
  lemma frame_rule: "htriple \<alpha> P c Q \<Longrightarrow> htriple \<alpha> (P ** F) c (\<lambda>r. Q r ** F)"
    unfolding htriple_def
    by (fastforce)

  lemma cons_rule:
    assumes "htriple \<alpha> P c Q"
    assumes "\<And>s. P' s \<Longrightarrow> P s"
    assumes "\<And>r s. Q r s \<Longrightarrow> Q' r s"
    shows "htriple \<alpha> P' c Q'"
    unfolding htriple_def
  proof clarsimp
    fix F s
    assume "(P' \<and>* F) (\<alpha> s)"
    with assms(2) have "(P \<and>* F) (\<alpha> s)"
      using sep_conj_impl1 by blast
    with assms(1) have "wp c (\<lambda>r s'. (Q r \<and>* F) (\<alpha> s')) s"
      unfolding htriple_def by auto
    thus "wp c (\<lambda>r s'. (Q' r \<and>* F) (\<alpha> s')) s"
      apply (rule wp_monoI)
      using assms(3)
      using sep_conj_impl1 by blast
  qed

  lemma cons_post_rule:
    assumes "htriple \<alpha> P c Q"
    assumes "\<And>r s. Q r s \<Longrightarrow> Q' r s"
    shows "htriple \<alpha> P c Q'"
    using cons_rule assms by blast
  
  
  lemma htriple_alt:
    "htriple \<alpha> P c Q 
      = (\<forall>p s f. p##f \<and> \<alpha> s = p + f \<and> P p \<longrightarrow> wp c (\<lambda>r s'. \<exists>p'. p'##f \<and> \<alpha> s'=p'+f \<and> Q r p') s)"
  proof (rule iffI, goal_cases)
    case 1
    show ?case
      using htripleD[OF 1, where F="EXACT x" for x]
        by (auto simp: sep_conj_def)
    
  next
    case 2
    show ?case proof (rule htripleI)
      fix F s 
      assume "(P \<and>* F) (\<alpha> s)"
      then obtain p f where "p##f" "P p" "F f" "\<alpha> s = p+f"
        by (blast elim: sep_conjE)
      with 2 have "wp c (\<lambda>r s'. \<exists>p'. p' ## f \<and> \<alpha> s' = p' + f \<and> Q r p') s" by blast
      then show "wp c (\<lambda>r s'. (Q r \<and>* F) (\<alpha> s')) s"
        apply (rule wp_monoI)
        using \<open>F f\<close> by (auto intro: sep_conjI)
    qed
  qed
  
  lemma htripleI': 
    assumes "\<And>p s f. \<lbrakk> p##f; \<alpha> s = p + f; P p\<rbrakk> \<Longrightarrow> wp c (\<lambda>r s'. \<exists>p'. p'##f \<and> \<alpha> s'=p'+f \<and> Q r p') s"
    shows "htriple \<alpha> P c Q"
    using assms by (auto simp: htriple_alt)

  lemma htripleD': 
    assumes "htriple \<alpha> P c Q"
    assumes "p##f" "\<alpha> s = p + f" "P p"
    shows "wp c (\<lambda>r s'. \<exists>p'. p'##f \<and> \<alpha> s'=p'+f \<and> Q r p') s"
    using assms by (auto simp: htriple_alt)
        
    
    
  lemma htriple_extract_pre_pure: 
    "htriple \<alpha> (\<up>\<Phi>**P) c Q \<longleftrightarrow> \<Phi> \<longrightarrow> htriple \<alpha> P c Q"  
    by (cases \<Phi>) (auto simp: sep_algebra_simps)
    
  (*
  lemma htriple_extract_pre_EXS: 
    assumes "\<And>x s. \<Phi> x \<Longrightarrow> P s \<Longrightarrow> f x ## s"
    shows "htriple \<alpha> (EXS x. \<up>\<Phi> x ** EXACT (f x) ** P) c Q \<longleftrightarrow> (\<exists>x. \<Phi> x \<and> htriple \<alpha> (EXACT (f x) ** P) c Q)"
    apply rule
  *)  
    
  thm htripleD
  
  thm option.simps
  
  lemma sv_htripleD:
    assumes "htriple \<alpha> P c Q"
    assumes "(P**F) (\<alpha> s)"
    assumes "\<And>r s. (Q r ** F) (\<alpha> s) \<Longrightarrow> Q' r s"
    shows "wp c Q' s"
    using assms 
    by (force simp: htriple_def intro: wp_monoI)
  
  lemma sv_htripleFD:
    assumes "htripleF \<alpha> F P c Q"
    assumes "(P**F) (\<alpha> s)"
    assumes "\<And>r s. (Q r ** F) (\<alpha> s) \<Longrightarrow> Q' r s"
    shows "wp c Q' s"
    using assms 
    by (force simp: htripleF_def intro: wp_monoI)
    
    
  lemma htriple_conj_pure:
    fixes \<alpha>
    assumes "htriple \<alpha> P c Q"
    assumes "htriple \<alpha> P c (\<lambda>r. \<up>\<Phi> r ** sep_true)"
    shows "htriple \<alpha> P c (\<lambda>r. \<up>\<Phi> r ** Q r)"
  proof (rule htripleI)  
    fix F s
    assume "(P**F) (\<alpha> s)"
    from wp_comm_conjI[OF assms[THEN htripleD,OF this]]
    show "wp c (\<lambda>r s'. ((\<up>\<Phi> r \<and>* Q r) \<and>* F) (\<alpha> s')) s"
      apply (rule wp_monoI)
      using and_pure_true unfolding entails_def by blast
      
  qed    
    
end

experiment begin
  text \<open>Precondition defined by semantics relation:
    \<^item> \<open>T c s\<close> command terminates in state \<open>s\<close>
    \<^item> \<open>R c s r s'\<close> command yields result \<open>r\<close> and new state \<open>s'\<close>
  \<close>
  
  definition "my_wp T (R::_ \<Rightarrow> 's\<Rightarrow>_\<Rightarrow>'s\<Rightarrow>bool) c Q s \<equiv> T c s \<and> (\<forall>r s'. R c s r s' \<longrightarrow> Q r s')"
  

  interpretation generic_wp "my_wp T R"  
    apply unfold_locales
    unfolding my_wp_def
    by auto
  

end




definition STATE :: "('s \<Rightarrow> 'a::sep_algebra) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" 
  where "STATE \<alpha> P s \<equiv> P (\<alpha> s)"

lemma STATE_assn_cong[fri_extract_congs]: "P\<equiv>P' \<Longrightarrow> STATE \<alpha> P s \<equiv> STATE \<alpha> P' s" by simp
  
lemma STATE_extract[vcg_normalize_simps]:
  "STATE \<alpha> (\<up>\<Phi>) h \<longleftrightarrow> \<Phi> \<and> STATE \<alpha> \<box> h"
  "STATE \<alpha> (\<up>\<Phi> ** P) h \<longleftrightarrow> \<Phi> \<and> STATE \<alpha> P h"
  "STATE \<alpha> (EXS x. Q x) h \<longleftrightarrow> (\<exists>x. STATE \<alpha> (Q x) h)"
  "STATE \<alpha> (\<lambda>_. False) h \<longleftrightarrow> False"
  "STATE \<alpha> ((\<lambda>_. False) ** P) h \<longleftrightarrow> False"
  by (auto simp: STATE_def sep_algebra_simps pred_lift_extract_simps)
 

definition POSTCOND :: "('s \<Rightarrow> 'a::sep_algebra) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" 
  where [vcg_tag_defs]: "POSTCOND \<alpha> \<equiv> STATE \<alpha>"
  
lemma POSTCONDI:
  "STATE \<alpha> A h \<Longrightarrow> POSTCOND \<alpha> A h"
  by (auto simp add: POSTCOND_def)
lemma POSTCOND_cong[vcg_normalize_congs]: "POSTCOND \<alpha> A = POSTCOND \<alpha> A" ..

lemma POSTCOND_triv_simps[vcg_normalize_simps]:
  "POSTCOND \<alpha> sep_true h"
  "\<not>POSTCOND \<alpha> sep_false h"
  unfolding POSTCOND_def STATE_def by auto
  
lemma start_entailsE:
  assumes "STATE \<alpha> P h"
  assumes "ENTAILS P P'"
  shows "STATE \<alpha> P' h"
  using assms unfolding STATE_def ENTAILS_def entails_def
  by auto

declaration \<open>
  K (Basic_VCG.add_xformer (@{thms POSTCONDI},@{binding postcond_xformer},
    fn ctxt => eresolve_tac ctxt @{thms start_entailsE}
  ))
\<close>


named_theorems htriple_vcg_intros
named_theorems htriple_vcg_intro_congs
definition [vcg_tag_defs]: "DECOMP_HTRIPLE \<phi> \<equiv> \<phi>"
lemma DECOMP_HTRIPLEI: "\<phi> \<Longrightarrow> DECOMP_HTRIPLE \<phi>" unfolding vcg_tag_defs by simp

 
context generic_wp begin
  thm frame_rule
  thm cons_rule  
    
  lemma htriple_vcg_frame_erule[vcg_frame_erules]:
    assumes S: "STATE \<alpha> P' s"
    assumes F: "PRECOND (FRAME P' P F)"
    assumes HT: "htriple \<alpha> P c Q"  
    assumes P: "\<And>r s. STATE \<alpha> (Q r ** F) s \<Longrightarrow> PRECOND (EXTRACT (Q' r s))"
    shows "wp c Q' s"
  proof -
    from S F have "(P \<and>* F) (\<alpha> s)"
      unfolding vcg_tag_defs
      by (metis (no_types) FRAME_def entails_def STATE_def)
    with P show ?thesis
      unfolding vcg_tag_defs
      by (metis (no_types) STATE_def sv_htripleD[OF HT])
      
  qed

  lemma htripleF_vcg_frame_erule[vcg_frame_erules]:
    assumes S: "STATE \<alpha> P' s"
    assumes F: "PRECOND (FRAME P' P F)"
    assumes HT: "htripleF \<alpha> F P c Q"  
    assumes P: "\<And>r s. STATE \<alpha> (Q r ** F) s \<Longrightarrow> PRECOND (EXTRACT (Q' r s))"
    shows "wp c Q' s"
  proof -
    from S F have "(P \<and>* F) (\<alpha> s)"
      unfolding vcg_tag_defs
      by (metis (no_types) FRAME_def entails_def STATE_def)
    with P show ?thesis
      unfolding vcg_tag_defs
      by (metis (no_types) STATE_def sv_htripleFD[OF HT])
      
  qed
  
  
  
  lemma htriple_vcgI': 
    assumes "\<And>F s. STATE \<alpha> (P**F) s \<Longrightarrow> wp c (\<lambda>r. POSTCOND \<alpha> (Q r ** F)) s"
    shows "htriple \<alpha> P c Q"
    apply (rule htripleI)
    using assms unfolding vcg_tag_defs STATE_def .
  
  lemma htriple_vcgI[htriple_vcg_intros]: 
    assumes "\<And>F s. STATE \<alpha> (P**F) s \<Longrightarrow> EXTRACT (wp c (\<lambda>r. POSTCOND \<alpha> (Q r ** F)) s)"
    shows "htriple \<alpha> P c Q"
    apply (rule htripleI)
    using assms unfolding vcg_tag_defs STATE_def .

  lemma htripleF_vcgI[htriple_vcg_intros]: 
    assumes "\<And>s. STATE \<alpha> (P**F) s \<Longrightarrow> EXTRACT (wp c (\<lambda>r. POSTCOND \<alpha> (Q r ** F)) s)"
    shows "htripleF \<alpha> F P c Q"
    apply (rule htripleFI)
    using assms unfolding vcg_tag_defs STATE_def .
    
      
  lemma htriple_decompI[vcg_decomp_rules]: 
    "DECOMP_HTRIPLE (htriple \<alpha> P c Q) \<Longrightarrow> htriple \<alpha> P c Q"
    "DECOMP_HTRIPLE (htripleF \<alpha> F P c Q) \<Longrightarrow> htripleF \<alpha> F P c Q"
    unfolding vcg_tag_defs by auto

  lemma htriple_assn_cong[htriple_vcg_intro_congs]: 
    "P\<equiv>P' \<Longrightarrow> Q\<equiv>Q' \<Longrightarrow>  htriple \<alpha> P c Q \<equiv> htriple \<alpha> P' c Q'" by simp

  lemma htripleF_assn_cong[htriple_vcg_intro_congs]: 
    "P\<equiv>P' \<Longrightarrow> Q\<equiv>Q' \<Longrightarrow>  htripleF \<alpha> F P c Q \<equiv> htripleF \<alpha> F P' c Q'" by simp
            
  lemma htriple_ent_pre:
    "P\<turnstile>P' \<Longrightarrow> htriple \<alpha> P' c Q \<Longrightarrow> htriple \<alpha> P c Q"
    unfolding entails_def
    apply (erule cons_rule) by blast+
    
  lemma htriple_ent_post:
    "\<lbrakk>\<And>r. Q r \<turnstile> Q' r\<rbrakk> \<Longrightarrow> htriple \<alpha> P c Q \<Longrightarrow> htriple \<alpha> P c Q'"
    unfolding entails_def
    apply (erule cons_rule) by blast+
   
  lemma htriple_pure_preI: "\<lbrakk>pure_part P \<Longrightarrow> htriple \<alpha> P c Q\<rbrakk> \<Longrightarrow> htriple \<alpha> P c Q"  
    by (meson htriple_def pure_partI sep_conjE)
    
     
end


declaration \<open>
  K (Basic_VCG.add_xformer (@{thms DECOMP_HTRIPLEI},@{binding decomp_htriple_xformer},
    fn ctxt => 
      (full_simp_tac (put_simpset HOL_basic_ss ctxt 
        addsimps (Named_Theorems.get ctxt @{named_theorems vcg_tag_defs})
        |> fold Simplifier.add_cong (Named_Theorems.get ctxt @{named_theorems htriple_vcg_intro_congs})
      ))
      THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems htriple_vcg_intros})
  ))
\<close>



section \<open>a General framework for abstract and concrete costs\<close>

text \<open>This locale fixes a type of concrete costs \<open>'cc\<close> which is used in \<open>mres\<close> and a type for
      abstract costs \<open>'ca\<close> which should be used in the separation logic with (resource) credits. 
      There is some invariant that has to hold between the credits currently available "on the heap"
      and the resources spent in the computation, \<open>I\<close> captures that.
      Also it needs to be possible to deduct the resources used by the computation from the credits,
      this is captured by \<open>minus\<close>.
      \<close>

locale cost_framework =
  fixes
    I :: "'cc::{monoid_add} \<Rightarrow> 'ca \<Rightarrow> bool"
  and minus :: "'ca \<Rightarrow> 'cc \<Rightarrow> 'ca" \<comment> \<open>takes abstract credits, and returns the effect of consuming
                                        the concrete resources\<close>
assumes minus_0: "\<And>y. minus y 0 = y"
  and I_0: "I 0 cr"
  and minus_minus_add: "\<And>a b c. minus (minus a b) c = minus a (b + c)"
  \<comment> \<open>TODO: maybe some of these are redundant\<close>
  and I1: "\<And>a b c. I (a + b) c \<Longrightarrow> I b (minus c a)"
  and I2: "\<And>a b c. I (a + b) c \<Longrightarrow> I a c"
  and I3:  "\<And>a b c. I a (minus c b) \<Longrightarrow> I b c \<Longrightarrow> I (b + a) c"
begin

  definition  wp :: "('d, 'e, _, 'a, 'f) M \<Rightarrow> _ \<Rightarrow> _" where
    "wp m Q \<equiv> \<lambda>(s,cr). mwp (run m s) bot bot bot (\<lambda>r c s. Q r (s,minus cr c) \<and> I c cr)"


  interpretation generic_wp wp
    apply unfold_locales
    unfolding wp_def fun_eq_iff inf_fun_def inf_bool_def mwp_def
    by (auto split: mres.split)


  lemma wp_return: "wp (return x) Q s \<longleftrightarrow> Q x s"
    by (auto simp: wp_def run_simps minus_0 I_0)

  lemma wp_fail: "\<not> wp (fail x) Q s"
    by (auto simp: wp_def run_simps)

  lemma wp_fcheck: "wp (fcheck e \<Phi>) Q s \<longleftrightarrow> \<Phi> \<and> Q () s"
    by (auto simp: wp_def run_simps minus_0 I_0 split: if_splits)

  (* TODO: refactor that proof, should not need to unfold mwp_def at that stage *)
  lemma wp_bind: "wp (m\<bind>f) Q s = wp m (\<lambda>x. wp (f x) Q) s"
    apply (auto simp: wp_def run_simps split: prod.splits)
    unfolding mwp_def apply (auto split: mres.splits simp add: minus_minus_add)
    subgoal
      by (metis I1)
    subgoal
      by (metis I2)
    subgoal
      by (metis I3)
    done
end

interpretation nat: cost_framework "\<lambda>(c::nat) (cr::nat). cr-c+c=cr" "(-)"
  apply standard
  by auto

interpretation int: cost_framework "\<lambda>(c::int) (cr::int). True" "(-)"
  apply standard
  by auto




section \<open>Setup for mres-Monad\<close>

  lemma "cr-c+c=(cr::nat) \<longleftrightarrow> cr\<ge>c" by auto
  lemma "cr-c+c=(cr::int) \<longleftrightarrow> True" by auto


  lemma enat_diff_diff: "a - enat b - enat c = a - enat (b + c)"
    apply(cases a) by auto
  lemma enat_aux1: "c - enat (a + b) + enat (a + b) = c \<Longrightarrow> c - enat a + enat a = c"
    apply(cases c) by auto

  interpretation cost_framework "\<lambda>(c::nat) (cr::enat). cr-c+c=cr" "(-)"
    apply standard
         apply (auto simp: zero_enat_def)
    subgoal
      by (metis enat_diff_diff)
    subgoal
      by (metis enat_diff_diff add_diff_assoc_enat add_diff_cancel_left' enat_ord_simps(1)
                idiff_enat_enat le_add_same_cancel1 zero_le)
    subgoal
      by (metis enat_aux1)
    subgoal
      by (metis enat_diff_diff add.assoc add.commute plus_enat_simps(1))
    done

  lemma enat_nat_I_conv: "cr - enat c + enat c = cr \<longleftrightarrow> cr \<ge> c"
    by (cases cr; cases c; auto)

  (* Definition for presentation *)
  lemma natenat_alt: "wp m Q \<equiv> \<lambda>(s, cr). mwp (run m s) bot bot bot (\<lambda>r c s. Q r (s, cr - enat c) \<and> cr \<ge> c)"
    unfolding wp_def apply(subst enat_nat_I_conv) .

  (* Definition for presentation in paper *)
  lemma "wp m Q (s,cr::nat) = (\<exists>r c s'. run m s = SUCC r c s' \<and> Q r (s', cr-c) \<and> c\<le>cr )"
    unfolding wp_def mwp_def by (fastforce split: mres.splits)

  interpretation generic_wp wp 
    apply unfold_locales 
    unfolding wp_def fun_eq_iff inf_fun_def inf_bool_def mwp_def
    by (auto split: mres.split)

  declare wp_return[vcg_normalize_simps]

  declare wp_fail[vcg_normalize_simps]

  declare wp_fcheck[vcg_normalize_simps]

  declare wp_bind[vcg_normalize_simps]

  thm vcg_normalize_simps

  
section \<open>experiment: Hoare-triple without Time\<close>  
 
  
  (* TODO: Move, to Sep_Lift *)  
  text \<open>Lifting Assertions over Product\<close>
  definition FST :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'b::zero \<Rightarrow> bool" 
    where "FST P \<equiv> \<lambda>(a,b). P a \<and> b=0"
  
  definition SND :: "('b \<Rightarrow> bool) \<Rightarrow> 'a::zero \<times> 'b \<Rightarrow> bool" 
    where "SND P \<equiv> \<lambda>(a,b). a=0 \<and> P b"
    
  
  lemma FST_project_frame: "(FST P \<and>* F) (a, b) \<longleftrightarrow> (P ** (\<lambda>a. F (a,b))) a"
    unfolding sep_conj_def
    by (force simp add: sep_algebra_simps FST_def) 
    
  lemma FST_conj_conv: "(FST P ** FST Q) = FST (P**Q)"  
    unfolding sep_conj_def
    by (force simp add: sep_algebra_simps FST_def) 
    
  lemma FST_apply[sep_algebra_simps]: "FST P (a,b) \<longleftrightarrow> P a \<and> b=0"
    unfolding FST_def by auto
    
      
  (* TODO: Move *)
  instantiation enat :: stronger_sep_algebra begin
    definition "(_::enat) ## _ \<equiv> True"
  
    instance
      apply standard
      apply (simp_all add: sep_disj_enat_def)
      done
      
  end
  
  text \<open>Weakest precondition without time\<close>
  definition "wpn m Q s \<equiv> mwp (run m s) bot bot bot (\<lambda>r c s'. c=0 \<and> Q r s')"
  
  lemma wpn_def': "wpn m Q s = (\<exists>r s'. run m s = SUCC r 0 s' \<and> Q r s')"
    unfolding wpn_def mwp_def
    by (auto split: mres.split)
  
  lemma wpn_alt: "wpn m Q s = wp m (FST o Q) (s,0)"
    unfolding wp_def wpn_def mwp_def
    by (auto split: mres.split simp: zero_enat_def FST_def)
  
  interpretation notime: generic_wp wpn  
    apply unfold_locales 
    unfolding wpn_def fun_eq_iff inf_fun_def inf_bool_def mwp_def
    by (auto split: mres.split)

        
  lemma wpn_return[vcg_normalize_simps]: "wpn (return x) Q s \<longleftrightarrow> Q x s"
    by (auto simp: wpn_def run_simps)

  lemma wpn_fail[vcg_normalize_simps]: "\<not> wpn (fail x) Q s"
    by (auto simp: wpn_def run_simps)

  lemma wpn_fcheck[vcg_normalize_simps]: "wpn (fcheck e \<Phi>) Q s \<longleftrightarrow> \<Phi> \<and> Q () s"
    by (auto simp: wpn_def run_simps split: if_splits)

  (* TODO: refactor that proof, should not need to unfold mwp_def at that stage *)
  (* TODO: Intuitively, want equality here: BUT, equality only holds if costs cannot be negative! *)
  lemma wpn_bind[vcg_decomp_rules]: "wpn m (\<lambda>x. wpn (f x) Q) s \<Longrightarrow> wpn (m\<bind>f) Q s"
    apply (auto simp: wpn_def[abs_def] run_simps split: prod.splits)
    unfolding mwp_def 
    by (auto 
      split: mres.splits 
      simp add: minus_minus_add dest!: addcost_SUCC_D)
  
  (*      
  lemma wpn_bind: "wpn (m\<bind>f) Q s = wpn m (\<lambda>x. wpn (f x) Q) s"
    apply (auto simp: wpn_def run_simps split: prod.splits)
    unfolding mwp_def 
    apply (auto 
      split: mres.splits 
      simp add: minus_minus_add dest!: addcost_SUCC_D)
    xxx. ctd here: need positive costs, 
      otherwise negatove+positive can cancel out.
      
  *)
  
  
  lemma notime_return_rule: "notime.htriple \<alpha> P (return x) (\<lambda>r. \<up>(r=x)**P)" for \<alpha>
    by vcg
  
      
  text \<open>Transfer of Hoare-Triples\<close>
  
  lemma wp_time_mono: "wp m Q (s,c) \<Longrightarrow> wp m (\<lambda>r (s',c'). \<exists>cc'. c'=cc'+d \<and> Q r (s',cc')) (s,c+d)"
    unfolding wp_def mwp_def
    apply (auto simp add: algebra_simps sep_algebra_simps SND_def sep_conj_def split: mres.split)
    apply (metis add.commute add_diff_assoc_enat enat_nat_I_conv)
    by (metis ab_semigroup_add_class.add_ac(1) add_diff_cancel_enat enat.distinct(1))
      
  lemma notime_to_htriple:
    fixes c :: "('a, 'b, nat, 'd, 'e) M"
    assumes H: "notime.htriple \<alpha> P c Q"
    shows "htriple (\<lambda>(s,cr). (\<alpha> s, cr)) (FST P) c (FST o Q)"
    apply (rule htripleI)
    apply clarify
  proof -
    fix F a and b :: enat
    assume "(FST P \<and>* F) (\<alpha> a, b)"
    hence "(P ** (\<lambda>a. F (a,b))) (\<alpha> a)"
      by (simp add: sep_algebra_simps FST_project_frame)
    from notime.htripleD[OF H this] have "wpn c (\<lambda>r s'. (Q r \<and>* (\<lambda>a. F (a, b))) (\<alpha> s')) a" .
    then have "wp c (\<lambda>x (a, ba). (Q x \<and>* (\<lambda>a. F (a, b))) (\<alpha> a) \<and> ba = 0) (a, 0)"
      unfolding wpn_alt FST_def comp_def by simp
    from wp_time_mono[OF this, of b] have "wp c (\<lambda>r (s', c'). c' = b \<and> (Q r \<and>* (\<lambda>a. F (a, b))) (\<alpha> s')) (a, b)"
      by simp
    then show "wp c (\<lambda>r s'. ((FST \<circ> Q) r \<and>* F) (case s' of (s, x) \<Rightarrow> (\<alpha> s, x))) (a, b)"  
      apply (rule wp_monoI)
      apply (auto simp: FST_project_frame)
      done
  qed  

  lemma htriple_to_notime:
    assumes H: "htriple (\<lambda>(s,cr). (\<alpha> s, cr)) (FST P) c (FST o Q)"
    shows "notime.htriple \<alpha> P c Q"
    apply (rule notime.htripleI)
    unfolding wpn_alt
  proof -  
    fix F s
    assume A: "(P \<and>* F) (\<alpha> s)"
    
    show "wp c (FST \<circ> (\<lambda>r s'. (Q r \<and>* F) (\<alpha> s'))) (s, 0)"
      apply (rule wp_monoI)
      apply (rule htripleD[OF H, where F="FST F"])
      apply (auto simp: FST_conj_conv sep_algebra_simps A)
      done
  qed      
  
  lemma notime_htriple_eq: "notime.htriple \<alpha> P c Q = htriple (\<lambda>(s,cr). (\<alpha> s, cr)) (FST P) c (FST o Q)"
    by (blast intro: notime_to_htriple htriple_to_notime)
  

  definition "wlp c Q s \<equiv> mwp (run c s) top top top (\<lambda>r c s. Q r s)"
  lemma wlp_true[simp, intro!]:
    "wlp c (\<lambda>_ _. True) s"
    "wlp c top s"
    by (auto simp: wlp_def mwp_def split: mres.splits)
    
  lemma wlp_return[simp]: "wlp (return x) Q s = Q x s"
    by (auto simp: wlp_def run_simps)
        
  
section \<open>experiment: cost type for Space\<close>


datatype space_cost = Space_Cost nat nat (* highest point,  how far below that mark at the moment *)

fun max_cost where "max_cost (Space_Cost h _) = h"
fun curr_cost where "curr_cost (Space_Cost h c) = int h - int c"

definition "new_h m1 c1 m2 c2 \<equiv> (max (int m1) (((int m1 - int c1)+int m2)))"
definition "new_c m1 c1 m2 c2 \<equiv> (new_h m1 c1 m2 c2 - ((int m1 - int c1)+(int m2 - int c2)))"

lemma new_h_nonneg: "new_h m1 c1 m2 c2 \<ge> 0"
  by (auto simp: new_h_def)

lemma new_c_nonneg: "new_c m1 c1 m2 c2 \<ge> 0"
  by (auto simp: new_c_def new_h_def)

instantiation space_cost :: plus
begin
  lemma fixes m1 c1 m2 c2 :: nat
    shows "(max (int m1) (((int m1 - int c1)+int m2))) - ((int m1 - int c1)+(int m2 - int c2)) \<ge> 0"
    by auto

lemma "new_h m1 c1 m2 c2 - ((int m1 - int c1)+(int m2 - int c2)) \<ge> 0"
  by (auto simp: new_h_def)

  fun plus_space_cost :: "space_cost \<Rightarrow> space_cost \<Rightarrow> space_cost" where
    "plus_space_cost (Space_Cost m1 c1) (Space_Cost m2 c2) =
             Space_Cost (nat (new_h m1 c1 m2 c2)) (nat (new_c m1 c1 m2 c2))"

  instance ..
end


instantiation space_cost :: monoid_add
begin
  definition zero_space_cost :: space_cost where "zero_space_cost = Space_Cost 0 0"

  instance
    apply standard
    subgoal for a b c
      apply(cases a; cases b; cases c)
      apply (simp add: new_h_nonneg new_c_nonneg) apply safe
      subgoal for m1 c1 m2 c2 m3 c3
        apply(subst (2) new_h_def)
        apply(simp add: new_c_nonneg  new_h_nonneg)
        apply(subst (4) new_h_def)
        apply(simp add: new_c_nonneg  new_h_nonneg)
        by (auto simp: new_h_def new_c_def max.assoc)
      subgoal for m1 c1 m2 c2 m3 c3
        apply(subst (3) new_c_def)
        apply(simp add: new_c_nonneg  new_h_nonneg)
        apply(subst (3) new_c_def)
        apply(subst (3) new_h_def)
        apply(simp add: new_c_nonneg  new_h_nonneg)
        apply(subst (2) new_c_def)
        apply(simp add: new_c_nonneg  new_h_nonneg)
        by (auto simp: new_h_def new_c_def max.assoc)
      done
    subgoal for a apply(cases a)
      subgoal for m c
        by (auto simp: new_h_def new_c_def zero_space_cost_def)
      done
    subgoal for a apply(cases a)
      subgoal for m c
        by (auto simp: new_h_def new_c_def zero_space_cost_def)
      done
    done
end


text \<open>the Invariant denotes, that maximum space \<open>m\<close> is at most the number of space_credits \<open>n\<close>\<close>

fun space_I :: "space_cost \<Rightarrow> nat \<Rightarrow> bool"  where
  "space_I (Space_Cost m c) n \<longleftrightarrow> m\<le>n"

fun space_minus :: "nat \<Rightarrow> space_cost \<Rightarrow> nat"  where
  "space_minus  n (Space_Cost m c) = n - m + c"
\<comment> \<open>if space_I holds, this is n - (m-c), i.e. credits minus newly occupied space\<close>

interpretation space: cost_framework "space_I" "space_minus"
  apply standard
  subgoal for a by(simp add: zero_space_cost_def)
  subgoal for cr apply (simp add: zero_space_cost_def) done
  subgoal for a b c apply(cases b; cases c) by (simp add: new_c_def new_h_def)
  subgoal for a b c apply(cases a; cases b) by (simp add: new_c_def new_h_def)
  subgoal for a b c apply(cases a; cases b) by (simp add: new_c_def new_h_def)
  subgoal for a b c apply(cases a; cases b) by (simp add: new_c_def new_h_def)
  done


lemma space_minus_aux: "space_I b 0 \<Longrightarrow> Space_Cost 0 (space_minus 0 b) = b"
  apply(cases b) by simp


text \<open>The test \<open>sm\<le>cr\<close> makes sure that the maximum of space \<open>sm\<close> used does not exceed 
      the allowed space by the "space-credits" cr.
      When before executing \<open>m\<close> there are \<open>cr\<close> credits, after the execution there will be
      \<open>cr - (sm-c)\<close>, i.e. the credits before minus the number of consumed space,
      see @{const curr_cost}.\<close>

lemma "space.wp m Q (s,cr) = (\<exists>r sm c s'. run m s = SUCC r (Space_Cost sm c) s'
                                   \<and> Q r (s', cr - sm + c) \<and> sm\<le>cr )"
    unfolding space.wp_def  mwp_def
    apply (auto split: mres.splits)
    subgoal for a b c apply(cases b)
      by simp
    done


(* TODO: again clash with type class lifting with prod for sep_algebra!
instantiation prod :: (monoid_add,monoid_add) monoid_add
begin

end

lemma
  assumes "cost_framework I1 minus1"
    and "cost_framework I2 minus2"
  shows "cost_framework (\<lambda>(a,b) (c,d). I1 a c \<and> I2 b d) (\<lambda>(a,b) (c,d). (minus1 a c, minus2 b d))"
*)

end
