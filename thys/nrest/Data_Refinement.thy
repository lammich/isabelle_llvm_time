theory Data_Refinement
imports NREST Time_Refinement
begin

subsection \<open>Data Refinement\<close>

 


definition conc_fun  ("\<Down>") where
  "conc_fun R m \<equiv> case m of FAILi \<Rightarrow> FAILT | REST X \<Rightarrow> REST (\<lambda>c. Sup {X a| a. (c,a)\<in>R})"
                                                                 
definition abs_fun ("\<Up>") where
  "abs_fun R m \<equiv> case m of FAILi \<Rightarrow> FAILT 
    | REST X \<Rightarrow> if dom X\<subseteq>Domain R then REST (\<lambda>a. Sup {X c| c. (c,a)\<in>R}) else FAILT"

                                 
lemma 
  conc_fun_FAIL[simp]: "\<Down>R FAILT = FAILT" and
  conc_fun_RES: "\<Down>R (REST X) = REST (\<lambda>c. Sup {X a| a. (c,a)\<in>R})"
  unfolding conc_fun_def by (auto split: nrest.split)


lemma 
  abs_fun_FAIL[simp]: "\<Up>R FAILT = FAILT" and
  abs_fun_RES: "\<Up>R (REST X) = (if dom X\<subseteq>Domain R then REST (\<lambda>a. Sup {X c| c. (c,a)\<in>R}) else FAILT)"
  unfolding abs_fun_def by (auto split: nrest.split)

  
(* m \<le> \<Down>R m' *)  
lemma 
  "(SPECT m \<le> \<Down>R (SPECT m')) \<longleftrightarrow>
  (\<forall>x c. m x = Some c \<longrightarrow> (\<exists>a c'. (x,a)\<in>R \<and> c'\<ge>c \<and> m' a =Some c'))"
  apply (auto simp: conc_fun_RES)  
  oops


notepad begin
  fix m m' :: "bool \<Rightarrow> ( (string,enat) acost) option" and R co x
  assume m: "m = [ True \<mapsto> acostC ((\<lambda>_. 0)(''a'':=2,''b'':=2)) ]"
  
  assume m': "m' = [ True \<mapsto> acostC ((\<lambda>_. 0)(''a'':=1,''b'':=2)), False \<mapsto> acostC ((\<lambda>_. 0)(''a'':=2,''b'':=1))]"
  assume "m \<le> (\<lambda>c. Sup {m' a |a. (c, a) \<in> R})"
        "m x = Some co"
  assume R_def: "R = {(True,False), (True,True)}"
  have i: "(\<lambda>c. Sup {m' a |a. (c, a) \<in> R}) = [ True \<mapsto> acostC ((\<lambda>_. 0)(''a'':=2,''b'':=2)) ]"
    apply (rule ext)
    subgoal for c
      apply(cases c)
      subgoal unfolding R_def m' apply auto unfolding Sup_option_def apply auto
        unfolding Sup_acost_def apply auto apply(rule ext) sorry         
      subgoal unfolding R_def by (simp add: bot_option_def) 
      done
    done
  have "m \<le> (\<lambda>c. Sup {m' a |a. (c, a) \<in> R})"
    unfolding i m by simp
  have "\<exists>x'. (x, x') \<in> R \<and> (\<exists>c'\<ge>co. m' x' = Some c')" 
    sorry

end
    


lemma 
  "(\<Up>R (SPECT m) \<le> (SPECT m')) \<longleftrightarrow>
  (\<forall>x c. m x = Some c \<longrightarrow> (\<exists>x' c'. (x,x')\<in>R \<and> c'\<ge>c \<and> m' x' =Some c'))"
   unfolding abs_fun_def
  apply(auto) 
proof -
  fix x c 
  assume d: "dom m \<subseteq> Domain R" and p:"(\<lambda>a. Sup {m c |c. (c, a) \<in> R}) \<le> m'"
    and m: "m x = Some c"

  from d m obtain x' where xx': "(x,x') \<in> R" by auto
  from p have p': "\<And>a.  Sup {m c |c. (c, a) \<in> R} \<le> m' a" unfolding le_fun_def by auto
  have Supx': "Sup {m c |c. (c, x') \<in> R} \<ge> Some c"
    apply(rule Sup_upper) unfolding m[symmetric]
    using xx' by blast
  then have pf: "m' x' \<ge> Some c" using p'[of x'] by simp
  then obtain c' where ss: "m' x' = Some c'" by fastforce
  with pf have *: "Some c \<le> Some c'" by auto
  show "\<exists>x'. (x, x') \<in> R \<and> (\<exists>c'\<ge>c. m' x' = Some c')" 
    apply(rule exI[where x=x'])
    apply safe apply fact
    apply(rule exI[where x=c']) 
    using * ss by auto   
  oops


lemma 
  "(\<Up>R (SPECT m) \<le> (SPECT m')) \<longleftrightarrow>
  (\<forall>x c. m x = Some c \<longrightarrow> ((\<exists>x'. (x,x')\<in>R)
             \<and> (\<forall>x'. (x,x')\<in>R \<longrightarrow> (\<exists>c'. c'\<ge>c \<and> m' x' =Some c'))))"
  unfolding abs_fun_def
  apply(auto)
  prefer 3 subgoal  
    by (meson Domain.DomainI)  
proof -
  fix x c x'
  assume d: "dom m \<subseteq> Domain R" and p:"(\<lambda>a. Sup {m c |c. (c, a) \<in> R}) \<le> m'" and xx': "(x, x') \<in> R"
    and m: "m x = Some c"

  from p have p': "\<And>a.  Sup {m c |c. (c, a) \<in> R} \<le> m' a" unfolding le_fun_def by auto
  have Supx': "Sup {m c |c. (c, x') \<in> R} \<ge> Some c"
    apply(rule Sup_upper) unfolding m[symmetric]
    using xx' by blast
  then have pf: "m' x' \<ge> Some c" using p'[of x'] by simp
  then obtain c' where ss: "m' x' = Some c'" by fastforce
  with pf have *: "Some c \<le> Some c'" by auto
  show "(\<exists>c'\<ge>c. m' x' = Some c')"   
    apply(rule exI[where x=c']) 
    using * ss by auto   
next
  assume "dom m \<subseteq> Domain R"
    "\<forall>x c. m x = Some c \<longrightarrow> (\<exists>x'. (x, x') \<in> R) \<and> (\<forall>x'. (x, x') \<in> R \<longrightarrow> (\<exists>c'\<ge>c. m' x' = Some c'))"
  then have a: "\<And>x c.  m x = Some c \<Longrightarrow> (\<exists>x'. (x, x') \<in> R)"
      and b: "\<And>x c x'. m x = Some c \<Longrightarrow> (x, x') \<in> R \<Longrightarrow> (\<exists>c'\<ge>c. m' x' = Some c')"
    by auto

  show "(\<lambda>a. Sup {m c |c. (c, a) \<in> R}) \<le> m'"
    apply(rule le_funI)
    apply(rule Sup_least) apply safe
    subgoal for x' _ x
      apply(cases "m x") apply simp
      subgoal premises prems for c using b[OF prems(2,1)] prems(2) by auto
      done
    done
qed

lemma "(\<forall>x c. m x = Some c \<longrightarrow> ((\<exists>x'. (x,x')\<in>R) \<and> (\<forall>x'. (x,x')\<in>R \<longrightarrow> (\<exists>c'. c'\<ge>c \<and> m' x' =Some c'))))
   \<Longrightarrow> (\<forall>x c. m x = Some c \<longrightarrow> (\<exists>x' c'. (x,x')\<in>R \<and> c'\<ge>c \<and> m' x' =Some c'))"
  by blast
  

lemma Sup_dom: "Sup {m c |c. (c, a) \<in> S} \<noteq> None \<longleftrightarrow> (\<exists>c. m c \<noteq> None \<and> (c,a)\<in>S)"
  apply auto
  subgoal  
    by (smt Sup_bot_conv(1) Sup_empty combine_options_cases empty_Sup le_some_optE mem_Collect_eq option.simps(3))  
  subgoal  
    by (smt Sup_bot_conv(1) Sup_empty Sup_option_def mem_Collect_eq)  
  done


lemma SupSup_2: "Sup {m a |a. (c, a) \<in> R O S} =  Sup {m a |a b. (b,a)\<in>S \<and> (c,b)\<in>R }"
proof -
  have i: "\<And>a. (c,a) \<in> R O S \<longleftrightarrow> (\<exists>b. (b,a)\<in>S \<and> (c,b)\<in>R)" by auto
  have "Sup {m a |a. (c, a) \<in> R O S} = Sup {m a |a. (\<exists>b. (b,a)\<in>S \<and> (c,b)\<in>R)}" 
      unfolding i by auto
    also have "...  = Sup {m a |a b. (b,a)\<in>S \<and> (c,b)\<in>R}" by auto
    finally show ?thesis .
  qed

lemma SupSup_2c: "Sup {m c |c. (c, a) \<in> R O S} = Sup {m c |c b. (b,a)\<in>S \<and> (c,b)\<in>R}"
proof -
  have i: "\<And>c. (c,a) \<in> R O S \<longleftrightarrow> (\<exists>b. (b,a)\<in>S \<and> (c,b)\<in>R)" by auto
  have "Sup {m c |c. (c, a) \<in> R O S} = Sup {m c |c. (\<exists>b. (b,a)\<in>S \<and> (c,b)\<in>R)}" 
      unfolding i by auto
    also have "...  = Sup {m c |c b. (b,a)\<in>S \<and> (c,b)\<in>R}" by auto
    finally show ?thesis .
  qed

lemma 
  fixes m :: "'a \<Rightarrow> ('c::complete_lattice) option"
  shows SupSup: "Sup {Sup {m aa |aa. P a aa c} |a. Q a c} = Sup {m aa |a aa. P a aa c \<and> Q a c}"
  apply(rule antisym)
   subgoal apply(rule Sup_least)
     by (auto intro: Sup_subset_mono)
   subgoal 
     unfolding Sup_le_iff apply auto
     by (smt Sup_upper Sup_upper2 mem_Collect_eq)
   done 


lemma 
  fixes m :: "'a \<Rightarrow> ('c::complete_lattice) option"
  shows 
    SupSup_1: "Sup {Sup {m aa |aa. (a, aa) \<in> S} |a. (c, a) \<in> R} = Sup {m aa |a aa. (a,aa)\<in>S \<and> (c,a)\<in>R}"
  by(rule SupSup)

lemma 
  fixes m :: "'a \<Rightarrow> ('c::complete_lattice) option"
  shows 
    SupSup_1c: "Sup {Sup {m ca |ca. (ca, c) \<in> S} |c. (c, a) \<in> R} = Sup {m c |c b. (c,b)\<in>S \<and> (b,a)\<in>R}"
  apply(rule antisym)
   subgoal apply(rule Sup_least)
     by (auto intro: Sup_subset_mono)
   subgoal 
     unfolding Sup_le_iff apply auto
     by (smt Sup_upper Sup_upper2 mem_Collect_eq)
   done  




lemma abs_fun_chain:
  fixes M 
  shows "\<Up>R (\<Up>S M) = \<Up>(S O R) M"
  unfolding abs_fun_def
  apply(cases M) apply auto
  subgoal for m x c
  proof (goal_cases)
    case 1
    from 1(4) have "x\<in>dom m" by auto
    with 1 have "x\<in>Domain S" by auto
    then obtain y where xy: "(x,y) \<in> S" by blast
    with 1(2)[unfolded dom_def Sup_dom] have "y \<in> Domain R" apply auto  
      using `x\<in>dom m` by blast
    then obtain z where yz: "(y,z) \<in> R" by blast
    from xy yz show ?case apply - apply(rule DomainI) apply(rule relcompI) by auto
  qed
  subgoal for m apply(rule ext) apply(subst SupSup_2c[where m=m])  apply(subst SupSup_1c) apply auto by metis
  subgoal for m a co
    proof(goal_cases)
      case 1
      from 1(4) have pi: "\<And>c. c \<in> dom m \<Longrightarrow> (\<exists>b a. (c,b)\<in>S \<and> (b,a)\<in>R)" using Domain_iff by blast
      from 1(2) have "a \<in> dom (\<lambda>c. Sup {m c |c. (c, a) \<in> S})" unfolding dom_def by auto
      then obtain c where "m c \<noteq> None" "(c, a) \<in> S" unfolding dom_def Sup_dom by blast
      then have "c\<in>dom m" by blast
      with pi obtain b2 a2 where  "(c,b2)\<in>S" "(b2,a2)\<in>R" by blast
    with 1 show ?case oops(*
  qed   
  done*)



term "\<Down> S (\<Down> R M) \<le> \<Down>(S O R) M"
lemma abs_fun_chain_1dir:
  fixes M 
  shows "\<Up>(S O R) M \<le> \<Up>R (\<Up>S M)"
  unfolding abs_fun_def
  apply(cases M) apply auto
  subgoal for m x c
  proof (goal_cases)
    case 1
    from 1(4) have "x\<in>dom m" by auto
    with 1 have "x\<in>Domain S" by auto
    then obtain y where xy: "(x,y) \<in> S" by blast
    with 1(2)[unfolded dom_def Sup_dom] have "y \<in> Domain R" apply auto  
      using `x\<in>dom m` by blast
    then obtain z where yz: "(y,z) \<in> R" by blast
    from xy yz show ?case apply - apply(rule DomainI) apply(rule relcompI) by auto
  qed
  subgoal for m apply(rule le_funI) apply(subst SupSup_2c[where m=m])  apply(subst SupSup_1c) apply auto
    apply(rule Sup_mono) by auto
  done   



(*
  inresT S s t  heißt: computation S berechnet ergebnis s mit mindestens t Zeit.

  \<Up>R S' bedeutet. für ein abstractes ergebnis a, wieviel Zeit braucht die computation S' für
    das längste konkrete c, welches a verfeinert

  inresT (\<Up>R S') a t, alle konkreten computations in S' welche das ergebnis a verfeinern 
    benötigen mindestens 
  
*)
   

lemma pfF: "Sup X = Some (\<infinity>::enat) \<Longrightarrow> \<exists>x\<in>X. \<exists>a. x = Some a \<and> a\<ge>enat y"
proof -
  assume a: "Sup X = Some (\<infinity>::enat)"
  have g: "\<And>x. Sup X = Some x \<Longrightarrow> Sup (Option.these X) = x"
    unfolding Sup_option_def by (auto split: if_splits)
  from Sup_enat_less2[of "Option.these X", OF g, OF a]
  obtain x  where "x \<in> Option.these X" "enat y < x" by blast
  then show ?thesis unfolding Option.these_def  
    using not_less by fastforce  
qed


lemma yeaha: "X\<noteq>{} \<Longrightarrow> Sup X = enat e \<Longrightarrow> (\<exists>x\<in>X. x = enat e)"
  unfolding Sup_enat_def apply (auto split: if_splits)  
  using Max_in by fastforce  

lemma aux_lemma: assumes "S' =SPECT m"
  shows "dom m \<subseteq> Domain R \<longleftrightarrow> (\<forall>x t. inresT S' x t \<longrightarrow> (\<exists>x'. (x,x') \<in> R))"
  using assms apply auto  
    subgoal  
      by (metis Domain_iff zero_enat_def zero_le) 
    done

lemma inresT_abs_fun: "inresT (\<Up>R S') a t =
   (nofailT S' \<longrightarrow> (\<forall>m. S' =SPECT m \<longrightarrow> (\<forall>x\<in>dom m. \<exists>x'. (x,x')\<in> R) \<longrightarrow> ((\<exists>c. (c,a)\<in>R \<and> inresT S' c t))))"
  oops
lemma other_chara: "(nofailT S' \<longrightarrow> (\<forall>m. S' =SPECT m \<longrightarrow> dom m \<subseteq> Domain R \<longrightarrow> ((\<exists>c. (c,a)\<in>R \<and> inresT S' c t))))
    \<longleftrightarrow> (nofailT S' \<longrightarrow> ((\<forall>x t. inresT S' x t \<longrightarrow> (\<exists>x'. (x,x') \<in> R)) \<longrightarrow> ((\<exists>c. (c,a)\<in>R \<and> inresT S' c t))))"
  apply auto 
  subgoal using aux_lemma  
    by (smt inresT_REST nofailT_simps(1) nres_simp_internals(2) nrest.exhaust)    
   subgoal  
     by auto   
   done

(* wir sind hier bei enat! *)
lemma inresT_abs_fun: "inresT (\<Up>R S') a t =
   (nofailT S' \<longrightarrow> (\<forall>m. S' =SPECT m \<longrightarrow> dom m \<subseteq> Domain R \<longrightarrow> ((\<exists>c. (c,a)\<in>R \<and> inresT S' c t))))"
  apply(cases S')
  subgoal apply simp done
  subgoal for m'
    apply rule
    subgoal
      apply (auto simp: abs_fun_RES)
      apply(cases "dom m' \<subseteq> Domain R")
      subgoal for t' apply auto 
        subgoal premises prems
      proof (cases "t'")
        case (enat n)
        from prems(3) have "\<exists>c. (c,a)\<in>R \<and> m' c \<noteq> None" 
          by (smt Sup_bot_conv(1) Sup_empty empty_Sup mem_Collect_eq option.distinct(1))  
        then have i: "Option.these {m' c |c. (c, a) \<in> R} \<noteq> {}" unfolding Option.these_def by auto
        from prems(3) have ii: "Sup (Option.these {m' c |c. (c, a) \<in> R}) = t'"
          unfolding Sup_option_def by(auto split: if_splits)

        from yeaha[OF i] ii enat obtain x
          where u: "x\<in>Option.these {m' c |c. (c, a) \<in> R}" and prea: "x = enat n" by blast
        then obtain c where mcx: "m' c = Some x" "(c,a)\<in>R" unfolding Option.these_def  
          by (smt Sup_finite_enat enat mem_Collect_eq prems(3))  

        show ?thesis apply(rule exI[where x=c]) apply safe apply fact
          apply(rule exI[where x=t'])
          apply safe 
          subgoal using prems(2) prea enat by simp
          subgoal using mcx enat prea apply simp done
          done
      next
        case infinity
        from infinity pfF prems(3) obtain x v
          where "x \<in> {m' c |c. (c, a) \<in> R}" and xv: "x = Some v" and tv: "enat t \<le> v" by blast
        then obtain c where "(c,a)\<in>R" and m': "m' c = x" by blast
          
        show ?thesis
          apply(rule exI[where x=c]) apply safe apply fact
          apply(rule exI[where x=v]) apply safe using xv m' tv by auto 
      qed 
      done
      subgoal by simp
      done 
    subgoal
      apply (auto simp: abs_fun_RES)
    proof (goal_cases)
      case (1 c t')
      have t: "Sup {m' c |c. (c, a) \<in> R} \<ge> Some t'" apply(rule Sup_upper2[where u="m' c"]) using 1 apply blast using 1  
        by simp  
      then have "Sup {m' c |c. (c, a) \<in> R} \<noteq> None"  
        by (metis less_eq_option_Some_None)  
      then obtain Sc where pf: "Sup {m' c |c. (c, a) \<in> R} = Some Sc"   
        by blast    
      
      show ?case
        apply(rule exI[where x=Sc])
        using t 1(4) pf by auto 
    qed 
    done
  done

lemma inresT_abs_fun'[refine_pw_simps]: "inresT (\<Up>R S') a t =
    (nofailT S' \<longrightarrow> ((\<forall>x t. inresT S' x t \<longrightarrow> (\<exists>x'. (x,x') \<in> R)) \<longrightarrow> ((\<exists>c. (c,a)\<in>R \<and> inresT S' c t))))"
  unfolding other_chara[symmetric]
  by (fact inresT_abs_fun)


lemma nrest_Rel_mono':
  fixes A :: "('a,'b::complete_lattice) nrest"
  shows "A \<le> B \<Longrightarrow> \<Up> R A \<le> \<Up> R B"
  unfolding abs_fun_def
  apply (auto split: nrest.split simp: le_fun_def)  
  subgoal by (smt complete_lattice_class.Sup_mono mem_Collect_eq)   
  subgoal  
    by (metis domIff less_eq_option_Some_None subset_eq)
  done

lemma nofailT_abs_fun_RETURNT[refine_pw_simps]: "nofailT (\<Up> R (RETURNT x)) \<longleftrightarrow> (\<exists>x'. (x,x')\<in>R)"
  unfolding RETURNT_def abs_fun_def by auto

lemma nofailT_abs_fun_SPECT[refine_pw_simps]:
  "nofailT (\<Up> R M) \<longleftrightarrow> (nofailT M \<and> (\<forall>x t. inresT M x t \<longrightarrow> (\<exists>x'. (x,x')\<in>R)))"
  unfolding   abs_fun_def
  apply(cases M) apply auto  
  using le_zero_eq linear zero_enat_def   
  by (metis Domain.DomainI)  


lemma nofailT_abs_fun_acost_SPECT[refine_pw_simps]:
  "nofailT (\<Up> R M) \<longleftrightarrow> (nofailT M \<and> (\<forall>x b t. inresT (project_acost b M) x t \<longrightarrow> (\<exists>x'. (x,x')\<in>R)))"
  unfolding   abs_fun_def
  apply(cases M) apply (auto simp: project_acost_SPECT )  
  using le_zero_eq linear zero_enat_def  
  by (metis Domain.DomainI)  



lemma project_acost_conc_fun_commute[refine_pw_simps]: "project_acost b (\<Down>R m) = \<Down>R (project_acost b m)"
  unfolding project_acost_def conc_fun_def
  apply(cases m)
  subgoal by simp
  subgoal
    supply *[simp] = continuous_option'[OF continuous_the_acost, THEN continuousD]
    apply simp
    apply(rule ext)
    apply(rule arg_cong[where f=Sup])
    by auto
  done


lemma project_acost_abs_fun_commute[refine_pw_simps]: 
  "project_acost b (\<Up>R m) = \<Up>R (project_acost b m)"
  unfolding project_acost_def abs_fun_def
  apply(cases m)
  subgoal by simp
  subgoal
    supply *[simp] = continuous_option'[OF continuous_the_acost, THEN continuousD]
    apply (auto split: option.splits)
    apply(rule ext)
    apply(rule arg_cong[where f=Sup])
     apply (auto split: option.splits)
    subgoal 
      by (smt mem_Collect_eq option.simps(5) setcompr_eq_image) 
    subgoal 
      by (metis (mono_tags, lifting) mem_Collect_eq option.simps(4) setcompr_eq_image) 
    subgoal 
      by (simp add: domIff subset_iff) 
    done
  done


lemma RETURNT_SV_refine: "single_valued R \<Longrightarrow> (x,x')\<in>R \<Longrightarrow> \<Up> R (RETURNT x) \<le> (RETURNT x' :: ('a,('b,enat)acost) nrest)"
  by(auto simp: pw_acost_le_iff refine_pw_simps inresT_abs_fun dest: single_valuedD)

lemma "x\<in>Domain R \<Longrightarrow> \<Up> R (RETURNT x) \<le> (SPEC (\<lambda>x'. (x,x')\<in>R) (\<lambda>_.0) :: ('a,('b,enat)acost) nrest)"
  by(auto simp: pw_acost_le_iff refine_pw_simps inresT_abs_fun SPEC_def zero_acost_def zero_enat_def)


lemma abs_fun_chain_1dir_easy:
  fixes M :: "(_,(_,enat)acost) nrest"
  shows "\<Up>(S O R) M \<le> \<Up>R (\<Up>S M)"
  apply(auto simp: pw_acost_le_iff refine_pw_simps) 
   apply blast+
  done

lemma abs_fun_chain_1dir_wrong_aux: "((x, x'') \<in> S O R) \<longleftrightarrow> (\<exists>x'. (x,x')\<in>S \<and> (x',x'')\<in>R)"
  by auto

lemma abs_fun_chain_1dir_wrong:
  fixes M :: "(_,(_,enat)acost) nrest"
  shows "\<Up>(S O R) M \<ge> \<Up>R (\<Up>S M)"
  apply(auto simp: pw_acost_le_iff refine_pw_simps)
  unfolding abs_fun_chain_1dir_wrong_aux 
  oops

(* TODO: is  \<exists>t b. inresT (project_acost b m) x t; really what we want? *)
lemma bindT_refine_abs:
  fixes m' :: "('a,('b,enat)acost) nrest"
  assumes "\<Up> R' m \<le> m'"
  "(\<And>x x'. \<lbrakk>(x,x')\<in>R';  \<exists>t b. inresT (project_acost b m) x t;  \<exists>t b. inresT (project_acost b m') x' t;
    nofailT m; nofailT m'\<rbrakk> \<Longrightarrow> \<Up> R (f x) \<le> f' x' )"
shows "\<Up> R (bindT m f) \<le> bindT m' f'"
  using assms
  apply(auto simp: pw_acost_le_iff refine_pw_simps)
  apply metis+
  done



(* TODO: RECT *)

lemma RECT_refine_abs:
  assumes M: "mono2 body"
  assumes R0: "(x,x')\<in>R"
  assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> \<Up>S (f x) \<le> (f' x'); (x,x')\<in>R \<rbrakk> 
    \<Longrightarrow> \<Up>S (body f x) \<le> (body' f' x')"
  shows "\<Up>S (RECT (\<lambda>f x. body f x) x) \<le> (RECT (\<lambda>f' x'. body' f' x') x')"
  unfolding RECT_flat_gfp_def
  apply (clarsimp simp add: M) 
  apply (rule flatf_fixp_transfer[where 
        fp'="flatf_gfp body" 
    and B'=body 
    and P="\<lambda>x x'. (x',x)\<in>R", 
    OF _ _ flatf_ord.fixp_unfold[OF M[THEN trimonoD_flatf_ge]] R0])
  apply simp
  apply (simp add: trimonoD_flatf_ge)
  by (rule RS)

                      
lemma WHILET_refine_abs:
  fixes f :: "_ \<Rightarrow> (_,(_,enat)acost) nrest"
  assumes R0: "(x,x')\<in>R"
  assumes SV: "single_valued R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x' \<rbrakk> \<Longrightarrow> \<Up>R (f x) \<le> f' x'"
  shows "\<Up>R (whileT b f x) \<le> whileT b' f' x'"
  unfolding whileT_def apply(rule RECT_refine_abs)
    subgoal by(refine_mono)  
     apply (fact R0)
    by(auto simp: COND_REF STEP_REF SV  intro: RETURNT_SV_refine bindT_refine_abs[where R'=R])
  


(* 
lemma conc_fun_RES_sv: "single_valued R \<Longrightarrow> 
  \<Down>R (REST X) = REST (\<lambda>c. if c\<in>Dom R then Some (X Sup {X a| a. (c,a)\<in>R})"
*)

lemma nrest_Rel_mono:
  fixes A :: "('a,'b::complete_lattice) nrest"
  shows "A \<le> B \<Longrightarrow> \<Down> R A \<le> \<Down> R B"
  unfolding conc_fun_def
  apply (auto split: nrest.split simp: le_fun_def)  
  by (smt complete_lattice_class.Sup_mono mem_Collect_eq)   



lemma datarefine_timerefine_commute1:
  fixes m ::  "('f, ('b, enat) acost) nrest"
  assumes "wfR R'"
  shows "\<Down> R (timerefine R' m) \<le> timerefine R' (\<Down> R m)"
  unfolding conc_fun_def timerefine_def
  apply(cases m) apply auto apply(rule le_funI)
  apply(rule Sup_least)
  apply (auto split: option.splits)
  subgoal 
    by (metis (mono_tags, lifting) Sup_upper less_eq_option_Some_None mem_Collect_eq)
  unfolding less_eq_acost_def apply simp apply safe
  apply(rule Sum_any_mono)
  apply(rule mult_right_mono)
  subgoal
    by (metis (mono_tags, lifting) Sup_upper less_eq_acost_def less_eq_option_Some mem_Collect_eq)
   apply simp
  apply(rule wfR_finite_mult_left )
  using assms by simp



lemma datarefine_timerefine_commute2: 
  assumes "wfR R'" and sv: "single_valued R"
  shows "\<Down> R (timerefine R' m) \<ge> timerefine R' (\<Down> R m)"
    unfolding conc_fun_def timerefine_def
    apply(cases m) apply auto  apply(rule le_funI)
    subgoal for x2 x
    proof (cases "\<exists>a. (x, a) \<in> R")
      case True
      from sv have k: "\<And>a. (x, a) \<in> R \<longleftrightarrow> (a = (THE a. (x,a)\<in>R))"
        unfolding single_valued_def apply auto 
        subgoal           by (simp add: the_equality)   
        subgoal apply(rule theI') using True by auto 
        done      
      show ?thesis apply(subst k) apply simp
        apply(subst (2) k) by simp
    next
      case False
      then show ?thesis by (auto split: option.splits simp: bot_option_def)  
    qed 
    done 
 
           
lemma datarefine_timerefine_commute: 
  fixes m ::  "('f, ('b, enat) acost) nrest"
  assumes "wfR R'" and sv: "single_valued R"
  shows "\<Down> R (timerefine R' m) = timerefine R' (\<Down> R m)"
  apply(rule antisym)
  subgoal using assms datarefine_timerefine_commute1 by metis
  subgoal using assms datarefine_timerefine_commute2  by metis
  done


lemma pw_conc_nofail[refine_pw_simps]: 
  "nofailT (\<Down>R S) = nofailT S"
  by (cases S) (auto simp: conc_fun_RES)

lemma "single_valued A \<Longrightarrow> single_valued B \<Longrightarrow> single_valued (A O B)"
  by (simp add: single_valued_relcomp)

lemma Sup_enatoption_less2: " Sup X = Some \<infinity> \<Longrightarrow> (\<exists>x. Some x \<in> X \<and> enat t < x)"
  using Sup_enat_less2
  by (metis Sup_option_def in_these_eq option.distinct(1) option.sel)

lemma pw_conc_inres[refine_pw_simps]:
  "inresT (\<Down>R S') s t = (nofailT S' 
  \<longrightarrow> ((\<exists>s'. (s,s')\<in>R \<and> inresT S' s' t) \<comment> \<open> \<and> (\<forall>s' t'. (s,s')\<in>R \<longrightarrow> inresT S' s' t' \<longrightarrow> t' \<le> t )\<close> ))"
  apply (cases S')
  subgoal by simp
  subgoal  for m'
    apply rule
    subgoal 
      apply (auto simp: conc_fun_RES  )
      subgoal for t' 
        apply(cases t')
         apply auto
        subgoal for n apply(auto dest!: Sup_finite_enat) 
          subgoal for a apply(rule exI[where x=a]) apply auto
            apply(rule exI[where x="enat n"]) by auto  
          done
        subgoal apply(drule Sup_enatoption_less2[where t=t])
          apply auto subgoal for x a apply(rule exI[where x=a]) apply auto
            apply(rule exI[where x=x]) by auto 
          done
        done
      done
    subgoal 
      apply (auto simp: conc_fun_RES)
      by (smt Sup_upper dual_order.trans le_some_optE mem_Collect_eq)
    done
  done 

lemma bindT_refine':
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x' t . \<lbrakk> (x,x')\<in>R'; inresT M x t; inresT M' x' t;
    nofailT M; nofailT M'
  \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bindT M (\<lambda>x. f x) \<le> \<Down> R (bindT M' (\<lambda>x'. f' x'))"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  by blast 

(*
experiment
begin




lemma bindT_refine'':
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x' t . \<lbrakk> (x,x')\<in>R'    
  \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bindT M (\<lambda>x. f x) \<le> \<Down> R (bindT M' (\<lambda>x'. f' x'))" 
  sorry


lemma bindT_mono_under_timerefine:
  fixes R :: "('a \<Rightarrow> ('a, enat) acost)"
  assumes wfR: "wfR R"
  shows "m \<le> timerefine R m' \<Longrightarrow> (\<And>x. f x \<le> timerefine R (f' x)) \<Longrightarrow> bindT m f \<le> timerefine R (bindT m' f')"
  apply(rule order.trans) defer apply(subst timerefine_bindT_ge) using assms apply simp apply simp
  apply(rule bindT_mono_f2) by simp_all

thm bindT_refine'' bindT_mono_under_timerefine

lemma 
  assumes "wfR tR" and sv: "single_valued R" and sv: "single_valued R'"
  assumes R1: "M \<le> (timerefine tR (\<Down> R'  M'))"
  assumes R2: "\<And>x x' t . \<lbrakk> (x,x')\<in>R' \<rbrakk> \<Longrightarrow> f x \<le> (timerefine tR ( \<Down> R  (f' x')))"
  shows "bindT M (\<lambda>x. f x) \<le> (timerefine tR (\<Down> R  (bindT M' (\<lambda>x'. f' x'))))"
  apply(subst datarefine_timerefine_commute[symmetric, OF assms(1,2)])

  apply(rule order.trans)
   defer apply(rule nrest_Rel_mono) apply(subst timerefine_bindT_ge[OF assms(1)]) apply simp
  apply(rule bindT_refine''[where R'=R'])
  apply(rule order.trans[OF R1])
   apply(subst datarefine_timerefine_commute[  OF assms(1,3)]) apply simp
  apply(rule order.trans[OF R2]) apply simp
  apply(subst datarefine_timerefine_commute[  OF assms(1,2)]) apply simp
  done


lemma 
  assumes "wfR tR" 
  assumes R1: "M \<le> (\<Down> R'(timerefine tR   M'))"
  assumes R2: "\<And>x x' t . \<lbrakk> (x,x')\<in>R' \<rbrakk> \<Longrightarrow> f x \<le> ( \<Down> R (timerefine tR  (f' x')))"
  shows "bindT M (\<lambda>x. f x) \<le> (\<Down> R (timerefine tR   (bindT M' (\<lambda>x'. f' x'))))" 
  apply(rule order.trans)
   defer apply(rule nrest_Rel_mono) apply(subst timerefine_bindT_ge[OF assms(1)]) apply simp
  apply(rule bindT_refine''[where R'=R'])
  apply(rule R1) 
  apply(rule R2) by simp 



    
  

                     


end *)





subsubsection \<open>Examples\<close>

definition Rset where "Rset = { (c,a)| c a. set c = a}"
                                     
lemma "RETURNT [1,2,3] \<le> \<Down>Rset (RETURNT {1,2,3})"
  unfolding conc_fun_def RETURNT_def Rset_def
  apply simp unfolding le_fun_def by auto

lemma "RETURNT [1,2,3] \<le> \<Down>Rset (RETURNT {1,2,3})"
  unfolding conc_fun_def RETURNT_def Rset_def
  apply simp unfolding le_fun_def by auto


definition Reven where "Reven = { (c,a)| c a. even c = a}"

lemma "RETURNT 3 \<le> \<Down>Reven (RETURNT False)"
  unfolding conc_fun_def RETURNT_def Reven_def
  apply simp unfolding le_fun_def by auto

lemma "m \<le> \<Down>Id m"
  unfolding conc_fun_def RETURNT_def 
  apply (cases m) by auto


lemma "m \<le> \<Down>{} m \<longleftrightarrow> (m=FAILT \<or> m = SPECT bot)"
  unfolding conc_fun_def RETURNT_def 
  apply (cases m) apply auto by (metis bot.extremum dual_order.antisym le_funI)


lemma abs_fun_simps[simp]: 
  "\<Up>R FAILT = FAILT"
  "dom X\<subseteq>Domain R \<Longrightarrow> \<Up>R (REST X) = REST (\<lambda>a. Sup {X c| c. (c,a)\<in>R})"
  "\<not>(dom X\<subseteq>Domain R) \<Longrightarrow> \<Up>R (REST X) = FAILT"
  unfolding abs_fun_def by (auto  split: nrest.split)

term single_valued
 
context fixes R assumes SV: "single_valued R" begin


lemma 
  fixes m :: "'b \<Rightarrow> enat option"
  shows
  Sup_sv: "(c, a') \<in> R \<Longrightarrow>  Sup {m a| a. (c,a) \<in> R} = m a'"
proof -
  assume "(c,a') \<in> R"
  with SV have singleton: "{m a| a. (c,a) \<in> R} = {m a'}" by(auto dest: single_valuedD) 
  show ?thesis unfolding singleton by simp
qed 

lemma indomD: " M c = Some y \<Longrightarrow> dom M \<subseteq> Domain R \<Longrightarrow> (\<exists>a. (c,a)\<in>R)"
  by auto
(*
lemma conc_abs_swap: "m' \<le> \<Down>R m \<longleftrightarrow> \<Up>R m' \<le> m"
  apply rule
  subgoal (* <-- *)
  unfolding conc_fun_def abs_fun_def using SV
  apply (auto split: nrest.splits) 
  subgoal for M M'
    apply (auto simp add: le_fun_def)  
    sorry (* by (smt Sup_least antisym le_cases mem_Collect_eq single_valuedD)  *)
  subgoal 
    by (smt Collect_cong Domain.DomainI domI domIff empty_Sup empty_def le_map_dom_mono set_rev_mp)    
  done

  subgoal (* \<longrightarrow> *)
    unfolding conc_fun_def abs_fun_def using SV
    apply(auto split: nrest.splits if_splits)
    apply (auto simp add: le_fun_def)
    subgoal for M M' c
      apply(cases "M c = None")
       apply auto apply(frule indomD) apply simp
      apply(auto) sorry(*
      apply(simp only: Sup_sv)
       
      by (me tis (mono_tags, lifting) Sup_le_iff mem_Collect_eq) *)
    done
  done

lemma 
  fixes m :: "'b \<Rightarrow> enat option"
  shows
  Inf_sv: "(c, a') \<in> R \<Longrightarrow>  Inf {m a| a. (c,a) \<in> R} = m a'"
proof -
  assume "(c,a') \<in> R"
  with SV have singleton: "{m a| a. (c,a) \<in> R} = {m a'}" by(auto dest: single_valuedD) 
  show ?thesis unfolding singleton by simp
qed 

lemma ac_galois: "galois_connection (\<Up>R) (\<Down>R)"
  apply (unfold_locales)
  by (rule conc_abs_swap)
*)

lemma 
  fixes m :: "'b \<Rightarrow> enat option"
  shows 
  Sup_some_svD: "Sup {m a |a. (c, a) \<in> R} = Some t' \<Longrightarrow> (\<exists>a. (c,a)\<in>R \<and> m a = Some t')"
  using SV by (smt Sup_le_iff dual_order.antisym less_eq_option_Some_None mem_Collect_eq order_refl single_valued_def)
 

end 


lemma pw_abs_nofail[refine_pw_simps]: 
  "nofailT (\<Up>R M) \<longleftrightarrow> (nofailT M \<and> (\<forall>x. (\<exists>t. inresT M x t) \<longrightarrow> x\<in>Domain R))"
  apply (cases M)
  apply simp
  apply (auto simp: abs_fun_simps abs_fun_def)
  by (metis zero_enat_def zero_le)



(*
lemma pw_abs_inre: 
  "inresT (\<Up>R M) a t \<longleftrightarrow> (nofailT (\<Up>R M) \<longrightarrow> (\<exists>c. inresT M c t \<and> (c,a)\<in>R))"
  apply (cases M)
  apply simp
  apply (auto simp: abs_fun_def)
  done*)

(*
lemma pw_conc_inres:
  "inresT (\<Down>R S') s t = (nofailT S' 
  \<longrightarrow> (\<exists>s'. (s,s')\<in>R \<and> inresT S' s' t))"
  apply (cases S')
  subgoal by simp
  subgoal  for m'
    apply rule
    subgoal 
      apply (auto simp: conc_fun_RES) sorry
    subgoal 
      apply (auto simp: conc_fun_RES) sorry
    done
  oops *)

lemma sv_the: "single_valued R \<Longrightarrow> (c,a) \<in> R \<Longrightarrow> (THE a. (c, a) \<in> R) = a"
  by (simp add: single_valued_def the_equality)

lemma conc_fun_RES_sv:
  fixes X :: "'b \<Rightarrow> enat option"
  assumes SV: "single_valued R"
  shows "\<Down>R (REST X) = REST (\<lambda>c. if c\<in>Domain R then X (THE a. (c,a)\<in>R) else None )"
  unfolding conc_fun_def
  apply(auto split: nrest.split)
  apply(rule ext)
  apply auto
  subgoal using  SV  by (auto simp: Sup_sv sv_the)
  subgoal by (smt Collect_cong Domain.DomainI empty_Sup empty_def)
  done

lemma conc_fun_mono[simp, intro!]: 
  shows "mono ((\<Down>R)::('b, enat) nrest \<Rightarrow> ('a, enat) nrest)"
  apply rule 
  apply (simp add: pw_le_iff)
  by (auto simp: refine_pw_simps) 


lemma conc_fun_R_mono:
  fixes M :: "(_,enat) nrest"
  assumes "R \<subseteq> R'" 
  shows "\<Down>R M \<le> \<Down>R' M"
  using assms
  by (auto simp: pw_le_iff refine_pw_simps)


lemma conc_fun_chain:
  fixes M :: "(_,enat) nrest"
  shows "\<Down>R (\<Down>S M) = \<Down>(R O S) M"
  apply(cases M)
  subgoal by simp
  apply simp
  apply(simp only: conc_fun_RES)
  apply auto apply (rule ext)  unfolding SupSup_1 SupSup_2 by meson 

lemma conc_fun_chain_sv:
  fixes M :: "(_,enat) nrest"
  assumes SVR: "single_valued R" and SVS: "single_valued S"
  shows "\<Down>R (\<Down>S M) = \<Down>(R O S) M"
  apply(cases M)
  subgoal by simp
  apply simp
  using SVS apply(simp only: conc_fun_RES_sv)
  using SVR apply(simp only: conc_fun_RES_sv)
  using single_valued_relcomp[OF SVR SVS] apply(simp only: conc_fun_RES_sv)
  apply (auto split: nrest.split)
  apply (rule ext) apply auto
    apply(auto simp add: sv_the)  
  apply(subst sv_the) by auto


lemma conc_Id[simp]: "\<Down>Id = id"
  unfolding conc_fun_def [abs_def] by (auto split: nrest.split)

                                 
lemma conc_fun_fail_iff[simp]: 
  fixes S :: "(_,enat) nrest"
  shows
  "\<Down>R S = FAILT \<longleftrightarrow> S=FAILT"
  "FAILT = \<Down>R S \<longleftrightarrow> S=FAILT"
  by (auto simp add: pw_eq_iff refine_pw_simps)

lemma conc_trans[trans]:
  fixes B :: "(_,enat) nrest"
  assumes A: "C \<le> \<Down>R B" and B: "B \<le> \<Down>R' A" 
  shows "C \<le> \<Down>R (\<Down>R' A)"
  using assms by (fastforce simp: pw_le_iff refine_pw_simps)

lemma conc_trans_sv:
  fixes B :: "(_,enat) nrest"
  assumes SV: "single_valued R" "single_valued R'"
    and A: "C \<le> \<Down>R B" and B: "B \<le> \<Down>R' A" 
  shows "C \<le> \<Down>R (\<Down>R' A)"
  using assms by (fastforce simp: pw_le_iff refine_pw_simps)

text \<open>WARNING: The order of the single statements is important here!\<close>
lemma conc_trans_additional[trans]: 
  assumes "single_valued R"
  shows
  "\<And>(A::(_,enat) nrest) B C. A\<le>\<Down>R  B \<Longrightarrow> B\<le>    C \<Longrightarrow> A\<le>\<Down>R  C"
  "\<And>(A::(_,enat) nrest) B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>\<Down>R  C \<Longrightarrow> A\<le>\<Down>R  C"
  "\<And>(A::(_,enat) nrest) B C. A\<le>\<Down>R  B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>\<Down>R  C"

  "\<And>(A::(_,enat) nrest) B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>    C"
  "\<And>(A::(_,enat) nrest) B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>    C \<Longrightarrow> A\<le>    C"
  "\<And>(A::(_,enat) nrest) B C. A\<le>    B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>    C"
  using assms conc_trans[where R=R and R'=Id]
  by (auto intro: order_trans)



lemma RETURNT_refine:
  assumes "(x,x')\<in>R"
  shows "RETURNT x \<le> \<Down>R (RETURNT x')"
  using assms
  by (auto simp: RETURNT_def conc_fun_RES le_fun_def Sup_upper)  

(*
thm bindT_refine'
lemma bindT_refine'2:
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x' t . \<lbrakk> (x,x')\<in>R'; inresT M x t; inresT M' x' t;
    nofailT M; nofailT M'
  \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bindT M (\<lambda>x. f x) \<le> \<Down> R (bindT M' (\<lambda>x'. f' x'))"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)  
  by blast*)

lemma bindT_refine:
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set" and M :: "(_,enat) nrest"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x'. \<lbrakk> (x,x')\<in>R' \<rbrakk> 
    \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bindT M (\<lambda>x. f x) \<le> \<Down> R (bind M' (\<lambda>x'. f' x'))"
  apply (rule bindT_refine') using assms by auto

subsection \<open>WHILET refine\<close>

lemma RECT_refine:
  assumes M: "mono2 body"
  assumes R0: "(x,x')\<in>R"
  assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le>\<Down>S (f' x'); (x,x')\<in>R \<rbrakk> 
    \<Longrightarrow> body f x \<le>\<Down>S (body' f' x')"
  shows "RECT (\<lambda>f x. body f x) x \<le>\<Down>S (RECT (\<lambda>f' x'. body' f' x') x')"
  unfolding RECT_flat_gfp_def
  apply (clarsimp simp add: M) 
  apply (rule flatf_fixp_transfer[where 
        fp'="flatf_gfp body" 
    and B'=body 
    and P="\<lambda>x x'. (x',x)\<in>R", 
    OF _ _ flatf_ord.fixp_unfold[OF M[THEN trimonoD_flatf_ge]] R0])
  apply simp
  apply (simp add: trimonoD_flatf_ge)
  by (rule RS)

                                         
lemma WHILET_refine:
  fixes f :: "_ \<Rightarrow> (_,enat) nrest"
  assumes R0: "(x,x')\<in>R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "whileT b f x \<le> \<Down>R (whileT b' f' x')"
  unfolding whileT_def apply(rule RECT_refine)
    subgoal by(refine_mono)  
     apply (fact R0)
    by(auto simp: COND_REF STEP_REF RETURNT_refine intro: bindT_refine[where R'=R])  

lemma 
  assumes a: "\<And>m n c a. c\<in>Domain R \<Longrightarrow> \<exists>a. SPECT (n c) \<le>  SPECT (m a)"
  shows "(SPECT n) \<le> \<Down> R (SPECT m)"
  using a  apply auto  
    unfolding conc_fun_def apply (auto split: nrest.split) 
      unfolding le_fun_def apply auto
    proof -
      fix c 
      assume "(\<And>c n m. c \<in> Domain R \<Longrightarrow> \<exists>a. \<forall>x. n c x \<le> m a x)"
      oops

lemma SPECT_refines_conc_fun':
  assumes a: "\<And>m c.  M = SPECT m
          \<Longrightarrow> c \<in> dom n \<Longrightarrow> (\<exists>a. (c,a)\<in>R \<and> n c \<le> m a)"
  shows "SPECT n \<le> \<Down> R M"
proof - 
  show ?thesis
    unfolding conc_fun_def apply (auto split: nrest.split) 
    subgoal for m unfolding le_fun_def apply auto
    proof -
      fix c
      assume m: "M = SPECT m"
      show "n c \<le> Sup {m a |a. (c, a) \<in> R} "
      proof (cases "c \<in> dom n")
        case True
        with m a obtain a where k: "(c,a)\<in>R" "n c \<le> m a" by blast 
        show ?thesis apply(rule  Sup_upper2) using k by auto
      next
        case False
        then show ?thesis 
          by (simp add: domIff)
      qed 
    qed
    done
qed

lemma SPECT_refines_conc_fun:
  assumes a: "\<And>m c. (\<exists>a. (c,a)\<in>R \<and> n c \<le> m a)"
  shows "SPECT n \<le> \<Down> R (SPECT m)"
  apply(rule SPECT_refines_conc_fun') using a by auto


lemma SPECT_refines_conc_fun_sv:
  assumes "single_valued R" 
    and a: "dom n \<subseteq> Domain R"
    and "\<And>c. c \<in> dom n \<Longrightarrow> n c \<le> (THE a. (c,a)\<in>R)"
  shows "SPECT n \<le> \<Down> R (SPECT m)"
  apply(rule SPECT_refines_conc_fun') using a
  using indomD[OF assms(1) _ a] domIff
  oops




lemma conc_fun_br: "\<Down> (br \<alpha> I1) (SPECT (emb I2 t))
        = (SPECT (emb (\<lambda>x. I1 x \<and> I2 (\<alpha> x)) t))"
  unfolding conc_fun_RES  apply auto apply(rule ext)    
      by (auto simp: emb'_def br_def bot_option_def Sup_option_def) 



  
  
end