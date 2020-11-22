
theory Dynamic_Array
  imports "../../sepref/Hnr_Primitives_Experiment" "../../nrest/Refine_Heuristics"
  "../../nrest/NREST_Automation"
begin

subsection \<open>Misc\<close>



lemma SPECT_assign_emb': "SPECT [x\<mapsto>t] = SPECT (emb' (\<lambda>y. y=x) (\<lambda>_.t))"
  unfolding emb'_def apply auto done

lemma 
  SPEC_leq_SPEC_I_even_stronger:
  "A \<le> A' \<Longrightarrow> (\<And>x. A x \<Longrightarrow> B x \<le> (B' x)) \<Longrightarrow> SPEC A B \<le> (SPEC A' B')"
  apply(auto simp: SPEC_def)
  by (simp add: le_fun_def)  


section \<open>Array with Length\<close>


definition "mop_list_length T xs = SPECT [ length xs \<mapsto> T  ]"



definition "llist_rel = br snd (\<lambda>(l,cs). l = length cs)"

definition "llist_new ini n = doN {
        cs \<leftarrow> mop_list_init (\<lambda>n. cost ''list_init'' (enat n)) ini n;
        RETURNT (n,cs)
      }"

lemma "llist_new ini n \<le> \<Down>llist_rel (mop_list_init (\<lambda>n. cost ''list_init'' (enat n)) ini n)"
  sorry

definition "llist_nth T  \<equiv> \<lambda>(l,cs) n. doN {
              mop_list_get T cs n
          }"

lemma "llist_nth T lcs i \<le> \<Down>llist_rel (mop_list_get T cs i)"


 




subsection \<open>Array Copy\<close>

definition "array_copy_impl dst src n = doM {
          return dst      
      }"


definition list_copy_spec where
  "list_copy_spec T dst src n = doN {
       ASSERT (n\<le>length dst \<and> n\<le>length src);
       REST [take n src @ drop n dst \<mapsto> T]
    }"



definition list_copy :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a list, (char list, enat) acost) nrest" where
"list_copy dst src n = doN {
          monadic_WHILEIET (\<lambda>(dst',n'). n'\<le>n \<and> length dst' = length dst \<and> dst' = take n' src @ drop n' dst)
              (\<lambda>(_::'a list,n'). (n-n') *m (cost ''if'' 1 + cost ''call'' 1 + cost ''list_get'' 1 + 
                                        cost ''list_set'' 1 + cost ''add'' 1) )
            (\<lambda>(_,n'). SPECc2 ''less'' (<) n' n)
            (\<lambda>(dst',n'). doN {
              x \<leftarrow> mop_list_get (\<lambda>_. cost ''list_get'' 1) src n';
              dst'' \<leftarrow> mop_list_set (\<lambda>_. cost ''list_set'' 1) dst n' x;
              n'' \<leftarrow> SPECc2 ''add'' (+) n' 1;
              RETURNT (dst'',n'')
            })
          (dst,0);
          RETURNT dst
      }"


definition list_copy2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a list, (char list, enat) acost) nrest" where
  "list_copy2 dst src n = doN {
          monadic_WHILEIET (\<lambda>(dst',n'). n'\<le>n \<and> length dst' = length dst \<and> dst' = take n' src @ drop n' dst)
              (\<lambda>(_::'a list,n'). (n-n') *m (cost ''if'' 1 + cost ''call'' 1 + cost ''list_get'' 1 + 
                                        cost ''list_set'' 1 + cost ''add'' 1) )
            (\<lambda>(_,n'). SPECc2 ''icmp_slt'' (<) n' n)
            (\<lambda>(dst',n'). doN {
              x \<leftarrow> mop_array_nth src n';
              dst'' \<leftarrow> mop_array_upd dst n' x;
              ASSERT (n'+1\<le>n);
              n'' \<leftarrow> SPECc2 ''add'' (+) n' 1;
              RETURNT (dst'',n'')
            })
          (dst,0);
          RETURNT dst
      }"

definition "TR_lst_copy = 0(''list_get'':=lift_acost mop_array_nth_cost,''list_set'':=lift_acost mop_array_upd_cost)"

lemma "list_copy dst src n \<le> \<Down>Id (\<Down>\<^sub>C TR_lst_copy (list_copy_spec (cost ''list_copy_c'' (enat n)) dst src n))"
  sorry


thm OT_intros

lemma one_time_bind_assert[OT_intros]: "one_time m \<Longrightarrow> one_time (doN { ASSERT P; m})"
  unfolding one_time_def
  apply(cases P) by auto

declare hnr_array_upd[sepref_fr_rules del] 
lemma hnr_array_upd_ohne_sc[sepref_fr_rules]:
  "CONSTRAINT is_pure A \<Longrightarrow>(uncurry2 array_upd, uncurry2 mop_array_upd) \<in> (array_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a array_assn A"
  apply(rule hnr_array_upd)
   apply simp 
  unfolding SC_attains_sup_def
  apply safe
  apply(rule one_time_attains_sup)
  unfolding mop_array_upd_def mop_list_set_def
  unfolding uncurry_def apply simp
  by(intro OT_intros)


locale size_t_context = 
  fixes size_t :: "'size_t::len2 itself" 
    and elem_assn :: "'a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn"
  assumes SIZE_T: "8\<le>LENGTH('size_t)"
begin
  abbreviation "size_assn \<equiv> snat_assn' TYPE('size_t)"

  thm hnr_array_upd
  thm hnr_eoarray_upd'

   sepref_def list_copy_impl is "uncurry2 list_copy2"  
    :: "(array_assn (pure R))\<^sup>d *\<^sub>a (array_assn (pure R))\<^sup>d *\<^sub>a size_assn\<^sup>k  \<rightarrow>\<^sub>a array_assn (pure R)"
    unfolding  list_copy2_def PR_CONST_def  
    unfolding monadic_WHILEIET_def
  apply (annot_snat_const "TYPE('size_t)")
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
       apply sepref_dbg_opt
     apply sepref_dbg_cons_solve
     apply sepref_dbg_cons_solve
    apply sepref_dbg_constraints
    apply auto
    sorry



  
subsection \<open>List Double\<close>

term mop_list_init
term mop_list_init_raw
thm hnr_raw_array_new refine_mop_list_init_raw
term mop_array_new
thm hnr_array_new


thm hnr_array_new


text \<open>an dynamic list is a triple (bs,l,c) with the carrier list bs which has capacity \<open>c\<close>, 
      and length \<open>l\<close>, i.e. the first \<open>l\<close> elements are valid. \<close>

definition dyn_list_double_spec where
  "dyn_list_double_spec \<equiv> \<lambda>(bs,l,c). doN {
       ASSERT (l\<le>c \<and> c=length bs);
       SPEC (\<lambda>(bs',l',c'). take l bs' = take l bs \<and> 
              length bs' = 2 * length bs \<and> l' = l \<and> l<c' \<and> c'=length bs')
        (\<lambda>(bs',l',c'). (enat (length bs')) *m cost ''alloc_raw'' 1
                       + cost ''list_copy_c'' (enat l')) 
  }"

definition dyn_list_double where
  "dyn_list_double ini  \<equiv> \<lambda>(bs,l,c). doN {
       ASSERT (l\<le>length bs);
       bsl \<leftarrow> SPECc2 ''mul'' (*) 2 c;
       dst \<leftarrow> mop_list_init (\<lambda>n. cost ''list_init_c'' (enat n)) ini bsl;
       list_copy dst bs l; 
       RETURNT (dst,l,bsl)
      }"


lemma "dyn_list_double ini (bs,l,c) \<le> dyn_list_double_spec (bs,l,c)"
  unfolding dyn_list_double_def dyn_list_double_spec_def



subsection \<open>List Push\<close>

context fixes T :: ecost begin
definition mop_list_append where
 [simp]: "mop_list_append  xs x = SPECT [xs @ [x] \<mapsto> T]"
sepref_register mop_list_append
end

definition dyn_list_append_basic_spec where
  "dyn_list_append_basic_spec \<equiv> \<lambda>(bs,l,c) x. doN {
      ASSERT (l < length bs);
      bs' \<leftarrow> mop_list_set (\<lambda>_. cost ''list_set'' 1) bs l x;
      l' \<leftarrow> SPECc2 ''add'' (+) l 1;
      RETURNT (bs',l',c)
  }"



definition dyn_list_append_spec where
  "dyn_list_append_spec \<equiv> \<lambda>(bs,l,c) x. doN {
      ASSERT (l\<le>c \<and> c=length bs \<and> 0<length bs);
      if\<^sub>N SPECc2 ''less'' (<) l c then doN {
        dyn_list_append_basic_spec (bs,l,c) x
      } else doN {          
        (bs',l',c') \<leftarrow> dyn_list_double_spec (bs,l,c);
        ASSERT (l'=l \<and> l<c' \<and> c'=length bs' \<and> take l bs = take l bs' );
        dyn_list_append_basic_spec (bs',l',c') x
      }
  }"


subsection \<open>dynamic List init\<close>


definition "dyn_list_rel = {( ((bs,l,c)) , as) | bs l c  as. take l bs = as \<and> l \<le> c \<and> c = length bs \<and> length bs > 0 }"


lemma dyn_list_rel_alt: "dyn_list_rel = br (\<lambda>(bs,l,c). take l bs) (\<lambda>(bs,l,c). l \<le> c \<and> c = length bs \<and> length bs > 0)"
  unfolding dyn_list_rel_def br_def by auto




definition mop_list_emptylist where
  "mop_list_emptylist T = SPECT [ [] \<mapsto> T ]"

definition dyn_list_new where
  "dyn_list_new ini = do {
       dst \<leftarrow> mop_list_init (\<lambda>n. cost ''list_init_c'' 8) ini 8;
       RETURNT (dst,0,8)
    }"



lemma "dyn_list_new ini \<le> \<Down>dyn_list_rel (timerefine RR (mop_list_emptylist (cost ''list_init_c'' 8)))"
  sorry


subsection \<open>dynamic list lookup\<close>

definition dyn_list_get where
  "dyn_list_get \<equiv> \<lambda>(bs,l,c) i. doN {
    mop_list_get (\<lambda>_. cost ''list_get'' 1) bs i
  }"

lemma "( (bs,l,c), as)\<in>dyn_list_rel \<Longrightarrow> dyn_list_get (bs,l,c) i \<le> mop_list_get (\<lambda>_. cost ''list_get'' 1) as i"
  sorry


subsection \<open>Sketch\<close>


fun reclaim where
  "reclaim FAILi t = FAILT"
| "reclaim (SPECT M) t = Sup { if t'\<ge>t x then SPECT [x\<mapsto>t' - t x] else FAILT | t' x. M x = Some t' }"

lemma reclaim_nofailT[simp]: "reclaim FAILT t = FAILT"
  unfolding top_nrest_def apply (simp add: )
  sorry

lemma blaD1: "nofailT (reclaim m t) \<Longrightarrow> nofailT m \<and> (\<forall>M. m=SPECT M \<longrightarrow> (\<forall>x t'. M x = Some t' \<longrightarrow> t' \<ge> t x))"
  apply(cases m)
   apply auto
  unfolding pw_Sup_nofail 
  by force 

lemma blaD2: " nofailT m \<and> (\<forall>M. m=SPECT M \<longrightarrow> (\<forall>x t'. M x = Some t' \<longrightarrow> t' \<ge> t x)) \<Longrightarrow> nofailT (reclaim m t)"
  apply(cases m)
   apply auto
  unfolding pw_Sup_nofail  
  by auto

lemma nofailT_reclaim:
 "nofailT (reclaim m t) \<longleftrightarrow> (nofailT m \<and> (\<forall>M. m=SPECT M \<longrightarrow> (\<forall>x t'. M x = Some t' \<longrightarrow> t' \<ge> t x)))"
  apply(cases m)
   apply auto
  unfolding pw_Sup_nofail  
  apply force
  by auto



definition dyn_list_append_spec2 where
  "dyn_list_append_spec2 T \<equiv> \<lambda>(bs,l,c) x. SPEC (\<lambda>(bs',l',c'). l'\<le>c' \<and> c'=length bs' \<and> l'=l+1 \<and> length bs' \<ge> length bs
                                                          \<and> take l bs' = take l bs \<and> bs' ! l = x) T"

definition "RRmm = 0(''list_append'':=cost ''bla'' (1::enat))"

definition "dyn_list_append_spec2_cost == \<lambda>_. cost ''bla'' 1"

lemma "((bs,l,c),as)\<in>dyn_list_rel \<Longrightarrow> (x',x) \<in> Id
 \<Longrightarrow> dyn_list_append_spec2 (\<lambda>_. cost ''bla'' 1) (bs,l,c) x'
         \<le> \<Down>dyn_list_rel (timerefine RRmm (mop_list_append (cost ''list_append'' 1) as x))"
  unfolding dyn_list_append_spec2_def mop_list_append_def
  apply(subst timerefine_SPECT_map)
  apply(subst SPECT_assign_emb')
  unfolding dyn_list_rel_alt
    apply(subst conc_fun_br)
  apply(subst SPEC_REST_emb'_conv[symmetric])
  apply safe
  apply(rule SPEC_leq_SPEC_I_even_stronger)
  subgoal by (auto simp: in_br_conv take_Suc_conv_app_nth)
  subgoal apply auto unfolding RRmm_def
    by(simp add: norm_cost ) 
  done


lemma "(\<And>x. Q x \<Longrightarrow> T x \<ge> \<Phi> x) \<Longrightarrow> reclaim (SPEC Q T) (\<Phi>::_\<Rightarrow>ecost) = SPEC Q (\<lambda>x. T x - \<Phi> x)"
  apply (simp add: pw_acost_eq_iff)
  apply (simp add: nofailT_reclaim)
  apply (simp add: refine_pw_simps SPEC_def)
  apply auto oops

lemma reclaim_if_covered: "(\<And>x. Q x \<Longrightarrow> T x \<ge> \<Phi> x) \<Longrightarrow> reclaim (SPEC Q T) (\<Phi>::_\<Rightarrow>ecost) = SPEC Q (\<lambda>x. T x - \<Phi> x)"
  apply(rule antisym)
  subgoal   unfolding SPEC_def apply simp apply (rule Sup_least) apply (auto simp: le_fun_def split: if_splits) done
  subgoal      unfolding SPEC_def apply auto
    unfolding Sup_nrest_def apply (auto simp: le_fun_def)
    apply(rule Sup_upper2)  by auto
  done
  
lemma consume_SPEC_eq: "consume (SPEC \<Phi> T) (t::ecost)= SPEC \<Phi> (\<lambda>x. T x + t)"
  unfolding SPEC_def consume_def
  apply auto
  apply(rule ext) apply auto 
  using ecost_add_commute by blast
  
  (* RAW COST \<le>     (  PREPOTENTIAL + ADVERTISED COST ) - POSTPOTENTIAL *)

lemma enat_minusrule: "b<\<infinity> \<Longrightarrow> (a+b)-b = (a::enat)"
  by(cases a; cases b; auto simp: ) 

lemma zz: "(\<And>x. the_acost b x < \<infinity>) \<Longrightarrow> (a+b)-b = (a::ecost)"
  apply(cases a; cases b; auto simp: )
  apply(rule ext) apply(rule enat_minusrule)
  by auto

lemma zz2: "b\<ge>c \<Longrightarrow> (a+b)-c \<ge> (a::(string,nat) acost)"
  apply(cases a; cases b; cases c) apply (auto simp: less_eq_acost_def)
  by (simp add: nat_move_sub_le)


lemma zz3: "b\<ge>c \<Longrightarrow> (b+a)-c \<ge> (a::(string,nat) acost)"
  apply(cases a; cases b; cases c) apply (auto simp: less_eq_acost_def)
  by (simp add: nat_move_sub_le)

lemma "enat x *m A - enat y *m A = enat (x-y) *m A"
  oops


lemma costmult_add_distrib_left:
  fixes a :: "'b::semiring"
  shows "a *m A + b *m A = (a+b) *m A "
  apply(cases A) by (auto simp: costmult_def plus_acost_alt ring_distribs)

lemma costmult_right_mono:
  fixes a :: nat
  shows "a \<le> a' \<Longrightarrow> a *m c \<le> a' *m c"
  unfolding costmult_def less_eq_acost_def
  by (auto simp add: mult_right_mono)  


lemma costmult_left_cong: "a=b \<Longrightarrow> a *m A = b *m A"
  by simp

definition "A_dlas \<equiv> cost ''alloc_raw'' 2 + cost ''list_copy_c'' 1"
definition "C_dlas \<equiv> cost ''add'' 1 + (cost ''list_set'' 1 + (cost ''if'' 1 + (cost ''less'' 1 + cost ''list_length'' 1)))"
definition "\<Phi>_dlas \<equiv> (\<lambda>(xs,l,c). lift_acost (((2*l -length xs)) *m A_dlas))"

lemma pff: "b\<ge>c \<Longrightarrow> (a+b)-c = (a::(string,nat) acost) + (b-c)"
  apply(cases a; cases b; cases c) 
  by (auto simp: less_eq_acost_def)

lemma  dyn_list_append_spec_refines:
  assumes a: "l \<le> c" "c=length bs" "0<length bs"
  shows "dyn_list_append_spec (bs,l,c) x \<le> reclaim (consume (dyn_list_append_spec2 (\<lambda>_. lift_acost (2 *m A_dlas + C_dlas)) (bs,l,c) x) (\<Phi>_dlas (bs,l,c))) \<Phi>_dlas"
  unfolding dyn_list_append_spec_def
  unfolding dyn_list_append_spec2_def
  apply simp
  apply(subst consume_SPEC_eq)
  apply(subst reclaim_if_covered)
  subgoal
    unfolding \<Phi>_dlas_def A_dlas_def C_dlas_def
    apply (auto simp: norm_cost) apply sc_solve  by auto 
  unfolding SPEC_def
  apply(rule gwp_specifies_I)
  unfolding mop_list_length_def SPECc2_alt dyn_list_append_basic_spec_def mop_list_set_def
        dyn_list_double_spec_def SPEC_REST_emb'_conv
  apply(refine_vcg \<open>-\<close>)
  using a 
  subgoal apply auto
    unfolding \<Phi>_dlas_def apply (simp add: lift_acost_propagate[symmetric] lift_acost_minus)
    apply(subst (4) add.commute)
    apply(subst add.assoc)
    apply(subst costmult_add_distrib_left)  
    apply(rule order.trans[rotated])
     apply(rule lift_acost_mono)
     apply(rule zz2)
     apply(rule costmult_right_mono) apply simp 
    unfolding C_dlas_def  apply(simp add: norm_cost) apply(sc_solve) by (simp add: one_enat_def)
         apply auto[1]
        apply auto [1]
  subgoal apply simp (* can't see why auto would loop here *)
    unfolding \<Phi>_dlas_def apply (simp add: lift_acost_propagate[symmetric] lift_acost_minus add.assoc)
    apply(subst (6) add.commute)
    apply(subst add.assoc)
    apply(subst costmult_add_distrib_left)
    apply(subst pff) subgoal apply(rule costmult_right_mono) by auto

    apply(subst costmult_minus_distrib)
    apply simp
    unfolding C_dlas_def A_dlas_def
    apply(simp add: norm_cost)
    apply sc_solve  by(simp add: one_enat_def)
      apply auto [1]
     apply auto [1]
    apply auto [1]
   apply auto [1]
  using assms    apply auto [1]
  done


definition "augment_amor_assn \<Phi> A = (\<lambda>ra r. $\<Phi> ra ** A ra r)"
definition "augment_amor_assn' \<Phi> A = (\<lambda>ra r. $(lift_acost (\<Phi> ra)) ** A ra r)"

lemma invalid_assn_augment_amor_assn: "invalid_assn (augment_amor_assn \<Phi> A) = invalid_assn A"
  unfolding augment_amor_assn_def invalid_assn_def
  unfolding pure_part_def 
  apply auto apply(rule ext) apply(rule ext)
  apply auto
  subgoal  
    using hnr_vcg_aux3 by blast
  subgoal
    by (metis hnr_vcg_aux1 sep_conj_commute) 
  done


thm hn_refine_def
thm hn_refineI
thm hn_refineD

lemma hn_refineI2: 
  assumes "\<And>F s cr M. \<lbrakk> nofailT m ; m = REST M; (\<Gamma>**F) (ll_\<alpha>(s,cr)) \<rbrakk>
          \<Longrightarrow> (\<exists>ra Ca. M ra \<ge> Some Ca \<and>
                     (wp c (\<lambda>r s.  (\<Gamma>' ** R ra r ** F ** GC) (ll_\<alpha> s)) (s,cr+Ca)))"
  shows "hn_refine \<Gamma> c \<Gamma>' R m"  
  apply (auto simp add: hn_refine_def STATE_alt)  
  apply(rule assms) by auto


thm hn_refine_payday
thm hn_refine_payday_reverse

lemma wp_time_frame: "wp c (\<lambda>r s. (G r) (ll_\<alpha> s)) (s,tc)
  \<Longrightarrow> wp c (\<lambda>r s. ($t ** G r) (ll_\<alpha> s)) (s,tc+t)"
  unfolding wp_def apply auto
  unfolding mwp_def apply(cases "run c s")
     apply auto
  unfolding ll_\<alpha>_def
  subgoal for x y z
    apply(rule sep_conjI[where x="(0,t)" and y="(lift_\<alpha>_cost llvm_\<alpha> (z, minus_ecost_cost tc y))"]) 
    subgoal unfolding time_credits_assn_def SND_def by auto 
    subgoal apply simp done
    subgoal by (simp add: sep_disj_acost_def sep_disj_enat_def sep_disj_prod_def) 
    subgoal
      by (smt \<open>\<lbrakk>run c s = SUCC x y z; G x (lift_\<alpha>_cost llvm_\<alpha> (z, minus_ecost_cost tc y)); le_cost_ecost y tc\<rbrakk> \<Longrightarrow> (0, t) ## lift_\<alpha>_cost llvm_\<alpha> (z, minus_ecost_cost tc y)\<close>
              add.commute cost_ecost_minus_add_assoc2 lift_\<alpha>_cost_def old.prod.case plus_prod_eqI prod.sel(1) sep_disj_prod_def unique_zero_simps(3))
    done
  subgoal
    using cost_ecost_add_increasing2 by blast
  done
 
lemma meh: "b \<ge> lift_acost a \<Longrightarrow> Ca \<le> b - lift_acost a\<Longrightarrow> Ca + lift_acost a \<le> b"
  apply(cases b; cases Ca; cases a) apply auto
  using plus_minus_adjoint_ecost by blast 

lemma
   hn_refine_reclaimday: 
   assumes
     nofail: "nofailT m \<Longrightarrow> nofailT (reclaim m (lift_acost o \<Phi>))"
     and as: "hn_refine \<Gamma> c \<Gamma>' G (reclaim m (lift_acost o \<Phi>))"
   shows "hn_refine \<Gamma> c \<Gamma>' (augment_amor_assn' \<Phi> G) m"
proof (rule hn_refineI2)
  fix F s cr M
  assume n: "nofailT m"
      and m: "m = SPECT M" and H: "(\<Gamma> \<and>* F) (ll_\<alpha> (s, cr))"

  from n nofail have z: "nofailT (reclaim m (lift_acost o \<Phi>))" by simp
  then obtain M' where kl: " (reclaim m (lift_acost o \<Phi>)) = SPECT M'"   
    unfolding nofailT_def 
    by force

  from z m have Z: "(\<forall>x t'. M x = Some t' \<longrightarrow> lift_acost (\<Phi> x) \<le> t')" apply(simp only: nofailT_reclaim) by auto

  from as[unfolded hn_refine_def STATE_def, rule_format, OF z, OF kl H] obtain ra Ca where
    ff: "Some Ca \<le> M' ra" and wp: "wp c (\<lambda>r s. (\<Gamma>' \<and>* G ra r \<and>* F \<and>* GC) (ll_\<alpha> s)) (s, cr + Ca)" by blast

  from ff have "M' ra \<noteq> None"
    by (metis less_eq_option_Some_None)
  with kl[symmetric] have mra: "M ra \<noteq> None" unfolding m
    apply(cases "M ra") apply auto unfolding Sup_nrest_def apply (auto split: if_splits) 
    by (smt SUP_bot_conv(2) Sup_empty empty_Sup fun_upd_apply mem_Collect_eq option.distinct(1))

  then obtain mra where Mra: "M ra = Some mra" by auto

  have nene: "M' ra \<le> Some (mra - lift_acost (\<Phi> ra))"
    using kl unfolding m  apply (auto split: if_splits)
    unfolding Sup_nrest_def apply (auto split: if_splits)
    apply(rule Sup_least) apply auto 
    by (simp add: Mra) 

  with ff have ff': " Some Ca \<le>Some (mra - lift_acost (\<Phi> ra))" by(rule order.trans)

  show "\<exists>ra Ca. Some Ca \<le> M ra \<and> wp c (\<lambda>r s. (\<Gamma>' \<and>* augment_amor_assn' \<Phi> G ra r \<and>* F \<and>* GC) (ll_\<alpha> s)) (s, cr + Ca)"
    apply(rule exI[where x=ra])
    apply(rule exI[where x="Ca+lift_acost (\<Phi> ra)"])
    apply safe
    subgoal        
      using ff' unfolding Mra apply simp
      apply(rule meh) apply auto using Z[rule_format, of ra mra] Mra by simp
    subgoal using wp_time_frame[OF wp, where t="lift_acost (\<Phi> ra)"] unfolding augment_amor_assn'_def
      by (auto simp:  sep_conj_left_commute sep_conj_commute add.assoc add.left_commute add.commute)
    done
qed


lemma
   brut: 
   assumes
     nofail: "\<And>x r. nofailT (m x r) \<Longrightarrow> nofailT (reclaim (consume (m x r) ((lift_acost o \<Phi>) x)) (lift_acost o \<Phi>))"
     and as: "hn_refine (G x x' ** F' r r') (c x' r') (invalid_assn G x x' ** F' r r') G (reclaim (consume (m x r) ((lift_acost o \<Phi>) x)) (lift_acost o \<Phi>))"
   shows
  "hn_refine ((augment_amor_assn (lift_acost o \<Phi>) G) x x' ** F' r r') (c x' r') (invalid_assn G x x' ** F' r r') (augment_amor_assn (lift_acost o \<Phi>) G) (m x r)"
  unfolding augment_amor_assn_def
  apply(subst sep_conj_assoc) apply simp
  apply(fold augment_amor_assn'_def)
  apply(rule hn_refine_payday_reverse)
  apply(rule hn_refine_reclaimday)
  subgoal apply (simp add: nofailT_consume) using nofail by simp
  subgoal using as by simp
  done


lemma
   brut2: 
  "hn_refine (G x x' ** F' r r') (c x' r') (invalid_assn G x x' ** F' r r') G (reclaim (consume (m x r) (\<Phi> x)) \<Phi>)
    \<Longrightarrow> hn_refine ((augment_amor_assn \<Phi> G) x x' ** F' r r') (c x' r') (invalid_assn (augment_amor_assn \<Phi> G) x x' ** F' r r') (augment_amor_assn \<Phi> G) (m x r)"
  sorry



definition dyn_array_append_impl :: "'b ptr \<times> 'c word \<times> 'd word \<Rightarrow> 'b \<Rightarrow> ('b ptr \<times> 'c word \<times> 'd word) llM "  where
  "dyn_array_append_impl = undefined"

lemma AA: "hn_refine (L (bs,n) (p,m) ** A x x')
        (dyn_array_append_impl (p,m) x')
            (invalid_assn L (bs,n) (p,m) ** A x x')
            L (dyn_list_append_spec (bs,n) x)"
  sorry

 

thm hn_refine_ref[OF AA dyn_list_append_spec_refines, THEN brut[where m="dyn_list_append_spec2 (\<lambda>_. lift_acost (2 *m A_dlas + C_dlas))" and c=dyn_array_append_impl and \<Phi>="\<Phi>_dlas"]]

thm  brut[where m="dyn_list_append_spec2 (\<lambda>_. lift_acost (2 *m A_dlas + C_dlas))" and c=dyn_array_append_impl and \<Phi>="\<Phi>_dlas", OF _ hn_refine_ref[OF AA dyn_list_append_spec_refines]]


term array_assn

definition dyn_array_raw_assn where
  "dyn_array_raw_assn A \<equiv> \<lambda>(bs,l,c) (p,l',c'). array_assn A bs p ** snat_assn l l' ** snat_assn c c'"
                                            
lemma AA_real: "hn_refine (dyn_array_raw_assn A (bs,l,c) (p,l',c') ** A x x')
        (dyn_array_append_impl (p,l',c') x')
            (invalid_assn (dyn_array_raw_assn A) (bs,l,c) (p,l',c') ** A x x')
           (dyn_array_raw_assn A) (dyn_list_append_spec (bs,l,c) x)"
  sorry



thm hn_refine_ref[ OF AA_real dyn_list_append_spec_refines, THEN brut[where m="dyn_list_append_spec2 (\<lambda>_. lift_acost (2 *m A_dlas + C_dlas))" and c=dyn_array_append_impl and \<Phi>="\<Phi>_dlas"], no_vars]



definition dyn_array_raw_armor_assn where
  "dyn_array_raw_armor_assn \<equiv> \<lambda>A (bs, l, c) (p, l', c').  $\<Phi>_dlas (bs, l, c) \<and>* dyn_array_raw_assn A (bs, l, c) (p, l', c')"

lemma dyn_array_raw_armor_assn_alt: "dyn_array_raw_armor_assn A = augment_amor_assn \<Phi>_dlas (dyn_array_raw_assn A)"
  unfolding augment_amor_assn_def dyn_array_raw_armor_assn_def 
  apply (rule ext) 
  apply (rule ext) by simp


lemma LLL: "invalid_assn (dyn_array_raw_armor_assn A) = invalid_assn (dyn_array_raw_assn A)"
  unfolding dyn_array_raw_armor_assn_alt
  apply(rule invalid_assn_augment_amor_assn)
  done

lemma YEAH: "\<lbrakk>l \<le> c; c = length bs; 0 < length bs\<rbrakk>
\<Longrightarrow> hn_refine (hn_ctxt (dyn_array_raw_armor_assn A) (bs, l, c) (p, l', c') \<and>* hn_ctxt A r r')
     (dyn_array_append_impl $ (p, l', c') $ r')
     (hn_invalid (dyn_array_raw_armor_assn A) (bs, l, c) (p, l', c') \<and>* hn_ctxt A r r')
       (dyn_array_raw_armor_assn A)
      (PR_CONST (dyn_list_append_spec2 (\<lambda>_. lift_acost (2 *m A_dlas + C_dlas))) $ (bs, l, c) $ r) "
  unfolding hn_ctxt_def APP_def PR_CONST_def
  unfolding LLL
  unfolding dyn_array_raw_armor_assn_alt apply (simp only: prod.case)
  apply(rule brut[where m="dyn_list_append_spec2 (\<lambda>_. lift_acost (2 *m A_dlas + C_dlas))" and c=dyn_array_append_impl and \<Phi>="\<Phi>_dlas"])
  apply(rule hn_refine_ref)
   apply(rule AA_real)
  apply(rule dyn_list_append_spec_refines)
    apply auto
  done



lemma dyn_list_append_spec2_refines: "((bs,l,c),as)\<in> dyn_list_rel \<Longrightarrow> (r',r)\<in>Id \<Longrightarrow> dyn_list_append_spec2 (\<lambda>_. T) (bs, l, c) r' \<le> \<Down>dyn_list_rel (mop_list_append T as r)"
  unfolding mop_list_append_def dyn_list_rel_alt
  apply(subst SPECT_assign_emb')
  unfolding conc_fun_br
  apply(subst SPEC_REST_emb'_conv[symmetric])
  unfolding dyn_list_append_spec2_def  apply simp
  apply(rule SPEC_leq_SPEC_I_even_stronger)
  unfolding in_br_conv
  by (auto simp add: take_Suc_conv_app_nth) 




lemma YEAH2: "hn_refine (hn_ctxt E x x' \<and>* hn_ctxt A r r')
     (dyn_array_append_impl $ x' $ r')
     (hn_invalid E x x' \<and>* hn_ctxt A r r')
       (F A)
      (PR_CONST AE $ x $ r) "
  sorry

lemma faz: "hn_refine (hn_val E a ai \<and>* hn_val bool1_rel b bi) (ll_xor $ ai $ bi) (hn_val E a ai \<and>* hn_val bool1_rel b bi) bool1_assn (PR_CONST (SPECc2 ''xor'' op_neq) $ a $ b)"
  sorry
thm faz[to_hfref]


lemma YEAH3: "\<lbrakk>(case x of (bs,l,c) \<Rightarrow> l \<le> c \<and> c = length bs \<and> 0 < length bs)\<rbrakk>
  \<Longrightarrow> hn_refine (hn_ctxt (dyn_array_raw_armor_assn A) x x' \<and>* hn_ctxt A r r')
     (dyn_array_append_impl $ x' $ r')
     (hn_invalid (dyn_array_raw_armor_assn A) x x' \<and>* hn_ctxt A r r')
       (dyn_array_raw_armor_assn A)
      (PR_CONST (dyn_list_append_spec2 (\<lambda>_. lift_acost (2 *m A_dlas + C_dlas))) $ x $ r) "
  sorry

thm YEAH2[to_hfref]
lemmas RICHTIGCOOL = YEAH3[to_hfref]

lemma dyn_list_append_spec2_refines_fref: "(uncurry (PR_CONST (dyn_list_append_spec2 (\<lambda>_. T))), uncurry (PR_CONST (mop_list_append T)))
        \<in> dyn_list_rel \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>dyn_list_rel\<rangle>nrest_rel" 
  sorry

thm dyn_list_append_spec2_refines[to_fref]

thm RICHTIGCOOL dyn_list_append_spec2_refines_fref[where T="lift_acost (2 *m A_dlas + C_dlas)"]


definition "dyn_array_assn A = hr_comp (dyn_array_raw_armor_assn A) dyn_list_rel"

lemma dyn_array_raw_armor_: "hr_comp (dyn_array_raw_armor_assn A) dyn_list_rel = dyn_array_assn A"
  unfolding dyn_array_assn_def by auto

 

lemma dyn_list_rel_sv[relator_props]: "single_valued dyn_list_rel"
  unfolding dyn_list_rel_alt by(rule br_sv)  

text \<open>this makes the tactic \<open>solve_attains_sup\<close> solve the supattains sidecondition, 
  because \<open>tagged_solver\<close> can then solve the single_valued goal. \<close>

declare dyn_list_rel_def[simp] \<comment> \<open>don't know how to tag this fact such that FCOMP picks it up
    correctly\<close>
declare dyn_array_raw_armor_[fcomp_norm_unfold]
thm RICHTIGCOOL[FCOMP dyn_list_append_spec2_refines_fref[where T="lift_acost (2 *m A_dlas + C_dlas)"]]
lemmas FFF = RICHTIGCOOL[FCOMP dyn_list_append_spec2_refines_fref]

declare dyn_list_rel_def[simp del]

thm FFF




subsection \<open>The Refinement Relation between abstract dynamic lists and lists\<close>

definition "\<Phi>_dyn bsl n = 2 * bsl - n"

definition "dyn_abs = {( ((bs,n),c) , as) | bs n c as. take n bs = as \<and> n \<le> length bs \<and>
                                                  c = \<Phi>_dyn (length bs) n }"


lemma dyn_abs_alt: "dyn_abs = br (\<lambda>((bs,n),c). take n bs) (\<lambda>((bs,n),c). n \<le> length bs \<and>
                                                  c = \<Phi>_dyn (length bs) n)"
  unfolding dyn_abs_def br_def by auto


subsection \<open>The implementation of the empty list\<close>

definition "empty_list_spec T = REST [[] \<mapsto> T]"


definition dyn_array_init_spec where
  "dyn_array_init_spec ilen = SPEC (\<lambda>((bs,n),c). n=0 \<and> c = 2 * length bs \<and> length bs = ilen) 
                                       (\<lambda>((bs,n),c). (enat (length bs)) *m cost ''init_raw'' 1
                                                         + (enat c) *m cost ''amor'' 1)"



definition "R ilen = 0(''empty_list'':= (enat ilen) *m cost ''init_raw'' 1
                                                         + (enat (\<Phi>_dyn ilen 0)) *m cost ''amor'' 1)"

lemma "dyn_array_init_spec ilen \<le> \<Down>dyn_abs (timerefine (R ilen) (empty_list_spec (cost ''empty_list'' 1)))"
  unfolding dyn_array_init_spec_def
    empty_list_spec_def
  apply(subst timerefine_SPECT_map)
  unfolding dyn_abs_alt SPECT_assign_emb'
  unfolding conc_fun_br
  apply (auto split: prod.splits)
  unfolding R_def apply(simp add: norm_cost)
  apply(subst SPEC_REST_emb'_conv[symmetric])
  apply(rule SPEC_leq_SPEC_I_even_stronger)
  subgoal apply (auto simp: \<Phi>_dyn_def) done
  subgoal
    by (auto split: prod.splits simp: \<Phi>_dyn_def)
  done


subsection \<open>The implementation of the empty list\<close>

definition "append_spec T xs x = REST [xs @ [x] \<mapsto> T]"


term MIf

definition dyn_array_push_raw where
  "dyn_array_push_raw \<equiv> \<lambda>((bs,n),c) x. SPECT [ ( (bs[n:=x],n+1),c) \<mapsto> cost ''push_raw'' 1]"


definition dyn_array_push where
  "dyn_array_push \<equiv> \<lambda>((bs,n),c) x. do {
          lenbs \<leftarrow> SPECT [length bs \<mapsto> cost ''list_length'' 1];
          if\<^sub>N SPECc2 ''eq'' (=) lenbs n then doN {
            ((bs',n'),c') \<leftarrow> dyn_array_double ((bs,n),c);
            dyn_array_push_raw ((bs',n'),c') x
          } else do {
            dyn_array_push_raw ((bs,n),c) x
          }
        }"







subsection \<open>end result\<close>

definition "dyn_abs2 = {( ((bs,n)) , as) | bs n as. take n bs = as \<and> n \<le> length bs }"


term array_assn
definition "dyn_array_assn RR \<equiv> \<lambda>as (p,n). EXS bs m. array_assn RR bs p ** snat_assn m n
            ** \<up>( ((bs,m), as) \<in> dyn_abs2) " 


definition "dyn_array_assn_raw RR \<equiv> \<lambda>(as,m) (p,n). array_assn RR as p ** snat_assn m n"

definition "\<Phi>_da las m = cost ''kA'' 1"

definition "dyn_array_assn_raw_d RR \<equiv> \<lambda>(as,m) (p,n). array_assn RR as p ** snat_assn m n ** $(\<Phi>_da (length as) m)" 


term invalid_assn

definition "dyn_array_push_spec \<equiv> \<lambda>(as,m) x. do {
          ASSERT (m\<le>length as);
          RETURNT (as,m)
      }"


term bindT


definition "balances T m t = (case m of FAILi \<Rightarrow> FAILT 
                                            | SPECT M \<Rightarrow> SPECT (\<lambda>x. (case M x of None \<Rightarrow> None
                                                                             | Some tt \<Rightarrow> Some ((T + tt) - t x))))"

lemma "hn_refine G c G' RR (reclaim m t) \<Longrightarrow> hn_refine G c G' (\<lambda>ra r. RR ra r ** $(t ra)) m" 

  unfolding hn_refine_def
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply(drule blaD)
  sorry

definition consume_after where
  "consume_after M t = doN { x \<leftarrow> M ; consume (RETURNT x) (t x)  }"

lemma "hn_refine (dyn_array_assn_raw RR (as,m) (p,n) ** RR x x')
             (dyn_array_push_impl (p,n) x')
          (invalid_assn (dyn_array_assn_raw RR) (as,m) (p,n) ** RR x x') (dyn_array_assn_raw RR)
            (consume_after (dyn_array_push_spec (as,m) x) (\<lambda>(as',m'). \<Phi>_da (length as) m - \<Phi>_da (length as') m'))"
  sorry



lemma "hn_refine (dyn_array_assn RR as (p,n) ** RR x x')
             (dyn_array_push_impl (p,n) x')
          (invalid_assn (dyn_array_assn RR) as (p,n) ** RR x x') (dyn_array_assn RR)
            (append_spec T as x)"
  sorry



lemma "hn_refine (dyn_array_assn RR as (p,n) ** RR x x')
             (dyn_array_push_impl (p,n) x')
          (invalid_assn (dyn_array_assn RR) as (p,n) ** RR x x') (dyn_array_assn RR)
            (append_spec T as x)"
  sorry





end