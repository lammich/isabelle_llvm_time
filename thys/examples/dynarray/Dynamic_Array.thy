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

end

  
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
              length bs' = 2 * length bs \<and> l' = l \<and> l\<le>c' \<and> c'=length bs')
        (\<lambda>(bs',l',c'). cost ''dyn_list_double_c'' (enat c')) 
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
  sorry


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



definition dyn_list_append where
  "dyn_list_append \<equiv> \<lambda>(bs,l,c) x. doN {
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



text \<open>The abstract program A for empty list:\<close>


definition mop_list_emptylist where
  "mop_list_emptylist T = SPECT [ [] \<mapsto> T ]"


text \<open>The abstract program B for empty dynamic list, (in dynamic array currencies) :\<close>


definition "dyn_list_empty_spec T = SPEC (\<lambda>(ls,l,c). l=0 \<and> c=8 \<and> c = length ls) (\<lambda>_. T)"


lemma timerefine_dyn_list_empty_spec: "timerefine TR (dyn_list_empty_spec T) = dyn_list_empty_spec (timerefineA TR T)"
  unfolding dyn_list_empty_spec_def
  by (auto split: prod.splits simp: SPEC_timerefine_conv)

definition dyn_list_new_raw where
  "dyn_list_new_raw = do {
       dst \<leftarrow> mop_list_init_raw (\<lambda>n. cost ''list_init_c'' 8) 8;
       RETURNT (dst,0,8)
    }"

definition dyn_list_new where
  "dyn_list_new ini = do {
       dst \<leftarrow> mop_list_init (\<lambda>n. cost ''list_init_c'' 8) ini 8;
       RETURNT (dst,0,8)
    }"



text \<open>Refinement THEOREM A-B\<close>

abbreviation "TR_dyn_list_new ==  (0(''list_empty'':=cost ''list_init_c'' 8))"

lemma dyn_list_new_refines:
 "dyn_list_new ini \<le> \<Down>dyn_list_rel (\<Down>\<^sub>C TR_dyn_list_new (mop_list_emptylist (cost ''list_empty'' 1)))"
  unfolding mop_list_emptylist_def dyn_list_new_def dyn_list_rel_alt
  apply (simp add: timerefine_SPECT_map norm_cost )                   
  apply (simp add: SPECT_assign_emb' conc_fun_br)
  apply(rule gwp_specifies_I)
  apply(refine_vcg \<open>-\<close>)    by(auto simp: emb'_def)



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




lemma "reclaim (SPECT M) (t::_\<Rightarrow>ecost) = SPECT rM
    \<Longrightarrow> (rM x = Some tt) \<longleftrightarrow> M x = Some (tt - t x)"
  apply(cases "nofailT (reclaim (SPECT M) t)")
  subgoal
    unfolding nofailT_reclaim
    apply simp
    apply(drule nrest_Sup_SPECT_D[where x=x]) apply auto
    oops
  



definition dyn_list_append_spec where
  "dyn_list_append_spec T \<equiv> \<lambda>(bs,l,c) x. SPEC (\<lambda>(bs',l',c'). l'\<le>c' \<and> c'=length bs' \<and> l'=l+1 \<and> length bs' \<ge> length bs
                                                          \<and> take l bs' = take l bs \<and> bs' ! l = x) (\<lambda>_. T)"

lemma timerefine_dyn_list_append_spec: "timerefine TR (dyn_list_append_spec T dl x) = dyn_list_append_spec (timerefineA TR T) dl x"
  unfolding dyn_list_append_spec_def
  by (auto split: prod.splits simp: SPEC_timerefine_conv)


lemma "((bs,l,c),as)\<in>dyn_list_rel \<Longrightarrow> (x',x) \<in> Id
 \<Longrightarrow> dyn_list_append_spec T (bs,l,c) x'
         \<le> \<Down>dyn_list_rel (timerefine (0(''list_append'':=T)) (mop_list_append (cost ''list_append'' 1) as x))"
  unfolding dyn_list_append_spec_def mop_list_append_def
  apply(subst timerefine_SPECT_map)
  apply(subst SPECT_assign_emb')
  unfolding dyn_list_rel_alt
    apply(subst conc_fun_br)
  apply(subst SPEC_REST_emb'_conv[symmetric])
  apply safe
  apply(rule SPEC_leq_SPEC_I_even_stronger)
  subgoal by (auto simp: in_br_conv take_Suc_conv_app_nth)
  subgoal apply auto 
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

definition "A_dlas \<equiv> cost ''dyn_list_double_c'' (2::nat)"
definition "C_dlas \<equiv> cost ''add'' 1 + (cost ''list_set'' 1 + (cost ''if'' 1 + (cost ''less'' 1 + cost ''list_length'' 1)))"
definition "\<Phi>_dlas \<equiv> (\<lambda>(xs,l,c). (((2*l -length xs)) *m A_dlas))"
abbreviation "\<Phi>_dlas' \<equiv> lift_acost o \<Phi>_dlas"

lemma pff: "b\<ge>c \<Longrightarrow> (a+b)-c = (a::(string,nat) acost) + (b-c)"
  apply(cases a; cases b; cases c) 
  by (auto simp: less_eq_acost_def)

lemma  dyn_list_append_spec_refines:
  assumes a: "l \<le> c" "c=length bs" "0<length bs"
  shows "dyn_list_append (bs,l,c) x \<le> reclaim (consume (dyn_list_append_spec (lift_acost (2 *m A_dlas + C_dlas)) (bs,l,c) x) (\<Phi>_dlas' (bs,l,c))) \<Phi>_dlas'"
  unfolding dyn_list_append_spec_def
  unfolding dyn_list_append_def
  apply simp
  apply(subst consume_SPEC_eq)
  apply(subst reclaim_if_covered)
  subgoal
    unfolding \<Phi>_dlas_def A_dlas_def C_dlas_def
    apply (auto simp: norm_cost) apply(subst add.commute) apply(subst (2) add.assoc) apply(subst cost_same_curr_add)
    apply(simp add: add.assoc)  
      apply sc_solve  by auto
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
    apply(subst (5) add.commute)
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
  subgoal by force
  using assms  
   apply auto 
  done



definition "E_dlas \<equiv> cost ''list_init_c'' 8" (* the cost to initialize the empty list *)

lemma cost_mult_zero_enat[simp]:"(0::enat) *m m = (0) "
  by(auto simp: zero_acost_def costmult_def) 
lemma cost_mult_zero_nat[simp]: "(0::nat) *m m = (0) "
  by(auto simp: zero_acost_def costmult_def) 
 

lemma  dyn_list_new_raw_refines:
  shows "dyn_list_new_raw \<le> reclaim (consume (dyn_list_empty_spec (lift_acost E_dlas)) 0) \<Phi>_dlas'"
  unfolding dyn_list_new_raw_def mop_list_init_raw_def
  unfolding dyn_list_empty_spec_def
  apply(subst consume_SPEC_eq)
  apply(subst reclaim_if_covered)
  subgoal unfolding \<Phi>_dlas_def  by (auto simp: lift_acost_def less_eq_acost_def zero_acost_def)
  unfolding SPEC_def
  unfolding autoref_tag_defs
  apply(rule gwp_specifies_I)
  apply(refine_vcg \<open>-\<close>)
  subgoal 
    unfolding \<Phi>_dlas_def  apply (auto simp: lift_acost_zero E_dlas_def lift_acost_cost needname_minus_absorb) 
    apply sc_solve by auto
  subgoal by simp
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


lemma invalid_assn_augment'_amor_assn: "invalid_assn (augment_amor_assn' \<Phi> A) = invalid_assn A"
  unfolding augment_amor_assn'_def invalid_assn_def
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

term the_enat

lemma extract_lift_acost_if_less_infinity:
  assumes
    less_infinity: "\<And>x. the_acost t x < \<infinity>" 
  obtains t' where "lift_acost t' = t"
proof 
  show "lift_acost (acostC (\<lambda>x. the_enat (the_acost t x))) = t"
    unfolding lift_acost_def
    apply(cases t)
    apply simp
    using less_infinity
    by (metis (mono_tags) acost.sel acost_eq_I comp_apply less_infinityE the_enat.simps)
qed

definition "finite_cost t \<equiv> \<forall>x. the_acost t x < \<infinity>"

lemma finite_costD: "finite_cost t \<Longrightarrow> the_acost t x < \<infinity>"
  unfolding finite_cost_def by auto
   
lemma finite_costI: "(\<And>x. the_acost t x < \<infinity>) \<Longrightarrow> finite_cost t"
  unfolding finite_cost_def by auto


lemma finite_cost_lift_acost: "finite_cost (lift_acost x)"
  unfolding finite_cost_def lift_acost_def by auto


lemma hn_refine_payday_reverse_alt:
  fixes m :: " ('d, (char list, enat) acost) nrest"
  assumes 
    a: "finite_cost t" 
  and "hn_refine \<Gamma> c \<Gamma>' R (consume m t)"
  shows "hn_refine ($t \<and>* \<Gamma>) c \<Gamma>' R m"
proof -
  from extract_lift_acost_if_less_infinity[OF a[THEN finite_costD]]
  obtain t' where t: "t = lift_acost t'" by blast


  show ?thesis
    unfolding t apply(rule hn_refine_payday_reverse)
    apply(fold t)
    apply(fact)
    done
qed

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
 
lemma meh_special: "b \<ge> lift_acost a \<Longrightarrow> Ca \<le> b - lift_acost a\<Longrightarrow> Ca + lift_acost a \<le> b"
  apply(cases b; cases Ca; cases a) apply auto
  using plus_minus_adjoint_ecost by blast 


lemma meh: "b \<ge> (a::ecost) \<Longrightarrow> Ca \<le> b - a\<Longrightarrow> Ca + a \<le> b"
  apply(subst plus_minus_adjoint_ecost[symmetric]) by simp_all


lemma
   hn_refine_reclaimday: 
   assumes
     nofail: "nofailT m \<Longrightarrow> nofailT (reclaim m \<Phi>)"
     and as: "hn_refine \<Gamma> c \<Gamma>' G (reclaim m \<Phi>)"
   shows "hn_refine \<Gamma> c \<Gamma>' (augment_amor_assn \<Phi> G) m"
proof (rule hn_refineI2)
  fix F s cr M
  assume n: "nofailT m"
      and m: "m = SPECT M" and H: "(\<Gamma> \<and>* F) (ll_\<alpha> (s, cr))"

  from n nofail have z: "nofailT (reclaim m \<Phi>)" by simp
  then obtain M' where kl: " (reclaim m \<Phi>) = SPECT M'"   
    unfolding nofailT_def 
    by force

  from z m have Z: "(\<forall>x t'. M x = Some t' \<longrightarrow> \<Phi> x \<le> t')" apply(simp only: nofailT_reclaim) by auto

  from as[unfolded hn_refine_def STATE_def, rule_format, OF z, OF kl H] obtain ra Ca where
    ff: "Some Ca \<le> M' ra" and wp: "wp c (\<lambda>r s. (\<Gamma>' \<and>* G ra r \<and>* F \<and>* GC) (ll_\<alpha> s)) (s, cr + Ca)" by blast

  from ff have "M' ra \<noteq> None"
    by (metis less_eq_option_Some_None)
  with kl[symmetric] have mra: "M ra \<noteq> None" unfolding m
    apply(cases "M ra") apply auto unfolding Sup_nrest_def apply (auto split: if_splits) 
    by (smt SUP_bot_conv(2) Sup_empty empty_Sup fun_upd_apply mem_Collect_eq option.distinct(1))

  then obtain mra where Mra: "M ra = Some mra" by auto

  have nene: "M' ra \<le> Some (mra - \<Phi> ra)"
    using kl unfolding m  apply (auto split: if_splits)
    unfolding Sup_nrest_def apply (auto split: if_splits)
    apply(rule Sup_least) apply auto 
    by (simp add: Mra) 

  with ff have ff': " Some Ca \<le>Some (mra - \<Phi> ra)" by(rule order.trans)

  show "\<exists>ra Ca. Some Ca \<le> M ra \<and> wp c (\<lambda>r s. (\<Gamma>' \<and>* augment_amor_assn \<Phi> G ra r \<and>* F \<and>* GC) (ll_\<alpha> s)) (s, cr + Ca)"
    apply(rule exI[where x=ra])
    apply(rule exI[where x="Ca+\<Phi> ra"])
    apply safe
    subgoal        
      using ff' unfolding Mra apply simp
      apply(rule meh) apply auto using Z[rule_format, of ra mra] Mra by simp
    subgoal using wp_time_frame[OF wp, where t="\<Phi> ra"] unfolding augment_amor_assn_def
      by (auto simp:  sep_conj_left_commute sep_conj_commute add.assoc add.left_commute add.commute)
    done
qed


lemma
   hn_refine_amortization: 
   assumes
     nofail: "\<And>x r. nofailT (m x r) \<Longrightarrow> nofailT (reclaim (consume (m x r) (\<Phi> x)) \<Phi>)"
  and finite: "\<And>x. finite_cost (\<Phi> x)" 
     and as: "hn_refine (G x x' ** F' r r') (c x' r') (invalid_assn G x x' ** F' r r') G (reclaim (consume (m x r) (\<Phi> x)) \<Phi>)"
   shows
  "hn_refine ((augment_amor_assn \<Phi> G) x x' ** F' r r') (c x' r') (invalid_assn (augment_amor_assn \<Phi> G) x x' ** F' r r') (augment_amor_assn \<Phi> G) (m x r)"
  unfolding invalid_assn_augment_amor_assn
  unfolding augment_amor_assn_def
  apply(subst sep_conj_assoc) apply simp
  apply(fold augment_amor_assn_def)
  apply(rule hn_refine_payday_reverse_alt[OF finite])
  apply(rule hn_refine_reclaimday)
  subgoal apply (simp add: nofailT_consume) using nofail by simp
  subgoal using as by simp
  done

(* TODO: move *)



lemma timerefineA_mono:
    assumes "wfR'' R"
    shows "t \<le> t' \<Longrightarrow> timerefineA R t \<le> timerefineA R (t'::ecost)"
  apply (auto simp: less_eq_acost_def timerefineA_def split: nrest.splits option.splits simp: le_fun_def)
  proof (goal_cases)
    case (1 ac)
    then have l: "\<And>ac. the_acost t ac \<le>  the_acost t' ac"
      apply(cases t; cases t') unfolding less_eq_acost_def  
      by auto
    show ?case
      apply(rule Sum_any_mono)
      subgoal using l apply(rule ordered_semiring_class.mult_right_mono) by (simp add: needname_nonneg)
      apply(rule wfR_finite_mult_left2) by fact
  qed 


locale dyn_list_impl =
  fixes dyn_list_append2
    and dyn_array_append_impl :: "'f \<Rightarrow> 'i \<Rightarrow> 'f llM" 

    and dynamiclist_empty2 :: "((('e::llvm_rep) list \<times> nat \<times> nat),ecost) nrest"
    and dynamiclist_empty_impl :: "'f llM"

    and TR_dynarray
    and dyn_array_raw_assn :: "('e \<Rightarrow> 'i \<Rightarrow> assn)  \<Rightarrow> 'e list \<times> nat \<times> nat \<Rightarrow> 'f \<Rightarrow> assn"
  assumes 
        wfR_TR_dynarray: "wfR'' TR_dynarray"                           
    and TR_dynarray_keeps_finite: "\<And>\<Phi>. finite {x. the_acost \<Phi> x \<noteq>0} \<Longrightarrow> finite_cost \<Phi> \<Longrightarrow> finite_cost (timerefineA TR_dynarray \<Phi>)"
    and dyn_list_append2_refine: "dyn_list_append2 dl x \<le> \<Down>\<^sub>C TR_dynarray (dyn_list_append dl x)"

    and AA_real: "hn_refine (dyn_array_raw_assn A (bs,l,c) da' ** A x x')
                        (dyn_array_append_impl da' x')
                      (invalid_assn (dyn_array_raw_assn A) (bs,l,c) da' ** A x x')
                        (dyn_array_raw_assn A) (dyn_list_append2 (bs,l,c) x)"

    and emptylist2_real: "(uncurry0 dynamiclist_empty_impl, uncurry0 dynamiclist_empty2) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a  dyn_array_raw_assn A"
    and emptylist2_refine: "dynamiclist_empty2 \<le> \<Down>\<^sub>C TR_dynarray dyn_list_new_raw"
begin 



thm dyn_list_append_spec_refines[no_vars]

abbreviation "\<Phi>_d == \<lambda>x. timerefineA TR_dynarray  (\<Phi>_dlas' x)"
abbreviation "abstract_advertised_cost == lift_acost (2 *m A_dlas + C_dlas)"
abbreviation "abstracted_advertised_cost == timerefineA TR_dynarray abstract_advertised_cost"


thm pw_inresT_Sup


lemma reclaim_SPEC: "(\<And>x. \<Phi> x \<Longrightarrow> T x \<ge> t x) \<Longrightarrow> reclaim (SPEC \<Phi> T) t = SPEC \<Phi> (\<lambda>x. T x - t x)"
  unfolding SPEC_def apply simp
  unfolding Sup_nrest_def apply auto 
  apply(rule ext) apply auto 
  subgoal for v apply(rule antisym)
    subgoal apply(rule Sup_least) by auto
    subgoal apply(rule Sup_upper2[where u="[v\<mapsto>T v - t v] v"])
       apply(rule image_eqI[where x="[v \<mapsto> T v - t v]"]) apply simp by auto
    done
  subgoal 
    by (smt SUP_bot_conv(2) Sup_empty empty_Sup fun_upd_apply mem_Collect_eq) 
  done


thm Sum_any.distrib[no_vars]

lemma finite_nonzero_minus: "finite {a. g a \<noteq> 0} \<Longrightarrow> finite {a. h a \<noteq> (0::enat)} \<Longrightarrow> finite {a. g a - h a \<noteq> 0}"
  by (metis (mono_tags, lifting) Collect_mono_iff idiff_0 rev_finite_subset)


lemma sum_minus_distrib_enat:
  assumes "\<And>a. g a \<ge> (h a::enat)"
  shows "finite A \<Longrightarrow> sum (\<lambda>a. g a - h a) A = sum g A - sum h A" 
proof (induct rule: finite_induct)
  case (insert x F)
  have *: "sum g F \<ge> sum h F"
    apply(rule sum_mono) using assms by auto
  have "(\<Sum>a\<in>insert x F. g a - h a)
      = (g x - h x) + (\<Sum>a\<in>F. g a - h a)"  
    by (simp add: insert.hyps(1) insert.hyps(2))
  also have "\<dots> = (g x - h x) + (sum g F - sum h F)"
    by (simp add: insert.hyps(3))
  also have "\<dots> = (g x + sum g F) - (h x + sum h F)"
    using assms[of x] * 
    by (metis add.commute add_diff_assoc_enat assms minus_plus_assoc2) 
  also have "\<dots> = sum g (insert x F) - sum h (insert x F)"
    by (simp add: insert.hyps(1) insert.hyps(2))
  finally show ?case .
qed simp  

lemma Sum_any_minus_distrib_enat:
  assumes "finite {a. g a \<noteq> 0}" "finite {a. h a \<noteq> 0}"
  assumes "\<And>a. g a \<ge> (h a :: enat)"
  shows "Sum_any (\<lambda>a. g a - h a) = Sum_any g - Sum_any h"
proof -
  have z: "{a. g a - h a \<noteq> 0} \<subseteq> {a. g a \<noteq> (0::enat)}"
    by auto

  have "Sum_any (\<lambda>a. g a - h a) = sum (\<lambda>a. g a - h a)  {a. g a \<noteq> 0}"
    apply  (rule Sum_any.expand_superset) 
    apply(rule assms(1))
    apply(rule z)
    done
  also have "\<dots> = sum g {a. g a \<noteq> 0} - sum h {a. g a \<noteq> 0}"
    apply(subst sum_minus_distrib_enat) 
      apply(rule assms(3))
    apply(rule assms(1))
    apply simp done 
  also have "\<dots> = Sum_any g - Sum_any h"
    apply(subst Sum_any.expand_set)
    apply(subst Sum_any.expand_superset[OF assms(1)])
    subgoal using assms(3)  apply auto 
      by (metis ile0_eq) 
    apply simp 
    done
  finally show ?thesis .
qed
    

thm diff_mult_distrib
lemma 
  assumes "a\<ge>b"
  shows "(a - b) * (c::enat) = a * c - b * c"
  using assms apply(cases a; cases b; cases c; auto)
  oops

lemma diff_mult_sub_distrib_enat:
  shows "(a - b) * (c::enat) \<le> a * c - b * c"
  apply(cases a; cases b; cases c; auto)
  using diff_mult_distrib by simp


(* TODO: move improved version upstream *)
lemma wfR''_finite_mult_left:
  assumes "wfR'' R"
  shows "finite {ac. x ac * the_acost (R ac) cc \<noteq> 0}"
proof - 
  from assms have "finite {s. the_acost (R s) cc \<noteq> 0}" unfolding wfR''_def by auto
  show ?thesis
    apply(rule finite_subset[where B="{ac. the_acost (R ac) cc \<noteq> 0}"])
    subgoal by auto
    subgoal apply fact done
    done
qed 

thm timerefineA_propagate
lemma timerefineA_propagate_minus:
  assumes "wfR'' E"
  fixes a b :: "('a, enat) acost"
  assumes "a\<ge>b"
  shows "timerefineA E (a - b) \<le> timerefineA E a - timerefineA E b"
  unfolding timerefineA_def
  apply(auto simp: less_eq_acost_def minus_acost_alt timerefine_def consume_def timerefineA_def split: nrest.splits option.splits)
  apply(cases a, cases b) 
  apply auto
  unfolding  ring_distribs 
  apply(rule order.trans)
   apply(rule Sum_any_mono)
    apply(rule diff_mult_sub_distrib_enat) 
   apply(rule finite_nonzero_minus)
  subgoal apply(rule wfR''_finite_mult_left) by(rule assms(1))
  subgoal apply(rule wfR''_finite_mult_left) by(rule assms(1))
  apply(subst Sum_any_minus_distrib_enat)
  subgoal apply(rule wfR''_finite_mult_left) by(rule assms(1))
  subgoal apply(rule wfR''_finite_mult_left) by(rule assms(1))
  subgoal apply(rule mult_right_mono) using assms(2) unfolding le_fun_def  by (auto simp: less_eq_acost_def  )
  apply simp
  done

lemma add_increasing2_nat_acost: "(a::(_,nat)acost)\<le>b \<Longrightarrow> a\<le>b+c" 
  apply(cases a; cases b; cases c) apply (auto simp: less_eq_acost_def)  
  by (simp add: add_increasing2)  
lemma add_increasing2_ecost: "(a::ecost)\<le>b \<Longrightarrow> a\<le>b+c" 
  apply(cases a; cases b; cases c) apply (auto simp: less_eq_acost_def)  
  by (simp add: add_increasing2)  


lemma pull_timerefine_through_reclaim:
  fixes TR :: "_\<Rightarrow>ecost"
  assumes *: "wfR'' TR"
      and ineq: "\<And>x. \<Psi> x \<Longrightarrow> \<Phi>' x \<le> T x + \<Phi>"
  shows "\<Down>\<^sub>C TR (reclaim (NREST.consume (SPEC \<Psi> (T::_\<Rightarrow>ecost)) \<Phi>) \<Phi>') \<le>
         (reclaim (NREST.consume (SPEC \<Psi> (\<lambda>x. timerefineA TR ((T::_\<Rightarrow>ecost) x))) (timerefineA TR \<Phi>)) (timerefineA TR o \<Phi>'))"
  unfolding dyn_list_append_spec_def
  apply(subst consume_SPEC_eq)
  apply(subst consume_SPEC_eq)  
  apply(subst reclaim_SPEC) 
    subgoal apply(rule ineq) by simp
  apply(subst reclaim_SPEC) 
    subgoal
     apply(subst timerefineA_propagate[symmetric])
       apply(rule *)     apply simp
      apply(rule timerefineA_mono)
      subgoal by(rule *)   
    subgoal apply(rule ineq) by simp
      done
  apply(subst SPEC_timerefine_conv)
  apply(rule SPEC_leq_SPEC_I_even_stronger)
  subgoal apply auto done
  subgoal apply (subst timerefineA_propagate[symmetric])
     apply(rule *)       apply simp
    apply(rule order.trans[rotated])
     apply(rule timerefineA_propagate_minus)
    subgoal by(rule *)     
    subgoal apply(rule ineq) by simp
    subgoal 
      apply(rule timerefineA_mono)
      subgoal by(rule *)     
      apply simp
      done
    done
  done   

lemma dyn_list_append_spec_leq_pull_TR:
  fixes TR :: "_\<Rightarrow>ecost"
  assumes *: "wfR'' TR"
  shows "\<Down>\<^sub>C TR (reclaim (NREST.consume (dyn_list_append_spec abstract_advertised_cost (bs, l, c) x) (\<Phi>_dlas' (bs, l, c))) \<Phi>_dlas') \<le>
         (reclaim (NREST.consume ((dyn_list_append_spec (timerefineA TR abstract_advertised_cost) (bs, l, c) x)) (timerefineA TR (\<Phi>_dlas' (bs, l, c)))) (timerefineA TR o \<Phi>_dlas'))"
  unfolding dyn_list_append_spec_def
  apply simp
  supply [[unify_trace_failure]]
  apply(rule pull_timerefine_through_reclaim)
   apply(rule *) 
  subgoal apply(auto simp: \<Phi>_dlas_def) apply(subst lift_acost_propagate[symmetric])
    apply(rule lift_acost_mono)
    apply(subst add.commute) apply(subst add.assoc)
    apply(subst costmult_add_distrib_left)
    apply(subst add.commute)
    apply(rule add_increasing2_nat_acost) 
    apply(rule costmult_right_mono) by auto 
  done


lemma dyn_list_append2_refines:
  "\<lbrakk>l \<le> c; c = length bs; 0 < length bs\<rbrakk> \<Longrightarrow> dyn_list_append2 (bs,l,c) x
    \<le> reclaim
          (NREST.consume (dyn_list_append_spec abstracted_advertised_cost (bs, l, c) x)
            (\<Phi>_d (bs, l, c)))
          \<Phi>_d"
  apply(rule order.trans)   
  apply(rule dyn_list_append2_refine)
  apply(rule order.trans)
   apply(rule timerefine_mono2)
  apply(rule wfR_TR_dynarray)
   apply(rule dyn_list_append_spec_refines)
     apply simp_all [3]
  apply(rule order.trans)
   apply(rule dyn_list_append_spec_leq_pull_TR)
  apply(rule wfR_TR_dynarray)
  apply(simp add: timerefine_dyn_list_append_spec)
  unfolding comp_def
  by auto
  
  

definition dyn_array_raw_armor_assn where
  "dyn_array_raw_armor_assn \<equiv> \<lambda>A (bs, l, c) da'.  $\<Phi>_d (bs, l, c) \<and>* dyn_array_raw_assn A (bs, l, c) da'"

lemma dyn_array_raw_armor_assn_alt: "dyn_array_raw_armor_assn A = augment_amor_assn \<Phi>_d (dyn_array_raw_assn A)"
  unfolding augment_amor_assn_def dyn_array_raw_armor_assn_def 
  apply (rule ext) 
  apply (rule ext) by simp


thm timerefine_mono2

lemma YEAH: "\<lbrakk>l \<le> c; c = length bs; 0 < length bs\<rbrakk>
\<Longrightarrow> hn_refine (hn_ctxt (dyn_array_raw_armor_assn A) (bs, l, c) da' \<and>* hn_ctxt A r r')
     (dyn_array_append_impl $ da' $ r')
     (hn_invalid (dyn_array_raw_armor_assn A) (bs, l, c) da' \<and>* hn_ctxt A r r')
       (dyn_array_raw_armor_assn A)
      (PR_CONST (dyn_list_append_spec abstracted_advertised_cost) $ (bs, l, c) $ r) "
  unfolding hn_ctxt_def APP_def PR_CONST_def
  unfolding dyn_array_raw_armor_assn_alt apply (simp only: prod.case)        
  apply(rule hn_refine_amortization[where m="dyn_list_append_spec abstracted_advertised_cost" and c=dyn_array_append_impl and \<Phi>="\<Phi>_d"])
  subgoal 
    apply(simp add: nofailT_reclaim nofailT_consume)
    unfolding dyn_list_append_spec_def apply (auto simp: SPEC_def consume_def split: prod.splits)
    unfolding \<Phi>_dlas_def
    apply(subst timerefineA_propagate[OF wfR_TR_dynarray, symmetric])
    apply(rule timerefineA_mono[OF wfR_TR_dynarray])
    apply auto
    unfolding lift_acost_propagate[symmetric]
    apply(rule lift_acost_mono) 
    apply(subst add.assoc[symmetric])
    apply(subst costmult_add_distrib_left) 
    apply(rule add_increasing2_nat_acost) 
    apply(rule costmult_right_mono) by auto
  subgoal 
    apply(rule TR_dynarray_keeps_finite)
    subgoal apply (auto simp: \<Phi>_dlas_def lift_acost_def A_dlas_def norm_cost split: prod.splits)
      apply(rule finite_subset[where B="{''dyn_list_double_c''}"])
       apply auto
      apply(rule ccontr) unfolding cost_def zero_acost_def zero_enat_def by auto
    by(auto intro: finite_cost_lift_acost)
  apply(rule hn_refine_ref)
   apply(rule AA_real)
  apply(rule dyn_list_append2_refines)
    apply auto
  done


abbreviation "specify_cost == 0(''list_append'':= abstracted_advertised_cost)"

lemma dyn_list_append_spec_refines: 
  "((bs,l,c),as)\<in> dyn_list_rel \<Longrightarrow> (r',r)\<in>Id
   \<Longrightarrow> dyn_list_append_spec abstracted_advertised_cost (bs, l, c) r' \<le> \<Down>dyn_list_rel (\<Down>\<^sub>C specify_cost  (mop_list_append (cost ''list_append'' 1)  as r))"
  unfolding mop_list_append_def dyn_list_rel_alt
  apply(subst timerefine_SPECT_map)
  apply(subst SPECT_assign_emb')
  unfolding conc_fun_br
  apply(subst SPEC_REST_emb'_conv[symmetric])
  unfolding dyn_list_append_spec_def  apply simp
  apply(rule SPEC_leq_SPEC_I_even_stronger)
  unfolding in_br_conv
  by (auto simp add: take_Suc_conv_app_nth norm_cost) 


lemma dyn_list_append_spec_refines_one_step: 
  "((bs,l,c),as)\<in> dyn_list_rel \<Longrightarrow> (r',r)\<in>Id
   \<Longrightarrow> dyn_list_append_spec T (bs, l, c) r' \<le> \<Down>dyn_list_rel (mop_list_append T  as r)"
  unfolding mop_list_append_def dyn_list_rel_alt
  apply(subst SPECT_assign_emb')
  unfolding conc_fun_br
  apply(subst SPEC_REST_emb'_conv[symmetric])
  unfolding dyn_list_append_spec_def  apply simp
  apply(rule SPEC_leq_SPEC_I_even_stronger)
  unfolding in_br_conv
  by (auto simp add: take_Suc_conv_app_nth norm_cost) 



lemma YEAH3: "\<lbrakk>(case x of (bs,l,c) \<Rightarrow> l \<le> c \<and> c = length bs \<and> 0 < length bs)\<rbrakk>
  \<Longrightarrow> hn_refine (hn_ctxt (dyn_array_raw_armor_assn A) x x' \<and>* hn_ctxt A r r')
     (dyn_array_append_impl $ x' $ r')
     (hn_invalid (dyn_array_raw_armor_assn A) x x' \<and>* hn_ctxt A r r')
       (dyn_array_raw_armor_assn A)
      (PR_CONST (dyn_list_append_spec abstracted_advertised_cost) $ x $ r) "
  apply(cases x)
  apply (simp only:)
  apply(rule YEAH)
  by auto

lemmas RICHTIGCOOL = YEAH3[to_hfref]

lemma dyn_list_append_spec2_refines_fref: "(uncurry (PR_CONST (dyn_list_append_spec T)), uncurry (PR_CONST (mop_list_append T)))
        \<in> dyn_list_rel \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>dyn_list_rel\<rangle>nrest_rel" 
  apply(rule frefI)
  apply(rule nrest_relI)
  apply(auto split: prod.splits simp del: mop_list_append_def simp add: PR_CONST_def uncurry_def)
  apply(rule dyn_list_append_spec_refines_one_step) by auto

thm RICHTIGCOOL dyn_list_append_spec2_refines_fref[where T="lift_acost (2 *m A_dlas + C_dlas)"]

term the_pure

definition "dyn_array_assn A = hr_comp (dyn_array_raw_armor_assn A) dyn_list_rel"

lemma dyn_array_raw_armor_: "hr_comp (dyn_array_raw_armor_assn A) dyn_list_rel = dyn_array_assn A"
  unfolding dyn_array_assn_def by auto



definition "dynamiclist_append_spec = mop_list_append abstracted_advertised_cost"

sepref_register dynamiclist_append_spec


lemma dyn_list_rel_sv[relator_props]: "single_valued dyn_list_rel"
  unfolding dyn_list_rel_alt by(rule br_sv)  

text \<open>this makes the tactic \<open>solve_attains_sup\<close> solve the supattains sidecondition, 
  because \<open>tagged_solver\<close> can then solve the single_valued goal. \<close>

declare dyn_list_rel_def[simp] \<comment> \<open>don't know how to tag this fact such that FCOMP picks it up
    correctly\<close>
declare dyn_array_raw_armor_[fcomp_norm_unfold]

lemmas FFF = RICHTIGCOOL[FCOMP dyn_list_append_spec2_refines_fref, folded dynamiclist_append_spec_def, unfolded PR_CONST_def]

declare dyn_list_rel_def[simp del]

thm FFF


subsection \<open>empty list\<close>




abbreviation "el_abstract_advertised_cost == lift_acost E_dlas"
abbreviation "el_abstracted_advertised_cost == timerefineA TR_dynarray el_abstract_advertised_cost"

definition "dynamiclist_empty_spec = mop_list_emptylist el_abstracted_advertised_cost"




lemma dyn_list_empty2_refines:
  "dynamiclist_empty2
    \<le> reclaim (dyn_list_empty_spec el_abstracted_advertised_cost) \<Phi>_d"
  apply(rule order.trans)
  apply(rule emptylist2_refine)
  apply(rule order.trans)
   apply(rule timerefine_mono2)
  apply(rule wfR_TR_dynarray)
   apply(rule dyn_list_new_raw_refines)
  apply(rule order.trans)
  unfolding dyn_list_empty_spec_def
   apply(rule pull_timerefine_through_reclaim[OF wfR_TR_dynarray])
  subgoal by (auto simp: \<Phi>_dlas_def lift_acost_zero ecost_nneg)
  apply(simp add: timerefine_dyn_list_empty_spec consume_0)
  unfolding comp_def            
  by auto
  

(* declare [[unify_trace_failure]] *)


thm emptylist2_real
thm emptylist2_real[to_hnr]
thm emptylist2_refine


lemma YEAH32: "hn_refine \<box> dynamiclist_empty_impl \<box>
       (dyn_array_raw_armor_assn A)
      (PR_CONST (dyn_list_empty_spec el_abstracted_advertised_cost) ) "
  unfolding hn_ctxt_def APP_def PR_CONST_def
  unfolding dyn_array_raw_armor_assn_alt
  apply(rule hn_refine_reclaimday)
  subgoal                                    
    apply(simp add: nofailT_reclaim nofailT_consume)
    unfolding dyn_list_empty_spec_def apply (auto simp: SPEC_def consume_def split: prod.splits)
    unfolding \<Phi>_dlas_def apply auto
    apply(rule timerefineA_mono[OF wfR_TR_dynarray])
    by (auto simp: lift_acost_zero ecost_nneg) 
  apply(rule hn_refine_ref) 
   apply(rule emptylist2_real[to_hnr])
  apply(rule dyn_list_empty2_refines)
  done


lemmas RICHTIGCOOL2 = YEAH32[to_hfref]


lemma dynamiclist_empty_refines_fref: "(uncurry0 (PR_CONST (dyn_list_empty_spec (T::ecost))), uncurry0 (PR_CONST (mop_list_emptylist T)))
        \<in> unit_rel \<rightarrow>\<^sub>f \<langle>dyn_list_rel\<rangle>nrest_rel" 
  apply(rule frefI)
  apply(rule nrest_relI)
  unfolding mop_list_emptylist_def dyn_list_empty_spec_def dyn_list_rel_alt
  apply (simp add: timerefine_SPECT_map norm_cost )                   
  apply (simp add: SPECT_assign_emb' conc_fun_br)
  apply(subst SPEC_REST_emb'_conv[symmetric])
  apply(rule SPEC_leq_SPEC_I_even_stronger)
  by auto

lemmas GGG = RICHTIGCOOL2[FCOMP dynamiclist_empty_refines_fref, folded dynamiclist_empty_spec_def, unfolded PR_CONST_def]


end


thm hnr_raw_array_new
term mop_array_new


definition dyn_array_raw_assn where
  "dyn_array_raw_assn A \<equiv> \<lambda>(bs,l,c) (p,l',c'). array_assn A bs p ** snat_assn l l' ** snat_assn c c'"

definition "dyn_array_append_impl = undefined"
definition "dynamiclist_empty_impl = undefined"
definition "TR_dynarray = undefined"

global_interpretation dyn_array: dyn_list_impl dynamiclist_append2 dyn_array_append_impl
                            dynamiclist_empty2 dynamiclist_empty_impl
                            TR_dynarray dyn_array_raw_assn
    defines dynamic_array_append_spec = "dyn_array.dynamiclist_append_spec"
      and dynamic_array_empty_spec = "dyn_array.dynamiclist_empty_spec" 
      and dynamic_array_assn = dyn_array.dyn_array_assn
  sorry

sepref_register dynamic_array_append_spec
declare dyn_array.FFF[sepref_fr_rules]

term dynamic_array_empty_spec
sepref_register dynamic_array_empty_spec
declare dyn_array.GGG[sepref_fr_rules]



term dyn_array.dynamiclist_empty_spec
term dyn_array.dynamiclist_append_spec


term dynamic_array_append_spec

definition "algorithm = doN {
    (s::nat list) \<leftarrow> dynamic_array_empty_spec;
    s \<leftarrow> dynamic_array_append_spec s (0::nat);
    s \<leftarrow> dynamic_array_append_spec s (1::nat);
    s \<leftarrow> dynamic_array_append_spec s (42::nat);
    s \<leftarrow> dynamic_array_append_spec s (42::nat);
    s \<leftarrow> dynamic_array_append_spec s (32::nat);
    s \<leftarrow> dynamic_array_append_spec s (31::nat);
    s \<leftarrow> dynamic_array_append_spec s (42::nat);
    s \<leftarrow> dynamic_array_append_spec s (1::nat);
    s \<leftarrow> dynamic_array_append_spec s (1::nat);
    RETURNT s
  }"

term "dynnamic_array_assn snat_assn"

term narray_new

sepref_def algorithm_impl is "uncurry0 algorithm"
  :: "(unit_assn)\<^sup>k \<rightarrow>\<^sub>a dynamic_array_assn (snat_assn' TYPE(32))"
  unfolding algorithm_def
    supply [[goals_limit = 1]]
    apply (annot_snat_const "TYPE(32)")
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
  done

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