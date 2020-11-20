
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
            (\<lambda>(_,n'). undefined)
            (\<lambda>(dst',n'). doN {
              x \<leftarrow> mop_list_get (\<lambda>_. cost ''list_get'' 1) src n';
              dst'' \<leftarrow> mop_list_set (\<lambda>_. cost ''list_set'' 1) dst n' x;
              n'' \<leftarrow> SPECc2 ''add'' (+) n' 1;
              RETURNT (dst'',n'')
            })
          (dst,0);
          RETURNT dst
      }"

definition "TR_lst_copy = undefined"

lemma "list_copy dst src n \<le> \<Down>Id (\<Down>\<^sub>C TR_lst_copy (list_copy_spec (cost ''list_copy_c'' (enat n)) dst src n))"
  sorry


  
subsection \<open>List Double\<close>

term mop_list_init
term mop_list_init_raw
thm hnr_raw_array_new refine_mop_list_init_raw
term mop_array_new
thm hnr_array_new


thm hnr_array_new

definition dyn_list_double_spec where
  "dyn_list_double_spec \<equiv> \<lambda>(bs,n). doN {
       ASSERT (n\<le>length bs);
       SPEC (\<lambda>(bs',n'). take n bs' = take n bs \<and> 
              length bs' = 2 * length bs \<and> n' = n \<and> n<length bs' )
        (\<lambda>(bs',n'). (enat (length bs')) *m cost ''alloc_raw'' 1
                       + cost ''list_copy_c'' (enat n')) 
  }"

definition dyn_list_double where
  "dyn_list_double ini  \<equiv> \<lambda>(bs,n). doN {
       ASSERT (n\<le>length bs);
       bsl \<leftarrow> mop_list_length (cost ''list_length'' 1) bs;
       bsl \<leftarrow> SPECc2 ''mul'' (*) 2 bsl;
       bsl \<leftarrow> SPECc2 ''add'' (+) bsl 1;
       dst \<leftarrow> mop_list_init (\<lambda>n. cost ''list_init_c'' (enat n)) ini (2*bsl);
       list_copy dst bs n; 
       RETURNT (dst,n)
      }"


subsection \<open>List Push\<close>


definition mop_list_append where
  "mop_list_append T xs x = SPECT [xs @ [x] \<mapsto> T]"


definition dyn_list_append_basic_spec where
  "dyn_list_append_basic_spec \<equiv> \<lambda>(bs,n) x. doN {
      ASSERT (n < length bs);
      bs' \<leftarrow> mop_list_set (\<lambda>_. cost ''list_set'' 1) bs n x;
      n' \<leftarrow> SPECc2 ''add'' (+) n 1;
      RETURNT (bs',n')
  }"



definition dyn_list_append_spec where
  "dyn_list_append_spec \<equiv> \<lambda>(bs,n) x. doN {
      ASSERT (n\<le>length bs \<and> 0<length bs);
      bsl \<leftarrow> mop_list_length (cost ''list_length'' 1) bs;
      if\<^sub>N SPECc2 ''less'' (<) n bsl then doN {
        dyn_list_append_basic_spec (bs,n) x
      } else doN {          
        (bs',n') \<leftarrow> dyn_list_double_spec (bs,n);
        ASSERT (n<length bs' \<and> n'=n \<and> take n bs = take n bs' );
        dyn_list_append_basic_spec (bs',n') x
      }
  }"


subsection \<open>dynamic List init\<close>


definition "dyn_list_rel = {( ((bs,n)) , as) | bs n  as. take n bs = as \<and> n \<le> length bs \<and> length bs > 0 }"


lemma dyn_list_rel_alt: "dyn_list_rel = br (\<lambda>(bs,n). take n bs) (\<lambda>(bs,n). n \<le> length bs \<and> length bs > 0)"
  unfolding dyn_list_rel_def br_def by auto




definition mop_list_emptylist where
  "mop_list_emptylist T = SPECT [ [] \<mapsto> T ]"

definition dyn_list_new where
  "dyn_list_new ini = do {
       dst \<leftarrow> mop_list_init (\<lambda>n. cost ''list_init_c'' 8) ini 8;
       RETURNT (dst,0)
    }"



lemma "dyn_list_new ini \<le> \<Down>dyn_list_rel (timerefine RR (mop_list_emptylist (cost ''list_init_c'' 8)))"
  sorry


subsection \<open>dynamic list lookup\<close>

definition dyn_list_get where
  "dyn_list_get \<equiv> \<lambda>(bs,n) i. doN {
    mop_list_get (\<lambda>_. cost ''list_get'' 1) bs i
  }"

lemma "( (bs,n), as)\<in>dyn_list_rel \<Longrightarrow> dyn_list_get (bs,n) i \<le> mop_list_get (\<lambda>_. cost ''list_get'' 1) as i"
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
  "dyn_list_append_spec2 T \<equiv> \<lambda>(bs,n) x. SPEC (\<lambda>(bs',n'). n'\<le>length bs' \<and> n'=n+1 \<and> length bs' \<ge> length bs
                                                          \<and> take n bs' = take n bs \<and> bs' ! n = x) T"

definition "RRmm = 0(''list_append'':=cost ''bla'' (1::enat))"

definition "dyn_list_append_spec2_cost == \<lambda>_. cost ''bla'' 1"

lemma "((bs,n),as)\<in>dyn_list_rel \<Longrightarrow> (x',x) \<in> Id
 \<Longrightarrow> dyn_list_append_spec2 (\<lambda>_. cost ''bla'' 1) (bs,n) x'
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
definition "\<Phi>_dlas \<equiv> (\<lambda>(xs,n). lift_acost (((2*n -length xs)) *m A_dlas))"

lemma  dyn_list_append_spec_refines:
  assumes a: "n \<le> length bs" "0<length bs"
  shows "dyn_list_append_spec (bs,n) x \<le> reclaim (consume (dyn_list_append_spec2 (\<lambda>_. lift_acost (2 *m A_dlas + C_dlas)) (bs,n) x) (\<Phi>_dlas (bs,n))) \<Phi>_dlas"
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
          apply auto
  subgoal
    unfolding \<Phi>_dlas_def apply (simp add: lift_acost_propagate[symmetric] lift_acost_minus)
    apply(subst (5) add.commute)
    apply(subst add.assoc)
    apply(subst costmult_add_distrib_left)  
    apply(rule order.trans[rotated])
     apply(rule lift_acost_mono)
    apply(rule zz2)
     apply(rule costmult_right_mono) apply simp 
    unfolding C_dlas_def  apply(simp add: norm_cost) apply(sc_solve) by (simp add: one_enat_def)
  subgoal 
    unfolding \<Phi>_dlas_def apply (simp add: lift_acost_propagate[symmetric] lift_acost_minus add.assoc)
    unfolding C_dlas_def A_dlas_def
    apply(simp add: norm_cost)
    apply sc_solve  
    apply (auto simp: one_enat_def)[1] 
    done
  done


lemma
   brut: 
  "hn_refine (G x x' ** F' r r') (c x' r') (invalid_assn G x x' ** F' r r') G (reclaim (consume (m x r) (\<Phi> x)) \<Phi>)
    \<Longrightarrow> hn_refine (($(\<Phi> x) ** G x x') ** F' r r') (c x' r') (invalid_assn G x x' ** F' r r') (\<lambda>ra r. G ra r ** $ (\<Phi> ra)) (m x r)"
  sorry



definition "dyn_array_append_impl = undefined"

lemma AA: "hn_refine (L (bs,n) (p,m) ** A x x')
        (dyn_array_append_impl (p,m) x')
            (invalid_assn L (bs,n) (p,m) ** A x x')
            L (dyn_list_append_spec (bs,n) x)"
  sorry


declare [[unify_trace_failure]]

thm hn_refine_ref[OF AA dyn_list_append_spec_refines, THEN brut[where m="dyn_list_append_spec2 (\<lambda>_. lift_acost (2 *m A_dlas + C_dlas))" and c=dyn_array_append_impl and \<Phi>="\<Phi>_dlas"]]


term array_assn

definition dyn_array_raw_assn where
  "dyn_array_raw_assn A \<equiv> \<lambda>(bs,n) (p,m). array_assn A bs p ** snat_assn n m"
                                            
lemma AA_real: "hn_refine (dyn_array_raw_assn A (bs,n) (p,m) ** A x x')
        (dyn_array_append_impl (p,m) x')
            (invalid_assn (dyn_array_raw_assn A) (bs,n) (p,m) ** A x x')
           (dyn_array_raw_assn A) (dyn_list_append_spec (bs,n) x)"
  sorry


declare [[unify_trace_failure]]

thm hn_refine_ref[OF AA dyn_list_append_spec_refines, THEN brut[where m="dyn_list_append_spec2 (\<lambda>_. lift_acost (2 *m A_dlas + C_dlas))" and c=dyn_array_append_impl and \<Phi>="\<Phi>_dlas"]]





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