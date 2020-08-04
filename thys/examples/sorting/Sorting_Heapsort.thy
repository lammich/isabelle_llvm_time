theory Sorting_Heapsort
imports Sorting_Setup "../../nrest/NREST_Automation"
begin                                       

(*
  TODO: Fix section structure
*)


section "stuff to move"


(* TODO : Move *)

(* move *)
lemma bindT_refine_easy:
  fixes m :: "('e1,('c1,enat)acost) nrest"
  fixes m' :: "('e2,('c2,enat)acost) nrest"
  assumes "wfR'' E" " m \<le> \<Down>R' (timerefine E m')"
  "(\<And>x x'. \<lbrakk>(x,x')\<in>R'\<rbrakk>
         \<Longrightarrow> f x \<le> \<Down> R (timerefine E (f' x') ))"
shows "bindT m f \<le>  \<Down> R (timerefine E (bindT m' f'))"
  apply(rule bindT_refine_conc_time2) using assms
  by (auto dest: inres_if_inresT_acost)


(* TODO: move *)
lemma inres_bindT_SPECT_one[simp]: "inres (do {l' \<leftarrow> SPECT [x \<mapsto> t]; M l'}) r \<longleftrightarrow> inres (M x) r"
  by(auto simp: bindT_def inres_def split: nrest.splits)

declare inres_SPECT[simp]



lemma the_acost_costs_distrib_left:
  "the_acost (cost n x + (r:: ('c, nat) acost)) m * p
     = the_acost (cost n x) m * p + the_acost r m * p"
  apply(cases r) by(auto simp: cost_def zero_acost_def ring_distribs )
lemma the_acost_costs_distrib_right:
  "the_acost ((r:: ('c, nat) acost) + cost n x ) m * p
     = the_acost (cost n x) m * p + the_acost r m * p"
  apply(cases r) by(auto simp: cost_def zero_acost_def ring_distribs )
lemmas the_acost_costs_distrib = the_acost_costs_distrib_left the_acost_costs_distrib_right
lemma the_acost_cost_mult: "the_acost (cost n c) x * (p::nat) = the_acost (cost n (c*p)) x"
  by(auto simp: cost_def zero_acost_def)
lemma acostC_the_acost_cost: "acostC (\<lambda>x. the_acost (cost n t) x + r x) = cost n t + acostC r"
  by (auto simp: cost_def)
lemma "acostC (\<lambda>x. the_acost (cost n t) x + r x) = cost n t + acostC r"
  by (auto simp: cost_def)



lemma monadic_WHILEIT_refine':  
  fixes b :: "'c \<Rightarrow> (bool, (char list, enat) acost) nrest"
  assumes wfR[simp]:  "wfR'' E"
  assumes sp_E: "struct_preserving E"
  assumes [refine]: "(s',s) \<in> R"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s \<rbrakk> \<Longrightarrow> I' s'"  
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s' \<rbrakk> \<Longrightarrow> b' s' \<le>\<Down>bool_rel (timerefine E (b s))"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s'; inres (b s) True \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (timerefine E (f s))"
  shows "monadic_WHILEIT I' b' f' s' \<le> \<Down>R (timerefine E (monadic_WHILEIT I b f s))"
  apply(rule monadic_WHILEIT_refine_t[OF assms(1-5)])
  by(auto intro: assms(6) inres_if_inresT_acost)

lemma inres_consumea[simp]: "inres (do {_ \<leftarrow> consumea t; M}) r \<longleftrightarrow> inres M r"
  by (cases M) (auto simp: bindT_def inres_def consumea_def)

lemma inres_RETURNT[simp]: "inres (RETURNT x) y \<longleftrightarrow> (x=y)"
  by(auto simp: inres_def )

lemma inres_bind_ASSERT[simp]: "inres (doN { ASSERT \<phi>; N }) r \<longleftrightarrow> (\<phi> \<and> inres N r)"
  by(auto simp: inres_def ASSERT_def iASSERT_def)

declare inres_consume_conv[simp]

lemma inres_bindT_consume_conv[simp]:
  fixes t :: "(_,enat) acost"
  shows "inres (doN { x  \<leftarrow> NREST.consume m t; M x}) r = inres (doN { x \<leftarrow> m; M x }) r"
  unfolding consume_alt2 by simp

lemma if_rule2: "(c \<Longrightarrow> Some x \<le> a) \<Longrightarrow> c \<Longrightarrow> Some x \<le> (if c then a else None)"
  by auto

lemma if_rule: "(c \<Longrightarrow> x \<le> a) \<Longrightarrow> (~c \<Longrightarrow> x \<le> b) \<Longrightarrow> x \<le> (if c then a else b)"
  by auto

lemma ifSome_None: "(if P then Some x else None) = Some y \<longleftrightarrow> P \<and> x=y"
  by (auto split: if_splits)

lemma prod3: "m\<le> f x y z \<Longrightarrow> m \<le> (case (x,y,z) of (a,b,c) \<Rightarrow> f a b c)"
  by auto

lemma top_acost_absorbs: "top + (x::(_,enat)acost) = top"
  apply(cases x) by (auto simp: top_acost_def plus_acost_alt top_enat_def)





locale heap_range_context = 
  fixes l h :: nat
  assumes ran_not_empty[arith,simp]: "l\<le>h"
begin  

  (*lemma l_le_h[arith,simp]: "l\<le>h" by simp*)

  definition "in_heap i \<equiv> i\<in>{l..<h}"

  definition parent where "parent i \<equiv> (i-1-l) div 2 + l"
  definition lchild where "lchild i \<equiv> 2*(i-l) + 1 + l"
  definition rchild where "rchild i \<equiv> 2*(i-l) + 2+ l"
  
  
  
  
  definition has_parent where "has_parent i \<equiv> in_heap i \<and> i>l"
  definition has_lchild where "has_lchild i \<equiv> in_heap i \<and> in_heap (lchild i)"
  definition has_rchild where "has_rchild i \<equiv> in_heap i \<and> in_heap (rchild i)"
  
  context begin
    private method prove = (
      unfold in_heap_def parent_def has_parent_def lchild_def rchild_def has_lchild_def has_rchild_def, 
      auto)

    text \<open>Optimized checks, normalize to i-l, for index shift\<close>
    lemma has_rchild_ihs: "in_heap i \<Longrightarrow> has_rchild i \<longleftrightarrow> i-l<(h-l-1) div 2"
      by prove

    lemma has_lchild_ihs: "in_heap i \<Longrightarrow> has_lchild i \<longleftrightarrow> (i-l) < (h-l) div 2"  
      by prove
      
    lemma has_parent_ihs: "in_heap i \<Longrightarrow> has_parent i \<longleftrightarrow> i-l > 0"
      by prove
      
    lemma lchild_ihs: "lchild i - l = 2*(i-l)+1"  
      by prove
      
    lemma rchild_ihs: "rchild i - l = 2*(i-l)+2"  
      by prove
      
    lemma parent_ihs: "parent i - l = (i-l-1) div 2"
      by prove
      
    lemma in_heapI: "\<lbrakk> l\<le>i; i<h \<rbrakk> \<Longrightarrow> in_heap i" by prove
      
    lemma in_heap_bounds[simp]: 
      assumes "in_heap i" 
      shows "l\<le>i" and "i<h"
      using assms by prove

    lemma in_heap_triv[simp]: 
      "has_parent i \<Longrightarrow> in_heap i"        
      "has_lchild i \<Longrightarrow> in_heap i"        
      "has_rchild i \<Longrightarrow> in_heap i"        
      by prove
            
    lemma parent_in_heap[simp]: 
      "has_parent i \<Longrightarrow> in_heap (parent i)" 
      "has_parent i \<Longrightarrow> has_lchild (parent i)" 
      by prove
    
    lemma children_in_heap[simp]: 
      "has_lchild i \<Longrightarrow> in_heap (lchild i)"
      "has_rchild i \<Longrightarrow> in_heap (rchild i)"
      by prove

    lemmas in_heap_simps = in_heap_triv parent_in_heap children_in_heap
            

    lemma parent_of_child[simp]:
      "has_lchild i \<Longrightarrow> parent (lchild i) = i"
      "has_rchild i \<Longrightarrow> parent (rchild i) = i"
      by prove

    lemma children_differ[simp]:
      "lchild i \<noteq> rchild i" 
      "rchild i \<noteq> lchild i" 
      by prove

    lemma parent_less[simp]: "has_parent i \<Longrightarrow> parent i < i" by prove

    lemma children_greater[simp]: 
      "lchild i > i" 
      "rchild i > i"
      by prove

      
    lemma children_diff_add_simps[iff]:
      "lchild i \<noteq> i"  
      "i \<noteq> lchild i"  
      "rchild i \<noteq> i"  
      "i \<noteq> rchild i"  
      by prove
      
    lemma parent_diff_add_simps[simp]: 
      assumes "has_parent i" shows "i \<noteq> parent i" and "parent i \<noteq> i"
      using assms by prove
      
    lemma rchild_imp_lchild[simp, intro]: "has_rchild i \<Longrightarrow> has_lchild i" by prove

    lemma no_parent_is_root: "in_heap i \<Longrightarrow> \<not>has_parent i \<longleftrightarrow> i=l" by prove
    
    lemma root_no_parent[iff]: "\<not>has_parent l" by prove
    
    
    lemma root_in_heap: "in_heap l\<longleftrightarrow>l<h" using ran_not_empty by prove
    
                      
    lemma child_of_parent: "has_parent i \<Longrightarrow> lchild (parent i) = i \<or> has_rchild (parent i) \<and> rchild (parent i) = i" by prove
                
    lemma children_of_parent_cases[consumes 1]:
      assumes "has_parent i"
      obtains (left) "has_parent i" "lchild (parent i) = i" 
            | (right) "has_parent i" "has_rchild (parent i)" "rchild (parent i) = i"
      using assms child_of_parent by blast            

    lemma lchild_of_no_rchild_term: "\<lbrakk>\<not>has_rchild i; has_lchild i\<rbrakk> \<Longrightarrow> \<not>has_lchild (lchild i)" by prove 
      
      
          
  end

  lemmas heap_context_defs[no_atp] = in_heap_def parent_def lchild_def rchild_def has_parent_def has_lchild_def has_rchild_def
end  
  
locale heap_context = weak_ordering + heap_range_context begin
  
  definition is_heap :: "'a list \<Rightarrow> bool" 
    where "is_heap xs \<equiv> (h\<le>length xs) \<and> (\<forall>i. has_parent i \<longrightarrow> xs!parent i \<^bold>\<ge> xs!i)"

    
  subsection \<open>Heap Property implies Minimal Element at Top\<close>
  context
    fixes xs
    assumes H: "is_heap xs"
  begin  

    lemma parent_el_greater[simp]: "has_parent i \<Longrightarrow> xs!i \<^bold>\<le> xs!parent i"
      using H
      unfolding is_heap_def 
      by simp
    
    lemma root_greatest:
      assumes "in_heap i"
      shows "xs!i \<^bold>\<le> xs!l"
      using assms 
    proof (induction i rule: less_induct)
      case (less i)
      note [simp] = \<open>in_heap i\<close>
      
      show ?case proof cases
        assume [simp]: "has_parent i"
        have "xs!i \<^bold>\<le> xs!parent i" by simp
        also from less.IH[of "parent i"] have "xs!parent i \<^bold>\<le> xs!l" by simp
        finally show ?case .
      next
        assume "\<not>has_parent i" 
        hence "i=l" by (simp add: no_parent_is_root)
        thus ?case by simp
      qed  
    qed
  
  end  

    
  subsection \<open>Sift-Up Lemmas\<close>    
  definition is_heap_except_up :: "nat \<Rightarrow> 'a list \<Rightarrow> bool" 
    where "is_heap_except_up j xs \<equiv> 
      (h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> i\<noteq>j \<longrightarrow> xs!parent i \<^bold>\<ge> xs!i)
      \<and> (has_parent j \<and> has_lchild j \<longrightarrow> xs!parent j \<^bold>\<ge> xs!lchild j)
      \<and> (has_parent j \<and> has_rchild j \<longrightarrow> xs!parent j \<^bold>\<ge> xs!rchild j)"

  lemma is_heap_except_up_len_bound[simp, intro]: 
    assumes "is_heap_except_up i xs"
    shows "h\<le>length xs"     
    using assms unfolding is_heap_except_up_def
    by auto
        
  lemma sift_up_lemma:
    assumes HP: "has_parent i"
    assumes IHE: "is_heap_except_up i xs"
    assumes GE: "xs!i \<^bold>\<ge> xs!parent i"
    shows "is_heap_except_up (parent i) (swap xs i (parent i))"
  proof -
    from assms(2) have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_up_def by auto
  
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp

    have HPROP: "xs!j \<^bold>\<le> xs!parent j" if "has_parent j" "j\<noteq>i" for j
      using that IHE unfolding is_heap_except_up_def by simp
      
      
    show ?thesis using HP
      unfolding is_heap_except_up_def
      apply (clarsimp; safe)
      subgoal
        apply (clarsimp simp: swap_nth HPROP GE; safe)
        subgoal by (metis GE HPROP trans)
        by (metis IHE child_of_parent is_heap_except_up_def parent_in_heap(2))

      subgoal
        by (smt HPROP X children_greater(1) has_lchild_def in_heap_bounds(1) parent_of_child(1) trans nat_less_le no_parent_is_root parent_in_heap(2) parent_less less_le_trans swap_indep swap_nth)
      subgoal 
        by (smt HPROP X children_greater(2) has_parent_def has_rchild_def parent_less parent_of_child(2) less_le trans less_trans swap_nth)
        
      done
      
  qed

  text \<open>Terminate when reached root\<close>
  lemma sift_up_term1: "is_heap_except_up l xs \<Longrightarrow> is_heap xs"
    unfolding is_heap_def is_heap_except_up_def by auto
  
  text \<open>Terminate when parent is greater or equal\<close>  
  lemma sift_up_term2: "\<lbrakk>is_heap_except_up i xs; xs!i\<^bold>\<le>xs!parent i\<rbrakk> \<Longrightarrow> is_heap xs"
    unfolding is_heap_def is_heap_except_up_def by auto
  
  lemma grow_heap_context: "heap_range_context l (Suc h)" 
    apply unfold_locales using ran_not_empty by linarith 
    
  text \<open>Initializes a sift-up cycle by extending the heap by one element to the right\<close>  
  lemma sift_up_init:
    assumes "is_heap xs"
    assumes "h<length xs"
    shows "heap_context.is_heap_except_up (\<^bold>\<le>) l (Suc h) h xs"
  proof -
    interpret N: heap_range_context l "Suc h" using grow_heap_context .
    interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "Suc h" by unfold_locales
  
    show ?thesis
      using assms
      unfolding is_heap_def is_heap_except_up_def N.is_heap_except_up_def
      unfolding N.heap_context_defs heap_context_defs
      by auto
      
  qed
  
  subsection \<open>Sift-Down Lemmas\<close>    

  definition is_heap_except_down :: "nat \<Rightarrow> 'a list \<Rightarrow> bool"
    where "is_heap_except_down j xs \<equiv>
        (h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> parent i \<noteq> j \<longrightarrow> xs!parent i \<^bold>\<ge> xs!i)
      \<and> (\<forall>i. has_parent i \<and> has_parent j \<and> parent i = j \<longrightarrow> xs!parent j \<^bold>\<ge> xs!i)"

  lemma is_heap_except_down_len_bound[simp, intro]: 
    assumes "is_heap_except_down i xs"
    shows "h\<le>length xs"     
    using assms unfolding is_heap_except_down_def
    by auto
          
  lemma sift_down_lemma_left:
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down i xs"
    assumes GE: "xs!lchild i \<^bold>\<ge> xs!i" "xs!lchild i \<^bold>\<ge> xs!rchild i"
    shows "is_heap_except_down (lchild i) (swap xs i (lchild i))"
  proof -  
    show ?thesis 
      using IHE HRC GE
      unfolding is_heap_except_down_def
      apply (clarsimp)
      by (smt child_of_parent children_greater(1) children_in_heap(1) dual_order.trans has_parent_def parent_diff_add_simps(1) in_heap_bounds(2) leD order_less_le parent_of_child(1) rchild_imp_lchild swap_indep swap_nth1 swap_nth2)
      
  qed

  lemma sift_down_lemma_right:
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down i xs"
    assumes GE: "xs!rchild i \<^bold>\<ge> xs!i" "xs!lchild i \<^bold>\<le> xs!rchild i"
    shows "is_heap_except_down (rchild i) (swap xs i (rchild i))"
  proof -  
    show ?thesis 
      using IHE HRC GE
      unfolding is_heap_except_down_def
      apply (clarsimp)
      by (smt child_of_parent children_greater(2) children_in_heap(2) dual_order.trans eq_iff heap_range_context.has_parent_def heap_range_context_axioms in_heap_bounds(2) less_le parent_less parent_of_child(2) swap_nth)
      
  qed
  
    
  lemma sift_down_lemma_left_no_right_child:
    assumes HRC: "has_lchild i" "\<not>has_rchild i"
    assumes IHE: "is_heap_except_down i xs"
    assumes GE: "xs!lchild i \<^bold>\<ge> xs!i"
    shows "is_heap_except_down (lchild i) (swap xs i (lchild i))"
  proof -  
    from IHE have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_down_def by auto
    
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp
      
    show ?thesis 
      using IHE HRC GE
      unfolding is_heap_except_down_def
      apply clarsimp
      by (smt X child_of_parent children_greater(1) children_in_heap(1) heap_range_context.has_parent_def heap_range_context.parent_of_child(1) heap_range_context_axioms le_less_trans less_imp_le_nat parent_in_heap(1) swap_nth)
      
  qed

  
  lemma sift_down_term1: "\<not>has_lchild j \<Longrightarrow> is_heap_except_down j xs \<longleftrightarrow> is_heap xs"
    unfolding is_heap_except_down_def is_heap_def
    by auto
  
  lemma sift_down_term2: "\<lbrakk>is_heap_except_down j xs; has_rchild j; xs!j\<^bold>\<ge>xs!lchild j; xs!j\<^bold>\<ge>xs!rchild j \<rbrakk> \<Longrightarrow> is_heap xs"
    unfolding is_heap_except_down_def is_heap_def
    apply (clarsimp)
    by (metis children_of_parent_cases)
  
  lemma sift_down_term3: "\<lbrakk>is_heap_except_down j xs; has_lchild j; \<not>has_rchild j; xs!j\<^bold>\<ge>xs!lchild j \<rbrakk> \<Longrightarrow> is_heap xs"
    unfolding is_heap_except_down_def is_heap_def
    apply (clarsimp)
    by (metis children_of_parent_cases)
     
  lemma shrink_heap_context: "Suc l<h \<Longrightarrow> heap_range_context l (h-Suc 0)" 
    apply unfold_locales using ran_not_empty by linarith 
  
  text \<open>Initializes a sift-down cycle by swapping the first and last element, and then shrinking the heap by one element\<close>
  lemma sift_down_init:  
    assumes "is_heap xs"
    assumes LT: "Suc l < h"
    shows "heap_context.is_heap_except_down (\<^bold>\<le>) l (h-Suc 0) l (swap xs l (h-Suc 0))"
  proof -
    interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "h-Suc 0"
      apply intro_locales
      using shrink_heap_context[OF LT] .
    
    show ?thesis
      using assms
      unfolding is_heap_def is_heap_except_down_def N.is_heap_except_down_def
      unfolding N.heap_context_defs heap_context_defs
      by (auto simp: swap_nth)
      
  qed    
        
    
  subsection \<open>Bottom-up Heapify\<close>

  text \<open>The nodes from index \<open>l'\<close> upwards satisfy the heap criterion\<close>
  definition is_heap_btu :: "nat \<Rightarrow> 'a list \<Rightarrow> bool" where "is_heap_btu l' xs \<equiv> 
        (l'\<le>h \<and> h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> parent i \<ge> l' \<longrightarrow> xs!parent i \<^bold>\<ge> xs!i)"

  text \<open>Bottom-up heapify starts with only the last element being a heap\<close>
  lemma btu_heapify_init: "h\<le>length xs \<Longrightarrow> is_heap_btu (h-Suc 0) xs"  
    unfolding is_heap_btu_def
    apply auto
    by (meson dual_order.trans in_heap_bounds(2) in_heap_triv(1) nat_le_Suc_less_imp not_le parent_less)
        
  text \<open>When we have reached the lower index, we have a complete heap\<close>    
  lemma btu_heapify_term: "is_heap_btu l xs \<longleftrightarrow> is_heap xs"
    unfolding is_heap_btu_def is_heap_def
    by (auto simp: less_imp_le_nat)
      
      
  text \<open>All nodes in between l' and h form a valid heap, with downwards-hole at j\<close>
  definition is_heap_except_down_btu :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool"
    where "is_heap_except_down_btu l' j xs \<equiv>
        (l'\<le>j \<and> j<h \<and> h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> parent i \<ge> l' \<and> parent i \<noteq> j \<longrightarrow> xs!parent i \<^bold>\<ge> xs!i)
      \<and> (\<forall>i. has_parent i \<and> has_parent j \<and> parent j \<ge>l' \<and> parent i = j \<longrightarrow> xs!parent j \<^bold>\<ge> xs!i)"

  lemma is_heap_except_down_btu_lenD: "is_heap_except_down_btu l' j xs \<Longrightarrow> h\<le>length xs"    
    unfolding is_heap_except_down_btu_def by auto
      
  text \<open>A sift-down round starts by including one more left element, and marking it as a hole\<close>
  lemma btu_sift_down_init: "\<lbrakk>is_heap_btu l' xs; l'>l\<rbrakk> \<Longrightarrow> is_heap_except_down_btu (l'-1) (l'-1) xs"  
    unfolding is_heap_except_down_btu_def is_heap_btu_def 
    apply auto
    using leD parent_less by blast
  
      
  text \<open>Sift-down completed, we have a complete heap from \<open>l'\<close> upwards\<close>
  lemma btu_sift_down_term1: "\<not>has_lchild j \<Longrightarrow> is_heap_except_down_btu l' j xs \<Longrightarrow> is_heap_btu l' xs"
    unfolding is_heap_except_down_btu_def is_heap_btu_def 
    by auto
      
  lemma btu_sift_down_term2: "\<lbrakk>is_heap_except_down_btu l' j xs; has_rchild j; xs!j\<^bold>\<ge>xs!lchild j; xs!j\<^bold>\<ge>xs!rchild j \<rbrakk> 
    \<Longrightarrow> is_heap_btu l' xs"
    unfolding is_heap_except_down_btu_def is_heap_btu_def
    apply (clarsimp)
    by (smt dual_order.trans child_of_parent in_heap_bounds(2) in_heap_triv(3) le_cases not_le)
  
  lemma btu_sift_down_term3: "\<lbrakk>is_heap_except_down_btu l' j xs; has_lchild j; \<not>has_rchild j; xs!j\<^bold>\<ge>xs!lchild j \<rbrakk> \<Longrightarrow> is_heap_btu l' xs"
    unfolding is_heap_except_down_btu_def is_heap_btu_def
    apply (clarsimp)
    by (metis child_of_parent dual_order.trans in_heap_bounds(2) in_heap_triv(2) less_imp_le)
  

  

  lemma btu_heapify_down_left:
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down_btu l' i xs"
    assumes GE: "xs!lchild i \<^bold>\<ge> xs!i" "xs!lchild i \<^bold>\<ge> xs!rchild i"
    shows "is_heap_except_down_btu l' (lchild i) (swap xs i (lchild i))"
  proof -
    from IHE have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_down_btu_def by auto
    
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp
    
    show ?thesis
      using HRC IHE GE
      unfolding is_heap_except_down_btu_def
      apply (clarsimp simp: swap_nth)
      by (smt child_of_parent children_greater(1) children_in_heap(1) heap_range_context.has_parent_def heap_range_context_axioms leD le_cases less_le_trans parent_of_child(1) rchild_imp_lchild)
      
  qed  
        
  lemma btu_heapify_down_right:
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down_btu l' i xs"
    assumes GE: "xs!rchild i \<^bold>\<ge> xs!i" "xs!lchild i \<^bold>\<le> xs!rchild i"
    shows "is_heap_except_down_btu l' (rchild i) (swap xs i (rchild i))"
  proof -
    from IHE have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_down_btu_def by auto
    
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp
    
    show ?thesis
      using HRC IHE GE
      unfolding is_heap_except_down_btu_def
      apply (clarsimp simp: swap_nth)
      by (smt child_of_parent children_greater(2) children_in_heap(2) dual_order.strict_trans2 heap_range_context.has_parent_def heap_range_context_axioms less_imp_le_nat parent_of_child(2))
      
  qed  
    
  lemma btu_heapify_down_left_no_right_child:
    assumes HRC: "has_lchild i" "\<not>has_rchild i"
    assumes IHE: "is_heap_except_down_btu l' i xs"
    assumes GE: "xs!lchild i \<^bold>\<ge> xs!i"
    shows "is_heap_except_down_btu l' (lchild i) (swap xs i (lchild i))"
  proof -
    from IHE have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_down_btu_def by auto
    
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp
    
    show ?thesis
      using HRC IHE GE
      unfolding is_heap_except_down_btu_def
      apply (clarsimp simp: swap_nth)
      by (smt child_of_parent children_greater(1) children_in_heap(1) heap_range_context.has_parent_def heap_range_context_axioms leD le_cases less_le_trans parent_of_child(1))
      
  qed  
    
  definition "sift_up_invar xs\<^sub>0 i xs \<equiv>
      slice_eq_mset l h xs xs\<^sub>0      
    \<and> is_heap_except_up i xs"  
    
  lemma sift_up_invar_init: 
    assumes "is_heap xs" "slice_eq_mset l h xs xs\<^sub>0" "h<length xs" 
    shows "heap_context.sift_up_invar (\<^bold>\<le>) l (Suc h) xs\<^sub>0 h xs"
  proof -
    interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "Suc h" by intro_locales (simp add: grow_heap_context)
    
    show ?thesis 
      using assms
      by (meson N.sift_up_invar_def le_eq_less_or_eq nat_in_between_eq(1) ran_not_empty sift_up_init slice_eq_mset_subslice)
      
  qed    
      
  lemma sift_up_invar_step: "\<lbrakk>sift_up_invar xs\<^sub>0 i xs; has_parent i; xs!i\<^bold>\<ge>xs!parent i \<rbrakk> 
    \<Longrightarrow> sift_up_invar xs\<^sub>0 (parent i) (swap xs i (parent i))"
    unfolding sift_up_invar_def
    by (auto simp: sift_up_lemma)
    
  lemma sift_up_invar_term1: "\<lbrakk>sift_up_invar xs\<^sub>0 l xs\<rbrakk> \<Longrightarrow> is_heap xs \<and> slice_eq_mset l h xs xs\<^sub>0"
    unfolding sift_up_invar_def
    using sift_up_term1 by blast
    
  lemma sift_up_invar_term2: "\<lbrakk>sift_up_invar xs\<^sub>0 i xs; xs!i\<^bold>\<le>xs!parent i\<rbrakk> 
    \<Longrightarrow> is_heap xs \<and> slice_eq_mset l h xs xs\<^sub>0"
    unfolding sift_up_invar_def
    using sift_up_term2 by blast

  definition "sift_down_invar xs\<^sub>0 i xs \<equiv>
      slice_eq_mset l h xs xs\<^sub>0      
    \<and> is_heap_except_down i xs"  

  lemma sift_down_invar_step:
    assumes "sift_down_invar xs\<^sub>0 i xs"
    shows "\<lbrakk>has_rchild i; xs!i\<^bold>\<le>xs!lchild i; xs!lchild i \<^bold>\<ge> xs!rchild i\<rbrakk> \<Longrightarrow> sift_down_invar xs\<^sub>0 (lchild i) (swap xs i (lchild i))" 
      and "\<lbrakk>has_rchild i; xs!i\<^bold>\<le>xs!rchild i; xs!lchild i \<^bold>\<le> xs!rchild i\<rbrakk> \<Longrightarrow> sift_down_invar xs\<^sub>0 (rchild i) (swap xs i (rchild i))"
      and "\<lbrakk>has_lchild i; \<not>has_rchild i; xs!i\<^bold>\<le>xs!lchild i\<rbrakk> \<Longrightarrow> sift_down_invar xs\<^sub>0 (lchild i) (swap xs i (lchild i))" 
    using assms unfolding sift_down_invar_def
    by (auto simp: sift_down_lemma_left sift_down_lemma_right sift_down_lemma_left_no_right_child)

  thm sift_down_init (*xxx, ctd here: we need to initialize from heapsort loop invariant*)
  lemma sift_down_invar_init: 
    assumes "is_heap xs" "Suc l < h" 
    shows "heap_context.sift_down_invar (\<^bold>\<le>) l (h-Suc 0) (swap xs l (h-Suc 0)) l (swap xs l (h-Suc 0))"
  proof -
    interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "h-Suc 0" apply intro_locales using assms shrink_heap_context by auto
    show ?thesis using sift_down_init assms unfolding N.sift_down_invar_def 
      by (auto simp: sift_down_init)
      
  qed  

  
  definition "heapify_btu_invar xs\<^sub>0 l' xs \<equiv>
      slice_eq_mset l h xs xs\<^sub>0      
    \<and> is_heap_btu l' xs"
  
  definition "sift_down_btu_invar xs\<^sub>0 l' i xs \<equiv> 
      slice_eq_mset l h xs xs\<^sub>0      
    \<and> is_heap_except_down_btu l' i xs"
    
    
          
end  

context weak_ordering begin

  sublocale singleton_heap_context: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "(Suc l)"
    by unfold_locales auto

  lemma singleton_no_relatives[simp, intro!]:
    "\<not>singleton_heap_context.has_parent l i"  
    "\<not>singleton_heap_context.has_lchild l i"  
    "\<not>singleton_heap_context.has_rchild l i"  
    unfolding singleton_heap_context.heap_context_defs 
    by auto
    
  lemma singleton_heap: "l<length xs \<Longrightarrow> singleton_heap_context.is_heap l xs"  
    unfolding singleton_heap_context.is_heap_def
    by auto

end  

    
context heap_context begin  

context
  fixes  T :: "(nat) \<Rightarrow> (char list, enat) acost"
begin
  definition mop_has_lchild  :: "nat \<Rightarrow> (bool, _) nrest"
    where [simp]: "mop_has_lchild i \<equiv> do { consume (RETURNT (has_lchild i)) (T (i)) }"
  sepref_register "mop_has_lchild"
end

lemma mop_has_lchild:
  "(mop_has_lchild T, mop_has_lchild T) \<in> nat_rel \<rightarrow> \<langle>bool_rel\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI)
  unfolding mop_has_lchild_def 
  by (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)

context
  fixes  T :: "(nat) \<Rightarrow> (char list, enat) acost"
begin
  definition mop_has_rchild  :: "nat \<Rightarrow> (bool, _) nrest"
    where [simp]: "mop_has_rchild i \<equiv> do { consume (RETURNT (has_rchild i)) (T (i)) }"
  sepref_register "mop_has_rchild"
end

lemma mop_has_rchild:
  "(mop_has_rchild T, mop_has_rchild T) \<in> nat_rel \<rightarrow> \<langle>bool_rel\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI)
  unfolding mop_has_rchild_def 
  by (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)

context
  fixes  T :: "(nat) \<Rightarrow> (char list, enat) acost"
begin
  definition mop_lchild  :: "nat \<Rightarrow> (nat, _) nrest"
    where [simp]: "mop_lchild i \<equiv> do { consume (RETURNT (lchild i)) (T (i)) }"
  sepref_register "mop_lchild"
end

lemma mop_lchild:
  "(mop_lchild T, mop_lchild T) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI)
  unfolding mop_lchild_def 
  by (auto simp: pw_acost_le_iff refine_pw_simps)

context
  fixes  T :: "(nat) \<Rightarrow> (char list, enat) acost"
begin
  definition mop_rchild  :: "nat \<Rightarrow> (nat, _) nrest"
    where [simp]: "mop_rchild i \<equiv> do { consume (RETURNT (rchild i)) (T (i)) }"
  sepref_register "mop_rchild"
end

lemma mop_rchild:
  "(mop_rchild T, mop_rchild T) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI) 
  by (auto simp: pw_acost_le_iff refine_pw_simps)
 



abbreviation "mop_has_lchildF \<equiv> mop_has_lchild (\<lambda>_. top)"
abbreviation "mop_has_rchildF \<equiv> mop_has_rchild (\<lambda>_. top)"
abbreviation "mop_lchildF \<equiv> mop_lchild (\<lambda>_. top)"
abbreviation "mop_rchildF \<equiv> mop_rchild (\<lambda>_. top)"

abbreviation "mop_has_lchildN \<equiv> mop_has_lchild (\<lambda>_. cost ''has_lchild'' 1)"
abbreviation "mop_has_rchildN \<equiv> mop_has_rchild (\<lambda>_. cost ''has_rchild'' 1)"
abbreviation "mop_lchildN \<equiv> mop_lchild (\<lambda>_. cost ''lchild'' 1)"
abbreviation "mop_rchildN \<equiv> mop_rchild (\<lambda>_. cost ''rchild'' 1)"


  definition sift_down :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list,_) nrest" where "sift_down i\<^sub>0 xs \<equiv> doN {
    ASSERT (in_heap i\<^sub>0 \<and> i\<^sub>0<length xs);
    _ \<leftarrow> consumea top;
    (xs,i,_) \<leftarrow> monadic_WHILEIT (\<lambda>(xs,i,ctd). in_heap i \<and> i\<ge>i\<^sub>0) 
      (\<lambda>(xs,i,ctd). doN {                
                          hrc \<leftarrow> mop_has_rchildF i;
                          SPECc2F  (\<and>)  hrc ctd
                        }) 
      (\<lambda>(xs,i,ctd). doN {
        lci \<leftarrow> mop_lchildF i;
        lc \<leftarrow> mop_list_getF xs lci;
        rci \<leftarrow> mop_rchildF i;
        rc \<leftarrow> mop_list_getF xs rci;
        v \<leftarrow> mop_list_getF xs i;
      
        b1 \<leftarrow> SPECc2F (\<^bold><)  lc rc;
        MIf b1 (doN {
          b2 \<leftarrow> SPECc2F  (\<^bold><)  v rc;
          MIf b2 (doN {
                xs \<leftarrow> mop_list_swapF xs i rci;
                RETURN (xs,rci,True)
              })
             (RETURN (xs,i,False))
          })
        ( 
          doN {
          b3 \<leftarrow> SPECc2F  (\<^bold><)  v lc;
          MIf b3 (doN {
                  xs \<leftarrow> mop_list_swapF xs i lci;
                  RETURN (xs,lci,True)
               })
             ( RETURN (xs,i,False))
          }
      ) }) 
    (xs,i\<^sub>0,True);
  
    ASSERT (in_heap i \<and> i\<ge>i\<^sub>0);
    ASSERT (has_lchild i \<longrightarrow> lchild i < length xs);
    
    hlc \<leftarrow> mop_has_lchildF i;
    MIf hlc (doN {
          lci \<leftarrow> mop_lchildF i;
          b \<leftarrow> mop_cmp_idxs top xs i lci;
          MIf b (mop_list_swapF xs i lci)
              (doN { _ \<leftarrow> consumea top; RETURN xs })
          })
      ( doN {_ \<leftarrow> consumea top; RETURN xs })
      
  }"

  lemma in_heap_len_bound: "in_heap i \<Longrightarrow> h\<le>length xs \<Longrightarrow> i<length xs"
    using in_heap_bounds(2) less_le_trans by blast

 
declare less_eq_option_Some_None[simp]
lemma ifSome_iff: "(if b then Some T else None) = Some T' \<longleftrightarrow> T=T' \<and> b"
  by (auto split: if_splits)

  lemma sift_down_btu_correct:
    assumes "heapify_btu_invar xs\<^sub>0 l' xs" "l<l'"
    shows "sift_down (l'-Suc 0) xs \<le> SPEC (\<lambda>xs'. heapify_btu_invar xs\<^sub>0 (l'-Suc 0) xs') (\<lambda>_. top)" 
    unfolding sift_down_def
    unfolding SPEC_def
    apply(rule gwp_specifies_I)

    supply wr = monadic_WHILE_rule_real[OF refl, where 
      I="\<lambda>(xs,i,ctd). if (in_heap i \<and> i\<ge>(l'-Suc 0) \<and>
          sift_down_btu_invar xs\<^sub>0 (l'-Suc 0) i xs 
          \<and> h\<le>length xs
          \<and> (\<not>ctd \<longrightarrow> has_rchild i \<and> xs!i\<^bold>\<ge>xs!lchild i \<and> xs!i\<^bold>\<ge>xs!rchild i)) then Some top else None"
      and
      R = "measure (\<lambda>(xs,i,ctd). (if ctd then 1 else 0) + h - i)"    
    ]
    unfolding mop_has_rchild_def mop_has_lchild_def mop_lchild_def mop_rchild_def
          mop_cmp_idxs_def SPECc2_def mop_list_get_def mop_list_swap_def consumea_def
    apply (refine_vcg \<open>-\<close> rules: wr if_rule2 if_rule prod3) 
    using assms    
    unfolding heapify_btu_invar_def sift_down_btu_invar_def
    apply (simp_all add: ifSome_iff del: in_heap_simps)
    apply (all \<open>(auto simp: in_heap_len_bound diff_less_mono2 wo_leI; fail)?\<close>) (** Takes loooong *)
    subgoal by (force simp:  asym wo_leI simp: btu_heapify_down_right)  

    subgoal by (simp add: diff_less_mono2 less_Suc_eq)
    subgoal by simp (metis wo_leI wo_less_trans)
    subgoal by (simp add: diff_less_mono less_imp_le)
    subgoal by (force simp add: btu_heapify_down_left asym wo_leI)
    subgoal by (simp add: diff_less_mono2 less_Suc_eq)
    subgoal apply simp using local.trans wo_leI by blast
    subgoal by (simp add: diff_less_mono less_imp_le)
    subgoal 
      apply clarsimp
      using btu_heapify_down_left_no_right_child btu_sift_down_term1 connex lchild_of_no_rchild_term wo_leD by blast
    subgoal 
      apply clarsimp
      using btu_sift_down_term1 btu_sift_down_term2 btu_sift_down_term3 wo_leI by blast
    subgoal 
      apply clarsimp
      using btu_sift_down_term1 btu_sift_down_term2 btu_sift_down_term3 wo_leI by blast

    subgoal using btu_sift_down_init apply (auto simp: top_acost_absorbs)  
      using is_heap_btu_def by blast
    subgoal by (auto split: prod.splits simp: ifSome_iff)
    subgoal unfolding is_heap_btu_def by (auto intro!: in_heapI)
    done

  lemma sift_down_restore_correct: 
    assumes A: "l<h" "sift_down_invar xs\<^sub>0 l xs"
    shows "sift_down l xs \<le> SPEC (\<lambda>xs'. slice_eq_mset l h xs' xs\<^sub>0 \<and> is_heap xs') (\<lambda>_. top)"
    unfolding sift_down_def
    unfolding SPEC_def
    apply(rule gwp_specifies_I)
    unfolding mop_has_rchild_def mop_has_lchild_def mop_lchild_def mop_rchild_def
          mop_cmp_idxs_def SPECc2_def mop_list_get_def mop_list_swap_def consumea_def
    apply (refine_vcg \<open>-\<close> rules: monadic_WHILE_rule_real[OF refl, where 
      I="\<lambda>(xs,i,ctd). if (in_heap i \<and> i\<ge>l \<and>
          sift_down_invar xs\<^sub>0 i xs 
          \<and> h\<le>length xs
          \<and> (\<not>ctd \<longrightarrow> has_rchild i \<and> xs!i\<^bold>\<ge>xs!lchild i \<and> xs!i\<^bold>\<ge>xs!rchild i)) then Some top else None"
      and
      R = "measure (\<lambda>(xs,i,ctd). (if ctd then 1 else 0) + h - i)"    
    ] if_rule2 if_rule prod3)
    apply (clarsimp_all simp add: ifSome_iff)
    apply (all \<open>(auto simp: in_heap_len_bound diff_less_mono2 A sift_down_invar_step wo_leI root_in_heap; fail)?\<close>)
    subgoal using asym sift_down_invar_step(2) wo_leI by blast
    subgoal by (simp add: diff_less_mono2 less_SucI)
    subgoal using wo_less_trans wo_not_le_imp_less by blast
    subgoal by (simp add: Suc_diff_le less_imp_le)
    subgoal using asym sift_down_invar_step(1) wo_leI by blast
    subgoal by (simp add: diff_less_mono2 less_Suc_eq)
    subgoal using itrans wo_leI by blast 
    subgoal by (simp add: Suc_diff_le less_imp_le)
    subgoal apply rule
      subgoal unfolding sift_down_invar_def by simp    
      subgoal by (meson lchild_of_no_rchild_term sift_down_invar_def sift_down_invar_step(3) sift_down_term1 wo_leD wo_leI wo_less_not_sym)
      done
    subgoal apply rule   
      subgoal unfolding sift_down_invar_def by simp     
      subgoal unfolding sift_down_invar_def by (meson wo_leI sift_down_term1 sift_down_term2 sift_down_term3)
      done
    subgoal apply rule
      subgoal unfolding sift_down_invar_def by simp    
      subgoal by (meson lchild_of_no_rchild_term less_imp_le not_le sift_down_invar_def sift_down_lemma_left_no_right_child sift_down_term1)
      done
    subgoal using A unfolding sift_down_invar_def is_heap_except_down_def by (auto simp: top_acost_absorbs)
    subgoal using A unfolding sift_down_invar_def is_heap_except_down_def root_in_heap by auto
    done
    
    
    
  text \<open>Deferred swap optimization\<close>

  definition sift_down1 :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list,_) nrest" where "sift_down1 i\<^sub>0 xs \<equiv> doN {
    ASSERT (in_heap i\<^sub>0);
    v \<leftarrow> mop_list_getF xs i\<^sub>0;
    (xs,i,_) \<leftarrow> monadic_WHILEIT (\<lambda>(xs,i,ctd). in_heap i \<and> i\<ge>i\<^sub>0) 
      (\<lambda>(xs,i,ctd). doN {                
                          hrc \<leftarrow> mop_has_rchildF i;
                          SPECc2F  (\<and>)  hrc ctd
                        })
    (\<lambda>(xs,i,ctd). doN {
        lci \<leftarrow> mop_lchildF i;
        rci \<leftarrow> mop_rchildF i;
        lc \<leftarrow> mop_list_getF xs lci;
        rc \<leftarrow> mop_list_getF xs rci;
        _ \<leftarrow> consumea 0;
    
      b1 \<leftarrow> SPECc2F  (\<^bold><)  lc rc;
      MIf b1 (doN {
          b2 \<leftarrow> SPECc2F  (\<^bold><)  v rc;
          MIf b2 (doN {
              t \<leftarrow> mop_list_getF xs rci;
              xs \<leftarrow> mop_list_setF xs i t;
              RETURN (xs,rci,True)
              })
             (RETURN (xs,i,False))
            })
            (doN {
              b3 \<leftarrow> SPECc2F  (\<^bold><)  v lc;
              MIf b3 (doN {
                  t \<leftarrow> mop_list_getF xs lci;
                  xs \<leftarrow> mop_list_setF xs i t;
                  RETURN (xs,lci,True)
              }) 
              (RETURN (xs,i,False))} )
    }) (xs,i\<^sub>0,True);

    ASSERT (in_heap i \<and> i\<ge>i\<^sub>0);
    ASSERT (has_lchild i \<longrightarrow> lchild i < length xs);
    
    hlc \<leftarrow> mop_has_lchildF i;
    MIf hlc (doN {
              lci \<leftarrow> mop_lchildF i;
              b \<leftarrow> mop_cmp_v_idx top xs v lci;
              MIf b (doN {
                  t \<leftarrow> mop_list_getF xs lci;
                  xs \<leftarrow> mop_list_setF xs i t;
                  xs \<leftarrow> mop_list_setF xs lci v;
                  RETURN xs })
                (doN {
                  xs \<leftarrow> mop_list_setF xs i v;
                  RETURN xs}
                )
              })
              (doN {
                xs \<leftarrow> mop_list_setF xs i v;
                RETURN xs})
  }" 


  definition "swap_opt_rel v \<equiv> {((xs,i,ctd),(xs',i',ctd')). xs' = xs[i:=v] \<and> i<length xs \<and> i'=i \<and> ctd'=ctd }"

  thm swap_opt_rel_def

 lemma sift_down1_refine_functional_aux: "sift_down1 i\<^sub>0 xs \<le> \<Down> Id (timerefine TId (sift_down i\<^sub>0 xs))" 
    unfolding sift_down1_def sift_down_def
    unfolding mop_list_get_def mop_list_swap_def mop_list_set_def 
              mop_lchild_def mop_rchild_def mop_has_rchild_def mop_has_lchild_def
              SPECc2_alt mop_cmp_idxs_def mop_cmp_v_idx_def
    apply normalize_blocks
    apply (refine_rcg consumea_Id_refine bindT_refine_easy
            monadic_WHILEIT_refine_t[where R="swap_opt_rel (xs ! i\<^sub>0)"]
            MIf_refine
          )
    supply [simp del] = conc_Id  
    apply(auto simp: swap_opt_rel_def top_acost_absorbs swap_def)
    done


    
  text \<open>Index shift optimization\<close>
  
  definition "ihs_opt_rel \<equiv> {((xs,i,ctd),(xs',i',ctd')). xs' = xs \<and> i' = i+l \<and> ctd'=ctd }"
  
  lemma ihs_opt_rel_alt: "((xs,i,ctd), (xs',i',ctd'))\<in>ihs_opt_rel \<longleftrightarrow> xs'=xs \<and> (i',i)\<in>idx_shift_rel l \<and> ctd'=ctd"
    unfolding ihs_opt_rel_def idx_shift_rel_def by auto

    
  definition [simp]: "mop_lchild2 i \<equiv> doN { ASSERT (2*i+1<h); consume (RETURN (2*i+1))  ( cost ''lchild'' 1) }"
  definition [simp]: "mop_rchild2 i \<equiv> doN { ASSERT (2*i+2<h); consume (RETURN (2*i+2))  ( cost ''rchild'' 1) }"
  definition [simp]: "has_rchild2 i \<equiv> i<(h-l-1) div 2"
  definition [simp]: "has_lchild2 i \<equiv> i<(h-l) div 2"
  definition [simp]: "mop_has_lchild2  i \<equiv> do { consume (RETURNT (has_lchild2 i)) (cost ''has_lchild'' 1) }"
  definition [simp]: "mop_has_rchild2  i \<equiv> do { consume (RETURNT (has_rchild2 i)) (cost ''has_rchild'' 1) }"

  definition [simp]: "mop_lchild2F i \<equiv> doN { ASSERT (2*i+1<h); consume (RETURN (2*i+1))  top }"
  definition [simp]: "mop_rchild2F i \<equiv> doN { ASSERT (2*i+2<h); consume (RETURN (2*i+2))  top }"
  definition [simp]: "mop_has_lchild2F  i \<equiv> do { consume (RETURNT (has_lchild2 i)) top }"
  definition [simp]: "mop_has_rchild2F  i \<equiv> do { consume (RETURNT (has_rchild2 i)) top }"


  definition [simp]: "mop_lchild_l' i \<equiv> doN { ASSERT (2*i+1<h); i'\<leftarrow>SPECc2 ''mul'' (*) i 2; SPECc2 ''add'' (+) i' 1 }"
  definition [simp]: "mop_rchild_l' i \<equiv> doN { ASSERT (2*i+2<h); i'\<leftarrow>SPECc2 ''mul'' (*) i 2; SPECc2 ''add'' (+) i' 2 }"
  definition [simp]: "mop_has_lchild_l'  i \<equiv> do { hl \<leftarrow> SPECc2 ''sub'' (-) h l; hld2 \<leftarrow> SPECc2 ''udiv'' (div) hl 2; SPECc2 ''icmp_slt'' (<) i hld2 }"
  definition [simp]: "mop_has_rchild_l'  i \<equiv> do { hl \<leftarrow> SPECc2 ''sub'' (-) h l; hl1 \<leftarrow> SPECc2 ''sub'' (-) hl 1; hld2 \<leftarrow> SPECc2 ''udiv'' (div) hl1 2; SPECc2 ''icmp_slt'' (<) i hld2 }"

      
end  
  
concrete_definition mop_lchild3 is heap_context.mop_lchild_l'_def
concrete_definition mop_rchild3 is heap_context.mop_rchild_l'_def
concrete_definition has_rchild3 is heap_context.has_rchild2_def
concrete_definition has_lchild3 is heap_context.has_lchild2_def
concrete_definition mop_has_lchild3 is heap_context.mop_has_lchild_l'_def
concrete_definition mop_has_rchild3 is heap_context.mop_has_rchild_l'_def

concrete_definition mop_lchild3F is heap_context.mop_lchild2F_def
concrete_definition mop_rchild3F is heap_context.mop_rchild2F_def
concrete_definition mop_has_lchild3F is heap_context.mop_has_lchild2F_def
concrete_definition mop_has_rchild3F is heap_context.mop_has_rchild2F_def
  
lemmas h_aux_refines = mop_lchild3.refine mop_rchild3.refine has_rchild3.refine 
  has_lchild3.refine  mop_has_lchild3.refine
  mop_lchild3F.refine mop_rchild3F.refine mop_has_lchild3F.refine mop_has_rchild3F.refine

context heap_context begin  


  definition sift_down2 :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list,_) nrest" where "sift_down2 i\<^sub>0 xs \<equiv> doN {
    ASSERT (l\<le>i\<^sub>0 \<and> i\<^sub>0<h);
    let i\<^sub>1 = i\<^sub>0 - l;
    
    v \<leftarrow> mop_list_getF xs (i\<^sub>1+l);
    
    (xs,i,_) \<leftarrow> monadic_WHILEIT (\<lambda>(xs,i,ctd). i<h-l \<and> i\<ge>i\<^sub>1)
       (\<lambda>(xs,i,ctd). do { hrc \<leftarrow> mop_has_rchild3F l h i;
                          SPECc2F (\<and>) hrc ctd })
       (\<lambda>(xs,i,ctd). doN {
      lci \<leftarrow> mop_lchild3F h i;
      rci \<leftarrow> mop_rchild3F h i;
      ASSERT (lci+l<h \<and> rci+l<h);
      ASSERT (lci\<noteq>i \<and> rci\<noteq>i \<and> lci\<noteq>rci);
      lc \<leftarrow> mop_list_getF xs (lci+l);
      rc \<leftarrow> mop_list_getF xs (rci+l);
    
      ASSERT (i+l<h);
      
      b1 \<leftarrow> SPECc2F (\<^bold><)  lc rc;
      MIf b1 (doN {
        b2 \<leftarrow> SPECc2F  (\<^bold><)  v rc;
        MIf b2 (doN {
          xs \<leftarrow> mop_list_setF xs (i+l) rc;
          RETURN (xs,rci,True)
        }) ( RETURN (xs,i,False) )
      }) (doN {
        b3 \<leftarrow> SPECc2F  (\<^bold><)  v lc;
        MIf b3 (doN {
          xs \<leftarrow> mop_list_setF xs (i+l) lc;
          RETURN (xs,lci,True)
          })
         ( RETURN (xs,i,False) ) })
    }) (xs,i\<^sub>1,True);
    
    ASSERT (i\<ge>i\<^sub>1 \<and> i+l<h);
    
    hlc \<leftarrow> mop_has_lchild3F l h i;
    MIf hlc ( doN {
      lci \<leftarrow> mop_lchild3F h i;
      ASSERT (lci+l<h);
      ASSERT (lci\<noteq>i);
      lc \<leftarrow> mop_list_getF xs (lci+l);
      b \<leftarrow> SPECc2F  (\<^bold><)  v lc;
      MIf b (doN {
        xs \<leftarrow> mop_list_setF xs (i+l) lc;
        xs \<leftarrow> mop_list_setF xs (lci+l) v;
        RETURN xs
      } ) ( doN {
        xs \<leftarrow> mop_list_setF xs (i+l) v;
        RETURN xs
      }  )
    } ) ( doN {
      xs \<leftarrow> mop_list_setF xs (i+l) v;
      RETURN xs
    } )
  }"

    
  lemma idx_shift_adjust:
    assumes "(i',i)\<in>idx_shift_rel l"
    shows 
      "in_heap i' \<longleftrightarrow> i<h-l"
      "has_lchild i' \<longleftrightarrow> i<(h-l) div 2"
      "has_rchild i' \<longleftrightarrow> i<(h-l-1) div 2"
      "lchild i' = 2*i+1+l"
      "rchild i' = 2*i+2+l"
      "i+l = i'"
      "i'<x \<longleftrightarrow> i<x-l"
      "i'\<le>h \<longleftrightarrow> i\<le>h-l"
      "x\<le>i' \<longleftrightarrow> x-l\<le>i"
    using assms
    thm lchild_ihs
    unfolding idx_shift_rel_def 
      in_heap_def 
      has_rchild_def rchild_def
      has_lchild_def lchild_def
    by auto



 lemma sift_down2_refine: "sift_down2 i xs \<le> \<Down>Id (timerefine TId (sift_down1 i xs))"
    unfolding sift_down1_def sift_down2_def 
    unfolding h_aux_refines[OF heap_context_axioms, symmetric]
    supply [simp del] = conc_Id
    apply (simp cong: if_cong)
    apply (rewrite at "let i=i-l in _" Let_def) 
    unfolding SPECc2_alt
    apply normalize_blocks

    apply (intro refine0)
      apply (all \<open>unfold in_heap_def; simp_all; fail \<close>) [2]
    apply(rule bindT_refine_easy)
    subgoal by simp
     apply(rule consumea_Id_refine)
    subgoal by simp
    apply(rule bindT_refine_easy)
    subgoal by simp
    focus
      apply (refine_rcg bindT_refine_easy monadic_WHILEIT_refine' MIf_refine consumea_Id_refine)
      supply [refine_dref_RELATES] = RELATESI[of ihs_opt_rel]  
      apply refine_dref_type
      apply(simp_all only: wfR''_TId sp_TId top_acost_absorbs )
      apply (simp_all add: ihs_opt_rel_alt ) (** Takes loooong *)
      apply (all \<open>(determ \<open>elim conjE\<close>)?; simp?\<close>)
      apply (clarsimp_all simp: idx_shift_adjust ihs_opt_rel_alt simp del: in_heap_simps) (** Takes loooong *)
      unfolding in_heap_def idx_shift_rel_def ihs_opt_rel_alt
      apply (auto simp: algebra_simps)  
      solved
    subgoal for _ _ s s'
      supply [split del] = if_split
      apply (cases s; simp)
      apply (cases s'; simp)
      apply (intro refine0 )
      subgoal by (clarsimp simp: idx_shift_adjust ihs_opt_rel_alt)

      apply(rule bindT_refine_easy)
      subgoal by simp
       apply(rule consumea_Id_refine)
      subgoal by simp
    
      apply (refine_rcg bindT_refine_easy MIf_refine consumea_Id_refine)
      apply(simp_all only: wfR''_TId sp_TId top_acost_absorbs)  
        apply (simp_all add: ihs_opt_rel_alt)
        apply (all \<open>determ \<open>elim conjE\<close>; simp?\<close>)
        apply (auto simp: algebra_simps idx_shift_adjust)
        done 
     done
       
  
  
  (* Auxiliary definitions to reduce proof complexity in sepref-step.
    TODO: Without these, the sepref step gets really slow, which is another indication that we
      should separate the bound-proofs from the actual transfer step!
  *)
  definition [simp]: "mop_geth2 xs i \<equiv> doN { ASSERT(l+i\<le>h); lpi \<leftarrow> SPECc2 ''add'' (+) l i;  mop_eo_extract (\<lambda>_. lift_acost mop_array_nth_cost) xs lpi }"
  definition [simp]: "mop_seth2 xs i x \<equiv> doN { ASSERT(l+i\<le>h); lpi \<leftarrow> SPECc2 ''add'' (+) l i;  mop_eo_set (\<lambda>_. lift_acost mop_array_upd_cost) xs lpi x }"

  thm mop_oarray_extract_def

end  
  
concrete_definition mop_geth3 is heap_context.mop_geth2_def
concrete_definition mop_seth3 is heap_context.mop_seth2_def
  
lemmas h_aux_refines2 = mop_geth3.refine mop_seth3.refine  

context heap_context begin  
  
  term mop_geth3
  definition sift_down3 :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list, _) nrest" where "sift_down3 i\<^sub>0 xs \<equiv> doN {
    ASSERT (l\<le>i\<^sub>0 \<and> i\<^sub>0<h);
    i\<^sub>1 \<leftarrow> SPECc2 ''sub'' (-) i\<^sub>0 l;
    xs \<leftarrow> mop_to_eo_conv xs;
    (v,xs) \<leftarrow> mop_geth3 l h xs i\<^sub>1;
    
    (xs,i,_) \<leftarrow> monadic_WHILEIT (\<lambda>(xs,i,ctd). i<h-l \<and> i\<ge>i\<^sub>1)
       (\<lambda>(xs,i,ctd). do { hrc \<leftarrow> mop_has_rchild3 l h i;
                          SPECc2 ''and'' (\<and>) hrc ctd }) (\<lambda>(xs,i,ctd). doN {
      lci \<leftarrow> mop_lchild3 h i;
      rci \<leftarrow> mop_rchild3 h i;

      ASSERT (l+lci<h \<and> l+rci<h \<and> l+lci \<noteq> l+rci);
      lplci \<leftarrow> SPECc2 ''add'' (+) l lci;
      lprci \<leftarrow> SPECc2 ''add'' (+) l rci;
      ASSERT(lplci\<noteq>lprci);
      b \<leftarrow> mop_cmpo_idxs (cost ''cmpo_idxs'' 1) xs lplci lprci;
      
      MIf b (doN {
        b \<leftarrow> mop_cmpo_v_idx (cost ''cmpo_v_idxs'' 1) xs v lprci; \<comment> \<open>this is actually one more list_get then in sift_down2 !\<close>
        MIf b ( doN {
          (rc,xs) \<leftarrow> mop_geth3 l h xs rci;
          xs \<leftarrow> mop_seth3 l h xs i rc;
          RETURN (xs,rci,True)
        } ) (  RETURN (xs,i,False) )
      } ) ( doN {
        b \<leftarrow> mop_cmpo_v_idx (cost ''cmpo_v_idxs'' 1) xs v lplci;
        MIf b ( doN {
          (lc,xs) \<leftarrow> mop_geth3 l h xs lci;
          xs \<leftarrow> mop_seth3 l h xs i lc;
          RETURN (xs,lci,True)
        } ) ( RETURN (xs,i,False) )
      } )
    }) (xs,i\<^sub>1,True);
    
    ASSERT (i\<ge>i\<^sub>1);
    
    hlc \<leftarrow> mop_has_lchild3 l h i;
    MIf hlc ( doN {
      lci \<leftarrow> mop_lchild3 h i;
      ASSERT (l+lci<h);
      lplci \<leftarrow> SPECc2 ''add'' (+) l lci;
      b \<leftarrow> mop_cmpo_v_idx (cost ''cmpo_v_idxs'' 1) xs v lplci;
      MIf b ( doN {
        (lc,xs) \<leftarrow> mop_geth3 l h xs lci;
        xs \<leftarrow> mop_seth3 l h xs i lc;
        xs \<leftarrow> mop_seth3 l h xs lci v;
        xs \<leftarrow> mop_to_wo_conv xs;
        RETURN xs
      } )( doN {
        xs \<leftarrow> mop_seth3 l h xs i v;
        xs \<leftarrow> mop_to_wo_conv xs;
        RETURN xs
      }  )
    } )( doN {
      xs \<leftarrow> mop_seth3 l h xs i v;
      xs \<leftarrow> mop_to_wo_conv xs;
      RETURN xs
    }  )
  }" 
    
  
  (* TODO: Move. Use also in insort. Maybe generalize to index set? *)
  definition "woe_eq_except i xs' xs \<equiv> length xs' = length xs \<and> xs'!i=None \<and> (\<forall>j\<in>{0..<length xs}-{i}. xs'!j = Some (xs!j))"
  
  lemma woe_eq_except_init: "i<length xs \<Longrightarrow> woe_eq_except i ((map Some xs)[i := None]) xs"
    unfolding woe_eq_except_def by auto
  
  lemma woe_eq_except_length[simp]: "woe_eq_except i xs' xs \<Longrightarrow> length xs'=length xs"
    unfolding woe_eq_except_def by auto
    
  lemma woe_eq_except_nth_eq_Some: "\<lbrakk>woe_eq_except i xs' xs; j<length xs\<rbrakk> \<Longrightarrow> xs'!j = Some v \<longleftrightarrow> (j\<noteq>i \<and> v = xs!j)"  
    unfolding woe_eq_except_def 
    by force
    
  lemma woe_eq_except_nth: "\<lbrakk>woe_eq_except i xs' xs; j<length xs; j\<noteq>i\<rbrakk> \<Longrightarrow> xs'!j = Some (xs!j)"  
    unfolding woe_eq_except_def 
    by force
    
  lemma woe_eq_except_ith[simp]: "\<lbrakk>woe_eq_except i xs' xs\<rbrakk> \<Longrightarrow> xs'!i = None"  
    unfolding woe_eq_except_def 
    by force
    
  lemma woe_eq_except_upd:
    assumes "woe_eq_except i xs' xs" "i'<length xs" "i<length xs" "i\<noteq>i'"
    shows "woe_eq_except i' (xs'[i':=None,i:=Some v]) (xs[i:=v])"
    using assms unfolding woe_eq_except_def by (auto simp: nth_list_update)
    
    
  
  definition "sd23_rel \<equiv> {((xs',i',ctd'),(xs,i,ctd)). i'=i \<and> ctd'=ctd \<and> i+l<length xs \<and> woe_eq_except (i+l) xs' xs }"
  
  lemma in_sd23_rel_conv: "((xs',i',ctd'),(xs,i,ctd))\<in>sd23_rel \<longleftrightarrow> i'=i \<and> ctd'=ctd \<and> i+l<length xs \<and> woe_eq_except (i+l) xs' xs"
    by (auto simp: sd23_rel_def)

(* TODO: Move *)
  lemma introR: "(a,a')\<in>R \<Longrightarrow> (a,a')\<in>R" .

  lemma mop_has_lchild3_refine: "(a,a')\<in>Id \<Longrightarrow> (mop_has_lchild3 l h a :: (_, (_, enat) acost) nrest) \<le> \<Down> bool_rel (timerefine TId (mop_has_lchild3F l h a'))"
    apply(auto simp: mop_has_lchild3_def SPECc2_alt mop_has_lchild3F_def simp del: conc_Id) 
    apply normalize_blocks
    apply(intro refine0 bindT_refine_easy RETURNT_refine_t consumea_refine) by auto 


  lemma mop_has_rchild3_refine: "(a,a')\<in>Id \<Longrightarrow> (mop_has_rchild3 l h a :: (_, (_, enat) acost) nrest) \<le> \<Down> bool_rel (timerefine TId (mop_has_rchild3F l h a'))"
    apply(auto simp: mop_has_rchild3_def SPECc2_alt mop_has_rchild3F_def simp del: conc_Id) 
    apply normalize_blocks
    apply(intro refine0 bindT_refine_easy RETURNT_refine_t consumea_refine) by auto 

  
  lemma mop_lchild3_refine: "(a,a')\<in>Id \<Longrightarrow> (mop_lchild3 h a:: (_, (_, enat) acost) nrest) \<le> \<Down> Id (timerefine TId (mop_lchild3F h a'))"
    apply(auto simp: mop_lchild3_def SPECc2_alt mop_lchild3F_def simp del: conc_Id) 
    apply normalize_blocks
    apply(intro refine0 bindT_refine_easy  RETURNT_refine_t consumea_refine) by auto 




  lemma inres_mop_has_lchild3F: "inres (mop_has_lchild3F l h a) t \<longleftrightarrow> (has_lchild2 a \<longleftrightarrow> t)"
    unfolding mop_has_lchild3F_def by(simp add: inres_consume_conv)
  
  lemma inres_mop_lchild3F: "inres (mop_lchild3F h a) a' \<longleftrightarrow> Suc (2 * a) < h \<and> Suc (2 * a) = a'"
    unfolding mop_lchild3F_def by (simp add: inres_consume_conv)



  lemma sift_down3_refine_funct: "sift_down3 i xs \<le>\<Down>Id (timerefine TId (sift_down2 i xs))"
    unfolding sift_down3_def sift_down2_def
    supply [simp del] = conc_Id
    supply [simp] = mop_to_eo_conv_alt
    apply (simp add: Let_def mop_geth3_def  cong: if_cong)
    unfolding SPECc2_alt
    apply normalize_blocks
    
    apply (intro refine0)
    apply clarsimp_all [3]
    apply (rule bindT_refine_easy)
    subgoal by simp
    focus
      apply (auto intro!: consumea_refine timerefineA_TId RETURNT_refine_t)
      solved
    subgoal
      for s s'
      apply(cases s; simp)
    apply (rule bindT_refine_easy)
    subgoal by simp
     apply (rule monadic_WHILEIT_refine')
    subgoal by simp
    subgoal by simp
    apply (rule introR[where R=sd23_rel])
    apply (auto simp: sd23_rel_def woe_eq_except_init) []
    apply (auto simp: sd23_rel_def) []
    subgoal 
      unfolding  SPECc2_alt
      apply (refine_rcg bindT_refine_conc_time_my_inres consumea_refine mop_has_rchild3_refine)
      apply refine_dref_type
      by (auto simp: sd23_rel_def ) 
    subgoal
      unfolding mop_has_rchild3F_def
      apply clarsimp
      unfolding mop_lchild3_def mop_rchild3_def mop_cmpo_idxs_def mop_lchild3F_def mop_rchild3F_def SPECc2_alt
      apply normalize_blocks
      apply (intro refine0 bindT_refine_easy)
            apply refine_dref_type
            apply (use [[put_named_ss Main_ss]] in \<open>auto simp: conc_Id in_sd23_rel_conv woe_eq_except_length woe_eq_except_nth\<close>) [6]
        apply simp
      subgoal apply(rule consumea_Id_refine) by (simp only: top_acost_absorbs timerefineA_TId_eq top_greatest)

      unfolding mop_seth3_def SPECc2_alt
      apply simp
      apply normalize_blocks
      apply(refine_rcg MIf_refine bindT_refine_easy)
                         apply refine_dref_type
      apply (auto simp only: sp_TId wfR''_TId timerefineA_TId_eq top_greatest intro!: consumea_refine)
      
      apply (auto simp: in_sd23_rel_conv woe_eq_except_length woe_eq_except_nth
                algebra_simps woe_eq_except_ith woe_eq_except_upd) (** Takes loooooooong *)
      done
    subgoal
      unfolding mop_to_wo_conv_def 
      apply (clarsimp split: prod.split split del: if_split cong: if_cong simp: mop_seth3_def SPECc2_alt ) 
      apply normalize_blocks
      apply (clarsimp split: prod.split)
      apply (refine_rcg MIf_refine bindT_refine_easy mop_has_lchild3_refine mop_lchild3_refine consume_refine)
      apply refine_dref_type
      apply (auto simp only: inres_mop_has_lchild3F inres_mop_lchild3F sp_TId wfR''_TId
                        timerefineA_TId_eq top_acost_absorbs top_greatest intro!: consumea_refine)
      unfolding has_lchild2_def
      supply [[put_named_ss Main_ss]]
      apply (auto simp: conc_Id in_sd23_rel_conv woe_eq_except_length woe_eq_except_nth algebra_simps woe_eq_except_ith woe_eq_except_upd in_set_conv_nth nth_list_update list_eq_iff_nth_eq)
      subgoal by (smt length_list_update nth_list_update_eq nth_list_update_neq singleton_heap_context.ifSome_iff woe_eq_except_length woe_eq_except_nth_eq_Some)
      subgoal by (metis woe_eq_except_init woe_eq_except_ith woe_eq_except_nth_eq_Some)   
      subgoal by (metis option.simps(3) woe_eq_except_nth) 
      done
    done
  done


abbreviation "cost_lchild p \<equiv> cost ''mul'' p + cost ''add'' p"
abbreviation "cost_rchild p \<equiv> cost ''mul'' p + cost ''add'' p"
abbreviation "cost_has_lchild p \<equiv> cost ''sub'' p + cost ''udiv'' p + cost ''icmp_slt'' p"
abbreviation "cost_has_rchild p \<equiv> cost ''sub'' (2*p) + cost ''udiv'' p + cost ''icmp_slt'' p"

definition E_sd3_l :: "_ \<Rightarrow> _ \<Rightarrow> (char list, nat) acost" where
  "E_sd3_l i ctd \<equiv> 
      (let p=(if ctd then 1+i else i) in
            cost ''add'' (4*p) +
            ( (acostC (\<lambda>x. the_acost mop_array_nth_cost x * p))) +
           ( ( (acostC (\<lambda>x. the_acost mop_array_upd_cost x * p))) +
            (cost ''if'' p + (cost ''cmpo_idxs'' p + (cost ''if'' p + (cost ''cmpo_v_idxs'' p
           + (cost_rchild p + (cost_lchild (2*p) + (cost ''call'' p + (cost_has_rchild (2*p)
             + cost ''and'' p + cost ''if'' p))))))))))"

definition sift_down3_cost :: "_ \<Rightarrow> ecost" where
  "sift_down3_cost i =
            cost ''sub'' 1
      + cost ''add'' 5 
      + lift_acost mop_array_upd_cost + lift_acost mop_array_nth_cost + lift_acost mop_array_upd_cost
      + cost ''if'' 1 + cost ''cmpo_v_idxs'' 1 + cost_lchild 1 + cost ''if'' 1 
      + cost_has_lchild 2 +
      lift_acost (E_sd3_l i True) 
      + cost_has_rchild 2 + cost ''and'' 1 + cost ''if'' 1 + lift_acost mop_array_nth_cost
      + lift_acost mop_array_upd_cost + lift_acost mop_array_nth_cost
      + cost ''call'' 1"



lemma sift_down3_refine_time: "sift_down3 i (xs:: 'a list) \<le>\<^sub>n (SPEC (\<lambda>_. True) (%_. sift_down3_cost (h-i)))"
  unfolding sift_down3_def SPEC_def
    apply(rule gwpn_specifies_I)


  apply(subst monadic_WHILEIET_def[symmetric, where E="\<lambda>(_,i,ctd). E_sd3_l ((h-l)-i) ctd"])
                         
  unfolding Let_def mop_to_eo_conv_def mop_geth3_def mop_eo_extract_def
  unfolding mop_has_rchild3_def mop_lchild3_def mop_rchild3_def 
            mop_cmpo_idxs_def mop_cmpo_v_idx_def mop_seth3_def mop_eo_set_def
            SPECc2_def

    apply(refine_vcg \<open>-\<close> rules:  gwpn_bindT_I gwpn_ASSERT_bind_I  gwpn_ASSERT_I gwpn_MIf_I
                      gwpn_consume gwpn_RETURNT_I gwpn_SPECT_I 
                      prod3 if_rule2 if_rule) 
  apply(rule gwpn_monadic_WHILEIET)
  subgoal unfolding wfR2_def E_sd3_l_def zero_acost_def cost_def Let_def by auto
  subgoal for e xs s
    apply(refine_vcg \<open>-\<close> rules: gwpn_bindT_I gwpn_consume gwpn_RETURNT_I gwpn_SPECT_I if_rule gwpn_ASSERT_I gwpn_MIf_I)
        prefer 5
    subgoal (* exiting loop because of wrong guard *)
      apply(rule loop_exit_conditionI)
      unfolding mop_has_lchild3_def mop_to_wo_conv_def SPECc2_alt
      apply (refine_vcg \<open>-\<close> rules: gwpn_bindT_I gwpn_consume gwpn_RETURNT_I gwpn_SPECT_I if_rule gwpn_ASSERT_I gwpn_MIf_I)
      subgoal
        unfolding Let_def   sift_down3_cost_def
        apply clarsimp
        apply(simp add: add.assoc lift_acost_zero lift_acost_diff_to_the_front lift_acost_diff_to_the_right lift_acost_diff_to_the_right_Some)
        apply(simp only: add.commute add.left_commute)
        apply(rule add_left_mono) 
        subgoal premises prems
          apply sc_solve_debug apply safe   by (all \<open>(auto simp: one_enat_def numeral_eq_enat sc_solve_debug_def;fail)?\<close>)
        done
      subgoal by simp
      subgoal
        unfolding Let_def   sift_down3_cost_def
        apply clarsimp
        apply(simp add: add.assoc the_acost_costs_distrib lift_acost_zero lift_acost_diff_to_the_front lift_acost_diff_to_the_right lift_acost_diff_to_the_right_Some)
        apply(simp only: add.commute add.left_commute)
        apply(rule add_left_mono) 
        subgoal premises prems
          apply sc_solve by auto
        done
      subgoal by simp
      subgoal
        unfolding Let_def   sift_down3_cost_def
        apply(simp add: add.assoc lift_acost_zero lift_acost_diff_to_the_front lift_acost_diff_to_the_right lift_acost_diff_to_the_right_Some)
        apply(simp only: add.commute add.left_commute)
        apply(rule add_left_mono) 
        apply sc_solve by auto
      subgoal by simp
      done 
    subgoal for xs' i' ctd (* first if branch *)
      apply(rule loop_body_conditionI) 
      subgoal (*  \<le> *)
        subgoal premises prems
        unfolding E_sd3_l_def Let_def
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc)
          apply sc_solve
          apply safe by (auto simp: one_enat_def numeral_eq_enat) 
        done
      subgoal (* diff pays *)
        apply simp apply safe
        unfolding E_sd3_l_def Let_def
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc)
          apply sc_solve_debug apply safe   by (all \<open>(auto simp: one_enat_def numeral_eq_enat sc_solve_debug_def;fail)?\<close>)
      subgoal 
        apply simp done
      done
    subgoal for xs' i' ctd (* second if branch *)
      apply(rule loop_body_conditionI) 
      subgoal (*  \<le> *)
        subgoal premises prems
        unfolding E_sd3_l_def Let_def
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc)
          apply sc_solve apply safe apply (auto simp: numeral_eq_enat one_enat_def) done  
        done
      subgoal (* diff pays *)
        apply simp apply safe
        subgoal premises prems
        unfolding E_sd3_l_def Let_def 
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc)
        apply sc_solve 
          apply safe by (auto simp: numeral_eq_enat one_enat_def) 
        done
      subgoal 
        apply simp done
      done
    subgoal for xs' i' ctd (* third if branch *)
      apply(rule loop_body_conditionI) 
      subgoal (*  \<le> *)
        unfolding E_sd3_l_def Let_def
        subgoal premises prems
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc)
         apply sc_solve apply safe apply (auto simp: numeral_eq_enat one_enat_def) done
        done
      subgoal (* diff pays *)
        apply simp apply safe
        unfolding E_sd3_l_def Let_def
        subgoal premises prems
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc)        
        apply sc_solve 
          apply safe using prems by (auto simp: one_enat_def) 
        done
      subgoal 
        by auto
      done
    subgoal for xs' i' ctd (* fourth if branch *)
      apply(rule loop_body_conditionI) 
      subgoal (*  \<le> *)
        unfolding E_sd3_l_def Let_def
        subgoal premises prems
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
          apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc) 
          apply sc_solve apply safe apply (auto simp: one_enat_def) done 
        done
      subgoal (* diff pays *)
        apply simp apply safe
        unfolding E_sd3_l_def Let_def
        subgoal premises prems
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc)
        apply sc_solve 
          apply safe by (auto simp: one_enat_def) 
        done
      subgoal 
        by auto
      done
    done
  subgoal apply auto done
  done

thm separate_correct_and_time
 

lemma sift_down_btu_correct':
  assumes "heapify_btu_invar xs\<^sub>0 l' xs" "l<l'"
  shows "sift_down3 (l'-Suc 0) xs \<le> SPEC (\<lambda>xs'. heapify_btu_invar xs\<^sub>0 (l'-Suc 0) xs') (%_. sift_down3_cost (h-(l' - Suc 0)))"
  apply(rule separate_correct_and_time)
  subgoal 
    apply(rule order.trans) 
     apply(rule sift_down3_refine_funct) apply (simp add: timerefine_id)
    apply(rule order.trans)
     apply(rule sift_down2_refine)  apply (simp add: timerefine_id)
    apply(rule order.trans)
     apply(rule sift_down1_refine_functional_aux)  apply (simp add: timerefine_id)
    apply(rule  sift_down_btu_correct) using assms by auto
  by (rule sift_down3_refine_time)
 

definition "sift_down3_t1 i\<^sub>0 xs = sup (sift_down3 i\<^sub>0 xs) (SPEC (\<lambda>_. True) (%_. cost ''sift_down'' 1))"


definition heapify_btu_step 
  where "heapify_btu_step l' xs\<^sub>0 xs  = do { ASSERT (heapify_btu_invar xs\<^sub>0 (Suc l') xs \<and> l<Suc l');
                                SPEC (\<lambda>xs'. heapify_btu_invar xs\<^sub>0 l' xs') (%_. cost ''sift_down'' 1) }"


definition sift_down_restore 
  where "sift_down_restore xs\<^sub>0 xs  = do { ASSERT (l<h \<and> sift_down_invar xs\<^sub>0 l xs);
                                SPEC (\<lambda>xs'. slice_eq_mset l h xs' xs\<^sub>0 \<and> is_heap xs') (%_. cost ''sift_down'' 1) }"



definition Rsd where "Rsd i = TId(''sift_down'':=sift_down3_cost i)"

lemma sift_down3_refines_heapify_btu_step:
    shows "sift_down3  l' xs \<le> \<Down>Id( timerefine (Rsd (h-l')) (heapify_btu_step l' xs\<^sub>0 xs))"
  unfolding heapify_btu_step_def
  apply(rule ASSERT_D3_leI)
  apply simp  
  apply(rule order.trans[OF sift_down_btu_correct'[of xs\<^sub>0 "Suc l'", simplified]])
    apply simp
   apply simp
  apply(rule SPEC_timerefine)
  subgoal by simp
  subgoal by(auto simp: Rsd_def  timerefineA_upd)
  done


thm sift_down_restore_correct


lemma sift_down_restore_correct':
  assumes "l < h" "sift_down_invar xs\<^sub>0 l xs"
  shows "sift_down3 l xs \<le> SPEC (\<lambda>xs'. slice_eq_mset l h xs' xs\<^sub>0 \<and> is_heap xs') (%_. sift_down3_cost (h-l))"
  apply(rule separate_correct_and_time)
  subgoal 
    apply(rule order.trans) 
     apply(rule sift_down3_refine_funct) apply (simp add: timerefine_id)
    apply(rule order.trans)
     apply(rule sift_down2_refine)  apply (simp add: timerefine_id)
    apply(rule order.trans)
     apply(rule sift_down1_refine_functional_aux)  apply (simp add: timerefine_id)
    apply(rule  sift_down_restore_correct) using assms by auto
  by (rule sift_down3_refine_time)

lemma sift_down3_refines_sift_down_restore:
  shows "sift_down3 l xs \<le>  \<Down>Id( timerefine (Rsd (h-l)) ( sift_down_restore xs\<^sub>0 xs))"
  unfolding sift_down_restore_def
  apply(rule ASSERT_D3_leI)
  apply simp  
  apply(rule order.trans[OF sift_down_restore_correct'[of xs\<^sub>0]])
    apply simp
   apply simp
  apply(rule SPEC_timerefine)
  subgoal by simp
  subgoal by(auto simp: Rsd_def  timerefineA_upd)
  done







end
                                            
concrete_definition sift_down4 is heap_context.sift_down3_def
concrete_definition sift_down_ab is heap_context.heapify_btu_step_def
concrete_definition sift_down_restore_a for less_eq l h xs\<^sub>0 xs is heap_context.sift_down_restore_def
                                                                              
context heap_context begin  

  (*
  lemma sift_down4_full_refine: "sift_down4 (\<^bold><) l h i xs \<le> sift_down i xs"
  proof -
    note sift_down4.refine[OF heap_context_axioms, symmetric, THEN meta_eq_to_obj_eq]
    also note sift_down3_refine 
    also note sift_down2_refine 
    also note sift_down1_refine 
    finally show ?thesis by simp
  qed *)

  lemmas bla = sift_down_ab.refine[OF heap_context_axioms, symmetric, unfolded heapify_btu_step_def]
  lemma sift_down4_refine: "sift_down4 (\<^bold><) l h l' xs \<le> \<Down>Id( timerefine (Rsd (h-l')) (sift_down_ab (\<^bold>\<le>) l h l' xs\<^sub>0 xs))"
  proof -
    note sift_down4.refine[OF heap_context_axioms, symmetric, THEN meta_eq_to_obj_eq]
    also note sift_down3_refines_heapify_btu_step
    finally show ?thesis unfolding sift_down_ab.refine[OF heap_context_axioms] .
  qed

  lemma sift_down4_refine_restore: "sift_down4 (\<^bold><) l h l xs \<le> \<Down>Id( timerefine (Rsd (h-l)) (sift_down_restore_a (\<^bold>\<le>) l h xs\<^sub>0 xs))"
  proof -
    note sift_down4.refine[OF heap_context_axioms, symmetric, THEN meta_eq_to_obj_eq]
    also note sift_down3_refines_sift_down_restore
    finally show ?thesis unfolding sift_down_restore_a.refine[OF heap_context_axioms] .
  qed


  lemma sift_down3_cost_mono:
    "x\<le>y \<Longrightarrow> sift_down3_cost x \<le> sift_down3_cost y"
    unfolding sift_down3_cost_def E_sd3_l_def Let_def
    apply(simp add: lift_acost_propagate lift_acost_cost)
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc)
    apply sc_solve by auto


  lemma sift_down4_refine_u: "(la,la')\<in>nat_rel \<Longrightarrow> (xs,xs')\<in> (\<langle>Id\<rangle>list_rel) \<Longrightarrow> sift_down4 (\<^bold><) l h la xs \<le> \<Down>(\<langle>Id\<rangle>list_rel) ( timerefine (Rsd (h-l)) (sift_down_ab (\<^bold>\<le>) l h la' xs\<^sub>0 xs'))"
    apply (simp del: conc_Id)
    apply(rule order.trans[OF sift_down4_refine, of _  xs\<^sub>0])
    unfolding sift_down_ab_def
    apply(rule ASSERT_D5_leI)
    apply simp
    apply(rule timerefine_R_mono_wfR'')
    subgoal by(auto simp: Rsd_def wfR''_TId intro: wfR''_upd)
    unfolding Rsd_def
    apply(simp add: le_fun_def) 
    apply(rule sift_down3_cost_mono)
    by auto

  definition "heapify_btu xs\<^sub>0 \<equiv> doN {
    ASSERT(h>0);
    h' \<leftarrow> SPECc2 ''sub'' (-) h 1;
    (xs,l') \<leftarrow> monadic_WHILEIT (\<lambda>(xs,l'). heapify_btu_invar xs\<^sub>0 l' xs \<and> l'\<ge>l)
      (\<lambda>(xs,l'). SPECc2 ''icmp_slt'' (<) l l') 
      (\<lambda>(xs,l'). doN {
        ASSERT (l'>0);
        l' \<leftarrow> SPECc2 ''sub'' (-) l' 1;
        xs \<leftarrow> sift_down_ab (\<^bold>\<le>) l h l' xs\<^sub>0 xs ;
        RETURN (xs,l')
      })
      (xs\<^sub>0,h');
    RETURN xs
  }"    

definition heapify_btu_cost :: "_ \<Rightarrow> ecost" 
  where "heapify_btu_cost xs\<^sub>0 = cost ''call'' (enat (h - Suc l) + 1) + cost ''icmp_slt'' (enat (h - Suc l) + 1)
       + cost ''if'' (enat (h - Suc l) + 1) + cost ''sub'' (enat (h - Suc l) +1) 
      + cost ''sift_down'' (enat (h - Suc l))"

\<comment> \<open>TODO: heapify_btu actually is O(n), not O(n * log n) ! but we don't need it for heapsort in O(n*log n)\<close> 

definition heapify_btu_lbc :: "_ \<Rightarrow> (char list, nat) acost" where
  "heapify_btu_lbc = (\<lambda>(xs,l'). (cost ''call'' (l'-l) + (cost ''icmp_slt'' (l'-l) + cost ''if'' (l'-l)) + cost ''sub'' (l'-l) + cost ''sift_down'' (l'-l)))"

  lemma heapify_btu_correct: "\<lbrakk> l<h; h\<le>length xs\<^sub>0 \<rbrakk> \<Longrightarrow> heapify_btu xs\<^sub>0 \<le> SPEC (\<lambda>xs. slice_eq_mset l h xs xs\<^sub>0 \<and> is_heap xs) (\<lambda>_. heapify_btu_cost xs\<^sub>0)"
    unfolding heapify_btu_def
    apply simp
    apply(subst monadic_WHILEIET_def[symmetric, where E=heapify_btu_lbc]) 
    unfolding SPEC_def SPECc2_def 
    unfolding bla SPEC_REST_emb'_conv
    apply(rule gwp_specifies_I)
    apply (refine_vcg \<open>-\<close> rules: gwp_monadic_WHILEIET)
    apply(rule gwp_monadic_WHILEIET)
    subgoal unfolding wfR2_def heapify_btu_lbc_def zero_acost_def cost_def by auto
    subgoal for s
      apply clarsimp
      apply (refine_vcg \<open>-\<close>)
      apply simp_all
      apply safe
      subgoal
        apply (refine_vcg \<open>-\<close>) (* loop body *)
        subgoal apply(rule loop_body_conditionI) 
          subgoal unfolding heapify_btu_lbc_def apply sc_solve by auto
          subgoal unfolding heapify_btu_lbc_def apply sc_solve_debug apply(all \<open>(auto simp: one_enat_def sc_solve_debug_def; fail)?\<close>) done 
          subgoal by auto 
          done
        subgoal by simp
        done
    subgoal (* exiting loop because of wrong guard *)
      apply(rule loop_exit_conditionI)
      apply (refine_vcg \<open>-\<close>)
      unfolding heapify_btu_invar_def
      unfolding heapify_btu_lbc_def heapify_btu_cost_def
      apply auto
      subgoal using btu_heapify_term by blast
      subgoal 
        apply(simp add: lift_acost_diff_to_the_front lift_acost_diff_to_the_right lift_acost_diff_to_the_right_Some)
       apply(sc_solve)
        by auto    
      done
    done      
    subgoal by (simp add: heapify_btu_invar_def btu_heapify_init) 
    done


  
  definition "heapify_btu2 xs\<^sub>0 \<equiv> doN {
    ASSERT(h>0);
    h' \<leftarrow> SPECc2 ''sub'' (-) h 1;
    (xs,l') \<leftarrow> monadic_WHILEIT (\<lambda>_. True) 
      (\<lambda>(xs,l'). SPECc2 ''icmp_slt'' (<) l l') 
      (\<lambda>(xs,l'). doN {
        ASSERT (l'>0);
        l'' \<leftarrow> SPECc2 ''sub'' (-) l' 1;
        xs \<leftarrow> sift_down4 (\<^bold><) l h l'' xs;
        RETURN (xs,l'')
      })
      (xs\<^sub>0,h');
    RETURN xs
  }"   

  lemma heapify_btu2_refine: "heapify_btu2 xs\<^sub>0 \<le> \<Down> (\<langle>Id\<rangle>list_rel) (timerefine (Rsd (h-l)) (heapify_btu xs\<^sub>0))"
    unfolding heapify_btu2_def heapify_btu_def
    supply monadic_WHILEIT_refine'[refine]
    supply bindT_refine_easy[refine]
    supply sift_down4_refine_u[refine]                           
    apply(refine_rcg SPECc2_refine)
    apply refine_dref_type   
    by  (auto simp: cost_n_leq_TId_n Rsd_def SPECc2_def inres_SPECT)
  
  lemma heapify_btu2_correct:
    "\<lbrakk>l < h; h \<le> length xs\<^sub>0\<rbrakk>
    \<Longrightarrow> heapify_btu2 xs\<^sub>0 \<le> \<Down> (\<langle>Id\<rangle>list_rel) (timerefine (Rsd (h-l)) (SPEC (\<lambda>xs. slice_eq_mset l h xs xs\<^sub>0 \<and> is_heap xs) (\<lambda>_. heapify_btu_cost xs\<^sub>0)))"
    apply(rule order.trans)
     apply(rule heapify_btu2_refine)
    apply simp
    apply(rule timerefine_mono2)
    by(auto simp: Rsd_def intro: heapify_btu_correct)
    
  
  thm heap_context.heapify_btu2_def
     
end

concrete_definition heapify_btu1 for less_eq  l h xs\<^sub>0 is heap_context.heapify_btu_def
concrete_definition heapify_btu2 for less l h xs\<^sub>0 is heap_context.heapify_btu2_def
concrete_definition Rsd_a for i is heap_context.Rsd_def


context heap_context begin  

    lemmas heapify_btu1_correct = heapify_btu_correct[unfolded heapify_btu1.refine[OF heap_context_axioms]]
end

context weak_ordering begin

  (* TODO: We keep \<le> out of the definition (although it occurs in invariants). 
    Otherwise, getting rid of the \<le> ghost parameter is difficult!
  *)


  (* abstraction level with currency sift_down *)
  definition heapsort :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "heapsort xs\<^sub>0 l h\<^sub>0 \<equiv> doN {
    ASSERT (l\<le>h\<^sub>0);
    hl \<leftarrow> SPECc2 ''sub'' (-) h\<^sub>0 l;
    b \<leftarrow> SPECc2 ''icmp_slt'' (<) 1 hl;
    MIf b (doN {
      xs \<leftarrow> heapify_btu1 (\<^bold>\<le>) l h\<^sub>0 xs\<^sub>0;
      
      (xs,h)\<leftarrow> monadic_WHILEIT (\<lambda>(xs,h). 
          l<h \<and> h\<le>h\<^sub>0 
        \<and> heap_context.is_heap (le_by_lt (\<^bold><)) l h xs
        \<and> slice_eq_mset l h\<^sub>0 xs xs\<^sub>0
        \<and> sorted_wrt_lt (\<^bold><) (slice h h\<^sub>0 xs)
        \<and> (\<forall>a\<in>set (slice l h xs). \<forall>b\<in>set (slice h h\<^sub>0 xs). (le_by_lt (\<^bold><)) a b)
      )
        (\<lambda>(xs,h). doN { l' \<leftarrow> SPECc2 ''add'' (+) l 1;
                        SPECc2 ''icmp_slt'' (<) l' h }) 
        (\<lambda>(xs,h). doN {
          ASSERT (h>0 \<and> l\<noteq>h-1);
          h' \<leftarrow> SPECc2 ''sub'' (-) h 1;
          xs \<leftarrow> mop_list_swapN xs l h';
          xs \<leftarrow> sift_down_restore_a (\<^bold>\<le>) l h' xs xs;
          RETURN (xs,h')
        })
        (xs,h\<^sub>0);
      
      RETURN xs
    } ) (
      RETURN xs\<^sub>0)
  }"
  
  
text \<open>heapsort loop body cost\<close> 
definition heapsort_lbc :: "nat \<Rightarrow> (char list, nat) acost" where
  "heapsort_lbc = (\<lambda>p.  
                 cost ''list_swap'' p + cost ''call'' p +  cost ''add'' p + cost ''icmp_slt'' p
               + cost ''if'' p + cost ''sub'' p + cost ''sift_down'' p )"

  definition heapsort_time :: "_ \<Rightarrow> _ \<Rightarrow> ecost" where
    "heapsort_time l h\<^sub>0 = lift_acost (heapsort_lbc (h\<^sub>0-l)) 
          + cost ''add'' 1 + cost ''call'' (enat (h\<^sub>0 - Suc l) + 2)
          + cost ''icmp_slt'' (enat (h\<^sub>0 - Suc l) + 1 + 1 + 1) + cost ''if'' (enat (h\<^sub>0 - Suc l) + 1 + 3)
          + cost ''sub'' (enat (h\<^sub>0 - Suc l) + 2) + cost ''sift_down'' (enat (h\<^sub>0 - Suc l))"

  
lemma heapsort_correct:
  fixes xs\<^sub>0 :: "'a list"
    assumes "l\<le>h\<^sub>0" "h\<^sub>0\<le>length xs\<^sub>0"
    shows "heapsort xs\<^sub>0 l h\<^sub>0 \<le> SPEC (\<lambda>xs. slice_eq_mset l h\<^sub>0 xs xs\<^sub>0 \<and> sorted_wrt_lt (\<^bold><) (slice l h\<^sub>0 xs)) (\<lambda>_. heapsort_time l h\<^sub>0)"
  proof -
    interpret initial: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l h\<^sub>0 by unfold_locales fact

    note F = initial.heapify_btu1_correct[unfolded SPEC_def, THEN gwp_specifies_rev_I, THEN gwp_conseq_0]
    note G = initial.bla 

    show ?thesis  
      using assms unfolding heapsort_def le_by_lt (* NOTE: not yet used here le_by_lt *)
      apply(subst monadic_WHILEIET_def[symmetric, where E="(\<lambda>(xs,h). heapsort_lbc (h-l) )::(('a list * nat) \<Rightarrow>  (char list, nat) acost)"]) 
      unfolding SPEC_def SPECc2_def mop_list_swap_def 
      apply(rule gwp_specifies_I)
      apply (refine_vcg \<open>-\<close> rules: gwp_monadic_WHILEIET F if_rule)

                apply (all \<open>(auto dest: slice_eq_mset_eq_length;fail)?\<close>)    
      subgoal unfolding wfR2_def apply (auto simp: handy_if_lemma zero_acost_def)
          unfolding heapsort_lbc_def Let_def cost_def zero_acost_def by auto
      apply (clarsimp_all simp add: handy_if_lemma)
      subgoal premises prems for xs\<^sub>1 M xs h y proof -
        (* TODO: This is the argument that swapping the max-element to the end will preserve the
            sortedness criteria. Though apparently simple, the reasoning seems to be much too complex here.
            Try to improve on that!
        *)
        interpret heap_context "(\<^bold>\<le>)" "(\<^bold><)" l h using prems by (unfold_locales) auto
        interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "h-Suc 0" using prems by (unfold_locales) auto
        
        from prems have 
          [simp]: "length xs = length xs\<^sub>0" 
          and [simp, arith]: "h\<^sub>0 \<le> length xs\<^sub>0"
        by (auto simp: slice_eq_mset_eq_length)
        
        {
          fix xs'
          assume A: "slice_eq_mset l (h - Suc 0) xs' (swap xs l (h - Suc 0))"  
          hence "slice_eq_mset l h\<^sub>0 xs' (swap xs l (h - Suc 0))"
            apply (rule slice_eq_mset_subslice)
            using prems by auto
          from this[symmetric] have "slice_eq_mset l h\<^sub>0 xs' xs"  
            apply -
            apply (drule slice_eq_mset_swap(2)[THEN iffD1, rotated -1])
            using prems by (auto dest: slice_eq_mset_sym)
          also note \<open>slice_eq_mset l h\<^sub>0 xs xs\<^sub>0\<close>   
          finally have G1: "slice_eq_mset l h\<^sub>0 xs' xs\<^sub>0" .
  
          note [simp] = slice_eq_mset_eq_length[OF G1]
          
          have [simp]: "slice (h - Suc 0) h\<^sub>0 xs' = (xs'!(h-Suc 0))#slice h h\<^sub>0 xs'"
            apply (rule slice_extend1_left)
            using prems by (auto)
          
            
          have "slice h h\<^sub>0 xs' = slice h h\<^sub>0 (swap xs l (h - Suc 0))"
            apply (rule slice_eq_mset_eq_outside(2)[OF A]) using prems by auto
          also have "\<dots> = slice h h\<^sub>0 xs" 
            by (metis Suc_lessD atLeastLessThan_iff leI le_antisym le_zero_eq nat_less_le nz_le_conv_less \<open>Suc l < h\<close> slice_swap_outside)
          finally have [simp]: "slice h h\<^sub>0 xs' = slice h h\<^sub>0 xs" .
            
          have [arith,simp]: "h - Suc 0 < length xs\<^sub>0" "l<length xs\<^sub>0" using prems by (auto)
          have [simp]: "xs' ! (h - Suc 0) = xs!l" 
            using slice_eq_mset_nth_outside[OF A, of "h-Suc 0"] 
            by auto
            
          have "xs!l \<in> set (slice l h xs)" using prems by (auto simp: set_slice_conv)
          then have G2: "sorted_wrt (\<^bold>\<le>) (slice (h - Suc 0) h\<^sub>0 xs')" 
            using prems 
            by (auto)
  
          have [simp]: "slice l (h - Suc 0) (swap xs l (h - Suc 0)) = xs!(h-Suc 0)#(slice (Suc l) (h-Suc 0) xs)"
            apply (rule nth_equalityI)
            apply (auto simp: nth_list_update slice_nth swap_nth Suc_diff_Suc \<open>Suc l < h\<close>)
            done
            
          have "in_heap (h - Suc 0)"
            unfolding in_heap_def apply simp
            using \<open>Suc l < h\<close> by linarith
          
          have G3: "\<forall>a \<in> set (slice l (h - Suc 0) xs'). \<forall>b \<in> set (slice (h - Suc 0) h\<^sub>0 xs'). a\<^bold>\<le>b" 
            thm slice_eq_mset_set_inside[OF A]
            apply (simp add: slice_eq_mset_set_inside[OF A])
            using \<open>\<forall>x\<in>set (slice l h xs). \<forall>_\<in>_. _\<close>
            apply (auto simp: set_slice_conv root_greatest[OF \<open>is_heap xs\<close> \<open>in_heap (h-Suc 0)\<close>])
            subgoal using N.ran_not_empty \<open>in_heap (h - Suc 0)\<close> in_heap_bounds(2) by blast  
            subgoal for j 
              apply (subgoal_tac "in_heap j")
              using root_greatest[OF \<open>is_heap xs\<close>, of j] apply blast
              unfolding in_heap_def by simp
            subgoal by (metis Suc_le_lessD diff_le_self less_imp_le less_le_trans)
            done
            
          note G1 G2 G3
        } note aux=this
        thm sift_down_invar_init[OF \<open>is_heap xs\<close> \<open>Suc l < h\<close>]

        have " l < h - Suc 0" using \<open>Suc l < h\<close>
          using N.ran_not_empty le_eq_less_or_eq prems(5) by blast

        show ?thesis
          unfolding sift_down_restore_a_def SPEC_REST_emb'_conv
          apply (refine_vcg \<open>-\<close> )
          subgoal for x
            apply(rule loop_body_conditionI)
            subgoal unfolding heapsort_lbc_def Let_def apply sc_solve by simp
            subgoal unfolding heapsort_lbc_def Let_def apply simp
              apply sc_solve by (auto simp: one_enat_def)
            subgoal  
              apply safe
              using \<open>Suc l < h\<close> \<open>h\<le>h\<^sub>0\<close>
              by (auto simp: aux)
            done
          subgoal using sift_down_invar_init[OF \<open>is_heap xs\<close> \<open>Suc l < h\<close>] \<open>l < h - Suc 0\<close> by simp
          done
          
      qed
      subgoal for xs\<^sub>1 M xs h y
        apply(rule loop_exit_conditionI)
        apply (refine_vcg \<open>-\<close> rules: if_rule2)
        subgoal 
          unfolding initial.heapify_btu_cost_def heapsort_time_def
          apply(simp add: lift_acost_zero lift_acost_diff_to_the_front lift_acost_diff_to_the_right lift_acost_diff_to_the_right_Some)

          apply(simp only: add.assoc)
          apply(rule add_left_mono)  
          apply sc_solve_debug apply safe by (all \<open>(auto simp: sc_solve_debug_def numeral_eq_enat one_enat_def;fail)?\<close>)
        subgoal 
          
      
      apply clarsimp
      subgoal premises prems
      proof -
        have [simp]: "h=l+1" using prems by auto
      
        from prems have [simp]: "length xs = length xs\<^sub>0"
          and [simp, arith]: "l<length xs\<^sub>0" "h<length xs\<^sub>0"
          by (auto dest: slice_eq_mset_eq_length)
        
        have "set (slice l (Suc l) xs) = {xs!l}" by simp
        
        show ?thesis using prems
          by (auto simp: slice_split_hd le_by_lt)
      qed
      done
    done
    prefer 3
  subgoal
    by (simp add: sorted_wrt01)
  subgoal by auto
  subgoal unfolding heapsort_time_def apply sc_solve by (auto simp: numeral_eq_enat one_enat_def)
  done
                                                                                      
qed



  definition heapsort2 :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "heapsort2 xs\<^sub>0 l h\<^sub>0 \<equiv> doN {
    ASSERT (l\<le>h\<^sub>0);
    hl \<leftarrow> SPECc2 ''sub'' (-) h\<^sub>0 l;
    b \<leftarrow> SPECc2 ''icmp_slt'' (<) 1 hl;
    MIf b (doN {
      xs \<leftarrow> heapify_btu2 (\<^bold><) l h\<^sub>0 xs\<^sub>0;
      
      (xs,h)\<leftarrow> monadic_WHILEIT (\<lambda>(xs,h).  True )
        (\<lambda>(xs,h). doN { l' \<leftarrow> SPECc2 ''add'' (+) l 1;
                        SPECc2 ''icmp_slt'' (<) l' h }) 
        (\<lambda>(xs,h). doN {
          ASSERT (h>0 \<and> l\<noteq>h-1);
          h' \<leftarrow> SPECc2 ''sub'' (-) h 1;
          xs \<leftarrow> mop_list_swapN xs l h';
          xs \<leftarrow> sift_down4 (\<^bold><) l h' l xs;
          RETURN (xs,h')
        })
        (xs,h\<^sub>0);
      
      RETURN xs
    } ) (
      RETURN xs\<^sub>0 )
  }"

  thm heap_context.sift_down4_refine_restore
  thm heap_context.heapify_btu2_refine


lemma heapsort2_refine:
  fixes xs\<^sub>0 :: "'a list"
  assumes "l\<le>h\<^sub>0" "h\<^sub>0\<le>length xs\<^sub>0"
  shows "heapsort2  xs\<^sub>0 l h\<^sub>0 \<le> \<Down>Id (timerefine (Rsd_a (h\<^sub>0-l)) (heapsort xs\<^sub>0 l h\<^sub>0))"
proof -
    interpret initial: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l h\<^sub>0 by unfold_locales fact

    

    show ?thesis
      unfolding heapsort_def heapsort2_def 
      supply bindT_refine_conc_time_my_inres[refine]
      apply(refine_rcg SPECc2_refine MIf_refine monadic_WHILEIT_refine' )
      apply refine_dref_type
      prefer 10
      subgoal
        apply(rule  initial.heapify_btu2_refine[unfolded heapify_btu1.refine[OF initial.heap_context_axioms]
                                                Rsd_a.refine[OF initial.heap_context_axioms]
                                                heapify_btu2.refine[OF initial.heap_context_axioms]
                    ])
        done
      apply(auto simp: Rsd_a_def wfR''_TId sp_TId simp del: conc_Id 
                intro!: wfR''_upd cost_n_leq_TId_n struct_preserving_upd_I )
      subgoal 
        apply(refine_rcg)
        by (auto simp: timerefineA_upd)
      unfolding SPECc2_def apply (simp del: conc_Id)
      subgoal premises prems for d _ _ _ xs\<^sub>1 h h' proof -
        interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "h-Suc 0" using prems by (unfold_locales) auto

        from prems have *: "h' \<le> h\<^sub>0" by simp

        show ?thesis
          unfolding Rsd_a_def[symmetric]
          using N.sift_down4_refine_restore[of "swap xs\<^sub>1 l h'" "swap xs\<^sub>1 l h'"]
          unfolding Rsd_a.refine[OF N.heap_context_axioms]
          unfolding Rsd_a_def  N.sift_down3_cost_def initial.sift_down3_cost_def
          unfolding prems(8)
          apply(rule order.trans)
          apply simp
          apply(rule timerefine_R_mono_wfR'')
          subgoal by(auto simp: wfR''_TId intro: wfR''_upd)
          subgoal apply(auto simp: le_fun_def)
            unfolding N.E_sd3_l_def Let_def prems(1)[symmetric]
            apply simp
            apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
            apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc)
            apply sc_solve_debug apply safe using \<open>h' \<le> h\<^sub>0\<close>  by (all \<open>(auto simp: sc_solve_debug_def numeral_eq_enat one_enat_def;fail)?\<close>)
          done
      qed
      done        
qed

definition heapsort_TR
  where "heapsort_TR l h = pp (Rsd_a (h-l)) (TId(''slice_sort'':=heapsort_time l h))"

lemma heapsort_correct': 
  "\<lbrakk>(xs,xs')\<in>Id; (l,l')\<in>Id; (h,h')\<in>Id\<rbrakk> \<Longrightarrow> heapsort2 xs l h \<le>
      \<Down>Id (timerefine (heapsort_TR l h) (slice_sort_spec (\<^bold><) xs' l' h'))"
    unfolding slice_sort_spec_alt              
    apply (rule refine0)
    apply(rule order.trans)
     apply(rule heapsort2_refine) apply simp apply simp
    apply simp
    unfolding heapsort_TR_def
    apply(subst timerefine_iter2[symmetric])
    subgoal by(auto simp: Rsd_a_def wfR''_TId intro: wfR''_upd) 
    subgoal by(auto simp: wfR''_TId intro: wfR''_upd) 
    apply(rule timerefine_mono2) 
    subgoal by(auto simp: Rsd_a_def wfR''_TId intro: wfR''_upd) 
    subgoal 
      apply(rule order.trans[OF heapsort_correct])
      apply simp apply simp
      apply(rule SPEC_timerefine)
      subgoal by (auto simp: slice_eq_mset_alt)
      subgoal by(simp add: timerefineA_update_apply_same_cost)
      done
    done
  
end

concrete_definition heapsort1 for less xs\<^sub>0 l h\<^sub>0 is weak_ordering.heapsort_def


context weak_ordering begin  
  lemmas heapsort1_correct = heapsort_correct'[unfolded heapsort1.refine[OF weak_ordering_axioms]]
end

context heap_context begin

end


sepref_register mop_lchild3 mop_rchild3 mop_has_rchild3 mop_has_lchild3 mop_geth3  mop_seth3  
sepref_def mop_lchild_impl [llvm_inline] is "uncurry mop_lchild3" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding mop_lchild3_def apply (annot_snat_const "TYPE (size_t)")
  by sepref

sepref_def mop_rchild_impl [llvm_inline] is "uncurry mop_rchild3" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding mop_rchild3_def apply (annot_snat_const "TYPE (size_t)")
  by sepref

sepref_def has_lchild_impl [llvm_inline] is "uncurry2 mop_has_lchild3" :: "[\<lambda>((l,h),i). l\<le>h]\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding mop_has_lchild3_def apply (annot_snat_const "TYPE (size_t)") by sepref

sepref_def has_rchild_impl [llvm_inline] is "uncurry2 mop_has_rchild3" :: "[\<lambda>((l,h),i). l<h]\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding mop_has_rchild3_def apply (annot_snat_const "TYPE (size_t)") by sepref 

sepref_def mop_geth_impl [llvm_inline] is "uncurry3 mop_geth3" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (eoarray_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a elem_assn \<times>\<^sub>a eoarray_assn elem_assn"
  unfolding mop_geth3_def  
  unfolding mop_oarray_extract_def[symmetric] thm mop_oarray_extract_def[symmetric]
  apply sepref_dbg_preproc
     apply sepref_dbg_cons_init
    apply sepref_dbg_id  
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
        apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
   apply sepref_dbg_constraints 
   sorry (* TODO: ask Peter *)
  
  
sepref_def mop_seth_impl [llvm_inline] is "uncurry4 mop_seth3" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (eoarray_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a elem_assn\<^sup>d \<rightarrow>\<^sub>a eoarray_assn elem_assn"
  unfolding mop_seth3_def  
  unfolding mop_oarray_upd_def[symmetric] thm mop_oarray_extract_def[symmetric]
  apply sepref_dbg_preproc
     apply sepref_dbg_cons_init
    apply sepref_dbg_id  
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
        apply sepref_dbg_trans
  apply sepref_dbg_opt
    apply sepref_dbg_cons_solve
   apply sepref_dbg_constraints 
  sorry (* TODO: ask Peter *)
   

sepref_register mop_to_eo_conv


context sort_impl_context begin





term "sift_down4 (\<^bold><)"

  definition sift_down5 :: " _ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list, _) nrest" where "sift_down5 l h i\<^sub>0 xs \<equiv> doN {
    ASSERT (l\<le>i\<^sub>0 \<and> i\<^sub>0<h);
    i\<^sub>1 \<leftarrow> SPECc2 ''sub'' (-) i\<^sub>0 l;
    xs \<leftarrow> mop_to_eo_conv xs;
    (v,xs) \<leftarrow> mop_geth3 l h xs i\<^sub>1;
    
    (xs,i,_) \<leftarrow> monadic_WHILEIT (\<lambda>(xs,i,ctd). i<h-l \<and> i\<ge>i\<^sub>1)
       (\<lambda>(xs,i,ctd). do { hrc \<leftarrow> mop_has_rchild3 l h i;
                          SPECc2 ''and'' (\<and>) hrc ctd }) (\<lambda>(xs,i,ctd). doN {
      lci \<leftarrow> mop_lchild3 h i;
      rci \<leftarrow> mop_rchild3 h i;

      ASSERT (l+lci<h \<and> l+rci<h \<and> l+lci \<noteq> l+rci);
      lplci \<leftarrow> SPECc2 ''add'' (+) l lci;
      lprci \<leftarrow> SPECc2 ''add'' (+) l rci;
      ASSERT (lplci \<noteq> lprci);
      b \<leftarrow> cmpo_idxs2' xs lplci lprci;
      
      MIf b (doN {
        b \<leftarrow> cmpo_v_idx2' xs v lprci;
        MIf b ( doN {
          (rc,xs) \<leftarrow> mop_geth3 l h xs rci;
          xs \<leftarrow> mop_seth3 l h xs i rc;
          RETURN (xs,rci,True)
        } ) (  RETURN (xs,i,False) )
      } ) ( doN {
        b \<leftarrow> cmpo_v_idx2' xs v lplci;
        MIf b ( doN {
          (lc,xs) \<leftarrow> mop_geth3 l h xs lci;
          xs \<leftarrow> mop_seth3 l h xs i lc;
          RETURN (xs,lci,True)
        } ) ( RETURN (xs,i,False) )
      } )
    }) (xs,i\<^sub>1,True);
    
    ASSERT (i\<ge>i\<^sub>1);
    
    hlc \<leftarrow> mop_has_lchild3 l h i;
    MIf hlc ( doN {
      lci \<leftarrow> mop_lchild3 h i;
      ASSERT (l+lci<h);
      lplci \<leftarrow> SPECc2 ''add'' (+) l lci;
      b \<leftarrow> cmpo_v_idx2' xs v lplci;
      MIf b ( doN {
        (lc,xs) \<leftarrow> mop_geth3 l h xs lci;
        xs \<leftarrow> mop_seth3 l h xs i lc;
        xs \<leftarrow> mop_seth3 l h xs lci v;
        xs \<leftarrow> mop_to_wo_conv xs;
        RETURN xs
      } )( doN {
        xs \<leftarrow> mop_seth3 l h xs i v;
        xs \<leftarrow> mop_to_wo_conv xs;
        RETURN xs
      }  )
    } )( doN {
      xs \<leftarrow> mop_seth3 l h xs i v;
      xs \<leftarrow> mop_to_wo_conv xs;
      RETURN xs
    }  )
  }" 

(* Move *)
lemma timerefineA_0[simp]: "timerefineA r 0 = 0"
  by(auto simp: timerefineA_def zero_acost_def)
 
lemma mop_to_eo_conv_refine: "wfR'' R \<Longrightarrow> (xs,xs')\<in>Id \<Longrightarrow> mop_to_eo_conv xs \<le> \<Down> Id (timerefine R (mop_to_eo_conv xs'))"
  unfolding mop_to_eo_conv_def
  apply(intro refine0)
  by (auto simp: lift_acost_zero  simp del: conc_Id )


definition "preserves_curr R n \<longleftrightarrow> (R n = (cost n 1))"

lemma preserves_curr_D: "preserves_curr R n \<Longrightarrow> R n = (cost n 1)"
  unfolding preserves_curr_def by metis
  
lemma timerefineA_cost_apply: "timerefineA TR (cost n (t::enat)) = acostC (\<lambda>x. t * the_acost (TR n) x)"
  unfolding timerefineA_def cost_def zero_acost_def
  apply simp
  apply(subst timerefineA_upd_aux)
  apply(subst Sum_any.delta) by simp 

lemma pr: "enat (Suc 0) = 1" by (simp add: one_enat_def)

lemma mop_geth3_refine:
  assumes 
     "preserves_curr TR ''add''"
   and "preserves_curr TR ''load''"
   and "preserves_curr TR ''ofs_ptr''"
  shows "wfR'' TR \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id  \<Longrightarrow> (h,h')\<in>Id  \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> mop_geth3 h l a b \<le> \<Down> Id (timerefine TR (mop_geth3 h' l' a' b'))"
  unfolding mop_geth3_def mop_eo_extract_def
  apply(intro refine0 bindT_refine_easy SPECc2_refine)
  apply refine_dref_type
  using assms    
  apply -
        apply (auto  simp: pr timerefineA_cost timerefineA_cost_apply lift_acost_propagate lift_acost_cost timerefineA_propagate)
  by(auto simp: preserves_curr_def ) 

lemma  mop_seth3_refine:
  fixes TR :: "_ \<Rightarrow> (_, enat) acost"
  assumes 
     "preserves_curr TR ''add''"
   and "preserves_curr TR ''store''"
   and "preserves_curr TR ''ofs_ptr''"
  shows "(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (c,c')\<in>Id \<Longrightarrow> (h,h')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> wfR'' TR \<Longrightarrow> mop_seth3 h l a b c \<le> \<Down> Id (timerefine TR (mop_seth3 h' l' a' b' c'))"
    
  unfolding mop_seth3_def mop_eo_set_def
  apply(intro refine0 bindT_refine_easy SPECc2_refine)
  apply refine_dref_type
  using assms    
  apply -
        apply (auto  simp: pr timerefineA_cost timerefineA_cost_apply lift_acost_propagate lift_acost_cost timerefineA_propagate)
  by(auto simp: preserves_curr_def ) 

lemma preserves_curr_other_updI:
  "preserves_curr R m \<Longrightarrow> n\<noteq>m \<Longrightarrow> preserves_curr (R(n:=t)) m"
  by(auto simp: preserves_curr_def)

definition aa :: ecost where "aa = lift_acost mop_array_nth_cost + (lift_acost mop_array_nth_cost + (cost lt_curr_name 1 + (lift_acost mop_array_upd_cost + lift_acost mop_array_upd_cost)))"
definition bb :: ecost where "bb = lift_acost mop_array_nth_cost + (cost lt_curr_name 1 + lift_acost mop_array_upd_cost)"
definition cc :: ecost where "cc = lift_acost mop_array_nth_cost + lift_acost mop_array_nth_cost + lift_acost mop_array_upd_cost + lift_acost mop_array_upd_cost "
abbreviation "E \<equiv> TId(''cmpo_idxs'':=aa,''cmpo_v_idxs'':=bb, ''list_swap'':= cc)"
lemma wfR''E[simp]: " wfR'' E" by (auto intro!: wfR''_upd)

lemma preserves_curr_TId[simp]: "preserves_curr TId n"
  by(auto simp: preserves_curr_def TId_def cost_def zero_acost_def)

lemma SPECc2_refine':
  fixes TR :: "'h \<Rightarrow> ('h, enat) acost"
  shows "(op x y, op' x' y')\<in>R \<Longrightarrow> preserves_curr TR n  \<Longrightarrow> SPECc2 n op x y \<le> \<Down> R (timerefine TR (SPECc2 n op' x' y'))"
  unfolding SPECc2_def    
  apply(subst SPECT_refine_t) by (auto simp: preserves_curr_def timerefineA_cost_apply) 
  
lemma sp_E[simp]: "struct_preserving E"
  by (auto intro!: struct_preserving_upd_I)

lemma mop_has_rchild3_refine:
  fixes TR :: "_ \<Rightarrow> ecost"
  assumes "preserves_curr TR ''sub''"
  assumes "preserves_curr TR ''udiv''"
  assumes "preserves_curr TR ''icmp_slt''"
  shows "wfR'' TR \<Longrightarrow> (a,a')\<in>Id   \<Longrightarrow> (h,h')\<in>Id  \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> mop_has_rchild3 h l a \<le> \<Down> bool_rel (timerefine TR (mop_has_rchild3 h' l' a'))"
  unfolding mop_has_rchild3_def SPECc2_alt
  apply(intro refine0 bindT_refine_easy SPECc2_refine')
  apply refine_dref_type
  using assms    
  apply -
        apply (auto  simp: pr timerefineA_cost timerefineA_cost_apply lift_acost_propagate lift_acost_cost timerefineA_propagate)
  by(auto simp: preserves_curr_def ) 

lemma mop_lchild3_refine:
  fixes TR :: "_ \<Rightarrow> ecost"
  assumes "preserves_curr TR ''mul''"
  assumes "preserves_curr TR ''add''"
  shows "wfR'' TR \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> mop_lchild3 l a \<le> \<Down> Id (timerefine TR (mop_lchild3 l' a'))"
  unfolding mop_lchild3_def SPECc2_alt
  apply(intro refine0 bindT_refine_easy SPECc2_refine')
  apply refine_dref_type
  using assms    
  apply -
        apply (auto  simp: pr timerefineA_cost timerefineA_cost_apply lift_acost_propagate lift_acost_cost timerefineA_propagate)
  by(auto simp: preserves_curr_def ) 
lemma mop_rchild3_refine:
  fixes TR :: "_ \<Rightarrow> ecost"
  assumes "preserves_curr TR ''mul''"
  assumes "preserves_curr TR ''add''"
  shows "wfR'' TR \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> mop_rchild3 l a \<le> \<Down> Id (timerefine TR (mop_rchild3 l' a'))"
  unfolding mop_rchild3_def SPECc2_alt
  apply(intro refine0 bindT_refine_easy SPECc2_refine')
  apply refine_dref_type
  using assms    
  apply -
        apply (auto  simp: pr timerefineA_cost timerefineA_cost_apply lift_acost_propagate lift_acost_cost timerefineA_propagate)
  by(auto simp: preserves_curr_def ) 

lemma mop_has_lchild3_refine:
  fixes TR :: "_ \<Rightarrow> ecost"
  assumes "preserves_curr TR ''sub''"
  assumes "preserves_curr TR ''udiv''"
  assumes "preserves_curr TR ''icmp_slt''"
  assumes "(h,h')\<in>Id" "(l,l')\<in>Id"
  shows "wfR'' TR \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> mop_has_lchild3 h l a \<le> \<Down> bool_rel (timerefine TR (mop_has_lchild3 h' l' a'))"
  unfolding mop_has_lchild3_def SPECc2_alt
  apply(intro refine0 bindT_refine_easy SPECc2_refine')
  apply refine_dref_type
  using assms    
  apply -
        apply (auto  simp: pr timerefineA_cost timerefineA_cost_apply lift_acost_propagate lift_acost_cost timerefineA_propagate)
  by(auto simp: preserves_curr_def ) 



lemma cmpo_idxs2'_refines_mop_cmpo_idxs_with_E:
  "b'\<noteq>c' \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (c,c')\<in>Id \<Longrightarrow>
    cmpo_idxs2' a b c \<le> \<Down> bool_rel (timerefine E (mop_cmpo_idxs (cost ''cmpo_idxs'' 1) a' b' c'))"
  supply conc_Id[simp del]
    unfolding cmpo_idxs2'_def mop_cmpo_idxs_def
    unfolding mop_oarray_extract_def mop_eo_extract_def unborrow_def SPECc2_alt
          mop_oarray_upd_def mop_eo_set_def consume_alt
    apply normalize_blocks apply(split prod.splits)+
    apply normalize_blocks
    apply simp
    apply(intro refine0 consumea_refine bindT_refine_easy)
            apply refine_dref_type
    subgoal by auto  
    subgoal by auto  
    subgoal by auto  
    subgoal by auto   
    subgoal by (metis list_update_id list_update_overwrite list_update_swap option.sel)
    subgoal by simp
    subgoal by simp
    subgoal by(simp add: timerefineA_update_apply_same_cost  aa_def)
    subgoal by simp
    done

lemma  cmpo_v_idx2'_refines_mop_cmpo_v_idx_with_E:
  "(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (c,c')\<in>Id \<Longrightarrow> cmpo_v_idx2' a b c \<le> \<Down> bool_rel (timerefine E (mop_cmpo_v_idx (cost ''cmpo_v_idxs'' 1) a' b' c'))"
  supply conc_Id[simp del]
    unfolding cmpo_v_idx2'_def mop_cmpo_v_idx_def
    unfolding mop_oarray_extract_def mop_eo_extract_def unborrow_def SPECc2_alt
          mop_oarray_upd_def mop_eo_set_def consume_alt
    apply normalize_blocks apply(split prod.splits)+
    apply normalize_blocks
    apply simp
    apply(intro refine0 consumea_refine bindT_refine_easy)
            apply refine_dref_type
    subgoal by auto  
    subgoal by auto  
    subgoal by auto  
    subgoal by auto   
    subgoal by(simp add: timerefineA_update_apply_same_cost  bb_def)
    subgoal by simp
    done

lemma mop_to_wo_conv_refines: "wfR'' R \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> mop_to_wo_conv a \<le> \<Down> Id (timerefine R (mop_to_wo_conv a'))"
  unfolding mop_to_wo_conv_def 
  apply(intro refine0 bindT_refine_easy SPECc2_refine')
  apply refine_dref_type 
  by (auto  simp: lift_acost_zero) 

lemma elegant: 
  assumes "(l,l')\<in>Id" "(h,h')\<in>Id" "(i\<^sub>0,i\<^sub>0')\<in>Id" "(xs,xs')\<in>Id"
  shows " sift_down5 l h i\<^sub>0 xs \<le> \<Down>Id (timerefine E (sift_down4 (\<^bold><) l' h' i\<^sub>0' xs'))"
  using assms
  supply conc_Id[simp del] mop_cmpo_v_idx_def[simp del]
  unfolding sift_down5_def sift_down4_def
  supply mop_to_eo_conv_refine[refine]
  supply mop_geth3_refine[refine]
  supply mop_seth3_refine[refine]
  supply mop_has_rchild3_refine[refine]
  supply mop_has_lchild3_refine[refine]
  supply mop_lchild3_refine[refine]
  supply mop_rchild3_refine[refine]
  supply mop_to_wo_conv_refines[refine]
  supply cmpo_idxs2'_refines_mop_cmpo_idxs_with_E[refine]
  supply cmpo_v_idx2'_refines_mop_cmpo_v_idx_with_E[refine]
  apply(refine_rcg MIf_refine SPECc2_refine' bindT_refine_conc_time_my_inres monadic_WHILEIT_refine' )
                      apply refine_dref_type
     apply(all \<open>(intro sp_E preserves_curr_other_updI wfR''_upd wfR''_TId preserves_curr_TId)?\<close>)
  
  apply (auto)
  done



  definition "heapify_btu3 l h xs\<^sub>0 \<equiv> doN {
    ASSERT(h>0);
    h' \<leftarrow> SPECc2 ''sub'' (-) h 1;
    (xs,l') \<leftarrow> monadic_WHILEIT (\<lambda>_. True) 
      (\<lambda>(xs,l'). SPECc2 ''icmp_slt'' (<) l l') 
      (\<lambda>(xs,l'). doN {
        ASSERT (l'>0);
        l'' \<leftarrow> SPECc2 ''sub'' (-) l' 1;
        xs \<leftarrow> sift_down5 l h l'' xs;
        RETURN (xs,l'')
      })
      (xs\<^sub>0,h');
    RETURN xs
  }"   


lemma heapify_btu3_refine: "heapify_btu3 l h xs\<^sub>0 \<le> \<Down> Id (timerefine E (heapify_btu2 (\<^bold><) l h xs\<^sub>0))"
  supply conc_Id[simp del] 
  unfolding heapify_btu3_def heapify_btu2_def
  supply SPECc2_refine'[refine]
  supply elegant[refine]
  apply(refine_rcg bindT_refine_easy monadic_WHILEIT_refine')
  apply refine_dref_type 
  apply(all \<open>(intro sp_E preserves_curr_other_updI wfR''_upd wfR''_TId preserves_curr_TId)?\<close>)
  by auto


definition myswap where "myswap xs l h =
  doN { 
      xs \<leftarrow> mop_to_eo_conv xs;
      (x,xs) \<leftarrow> mop_oarray_extract xs l;
      (y,xs) \<leftarrow> mop_oarray_extract xs h;
      xs \<leftarrow> mop_oarray_upd xs l y;
      xs \<leftarrow> mop_oarray_upd xs h x;
      xs \<leftarrow> mop_to_wo_conv xs;
      RETURN xs
  }"

lemma myswap_refine: "l\<noteq>h \<Longrightarrow> (xs,xs')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> (h,h')\<in>Id
       \<Longrightarrow> myswap xs l h \<le> \<Down> (\<langle>Id\<rangle>list_rel) (timerefine E (mop_list_swapN xs' l' h'))"
  unfolding myswap_def mop_list_swap_def
  unfolding mop_to_eo_conv_def mop_to_wo_conv_def
  unfolding mop_oarray_extract_def mop_oarray_upd_def
  unfolding mop_eo_extract_def mop_eo_set_def
  apply normalize_blocks
  apply(split prod.splits)+
  apply normalize_blocks
  apply safe
  apply(intro refine0 bindT_refine_conc_time_my_inres consumea_refine)
  apply refine_dref_type 
  subgoal apply auto done
  subgoal apply auto done
  subgoal apply auto done
  subgoal apply auto done
  subgoal apply auto
    by (metis None_notin_image_Some list.set_map list_update_overwrite list_update_swap map_update)  
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: add.assoc timerefineA_update_apply_same_cost cc_def lift_acost_zero)  
  subgoal by (auto simp add: More_List.swap_def list_update_swap map_update option.exhaust_sel)  
  done

  definition heapsort3 :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "heapsort3 xs\<^sub>0 l h\<^sub>0 \<equiv> doN {
    ASSERT (l\<le>h\<^sub>0);
    hl \<leftarrow> SPECc2 ''sub'' (-) h\<^sub>0 l;
    b \<leftarrow> SPECc2 ''icmp_slt'' (<) 1 hl;
    MIf b (doN {
      xs \<leftarrow> heapify_btu3 l h\<^sub>0 xs\<^sub>0;
      
      (xs,h)\<leftarrow> monadic_WHILEIT (\<lambda>(xs,h).  True )
        (\<lambda>(xs,h). doN { l' \<leftarrow> SPECc2 ''add'' (+) l 1;
                        SPECc2 ''icmp_slt'' (<) l' h }) 
        (\<lambda>(xs,h). doN {
          ASSERT (h>0 \<and> l\<noteq>h-1);
          h' \<leftarrow> SPECc2 ''sub'' (-) h 1;
          xs \<leftarrow> myswap xs l h';
          xs \<leftarrow> sift_down5 l h' l xs;
          RETURN (xs,h')
        })
        (xs,h\<^sub>0);
      
      RETURN xs
    } ) (
      RETURN xs\<^sub>0 )
  }"

lemma heapsort3_refine:
  fixes xs\<^sub>0 :: "'a list" 
  shows "heapsort3  xs\<^sub>0 l h\<^sub>0 \<le> \<Down>Id (timerefine E (heapsort2 xs\<^sub>0 l h\<^sub>0))" 
  unfolding heapsort3_def heapsort2_def
  supply conc_Id[simp del] 
  supply SPECc2_refine'[refine]
  supply heapify_btu3_refine[refine]
  supply elegant[refine]
  supply myswap_refine[refine]
  apply(refine_rcg bindT_refine_conc_time_my_inres MIf_refine monadic_WHILEIT_refine')
  apply refine_dref_type 
  apply(all \<open>(intro sp_E preserves_curr_other_updI wfR''_upd wfR''_TId preserves_curr_TId)?\<close>)
  by (auto simp: SPECc2_def)


sepref_register "sift_down5"
sepref_def sift_down_impl is "uncurry3 (PR_CONST sift_down5)" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (array_assn elem_assn)\<^sup>d \<rightarrow>\<^sub>a (array_assn elem_assn)"
  unfolding sift_down5_def PR_CONST_def
  supply [[goals_limit = 1]]
  apply sepref_dbg_preproc
     apply sepref_dbg_cons_init
    apply sepref_dbg_id  
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
      apply sepref_dbg_trans (* Takes loooong! *)

  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints 
  done


  

sepref_register "heapify_btu3"
sepref_def heapify_btu_impl is "uncurry2 (PR_CONST (heapify_btu3))" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (array_assn elem_assn)\<^sup>d \<rightarrow>\<^sub>a (array_assn elem_assn)"
  unfolding heapify_btu3_def PR_CONST_def
  apply (annot_snat_const "TYPE (size_t)")
  supply [[goals_limit = 1]]
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
  
sepref_register "heapsort3"
sepref_def heapsort_impl is "uncurry2 (PR_CONST (heapsort3))" :: "(array_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a (array_assn elem_assn)"
  unfolding heapsort3_def unfolding myswap_def PR_CONST_def
  apply (rewrite at "sift_down5 _ _ \<hole> _" fold_COPY)
  apply (annot_snat_const "TYPE (size_t)")
  by sepref

lemmas heapsort_hnr[sepref_fr_rules] = heapsort_impl.refine[unfolded heapsort1.refine[OF weak_ordering_axioms,symmetric]]  
  

thm heapsort_correct' heapsort3_refine  heapsort_hnr

end  
(*            
subsection \<open>Parameterized Comparison\<close>
context parameterized_weak_ordering begin


  definition sift_down_param :: "'cparam \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list nres" 
  where "sift_down_param cparam l h i\<^sub>0 xs \<equiv> doN {
    ASSERT (l\<le>i\<^sub>0 \<and> i\<^sub>0<h);
    let i\<^sub>1 = i\<^sub>0 - l;
    xs \<leftarrow> mop_to_eo_conv xs;
    (v,xs) \<leftarrow> mop_geth3 l h xs i\<^sub>1;
    
    (xs,i,_) \<leftarrow> WHILEIT (\<lambda>(xs,i,ctd). i<h-l \<and> i\<ge>i\<^sub>1) (\<lambda>(xs,i,ctd). has_rchild3 l h i \<and> ctd) (\<lambda>(xs,i,ctd). doN {
      lci \<leftarrow> mop_lchild3 h i;
      rci \<leftarrow> mop_rchild3 h i;
    
      ASSERT (l+lci<h \<and> l+rci<h \<and> l+lci \<noteq> l+rci);
      b \<leftarrow> pcmpo_idxs2 cparam xs (l+lci) (l+rci);
      
      if b then doN {
        b \<leftarrow> pcmpo_v_idx2 cparam xs v (l+rci);
        if b then doN {
          (rc,xs) \<leftarrow> mop_geth3 l h xs rci;
          xs \<leftarrow> mop_seth3 l h xs i rc;
          RETURN (xs,rci,True)
        } else RETURN (xs,i,False)
      } else doN {
        b \<leftarrow> pcmpo_v_idx2 cparam xs v (l+lci);
        if b then doN {
          (lc,xs) \<leftarrow> mop_geth3 l h xs lci;
          xs \<leftarrow> mop_seth3 l h xs i lc;
          RETURN (xs,lci,True)
        } else RETURN (xs,i,False)
      }
    }) (xs,i\<^sub>1,True);
    
    ASSERT (i\<ge>i\<^sub>1);
    
    if has_lchild3 l h i then doN {
      lci \<leftarrow> mop_lchild3 h i;
      ASSERT (l+lci<h);
      b \<leftarrow> pcmpo_v_idx2 cparam xs v (l+lci);
      if b then doN {
        (lc,xs) \<leftarrow> mop_geth3 l h xs lci;
        xs \<leftarrow> mop_seth3 l h xs i lc;
        xs \<leftarrow> mop_seth3 l h xs lci v;
        xs \<leftarrow> mop_to_wo_conv xs;
        RETURN xs
      } else doN {
        xs \<leftarrow> mop_seth3 l h xs i v;
        xs \<leftarrow> mop_to_wo_conv xs;
        RETURN xs
      }  
    } else doN {
      xs \<leftarrow> mop_seth3 l h xs i v;
      xs \<leftarrow> mop_to_wo_conv xs;
      RETURN xs
    }  
  }" 

  
  lemma mop_geth3_cdom_refine: "\<lbrakk>
    (l',l)\<in>Id; (h',h)\<in>Id; (i',i)\<in>Id; (xs',xs)\<in>cdom_olist_rel cparam
  \<rbrakk> \<Longrightarrow> mop_geth3 l' h' xs' i' 
    \<le> \<Down>(br id (\<lambda>x. x \<in> cdom cparam) \<times>\<^sub>r cdom_olist_rel cparam) (mop_geth3 l h xs i)"
    unfolding mop_geth3_def
    apply refine_rcg
    by auto

  lemma mop_seth3_cdom_refine: "\<lbrakk>
    (l',l)\<in>Id; (h',h)\<in>Id; (i',i)\<in>Id; (xs',xs)\<in>cdom_olist_rel cparam; (v',v)\<in>Id; v\<in>cdom cparam
  \<rbrakk> \<Longrightarrow> mop_seth3 l' h' xs' i' v' 
    \<le> \<Down>(cdom_olist_rel cparam) (mop_seth3 l h xs i v)"
    unfolding mop_seth3_def
    apply refine_rcg
    by auto
    
      
  lemma sift_down_param_refine[refine]: "\<lbrakk> (l',l)\<in>Id; (h',h)\<in>Id; (i\<^sub>0',i\<^sub>0)\<in>Id; (xs',xs)\<in>cdom_list_rel cparam \<rbrakk> 
    \<Longrightarrow> sift_down_param cparam l' h' i\<^sub>0' xs' \<le> \<Down>(cdom_list_rel cparam) (sift_down4 (less' cparam) l h i\<^sub>0 xs)"
    unfolding sift_down_param_def sift_down4_def
    apply (refine_rcg mop_geth3_cdom_refine mop_seth3_cdom_refine)
    apply (all \<open>(intro IdI)?;(elim conjE IdE Pair_inject)?;(assumption)?\<close>)
    supply [refine_dref_RELATES] = RELATESI[of "cdom_list_rel cparam"] RELATESI[of "cdom_olist_rel cparam"]
    apply refine_dref_type
    (* Note: The 3 simps below are an optimization for speed. Just a simp_all on the 65 subgoals takes too long.*)
    apply (simp_all named_ss HOL_ss: IdI split in_br_conv prod_rel_iff cdom_olist_rel_def id_def)
    apply simp_all
    apply (simp_all split: prod.splits)
    done
    
    
  definition "heapify_btu_param cparam l h xs\<^sub>0 \<equiv> doN {
    ASSERT(h>0);
    (xs,l') \<leftarrow> WHILET 
      (\<lambda>(xs,l'). l'>l) 
      (\<lambda>(xs,l'). doN {
        ASSERT (l'>0);
        let l'=l'-1;
        xs \<leftarrow> sift_down_param cparam l h l' xs;
        RETURN (xs,l')
      })
      (xs\<^sub>0,h-1);
    RETURN xs
  }"    
    
  lemma heapify_btu_param_refine[refine]: 
    "\<lbrakk> (l',l)\<in>Id; (h',h)\<in>Id; (xs',xs)\<in>cdom_list_rel cparam\<rbrakk> 
    \<Longrightarrow> heapify_btu_param cparam l' h' xs' \<le> \<Down>(cdom_list_rel cparam) (heapify_btu1 (less' cparam) l h xs)"
    unfolding heapify_btu_param_def heapify_btu1_def
    apply (refine_rcg prod_relI)
    supply [refine_dref_RELATES] = RELATESI[of "cdom_list_rel cparam"]
    apply refine_dref_type
    by auto
    
  term heapsort1  
    
  definition heapsort_param :: "'cparam \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list nres" 
  where "heapsort_param cparam xs\<^sub>0 l h\<^sub>0 \<equiv> doN {
    ASSERT (l\<le>h\<^sub>0);
    if h\<^sub>0-l > 1 then doN {
      xs \<leftarrow> heapify_btu_param cparam l h\<^sub>0 xs\<^sub>0;
      
      (xs,h)\<leftarrow>WHILET
        (\<lambda>(xs,h). Suc l < h) 
        (\<lambda>(xs,h). doN {
          ASSERT (h>0 \<and> l\<noteq>h-1);
          xs \<leftarrow> mop_list_swap xs l (h-1);
          xs \<leftarrow> sift_down_param cparam l (h-1) l xs;
          RETURN (xs,h-1)
        })
        (xs,h\<^sub>0);
      
      RETURN xs
    } else
      RETURN xs\<^sub>0
  }"

  lemma heapsort_param_refine[refine]: "\<lbrakk>
    (l',l)\<in>Id; (h',h)\<in>Id; (xs',xs)\<in>cdom_list_rel cparam
  \<rbrakk> \<Longrightarrow> heapsort_param cparam xs' l' h' \<le> \<Down>(cdom_list_rel cparam) (heapsort1 (less' cparam) xs l h)"  
    unfolding heapsort_param_def heapsort1_def mop_list_swap_alt (* TODO: inlined mop-list-swap refinement proof! *)
    apply refine_rcg
    supply [refine_dref_RELATES] = RELATESI[of "cdom_list_rel cparam"]
    apply refine_dref_type
    apply (auto simp: in_br_conv cdom_list_rel_alt)
    done
  
  
  lemma heapsort_param_correct: 
    assumes "(xs',xs)\<in>Id" "(l',l)\<in>Id" "(h',h)\<in>Id"
    shows "heapsort_param cparam xs' l' h' \<le> pslice_sort_spec cdom pless cparam xs l h"
  proof -
    note heapsort_param_refine[unfolded heapsort1.refine[OF WO.weak_ordering_axioms, symmetric]]
    also note WO.heapsort_correct'
    also note slice_sort_spec_xfer
    finally show ?thesis 
      unfolding pslice_sort_spec_def
      apply refine_vcg
      using assms unfolding cdom_list_rel_alt
      by (simp add: in_br_conv)
    
  qed

  lemma heapsort_param_correct': 
    shows "(PR_CONST heapsort_param, PR_CONST (pslice_sort_spec cdom pless)) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    using heapsort_param_correct 
    apply (intro fun_relI nres_relI) 
    by simp
    
  
  
end

context parameterized_sort_impl_context begin

sepref_def mop_geth_impl [llvm_inline] is "uncurry3 mop_geth3" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a eo_assn\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a elem_assn \<times>\<^sub>a eo_assn"
  unfolding mop_geth3_def by sepref
  
sepref_def mop_seth_impl [llvm_inline] is "uncurry4 mop_seth3" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a eo_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a elem_assn\<^sup>d \<rightarrow>\<^sub>a eo_assn"
  unfolding mop_seth3_def by sepref
  

end


context parameterized_sort_impl_context
begin
  sepref_register "sift_down_param"
  sepref_def sift_down_impl is "uncurry4 (PR_CONST sift_down_param)" 
    :: "cparam_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a wo_assn\<^sup>d \<rightarrow>\<^sub>a wo_assn"
    unfolding sift_down_param_def PR_CONST_def
    by sepref (* Takes loooong! *)
  

sepref_register "heapify_btu_param"
sepref_def heapify_btu_impl is "uncurry3 (PR_CONST heapify_btu_param)" 
  :: "cparam_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a wo_assn\<^sup>d \<rightarrow>\<^sub>a wo_assn"
  unfolding heapify_btu_param_def PR_CONST_def
  apply (annot_snat_const "TYPE (size_t)")
  by sepref
  
sepref_register "heapsort_param"
sepref_def heapsort_param_impl is "uncurry3 (PR_CONST heapsort_param)" 
  :: "cparam_assn\<^sup>k *\<^sub>a wo_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a wo_assn"
  unfolding heapsort_param_def PR_CONST_def
  apply (rewrite at "sift_down_param _ _ _ \<hole> _" fold_COPY)
  apply (annot_snat_const "TYPE (size_t)")
  by sepref

(*

TODO: Show that this refines a param_sort_spec!

lemmas heapsort_hnr[sepref_fr_rules] = heapsort_param_impl.refine[unfolded heapsort_param.refine[OF weak_ordering_axioms,symmetric]]  
*)


lemmas heapsort_param_hnr 
  = heapsort_param_impl.refine[FCOMP heapsort_param_correct']


end

*)


global_interpretation heapsort_interp: pure_sort_impl_context "(\<le>)" "(<)" ll_icmp_ult "''icmp_ult''"  unat_assn
  defines heapsort_interp_mop_lchild_impl  = heapsort_interp.mop_lchild_impl 
      and heapsort_interp_mop_rchild_impl  = heapsort_interp.mop_rchild_impl 
      and heapsort_interp_has_rchild_impl  = heapsort_interp.has_rchild_impl 
      and heapsort_interp_has_lchild_impl  = heapsort_interp.has_lchild_impl 
      and heapsort_interp_mop_geth_impl    = heapsort_interp.mop_geth_impl  
      and heapsort_interp_mop_seth_impl    = heapsort_interp.mop_seth_impl  
      and heapsort_interp_sift_down_impl   = heapsort_interp.sift_down_impl
      and heapsort_interp_heapify_btu_impl = heapsort_interp.heapify_btu_impl
      and heapsort_interp_heapsort_impl    = heapsort_interp.heapsort_impl
  by (rule unat_sort_impl_context)

export_llvm "heapsort_interp_heapsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* heapsort(uint64_t*, int64_t,int64_t)"
  file "../code/heapsort.ll"


end
