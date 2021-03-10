theory Sorting_Strings
  imports "HOL-Library.List_Lexorder" Sorting_Setup 
  "../dynarray/Dynamic_Array" "Sorting_Quicksort_Partition"
begin

  text \<open>The string comparison algorithm from libstdc++, abstractly: Compare min-length first, then compare lengths to break tie\<close>
  lemma list_lexorder_alt: "xs < ys \<longleftrightarrow> (let n=min (length xs) (length ys) in (take n xs < take n ys) \<or> (take n xs = take n ys \<and> length xs < length ys))"
  proof (cases "length xs < length ys")
    case True
    then show ?thesis
      apply (simp add: Let_def)
    proof (induction xs arbitrary: ys)
      case Nil
      then show ?case by (cases ys) auto 
    next
      case (Cons a xs)
      then show ?case by (cases ys) auto
    qed
  next
    case False
    then show ?thesis
      apply (simp add: Let_def)
    proof (induction xs arbitrary: ys)
      case Nil
      then show ?case by (cases ys) auto 
    next
      case (Cons a xs)
      then show ?case by (cases ys) auto
    qed
  qed
    
    
  definition cmpi :: "'a::preorder \<Rightarrow> 'a \<Rightarrow> int" where "cmpi x y \<equiv> if x = y then 0 else if x < y then -1 else (1::int)"
  
  lemma cmpi_simps[simp]: 
    "cmpi x y = 0 \<longleftrightarrow> x=y"
    "cmpi x y = -1 \<longleftrightarrow> x<y"
    "cmpi x y = 1 \<longleftrightarrow> x\<noteq>y \<and> (\<not>x<y)"
    "0 = cmpi x y \<longleftrightarrow> x=y"
    "-1 = cmpi x y \<longleftrightarrow> x<y"
    "1 = cmpi x y \<longleftrightarrow> x\<noteq>y \<and> (\<not>x<y)"
    "x=y \<Longrightarrow> cmpi x y = 0"
    "x<y \<Longrightarrow> cmpi x y = -1"
    unfolding cmpi_def by auto

 
  term "m *m e"
  definition "compare_cost xs ys n = (enat n) *m (cost ''ult_lt'' 1 
              + lift_acost mop_array_nth_cost + lift_acost mop_array_nth_cost 
              + cost ''ult_eq'' 1 + cost ''ult_add'' 1)"
  
  definition "compare_spec xs ys n \<equiv> doN {ASSERT (n\<le>length xs \<and> n\<le>length ys); SPECT [ (cmpi (take n xs) (take n ys)) \<mapsto> compare_cost xs ys n]}"


  definition "compare1 xs ys n \<equiv> doN {
    ASSERT (n\<le>length xs \<and> n\<le>length ys);
    (i,r)\<leftarrow> monadic_WHILEIET (\<lambda>(i,r). i\<le>n \<and> r=cmpi (take i xs) (take i ys) )
        (\<lambda>(i::nat,r::int). undefined:: (string, nat) acost)
       (\<lambda>(i,r).doN { 
              if\<^sub>N SPECc2 ''icmp_slt'' (<) i n 
                then SPECc2 ''icmp_eq'' (=) r 0
                else RETURNT False
            } )
       (\<lambda>(i,r). doN {
      x \<leftarrow> mop_array_nth xs i;
      y \<leftarrow> mop_array_nth ys i;
      ASSERT (i<n);
      if\<^sub>N SPECc2 ''icmp_eq'' (=) x y
        then doN {
            i' \<leftarrow> SPECc2 ''add'' (+) i 1;
            RETURNT (i',0) }
      else if\<^sub>N SPECc2 ''icmp_ult'' (<) x y then doN {
            i' \<leftarrow> SPECc2 ''add'' (+) i 1;
            RETURNT (i',-1) }
      else doN {
            i' \<leftarrow> SPECc2 ''add'' (+) i 1;
            RETURNT (i',1) }
    }) (0,0);
    RETURN r
  }"

  (* TODO: fix type of monadic_WHILEIET *)


  (* TODO: Move *)    
  lemma irreflD: "irrefl R \<Longrightarrow> (x,x)\<notin>R" by (auto simp: irrefl_def) 
  
  (* TODO: Move *)
  lemma lexord_append: "length u = length w \<Longrightarrow> (u@v,w@x)\<in>lexord R \<longleftrightarrow> (u,w)\<in>lexord R \<or> (u=w \<and> (v,x)\<in>lexord R)"  
    by (induction u w rule: list_induct2) auto

  lemma lexord_irreflD: "irrefl R \<Longrightarrow> \<not>(u,u)\<in>lexord R"
    by (simp add: irreflD lexord_irrefl) 
    
  lemma lexord_irrefl_common_prefix: "irrefl R \<Longrightarrow> (u@v,u@w)\<in>lexord R \<longleftrightarrow> (v,w)\<in>lexord R"
    by (auto simp: lexord_append lexord_irreflD)
    
    
  context begin
    private lemma take_smaller: "m\<le>n \<Longrightarrow> take n xs = take m xs @ (take (n-m) (drop m xs))"
      by (metis le_add_diff_inverse take_add)
      
    private lemma compare_impl_aux1:  "\<lbrakk>aa\<le>n; aa \<le> length xs; aa\<le>length ys; take aa xs \<noteq> take aa ys\<rbrakk> \<Longrightarrow> cmpi (take n xs) (take n ys) = cmpi (take aa xs) (take aa ys)"  
      by (auto simp: take_smaller cmpi_def list_less_def lexord_append)
    
    private lemma preorder_less_irrefl: "irrefl {(x, y::_::preorder). x < y}" by (auto simp: irrefl_def) 
      
    lemma compare1_refine: "(compare1, compare_spec) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nrest_rel" (*
      apply (intro fun_relI, clarsimp)
      subgoal for xs ys n
        unfolding compare1_def compare_spec_def
        apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(i,_). n-i)"])
        by (auto simp: take_Suc_conv_app_nth list_less_def lexord_append compare_impl_aux1 lexord_irreflD[OF preorder_less_irrefl])
      done *)      
      apply(intro fun_relI nrest_relI)
      unfolding compare_spec_def 
      unfolding compare1_def
      unfolding SPECc2_def
      unfolding mop_array_nth_def
      apply(rule ASSERT_D2_leI)
      apply simp
      apply(rule gwp_specifies_I)
      apply(refine_vcg \<open>-\<close> rules: gwp_monadic_WHILEIET If_le_rule)
      subgoal sorry
      subgoal 
        apply(rule loop_body_conditionI)
        sorry
      subgoal 
        apply(rule loop_body_conditionI)
        sorry
      subgoal 
        apply(rule loop_body_conditionI)
        sorry
      subgoal sorry
      subgoal sorry
      subgoal sorry
      subgoal 
        apply(rule loop_exit_conditionI)
        sorry
      (* have a look at the proof in *)
      thm weak_ordering.qsp_next_l_refine

      sorry (* TODO: Peter *) 
      
  end


  abbreviation "string_assn' TYPE('size_t::len2) TYPE('w::len) \<equiv> al_assn' TYPE('size_t::len2) (unat_assn' TYPE('w::len))"


  sepref_definition compare_impl2 [llvm_inline, llvm_code] is "uncurry2 compare1" :: 
    "(string_assn' TYPE('size_t::len2) TYPE('w::len))\<^sup>k *\<^sub>a (string_assn' TYPE('size_t) TYPE('w))\<^sup>k *\<^sub>a (snat_assn' TYPE('size_t))\<^sup>k \<rightarrow>\<^sub>a sint_assn' TYPE('r::len2)"  
    unfolding compare1_def
    unfolding monadic_WHILEIET_def
    apply (annot_snat_const "TYPE('size_t)")
    apply (annot_sint_const "TYPE('r)")
    by sepref 

  term b_assn
  term nbn_assn

definition "bstring_assn n TYPE('size_t::len2) TYPE('w::len)
       = b_assn (string_assn' TYPE('size_t::len2) TYPE('w::len)) (\<lambda>ls. length ls \<le> n)"


  
find_theorems hr_comp b_rel  
  
(* TODO: Move *)
lemma hr_comp_brel[fcomp_norm_simps]: "hr_comp A (b_rel B P) = b_assn (hr_comp A B) P"
  by (auto simp: hr_comp_def fun_eq_iff sep_algebra_simps pred_lift_extract_simps)

  
lemma mop_array_nth_len_bound:
  fixes nth_impl A B
  assumes "(uncurry nth_impl, uncurry mop_array_nth) \<in> A\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a B"
  shows "(uncurry nth_impl, uncurry mop_array_nth) \<in> (b_assn A P)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a B"
proof -
  have A: "(mop_array_nth, mop_array_nth) \<in> b_rel Id P \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nrest_rel"
    by (auto simp add: refine_pw_simps fun_rel_def pw_acost_nrest_rel_iff)
    
  from assms(1)[FCOMP A[to_fref]] show ?thesis .
qed    
    
lemma mop_array_upd_len_bound:
  fixes upd_impl A B
  assumes "(uncurry2 upd_impl, uncurry2 mop_array_upd) \<in> A\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a B\<^sup>k \<rightarrow>\<^sub>a A"
  shows "(uncurry2 upd_impl, uncurry2 mop_array_upd) \<in> (b_assn A (\<lambda>xs. P (length xs)))\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a B\<^sup>k \<rightarrow>\<^sub>a (b_assn A (\<lambda>xs. P (length xs)))"
proof -
  have A: "(mop_array_upd, mop_array_upd) \<in> b_rel Id (\<lambda>xs. P (length xs)) \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>b_rel Id (\<lambda>xs. P (length xs))\<rangle>nrest_rel"
    by (auto simp add: refine_pw_simps fun_rel_def pw_acost_nrest_rel_iff mop_array_upd_def)
    
  from assms(1)[FCOMP A[to_fref]] show ?thesis .
qed    

lemma bstring_nth[sepref_fr_rules]:
  "(uncurry dyn_array_nth, uncurry mop_array_nth)
     \<in> (bstring_assn n TYPE('size_t::len2) TYPE('w::len))\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn' TYPE('w::len)" 
  unfolding bstring_assn_def    
  apply (rule mop_array_nth_len_bound)
  apply (rule dyn_array_nth[of unat_assn dyn_array_nth]) (* TODO: delete of dyn_array_nth when rule is complete *)
  by simp
  
  
  sepref_definition compare_impl [llvm_inline, llvm_code] is "uncurry2 compare1" :: 
    "(bstring_assn n TYPE('size_t::len2) TYPE('w::len))\<^sup>k *\<^sub>a (bstring_assn n TYPE('size_t) TYPE('w))\<^sup>k *\<^sub>a (snat_assn' TYPE('size_t))\<^sup>k \<rightarrow>\<^sub>a sint_assn' TYPE('r::len2)"  
    unfolding compare1_def
    unfolding monadic_WHILEIET_def 
    apply (annot_snat_const "TYPE('size_t)")
    apply (annot_sint_const "TYPE('r) ")
    by sepref 
 
  lemmas compare_hnr[sepref_fr_rules] = compare_impl.refine[FCOMP compare1_refine]
  
    (*
  definition "strcmp xs ys \<equiv> doN {
    let n = min (length xs) (length ys);
    i \<leftarrow> compare_spec xs ys n;
    if i=-1 then RETURN True
    else if i=0 then RETURN (length xs < length ys)
    else RETURN False
  }"

  lemma strcmp_correct: "strcmp xs ys \<le> RETURN (xs<ys)"  
    unfolding strcmp_def compare_spec_def
    apply (rewrite in "_ \<le> \<hole>" list_lexorder_alt)
    apply refine_vcg
    by (simp_all)
    
  lemma strcmp_refines_aux: "(strcmp,RETURN oo (<)) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nrest_rel"
    using strcmp_correct by (force intro!: nres_relI)
    
  
  sepref_def strcmp_impl is "uncurry strcmp" :: "(string_assn' TYPE('size_t::len2) TYPE('w::len))\<^sup>k *\<^sub>a (string_assn' TYPE('size_t) TYPE('w))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding strcmp_def min_def
    apply (annot_sint_const "TYPE(2)")
    by sepref

  *)

definition "strcmp_impl = undefined"
definition "string_cmp_cost n = cost ''bla'' n"


term string_cmp_cost
term compare_cost

(* hier passiert die überabschätzung *)

lemma strcmp_impl_refine:
  "(uncurry strcmp_impl, uncurry (SPECc3 (lift_acost (string_cmp_cost n)) (<)))
   \<in> (bstring_assn n TYPE('size_t::len2) TYPE('w::len2))\<^sup>k *\<^sub>a (bstring_assn n TYPE('size_t) TYPE('w))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  sorry

  export_llvm "strcmp_impl :: 64 word \<times> 64 word \<times> 8 word ptr \<Rightarrow> 64 word \<times> 64 word \<times> 8 word ptr \<Rightarrow> 1 word llM"



lemma strcmp_refines_relp: "GEN_ALGO strcmp_impl (refines_relp (bstring_assn n TYPE('size_t::len2) TYPE('w::len2))
                    (lift_acost (string_cmp_cost n)) (<))"
    apply rule
    using strcmp_impl_refine[of n, where 'size_t='size_t] .

 

lemma strcmp_sort_impl_context: "8 \<le> LENGTH('size_t::len2) \<Longrightarrow> sort_impl_context TYPE('size_t) (\<le>) (<) strcmp_impl (string_cmp_cost n)
               (bstring_assn n TYPE('size_t) TYPE('w::len2))"
    apply unfold_locales
    apply (auto simp: strcmp_refines_relp)
  sorry


  
  
end
