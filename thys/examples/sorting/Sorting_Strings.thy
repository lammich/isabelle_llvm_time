theory Sorting_Strings
imports "HOL-Library.List_Lexorder" Sorting_Setup
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
        (\<lambda>(i::nat,r::int). False)
       (\<lambda>(i,r).doN { 
              if\<^sub>N SPECc2 ''ult_lt'' (<) i n 
                then SPECc2 ''ult_eq'' (=) r 0
                else RETURNT False
            } )
       (\<lambda>(i,r). doN {
      x \<leftarrow> mop_array_nth xs i;
      y \<leftarrow> mop_array_nth ys i;
      ASSERT (i<n);
      if\<^sub>N SPECc2 ''ult_eq'' (=) x y
        then doN {
            i' \<leftarrow> SPECc2 ''ult_add'' (+) i 1;
            RETURNT (i',0) }
      else if\<^sub>N SPECc2 ''ult_lt'' (<) x y then doN {
            i' \<leftarrow> SPECc2 ''ult_add'' (+) i 1;
            RETURNT (i',-1) }
      else doN {
            i' \<leftarrow> SPECc2 ''ult_add'' (+) i 1;
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
      sorry
      
  end


  abbreviation "string_assn' TYPE('size_t::len2) TYPE('w::len) \<equiv> al_assn' TYPE('size_t::len2) (unat_assn' TYPE('w::len))"
  
  sepref_definition compare_impl [llvm_inline, llvm_code] is "uncurry2 compare1" :: 
    "(string_assn' TYPE('size_t::len2) TYPE('w::len))\<^sup>k *\<^sub>a (string_assn' TYPE('size_t) TYPE('w))\<^sup>k *\<^sub>a (snat_assn' TYPE('size_t))\<^sup>k \<rightarrow>\<^sub>a sint_assn' TYPE('r::len2)"  
    unfolding compare1_def
    apply (annot_snat_const "TYPE('size_t)")
    apply (annot_sint_const "TYPE('r)")
    by sepref
  
  lemmas compare_hnr[sepref_fr_rules] = compare_impl.refine[FCOMP compare1_refine]
  
    
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
    
  lemma strcmp_refines_aux: "(strcmp,RETURN oo (<)) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    using strcmp_correct by (force intro!: nres_relI)
    
  
  sepref_def strcmp_impl is "uncurry strcmp" :: "(string_assn' TYPE('size_t::len2) TYPE('w::len))\<^sup>k *\<^sub>a (string_assn' TYPE('size_t) TYPE('w))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding strcmp_def min_def
    apply (annot_sint_const "TYPE(2)")
    by sepref
    
  export_llvm "strcmp_impl :: 64 word \<times> 64 word \<times> 8 word ptr \<Rightarrow> 64 word \<times> 64 word \<times> 8 word ptr \<Rightarrow> 1 word llM"


  lemma strcmp_refines_relp: "GEN_ALGO strcmp_impl (refines_relp (al_assn unat_assn) (<))"
    apply rule
    using strcmp_impl.refine[FCOMP strcmp_refines_aux] .
  
  lemma strcmp_sort_impl_context: "sort_impl_context (\<le>) (<) strcmp_impl (string_assn' TYPE('size_t::len2) TYPE('w::len))"
    apply unfold_locales
    apply (auto simp: strcmp_refines_relp)
    done
  
  
  
end
