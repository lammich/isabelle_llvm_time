\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
section \<open>Final Hoare Triples for heapsort and introsort\<close>
theory Sorting_Results
imports Sorting_Introsort
begin

paragraph \<open>Summary\<close>
text \<open>This theory collects the final Hoare Triples for heapsort and introsort.
  They do not involve the NREST monad any more. For inspecting their validity, only the
  LLVM semantics and the definitions of Hoare triples must be checked.
  By summing over all currencies, we project the fine-grained cost functions used in the
  Hoare Triples down to functions in @{typ "nat \<Rightarrow> nat"} and examine their asymptotic complexity.\<close>


subsection \<open>Heapsort\<close>


context sort_impl_context begin

lemma "slice_sort_aux xs\<^sub>0 xs l h \<equiv> (length xs = length xs\<^sub>0 \<and> take l xs = take l xs\<^sub>0
                    \<and> drop h xs = drop h xs\<^sub>0 \<and> sort_spec (\<^bold><) (slice l h xs\<^sub>0) (slice l h xs))"
  by simp

text \<open>Final correctness lemma:\<close>
lemma 
  assumes "l \<le> h \<and> h \<le> length xs\<^sub>0"
  shows "llvm_htriple ($heapsort_impl_cost l h \<and>* arr_assn xs\<^sub>0 p
           \<and>* pure snat_rel l l' \<and>* pure snat_rel h h')
        (heapsort_impl p l' h')
      (\<lambda>r. (\<lambda>s. \<exists>xs. (\<up>(slice_sort_aux xs\<^sub>0 xs l h) \<and>* arr_assn xs r) s)
           \<and>* invalid_assn arr_assn xs\<^sub>0 p \<and>* pure snat_rel l l' \<and>* pure snat_rel h h')"
  using assms
  apply(rule heapsort_final_hoare_triple[unfolded hn_ctxt_def])
  done

text \<open>@{term heapsort_impl_cost} projected to a function @{typ "nat \<Rightarrow> nat"} \<close>
lemma "heapsort3_allcost (h-l) = project_all (heapsort_impl_cost l h)"
  by (simp add: heapsort3_allcost_is_heapsort3_allcost' heapsort3_allcost'_Sum_any)

end

lemma "heapsort3_allcost n = 12 + 187 * n  + 82 * (n * Discrete.log n)"
  unfolding heapsort3_allcost_def by simp
  
lemma "(\<lambda>x. real (heapsort3_allcost x)) \<in> \<Theta>(\<lambda>n. (real n)*(ln (real n)))"
  by (fact heapsort3_allcost_nlogn)


subsection \<open>Introsort\<close>

context sort_impl_context begin

lemma "slice_sort_aux xs\<^sub>0 xs l h \<equiv> (length xs = length xs\<^sub>0 \<and> take l xs = take l xs\<^sub>0
                    \<and> drop h xs = drop h xs\<^sub>0 \<and> sort_spec (\<^bold><) (slice l h xs\<^sub>0) (slice l h xs))"
  by simp

text \<open>Final correctness lemma:\<close>
lemma
  assumes "l \<le> h \<and> h \<le> length xs\<^sub>0"
  shows "llvm_htriple ($introsort_impl_cost (h-l) \<and>* arr_assn xs\<^sub>0 p
           \<and>* pure snat_rel l l' \<and>* pure snat_rel h h')
        (introsort_impl p l' h')
      (\<lambda>r. (\<lambda>s. \<exists>xs. (\<up>(slice_sort_aux xs\<^sub>0 xs l h) \<and>* arr_assn xs r) s)
           \<and>* invalid_assn arr_assn xs\<^sub>0 p \<and>* pure snat_rel l l' \<and>* pure snat_rel h h')"
  by (rule introsort_final_hoare_triple[OF assms, unfolded hn_ctxt_def])

text \<open>introsort_impl_cost projected to a function @{typ "nat \<Rightarrow> nat"} \<close>
lemma "introsort3_allcost n = project_all (introsort_impl_cost n)"  
  by (rule introsort3_allcost_is_projected_introsort_impl_cost)

end

lemma "introsort3_allcost n = 4693 + 5 *  Discrete.log n + 231 * n + 455 * (n * Discrete.log n)"
  by(fact introsort3_allcost_simplified)

  
lemma "(\<lambda>x. real (introsort3_allcost x)) \<in> \<Theta>(\<lambda>n. (real n)*(ln (real n)))"
  by (fact introsort3_allcost_nlogn)


end