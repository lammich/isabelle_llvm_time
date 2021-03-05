theory Sorting_Export_Code
imports (* Sorting_PDQ *) Sorting_Introsort (* Sorting_Strings *) Sorting_Results
begin
  
text \<open>
  We instantiate Introsort and Pdqsort for unsigned \<open>i64\<close>, and for dynamic arrays of \<open>i8\<close>s \<open>string_assn\<close>.
  We then export code and generate a C header file to interface the code.
\<close>

global_interpretation unat_sort: pure_sort_impl_context "(\<le>)" "(<)" "TYPE(64)" ll_icmp_ult  "cost ''icmp_ult'' 1" unat_assn
  defines unat_sort_is_guarded_insert_impl = unat_sort.is_guarded_insert_impl
      and unat_sort_is_unguarded_insert_impl = unat_sort.is_unguarded_insert_impl
      and unat_sort_unguarded_insertion_sort_impl = unat_sort.unguarded_insertion_sort_impl
      and unat_sort_guarded_insertion_sort_impl = unat_sort.guarded_insertion_sort_impl
      and unat_sort_final_insertion_sort_impl = unat_sort.final_insertion_sort_impl
      and unat_sort_sift_down_impl   = unat_sort.sift_down_impl
      and unat_sort_heapify_btu_impl = unat_sort.heapify_btu_impl
      and unat_sort_heapsort_impl    = unat_sort.heapsort_impl
      and unat_sort_qsp_next_l_impl       = unat_sort.qsp_next_l_impl
      and unat_sort_qsp_next_h_impl       = unat_sort.qsp_next_h_impl
      and unat_sort_qs_partition_impl     = unat_sort.qs_partition_impl
      and unat_sort_partition_pivot_impl  = unat_sort.partition_pivot_impl 
      and unat_sort_introsort_aux_impl = unat_sort.introsort_aux_impl
      and unat_sort_move_median_to_first_impl = unat_sort.move_median_to_first_impl
      and unat_sort_introsort_impl        = unat_sort.introsort_impl      
  apply (rule unat_sort_impl_context)
  by simp

lemmas [llvm_inline] = unat_sort.introsort_aux_impl_def 
                      unat_sort.final_insertion_sort_impl_def
                      unat_sort.guarded_insertion_sort_impl_def
                      unat_sort.unguarded_insertion_sort_impl_def
                      unat_sort.is_guarded_insert_impl_def
                      unat_sort.is_unguarded_insert_impl_def
export_llvm "unat_sort_introsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort(uint64_t*, int64_t,int64_t)"
  file "../code/introsort.ll"

  
schematic_goal unat_sort_allcost_simp: "project_all (unat_sort.introsort_impl_cost n) = ?x"  
  apply (fold norm_cost_tag_def)
  unfolding unat_sort.projected_introsort_cost_simplified
  apply (simp add: unat_sort.Sum_any_cost) (* TODO: Move this lemma to global context *)
  by (rule norm_cost_tagI)
  
(* Final results for unat_sort: *)  
thm unat_sort.introsort_final_hoare_triple'  (* Hoare triple *)

(* Cost estimation *)
theorem unat_sort_allcost_nlogn: 
  "(\<lambda>n. real (project_all (unat_sort.introsort_impl_cost n))) \<in> \<Theta>(\<lambda>n. (real n)*(ln (real n)))"
  unfolding unat_sort_allcost_simp
  by auto2
  
  
  
  
  
end
