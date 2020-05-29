theory Basic_Imports
imports
  Named_Simpsets
  "Automatic_Refinement.Refine_Util"
  "Automatic_Refinement.Misc"
  Misc_LLang
  More_List
  "Refine_Imperative_HOL.Named_Theorems_Rev"
  More_Eisbach_Tools
  Find_In_Thms
  "HOL-Library.Rewrite"
begin
    (* DO NOT USE IN PRODUCTION VERSION \<rightarrow> SLOWDOWN *)
    declare [[ML_exception_debugger, ML_debugger, ML_exception_trace]]

end
