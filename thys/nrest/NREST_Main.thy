theory NREST_Main                                                  
imports NREST NREST_Type_Classes NREST_Backwards_Reasoning Time_Refinement Data_Refinement
begin


class nrest_cost = complete_lattice + needname_zero + nonneg + ordered_semiring + semiring_no_zero_divisors

 
notepad
begin
  fix R :: "_ \<Rightarrow> (_,'b::nrest_cost) acost"
  fix Q :: "'c \<Rightarrow> ('a, 'b) acost option"
  fix m :: "('c, ('a, 'b) acost) nrest"
  have "Some 0 \<le> gwp (timerefine R m) Q"
    sorry

end


notepad
begin
  fix R :: "'b \<Rightarrow> ('a,enat) acost"
  fix m :: "('c, ('a, enat) acost) nrest"
  fix Q :: "'c \<Rightarrow> ('b, enat) acost option"
  have "m \<le> timerefine R (SPECT Q)"
    apply(simp add: timerefine_SPECT)
    apply(rule gwp_specifies_I)
    sorry

  have "Some 0 \<le> gwp m (timerefineF R Q)"
    sorry

end


end