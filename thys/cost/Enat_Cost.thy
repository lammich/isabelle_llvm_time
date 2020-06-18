theory Enat_Cost
imports "HOL-Library.Extended_Nat" Abstract_Cost
begin


declare [[coercion_enabled = false]]


definition "lift_acost c \<equiv> acostC (enat o the_acost c)"

lemma lift_acost_zero: "lift_acost 0 = 0" by (auto simp add: lift_acost_def zero_acost_def zero_enat_def )


lemma lift_acost_cost: "lift_acost (cost name x) = (cost name (enat x))"
  by (auto simp: one_enat_def zero_enat_def lift_acost_def cost_def zero_acost_def)

end