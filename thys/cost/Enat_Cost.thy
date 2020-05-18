theory Enat_Cost
imports "HOL-Library.Extended_Nat" Abstract_Cost
begin


declare [[coercion_enabled = false]]


definition "lift_acost c \<equiv> acostC (enat o the_acost c)"



end