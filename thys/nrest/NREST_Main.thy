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







abbreviation (do_notation) bind_doN where "bind_doN \<equiv> NREST.bindT"

notation (output) bind_doN (infixr "\<bind>" 54)
notation (ASCII output) bind_doN (infixr ">>=" 54)

nonterminal doN_binds and doN_bind
syntax
  "_doN_block" :: "doN_binds \<Rightarrow> 'a" ("doN {//(2  _)//}" [12] 62)
  "_doN_bind"  :: "[pttrn, 'a] \<Rightarrow> doN_bind" ("(2_ \<leftarrow>/ _)" 13)
  "_doN_let" :: "[pttrn, 'a] \<Rightarrow> doN_bind" ("(2let _ =/ _)" [1000, 13] 13)
  "_doN_then" :: "'a \<Rightarrow> doN_bind" ("_" [14] 13)
  "_doN_final" :: "'a \<Rightarrow> doN_binds" ("_")
  "_doN_cons" :: "[doN_bind, doN_binds] \<Rightarrow> doN_binds" ("_;//_" [13, 12] 12)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr "\<then>" 54)

syntax (ASCII)
  "_doN_bind" :: "[pttrn, 'a] \<Rightarrow> doN_bind" ("(2_ <-/ _)" 13)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr ">>" 54)

translations
  "_doN_block (_doN_cons (_doN_then t) (_doN_final e))"
    \<rightleftharpoons> "CONST bind_doN t (\<lambda>_. e)"
  "_doN_block (_doN_cons (_doN_bind p t) (_doN_final e))"
    \<rightleftharpoons> "CONST bind_doN t (\<lambda>p. e)"
  "_doN_block (_doN_cons (_doN_let p t) bs)"
    \<rightleftharpoons> "let p = t in _doN_block bs"
  "_doN_block (_doN_cons b (_doN_cons c cs))"
    \<rightleftharpoons> "_doN_block (_doN_cons b (_doN_final (_doN_block (_doN_cons c cs))))"
  "_doN_cons (_doN_let p t) (_doN_final s)"
    \<rightleftharpoons> "_doN_final (let p = t in s)"
  "_doN_block (_doN_final e)" \<rightharpoonup> "e"
(*  "(m \<then> n)" \<rightharpoonup> "(m \<bind> (\<lambda>_. n))"*)

(* TODO: move *)
abbreviation RETURNTecost :: "'a \<Rightarrow> ('a, (string,enat) acost) nrest"
  where "RETURNTecost \<equiv> RETURNT"

end