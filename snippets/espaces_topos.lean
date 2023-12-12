import tactic
import data.set
import data.finset
import set_definitions
import user_notations
import parser_analysis_definitions
import topology.basic

-- import structures2

section definitions

parameter I : index_set
parameter J : finset I

class espaces_topologiques (X : Type) :=
(ouvert : set X → Prop)
(union_ouverts : ∀ F: I → set X, (∀ i, ouvert (F i)) → ouvert (set.Union F))
(intersection_ouverts: ∀ O O', ouvert O ∧ ouvert O' → ouvert (O ∩ O'))






end definitions




