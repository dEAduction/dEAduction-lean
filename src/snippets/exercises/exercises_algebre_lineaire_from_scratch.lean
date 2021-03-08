import tactic

-- dEAduction imports
import structures2
import definitions
import notations_definitions

-- General principles :
-- Type should be defined as parameters, in order to be implicit everywhere
-- other parameters are implicit in definitions, i.e. defined using '{}' (e.g. {A : set X} )
-- but explicit everywhere else, i.e. defined using '()' (e.g. (A : set X) )
-- each definition must be an iff statement (since it will be called with 'rw' or 'symp_rw')



local attribute [instance] classical.prop_decidable

---------------------------------------------
-- global parameters = implicit variables --
---------------------------------------------
section course

/-- Une structure de R-espace vectoriel sur un type X -/
class R_espace_vectoriel (X : Type) :=
()
(dist : X → X → ℝ)
(dist_pos : ∀ x y, dist x y ≥ 0)
(sep : ∀ x y, dist x y = 0 ↔ x = y)
(sym : ∀ x y, dist x y = dist y x)
(triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)



section definitions


















end definitions

end course