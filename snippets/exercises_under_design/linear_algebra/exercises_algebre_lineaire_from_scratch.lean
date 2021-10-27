-- import data.set
import tactic

-- dEAduction imports
import structures2
import notations_definitions
import utils

-- General principles :
-- Type should be defined as parameters, in order to be implicit everywhere
-- other parameters are implicit in definitions, i.e. defined using '{}' (e.g. {A : set X} )
-- but explicit everywhere else, i.e. defined using '()' (e.g. (A : set X) )
-- each definition must be an iff statement (since it will be called with 'rw' or 'symp_rw')

---------------------
-- Course metadata --
---------------------


/- dEAduction
Title
    blabla
Author
    Frédéric Le Roux
Institution
    Université de France
AvailableMagic
    ALL -compute
-/


local attribute [instance] classical.prop_decidable


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
class R_espace_vectoriel (X : Type) (zero : ):=
(add : X → X → X)
(mul : ℝ → X → X)
(add_com : sorry)
(add_ass : sorry)
()

section definitions


















end definitions

end course