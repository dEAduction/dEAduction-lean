-- import data.set
import tactic
import linear_algebra
--import algebra.module
--import topology.algebra.module
--import topology.instances.real
--import topology.instances.real_vector_space

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

parameters {E : Type} [add_comm_group E] [vector_space ℝ E]
variables {F : Type} [add_comm_group F] [vector_space ℝ F] [subspace ℝ F]
variables {G : Type} [add_comm_group G] [vector_space ℝ G] [subspace ℝ G]

-- A INTRODUIRE : sev ; vect ; somme ; somme directe






lemma exercise.essai (x y :E) : 2 • x + y = y + x + x
:=
begin
    abel,
end


/- dEAduction
PrettyName
    La somme égale le sous-espace vectoriel engendré par l'union
-/










end course