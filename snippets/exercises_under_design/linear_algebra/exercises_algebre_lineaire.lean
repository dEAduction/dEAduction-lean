
import tactic
import linear_algebra
--import algebra.module
--import topology.algebra.module
--import topology.instances.real
--import topology.instances.real_vector_space

-- dEAduction imports
import structures2
import notations_definitions
import utils

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
variable {f: E → F}



def est_lineaire (f: E → F) := ∀ u v : E, ∀ α β : ℝ, f(α • u + β • v) = α • f(u) + β • f(v)
def Ker (f: E → F) := {u:E | f u =0}

-- A INTRODUIRE : sev ; vect ; somme ; somme directe

-- example (x : E) : (0:E) + x = x := 


-- Axioms
lemma theorem.un_mul (u : E) : (1:ℝ) • u = u := one_smul ℝ u

example (α β : ℝ) (u : E) : (α + β)•u 	= 	(α • u) + (β • u) := 
begin 
    exact add_smul _ _ _
end

example (α : ℝ) (u v : E) : α • (u + v) = α • u + α • v :=
begin
    exact smul_add _ _ _ 
end

example (α β : ℝ) (u : E) : α • (β • u) 	= 	(α * β) • u := 
begin
    exact smul_smul _ _ _
end

-- "easy" csqces
example (α : ℝ) : α • (0 : E) = 0 := smul_zero _

example (u : E) : (0:ℝ) • u = 0 := zero_smul ℝ u

lemma theorem.mul_egal {u v : E} {α : ℝ} (H : u=v) : α • u = α • v :=
begin
    exact congr_arg (has_scalar.smul α) H,
end 

lemma theorem.egal_mul {u : E} {α β : ℝ} (H : α = β) : α • u = β • u :=
begin
    exact congr_fun (congr_arg has_scalar.smul H) u
end 


lemma inv_mul (a : ℝ) (H : a ≠ 0) : a⁻¹ * a = 1 := 
begin 
    exact inv_mul_cancel H,
end


lemma theorem.mul_zero_ssi (α : ℝ) (u : E) : α • u = 0 ↔ (α =0 ∨ u = 0) :=
begin
    split,
    intro H,
    by_cases (α = 0),
    {left, assumption}, 
    right,
    have H': u = 0, by 
    {calc u =  1 • u : (theorem.un_mul _).symm
    ...     =  (α ⁻¹ * α) • u  : @theorem.egal_mul u _ _ ((inv_mul α) h).symm
    ...     =  α ⁻¹ • (α • u)  : eq_comm.1 (smul_smul _ _ _)
    ...     =  α ⁻¹ • 0        : theorem.mul_egal H
    ...     = 0                : smul_zero _
    },
    assumption,
    intro H,
    cases H, rw H, exact zero_smul _ _,
    rw H, exact smul_zero _,
end




example (x :E) : x + x = 2 • x 
:=
begin
    exact (two_smul ℕ x).symm,
end



/- dEAduction
PrettyName
    La somme égale le sous-espace vectoriel engendré par l'union.
-/

/- dEAduction
PrettyName
     La somme de l'intersection avec F égale l'intersection de la somme.@
-/















end course