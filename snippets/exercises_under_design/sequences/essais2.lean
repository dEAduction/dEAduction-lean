import tactic
import structures2
import utils
import data.real.basic
import compute

/- dEAduction
Title
    Ensembles et applications
Institution
    Université du monde
AvailableProof
    proof_methods new_object apply
AvailableMagic
    assumption
AvailableExercises
  UNTIL_NOW -image_directe_et_inclusion_II -image_reciproque_et_inclusion_II -image_directe_et_intersection_II
-/

local attribute [instance] classical.prop_decidable
---------------------------------------------
-- global parameters = implicit variables --
---------------------------------------------
section course


------------------
-- COURSE TITLE --
------------------
namespace maths_approfondies
/- dEAduction
PrettyName
    1M003 : mathématiques approfondies
-/




def limite (u:ℕ → ℝ ) (l: ℝ) := 
∀ ε > 0, ∃ N >0, ∀ n ≥ N, |u n - l| < ε 
 

lemma definition.limite {u: ℕ → ℝ} (l: ℝ):
limite u l ↔  ∀ ε > 0, ∃ n_0 >0, ∀ n ≥ n_0, |u n - l| < ε 
:=
/- dEAduction
ImplicitUse
    True
DummyVarsNames
    FromLean
-/
begin
    refl,
end

lemma exercise.essai_suites1 :
limite (λ n, 1/(n+1)) 0 :=
begin
    -- rw limite,
    sorry
end




end maths_approfondies

end course