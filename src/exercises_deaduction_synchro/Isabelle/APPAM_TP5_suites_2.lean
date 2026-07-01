/-
This is a d∃∀duction file providing exercises about sequences.
-/

-- Lean standard imports
import tactic
import data.real.basic

-- dEAduction tactics
-- structures2 and utils are vital
import deaduction_all_tactics
-- import structures2      -- hypo_analysis, targets_analysis
-- import utils            -- no_meta_vars
-- import compute_all      -- Tactics for the compute buttons
-- import push_neg_once    -- Pushing negation just one step
-- import induction        -- Induction theorems

-- dEAduction definitions
import set_definitions
import real_definitions

-- Use classical logic
local attribute [instance] classical.prop_decidable

-------------------------
-- dEAduction METADATA --
-------------------------
/- dEAduction
title = "Autour de suites - Deuxième partie"
author = "Frédéric Le Roux et Isabelle Dubois"
institution = "Université du monde"
description = """
Des exercices sur les suites - Deuxième partie

"""
available_exercises = "NONE"
[settings]
display.use_symbols_for_logic_button = false
logic.usr_jokers_available = false
logic.usr_name_new_vars = true
logic.use_color_for_applied_properties = true
functionality.allow_sorry = true
functionality.allow_induction = true
functionality.calculator_available = true
functionality.automatic_use_of_exists = false
functionality.automatic_use_of_and = false
functionality.ask_to_prove_premises_of_implications = true
others.Lean_request_method = "normal"
logs.save_journal = false

[display]
constante_a_partir_certain_rang = [-1, " constante à partir d'un certain rang"]
-/



section course
open tactic.interactive


-----------------
--  exercices  --
-----------------

definition constante_a_partir_certain_rang (u : ℕ → ℝ) : Prop 
:= ∃ c: ℝ, ∃ N:ℕ, ∀ n ≥ N, u n =c 


namespace suites_2
/- dEAduction
pretty_name = "Suites : deuxième partie"
-/


lemma exercise.implication11
(u : ℕ → ℝ)  :
(∀ n: ℕ, ∀ m : ℕ, u m = u n)  → (∃ n: ℕ, ∀ m: ℕ, u m = u n)
:=
/- dEAduction
pretty_name = "Implication proposition A vers proposition D"
-/
begin
  todo,
end


lemma exercise.implication12
(u : ℕ → ℝ)  :
 (∃ n: ℕ, ∀ m: ℕ, u m = u n) → (∀ n : ℕ, ∀ m : ℕ, u m = u n)
:=
/- dEAduction
pretty_name = "Implication proposition D vers proposition A"
-/
begin
  todo,
end

lemma exercise.implication7
(u : ℕ → ℝ)  :
(∃ c : ℝ, ∀ n: ℕ,  (u n = c))  → (∀ n : ℕ, ∀ m : ℕ, u m = u n)
:=
/- dEAduction
pretty_name = "Implication proposition C vers proposition A : PAR CONTRAPOSITION"
description = "On fera obligatoirement un raisonnement par contraposée"
-/
begin
  todo,
end

end suites_2


----------------------


namespace suites_3
/- dEAduction
pretty_name = "Suites : autres exercices s'il reste du temps"
-/


lemma exercise.implication1
(u : ℕ → ℝ)  :
(∀ n, u n = u 0)  → (∃ c : ℝ, ∀ n: ℕ,  (u n = c))
:=
/- dEAduction
pretty_name = "Implication proposition B vers proposition C"
-/
begin
  todo,
end

lemma exercise.implication2
(u : ℕ → ℝ)  :
 (∃ c : ℝ, ∀ n: ℕ,  (u n = c)) → (∀ n, u n = u 0) 
:=
/- dEAduction
pretty_name = "Implication proposition C vers proposition B"
-/
begin
  todo,
end



lemma exercise.implication5
(u : ℕ → ℝ)  :
(∀ n, u n = u 0)  → (∃ n: ℕ, ∀ m: ℕ, u m = u n)
:=
/- dEAduction
pretty_name = "Implication proposition B vers proposition D"
-/
begin
  todo,
end

lemma exercise.implication6
(u : ℕ → ℝ)  :
 (∃ n: ℕ, ∀ m: ℕ, u m = u n) → (∀ n, u n = u 0) 
:=
/- dEAduction
pretty_name = "Implication proposition D vers proposition B"
-/
begin
  todo,
end



lemma exercise.implication8
(u : ℕ → ℝ)  :
 (∀ n : ℕ, ∀ m : ℕ, u m = u n) → (∃ c : ℝ, ∀ n: ℕ,  (u n = c))
:=
/- dEAduction
pretty_name = "Implication proposition A vers proposition C"
-/
begin
  todo,
end

lemma exercise.implication10
(u : ℕ → ℝ)  :
 (∃ n: ℕ, ∀ m: ℕ, u m = u n) → (∃ c : ℝ, ∀ n: ℕ,  (u n = c))
:=
/- dEAduction
pretty_name = "Implication proposition D vers proposition C"
-/
begin
  todo,
end

lemma exercise.incorrecte1    :
(∀ u : ℕ → ℝ, ∀ m: ℕ, ∃ n: ℕ, u m = u n) 
:=
/- dEAduction
pretty_name = "Vrai ou Faux ?"
open_question = true
-/
begin
  todo
end

namespace a_partir_dun_certain_rang
/- dEAduction
pretty_name = "Propriétés vraies à partir d'un certain rang"
-/

lemma definition.suite_constante_rang (u : ℕ → ℝ)  :
constante_a_partir_certain_rang u ↔
(∃ c: ℝ, ∃ N:ℕ, ∀ n ≥ N, u n = c) :=
/- dEAduction
pretty_name = "Suite constante à partir d'un certain rang"
-/
begin
  refl,
end


lemma exercise.somme
(u v : ℕ → ℝ) (H: constante_a_partir_certain_rang u)
(H': constante_a_partir_certain_rang v) : 
constante_a_partir_certain_rang (λn, u n + v n) :=
/- dEAduction
pretty_name = "Somme de suites constantes à partir d'un certain rang"
-/
begin
  todo
end
end a_partir_dun_certain_rang
end suites_3




end course
