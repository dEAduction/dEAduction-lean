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
title = "Autour de suites - Première partie"
author = "Frédéric Le Roux et Isabelle Dubois"
institution = "Université du monde"
description = """
Des exercices sur les suites - Première partie

"""
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
-/



section course
open tactic.interactive


-----------------
--  exercices  --
-----------------

namespace suites_1
/- dEAduction
pretty_name = "Suites : première partie"
-/
 
lemma exercise.implication4
(u : ℕ → ℝ)  :
 (∀ n : ℕ, ∀ m : ℕ, u m = u n) → (∀ n, u n = u 0) 
:=
/- dEAduction
pretty_name = "Implication proposition A vers proposition B"
-/
begin
  todo,
end



lemma exercise.implication3
(u : ℕ → ℝ)  :
(∀ n, u n = u 0)  → (∀ n : ℕ,( ∀ m : ℕ, u m = u n))
:=
/- dEAduction
pretty_name = "Implication proposition B vers proposition A"
-/
begin
  todo,
end



lemma exercise.implication9
(u : ℕ → ℝ)  :
(∃ c : ℝ, ∀ n: ℕ,  (u n = c))  → (∃ n: ℕ, ∀ m: ℕ, u m = u n)
:=
/- dEAduction
pretty_name = "Implication proposition C vers proposition D"
-/
begin
  todo,
end

end suites_1






end course
