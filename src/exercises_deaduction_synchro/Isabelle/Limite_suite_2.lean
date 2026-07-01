/-
This is a d∃∀duction file providing exercises about limits and continuity.
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
title = "Limites de suites - Partie II"
author = "Isabelle Dubois"
institution = "Université de Lorraine"
description = """
Des exercices sur les limites des suites
    Deuxième partie 

"""
available_exercises = "NONE"
[settings]
display.use_symbols_for_logic_button = false
logic.usr_jokers_available = false
logic.use_color_for_applied_properties = true
logic.usr_name_new_vars = false
functionality.allow_sorry = true
functionality.allow_induction = false
functionality.calculator_available = true
functionality.ask_to_prove_premises_of_implications = true
functionality.automatic_use_of_exists=true
functionality.automatic_use_of_and = true
functionality.target_selected_by_default=true
functionality.allow_implicit_use_of_definitions=true
functionality.choose_order_to_prove_conjunction=true
others.Lean_request_method = "normal"
logs.save_journal = false
-/


/-- Lots of definitions -/
definition limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | u n - l | < ε

definition converging_seq (u : ℕ → ℝ) : Prop :=
∃ l, limit u l

definition limit_plus_infinity (u : ℕ → ℝ) : Prop :=
∀ M:ℝ, ∃ N:ℕ, ∀ n ≥ N, u n ≥ M

definition increasing_seq (u : ℕ → ℝ) : Prop :=
∀ p q , p ≤ q → u p ≤ u q

definition bounded_above (u : ℕ → ℝ) : Prop :=
∃ M:ℝ, ∀ n, u n ≤ M

definition bounded_below (u : ℕ → ℝ) : Prop :=
∃ m:ℝ, ∀ n, u n ≥ m

definition bounded_sequence (u : ℕ → ℝ) : Prop :=
∃ M>0, ∀ n, | u n | ≤ M




section course
open tactic.interactive
-- notation `|` x `|` := abs x

-----------------
-- definitions --
-----------------




-- #check real.exists_floor

/-
abs_pos : 0 < |a| ↔ a ≠ 0
abs_mul x y : |x * y| = |x| * |y|
abs_add x y : |x + y| ≤ |x| + |y|
-/

----------------------------------


namespace suites
/- dEAduction
pretty_name = "Suites : limites et convergence"
-/
------------------------------
-- Définitions de la limite --
------------------------------

lemma definition.limit 
{u : ℕ → ℝ} {l : ℝ} :
(limit u l) ↔ 
∀ ε > 0, ∃ N, ∀ n ≥ N, | u n - l | < ε
:= 
/- dEAduction
pretty_name = "Limite finie d'une suite"
implicit_use = true
-/
begin
  refl
end



lemma definition.converging_seq
{u : ℕ → ℝ} :
(converging_seq u) ↔ 
∃ l, limit u l
:= 
/- dEAduction
pretty_name = "Suite convergente"
implicit_use = true
-/
begin
  refl
end

end suites




namespace valeur_absolue
variables {RealSubGroup : Type} [decidable_linear_ordered_comm_ring RealSubGroup] 



lemma theorem.valeur_absolue_de_positif
(x : RealSubGroup) :
((0 ≤ x) → (abs x = x)) :=
/- dEAduction
pretty_name = "Valeur absolue d'un nombre positif"
-/
begin
  todo
end

lemma theorem.valeur_absolue_de_negatif
(x : RealSubGroup) :
((x ≤ 0) → (abs x = -x)) :=
/- dEAduction
pretty_name = "Valeur absolue d'un nombre négatif"
-/
begin
  todo
end

lemma theorem.majoration_valeur_absolue
(x r : RealSubGroup):
(abs x < r) ↔ ((-r < x) ∧ (x < r))
:= 
/- dEAduction
pretty_name = "Majoration d'une valeur absolue"
-/
begin
  todo
end


end valeur_absolue

-- end generalites


-----------------
--  exercices  --
-----------------

namespace exercices_demontrer
/- dEAduction
pretty_name = "Limite finie d'une suite : démonstration de la définition"
-/

lemma exercise.suited1
(u : ℕ → ℝ) (H : ∀ n,  u n = (5/4:  ℝ)) :
  limit u (5/4 :  ℝ)
:=
/- dEAduction
pretty_name = "1) Démontrer une limite finie"
-/
begin
  todo,
end



lemma exercise.limit_constante 
(u : ℕ → ℝ) (c : ℝ) (H : ∀ n, u n = c) :
converging_seq u :=
/- dEAduction
pretty_name = "2) La limite d'une suite constante"
description = """
  Il s'agit de démontrer, dans un cas très simple,
  l'existence d'une limite. A vous de trouver sa valeur.
"""
-/
begin
  todo,
end

lemma exercise.limit_constante2
(u : ℕ → ℝ)  (H : ∀ n, ∀ m, u n = u m) :
converging_seq u :=
/- dEAduction
pretty_name = "3) La limite d'une suite particulière"
description = """
  Trouverez vous la limite ?
"""
-/
begin
  todo,
end


end exercices_demontrer



namespace raisonnemment_epsilon
/- dEAduction
pretty_name = "Raisonnement à epsilon près, applications aux propriétés des limites et inégalités"
-/

lemma exercise.prel1
(x: ℝ) :
∃ y : ℝ, ∀ ε > 0, x < y +ε
:=
/- dEAduction
pretty_name = "4) Un premier exercice préliminaire"
description = """
Que peut valoir y ?
"""
-/
begin
  todo,
end

lemma exercise.prel2
(x : ℝ) :
 (∀ ε > 0, x < 1 + ε ) → (x  ≤ 1)
:=
/- dEAduction
pretty_name = "5) Un deuxième exercice préliminaire"
description = """
Faire un RAISONNEMENT PAR CONTRAPOSEE.
"""
-/
begin
  todo,
end



lemma exercise.prel4
(x y: ℝ) :
 (∀ ε > 0, x < y + ε ) → (x  ≤ y)
:=
/- dEAduction
pretty_name = "6) Démonstration d'un lemme"
description = """
Démonstration d'un lemme important pour le raisonnement à epsilon près.
On fera un RAISONNEMENT PAR CONTRAPOSEE.
"""
-/
begin
  todo,
end

lemma exercise.limite_inegalite_constante
(u : ℕ → ℝ) (l c : ℝ) 
 (LEMME : ∀ x y: ℝ, 
 ((∀ ε > 0, x < y + ε ) → (x  ≤ y)) )
 (Hu : limit u l) (Hc : ∀n, u n ≤ c ):
 l ≤ c
:=
/- dEAduction
pretty_name = "7) Passage à la limite dans une inégalité - 1"
description = """
  On utilisera le LEMME pour démontrer l'inégalité l ≤ c.
"""
-/
begin
  todo,
end


lemma exercise.limite_inegalites2
(u v: ℕ → ℝ) (l l' : ℝ) 
 (LEMME : ∀ x y: ℝ, 
 ((∀ ε > 0, x < y + ε ) → (x  ≤ y)) )
 (Hu : limit u l) (Hv : limit v l'):
(∀n, u n ≤ v n ) → l ≤ l'
:=
/- dEAduction
pretty_name = "8) Passage à la limite dans une inégalité - 2 (plus difficile)"
description = """
  On utilisera le LEMME pour démontrer l'inégalité  l ≤ l'.
  De plus, il faudra choisir un epsilon bien judicieux dans l'utilisation de la définition de la limite.
"""
-/
begin
  todo,
end

end raisonnemment_epsilon



end course
