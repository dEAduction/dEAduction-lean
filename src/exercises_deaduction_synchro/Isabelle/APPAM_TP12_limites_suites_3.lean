/-
This is a d∃∀duction file providing exercises about limits.
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
title = "Des exercices sur les limites de suites - Partie III"
author = "Isabelle Dubois"
institution = "Université de Lorraine"
description = """
Des exercices sur les limites des suites
    Troisième partie 

"""
available_exercises = "NONE"
[settings]
display.use_symbols_for_logic_button = false
logic.usr_jokers_available = false
logic.use_color_for_applied_properties = true
logic.usr_name_new_vars = true
functionality.allow_sorry = false
functionality.allow_induction = false
functionality.calculator_available = true
functionality.ask_to_prove_premises_of_implications = true
functionality.automatic_use_of_exists= false
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
namespace definitions
/- dEAduction
pretty_name = "Définitions"
-/

namespace suites
------------------------------
-- Définitions de la limite --
------------------------------


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

lemma definition.limit_plus_infinity
{u : ℕ → ℝ} :
(limit_plus_infinity u) ↔ ∀ M:ℝ, ∃ N:ℕ, ∀ n ≥ N, u n ≥ M := 
/- dEAduction
pretty_name = "Limite infinie d'une suite"
implicit_use = true
-/
begin
  refl
end

lemma definition.increasing_seq
{u : ℕ → ℝ} :
(increasing_seq u) ↔ 
∀ p q, p ≤ q → u p ≤ u q
:= 
/- dEAduction
pretty_name = "Suite croissante"
implicit_use = true
-/
begin
  refl
end

lemma definition.bounded_above 
{u : ℕ → ℝ} :
(bounded_above u) ↔ 
∃ M:ℝ, ∀ n,  u n ≤ M
:= 
/- dEAduction
pretty_name = "Suite majorée"
implicit_use = true
-/
begin
  refl
end



lemma definition.bounded 
{u : ℕ → ℝ} :
(bounded_sequence u) ↔ 
∃ M>0, ∀ n, | u n | ≤ M
:= 
/- dEAduction
pretty_name = "Suite bornée"
implicit_use = true
-/
begin
  refl
end

end suites


namespace valeur_absolue
variables {RealSubGroup : Type} [decidable_linear_ordered_comm_ring RealSubGroup] 

lemma definition.valeur_absolue
(a b : RealSubGroup) :
a = abs b ↔ (a ≥ 0 ∧ (a=b ∨ a=-b))
:=
begin
  todo
end

lemma theorem.valeur_absolue_majorant
(x : RealSubGroup) :
(x ≤ abs x ) :=
/- dEAduction
pretty_name = "Un réel est inférieur ou égal à sa valeur absolue"
-/
begin
  todo
end

lemma theorem.valeur_absolue_est_positive
(x : RealSubGroup) :
(0 ≤ abs x ) :=
/- dEAduction
pretty_name = "Une valeur absolue est positive"
-/
begin
  todo
end

lemma theorem.valeur_absolue_de_positif
(x : RealSubGroup) :
((0 ≤ x) → (abs x = x)) :=
/- dEAduction
pretty_name = "Valeur absolue d'un nombre positif"
-/
begin
  exact abs_of_nonneg,
end

lemma theorem.valeur_absolue_de_negatif
(x : RealSubGroup) :
((x ≤ 0) → (abs x = -x)) :=
/- dEAduction
pretty_name = "Valeur absolue d'un nombre négatif"
-/
begin
  exact abs_of_nonpos,
end

lemma theorem.majoration_valeur_absolue
(x r : RealSubGroup):
(abs x < r) ↔ ((-r < x) ∧ (x < r))
:= 
/- dEAduction
pretty_name = "Majoration d'une valeur absolue"
-/
begin
  exact abs_lt
end

lemma theorem.minoration_valeur_absolue
(x r : RealSubGroup) (H: r ≥ 0):
(r ≤ x) → (r ≤ abs x) 
:= 
/- dEAduction
pretty_name = "Minoration d'une valeur absolue"
-/
begin
   todo,
end


lemma theorem.inegalite_triangulaire
(x y : RealSubGroup):
|x + y| ≤ |x| + |y|
:= 
/- dEAduction
pretty_name = "Inégalité triangulaire"
-/
begin
  exact abs_add x y 
end

lemma theorem.valeur_absolue_produit :
∀ x y : RealSubGroup,  |x * y| = |x| * |y|
:= 
/- dEAduction
pretty_name = "Valeur absolue d'un produit"
-/
begin
  intros x y, exact abs_mul x y 
end

end valeur_absolue

----------------------------------
namespace maximum
-- The name RealSubGroup will be replaced by ℝ in d∃∀duction, 
-- but allows to treat the cases of integers or rationals.
variables {RealSubGroup : Type} [decidable_linear_order RealSubGroup] 

lemma definition.max (a b c : RealSubGroup) :
a = max b c ↔ (b ≤ a ∧ c ≤ a ∧ (a=b ∨ a=c))
:=
begin
  todo
end

lemma theorem.minoration_max_gauche :
∀ a b : RealSubGroup, a ≤ max a b :=
/- dEAduction
pretty_name = "Minoration max par membre de gauche"
-/
begin
  intros a b,
  -- hypo_analysis,
  -- norm_num, tautology,
  exact le_max_left a b,
  -- todo
end

lemma theorem.minoration_max_droite :
∀ a b : RealSubGroup,  b ≤ max a b :=
/- dEAduction
pretty_name = "Minoration max par membre de droite"
-/
begin
  todo
end

lemma theorem.max_majoration
(a b c : RealSubGroup) (Ha: a ≤ c) (Hb: b ≤ c) :
max a b ≤ c :=
/- dEAduction
pretty_name = "Majoration d'un maximum"
-/
begin
  norm_num, tautology,
  -- exact max_le Ha Hb,
end

lemma theorem.max_majoration_stricte
(a b c : RealSubGroup) (Ha: a < c) (Hb: b < c) :
max a b < c :=
/- dEAduction
pretty_name = "Majoration stricte d'un maximum"
-/
begin
  norm_num, tautology,
  -- exact max_lt Ha Hb,
end

end maximum



end definitions

-----------------
--  exercices  --
-----------------


namespace limite_positive
/- dEAduction
pretty_name = "Exercice 1 : Limite strictement positive"
-/


lemma exercise.limite_positive
(u : ℕ → ℝ) (l : ℝ) (H : limit u l)
(H' : l >0) :
∃ N, ∀ n ≥ N, u n > 0
:=
/- dEAduction
pretty_name = "Suite dont la limite est strictement positive"
-/
begin
  todo,
end

end limite_positive



namespace limite_infinie_croissante
/- dEAduction
pretty_name = "Exercice 2 : Non majoration, croissance et limite infinie"
-/




lemma exercise.croissante_non_majoree
(u: ℕ → ℝ) (H1: increasing_seq u) (H2: not (bounded_above u)) :
limit_plus_infinity u :=
/- dEAduction
pretty_name = "Une suite croissante non majorée tend vers plus l'infini"
-/
begin
  todo,
end



end limite_infinie_croissante



namespace limite_infinie_pas_finie
/- dEAduction
pretty_name = "Exercice 3 : Limite infinie et convergence"

-/

lemma exercise.limite_infinie_pas_finie
(u : ℕ → ℝ):
limit_plus_infinity u → not (converging_seq u)
:=
/- dEAduction
pretty_name = "Une suite qui tend vers plus l'infini n'est pas convergente"
description = "Ici, plusieurs méthodes de preuve peuvent être utilisées : ne pas hésiter à les essayer toutes. "
-/
begin
  todo,
end

end limite_infinie_pas_finie

namespace limite_infinie
/- dEAduction
pretty_name = "Exercice supplémentaire"
-/

lemma exercise.infinie_pas_majoree
(u: ℕ → ℝ):
((not bounded_above u) → limit_plus_infinity u)
or
(limit_plus_infinity u → not (bounded_above u))
:=
/- dEAduction
pretty_name = "Liens entre tendre vers plus l'infini et ne pas être majorée"
-/
begin
  todo,
end
end limite_infinie

end course
