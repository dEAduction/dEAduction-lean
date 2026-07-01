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
title = "Limites de suites - Partie I"
author = "Isabelle Dubois"
institution = "Université de Lorraine"
description = """
Des exercices sur les limites des suites
    Première partie 

"""
available_exercises = "NONE"
[settings]
display.use_symbols_for_logic_button = false
logic.usr_jokers_available = false
logic.use_color_for_applied_properties = true
logic.usr_name_new_vars = true
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



lemma definition.limit_plus_infinity
{u : ℕ → ℝ} :
(limit_plus_infinity u) ↔ ∀ M:ℝ, ∃ N:ℕ, ∀ n ≥ N,  M ≤ u n:= 
/- dEAduction
pretty_name = "Limite infinie d'une suite"
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



lemma theorem.valeur_absolue_oppose :
∀x: ℝ ,  abs (-x) = abs (x)
:=
/- dEAduction
pretty_name = "Valeur absolue de l'opposé d'un réel"
description = "On pourra se servir du résultat de l'exercice précédent."
-/
begin
  todo
end




end valeur_absolue

-- end generalites
namespace maximum
/- dEAduction
pretty_name = "Maximum de deux réels"
-/


-- The name RealSubGroup will be replaced by ℝ in d∃∀duction, 
-- but allows to treat the cases of integers or rationals.
variables {RealSubGroup : Type} [decidable_linear_order RealSubGroup] 

lemma definition.max (a b c : RealSubGroup) :
a = max b c ↔ (b ≤ a ∧ c ≤ a ∧ (a=b ∨ a=c))
:=
/- dEAduction
pretty_name = "Définition du maximum"
-/
begin
  todo
end

lemma theorem.ppe_max_gauche :
∀ a b : RealSubGroup, a ≤ max a b :=
/- dEAduction
pretty_name = "Propriété du maximum - gauche"
-/
begin
  todo
end

lemma theorem.ppe_max_droite :
∀ a b : RealSubGroup,  b ≤ max a b :=
/- dEAduction
pretty_name = "Propriété du maximum - droite"
-/
begin
  todo
end

lemma theorem.max_ppe
(a b c : RealSubGroup) (Ha: a ≤ c) (Hb: b ≤ c) :
max a b ≤ c :=
/- dEAduction
pretty_name = "Inégalité large maximum" 
-/
begin
  todo
end

lemma theorem.max_pp
(a b c : RealSubGroup) (Ha: a < c) (Hb: b < c) :
max a b < c :=
/- dEAduction
pretty_name = "Inégalité stricte maximum"
-/
begin
  todo
end

end maximum



-----------------
--  exercices  --
-----------------

namespace exercices_simples
/- dEAduction
pretty_name = "Limite d'une suite : utilisation de la définition"
-/

lemma exercise.suite1
(u : ℕ → ℝ) (H : limit u (-2 :  ℝ)) :
 ∃ N, ∀ n ≥ N, ((-3:  ℝ) ≤ u n) and (u n < (0:  ℝ))
:=
/- dEAduction
pretty_name = "Utilisation de la définition d'une limite finie"
-/
begin
  todo,
end

lemma exercise.suite2
(u : ℕ → ℝ) (H : limit_plus_infinity u) :
 ∃ N, ∀ n ≥ N, ((10:  ℝ) ≤ u n) and (-u n < (-42:  ℝ))
:=
/- dEAduction
pretty_name = "Utilisation de la définition d'une limite infinie"
-/
begin
  todo,
end

end exercices_simples

namespace exercices_demontrer
/- dEAduction
pretty_name = "Limite d'une suite : démonstration de la définition"
-/

lemma exercise.suited1
(u : ℕ → ℝ) (H : ∀ n,  u n = (5/4:  ℝ)) :
  limit u (5/4 :  ℝ)
:=
/- dEAduction
pretty_name = "Démontrer une limite finie"
-/
begin
  todo,
end

lemma exercise.suited2 
(u : ℕ → ℝ) (H : ∀ n,  u n = (n: ℝ)/2+1) (Archimedien : ∀ x : ℝ, ∃ N : ℕ, (x <(N : ℝ)) ) 
(Inegalite : ∀ n : ℕ, ∀ m: ℕ, n ≤ m →( (n : ℝ)/2 ≤  (m : ℝ)/2) ):
 limit_plus_infinity u
:=
/- dEAduction
pretty_name = "Démontrer une limite infinie"
-/
begin
  todo,
end




lemma exercise.limit_constante 
(u : ℕ → ℝ) (c : ℝ) (H : ∀ n, u n = c) :
converging_seq u :=
/- dEAduction
pretty_name = "La limite d'une suite constante"
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
pretty_name = "La limite d'une suite particulière"
description = """
  Trouverez vous la limite ?
"""
-/
begin
  todo,
end


end exercices_demontrer

namespace exercices_utiliser_demontrer
/- dEAduction
pretty_name = "Utiliser ET démontrer une limite"
-/



lemma exercise.suiteud1
(u  : ℕ → ℝ) (H1 : limit u (2 :  ℝ)) :
 limit  (λn, -u n ) (-2 :  ℝ)
:=
/- dEAduction
pretty_name = "Utilisation, et démonstration de la définition d'une limite finie - 1"
-/
begin
  todo,
end

lemma exercise.suiteud2
(u v : ℕ → ℝ) (H1 : limit u (-3 :  ℝ)) (H2 : limit v (1:  ℝ)):
 limit  (λn, u n + v n) (-2 :  ℝ)
:=
/- dEAduction
pretty_name = "Utilisation, et démonstration de la définition d'une limite finie - 2"
-/
begin
  todo,
end

end exercices_utiliser_demontrer

namespace exercices_definitions_alternatives
/- dEAduction
pretty_name = "Définitions alternatives de la limite (finie) d'une suite"
-/

lemma exercise.inegalite_large_ou_stricte
(u : ℕ → ℝ) (l : ℝ) :
(limit u l) ↔ 
∀ ε > 0, ∃ N, ∀ n ≥ N, | u n - l | ≤ ε
:=
/- dEAduction
pretty_name = "Inégalité large ou stricte dans la définition"
description = """
Peu importe si l'inégalité est large ou stricte, la définition est équivalente.
"""
-/
begin
  todo,
end


lemma exercise.couper_epsilon_en_deux
(u : ℕ → ℝ) (l : ℝ) :
(limit u l) ↔ 
∀ ε > 0, ∃ N, ∀ n ≥ N, | u n - l | < 2*ε
:=
/- dEAduction
pretty_name = "Couper les epsilons en deux"
description = """
Il est souvent utile, en analyse, de couper les epsilon en deux, ou alors,
de façon équivalente, de se ramener à 2*ε.
"""
-/
begin
  todo,
end


lemma exercise.couper_epsilon_en_100
(u : ℕ → ℝ) (l : ℝ) :
(limit u l) ↔ 
∀ ε > 0, ∃ N, ∀ n ≥ N, | u n - l | < 100*ε
:=
/- dEAduction
pretty_name = "Couper les epsilons en cent !"
description = """
Simple variante du précédent,
  pour voir si vous avez compris...
"""
-/
begin
  todo,
end


end exercices_definitions_alternatives




end course
