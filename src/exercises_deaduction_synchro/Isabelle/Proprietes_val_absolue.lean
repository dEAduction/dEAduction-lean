/-
Un fichier d'exercices sur les propriétés des nombres réels
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
title = "Propriétés des réels - Valeur absolue"
author = "Isabelle Dubois"
institution = "Université de Lorraine"
description = """
Des exercices sur les propriétés des réels - Valeur absolue

"""
[settings]
display.use_symbols_for_logic_button = false
logic.usr_jokers_available = false
logic.use_color_for_applied_properties = true
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



section course
open tactic.interactive
-- notation `|` x `|` := abs x

-----------------
-- definitions --
-----------------
namespace definitions
/- dEAduction
pretty_name = "Définitions de la valeur absolue"
-/




variables {RealSubGroup : Type} [decidable_linear_ordered_comm_ring RealSubGroup] 



lemma definition.valeur_absolue2
(b : RealSubGroup) :
(abs b ≥ 0 ∧ (abs b=b ∨ abs b=-b))
:=
/- dEAduction
pretty_name = "Définition générale de la valeur absolue"
-/
begin
  todo
end


lemma definition.valeur_absolue_de_positif (b : ℝ):
(0 ≤ b)   → (abs b = b) 
:=
/- dEAduction
pretty_name = "Valeur absolue d'un nombre positif"
-/
begin
  exact abs_of_nonneg,
end

lemma definition.valeur_absolue_stt_positif (b : ℝ) :
 (0 < b)   → (abs b = b) 
:=
/- dEAduction
pretty_name = "Valeur absolue d'un nombre strictement positif"
-/
begin
  todo
end

lemma definition.valeur_absolue_de_negatif (b : ℝ ) :
(b ≤ 0)  → (abs b = -b) 
:=
/- dEAduction
pretty_name = "Valeur absolue d'un nombre négatif"
-/
begin
  exact abs_of_nonpos,
end

lemma definition.valeur_absolue_stt_negatif (b : ℝ):
 (b < 0)  → (abs b = -b) 
:=
/- dEAduction
pretty_name = "Valeur absolue d'un nombre strictement négatif"
-/
begin
  exact abs_of_nonpos,
end

lemma definition.valeur_absolue_zero (b : ℝ) :
 (b = (0: ℝ))  →  (abs b = (0 : ℝ)) 
:=
/- dEAduction
pretty_name = "Valeur absolue de zéro"
-/
begin
  todo
end





end definitions


-----------------
--  exercices  --
-----------------



namespace exercices_valeur_absolue
/- dEAduction
pretty_name = "Exercices sur la valeur absolue"
-/

open definitions

open set

variables {RealSubGroup : Type} [decidable_linear_ordered_comm_ring RealSubGroup] 

lemma exercise.valeur_absolue_positive :
∀x: ℝ ,  abs (x)  ≥ 0
:=
/- dEAduction
pretty_name = "Une valeur absolue est positive"
description = "On pourra utiliser la définition générale, ou alors faire un raisonnement par cas."
-/
begin
  todo
end

lemma exercise.valeur_absolue_minoration :
∀ x : ℝ,  x  ≤|x| 
:= 
/- dEAduction
pretty_name = "Un réel est inférieur ou égal à sa valeur absolue" 
description = "On pourra utiliser la définition générale, ou alors faire un raisonnement par cas, les deux méthodes se ramenant de toute façon à un raisonnement par cas."
-/
begin
  todo
end

lemma exercise.valeur_absolue_majoration :
∀x : ℝ, ∀ M : ℝ, ((x  ≤ M) and (-x  ≤ M) ) →  ( (|x| : ℝ)≤ M )
:= 
/- dEAduction
pretty_name = "Si un réel et son opposé sont majorés par M alors sa valeur absolue aussi"
description = "On pourra utiliser la définition générale, ou alors faire un raisonnement par cas, les deux méthodes se ramenant de toute façon à un raisonnement par cas."
-/
begin
  todo
end

lemma exercise.intervalle :
∀x: ℝ , ∀a: ℝ, ∀r: ℝ, (| x - a | ≤ r )  ↔ (a-r ≤ x ) ∧  ( x ≤ a+r )
:=
/- dEAduction
pretty_name = "Valeur absolue et intervalle"
description = "On pourra utiliser l'exercice précédent pour une des implications."
-/
begin
  todo
end

lemma theorem.produit_1 (a b : ℝ):
  a*b ≥ 0 ↔ ((0 < a ∧  0 < b) ∨ ( a<0 ∧ b<0) ∨ (a=0) ∨  (b=0))
:=
/- dEAduction
pretty_name = "Produit de réels positif"
-/
begin
  todo
end

lemma theorem.produit_2 (a b : ℝ):
 a*b <0 ↔ (( a< 0∧  0 < b) ∨ ( b<0 ∧ 0<a) )
:=
/- dEAduction
pretty_name = "Produit de réels strictement négatif"
-/
begin
  todo
end

lemma theorem.produit_3 (a b : ℝ):
 a*b = 0 ↔ ((a=0) ∨ ( b=0) )
:=
/- dEAduction
pretty_name = "Produit de réels nul"
-/
begin
  todo
end

lemma exercise.valeur_absolue_produit :
∀ x : ℝ, ∀ y : ℝ,  |x * y| = |x| * |y|
:= 
/- dEAduction
pretty_name = "Valeur absolue d'un produit de réels"
description = "On pourra raisonner par cas, par exemple en commençant par x*y  ≥ 0, et en se servant de résultats mis à disposition."
-/
begin
  todo
end


lemma exercise.valeur_absolue_oppose :
∀x: ℝ ,  abs (-x) = abs (x)
:=
/- dEAduction
pretty_name = "Valeur absolue de l'opposé d'un réel"
description = "On pourra se servir du résultat de l'exercice précédent."
-/
begin
  todo
end

lemma exercise.carre_valeur_absolue :
∀x: ℝ ,  |x|^2 = x^2 
:=
/- dEAduction
pretty_name = "Carré de la valeur absolue"
description = "On pourra se servir de résultats d'exercices précédents."
-/
begin
  todo
end


lemma exercise.ineg_triangulaire  (H1 : ∀a: ℝ , ∀b: ℝ, (a+b)^2 = a^2 + 2*a*b +b^2 ) (H2 : ∀x : ℝ, ∀ y : ℝ, ((x≥ 0) and (y≥ 0) )→ ( ( x^2 ≤  y^2) →  (x ≤  y ) )) :
∀x: ℝ , ∀y: ℝ, (|x + y| : ℝ) ≤  (|x|: ℝ) + (|y| : ℝ)
:=
/- dEAduction
pretty_name = "Exercice pour démontrer l'inégalité triangulaire"
description = "On se propose d'utiliser des identités remarquables pour démontrer le résultat. Se servir également d'exercices précédents à bon escient."
-/
begin
  todo
end


lemma theorem.inegalite_triangulaire (x y : RealSubGroup):
|x + y| ≤ |x| + |y|
:= 
/- dEAduction
pretty_name = "Théorème Inégalité triangulaire"
-/
begin
  exact abs_add x y 
end

--

lemma exercise.inegalite :
∀x: ℝ , ∀y: ℝ, (| |x| - |y| | : ℝ) ≤  (|x- y| : ℝ)
:=
/- dEAduction
pretty_name = "Majoration de la valeur absolue de la différence des valeurs absolues"
description = "On pourra utiliser l'inégalité triangulaire mise à disposition, et un des exercices précédent bien choisi."
-/
begin
  todo
end



end exercices_valeur_absolue




end course



