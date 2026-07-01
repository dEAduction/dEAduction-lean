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
title = "Propriétés des réels - Max,  Inf, Sup"
author = "Isabelle Dubois"
institution = "Université de Lorraine"
description = """
Des exercices sur les propriétés des réels - Maximum,  borne inférieure et supérieure

"""
available_exercises = "NONE"
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
[display]
maximum = [ " maximum ( ",-1, " ) "]
sup = [ " sup ( ",-1, " ) "]
inf = [ " inf ( ",-1, " ) "]
-/


/-- Lots of definitions -/


section course
open tactic.interactive


-----------------
-- definitions --
-----------------

open set

namespace definitions
/- dEAduction
pretty_name = "Définitions"
-/



variables {RealSubGroup : Type} [decidable_linear_ordered_comm_ring RealSubGroup] 

def maximum  ( X : set RealSubGroup) : RealSubGroup := (∀ x ∈ X, x ≤ maximum X ) ∧ (maximum X ∈ X)

lemma definition.maximum {X : set RealSubGroup} {s :RealSubGroup} :
 maximum X = s ↔ (∀ x ∈ X, x ≤ s) ∧ (s ∈ X)
:=
/- dEAduction
pretty_name = "Définition maximum d'un ensemble"
-/
begin
    todo
end

def sup ( X : set  RealSubGroup) : RealSubGroup  := (∀ x ∈ X, x ≤ sup X) ∧ (∀e >0, ∃  x ∈ X, (sup X - e < x))

lemma definition.sup {X : set  RealSubGroup} {s  : RealSubGroup }  :
sup X = s ↔ (∀ x ∈ X, x ≤ s ) ∧ (∀ e >0 , ∃  x ∈ X, (s - e < x))
:=
/- dEAduction
pretty_name = "Définition borne supérieure d'un ensemble"
-/
begin
    todo
end

def inf  ( X : set RealSubGroup ) : RealSubGroup := (∀ x ∈ X,  inf X ≤ x) ∧ (∀ e >0 , ∃  x ∈ X, (x < inf X + e ))  

lemma definition.inf {X : set RealSubGroup} {i e : RealSubGroup } :
inf X = i ↔ (∀ x ∈ X, i ≤ x ) ∧ (∀ e >0 , ∃  x ∈ X, (x < i + e))  
:=
/- dEAduction
pretty_name = "Définition borne inférieure d'un ensemble"
-/
begin
    todo
end




lemma definition.singleton {X : Type} {x y : X}: x ∈ ({y} : set X) ↔ x = y
:=
/- dEAduction
pretty_name = "Ensemble singleton"
-/
begin
    todo
end

lemma definition.ensemble_extension {X: Type}  {P : X → Prop} {x:X} :
 x ∈ {x | P x} ↔ P x
:=
/- dEAduction
pretty_name = "Ensemble défini en extension"
-/
begin
    todo
end

end definitions

namespace prop
/- dEAduction
pretty_name = "Propriétés des réels - Inverse"
-/


lemma theorem.archimedien (x :  ℝ) : ( x>0  ) → (∃ n:ℕ, (x < (n : ℝ) ) ∧ ((1 : ℝ) ≤ n ) )
:=
/- dEAduction
pretty_name = "ℝ est archimédien"
-/
begin
  todo
end


lemma theorem.propriete_inverse
(x :  ℝ):
((1 : ℝ) ≤ x) → ((0 < 1/x ) ∧ (1/x ≤ (1 : ℝ)))
:= 
/- dEAduction
pretty_name = "Inverse d'un réel plus grand que 1"
-/
begin
  todo
end


lemma theorem.inverse_2 (a : ℝ):
0 < a → (0 < (1/a))
:= 
/- dEAduction
pretty_name = "Inverse et stricte positivité"
-/
begin
  todo
end

lemma theorem.inverse_3
(x y: ℝ):
((0 < x)  ∧ (x < y)) → ((1/y) <(1/x) )
:= 
/- dEAduction
pretty_name = "Stricte décroissance de l'inverse sur les stricts positifs"
-/
begin
  todo
end


end prop


-----------------
--  exercices  --
-----------------


namespace exercices_maximum
/- dEAduction
pretty_name = "Exercices sur le maximum"
-/

open definitions
open prop

open set
variables {RealSubGroup : Type} [decidable_linear_ordered_comm_ring RealSubGroup] 




lemma exercise.essai_max (A : set ℝ) :
( A = ({1} : set  ℝ) )  → (  maximum A = ( 1 :  ℝ) )
:=
/- dEAduction
pretty_name = "Maximum d'un ensemble singleton particulier"
-/
begin
  todo
end

lemma exercise.max_singleton (A : set ℝ) (a : ℝ) :
( A = ({a} : set  ℝ) )  → ( ∃ m: ℝ, maximum A = m )
:=
/- dEAduction
pretty_name = "Maximum d'un ensemble singleton général"
-/
begin
  todo
end


lemma exercise.essai_max_ens  :
  (  maximum {x | ∃ m:ℕ, (1 ≤(m : ℝ) ) ∧ (x= 1/(m : ℝ)) } = ( 1 :  ℝ) )
:=
/- dEAduction
pretty_name = "Maximum d'un ensemble"
-/
begin
  todo
end

lemma exercise.max_prop  (A B : set ℝ) ( k m: ℝ) (H: B={x | ∃ y ∈ A, x=y-k }) :
  maximum A = m → maximum (B) = m - k 
:=
/- dEAduction
pretty_name = "Maximum et soustraction"
-/
begin
  todo
end

end exercices_maximum



namespace exercices_borne_sup
/- dEAduction
pretty_name = "Exercices sur borne supérieure et inférieure"
-/

open definitions
open prop

open set
variables {RealSubGroup : Type} [decidable_linear_ordered_comm_ring RealSubGroup] 




lemma exercise.borne_sup_1 (A : set ℝ) (a : ℝ) :
( A = ({a} : set  ℝ) )  → (  sup (A) = ( a :  ℝ) )
:=
/- dEAduction
pretty_name = "Borne supérieure d'un ensemble singleton"
-/
begin
  todo
end

lemma exercise.borne_sup_inter (I : set ℝ) (a b : ℝ) (H : a<b) :
( I = ({x | ( a ≤ x ) ∧ (x <b) } : set  ℝ) )  → ( ∃ c :ℝ,  sup (I) = ( c :  ℝ) )
:=
/- dEAduction
pretty_name = "Borne supérieure d'un intervalle"
-/
begin
  todo
end

lemma exercise.borne_sup_2  :
  (  sup {x | ∃ m:ℕ, (1 ≤(m : ℝ) ) ∧ (x= 1/(m : ℝ)) } = ( 1 :  ℝ) )
:=
/- dEAduction
pretty_name = "Borne supérieure d'un ensemble particulier"
-/
begin
  todo
end

lemma exercise.essai_inf  :
  (  inf {x | ∃ m:ℕ, (1 ≤(m : ℝ) ) ∧ (x= 1/((m : ℝ))) } = ( 0 :  ℝ) )
:=
/- dEAduction
pretty_name = "Borne  inférieure d'un ensemble particulier"
-/
begin
  todo
end

lemma exercise.sup_prop  (A B : set ℝ) ( k : ℝ) (H: B={x | ∃ y ∈ A, x=-y }) :
  sup A = k → ∃ y:ℝ, inf B = y
:=
/- dEAduction
pretty_name = "Borne supérieure/inférieure et opposé"
-/
begin
  todo
end

lemma exercise.sup_max  (A  : set ℝ) ( m : ℝ)  :
  maximum A = m → ∃ y:ℝ, sup A = y
:=
/- dEAduction
pretty_name = "Maximum et borne supérieure"
-/
begin
  todo
end


end exercices_borne_sup




end course


