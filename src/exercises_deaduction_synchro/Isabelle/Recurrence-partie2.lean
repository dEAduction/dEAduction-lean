/-
Feuille d'exercice pour travailler le raisonnement par récurrence sur N 
Deuxième partie
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
-- import set_definitions
-- import real_definitions

-- Use classical logic
local attribute [instance] classical.prop_decidable


/- dEAduction
title = "Démonstration par récurrence - Partie 2"
author = "Isabelle Dubois"
institution = "Université de Lorraine"
description = "Exercices sur la récurrence - Partie 2"
available_exercises = "NONE"
available_definitions = "NONE"
[settings]
logic.usr_jokers_available = false
logic.use_color_for_applied_properties = false
functionality.allow_sorry = false
functionality.allow_induction = false
functionality.calculator_available = true
others.Lean_request_method = "normal"
[display]
strictementcroissante = [-1, " est strictement croissante"]
-/


-- logic names ['and', 'or', 'not', 'implies', 'iff', 'forall', 'exists']
-- proofs names ['proof_methods', 'new_object', 'apply']
-- magic names ['compute', 'assumption']


local attribute [instance] classical.prop_decidable
---------------------------------------------
-- global parameters = implicit variables --
---------------------------------------------
section course
open nat


namespace recurrence
/- dEAduction
pretty_name = "Récurrence simple"
-/

--description = "rec simple"

lemma theorem.recurrence_simple {P: nat → Prop}  :
 (  P 0 and ( ∀ (n : nat) , P n →  P (n+1))  ) →  (∀n, P n )
:=
/- dEAduction
pretty_name = "Théorème de récurrence simple"
implicit_use = true
-/
begin
  todo
end 

lemma theorem.puissance1  : ∀ a: ℤ , ∀ n: nat, a^(n+1) = (a^n)*a :=
/- dEAduction
pretty_name = "Propriété Puissance (Entiers relatifs)"
implicit_use = true
-/
begin
  todo
end

def divides (a b:ℤ) := ∃ c, b = a * c

lemma definition.divise {a b : ℤ} : (divides a b) ↔ (∃ c, b = a * c) :=
/- dEAduction
pretty_name = "Divise"
implicit_use = true
-/
begin
  todo
end

--available_definitions = "divise"
--available_theorems = "puissance1"

lemma exercise.formule_divise {a b : ℤ} : ∀n: nat, divides (b-a) (b^n -(a)^n) :=
/- dEAduction
pretty_name = "Une relation classique de divisibilité"
description = "Une relation classique de divisibilité,  à démontrer par une récurrence simple."
available_definitions = "divise"
available_theorems = "puissance1, recurrence_simple"
-/
begin
  todo
end

lemma theorem.puissance2  : ∀ x: ℝ , ∀ n: nat, x^(n+1) = (x^n)*x :=
/- dEAduction
pretty_name = "Propriété Puissance (Réels)"
implicit_use = true
-/
begin
  todo
end


lemma theorem.utile  (r: ℝ )  (m: nat) :  0 ≤ (m :  ℝ )*r^2
 :=
/- dEAduction
pretty_name = "Le produit d'un entier par un carré est positif"
implicit_use = true
-/
begin
  todo
end



lemma auxiliary_theorem.prod_ineg_var1 (a b c: ℝ) (H: b ≤ c ):
 (0 < a) → (b*a ≤ c*a)
:=
begin
    todo
end

lemma theorem.prod_ineg (a b c : ℝ) (H: b ≤ c):
 (0 <  a) → (b*a ≤ c*a)
:=
/- dEAduction
pretty_name = "Multiplier une inégalité par un nombre strictement positif"
auxiliary_definitions = "lemmes_de_calcul.auxiliary_theorem.prod_ineg_var1"
-/
begin
    todo
end



lemma exercise.ineg_bernoulli : 
∀ x :ℝ , (0 < 1+x ) → (  ∀n: nat,   (1+n*x :ℝ )  ≤  (1+x :ℝ)^n )
 :=
/- dEAduction
pretty_name = "Inégalité de Bernoulli"
description = "Inégalité de Bernoulli,  à démontrer par récurrence. INDICATIONS : Utiliser les théorèmes sur les inégalités à disposition, puis, dans la partie Calculer (expérimental), utiliser le bouton MOINS puis le bouton Simp (dans l'hypothèse et le but)."
available_theorems = "puissance2, recurrence_simple, prod_ineg, utile"
-/
begin
  todo
end

end recurrence

namespace recurrence2
/- dEAduction
pretty_name = "Récurrence double"
-/

--(H0: P 0) (H1: P 1) (HR: ∀ n : nat , ( P n and P (n+1)) → P (n+2) )



lemma theorem.recurrence_double {P: nat → Prop}  :
 (  (P 0 and P 1) and ( ∀ (n : nat) , ( P n and P (n+1)) → P (n+2))  ) →  (∀n, P n )
:=
/- dEAduction
pretty_name = "Théorème de récurrence double"
description = "Théorème de récurrence double"
-/
begin
  todo
end 

-- available_definitions = "NONE"
-- available_theorems = "puissance1"

def strictementcroissante ( u : ℕ → ℝ )  := ∀  n : ℕ, ( u n < u (n+1))

lemma definition.suite_strictementcroissante {u}:
strictementcroissante u ↔ ∀ n, u n < u (n+1)
:=
/- dEAduction
pretty_name = "Suite strictement croissante"
implicit_use = true
-/
begin
    todo
end

lemma exercise.suite_rec_double {u : ℕ → ℝ} (H0 : u 0 = (0 : ℝ)) (H1 : u 1 = (1 : ℝ)) (H2 :  ∀n: nat, u (n+2) = (1/2)*(u n + u (n+1) ) +1 ) : 
strictementcroissante u
:=
/- dEAduction
pretty_name = "Suite définie par une récurrence double"
description = "Suite définie par une récurrence double : il faudra donc utiliser le théorème de récurrence double. INDICATIONS : Utiliser sans modération le bouton =. Aussi, dans la partie Calculer (expérimental), utiliser le bouton PLUS puis le bouton Simp (dans le but)."
available_definitions = "suite_strictementcroissante"
available_theorems = "recurrence_double"
-/
begin
    todo
end

lemma exercise.rec_double {P Q: nat → Prop}  (DefinitiondeQ :  ∀ n : nat , Q n =( P n and P (n+1))): 
( ( P 0 ) and ( P 1 ) and ( ∀ n : nat , ( P n and P (n+1)) → P (n+2) )  ) → ( ∀n: nat, P n )
:=
/- dEAduction
pretty_name = "Démonstration du théorème de récurrence double"
description = "Il s'agit de démontrer que le principe de récurrence double est valide, à partir du théorème de récurrence simple. INDICATION: démontrer par récurrence simple que Q(n) est vraie pour tout entier n."
available_theorems = "recurrence_simple"
-/
begin
    todo
end



end recurrence2

end course
