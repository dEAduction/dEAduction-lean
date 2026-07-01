/-
Feuille d'exercice pour travailler les applications sur les ensembles - Exercices classiques
-/

-- Lean standard imports
import tactic
import data.real.basic
import data.set


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
--import real_definitions

-- Use classical logic
local attribute [instance] classical.prop_decidable





-------------------------
-- dEAduction METADATA --
-------------------------


/- dEAduction
title = "Théorie des ensembles : applications"
author = "Isabelle Dubois"
institution = "Université de Lorraine"
description = """
Cette feuille d'exercices concerne la théorie "élémentaire" des ensembles, partie Applications : Injectivité, surjectivité, bijectivité. Une première partie est un vrai/faux portant sur des applications explicites, puis les deux autres parties sont des exercices théoriques standards.
"""
available_exercises = "NONE"
available_compute = "NONE"
[settings]
logic.usr_jokers_available = false
logic.use_color_for_applied_properties = false
functionality.allow_induction = false
functionality.calculator_available = true
others.Lean_request_method = "normal"
-/

local attribute [instance] classical.prop_decidable

---------------------------------------------
-- global parameters = implicit variables --
---------------------------------------------
section course
parameters {X Y Z: Type}


open set




------------------------
-- COURSE DEFINITIONS --
------------------------

variables  {A A': set X}
variables {f: X → Y} {B B': set Y}
variables {I : index_set} {E : set_family I X} {F : set_family I Y}
variables (g : Y → Z) (h : X → Z)


namespace injection_surjection
/- dEAduction
pretty_name = "Applications : injectivité, surjectivité, bijectivité"
-/

lemma definition.injectivite :
injective f ↔ ∀ x y : X, (f x = f y → x = y)
:=
/- dEAduction
pretty_name = "Application injective"
implicit_use = true
-/
begin
    refl,
end

lemma definition.surjectivite :
surjective f ↔ ∀ y : Y, ∃ x : X, y = f x
:=
/- dEAduction
pretty_name = "Application surjective"
implicit_use = true
-/
begin
    refl,
end



lemma definition.bijectivite_1 :
bijective f ↔ (injective f ∧ surjective f)
:=
/- dEAduction
pretty_name = "Application bijective (première définition)"
-/
begin
    todo
end

lemma definition.bijectivite_2 :
bijective f ↔ ∀ y : Y, exists_unique (λ x, y = f x)
:=
/- dEAduction
pretty_name = "Application bijective (seconde définition)"
-/
begin
    refl,
end

-- A bouger, mais à enlever de tous les exos où ça ne sert pas !
lemma definition.existe_un_unique
(P : X → Prop) :
(∃! (λx,  P x)) ↔  (∃ x : X, (P x ∧ (∀ x' : X, P x' → x' = x)))
:=
/- dEAduction
pretty_name = "∃! : existence et unicité"
-/
begin
    todo
end

end injection_surjection




namespace injectivite_surjectivite_bijectivite
/- dEAduction
pretty_name = "VRAI/FAUX : Injectivité, surjectivité, bijectivité d'une application"
-/

--open definitions


---------------
-- EXERCICES --
---------------




lemma exercise.inj_nplus1  :
injective (λ (n:ℕ) , n+1)
:=
/- dEAduction
description = "La fonction f : ℕ → ℕ, f(n) = n+1, est-elle injective ?"
pretty_name = "Injectivité de f(n) = n+1 - Entiers naturels"
open_question = true
-/
begin
    todo
end

lemma exercise.surj_nplus1  :
surjective (λ (n:ℕ) , n+1)
:=
/- dEAduction
description = "La fonction f : ℕ → ℕ, f(n) = n+1, est-elle surjective ?"
pretty_name = "Surjectivité de f(n) = n+1 - Entiers naturels"
open_question = true
-/
begin
    todo
end

lemma exercise.bij_nplus1 :
bijective (λ (n:ℕ) , n+1)
:=
/- dEAduction
description = "La fonction f : ℕ → ℕ, f(x) = n+1, est-elle bijective ?"
pretty_name = "Bijectivité de f(n) = n+1 - Entiers naturels"
open_question = true
-/
begin
    todo
end


lemma exercise.bij_kplus1 :
bijective (λ (k :ℤ) , k+1)
:=
/- dEAduction
description = "La fonction f : ℤ → ℤ, f(k) = k+1, est-elle bijective ?"
pretty_name = "Bijectivité de f(k) = k+1 - Entiers relatifs"
open_question = true
-/
begin
    todo
end

lemma exercise.inj_pol  :
injective (λ (x : ℝ ) , 2*x^2 +3)
:=
/- dEAduction
description = "La fonction f : ℝ  → ℝ , f(x) = 2*x^2 +3, est-elle injective ?"
pretty_name = "Injectivité de  f(x) = 2*x^2 +3 - Réels"
open_question = true
-/
begin
    todo
end

lemma exercise.surj_pol  :
surjective (λ (x : ℝ ) , 2*x^2 +3)
:=
/- dEAduction
description = "La fonction f : ℝ  → ℝ , f(x) = 2*x^2 +3, est-elle surjective ?"
pretty_name = "Surjectivité de  f(x) = 2*x^2 +3 - Réels"
open_question = true
-/
begin
    todo
end

lemma exercise.bij_pol  :
bijective (λ (x : ℝ ) , 2*x^2 +3)
:=
/- dEAduction
description = "La fonction f : ℝ  → ℝ , f(x) = 2*x^2 +3, est-elle bijective ?"
pretty_name = "Bijectivité de  f(x) = 2*x^2 +3 - Réels"
open_question = true
-/
begin
    todo
end


end injectivite_surjectivite_bijectivite


namespace generalites_applications
/- dEAduction
pretty_name = "Définitions concernant les applications"
-/


lemma definition.composition {x:X}:
 function.comp g f x = g (f x)
:=
begin
   refl,
end

lemma definition.egalite_fonctions (f' : X → Y) :
f = f' ↔ ∀ x, f x = f' x :=
/- dEAduction
pretty_name = "Egalité de deux fonctions"
-/
begin
    exact function.funext_iff,
end


end generalites_applications

---------------
-- SECTION 2 --
---------------

namespace inj_surj
/- dEAduction
pretty_name = "Applications injectives, surjectives, bijectives et composition"
-/
open generalites
open generalites.generalites_ensembles
open generalites.injection_surjection
open generalites.generalites_applications

-- variables {A B C : set X}
variables  {A A': set X}
variables {f: X → Y} {B B': set Y}
variables {I : index_set} {E : set_family I X} {F : set_family I Y}
variables (g : Y → Z) (h : X → Z)

lemma exercise.composition_injections
(H1 : injective f) (H2 : injective g)
:
injective (function.comp g f)
:=
/- dEAduction
pretty_name = "Composition d'injections"
-/
begin
    todo
end

lemma exercise.composition_surjections
(H1 : surjective f) (H2 : surjective g) :
surjective (function.comp g f)
:=
/- dEAduction
pretty_name = "Composition de surjections"
-/
begin
    todo
end

lemma exercise.injective_si_compo_injective
(H1 : injective (function.comp g f)) :
injective f
:=
/- dEAduction
pretty_name = "Injective si composition injective"
-/
begin
    todo
end

lemma exercise.surjective_si_compo_surjective
(H1 : surjective (function.comp g f)) :
surjective g
:=
/- dEAduction
pretty_name = "Surjective si composition surjective"
-/
begin
    todo
end

lemma exercise.surjective_si_inj_et_compo_surjective
(H1 : surjective (function.comp g f)) (H2 : injective g) :
surjective f
:=
/- dEAduction
pretty_name = "f surjective si g injective et  g∘f surjective"
-/
begin
    todo
end

lemma exercise.injective_si_surj_et_compo_injective
(H1 : injective (function.comp g f)) (H2 : surjective f) :
injective g
:=
/- dEAduction
pretty_name = "g injective si f surjective et  g∘f injective"
-/
begin
    todo
end

lemma exercise.comp_comp_f {f : X → X}
(H : f= function.comp (function.comp f f) f )  :
injective f ↔  surjective f
:=
/- dEAduction
pretty_name = "Si f∘f∘f=f alors injectivité équivaut surjectivité"
-/
begin
    todo
end
end inj_surj

namespace images
/- dEAduction
pretty_name = "Définitions image directe et réciproque"
-/


lemma definition.image_directe (y : Y) : y ∈ f '' A ↔ ∃ x : X, x ∈ A ∧  f x = y :=
begin
    todo
end

lemma definition.image_reciproque (x:X) : x ∈ f  ⁻¹' B ↔ f(x) ∈ B :=
begin
    todo
end

end images

namespace generalites_ensembles
/- dEAduction
pretty_name = "Définitions concernant les ensembles"
-/

lemma definition.inclusion {A B : set X} : A ⊆ B ↔ ∀ {x:X}, x ∈ A → x ∈ B :=
/- dEAduction
implicit_use = true
-/
begin
    todo
end

lemma definition.egalite_deux_ensembles {A A' : set X} :
(A = A') ↔ ( ∀ x, x ∈ A ↔ x ∈ A' ) :=
/- dEAduction
pretty_name = "Egalité de deux ensembles"
implicit_use = true
-/
begin
     todo
end
lemma definition.intersection_deux_ensembles {A B : set X} {x : X} :
x ∈ A ∩ B ↔ ( x ∈ A ∧ x ∈ B) :=
/- dEAduction
pretty_name = "Intersection de deux ensembles"
implicit_use = true
-/
begin
    exact iff.rfl
end



lemma definition.union_deux_ensembles  {A : set X} {B : set X} {x : X} :
x ∈ A ∪ B ↔ ( x ∈ A ∨ x ∈ B) :=
/- dEAduction
pretty_name = "Union de deux ensembles"
implicit_use = true
-/
begin
    exact iff.rfl
end


lemma definition.singleton {X : Type} {x y : X}: x ∈ ({y} : set X) ↔ x = y
:=
/- dEAduction
pretty_name = "Ensemble singleton"
-/
begin
    todo
end

lemma definition.complement {A : set X} {x : X} : x ∈ set.compl A ↔ x ∉ A :=
/- dEAduction
pretty_name = "Ensemble complémentaire"
-/
begin
    finish
end


end generalites_ensembles

namespace inj_ens
/- dEAduction
pretty_name = "Caractérisations à l'aide des images directes et réciproque"
-/


lemma exercise.caracterisation_surj  :
surjective f ↔ ∀ B : set Y, f '' ( (f ⁻¹' B) ) = B
:=
/- dEAduction
pretty_name = "Caractérisation de la surjectivité par image de l'image réciproque"
-/
begin
    todo
end

lemma exercise.caracterisation_inj1  :
injective f ↔ ∀ A : set X, f ⁻¹' ( f '' A ) = A
:=
/- dEAduction
pretty_name = "Caractérisation de l'injectivité par image réciproque de l'image"
-/
begin
    todo
end

lemma exercise.caracterisation_inj2  :
injective f ↔ ∀ A  : set X, ∀ A' : set X,  f '' (A∩A') = (f '' A) ∩ (f ''  A')
:=
/- dEAduction
pretty_name = "Caractérisation de l'injectivité par image d'une intersection"
-/
begin
    todo
end

lemma exercise.bij_comp {f: X → Y} :
bijective f → ∀ A : set X, f '' ( set.compl A ) = ( set.compl (f '' A) )
:=
/- dEAduction
pretty_name = "Bijectivité et image du complémentaire"
-/
begin
    todo
end

end inj_ens


end course
