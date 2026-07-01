/-
This is a d∃∀duction file providing exercises for divisibility in Z. French version.
-/

-- Standard Lean import
import data.set
import tactic
import data.nat.basic

-- dEAduction tactics
import deaduction_all_tactics

-- dEAduction definitions
import set_definitions

-- Use classical logic
local attribute [instance] classical.prop_decidable

-------------------------
-- dEAduction METADATA --
-------------------------
/- dEAduction
title = "Arithmétique - Partie 1"
author = "Frédéric Le Roux et Isabelle Dubois"
institution = "Université du monde"
description = """
Arithmétique : exercices sur la divisibilité dans  ℤ - PARTIE 1

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
functionality.automatic_use_of_exists=false
functionality.automatic_use_of_and = true
functionality.target_selected_by_default=true
functionality.allow_implicit_use_of_definitions=true
functionality.choose_order_to_prove_conjunction=true
others.Lean_request_method = "normal"
logs.save_journal = false
-/


-- Old:
-- [display]
-- prime = [-1, " est premier"]
-- puissancede2 = [-1, " est une puissance de 2"]
-- multiple = [-2, " est multiple de ", -1]
---------------------------------------------
-- global parameters = implicit variables --
---------------------------------------------


open nat


open set


---------------------
namespace definitions
/- dEAduction
pretty_name = "Définitions"
-/

variables {IntegerSubGroup:Type} [has_add IntegerSubGroup] 
[has_one IntegerSubGroup] [has_mul IntegerSubGroup] 



def divides (a b: IntegerSubGroup) := ∃ c, b = a * c

def multiple (a b: IntegerSubGroup) := ∃ c, a = b * c




lemma definition.divides {a b : IntegerSubGroup} : (divides a b) ↔ (∃ (c: IntegerSubGroup), b = a * c) :=
/- dEAduction
pretty_name = "Divise"
implicit_use = true
-/
begin
  refl
end

lemma definition.multiple {a b : IntegerSubGroup} : (multiple a b) ↔ (∃ c, a = b * c) :=
/- dEAduction
pretty_name = "Multiple"
implicit_use = true
-/
begin
  refl
end



end definitions

open definitions



--------------------------------
namespace preuve_d_existence
/- dEAduction
pretty_name = "Preuves d'existence"
-/



lemma exercise.divise : divides 7 42 :=
/- dEAduction
pretty_name = "Sept divise quarante-deux."
-/
begin
  todo
end

lemma exercise.divise_zero : ∃ a : ℤ,  divides 0 a :=
/- dEAduction
pretty_name = "Il existe un entier divisible par zéro."
-/
begin
  todo
end

end preuve_d_existence

--------------------------------

namespace preuves_universelles
/- dEAduction
pretty_name = "Preuves d'énoncés universels"
-/

lemma exercise.diviseur_lui_meme  : ∀ {a : ℤ}, (divides a a) and (divides a (-a))  :=
/- dEAduction
pretty_name = "Tout entier est diviseur de lui-même et de son opposé."
-/
begin
  todo
end


lemma exercise.un_et_zero  : ∀ {a : ℤ}, (multiple 0 a) and (divides 1 a) :=
/- dEAduction
pretty_name = "0 est un multiple universel et 1 est un diviseur universel"
-/
begin
  todo
end


end preuves_universelles

--------------------------------
namespace preuve_par_l_absurde

lemma exercise.divisibilite_un_non_nul {a  : ℤ} :
((divides a 1))→ not (a=0 )
  :=
/- dEAduction
pretty_name = "Si a divise 1 alors a n'est pas nul"
description = "On utilisera un raisonnement par l'absurde à bon escient."
-/
begin
  todo
end


end preuve_par_l_absurde

--------------------------------


namespace but_intermediaire
/- dEAduction
pretty_name = "Utilisation d'un but intermédiaire"
-/

lemma exercise.divisibilite_inferieur {a b : ℤ} (H1 : a >0) (H2: b> 0) : 
((divides a b))→ ( a ≤  b)
  :=
/- dEAduction
pretty_name = "Si a divise b, avec a et b >0, alors a est inférieur ou égal à b."
description = "On utilisera la fonctionnalité Introduire un But intermédiaire (icône Nouvel Objet), concernant un nombre bien choisi."
-/
begin
  todo
end

lemma exercise.multiple_superieur {a b : ℤ} (H1 : 0≤ a) (H2: 0≤ b) : 
((multiple a b))→( (a=0) or ( b ≤  a))
  :=
/- dEAduction
pretty_name = "Si a est multiple de b, avec a et b positifs, alors b est inférieur ou égal à a."
description = "On combinera raisonnement par cas et la fonctionnalité Introduire un But intermédiaire."
-/
begin
  todo
end


end but_intermediaire



--------------------------------
namespace implications
/- dEAduction
pretty_name = "Implications : propriétés de la divisibilité"  
-/

variables {IntegerSubGroup:Type} [has_add IntegerSubGroup] 
[has_one IntegerSubGroup] [has_mul IntegerSubGroup] 

lemma exercise.divise_transitive (a b c : ℤ) :
(divides a b) ∧ (divides b c) → (divides a c) :=
/- dEAduction
pretty_name = "La divisibilité est transitive"  
-/
begin
  todo
end


lemma exercise.mul_divides  : ∀ {a b c : ℤ}, ((divides a b) ∧ (multiple c b)  ) → divides a c :=
/- dEAduction
pretty_name = "Diviseur et multiple"
-/
begin
  todo
end



lemma exercise.divisibilite_somme {a b c  : ℤ} :
((divides a b) ∧ (divides a c))→ (divides a (b+c) )
  :=
/- dEAduction
pretty_name = "Si a divise b et c, alors a divise (b+c)"
-/
begin
  todo
end


lemma exercise.divisibilite_produit {a b c d : ℤ} :
((divides a b) ∧ (divides c d))→ (divides (a*c) (b*d) )
  :=
/- dEAduction
pretty_name = "Si a divise b et c divise d, alors ac divise bd"
-/
begin
  todo
end


lemma exercise.divisibilite_combinaison_lineaire {a b d : ℤ} :
∀ {u v : ℤ}, ((divides d a) ∧ (divides d b))→ (divides (d) (a*u+b*v) )
  :=
/- dEAduction
pretty_name = "Si d divise a et b, alors d divise toute combinaison linéaire de a et b"
-/
begin
  todo
end

-- exo 7 page 126
lemma exercise.divisibilite_carres {a b   : ℤ} :
((divides a b) )→ (divides (a^2) (b^2) )
  :=
/- dEAduction
pretty_name = "Si a divise b, alors a^2 divise b^2"
-/
begin
  todo
end



end implications


