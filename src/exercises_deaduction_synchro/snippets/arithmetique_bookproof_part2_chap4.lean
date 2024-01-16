/-
This is a d∃∀duction file providing exercises for sets and maps. French version.
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
Title
    Arithmétique - BOOK OF PROOF PART II - Chapitre 4 
Author
    Frédéric Le Roux, Thomas Richard
Institution
    Université du monde
Description
    Premier essai d'arithmétique
Display
    divise --> (-2, " | ", -1)
   
-/

---------------------------------------------
-- global parameters = implicit variables --
---------------------------------------------


open nat
universe u

-- theorem two_step_induction {P : ℕ → Sort u} (H1 : P 0) (H2 : P 1)
--     (H3 : ∀ (n : ℕ) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : Π (a : ℕ), P a
-- | 0               := H1
-- | 1               := H2
-- | (succ (succ n)) := H3 _ (two_step_induction _) (two_step_induction _)

open set

-----------------
namespace logique

lemma definition.iff {P Q : Prop} : (P ↔ Q) ↔ ((P → Q) ∧ (Q → P)) :=
/- dEAduction
PrettyName
    Equivalence logique
-/
begin
  exact iff_def,
end

lemma theorem.disjonction_eqv_implication (P Q: Prop) :
(P ∨ Q) ↔ ((not P) → Q)
:= 
/- dEAduction
PrettyName
    Disjonction sous forme d'implication
-/
begin
  tautology,
end

lemma theorem.induction {P: nat → Prop} (H0: P 0)
(H1: ∀ (n : ℕ) (IH1 : P n), P (n+1) ) :
∀n, P n
:=
begin
  todo
end 

end logique

---------------------
namespace definitions
/- dEAduction
PrettyName
    Définitions
-/

def even (a: ℤ) := ∃ b, a = 2*b 

def odd (a: ℤ) := ∃ b, a = 2*b + 1 

def divides (a b:ℤ) := ∃ c, b = a * c

lemma definition.even {a:ℤ} : (even a) ↔ ∃ b, a = 2*b :=
/- dEAduction
PrettyName
  Pair
ImplicitUse
  True
-/
begin
  refl
end

lemma definition.odd {a:ℤ} : (odd a) ↔ ∃ b, a = 2*b + 1 :=
/- dEAduction
PrettyName
  Impair
ImplicitUse
  True
-/
begin
  refl
end

lemma theorem.not_odd {a:ℤ} : (not (odd a)) ↔ (even a ) :=
/- dEAduction
PrettyName
  Non Impair équivalent à Pair
ImplicitUse
  True
-/
begin
  refl
end

lemma theorem.not_even {a:ℤ} : (not (even a)) ↔ (odd a) :=
/- dEAduction
PrettyName
  Non Pair équivalent à Impair
ImplicitUse
  True
-/
begin
  refl
end

lemma definition.divides {a b : ℤ} : (divides a b) ↔ (∃ c, b = a * c) :=
/- dEAduction
PrettyName
  Divise
ImplicitUse
  True
-/
begin
  refl
end




end definitions

open definitions

/- PLAN

I - construction des symboles logiques

  - ∃ 
  - →
  - ∀
  - ↔  
  - ∧
  - ∨

II - Utilisation des symboles
  - ∧
  - ∃
  - → 
  - ∀

III - Types de preuves
  - Par cas ; utilisation du ∨ ; wlog
  - Contraposée
  - Absurde



-/
--------------------------------
namespace provisoirement_non_classes
/- dEAduction
PrettyName
  Exos à classer
-/

-- lemma exercise.  :
--  :=
-- /- dEAduction
-- PrettyName
  
-- -/
-- begin
--   todo
-- end



end provisoirement_non_classes


--------------------------------
namespace preuve_d_existence
/- dEAduction
PrettyName
  Preuves d'existence
-/

-- exo 26 page 127
lemma exercise.impair_difference_carres {a  : ℤ} :
(odd a)→ ( ∃b, ∃c, a = b^2 -c^2 )
  :=
/- dEAduction
PrettyName
 Si a impair, alors a est la différence de deux carrés d'entiers
-/
begin
  todo
end


end preuve_d_existence



--------------------------------
namespace implications
/- dEAduction
PrettyName
  Preuves d'implications
-/

-- exo 3 page 126
lemma exercise.expression_impaire {a  : ℤ} :
(odd a)→ (odd (a^2 +3*a+5) )
  :=
/- dEAduction
PrettyName
 Si a impair, alors a^2+3a+5 est impair
-/
begin
  todo
end

-- exo 6 page 126
lemma exercise.divisibilite_somme {a b c  : ℤ} :
((divides a b) ∧ (divides a c))→ (divides a (b+c) )
  :=
/- dEAduction
PrettyName
 Si a divise b et c, alors a divise (b+c)
-/
begin
  todo
end

-- exo 7 page 126
lemma exercise.divisibilite_carres {a b   : ℤ} :
((divides a b) )→ (divides (a^2) (b^2) )
  :=
/- dEAduction
PrettyName
 Si a divise b, alors a^2 divise b^2
-/
begin
  todo
end

-- exo 11 page 126
lemma exercise.divisibilite_produit {a b c d : ℤ} :
((divides a b) ∧ (divides c d))→ (divides (a*c) (b*d) )
  :=
/- dEAduction
PrettyName
 Si a divise b et c divise d, alors ac divise bd
-/
begin
  todo
end

-- exo 10 page 126
lemma exercise.divisibilite_expression {a b : ℤ} :
((divides a b))→ (divides a (3*b^3-b^2+5*b) )
  :=
/- dEAduction
PrettyName
 Si a divise b, alors a divise 3*b^3-b^2+5*b
-/
begin
  todo
end

end implications


--------------------------------
namespace preuves_universelles
/- dEAduction
PrettyName
  Preuves d'énoncés universels
-/




end preuves_universelles

--------------------------------
namespace preuve_par_cas

-- lemma exercise.  :
--  :=
-- /- dEAduction
-- PrettyName
  
-- -/  
-- begin
--   todo  
-- end

-- exo 14 page 126
lemma exercise.expression_impaire {n  : ℤ} :
odd (5*n^2+3*n+7)
  :=
/- dEAduction
PrettyName
 L'entier 5n^2+3n+7 est toujours impair
-/
begin
  todo
end

-- exo 15 page 126
lemma exercise.expression_paire {n  : ℤ} :
even (n^2+3*n+4)
  :=
/- dEAduction
PrettyName
 L'entier n^2+3n+4 est toujours pair
-/
begin
  todo
end

-- exo 8 page 126
lemma exercise.divisibilite_par_5 {a  : ℤ} :
((divides 5 (2*a)) )→ (divides 5 a )
  :=
/- dEAduction
PrettyName
 Si 5 divise 2a, alors 5 divise a
-/
begin
  todo
end

-- exo 9 page 126
lemma exercise.divisibilite_par_7 {a  : ℤ} :
((divides 7 (4*a)) )→ (divides 7 a )
  :=
/- dEAduction
PrettyName
 Si 7 divise 4a, alors 7 divise a
-/
begin
  todo
end


end preuve_par_cas



--------------------------------
namespace preuves_par_contraposee
/- dEAduction
PrettyName
  Preuves par contraposée
-/


end preuves_par_contraposee

--------------------------
namespace preuve_par_absurde
/- dEAduction
PrettyName
  Preuve par l'absurde
-/



-- lemma exercise. {a b : ℤ} :
--  :=
-- /- dEAduction
-- PrettyName

-- -/
-- begin
--   todo
-- end





end preuve_par_absurde

-----------------------------
namespace equivalence_logique



end equivalence_logique


-------------------------------
namespace preuve_par_recurrence
/- dEAduction
PrettyName
  Preuve par récurrence
-/



end preuve_par_recurrence

namespace disproofs

namespace contre_exemples
/- dEAduction
PrettyName
  Contre-exemples
-/

end contre_exemples

end disproofs

namespace autres_exercices

--- exo Proposition bas page 125 -- implication, équivalence, par cas, contraposée, absurde
lemma exercise.parite_opposee_et_somme (a b:ℤ)  :
((even a) ↔ ( odd b) ) → ( odd (a+b) ) 
:=
/- dEAduction
PrettyName
  La somme de deux entiers de parité opposée est impaire
-/
begin
  todo
end

--- exo 17 page 126 -- implication, équivalence, par cas, contraposée, absurde
lemma exercise.parite_opposee_et_produit (a b:ℤ)  :
((even a) ↔ ( odd b) ) → ( even (a*b) ) 
:=
/- dEAduction
PrettyName
  Le produit de deux entiers de parité opposée est pair
-/
begin
  todo
end

--- exo 16 page 126 -- implication, équivalence, par cas, contraposée, absurde
lemma exercise.parite_identique_et_somme (a b:ℤ)  :
((even a) ↔ ( even b) ) → ( even (a*b) ) 
:=
/- dEAduction
PrettyName
  La somme de deux entiers de même parité est paire
-/
begin
  todo
end

end autres_exercices


