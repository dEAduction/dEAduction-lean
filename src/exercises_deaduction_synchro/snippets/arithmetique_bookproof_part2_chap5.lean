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
    Arithmétique - BOOK OF PROOF PART II - Chapitre 5 
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



end preuve_d_existence



--------------------------------
namespace implications
/- dEAduction
PrettyName
  Preuves d'implications
-/






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

-- exo 17 page 136 -- raisonnement direct et par cas parite b
lemma exercise.impair_divisibilite_par_8 {a  : ℤ} :
(odd a)→ (divides 8 (a^2-1) )
  :=
/- dEAduction
PrettyName
 Si a est impair, alors 8 divise a^2-1
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

-- exo proposition page 129
lemma exercise.expression_paire_implique_impair {a  : ℤ} :
(even (7*a+9))→ (odd (a) )
:=
/- dEAduction
PrettyName
 Si 7*a+9 pair, alors a est impair - Démontrer par un raisonnement direct, puis par contraposée et comparer les deux méthodes.
-/
begin
  todo
end

-- exo 9 page 136
lemma exercise.non_divisibilite_par_3_carre {a : ℤ} :
(not (divides 3 (a^2)))→ (not (divides 3 a) ) 
:=
/- dEAduction
PrettyName
 Si 3 ne divise pas a^2, alors 3 ne divise pas a.
-/
begin
  todo
end


-- exo proposition haut page 131
lemma exercise.non_divisibilite_par_5_produit {a b : ℤ} :
(not (divides 5 (a*b)))→ (not (divides 5 a) ) ∧ (not (divides 5 b) )
:=
/- dEAduction
PrettyName
 Si 5 ne divise pas a*b, alors 5 ne divise ni a, ni b.
-/
begin
  todo
end

-- exo 10 page 136
lemma exercise.non_divisibilite_par_a_produit {a b c : ℤ} :
 (not (divides a (b*c))) → (not (divides a b) ) ∧ (not (divides a c) )
:=
/- dEAduction
PrettyName
 Si a  ne divise pas bc, alors a ne divise ni b, ni c.
-/
begin
  todo
end


-- exo 15 page 136
lemma exercise.expression_cube_paire {a  : ℤ} :
 (even (a^3-1)) → (odd a)
:=
/- dEAduction
PrettyName
 Si a^3-1 est pair, alors a est impair.
-/
begin
  todo
end

-- exo 11 page 136
lemma exercise.expressionpaire_ou {a b : ℤ} :
 (even ((a^2)*(b+3))) → (even a) ∨  (odd b )
:=
/- dEAduction
PrettyName
 Si (a^2)*(b+3) est pair, alors a est pair ou b est impair.
-/
begin
  todo
end


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
/- dEAduction
PrettyName
  Equivalence
-/

-- exo 16 page 136 
lemma exercise.somme_paire_implique_meme_parite {a b : ℤ} :
 (even (a+b)) → ( (odd a) ↔ (odd b) )
  :=
/- dEAduction
PrettyName
 Si a+b est pair, alors a et b ont même parité
-/
begin
  todo
end

-- exo 14 page 136 
lemma exercise.meme_parite_implique_parite_opposee {a b : ℤ} :
( (even a) ↔ (even b) )→ ( odd (3*a+7) ↔ even (7*b-4) )
  :=
/- dEAduction
PrettyName
 Si a et b ont même parité, alors 3a+7 et 7b-4 sont de parité opposée
-/
begin
  todo
end



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

-
end autres_exercices


