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
    Arithmétique - BOOK OF PROOF PART II - Chapitre 6 
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
/- dEAduction
PrettyName
  Preuves par cas
-/
-- lemma exercise.  :
--  :=
-- /- dEAduction
-- PrettyName
  
-- -/  
-- begin
--   todo  
-- end



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


-- exo 2 page 144 -- raisonnement par l'absurde à utiliser
lemma exercise.parite_carre {a  : ℤ} (H: even (a^2) ) :
(even a )
  :=
/- dEAduction
PrettyName
 Si a^2 est pair, alors a est pair 
-/
begin
  todo
end

-- proposition page 141 -- raisonnement par l'absurde à utiliser
lemma exercise.imparite_carre {a  : ℤ} (H: odd (a^2) ) :
(odd a )
  :=
/- dEAduction
PrettyName
 Si a^2 est impair, alors a est impair
-/
begin
  todo
end

-- proposition page 142 
lemma exercise.divisibilite_superieur_2 {a b : ℤ} (H: a >= 2 ) :
(not(divides a b)) ∨ (not( divides a (b+1) ))
  :=
/- dEAduction
PrettyName
 Si a>=2 et b est un entier, alors a divise b ou a divise (b+1)
-/
begin
  todo
end

-- exo 15 page 144
lemma exercise.condition_nul {a  : ℤ} (H: ∀b, (b>0) → (not(divides a b)) ) :
a=0
  :=
/- dEAduction
PrettyName
 Si a est un entier relatif qui ne divise aucun entier strictement positif, alors a est nul
-/
begin
  todo
end





-- exo 10 page 144 
lemma exercise.relation_fausse_1 {a b : ℤ}  :
not ( ∃a, ∃b, 21*a+30*b=1)
:=
/- dEAduction
PrettyName
 Il n'existe pas d'entiers a et b tels que 21a+30b=1
-/
begin
  todo
end

-- exo 11 page 144 
lemma exercise.relation_fausse_2 {a b : ℤ}  :
not ( ∃a, ∃b, 18*a+6*b=1)
:=
/- dEAduction
PrettyName
 Il n'existe pas d'entiers a et b tels que 18a+6b=1
-/
begin
  todo
end

-- exo 17 page 144
lemma exercise.non_divisible_par_4 {a  : ℤ} :
∀a, (not(divides 4 (a^2+2))) 

:=
/- dEAduction
PrettyName
 Aucun entier de la forme a^2+2 n'est divisible par 4 -- Utiliser exo carré pair implique entier pair
-/
begin
  todo
end

-- A PARTIR DE LA, FASTIDIEUX POUR TOUT LE CALCUL ALGEBRIQUE

-- exo 6 page 144
lemma exercise.expression_carre_non_nulle1 {a b : ℤ} :
not(a^2-4*b-2=0) 

:=
/- dEAduction
PrettyName
 L'entier a^2-4b-2 n'est jamais nul  -- Utiliser exo carré pair implique entier pair
-/
begin
  todo
end

-- exo 7 page 144
lemma exercise.expression_carre_non_nulle2 {a b : ℤ} :
not(a^2-4*b-3=0) 

:=
/- dEAduction
PrettyName
 L'entier a^2-4b-3 n'est jamais nul  -- Utiliser exo carré impair implique entier impair
-/
begin
  todo
end






-- exo 18 page 144 -- trop compliqué ?
lemma exercise.divisible_par_4_tous_deux_impairs {a b : ℤ} :
(divides 4 (a^2+b^2))   → (not ((odd a)  ∧ (odd b)))

:=
/- dEAduction
PrettyName
 Si 4 divise a^2+b^2, alors a et b ne sont pas tous deux impairs 
-/
begin
  todo
end

-- exo 8 page 144 -- semble et difficile et long --
lemma exercise.parite_triplet_pythagoricien {a b c : ℤ} (H: a^2+b^2=c^2 ) :
(even a) ∨ (even b)
:=
/- dEAduction
PrettyName
 Si a^2+b^2=c^2, alors a est pair ou b est pair
-/
begin
  todo
end


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


