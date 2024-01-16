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
    Arithmétique - BOOK OF PROOF PART II - Chapitre 1  
Author
    Frédéric Le Roux, Thomas Richard
Institution
    Université du monde
Description
    Premier essai d'arithmétique
Display
    divise --> (-2, " | ", -1)
    signe_parite --> ( "[(-1)∧(", -1, ")]" )
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

-- def signe_parite (a: ℤ) : ℤ := 
constant signe_parite : ℤ → ℤ 

axiom signe_parite_pair : ∀ a:ℤ , (( even a) → ((signe_parite a) = 1 ))

lemma theorem.signe_parite_pair  :
∀ a:ℤ , (( even a) → ((signe_parite a) = 1 ))
:= 
/- dEAduction
PrettyName
   Fonction [(-1)∧(a)] vaut 1 si a pair
-/
begin
   todo
end

axiom signe_parite_impair : ∀ a:ℤ , (( odd a) → ((signe_parite a) = -1 ))

lemma theorem.signe_parite_impair  :
∀ a:ℤ , (( odd a) → ((signe_parite a) = -1 ))
:= 
/- dEAduction
PrettyName
   Fonction [(-1)∧(a)] vaut -1 si a impair
-/
begin
   todo
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

II - Types de preuves
  - Par cas ; utilisation du ∨ ; wlog
  - Contrapposée
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

--- exo Proposition bas page 124

lemma exercise.multiple_de_quatre (n:ℕ) :
divides 4 (1+(signe_parite n)*(2*n-1)) :=
/- dEAduction
PrettyName
  Des multiples de quatre - entier naturel
-/
begin
  todo
end

lemma exercise.multiple_de_quatre_bis (n:ℤ) :
divides 4 (1+(signe_parite n)*(2*n-1)) :=
/- dEAduction
PrettyName
  Des multiples de quatre - entier relatif
-/
begin
  todo
end

--- exo Proposition haut page 125
lemma exercise.multiple_de_quatre_reciproque (m:ℤ) :
(divides 4 m) →  ∃ n, (m = (1+(signe_parite n)*(2*n-1)) ) ∧  (n > 0 )   
:=
/- dEAduction
PrettyName
  Des multiples de quatre, réciproque 
-/
begin
  todo
end




end preuve_par_cas



--------------------------------
namespace preuves_par_contrapposee
/- dEAduction
PrettyName
  Preuves par contrapposée
-/


end preuves_par_contrapposee

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


end autres_exercices


