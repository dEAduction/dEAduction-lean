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
    Arithmétique - BOOK OF PROOF PART I  
Author
    Frédéric Le Roux, Thomas Richard
Institution
    Université du monde
Description
    Premier essai d'arithmétique
Display
    divise --> (-2, " | ", -1)
    puissancede2 --> (-1, " est une puissance de 2")
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

def puissancede2 (a :ℕ) := ∃ b : ℕ, a = 2^b

lemma definition.puissancede2 {a:ℕ} : (puissancede2 a) ↔ ∃ b:ℕ, a = 2^b :=
/- dEAduction
PrettyName
  Puissance de 2
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

-- exo 1 page 42 


lemma exercise.nombre_8  :
(even 8) ∧ (puissancede2 8)
 :=
/- dEAduction
PrettyName
 8 est pair et une puissance de 2 
-/
begin
  todo
end

-- exo 10 page 55
lemma exercise.il_existe_pour_tout :
 ∃  m:ℤ, ∀ n:ℤ, m=n+5
 :=
/- dEAduction
PrettyName
 Il existe suivi de Pour tout
OpenQuestion
 True
-/
begin
  todo
end

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

-- exo 9 page 55
lemma exercise.pour_tout_il_existe   :
∀ n:ℤ, ∃  m:ℤ, m=n+5
:=
/- dEAduction
PrettyName
 Pour tout suivi de Il existe 
OpenQuestion
 True
-/
begin
  todo
end




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


