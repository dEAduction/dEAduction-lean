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
    Arithmétique
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

section course

open nat
universe u

-- theorem two_step_induction {P : ℕ → Sort u} (H1 : P 0) (H2 : P 1)
--     (H3 : ∀ (n : ℕ) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : Π (a : ℕ), P a
-- | 0               := H1
-- | 1               := H2
-- | (succ (succ n)) := H3 _ (two_step_induction _) (two_step_induction _)

open set

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

end logique

namespace definitions
/- dEAduction
PrettyName
    Définitions
-/


def even (a: nat) := ∃ b, a = 2*b 

def odd (a: nat) := ∃ b, a = 2*b + 1 

def divides (a b:ℤ) := ∃ c, b = a * c


lemma theorem.induction {P: nat → Prop} (H0: P 0)
(H1: ∀ (n : ℕ) (IH1 : P n), P (n+1) ) :
∀n, P n
:=
begin
  todo
end 


lemma definition.even {a:nat} : (even a) ↔ ∃ b, a = 2*b :=
/- dEAduction
PrettyName
  Pair
ImplicitUse
  True
-/
begin
  refl
end

lemma definition.odd {a:nat} : (odd a) ↔ ∃ b, a = 2*b + 1 :=
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


lemma exercise.even_or_odd : ∀n: nat, (even n or odd n) :=
/- dEAduction
PrettyName
  Pair ou impair I
-/
begin
    -- intro n, induction n with n H1,
    -- apply induction.simple_induction,
    -- apply induction.strong_induction,
    -- rotate, intros n HR1,
    -- targets_analysis,
    -- all_goals {hypo_analysis2 2},
    todo
end

lemma exercise.even_or_odd2 : ∀n: nat, (not (even n)) ↔ odd n :=
/- dEAduction
PrettyName
  Pair ou impair II
-/
begin
    todo
end

lemma exercise.mul_divides {a b c : ℤ} : divides a b → divides a (b*c) :=
/- dEAduction
PrettyName
  Diviseurs d'un multiple
-/
begin
  todo
  -- intro H2,
  -- cases H2 with k,
  -- use (k*c),
  -- rw H2_h,
  -- cc, -- ring
end

lemma theorem.divides_one {a b : ℤ} :
a * b = 1 → (a=1 ∧ b=1) ∨ (a=-1 ∧ b=-1) :=
/- dEAduction
PrettyName
  Diviseurs de 1
-/
begin
  todo
end

lemma exercise.mutual_divisors {a b : ℤ} :
(divides a b and divides b a) → (a = b or a = -b) :=
/- dEAduction
PrettyName
  Diviseurs mutuels
-/
begin
  todo
  -- rintro ⟨H1 , H2⟩,
  -- cases H1 with d H1,
  -- cases H2 with d' H2,
  -- rw H1 at H2,
  -- by_cases a=0, rotate,
  -- have H2b : (d * d' =1),
  -- todo, todo, todo,
end

lemma exercise.carre_pair {n : ℕ} : (even n) ↔ (even (n^2)) :=
/- dEAduction
PrettyName
  Parité et carré.
-/
begin
  todo
end


end definitions

end course


