/-
This is a d∃∀duction file providing exercises for sets and maps. French version.
-/

import data.set
import tactic

-- dEAduction tactics
import structures2      -- hypo_analysis, targets_analysis
import utils            -- no_meta_vars
import user_notations   -- notations that can be used in deaduction UI for a new object
import push_neg_once    -- pushing negation just one step
import compute

-- dEAduction definitions
import set_definitions

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
-/

local attribute [instance] classical.prop_decidable
---------------------------------------------
-- global parameters = implicit variables --
---------------------------------------------
section course

open set

------------------
-- COURSE TITLE --
------------------
namespace definitions
/- dEAduction
PrettyName
    Ensembles et applications
-/


def pair (a: ℕ) := ∃ b, a = 2*b 

def divise (a b:ℕ) := ∃ c, b = a * c

lemma definition.pair {a:ℕ} : (pair a) ↔ ∃ b, a = 2*b :=
/- dEAduction
ImplicitUse
  True
-/
begin
  refl
end

lemma definition.divise {a b : ℕ} : (divise a b) ↔ (∃ c, b = a * c) :=
/- dEAduction
ImplicitUse
  True
-/
begin
  refl
end

lemma exercise.mul_divise {a b c : ℕ} : divise a b → divise a (b*c) :=
begin
  intro H2,
  cases H2 with k,
  use (k*c),
  rw H2_h,
  ring,
end





end definitions

end course



