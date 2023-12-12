import tactic
import data.real.basic
import data.set


import structures2
------------
-- ESSAIS --
------------
open set

-----------
-- DEBUT --
-----------

/-- Une structure d'espace métrique sur un type X -/
class espace_metrique (X : Type) :=
(dist : X → X → ℝ)
(dist_pos : ∀ x y, dist x y ≥ 0)
(sep : ∀ x y, dist x y = 0 ↔ x = y)
(sym : ∀ x y, dist x y = dist y x)
(triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)


open espace_metrique

/-- Fonction distance avec le type en argument explicite -/
def dist' (X : Type) [espace_metrique X] : X → X → ℝ := λ x y, dist x y

notation `d` := dist
notation `d_[` X `]` := dist' X


----------------------------------------------------
section fondements
----------------------------------------------------

variables {X : Type} [espace_metrique X]

@[simp]
lemma dist_sym (x:X) (y:X) : d x y = d y x := sym x y

@[simp]
lemma dist_x_x_eq_zero  (x:X) : d x x = 0 := 
 (sep x x).2 rfl 

lemma dist_str_pos  {x:X} {y:X} : x ≠ y → d x y > 0 := 
begin
-- hypo_analysis,
-- have ddd := _inst_1.dist,
contrapose!,
intro d_neg,
have d_pos : d x y ≥ 0, from dist_pos x y,
have d_zero : d x y = 0, from antisymm d_neg d_pos,
exact iff.mp (sep x y) d_zero
end


/-- `boule x r` est la boule ouverte de centre `x` et de rayon `r` -/
def boule (x : X) (r : ℝ)  := {y | dist x y < r}

/-- appartenir à une boule équivaut à une inégalité -/
@[simp]
lemma mem_boule (x : X) (r : ℝ) (y : X) : y ∈ boule x r ↔ dist x y < r := 
iff.rfl

/-- Une boule de rayon >0 contient son centre --/
lemma centre_mem_boule (x : X) (r : ℝ) : r > 0 → x ∈ boule x r :=
begin
intro r_pos,
simpa [boule] -- simplifie et utilise l'hypothèse
end
