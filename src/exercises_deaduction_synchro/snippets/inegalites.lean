import tactic
import data.real.basic
-- import data.set
/-
- nom des variables dans la def de limite !
- variables muettes = variables globales : bof
- calcul avec abs : abs (l'-l) /2 >0 ??
(x ≠ 0 → |x| >0)
- ne pas ajouter l'inégalité au contexte si elle y est déjà !
- 'dsimp only at h' effectue les beta-réduction : (λ x, f x) 37 = f 37
- max : def et propriétés
- utiliser specialize ??

-/


-- dEAduction tactics
import structures2      -- hypo_analysis, targets_analysis
import utils            -- no_meta_vars
import user_notations   -- notations that can be used in deaduction UI for a new object
import compute_all
import push_neg_once    -- pushing negation just one step

-- dEAduction definitions
import set_definitions
import real_definitions


-- class real_number_subgroup (α : Type) := 
-- (subgroup : ((α = ℕ) ∨ (α = ℤ) ∨ (α = ℚ) ∨ (α = ℝ)) )

-- lemma real_number_subgroup_nat : (nat = ℕ) ∨ (nat = ℤ) ∨ (nat = ℚ) ∨ (nat = ℝ) :=
-- begin
--   left, refl,
-- end

-- instance : real_number_subgroup nat := ⟨real_number_subgroup_nat⟩ 


local attribute [instance] classical.prop_decidable


/-- `l` is the limit of the sequence `a` of reals -/
definition limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | u n - l | < ε

definition converging_seq (u : ℕ → ℝ) : Prop :=
∃ l, limit u l

definition limit_plus_infinity (u : ℕ → ℝ) : Prop :=
∀ M:ℝ, ∃ N:ℕ, ∀ n ≥ N, u n ≥ M

definition increasing_seq (u : ℕ → ℝ) : Prop :=
∀ p q , p ≤ q → u p ≤ u q

definition bounded_above (u : ℕ → ℝ) : Prop :=
∃ M:ℝ, ∀ n, u n ≤ M

definition bounded_below (u : ℕ → ℝ) : Prop :=
∃ m:ℝ, ∀ n, u n ≥ m

definition bounded_sequence (u : ℕ → ℝ) : Prop :=
∃ M>0, ∀ n, | u n | ≤ M

definition even (n:ℕ) : Prop := ∃ n', n=2 * n'

definition limit_function (f : ℝ → ℝ) (a : ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ δ>0, ∀ x: ℝ, ( | x-a | < δ → | f x  - l | < ε )

definition continuous_at (f : ℝ → ℝ) (a : ℝ) : Prop :=
limit_function (λ x, f x) a (f a)

definition continuous (f: ℝ → ℝ) : Prop :=
∀ a, continuous_at f a

definition cauchy (u: ℕ → ℝ) : Prop :=
∀ ε>0, ∃ N: ℕ, ∀ p≥N, ∀ q≥N, |u p - u q | < ε

definition uniformly_continuous (f: ℝ → ℝ) : Prop :=
∀ ε>0, ∃ δ>0, ∀ x y: ℝ,
(|x - y| < δ → |f x - f y | < ε)

section course
open tactic.interactive
-- notation `|` x `|` := abs x

-----------------
-- definitions --
-----------------
namespace definitions
/- dEAduction
PrettyName
  Définitions
-/


namespace generalites
/- dEAduction
PrettyName
  Généralités
-/

/-
abs_pos : 0 < |a| ↔ a ≠ 0
abs_mul x y : |x * y| = |x| * |y|
abs_add x y : |x + y| ≤ |x| + |y|
-/

/-
Max :
def
max ≥ n et n'
1) We will be using `max` a lot in this workshop. `max A B` is
the max of `A` and `B`. `max` is a definition, not a theorem, so 
that means that there will be an API associated with it, i.e. 
a list of little theorems which make `max` possible to use.
We just saw the two important theorems which we'll be using:
`le_max_left A B : A ≤ max A B` and
`le_max-right A B : B ≤ max A B`.
There are other cool functions in the `max` API, for example
`max_le : A ≤ C → B ≤ C → max A B ≤ C`. The easiest way to 
find your way around the `max` API is to *guess* what the names
of the theorems are! For example what do you think 
`max A B < C ↔ A < C ∧ B < C` is called?
-/



----------------------------------
namespace maximum
-- The name RealSubGroup will be replaced by ℝ in d∃∀duction, 
-- but allows to treat the cases of integers or rationals.
variables {RealSubGroup : Type} [decidable_linear_order RealSubGroup] 

lemma definition.max (a b c : RealSubGroup) :
a = max b c ↔ (b ≤ a ∧ c ≤ a ∧ (a=b ∨ a=c))
:=
begin
  todo
end

lemma theorem.ppe_max_gauche :
∀ a b : RealSubGroup, a ≤ max a b :=
begin
  intros a b,
  -- hypo_analysis,
  -- norm_num, tautology,
  exact le_max_left a b,
  -- todo
end

lemma theorem.ppe_max_droite :
∀ a b : RealSubGroup,  b ≤ max a b :=
begin
  have H := @theorem.ppe_max_gauche,
  intros a b, norm_num, tautology,
  -- exact le_max_right a b,
end

lemma theorem.max_ppe
(a b c : RealSubGroup) (Ha: a ≤ c) (Hb: b ≤ c) :
max a b ≤ c :=
begin
  norm_num, tautology,
  -- exact max_le Ha Hb,
end

lemma theorem.max_pp
(a b c : RealSubGroup) (Ha: a < c) (Hb: b < c) :
max a b < c :=
begin
  norm_num, tautology,
  -- exact max_lt Ha Hb,
end

end maximum

namespace valeur_absolue
variables {RealSubGroup : Type} [decidable_linear_ordered_comm_ring RealSubGroup] 
-- [has_zero RealSubGroup]

-- A modifier : faire une classe "nombres" ?
lemma definition.valeur_absolue (a b : RealSubGroup) :
a = abs b ↔ (a ≥ 0 ∧ (a=b ∨ a=-b))
:=
begin
  todo
end

lemma theorem.valeur_absolue :
∀ x : RealSubGroup,
((0:RealSubGroup) ≤ x) → (abs x = x) and ((x ≤ 0) → (abs x = -x)) :=
begin
  intro x, split, exact abs_of_nonneg, exact abs_of_nonpos,
end

lemma theorem.majoration_valeur_absolue :
∀ x r : RealSubGroup, (abs x < r) ↔ ((-r < x) ∧ (x < r))
:= 
/- dEAduction
PrettyName
  Majoration d'une valeur absolue
-/
begin
  intros x r,
  exact abs_lt
end


lemma theorem.inegalite_triangulaire :
∀ x y : RealSubGroup, |x + y| ≤ |x| + |y|
:= 
/- dEAduction
PrettyName
  Inégalité triangulaire
-/
begin
  intros x y, exact abs_add x y 
end

lemma theorem.valeur_absolue_produit :
∀ x y : RealSubGroup,  |x * y| = |x| * |y|
:= 
/- dEAduction
PrettyName
  Valeur absolue d'un produit
-/
begin
  intros x y, exact abs_mul x y 
end

end valeur_absolue

end generalites

end definitions


-----------------
--  exercices  --
-----------------
namespace tests_inegalites
/- dEAduction
PrettyName
  Exercices pour tester le module de calcul.
-/
variables x y z t: real

lemma exercise.inegalites_1
(H1_lt: x < y) (H2_lt: t < z)
(H1_lte: x ≤ y) (H2_lte: t ≤ z):
x + t < y + z :=

begin
  todo
end

-- lemma exercise.simp0
-- (a n :ℝ) (H1: a = 1 - 1) (H2: n = 100-10) : a = 0 :=
-- begin
--   -- try {norm_num},
--   -- simp only [*],
--   -- try {simp only [] with simp_arith at H1},
--   -- assumption,
--   -- try {simp only [*]},
--   -- compute_n 10,
--   -- simp only [] with simp_arith at H2,
--   norm_num at H2,
-- end

example (a b : ℝ) (H: a + 0 = b) : a=b :=
begin
  simp only [add_zero] at H,
  assumption,
end

lemma exercise.comm1 (a b: ℝ) (H: a=b): b=a :=
begin
  -- smart_comm H, assumption,
  todo
end



lemma exercise.simp2 (x y l l': ℝ) (H: abs((x-l) + (y-l')) < 1): 
abs ((x+y) -(l+l')) < 1 :=
begin
  -- smart_triang_ineq H with H',
  -- have H' := triangular_inequality (x - l) (y - l'),
  -- todo,
  -- Sol 1:
--   have Haux : (x-l) + (y-l') = (x+y) -(l+l'), ring,
--   rw Haux at H,
--   assumption,
-- -- Sol 2:
-- rw abs_lt at H,
-- rw abs_lt,
-- split, linarith, linarith,
-- compute_n 10,
  todo
end

lemma exercise.simp3 (n: nat) (u v: nat → ℝ) (l l' ε: ℝ)
(H: abs((u n-l) + (v n -l')) < ε + ε): 
abs ((u n + v n ) -(l+l')) < 2*ε :=
begin
  -- smart_triang_ineq H with H',
  -- have H' := triangular_inequality (x - l) (y - l'),
  -- todo,
  -- Sol 1:
--   have Haux : (x-l) + (y-l') = (x+y) -(l+l'), ring,
--   rw Haux at H,
--   assumption,
-- -- Sol 2:
-- rw abs_lt at H,
-- rw abs_lt,
-- split, linarith, linarith,
-- compute_n 10,
--  have Haux0: ((u n + v n) - (l + l'))  = ((u n - l) + (v n - l')) , ring,
--  `[ rw Haux0] <|> `[ simp_rw Haux0], assumption,
  todo
end

-- #check mul_lt_mul'',

lemma exercise.ineg1 (a b c: ℝ) (H: a>0) (H': b < c) : a*b < a*c :=
begin
  -- smart_mul H H' with H'',
  todo
end


lemma exercise.ineq_triang (x y l l': ℝ) (H: abs(x-l) + abs(y-l') < 1): 
abs ((x+y) -(l+l')) < 1 :=
begin
  -- smart_triang_ineq H with H',
  -- smart_trans H H' with H'',
  -- ... ring  
  todo,
end


end tests_inegalites

end course


