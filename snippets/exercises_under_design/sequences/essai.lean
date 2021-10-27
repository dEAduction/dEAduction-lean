import tactic
import data.real.basic



-- dEAduction imports
import structures2
import compute
import utils

-- import definitions
-- import notations_definitions

-- General principles :
-- Type should be defined as parameters, in order to be implicit everywhere
-- other parameters are implicit in definitions, i.e. defined using '{}' (e.g. {A : set X} )
-- but explicit everywhere else, i.e. defined using '()' (e.g. (A : set X) )
-- each definition must be an iff statement (since it will be called with 'rw' or 'symp_rw')



local attribute [instance] classical.prop_decidable

---------------------------------------------
-- global parameters = implicit variables --
---------------------------------------------
section course



------------------
-- COURSE TITLE --
------------------
namespace maths_approfondies
/- dEAduction
PrettyName
    1M003 : mathématiques approfondies
-/


-- lemma definition.valeur_absolue
-- {a: ℝ} : |a| = if a ≤ 0 then -a else a 
-- :=
-- begin
--     todo
-- end

lemma exercise.majorer_valeur_absolue
{a b : ℝ} : abs a ≤ b ↔ -b ≤ a ∧ a ≤ b
:=
begin
  todo
  --  rw definition.valeur_absolue,
  --  split_ifs,
  --  split, 
  --  intro H, split, {compute_n 1},
  --  {compute_n 1},
  --  intro H, {compute_n 1},
  --  split, 
  --  intro H, split, compute_n 1, compute_n 1,
  --  intro H, compute_n 1,
end

lemma theorem.inegalite_triangulaire1
{a b : ℝ} : abs (a-b) ≤ abs a + abs b :=
begin
    -- simp [exercise.majorer_valeur_absolue],
    -- split,
    -- rw definition.valeur_absolue, rw definition.valeur_absolue,
    -- split_ifs,
    -- repeat {linarith},
    -- rw definition.valeur_absolue, rw definition.valeur_absolue,
    -- split_ifs,
    -- repeat {linarith},
  todo
end

lemma theorem.inegalite_triangulaire2
{a b c : ℝ} : |a-b| ≤ |a-c| + |b-c| :=
begin
  todo
    -- calc |a-b| = |a-c- (b-c)|: by ring
    --      ...   ≤ |a-c| + |b-c|: @theorem.inegalite_triangulaire1 (a-c) (b-c),
end

variables (u:ℕ → ℝ) (l: ℝ)

def limite (u:ℕ → ℝ ) (l: ℝ) := 
∀ ε > 0, ∃ N >0, ∀ n ≥ N, |u n - l| < ε 
 

lemma definition.limite :
limite u l ↔  ∀ ε > 0, ∃ n_0 >0, ∀ n ≥ n_0, |u n - l| < ε 
:=
/- dEAduction
ImplicitUse
    True
DummyVarsNames
    FromLean
-/
begin
    refl,
end

-- exo 8 a b c d
lemma exercise.plus_petit_que_tout_positif_I : 
∀x:ℝ, ((∀ ε>0, x< ε) → x ≤ 0) :=
/- dEAduction
PrettyName
    1M003 exercice 1.8 (a)
-/

begin
  todo
end

lemma exercise.unicite_limite (l': ℝ) :
(limite u l) ∧ (limite u l') → l=l'
:=
begin
  todo
end



lemma exercise.essai_suites1 :
limite (λ n, 1/(n+1)) 0 :=
begin
    todo
end

lemma exercise.essai_suites2
(f: ℝ → ℝ):
limite (λ n, f 1/(n+1)) 0 :=
begin
    todo
end

end maths_approfondies

end course
