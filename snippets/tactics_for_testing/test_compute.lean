import tactic
import data.real.basic


/- TODO: This file should be transformed into a test file for the goal! button. -/

-- dEAduction tactics
import structures2      -- hypo_analysis, targets_analysis
import utils            -- no_meta_vars
import user_notations   -- notations that can be used in deaduction UI for a new object
import compute3

-- dEAduction definitions
-- import set_definitions
import real_definitions


local attribute [instance] classical.prop_decidable

-- open tactic.interactive
open compute_lemmas -- for testing directly in VSC

-- PM tactics ! --
namespace tactic.interactive
setup_tactic_parser

meta def compute_at_hyp' (h : name) : tactic unit :=
let lo := loc.ns [h] in
do { ring none tactic.ring.normalize_mode.horner lo <|>
norm_num [] lo <|>
abel tactic.abel.normalize_mode.term lo } ; try (simp_core {} skip ff [] [] lo)

meta def compute_at_goal' : tactic unit :=
do focus (tactic.iterate_at_most 3 `[refl <|> ring <|> abel <|> norm_num] >>= list.mmap' (λ _, skip))

end tactic.interactive





------------------------------------------
section helper_lemmas

-- lemma ineq_from_non_eq {α: Type} [decidable_linear_order α] (a b : α) :
-- ¬ (a = b) ↔ (if a < b then a < b else b < a) :=
-- begin
--     todo
-- end

/- Beware that `rw ineq_from_non_eq1` does not work for `¬ a = b`. 
Use `norm_num` followed by `ineq_from_non_eq`. -/
-- lemma ineq_from_non_eq' {α: Type} [linear_order α] (a b : α) : a ≠ b ↔ (a < b ∨ b < a) :=
-- begin
--     todo
-- end

end helper_lemmas

---------------------
-- Absolute values --
---------------------
namespace absolute_value

lemma exercise.test_compute_abs1a (l l': ℝ) (H: l≠l') : 
|l-l'|/2 >0 :=
begin
  -- norm_num at *,
  compute_and_trace_code "1", -->
  -- rw ineq_from_non_eq at H,
  -- unfold abs max at *,
  -- cases_type* or, -- ?????????????????????
  -- cases H with H1 H2, 
  -- all_goals {split_ifs, linarith, linarith,},
end

lemma exercise.test_compute_abs1b (l l': ℝ) (H: ¬ (l=l')) : 
|l-l'|/2 >0 :=
begin
  -- norm_num at *,
  compute_and_trace_code "1", -->
  -- rw ineq_from_non_eq at H,
  -- unfold abs max at *,
  -- cases H with H1 H2, 
  -- all_goals {split_ifs, linarith, linarith,},
end

lemma exercise.test_compute_abs1c (l l': ℝ) (H: ¬ (l=l')) : 
|l-l'|/2 >0 :=
begin 
  compute_and_trace_code "1" -- fails: unable to use `¬ l = l'`

end




example (a b c d: ℝ) (H1: abs(a-b) >0) (H2: abs (b-a) >0) : b ≠ a :=
begin
  compute_and_trace_code "1", --> fails  TODO: pre-process with abs context lemmas
    -- unfold abs max at *, split_ifs at *,
    -- all_goals {linarith},
end

example (l l': ℝ ) (H: l ≠ l') : |l-l'| >0 :=
begin
  -- norm_num at *,
  compute_and_trace_code "1", -->
    -- WORKS:  apply abs_pos_of_ne_zero, apply sub_ne_zero_of_ne, assumption,

end

lemma theorem.inegalite_triangulaire1
{a b : ℝ} : abs (a-b) ≤ abs a + abs b :=
begin
    compute_and_trace_code "1",  -->
    -- unfold abs, unfold min max, split_ifs, linarith, linarith, linarith, linarith, linarith, linarith, tautology, linarith,
end


-----------------------------------
-- inequalities from L_1_numbers --
-----------------------------------

lemma exercise.non_equality : 10 ≠ 0 := begin norm_num, end


lemma exercise.plus_petit : ∀ n:ℕ, 0 ≤ n
:=
/- dEAduction
PrettyName
    Plus petit que tous
-/
begin
  intro n,
  norm_num,
end


lemma exercise.vraiment_plus_petit : ∀ n:ℤ, n -1 ≤ n
:=
/- dEAduction
PrettyName
    Plus petit que tous...
-/
begin
  intro n,
  compute_and_trace_code "1",
end


lemma exercise.egalite : ∀ n:ℕ, n=n
:=
/- dEAduction
PrettyName
    Tous égaux
-/
begin
    intro n, norm_num,
end


lemma exercise.egalite_2 :
∀ n:ℕ, n+10 ≠ n
:=
/- dEAduction
PrettyName
    Egaux à tous !
-/
begin
    intro n, -- norm_num at *,
    compute_and_trace_code "1",
end


lemma exercise.tres_petit :
∀ a ≥ (0:ℝ), a ≤ 0 → a = 0
:=
/- dEAduction
PrettyName
    Très petit
-/
begin
    intros a H1 H2,
    compute_and_trace_code "1",
end


lemma exercise.tres_petit_3 :
∀ a ≥ (0:ℝ), (a ≠ 0 → a/2 < a)
:=
/- dEAduction
PrettyName
    Trop compliqué !
-/
begin
    intros a H1 H2,
    -- norm_num at *,
    compute_and_trace_code "1", -->
    -- rw ineq_from_non_eq at *, cases_type* or, linarith, linarith,
end


lemma exercise.entre_deux_entiers :
∀x:ℤ, ∀y:ℤ, (x<y → x+1 ≤ y)
:=
/- dEAduction
PrettyName
    Entre deux entiers
-/
begin
  intros x y H,
  compute_and_trace_code "1", --> assumption
end


lemma exercise.entre_deux_reels :
∀x:ℝ, ∀y:ℝ, x<y → x < (x+y)/2
:=
/- dEAduction
PrettyName
    Entre deux réels
-/
begin
    intros x y H,
    compute_and_trace_code "1", --> linarith
end

end absolute_value


example (a b c: ℝ) (Ha: ¬ a=0) (Ha': a ≥ 0) (Hb : b >0) : a>0 ∧ b>0 :=
begin
  split, -- rw ineq_from_non_eq at Ha, cases Ha with Ha1 Ha2, 
  solve1 {compute_and_trace_code "1"}, -->
  solve1 {compute_and_trace_code "1"}, -->
end