import data.real.basic
import tactic.apply_fun

namespace tactic.interactive
setup_tactic_parser

meta def compute_at_hyp (h : name) : tactic unit :=
let lo := loc.ns [h] in
do { ring none tactic.ring.normalize_mode.horner lo <|>
norm_num [] lo <|>
abel tactic.abel.normalize_mode.term lo } ; try (simp_core {} skip ff [] [] lo)

meta def compute_at_goal : tactic unit :=
do focus (tactic.iterate_at_most 3 `[refl <|> ring <|> abel <|> norm_num])

meta def compute_at (h : option name) :=
if H : h.is_some then compute_at_hyp (option.get H) else compute_at_goal

meta def compute (l : parse location) : tactic unit :=
  match l with
  | loc.ns ll := ll.mmap' compute_at
  | loc.wildcard := tactic.local_context >>= list.mmap' (compute_at_hyp ∘ expr.local_pp_name)
  end
end tactic.interactive

notation `|`:1024 x:1 `|`:1 := abs x


lemma abs_inferieur_ssi (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y :=
abs_le

lemma abs_diff (x y : ℝ) : |x - y| = |y - x | :=
abs_sub _ _

variables {α : Type*} [decidable_linear_order α]
lemma superieur_max_ssi (p q r : α) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q :=
max_le_iff

lemma inferieur_max_gauche (p q : α) : p ≤ max p q :=
le_max_left _ _

lemma inferieur_max_droite (p q : α) : q ≤ max p q :=
le_max_right _ _

lemma egal_si_abs_diff_neg {a b : ℝ} : |a - b| ≤ 0 → a = b :=
decidable_linear_ordered_comm_group.eq_of_abs_sub_nonpos
-- Pour la lib
lemma egal_si_abs_eps (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y :=
begin
  intro h,
  apply egal_si_abs_diff_neg,
  by_contradiction H,
  push_neg at H,
  specialize h ( |x-y|/2) (by linarith),
  linarith,
end

lemma ineg_triangle (x y : ℝ) : |x + y| ≤ |x| + |y| :=
abs_add x y

def limite_suite (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

-- Fait dans la feuille 5, à mettre dans 06_lib
lemma unicite_limite {u l l'}: limite_suite u l → limite_suite u l' → l = l' :=
begin
  -- sorry
  intros hl hl',
  apply egal_si_abs_eps,
  intros ε ε_pos,
  specialize hl (ε/2) (by linarith),
  cases hl with N hN,
  specialize hl' (ε/2) (by linarith),
  cases hl' with N' hN',
  specialize hN (max N N') (inferieur_max_gauche _ _),
  specialize hN' (max N N') (inferieur_max_droite _ _),
  calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')| : by compute
  ... ≤ |l - u (max N N')| + |u (max N N') - l'| : by apply ineg_triangle
  ... =  |u (max N N') - l| + |u (max N N') - l'| : by rw abs_diff
  ... ≤ ε/2 + ε/2 : by linarith
  ... = ε : by compute,
end
