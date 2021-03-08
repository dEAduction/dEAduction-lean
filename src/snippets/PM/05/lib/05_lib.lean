import m114 algebra.pi_instances rename_var

lemma abs_inferieur_ssi (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y :=
abs_le

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
