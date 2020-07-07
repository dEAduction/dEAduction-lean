
import tactic
import data.real.basic
import data.set
import data.set.lattice
import logics
import definitions


set_option trace.simplify.rewrite true
-- set_option pp.all true


------------- Lemmes définitionnels ---------------
namespace definitions


------------------ Numbers -------------------
section numbers
lemma minimum (a b m :ℝ) : m = min a b ↔ (m=a ∨ m=b) ∧ m ≤ a ∧ m ≤ b := 
begin
by_cases a ≤ b,
    simp only [h, min_eq_left],
    split, intro H, rw H, finish,
    finish,
    
push_neg at h, 
have H : min a b = b, by exact min_eq_right_of_lt h,
rw H,
    split,
    intro H', split, 
        finish,
    rw H', split, linarith only [h], 
    exact le_refl b,
rintro ⟨ H1, H2, H3 ⟩,
cases H1 with Ha Hb,
    exfalso, 
    rw Ha at H3,
    linarith only [h, H3],
assumption
end


end numbers


end definitions

