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



-------------------- LOGIQUE -----------------------
section logique
lemma double_implication (P Q : Prop) : (P ↔ Q) ↔ (P → Q) ∧ (Q → P) := by tautology


end logique

