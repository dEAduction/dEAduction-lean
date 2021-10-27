import tactic.linarith


/- Tactique écrite par Mario, qui aojute au contexte que les carrés sont positifs
et que les produits de nb positifs sont positifs avant d'essayer linarith
AFER : ajouter les inverses de positifs
-/


namespace tactic

meta def find_squares : expr → tactic unit
| e@`(%%a ^ 2) := do
  find_squares a,
  try (do
    p ← mk_app ``pow_two_nonneg [a],
    t ← infer_type p,
    assertv `h t p) >> skip
| e := () <$ e.traverse (λ e, e <$ find_squares e)

meta def nra : tactic unit :=
do ls ← local_context,
  ls' ← ls.mfoldr (λ h l, do
    t ← infer_type h,
    find_squares t,
    match t with
    | `(0 ≤ %%a) := return (h :: l)
    | _ := return l
    end) [],
  target >>= find_squares,
  ls'.mmap' (λ a, ls'.mmap' $ λ b, do
    p ← mk_app ``mul_nonneg [a, b],
    t ← infer_type p,
    assertv `h t p),
  tactic.interactive.linarith none none none

example {α:Type} [linear_ordered_comm_ring α] (a b : α) : 0 ≤ a ^ 2 + b ^ 2 := by nra
end tactic

