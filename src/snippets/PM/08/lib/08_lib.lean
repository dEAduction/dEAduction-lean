import «06_lib»

attribute [instance] classical.prop_decidable

namespace tactic.interactive
open tactic
/-- Une version améliorée de `linarith`. -/
meta def linarith' : tactic unit :=
do `[try { dsimp only }],
   try `[rw dans_segment at *],
   try auto.split_hyps,
   `[linarith]

meta def verifie : tactic unit :=
`[ { repeat { unfold limite_suite},
   repeat { unfold continue_en },
   push_neg,
   try { simp only [exists_prop] },
   try { exact iff.rfl },
   done } <|> fail "Ce n'est pas cela. Essayez encore." ]

end tactic.interactive
