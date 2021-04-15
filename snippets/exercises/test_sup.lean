-- import data.set
import tactic
import data.real.basic



-- dEAduction imports
import structures2
import compute

-- General principles :
-- Type should be defined as parameters, in order to be implicit everywhere
-- other parameters are implicit in definitions, i.e. defined using '{}' (e.g. {A : set X} )
-- but explicit everywhere else, i.e. defined using '()' (e.g. (A : set X) )
-- each definition must be an iff statement (since it will be called with 'rw' or 'symp_rw')



---------------------
-- Course metadata --
---------------------
-- logic names ['and', 'or', 'negate', 'implicate', 'iff', 'forall', 'exists']
-- proofs names ['use_proof_methods', 'new_object', 'apply', 'assumption']
-- magic names ['compute']
-- proof methods names ['cbr', 'contrapose', 'absurdum', 'sorry']
-- Note for Python devs:
--      Any supplementary metadata will be put in the 'info' dict of each exo

/- dEAduction
Author
    Frédéric Le Roux
Institution
    Université de France
Title
    Logique et inégalités
OpenQuestion
    True
AvailableExercises
    NONE
AvailableLogic
    ALL -negate
-/

-- If OpenQuestion is True, DEAduction will ask the user if she wants to
-- prove the statement or its negation, and set the variable
-- NegateStatement accordingly
-- If NegateStatement is True, then the statement will be replaced by its
-- negation
-- AvailableExercises is set to None so that no exercise statement can be applied
-- by the user. Recommended with OpenQuestions set to True!
universe u
variable  {α : Sort u}
variables (p q : Prop)
variable  (s : α → Prop)

local attribute [instance, priority 10] classical.prop_decidable
theorem not_not_eq : (¬ ¬ p) = p := propext not_not
theorem not_and_eq : (¬ (p ∧ q)) = (¬ p ∨ ¬ q) := propext not_and_distrib
theorem not_or_eq : (¬ (p ∨ q)) = (¬ p ∧ ¬ q) := propext not_or_distrib
theorem not_forall_eq : (¬ ∀ x, s x) = (∃ x, ¬ s x) := propext not_forall
theorem not_exists_eq : (¬ ∃ x, s x) = (∀ x, ¬ s x) := propext not_exists
theorem not_implies_eq : (¬ (p → q)) = (p ∧ ¬ q) := propext not_imp

theorem classical.implies_iff_not_or : (p → q) ↔ (¬ p ∨ q) := imp_iff_not_or


theorem not_eq (a b : α) : (¬ a = b) ↔ (a ≠ b) := iff.rfl

variable  {β : Type u}
variable [linear_order β]
theorem not_le_eq (a b : β) : (¬ (a ≤ b)) = (b < a) := propext not_le
theorem not_lt_eq (a b : β) : (¬ (a < b)) = (b ≤ a) := propext not_lt



lemma prop_ex {P Q : Prop} : ( ∃ H: P, Q ) ↔ (P ∧ Q) := 
begin
    exact exists_prop
end



local attribute [instance] classical.prop_decidable

---------------------------------------------
-- global parameters = implicit variables --
---------------------------------------------
section course

notation [parsing_only] P ` and ` Q := P ∧ Q
notation [parsing_only]  P ` or ` Q := P ∨ Q
notation [parsing_only]  ` not ` P := ¬ P
notation [parsing_only]  P ` implies ` Q := P → Q
notation [parsing_only]  P ` iff ` Q := P ↔ Q

notation [parsing_only]  x ` in ` A := x ∈ A
notation [parsing_only]  A ` cap ` B := A ∩ B
notation [parsing_only]  A ` cup ` B := A ∪ B
notation [parsing_only]  A ` subset ` B := A ⊆ B
notation [parsing_only]  `emptyset` := ∅

notation [parsing_only] P ` et ` Q := P ∧ Q
notation [parsing_only]  P ` ou ` Q := P ∨ Q
notation [parsing_only]  ` non ` P := ¬ P
notation [parsing_only]  P ` implique ` Q := P → Q
notation [parsing_only]  P ` ssi ` Q := P ↔ Q

notation [parsing_only]  x ` dans ` A := x ∈ A
notation [parsing_only]  x ` appartient ` A := x ∈ A
notation [parsing_only]  A ` inter ` B := A ∩ B
notation [parsing_only]  A ` intersection ` B := A ∩ B
notation [parsing_only]  A ` union ` B := A ∪ B
notation [parsing_only]  A ` inclus ` B := A ⊆ B
notation [parsing_only]  `vide` := ∅


namespace Logique_et_nombres_reels
/- dEAduction
PrettyName
    Logique et nombres réels
-/

namespace negation
/- dEAduction
PrettyName
    Enoncés de négation
-/

lemma theorem.negation_et {P Q : Prop} :
( not (P and Q) ) ↔ ( (not P) or (not Q) )
:=
/- dEAduction
PrettyName
    Négation du 'et'
-/
begin
    exact not_and_distrib
end

lemma theorem.negation_ou {P Q : Prop} :
( not (P or Q) ) ↔ ( (not P) and (not Q) )
:=
/- dEAduction
PrettyName
    Négation du 'ou'
-/
begin
    exact not_or_distrib
end

lemma theorem.negation_non {P : Prop} :
( not not P ) ↔  P 
:=
/- dEAduction
PrettyName
    Négation du 'non'
-/
begin
    exact not_not
end


lemma theorem.negation_implique {P Q : Prop} :
( not (P → Q) ) ↔  ( P and (not Q) )
:=
/- dEAduction
PrettyName
    Négation d'une implication
-/
begin
    exact not_imp,
end


lemma theorem.negation_existe  {X : Sort*} {P : X → Prop} :
( ( not ∃ (x:X), P x  ) = ∀ x:X, not P x )
:=
/- dEAduction
PrettyName
    Négation de '∃X, P(x)'
-/
begin
    exact propext not_exists,
end



lemma theorem.negation_pour_tout {X : Sort*} {P : X → Prop} :
( not (∀x, P x ) ) ↔ ∃x, not P x
:=
/- dEAduction
PrettyName
    Négation de '∀x, P(x)'
-/
begin
    exact not_forall    
end


lemma theorem.negation_inegalite_stricte {X : Type} (x y : X) [linear_order X]:
( not (x < y) ) ↔ y ≤ x
:=
/- dEAduction
PrettyName
    Négation de 'x < y'
-/
begin
    exact not_lt
end


lemma theorem.negation_inegalite_large {X : Type} (x y : X) [linear_order X]:
( not (x ≤ y) ) ↔ y < x
:=
/- dEAduction
PrettyName
    Négation de 'x ≤ y'
-/
begin
    exact not_le
end




end negation

namespace exercices
/- dEAduction
PrettyName
    Exercices
-/



lemma exercise.zero_ou_un : ∀ n:ℕ, (n ≠ 0 or n ≠ 1)
:=
/- dEAduction
PrettyName
    Pas zéro ou pas un
-/
begin
    sorry
end

lemma exercise.zero_ou_un_2 : not ( ∀ n:ℕ, (n = 0 or n = 1) )
:=
/- dEAduction
PrettyName
    Zéro ou un ou ?...
-/
begin
    rw negation.theorem.negation_pour_tout,
    simp_rw negation.theorem.negation_ou,
    use 2,
    split,
    solve1 {norm_num at *} <|> solve1 {norm_num at *, compute_n 10},
    solve1 {norm_num at *} <|> solve1 {norm_num at *, compute_n 10},
end


lemma exercise.plus_petit : ∃ m:ℕ, ∀ n:ℕ, m ≤ n
:=
/- dEAduction
PrettyName
    Plus petit que tous
-/
begin
    sorry
end

-- set_option pp.all true
lemma exercise.vraiment_plus_petit : 
non( ∃ m:ℤ,
(∀ n:ℤ,
m ≤ n) )
:=
/- dEAduction
PrettyName
    Plus petit que tous...
-/
begin
    -- rw not_exists,
    -- rw negation.theorem.negation_existe,
    -- simp_rw negation.theorem.negation_pour_tout,
    -- simp_rw negation.theorem.negation_inegalite_large,
    -- intro x,
    -- use x-1,
    -- compute_n 10,
end


lemma exercise.egalite : ∀ n:ℕ, ∃ m:ℕ, m=n
:=
/- dEAduction
PrettyName
    Tous égaux
-/
begin
    sorry
end


lemma exercise.egalite_2 :
not (∃ m:ℕ, ∀ n:ℕ, m=n)
:=
/- dEAduction
PrettyName
    Egaux à tous !
-/
begin
    rw negation.theorem.negation_existe,
    simp_rw negation.theorem.negation_pour_tout,
    intro x,
    use x+1,
    compute_n 10,
end


lemma essai (X : Type) (x: X) (A B C : set X) (H : x ∈ A ∩ B) : x ∈ B ∩ A :=
begin
    cases H with H1 H2,
end


lemma exercise.tres_petit :
non (∀ a ≥ (0:ℝ), ∀ ε ≥ (0:ℝ), (a ≤ ε → a = 0) )
:=
/- dEAduction
PrettyName
    Très petit
-/
begin
        conv {whnf },
    -- rw not_forall_eq,
    --  simp_rw Logique_et_nombres_reels.negation.theorem.negation_implique,
    -- simp_rw not_forall_eq,
    -- targets_analysis,
    -- use 1,
    -- split,
    -- solve1 {norm_num at *},
    -- use 2,
    -- rw and.comm, split,
    -- rw exists_prop, rw and.comm, split,
    -- compute_n 10,
end


lemma essai.conv1 (X : Type) (x y : X) (P Q : Prop) : (x = y)  ∧ Q :=
begin
    conv
    begin
        congr,
    end
end


lemma essai.conv :
non (∀ a ≥ (0:ℝ), ∀ ε ≥ (0:ℝ), (a ≤ ε → a = 0) )
:=
begin
--    rw not_forall,
--    conv in (¬ (_ → _)) {skip},
end



example : (∀ ε ≥ (0:ℝ), not (1 ≤ ε → 1 = 0)) :=
begin
    
    conv in (not (1 ≤ ε → 1 = 0)) {rw not_implies_eq},

end





lemma exercise.tres_petit_2 :
∀ a ≥ (0:ℝ), ((∀ ε ≥ (0:ℝ), a ≤ ε) → a = 0)
:=
/- dEAduction
PrettyName
    Ca se complique
SimplificationCompute
    $ALL
-/
begin
    intro a, intro H1,
    intro H2,
    let x := 0, have H3 : x=0, from rfl,
    have H7 : (x:ℝ) ≥ (0:ℝ), by { try {norm_num at *}, try {compute_n 10}},
    -- have H8 := H2 (0:ℕ),
    -- norm_cast at *,
    have H9 := H2 _ H7,
    norm_num at *,
    compute_n 10,
end


example : 0.5 ≥ 0 and 3>0 :=
begin
    split,
    targets_analysis,
    solve1 {norm_num at *} <|> solve1 {norm_num at *, compute_n 10},
    solve1 {norm_num at *} <|> solve1 {norm_num at *, compute_n 10},

end

example (X:Type) (x:X) (A B: set X) (H: A = has_emptyc.emptyc) (H2: x ∈ A)
:
false :=
begin
    rw H at H2,
    exfalso,
    apply set.not_mem_empty _ H2,
end


lemma exercise.tres_petit_3 :
∀ a ≥ (0:ℝ), ((∀ ε > (0:ℝ), a ≤ ε) → a = 0)
:=
/- dEAduction
PrettyName
    Trop compliqué !
-/
begin
    intro x, intro H1,
    intro H2,
    by_contradiction H3,
    have H6: (x/2:ℝ) > 0, rotate, 
    -- have H7 := H2 (x/2) H6,
    `[ have H7 := H2 (x/2) H6] <|> `[ have H7 := H2 _ x/2 H6] <|> `[ have H7 := H2 _ _ x/2 H6] <|> `[ have H7 := H2 _ _ _ x/2 H6] <|> `[ have H7 := H2 _ _ _ _ x/2 H6] <|> `[ have H7 := @H2 x/2 H6] <|> `[ have H7 := @H2 _ x/2 H6] <|> `[ have H7 := @H2 _ _ x/2 H6] <|> `[ have H7 := @H2 _ _ _ x/2 H6] <|> `[ have H7 := @H2 _ _ _ _ x/2 H6], rotate, `[ solve1 {try {norm_num at * }, try {compute_n 1 } }] <|> `[ rotate], rotate,

    -- intros x H1 H2,
    -- by_contradiction,
    -- let x1 := x/2, have H3 : x1 = x/2, refl,
    -- have H4 : x1>0, by { try {norm_num at *}, try {compute_n 10}},
    -- -- have H8 := H2 (0:ℕ),
    -- -- norm_cast at *,
    -- have H9 := H2 _ H4,
    -- rw H3 at H9,
    -- norm_num at *,
    -- compute_n 10,
    -- solve1 {norm_num at *} <|> solve1 {norm_num at *, compute_n 10},
end


lemma exercise.entre_deux_entiers :
∀x:ℤ, ∀y:ℤ, (x<y → (∃z:ℤ, x < z and z < y))
:=
/- dEAduction
PrettyName
    Entre deux entiers
-/
begin
    sorry,
end


lemma exercise.entre_deux_reels :
∀x:ℝ, ∀y:ℝ, (x<y → (∃z:ℝ, x < z and z < y))
:=
/- dEAduction
PrettyName
    Entre deux réels
-/
begin
    admit,
end


lemma exercise.essai_qqs (x y x' y' : ℝ) (H1 : x>1) (H2: y ≥ 56) (P: ℝ → ℝ → Prop)
(H3: ∀ x>(0:ℝ), ∀ y>(0:ℝ), P x y) : P x y
-- ∀ x>(0:ℝ), ∀ y>(0:ℝ), x*y >0
:=
begin
--    have h1: x>0, rotate,
--    have h2: y>0, rotate,
--    have h3 := H3 x h1 y h2, rotate,
--    iterate 2 { focus {try {norm_num at *}, compute_n 10} <|> rotate}, rotate,

end

lemma ex1 (X: Type) (x: X) (P Q : X → Prop) (H1: ∀ x, P x → Q x) (H2: P x):
Q x
:=
begin
    apply H1,
end


lemma ex2 (X Y: Type)(f: X → Y) (H: ∀ x x':X,  x = x') : true
:=
begin
    have h := congr_arg f (H _ _),
end

lemma ex3 (X: Type)  (x: X) (A B : set X) (H: x ∉ A ∪ B) : true
:=
begin
    push_neg at H,
end

end exercices

end Logique_et_nombres_reels

end course