import tactic
import data.real.basic
import data.set
import data.set.lattice
import tactic
import logics


namespace tactic.interactive
open lean.parser tactic interactive 
open tactic expr


local postfix *:9001 := many



/- Tente de réécrire le but ou une hypothèse avec un lemme du type "definitions.***"
dans le sens direct, puis dans le sens réciproque -/
-- Ammélioration : utilisation parse location, cf mathlib doc
-- Amélioration vitale : cibler une occurence de la définition
-- Amélioration : pouvoir passer deux hypothèses (ou plus) qui seront combinées en P ∧ Q ; problème = 
-- comment les combiner dans le bon ordre ? 
-- Amélioration : essayer successivement toutes les versions d'un lemme, 
-- terminant par un numéro, e g intersection_2, intersection_ensemble
meta def defi (name : parse ident) (at_hypo : parse (optional (tk "at" *> ident)))
                            : tactic unit :=
do
    let name := "definitions" <.> to_string name, 
    trace ("J'appelle le lemme " ++ to_string name ++ ","),
    expr ← mk_const name,
    -- expr ← get_local name,
    -- expr ← (to_expr ``(%%name)),
    match at_hypo with
    | none :=  do {rewrite_target expr, trace "sur le but, sens direct"}
            <|>  do {rewrite_target expr {symm := tt},
                    trace "sur le but, sens réciproque"}
 --   | `(tk "at" %%hypo) := skip,
    | some hypo := do e ← get_local hypo, 
                    do {rewrite_hyp expr e,
                 trace ("sur l'hypothèse " ++ (to_string hypo) ++", sens direct")}
                <|>  do {rewrite_hyp expr e {symm := tt},
                 trace ("sur l'hypothèse " ++ (to_string hypo) ++", sens réciproque")}
    end


-- à AMELIORER : essayer simp only si ça rate
meta def applique (names : parse ident*) : tactic unit :=
match names with 
    | [H1,H2] := do 
         nom_hyp ← get_unused_name `H,
        n1 ← get_local H1, 
        n2 ← get_local H2,
        «have» nom_hyp none ``(%%n1 %%n2)
    | _ := fail "Il faut deux paramètres exactement"
    end

-- à AMELIORER
meta def appliquetheo (names : parse ident*) : tactic unit :=
match names with 
    | [name,H2] := do 
         nom_hyp ← get_unused_name `H,
        let name := "theoremes" <.> to_string name, 
        n1 ← mk_const name,
        n2 ← get_local H2,
    «have» nom_hyp none ``(%%n1 %%n2)
    | _ := fail "Il faut deux paramètres exactement"
    end


end tactic.interactive


------------- Lemmes définitionnels ---------------
namespace definitions


------------ Théorie des ensembles --------------
section theorie_des_ensembles

variables {X : Type} {Y : Type}
-- mem_compl_iff
--lemma complement {A : set X} {x : X} : x ∈ - A ↔ ¬ x ∈ A :=
--iff.rfl

lemma complement {A : set X} {x : X} : x ∈ set.univ \ A ↔ x ∉ A := 
by finish

lemma complement_1 {A : set X} {x : X} : x ∈ set.compl A ↔ x ∉ A := 
by finish

lemma complement_2 {A B : set X} {x : X} : x ∈ B \ A ↔ (x ∈ B ∧ x ∉ A) :=
iff.rfl

lemma inclusion (A B : set X) : A ⊆ B ↔ ∀ {{x:X}}, x ∈ A → x ∈ B := 
iff.rfl

lemma intersection_deux  (A B : set X) (x : X) :  x ∈ A ∩ B ↔ ( x ∈ A ∧ x ∈ B) := 
iff.rfl

-- bof : ce n'est pas une définition, mais une caractérisation
lemma intersection_ensemble  (A B C : set X) : C ⊆ A ∩ B ↔ C ⊆ A ∧ C ⊆ B := 
begin
    exact ball_and_distrib
end

lemma intersection_quelconque (I : Type) (O : I → set X)  (x : X) : (x ∈ set.Inter O) ↔ (∀ i:I, x ∈ O i) :=
set.mem_Inter

-- Les deux lemmes suivants seront à regroupé au sein d'une même tactique : essayer le premier, 
-- en cas d'échec essayer le second. Un seul bouton dans l'interface graphique
lemma union  (A : set X) (B : set X) (x : X) :  x ∈ A ∪ B ↔ ( x ∈ A ∨ x ∈ B) := 
iff.rfl

lemma union_quelconque (I : Type) (O : I → set X)  (x : X) : (x ∈ set.Union O) ↔ (∃ i:I, x ∈ O i) :=
set.mem_Union


-- mem_image_iff_bex
lemma image  (A : set X)  (f : X → Y) (b : Y) : b ∈ f '' A ↔  ∃ a, a ∈ A ∧ f(a) = b :=
begin
    tidy,
end

lemma image_reciproque  {B : set Y}  {f : X → Y} {a : X} :
                             a ∈ f ⁻¹' B ↔  f a ∈ B :=
                             iff.rfl

lemma ensemble_egal {A A' : set X} : (A = A') ↔ ( ∀ x, x ∈ A ↔ x ∈ A' ) :=
by exact set.ext_iff

lemma double_inclusion {A A' : set X} : (A = A') ↔ (A ⊆ A' ∧ A' ⊆ A) :=
begin
    exact le_antisymm_iff
end


end theorie_des_ensembles

-------------------- LOGIQUE -----------------------
section logique
lemma double_implication (P Q : Prop) : (P ↔ Q) ↔ (P → Q) ∧ (Q → P) := by tautology


end logique

set_option trace.simplify.rewrite true
-- set_option pp.all true
------------------ Nombres -------------------
section nombres
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


end nombres
------------------ Topologie -------------------







------------------------------------------------
end definitions

