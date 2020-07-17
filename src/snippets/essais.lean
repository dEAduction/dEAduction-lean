import tactic
import structures
--import structures
import definitions


namespace tactic.interactive
open lean.parser tactic interactive 
open interactive (loc.ns)
open interactive.types
open tactic expr
local postfix *:9001 := many -- sinon ne comprends pas ident*

/- Appelle l'analyse récursive sur le but ou sur une hypothèse. Non utilisé par la suite. -/
meta def estcepi (names : parse ident*) : tactic unit := 
match names with
    | [] := do goal ← tactic.target,
                trace (is_pi goal)
    | [nom] := do expr ← get_local nom,
                expr_t ←  infer_type expr,
                trace(is_pi expr_t)
    | _ := skip
    end

meta def estcefl (names : parse ident*) : tactic unit := 
match names with
    | [] := do goal ← tactic.target,
                trace (is_arrow goal)
    | [nom] := do expr ← get_local nom,
                expr_t ←  infer_type expr,
                trace(is_arrow expr_t)
    | _ := skip
    end

meta def estceprop (names : parse ident*) : tactic unit := 
match names with
    | [] := do goal ← tactic.target,
                trace (is_prop goal)
    | [nom] := do expr ← get_local nom,
                expr_t ←  infer_type expr,
                trace(is_prop expr_t)
    | _ := skip
    end

/- 
Tactic to get the list of definitions, ie lemmas from the definitions spacename
-/

meta def is_theorem : declaration → bool
| (declaration.defn _ _ _ _ _ _) :=  ff
| (declaration.thm _ _ _ _) := tt
| (declaration.cnst _ _ _ _) := ff
| (declaration.ax _ _ _) := tt

meta def get_all_theorems : tactic (list name) := 
do
    env ← tactic.get_env,
    pure (environment.fold env [] (λ decl nams,
         if is_theorem decl then 
            declaration.to_name decl :: nams
         else 
            nams))

meta def print_all_theorems' : tactic unit :=
do
    nams ← get_all_theorems,
    nams.mmap (λ h, tactic.trace h),
    return ()

meta def name.get_ante_suffix : name → name
| (name.mk_string s1 (name.mk_string s2 p))  := s2
| (name.mk_numeral s1 (name.mk_string s2 p)) := s2
| p := name.anonymous

meta def print_all_as_theorems : tactic unit :=
do
    nams ← get_all_theorems,
    nams.mmap (λ h, tactic.trace $ name.get_ante_suffix h),
    return ()

meta def is_definitions_as (n : name) : bool :=
if (name.get_ante_suffix n = "set") then tt else ff

meta def print_all_is_as_theorems : tactic unit :=
do
    nams ← get_all_theorems,
    nams.mmap (λ h, tactic.trace $ is_definitions_as h),
    return ()

meta def is_definitions_as' (n : name) : tactic bool :=
if (name.get_ante_suffix n = "definitions") then return tt else return ff

meta def print_all_is_as_theorems' : tactic unit :=
do
    nams ← get_all_theorems,
    nams.mmap (λ h, tactic.trace $ is_definitions_as' h),
    return ()


meta def print_all_definitions' : tactic unit :=
do
    nams ← get_all_theorems,
    def_nams ← list.mfilter is_definitions_as' nams,
    def_nams.mmap (λ h, tactic.trace h),
    return ()




end tactic.interactive




------------ Théorie des ensembles --------------
namespace theorie_des_ensembles

variables {X : Type} {Y : Type}
-- mem_compl_iff
--lemma complement {A : set X} {x : X} : x ∈ - A ↔ ¬ x ∈ A :=
--iff.rfl

lemma def.essai : true :=
begin
    print_all_theorems,
    print_all_as_theorems,
    print_all_is_as_theorems,
    print_all_is_as_theorems',
    print_all_definitions,
    tautology,
end

lemma definitions.complement {A : set X} {x : X} : x ∈ set.univ \ A ↔ x ∉ A := 
begin
    finish
end

lemma definitions.complement_1 {A : set X} {x : X} : x ∈ set.compl A ↔ x ∉ A := 
by finish


lemma exercises.toto (P Q : Prop) (H: P → Q): ∀ R: Prop, R → R :=
begin
    print_all_definitions,
    estcefl,
    intro H1,
    estcefl H1,
    estcefl,
    sorry
end

open tactic

example (y : ℕ) : true :=
by do e ← to_expr ```(∀ x : ℕ, y = 1), trace e, trace e.is_arrow, trace e.is_pi


example (X Y : Type) (A : set Y) (f : X → Y): ∀ x : X, ∃ y ∈ A, f x = y → y = f x :=
begin
--    interactive.goals_analysis,
    hypo_analysis,
    print_all_exercises,
    print_all_definitions,    
    goals_analysis,
    estcefl f,
    estcefl,
    intros x y,
    estcefl,
end

#check is_prop

example (X Y I : Type) (y_1 : Y) (E : I → set X) : ∀ i' : I , ∀ x : E i',  ∀ f : (E i') → Y, f x = y_1 :=
begin
    goals_analysis,
end

#print set

example (X : Type) (x : X) (A : set $ set X)
 (B : X → Prop) (a : A) : X := 
begin
    hypo_analysis,
    
end


example (X : Type) (n : ℕ) (u : ℕ → X): tt :=
begin
    hypo_analysis
end
