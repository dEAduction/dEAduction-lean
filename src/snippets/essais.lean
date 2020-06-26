import tactic
import essai2structures
--import structures

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
end tactic.interactive


example (P Q : Prop) (H: P → Q): ∀ R: Prop, R → R :=
begin
    estcefl,
    intro H1,
    estcefl H1,
    estcefl,
end

open tactic

example (y : ℕ) : true :=
by do e ← to_expr ```(∀ x : ℕ, y = 1), trace e, trace e.is_arrow, trace e.is_pi


example (X Y : Type) (A : set Y) (f : X → Y): ∀ x : X, ∃ y ∈ A, f x = y → y = f x :=
begin
--    interactive.goals_analysis,
    interactive.analyse_buts,
    estcefl f,
    estcefl,
    intros x y,
    estcefl,
end

#check is_prop

example (X Y I : Type) (y : Y) (E : I → set X) : ∀ i : I , ∀ x : E i,  ∀ f : (E i) → Y, f x = y :=
begin
    analyse_buts
end
