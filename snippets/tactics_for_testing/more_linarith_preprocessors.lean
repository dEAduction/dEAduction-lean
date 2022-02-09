import data.real.basic
import tactic
import real_definitions
-- import utils

-- #print linarith.make_comp_with_zero

import tactic.linarith.datatypes

import structures2

/-
- add an optional list of hypos in parameters, then compute is restricted to the given list.

- essayer le simple : assumption, tautology

- tags : 
    - `target_strict`: but est une inégalité stricte ?
    - `target_abs`, `target_max`: but contient une valeur absolue / un max ?
    - `hypo_abs`, `hypo_max`: hypos contiennent des valeurs absolues / max, min ?

    - `target_strict`: 
            - `get_pos_from_pos_eq`, ou bien splitter les non-égalités
            - `%%a ≠ 0` -->  `abs a >0` si target_abs (`abs_pos_of_ne_zero`)
            - `%%abs a ≠ 0` --> a ≠ 0   si pas target_abs (`ne_zero_of_abs_ne_zero`)
            - idem, utiliser |a| < b ==> -b < a < b, ...

- abs pre_processor:
    - abs ≥ 0. Comment l'utiliser au milieu d'une expression ?
    - simplifier |a| < b, |a| ≤ b, (idem minoration)


- min_max_preprocessor:
    max a b ≥ a, max a b ≥ b, ... à appliquer sur `%%a = max %%b %%c`

- pre-processing n°1:
    - from linarith: `[filter_comparisons, remove_negations, make_comp_with_zero]`
    ou même tout ? `[filter_comparisons, remove_negations, nat_to_int, strengthen_strict_int, make_comp_with_zero, cancel_denoms]`
    - Si `but = inégalité stricte`, y ajouter `get_pos_from_pos_eq` ?
    - pour la suite, il faut récupérer la liste des preuves résultantes
- puis appliquer `linarith` à cette liste (sans preprocessing!)

- target pre-processing:
    - `[apply mul_pos, inv_pos.mpr, mul_ne_zero]` avant de recommencer ?
    Attention, ces énoncés jouent sur le target, pas sur les hypos
    (donc ça ne rentre pas dans la classe preprocessors)
    Deux de ces tactiques dédouble le but (ab >0 remplacé par a>0 et b>0).

    Et ré-essayer `linarith`?
- pre-processor ifs:
    - dans la liste d'égalités / inégalité, unfold abs max (ou éventuellement ré-écrire abs ?)
    - split_ifs, cases_type or and,
-/

/- 
(1) Splittings bourrins :
    - si target strict, splitter les a≠b
    [- si target non abs, essayer de se déparrasser des abs (|a| < b ==> -b < a < b)]
    - si target abs, splitter les abs : unfold abs max, split_ifs

    - si ça ne marche, pas, `apply mul_pos, inv_pos.mpr, mul_ne_zero` et recommencer linarith


-/



open native tactic expr
namespace linarith

/-! ### Preprocessing -/


-- New preprocessors for linarith:
-- `filter_comparisons'`, remove_negations, nat_to_int, strengthen_strict_int,
--  `make_comp_with_zero'`, (`get_strict_ineq`, `filter_noneq`) / `split_noneq`,
-- cancel_denoms
-- make_comp_with_zero' must take into account non-equalities a≠b.
-- After having added strict inequalities we have to filter nonremove non-equalities.

--------------------------------------------------------------------------
-- filter_comparisons': Filter inequalities, equalities, non-equalities -- 
--------------------------------------------------------------------------
/-
Based on linarith.filter_comparisons, but keep non-equalities a≠b -/
private meta def filter_comparisons_aux' : expr → bool
| `(¬ %%p) := p.app_symbol_in [`has_lt.lt, `has_le.le, `gt, `ge, `eq]
| tp := tp.app_symbol_in [`has_lt.lt, `has_le.le, `gt, `ge, `eq, `ne]

/--
Removes any expressions that are not proofs of inequalities, equalities, or negations thereof.
-/
meta def filter_comparisons' : linarith.preprocessor :=
{ name := "filter terms that are not proofs of comparisons",
  transform := λ h,
(do tp ← infer_type h,
   is_prop tp >>= guardb,
   guardb (filter_comparisons_aux' tp),
   return [h])
<|> return [] }

--------------------------------
-- make comparisons with zero -- 
--------------------------------

set_option eqn_compiler.max_steps 50000
private meta def rearr_comp_aux' : expr → expr → tactic expr
| prf `(%%a ≠ 0) := return prf
| prf `(%%a ≠ %%b) := mk_app ``sub_ne_zero_of_ne [prf]
| prf `(%%a ≤ 0) := return prf
| prf  `(%%a < 0) := return prf
| prf  `(%%a = 0) := return prf
| prf  `(%%a ≥ 0) := mk_app ``neg_nonpos_of_nonneg [prf]
| prf  `(%%a > 0) := mk_app `neg_neg_of_pos [prf]
| prf  `(0 ≥ %%a) := to_expr ``(id_rhs (%%a ≤ 0) %%prf)
| prf  `(0 > %%a) := to_expr ``(id_rhs (%%a < 0) %%prf)
| prf  `(0 = %%a) := mk_app `eq.symm [prf]
| prf  `(0 ≤ %%a) := mk_app ``neg_nonpos_of_nonneg [prf]
| prf  `(0 < %%a) := mk_app `neg_neg_of_pos [prf]
| prf  `(%%a ≤ %%b) := mk_app ``sub_nonpos_of_le [prf]
| prf  `(%%a < %%b) := mk_app `sub_neg_of_lt [prf]
| prf  `(%%a = %%b) := mk_app `sub_eq_zero_of_eq [prf]
| prf  `(%%a > %%b) := mk_app `sub_neg_of_lt [prf]
| prf  `(%%a ≥ %%b) := mk_app ``sub_nonpos_of_le [prf]
| prf  `(¬ %%t) := do nprf ← rem_neg prf t, tp ← infer_type nprf, rearr_comp_aux' nprf tp
| prf  a := trace a >> fail "couldn't rearrange comp"

/--
`rearr_comp e` takes a proof `e` of an equality, inequality, or negation thereof,
and turns it into a proof of a comparison `_ R 0`, where `R ∈ {=, ≤, <}`.
 -/
private meta def rearr_comp' (e : expr) : tactic expr :=
infer_type e >>= rearr_comp_aux' e


/--
`mk_comp_with_zero h` takes a proof `h` of an equality, inequality, or negation thereof,
and turns it into a proof of a comparison `_ R 0`, where `R ∈ {=, ≤, <, ≠}`.
 -/
meta def make_comp_with_zero' : preprocessor :=
{ name := "make comparisons with zero",
  transform := λ e, singleton <$> rearr_comp' e <|> return [] }

-----------------------------
-- Get strict inequalities --
-----------------------------
/-
This will be a global preprocessor. It takes a list of comparisons with 0,
and replace each a≤0 by a<0 if the list also contains a≠0 or -a≠0.
We need auxiliary tactic make_lt.
-/

/-  Take proofs of "a ≤ 0" and of "a' ≠ 0'", and if a=a'
    then add a proof of "a < 0" -/
private meta def make_lt_aux : expr × expr → expr × expr → tactic expr
| (prf, a) (prf', a') := tactic.unify a a' >> to_expr ``(lt_of_le_of_ne %%prf %%prf')
                        <|> do linarith_trace "(strengthening failed)", fail ""

lemma neg_non_zero_of_non_zero {G: Type} [add_group G] (a:G) (ha: a ≠ 0) : -a ≠0 := 
begin
    contrapose! ha,-- neg_eq_zero.mpr
    apply neg_eq_zero.mp ha,
end

lemma neg_non_zero_of_non_zero' (a:ℝ) (ha: a ≠ 0) : -a ≠0 := 
begin
    contrapose! ha,-- neg_eq_zero.mpr
    apply neg_eq_zero.mp ha,
end

/- The same, with the possibility that a=-a' -/
private meta def make_lt_aux' : expr × expr → expr × expr → tactic expr
| (prf, a) (prf', a') := do linarith_trace ("trying with..." ++ to_string a'),
    prf'' ← mk_app ``neg_non_zero_of_non_zero' [prf'],
    linarith_trace "...hard",
    t ← infer_type prf'',
    match t with
    | `(%%a'' ≠ 0) := do linarith_trace ("(-->" ++ to_string a'' ++ "≠0"),
                        (make_lt_aux (prf, a) (prf'', a''))
    | _ := do linarith_trace ("failed trying " ++ to_string t), fail "Unexpected failure"
    end

/-  Take a proof of some inequality ineq and a proof of `a' ≠ 0`, 
and if ineq is `a ≤ 0` with a=a' or a = -a'
then return a proof of `a < 0` ; else return the original proof of ineq. -/
private meta def make_lt : expr × expr → expr × expr → tactic expr
| (prf, a) (prf', a') := make_lt_aux (prf, a) (prf', a') 
                        <|> make_lt_aux' (prf, a) (prf', a')  
                        <|> return prf

private meta def make_lt_from_prf : expr → expr → tactic expr 
| prf prf' :=  (do `(%%a ≤ 0) ← infer_type prf,
                 `(%%a' ≠ 0) ← infer_type prf',
                 linarith_trace_proofs "trying with " [prf, prf'],
                 (make_lt (prf, a) (prf', a'))) <|> return prf 

/- Given a list of proofs and a proof of a≠0, replace each proof of a≤0 in the list
 by a proof of a<0. -/
private meta def replace_le : list expr → expr → tactic (list expr)
| ls prf' := ls.mmap (λ prf, (make_lt_from_prf prf prf'))

/- Globalize the previous tactic to a list of proofs of `a≠0`. -/
private meta def replace_le_glob : list expr → list expr → tactic (list expr)
| ls ls' := match ls' with 
            | [] := return ls
            | head :: tail := do ls_new ← replace_le ls head,
                                 (replace_le_glob ls_new tail)
            end

private meta def filter_neg (prf: expr) : tactic bool :=
do t ← infer_type prf, match t with
                        | `(%%a ≠ 0) := return tt
                        | `(¬ %%p)   := return tt
                        | _          := return ff
                        end

private meta def filter_noneq_aux (prf: expr) : tactic bool :=
do t ← infer_type prf, match t with
                        | `(%%a ≠ 0) := return ff
                        | _        := return tt
                        end
-- private meta def filter_le : expr → tactic bool
-- | `(%%a ≤ 0) := return tt
-- | _        := return ff

/- In a list of comparisons with 0, replace each a≤0 by a<0 if the list 
also contains a≠0 or -a≠0.-/
meta def get_strict_ineq : global_preprocessor :=
{ name := "try to replace large inequalities by strict ones",
  transform := λ ls, do
    ls_neq ← ls.mfilter filter_neg, linarith_trace_proofs "Non-equalities: " ls_neq,
    -- ls_le ← ls.mfilter filter_le,
    ls ← replace_le_glob ls ls_neq,
    return ls
}

meta def filter_noneq : preprocessor :=
{ name := "Remove non equalities a≠0",
  transform := λ l, do t ← infer_type l, match t with 
                    | `(%%a ≠ 0) := return []
                    | _        := return [l]
                    end
}

--------------------------
-- Split non equalities --
--------------------------
lemma lt_or_gt_of_non_zero {α: Type} [linear_order α] {a b: α} (ha: a ≠ b) : a < b ∨ b < a :=
begin
    exact lt_or_gt_of_ne ha,
end

example (a b c d: ℝ ) (H0: b=a) (H1: a ≤ 0) (H2: -a ≠ 0): a +1 < 1 := 
begin
    have H2' := lt_or_gt_of_non_zero H2,
    cases H2' with H2l H2g,
    linarith, linarith,
end









meta def deaduction_preprocessors : list global_preprocessor :=
[filter_comparisons', remove_negations, nat_to_int, strengthen_strict_int, 
make_comp_with_zero', get_strict_ineq, filter_noneq,  cancel_denoms]

end linarith

-- meta def deaduction_cfg : linarith_config := {preprocessors := deaduction_preprocessors}

open linarith
open interactive.types
open interactive (parse loc.ns loc.wildcard)
open lean.parser (tk ident many) interactive.loc
local postfix `?`:9001 := optional

meta def tactic.interactive.linarith' (red : parse ((tk "!")?))
  (restr : parse ((tk "only")?)) (hyps : parse pexpr_list?)
  (cfg : linarith_config := {}) : tactic unit :=
tactic.linarith red.is_some restr.is_some (hyps.get_or_else [])
  { cfg with preprocessors := deaduction_preprocessors }

open tactic.interactive
set_option trace.linarith true

-- meta def filter_noneq_aux : expr → tactic string
-- | `(¬ %%p)  := return "¬" 
-- | `(%%a ≠ 0) := return "≠"
-- | _        := return "_"

-- meta def tactic.interactive.essai : tactic unit :=
-- do ls ← local_context, ls.mmap' (λ l, do t ← infer_type l, tactic.trace (filter_noneq_aux t))

example (a b c d: ℝ ) (H0: b=a) (H1: a ≤ 0) (H2: -a ≠ 0): a +1 < 1 := 
begin
    -- essai,
    -- hypo_analysis,
    linarith',
end

