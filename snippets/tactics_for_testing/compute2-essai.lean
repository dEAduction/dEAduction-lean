import data.real.basic
import tactic
import real_definitions
-- import utils

-- #print linarith.make_comp_with_zero

import tactic.linarith.datatypes

import structures2
import utils

/-
- add an optional list of hypos in parameters, then compute is restricted to the given list.

- essayer le simple : assumption, tautology

- tags : 
    - `target_strict`: but est une inégalité stricte ?
    - `target_abs`, `target_max`: but contient une valeur absolue / un max ?
    - `hypo_abs`, `hypo_max`: hypos contiennent des valeurs absolues / max, min ?

    - `target_strict`: 
            - `get_pos_from_pos_eq`
            - `%%a ≠ 0` -->  `abs a >0` si target_abs (`abs_pos_of_ne_zero`)
            - `%%abs a ≠ 0` --> a ≠ 0   si pas target_abs (`ne_zero_of_abs_ne_zero`)
            - idem, utiliser |a| < b ==> -b < a < b, ...

- abs pre_processor:
    - abs ≥ 0. Comment l'utiliser au milieu d'une expression ?
    - simplifier |a| < b, |a| ≤ b, idem minoration


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











namespace tactic.interactive
open lean.parser tactic interactive
open interactive (loc.ns)
open interactive.types
open expr
open linarith

-- useful lemmas:
-- ge_iff_le
-- gt_iff_lt
-- lt_of_le_of_ne
-- le_of_lt
-- div_pos
-- mul_pos
-- inv_pos

-- open tactic.interactive

-------------------------------------------
-------------------------------------------
-- Make 'a < b' from 'a ≠ b' and 'a ≤ b' --
-------------------------------------------
-------------------------------------------
-- This is achieved by the following sequence of tactics:
-- * make_ineq  take "a ≤ b" and "a' ≠ b'" and try to make "a < b"
-- * extract_gt extract the list of inequalities "a ≤ b" from a list of expressions
-- * extract_non_eq does the same for "a ≠ b"
-- * list_prod make the product list of two lists
-- * get_pos_from_pos_eq_from_list is build on the previous ones:
-- it takes a list of expressions,
-- extract inequalities and non-equalities,
-- take all pairs and try to make "a < b" by applying make_ineq
-- * get_pos_from_pos_eq is an interactive tactic that applies this to the local context


set_option trace.linarith true
#help options

def compute3.trace: list string := [""]

meta def default_preprocessors : list global_preprocessor :=
[filter_comparisons, remove_negations, make_comp_with_zero]

------------------------------
-- Detecting abs, max, etc. --
------------------------------

/- Check if some expression contains some constant name inside app. -/
meta def contain_cst (cst_name: name) : expr → bool
| (const a a_1) := (a = cst_name)
| (app a a_1) := (contain_cst a) ∨ (contain_cst a_1)
| _ := ff

/- Check if expr contains abs inside app. -/
meta def contain_abs (e: expr) : tactic bool :=
return (contain_cst `abs e)

/- Detect abs in target in app. -/
meta def target_abs : tactic bool :=
do  target ← tactic.target, e ← infer_type target,
    trace target,
    b ← contain_abs target,
    trace b, return b

/- Check if target is a strict inequality. -/
meta def target_lt_or_gt : tactic bool :=
do target ← tactic.target,
    match target with
    | `(%%a < %%b) := do trace tt, return tt
    | `(%%a > %%b) := do trace tt, return tt
    | _ := return ff
    end


-- example (a b :ℝ) : a < 10*(|b| + 1)-22 := 
-- begin
--     targets_analysis,
--     target_abs,
--     target_lt_or_gt,
-- end

----------------------------
----------------------------
-- Get strict inequalities -
----------------------------
----------------------------

/- Take a proof of a non equality a≠b and replace it by a proof of a-b≠0 -/
private meta def rearr_noneq_aux : expr → expr → tactic expr
| prf `(%%a ≠ 0)    := return prf
| prf `(%%a ≠ %%b)  := mk_app ``sub_ne_zero_of_ne [prf]
| prf  a            := trace a >> fail "couldn't rearrange noneq"

meta def rearr_noneq (e : expr) : tactic expr :=
infer_type e >>= rearr_noneq_aux e

-- lemma neg_zero_of_zero (G: Type) [add_group G] (a: G) (H: a =0) : -a = 0 := neg_eq_zero.mpr H

/-  Take H1 of type "a ≤ 0", H2 of type "a' ≠ 0'", and if a=a'
    then add H3 of type "a < 0" in the local context -/
meta def make_lt_aux : expr × expr → expr × expr → tactic expr
| (prf, a) (prf', a') :=
    tactic.unify a a' >> to_expr ``(lt_of_le_of_ne %%prf %%prf')

/- The same, with the possibility that a=-a' -/
meta def make_lt_aux' : expr × expr → expr × expr → tactic expr
| (prf, a) (prf', a') := do
    prf'' ← mk_app `neg_eq_zero.mpr [prf'], t ← infer_type prf'',
    match t with
    | `(%%a'' = 0) := make_lt_aux (prf, a) (prf'', a'')
    | _ := fail "Unexpected failure"
    end

/-  Take proofs of "a ≤ 0", "a' ≠ 0'", and if a=a' or a = -a'
    then compute a proof of "a < 0". -/
meta def make_lt : expr × expr → expr × expr → tactic expr
| (prf, a) (prf', a') := make_lt_aux (prf, a) (prf', a') <|> make_lt_aux' (prf, a) (prf', a')


private meta def filter_le_zero : expr → bool
| `(%%a ≤ 0) := tt
| _          := ff

private meta def filter_neq_zero (prf: expr) : tactic (expr × expr) :=
do ineq ← infer_type prf, match ineq with
| `(%%a ≠ 0) := return (prf, a)
| _          := fail ""
end

/--
`mk_noneq_with_zero h` takes each proof `h` of a non-equality a ≠ b
and turns it into a proof of a-b ≠ 0.
 -/
meta def make_noneq_with_zero : preprocessor :=
{ name := "make non-equalities with zero",
  transform := λ e, singleton <$> rearr_noneq e <|> return [] }

-- meta def is_lt_zero : expr → tactic expr
-- | `(%%a < 0) := return a
-- | _ := fail "not ?? < 0"

-- meta def is_neq_zero : expr → tactic expr
-- | `(%%a ≠ 0) := return a
-- | _ := fail "not ?? ≠ 0"



/- Pre-processor version of get_pos_from_pos_eq.
We start with normalised comparisons. Specifically, we search for comparisons of the form
    a ≠ 0 (or -a ≠ 0) and a ≤ 0
get a new inequality a < 0 and clear both premises.
-/
meta def add_pos_from_pos_eq : global_preprocessor :=

{ name := "add strict inequalities, e.g. a < 0 from a ≠ 0 and a ≤ 0",
--(transform : list expr → tactic (list expr))
  transform := λ ls,
    -- TODO




-------------------
-------------------
-- Tactic compute -
-------------------
-------------------

lemma inv_pos_mpr {α : Type} [linear_ordered_field α] (a:α) :
0 < a → 0 < a⁻¹ := inv_pos.mpr

open linarith
/- Non-interactive version of nl_linarith. -/
meta def nl_linarith (cfg : linarith_config := {}): tactic unit :=
do
{
tactic.linarith false false []
  { cfg with preprocessors := some $
      cfg.preprocessors.get_or_else default_preprocessors ++ [nlinarith_extras] }
}


/-- A configuration object for `compute1`. 
 develop_ite: set to tt to develop if_then_else definitions, e.g. abs and max.
 -/
meta structure compute_config : Type :=
(develop_ite : bool := ff)


/- Unfold some definitions using if_then_else, then get rid of if_then_else by case reasoning, and try to 
close all the goals by linarith. Unfolded definitions includes abs, max, min.
-/
meta def develop_ite : tactic string :=
    do {`[unfold abs at *], `[unfold min max at *], `[split_ifs at *], repeat $ tactic.linarith false false [],
    return "unfold abs, unfold min max, split_ifs, repeat {linarith}"}
    <|>
    do {`[unfold abs], `[unfold min max], `[split_ifs],
    return "unfold abs, unfold min max, split_ifs"}

/- try several computing tactics for STRICT inequalities.
In case of success return the corresponding effective code. -/
meta def compute1 : tactic string :=
do
{   do {assumption, return "assumption"}
    <|>
    -- solve e.g. "n_0 ≤ n_0 ∨ n_0 ≤ n_1"
    -- with norm_num, solves "n_0 ≤ max n_0 n_1"
    do {tactic.tautology, return "tautology"}
    <|>
    do {tactic.linarith false false [], return "linarith"}
    <|>
    do {nl_linarith, return "nl_linarith"}
    <|>
    do {tactic.applyc ``mul_pos, return "apply mul_pos"}
    <|>
    -- a>0 → a⁻¹ >0
    do {tactic.applyc ``inv_pos_mpr, return "apply inv_pos.mpr"}
    <|>
 -- a≠0 → b≠0 → ab≠0
     do {tactic.applyc ``mul_ne_zero, return "apply mul_ne_zero"}
--  div_pos is now useless
}
#print mul_ne_zero
/- Repeat n times the tactic compute1 ; never fails -/
meta def compute_n_old (n: nat)  (cfg: compute_config := {}) : tactic string :=
do  effective_code_0 ←  if cfg.develop_ite 
                        then try_tactic_string develop_ite 
                        else skip_tactic_string,
    n ← num_goals, match n with
        | 0 := return effective_code_0
        | _ := do
        -- Try to add strict inequalities to the context, if there remains some goal:
        effective_code_1 ← get_pos_from_pos_eq,
        effective_code_2 ← iterate_and_return_code n compute1,
        return $ string.concatenate [effective_code_0, effective_code_1, effective_code_2]
        end

/- Repeat n times the tactic compute1 ; never fails -/
meta def compute_n (n: nat)  (cfg: compute_config := {}) : tactic string :=
do let first_tac := if cfg.develop_ite then [try_tactic_string develop_ite]
                      else ([]:list (tactic string)),
    -- Try to add strict inequalities to the context, if there remains some goal:
    let list_tac := first_tac.append [get_pos_from_pos_eq,
                                      iterate_and_return_code n compute1],
        code ← and_then_and_return_code list_tac,
        return code

/- Apply the compute_n tactic n times,
and in case of success trace the effective code with id. -/
meta def compute_and_return_code (n: nat) (id: string)  (cfg: compute_config := {}):
tactic unit :=
do apply_and_return_code id (tactic.interactive.compute_n n cfg)


end tactic.interactive

-------------
-- Example -- 
-------------
-- set_option trace.linarith true
example (a:ℝ) (H: a ≠ 0) (H': a ≥ 0): a^2 ≥ 0 :=
begin
    -- compute_n 1,
    norm_num at *,
    -- apply_and_return_code "12.1" (tactic.interactive.compute_n 1),
    compute_and_return_code 10 "12.1",
    --compute1,
    -- compute_and_return_code 10 "12.1",  -->
    -- have H_aux := lt_of_le_of_ne H' (ne.symm H), nl_linarith,
end


