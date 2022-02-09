import data.real.basic
import tactic
import real_definitions
-- import utils

-- #print linarith.make_comp_with_zero

namespace tactic.interactive
open lean.parser tactic interactive
open interactive (loc.ns)
open interactive.types
open expr


-- useful lemmas:
-- ge_iff_le
-- gt_iff_lt
-- lt_of_le_of_ne
-- le_of_lt
-- div_pos
-- mul_pos
-- inv_pos

open tactic.interactive

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


----------------------
----------------------
-- Chaining tactics -
----------------------
----------------------
set_option trace.linarith true

/- Concatenate a list of strings using commas as separators-/
-- set_option trace.eqn_compiler.elim_match true
def string.concatenate : (list string) → string
-- (l: list string) : string :=
-- list.foldl (λ (s: string) (t: string), s ++ ", " ++ t) "" l
| []  := ""
| [s] := s
| ("" :: tail) := string.concatenate tail
| (head :: tail) := do let tail_string := string.concatenate tail,
                    match tail_string with
                    | "" := head
                    | _  := head ++ ", " ++ tail_string
                    end




/- Try some (tactic string) and in case of success return its string.
Always succeed. -/
meta def try_and_return_code (my_tactic: tactic string) : tactic string :=
do {s ← my_tactic, return s} <|> return ""

/- Iterate some (tactic string) and return the concatenated returned strings. Stops as soon as 
the tactic makes no progress, i.e. returns the empty string or num_goals = 0.
Fail if some tactic fails. -/
meta def iterate_and_return_code : nat → tactic string → tactic string
| 0       my_tactic := return ""
| (n + 1) my_tactic := do -- trace "(iterating tactic...)",
    first_code ← my_tactic, l ← num_goals,
    match first_code, l with
    | "", _  := return ""
    | s, 0   := return s
    | _ , _  := do
        remaining_code ← iterate_and_return_code n my_tactic,
        return $ string.concatenate [first_code, remaining_code]
    end

/- Apply successively tactics in a given list,
but stop as soon as there is no more goal,
and return concatenation of returned code.
Fail if some tactic fails. -/
meta def and_then_and_return_code : list (tactic string) → tactic string 
| []                  := return ""
| (first_tac :: tail) :=  do
    first_code ← first_tac, l ← num_goals,
    match first_code, l with
    | s, 0   := return s
    | _ , _  := do
        remaining_code ← and_then_and_return_code tail,
        return $ string.concatenate [first_code, remaining_code]
    end


meta def try_tactic_string (my_tac: tactic string) : tactic string :=
do {my_tac <|> return ""}

meta def skip_tactic_string : tactic string :=
do {skip, return ""}

/- Apply some tactic string and trace the returned string as effective code with id-/
meta def apply_and_return_code (id: string) (my_tactic: tactic string) : tactic unit:=
do  effective_code ← my_tactic, 
    tactic.trace $ "EFFECTIVE CODE LEAN n°" ++ id ++ ":" ++ effective_code,
    tactic.trace $ "Try this: "++ effective_code

----------------------------
----------------------------
-- Get strict inequalities -
----------------------------
----------------------------
/-  Take H1 of type "a ≤ b", H2 of type "a' ≠ b'", and if a=a' and b = b'
    then add H3 of type "a < b" in the local context -/
meta def make_ineq : expr × expr × expr → expr × expr × expr → tactic string
| (H1, a, b) (H2, a', b') :=
    tactic.unify a a' >> tactic.unify b b' >> do
    {
    -- H ← mk_fresh_name,
    let H := `H_aux,
    «have» H none ``(lt_of_le_of_ne %%H1 %%H2),
    return $ "lt_of_le_of_ne " ++ to_string H1 ++ " " ++ to_string H1
    }
    <|>
    tactic.unify a b' >> tactic.unify a' b >> do
    {
    -- H ← mk_fresh_name,
    let H := `H_aux,
    «have» H none ``(lt_of_le_of_ne %%H1 (ne.symm %%H2)),
    return $ "have " ++ to_string H ++ " := lt_of_le_of_ne " ++ to_string H1 ++ " (ne.symm " ++ to_string H2 ++ ")"
    }
    <|> 
    do {return ""}

/- The same, but remove H1 and H2 from context
  TODO
  -/
meta def make_ineq' : expr → expr → tactic unit
| H1 H2 := do skip

/- Extract from list of expr the couples (H, a,b)
where the expr H of type "a ≤ b" in is the list -/
meta def extract_gt : list expr → tactic (list (expr × expr × expr))
-- match hypos with
| []                    := return []
| (hypo :: less_hypos)  := do
    {
    ineq ← infer_type hypo,
    remaining_list ← (extract_gt less_hypos),
    match ineq with
        | `(%%a ≤ %%b)  := return $ (hypo, a, b) :: remaining_list
        | _             := return $ remaining_list
        end
    }

/- Extract from list of expr the couples (H, a,b)
where the expr H of type "a ≠ b" in is the list -/
meta def extract_non_eq : list expr → tactic (list (expr × expr × expr))
-- match hypos with
| []                    := return []
| (hypo :: less_hypos)  := do
    {
    ineq ← infer_type hypo,
    remaining_list ← (extract_non_eq less_hypos),
    match ineq with
        | `(%%a ≠ %%b)      := return $ (hypo, a, b) :: remaining_list
        | `(¬ %%a = %%b)    := return $ (hypo, a, b) :: remaining_list
        | _                 := return $ remaining_list
        end
    }


/- Return the product list -/
meta def list_prod {α β : Type} : list α → list β → list (α × β)
| []    l2                  := []
| l1    []                  := []
| (h1 :: l1)  (h2 :: l2)    :=
    (h1, h2) ::
    append  (append (list_prod [h1] l2)
                    (list_prod l1 [h2]))
            (list_prod l1 l2)


meta def get_pos_from_pos_eq_from_list (hypos: list expr) : tactic string :=
do
    inequalities    ← extract_gt hypos,     -- tactic.trace inequalities,
    equalities      ← extract_non_eq hypos, -- tactic.trace equalities,
    -- take all pairs and try to build " a < b "
    effective_codes ← (list_prod inequalities equalities).mmap (λh, make_ineq h.1 h.2),
    let effective_code := string.concatenate effective_codes,
    return effective_code

/- To be applied after "norm_num at *"
    This tactic search in the hypotheses for two hypotheses of the for
    a ≤ b  and a ≠ b
    and deduces
    a < b
    Return the effective code that is equivalent to get_pos_from_pos_eq
    in the given context.
-/
meta def get_pos_from_pos_eq : tactic string :=
do  hypos ← tactic.local_context,
    effective_code ← get_pos_from_pos_eq_from_list hypos,
    return effective_code
    

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
    -- nl_linarith,
    -- apply_and_return_code "12.1" (tactic.interactive.compute_n 1),
    compute_and_return_code 10 "12.1",
    --compute1,
    -- compute_and_return_code 10 "12.1",  -->
    -- have H_aux := lt_of_le_of_ne H' (ne.symm H), nl_linarith,
end

lemma theorem.inegalite_triangulaire1
{a b : ℝ} : abs (a-b) ≤ abs a + abs b :=
begin
    compute_and_return_code 2 "1" {develop_ite:=tt},
end

lemma def.abs (a: ℝ) : abs a = if a ≥ 0 then a else -a :=
begin
    unfold abs max, split_ifs, repeat{linarith},
end

lemma ineq_from_non_eq2 {α: Type} [linear_order α] (a b : α) : ¬ (a = b) ↔ (a < b ∨ b < a) :=
begin
    sorry,
end

example (l l': ℝ) (H: l' ≠ l) : abs (l'-l) >0 :=
begin
    norm_num at *, --rw def.abs,
    rw ineq_from_non_eq2 at *, -- replace `a≠b` by `a < b OR b < a`
    cases_type or and, -- split conjonctions and disjunctions
    all_goals {compute_and_return_code 2 "1" {develop_ite:=tt}},
    --  split_ifs,
    --  get_pos_from_pos_eq, assumption,
    --  linarith,
    -- norm_num at *,
    -- get_pos_from_pos_eq,
    -- compute_and_return_code 5 "1" {develop_ite:=tt},
end