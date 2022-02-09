import data.real.basic
import tactic

/-  VIDEO 1 -/

lemma my_lemma : ∀ n : ℕ, n ≥ 0 :=
λ n, nat.zero_le n

lemma my_lemma2 : ∀ n : ℕ, n ≥ 0 :=
begin
  intro n,
  apply nat.zero_le,
end

#check `[intro n, apply nat.zero_le]
#check my_lemma2


/-  VIDEO 2: meta-Lean-/

def n: ℕ := 2*3

#reduce n -- 6

set_option pp.numerals false
#reduce n  -- nat.zero.succ.succ.succ.succ.succ.succ


set_option pp.generalized_field_notation false
#reduce n  -- nat.succ (nat.succ (nat.succ (nat.succ (nat.succ (nat.succ nat.zero)))))

#reduce (show 2 ≤ 10, from dec_trivial)

-- The VM can compute efficiently (e.g. on big integers)
-- but we do not trust it.
-- reduce -> Lean's kernel
-- eval -> VM

#eval 2345*22233

-- "meta" disables the termination checker.
-- "meta" allows not well founded recursion, e.g.:
meta def f: ℕ → ℕ
|n := if n = 1 then 1 
else if n%2=0 then f (n/2)
else f (3*n + 1)

#eval f 56


/-  VIDEO 3: How do we maniuplate Lean's expressions in Lean? -/

/- Type expr = semi-faithful relection of how expressions are 
 actually represented in the source code.
 Think of it as an API for manipulating C++ expressions.

-/

set_option pp.generalized_field_notation true
#check expr

/-
var               = dummy var
sort
metavar
local_constant
-- terms sent to the kernel for typechecking should not contain any metavar
-- nor local_constant ; elles servent juste pendant la construction du terme
app               = applique une fonction à un argument
-- Le contraire est l'abstraction ; 
-- on a deux type d'abstraction, lambda et Pi
-- Pi is a function type, lambda is a function
lam (var_name) (var_type) (body) 
-- var name is only for printing,
-- var_type is there (so we d not need type for dummy_var)
pi
elet      = binding a var to some value
macro  = un truc interne
-/

open expr -- Cliquer pour voir l'API sur expr


/- Une fonction qui dit si une expression est une constant apparaissant
dans une liste de noms -/
-- on écrit {! expr → bool} pour générer automatiquement la liste de cas
-- OK
meta def is_constant_of (l: list name) : expr → bool
| (const a a_1) := a ∈ l
| _ := ff


-- nat and int are types, not names.
-- `nat is the name "nat" (a string)
-- ℕ is also a type, we need the expression representing that type
-- we antiquote expression : `(ℕ) is the expression representing ℕ
#eval is_constant_of [`real, `int, `nat] `(ℕ)


/- Une fonction qui dit si une expression est une fonction 
apparaissant dans une liste de noms -/
-- Ne marche pas !?
meta def is_app_of (l: list name) (e : expr) :  bool :=
match e with
| (app a a_1) := a.const_name ∈ l  
| _ := ff
end

-- OK
meta def is_app_of2 (l: list name) (e : expr) :  bool :=
let app_name := e.get_app_fn in 
is_constant_of l app_name

#check has_le.le
#check nat.has_le.le
#check (20 < 5)
#eval is_app_of2 [`has_le.le, `has_lt.lt] `(20 < 5)

#check abs


/- Essais ratés !-/

-- meta def abs_occurs (e : expr) : bool :=
-- let ns :=  name_set.of_list [`abs] in
-- expr.has_local_in e ns

-- meta def abs_occurs2 (e : expr) : bool :=
-- expr.occurs `(abs) e

-- #print (to_raw_fmt (1+1))

-- #eval abs_occurs `(ℕ → ℝ)

-- #eval app `(nat.succ) `(nat.zero)  -- pb = type is "reflected blabla" instead of expr

-- OK
meta def mk_app (e₁ e₂ : expr) : expr :=
app e₁ e₂

#eval to_string $ to_raw_fmt $ mk_app `(nat.succ) `(nat.zero) 


-- OK
meta def get_lhs_rhs : expr → option (expr × expr) 
| `(%%a < %%b) := some (a, b)
| `(%%a ≤ %%b) := some (a, b)
| _ := none

set_option pp.numerals true
#eval  get_lhs_rhs `(1 < 5)             -- nothing
#eval to_string $ get_lhs_rhs `(1 < 5)  -- complicated
#eval tactic.trace $ get_lhs_rhs `(1 < 5)  -- nice

-- #eval to_string $ to_raw_fmt $ `(abs 1:ℝ)  -- reflected blabla -> tell Lean it is an expr
#eval to_string $ to_raw_fmt $ (`(λ x: ℕ , x) : expr)


-- DANGER !!
meta def succ_fn : expr → option expr
| (lam var_name bi var_type body) := 
let new_body :=  mk_app `(nat.succ) body in
(lam var_name bi var_type new_body)
| _ := none

-- | `(%%f: ℕ → ℕ) := some `(λ n , f n + 1)
-- | _             := none

#eval to_string $ succ_fn (`(λ x: ℕ , x) : expr)
#eval to_string $ succ_fn (`(λ x: ℝ , x) : expr)


---------------------------------
/-  VIDEO 4 : tactic monad !!  -/
---------------------------------

-- Write functions that manipulates the context
-- A term of type tactic nat is a function that takes a tactic state
-- and return a nat number paired with a new tactic state
-- The syntax let us ignore the input tactic state and write as if it was just a fct returning a nat.in

open tactic

-- pure = return, commun to all monads
meta def make_a_nat : tactic ℕ :=
return 14  -- lifts 14 into the tactic monad

#check @return
#check tactic.trace
#check @tactic.trace  -- type "tactic unit" means no output, we just care about its side effects.

meta def trace_a_nat : tactic unit :=
do
{
  n ← make_a_nat,
  trace n  
}
-- la flèche ← permet d'enchainer (de composer) les tactiques, 
-- elle signifie "exécute la tactique et assigne la valeur"
-- elle ne marche que pour les fonctions à valeur "tactic"
-- e.g. "new_nat ← 48"  -> erreur. On peut écrire
-- "new_nat ← return 48", ou alors utiliser "let new_nat := 48,"

-- NB: le type du bloc entier est le type de la dernière ligne

run_cmd trace_a_nat  -- run_cmd creates an empty tacti state
-- example (a b : ℕ) : false :=
-- begin
--   trace_a_nat,
--   sorry
-- end

#check @list.mmap -- For us m is "tactic"
#check @list.mmap' -- If we just care about side effect

meta def inspect : tactic unit:=
do t ← target,
trace t,
let new_nat := 48,
a_expr ← get_local `a, -- <|>  fail "oops, no 'a'!",
trace (expr.to_raw_fmt a_expr),
t ← infer_type a_expr,
trace t,
ctx ← local_context,
trace ctx,
-- list.mmap loops over the list ctx and apply infer_type to each element, returning a new list
ctx_type ← list.mmap infer_type ctx,   
ctx_type ← ctx.mmap infer_type,  -- same effect: field notation
ctx_type ← ctx.mmap $ λ e, infer_type e, -- same effect
trace ctx_type,
-- in 1 step:
ctx.mmap' $ λ e, do t ← infer_type e, trace t



-- A tactic can fail, e.g. if there is nothing called "a" in the context
example (a b : ℕ) (c d : ℤ): b ≥ 0 := by do inspect

-----------------------------------
/-  VIDEO 5 : concrete examples  -/
-----------------------------------

meta def test (hyp tgt : expr) : tactic bool :=
do 
hyp_tp ← infer_type hyp,
return (hyp_tp = tgt)


meta def map_over_lc (tgt : expr) :  list expr → tactic unit 
 | []       := fail "Nothing match the target"
 | (ls::l)  := 
  do  is_match ← test ls tgt,
      if is_match then exact ls else map_over_lc l

meta def assump : tactic unit :=
do
{t ← target,
ctx ← local_context,
map_over_lc t ctx
}

-- More monadic :
meta def test_and_exact (hyp tgt : expr) : tactic unit :=
do 
hyp_tp ← infer_type hyp,
--guard (hyp_tp = tgt), -- fail if ff
is_def_eq hyp_tp tgt,
exact hyp

#check @list.mfirst


-- Now useless
meta def map_over_lc' (tgt : expr) :  list expr → tactic unit 
 | []       := fail "Nothing match the target"
 | (ls::l)  := 
   (test_and_exact ls tgt) <|> map_over_lc' l



-- In one line!!
meta def assump' : tactic unit :=
local_context >>= list.mfirst exact
/- {
ctx ← local_context,
ctx.mfirst exact
-- map_over_lc t ctx
}
 -/


example (A B C : Prop) (ha : A) (hc : C) : C :=
by assump'


example (n: ℕ ) (H : n + 0 = 5) : n = 5 := by assump'


meta def single_refl (e : expr) : tactic unit :=
do tp ← infer_type e,
  guard $ tp = `(ℕ),
  -- pf ← mk_app `eq.refl [e],  -- build a proof of e = e
  pf ← to_expr ``(not_lt_of_ge  (nat.zero_le %%e)), -- Here we build  aproof of new prop
  nm ← get_unused_name e.local_pp_name,
  note nm none pf,                                  -- And now we add these new props to the context
  skip  -- so that type is tactic unit


meta def add_refls : tactic unit :=
local_context >>= list.mmap' (λ e, try $ single_refl e )  -- mmap' needs every step to succeed

example (a b c : ℕ) (hab : a=b) : 0=0 := 
begin
  add_refls, refl,
end


-------------------------------------------
/-  VIDEO 6 : parsing, pattern matching  -/
-------------------------------------------















