# CONTRIBUTING

## Making your own exercises: an overview
dEAduction is designed so that everyone can create its own exercises sheet. Designing a new exercise sheet consists in creating a Lean file
that dEAduction will be able to parse. The dEAduction format of Lean's files is described in [this other page](https://github.com/dEAduction/dEAduction/wiki/d%E2%88%83%E2%88%80duction-format-for-Lean-files).
Here we just give an overview of the creation of new files. Roughly speaking, you may face two different situations.
* If the concepts you need for your exercises have already been incorporated into dEAduction, then creating exercises should not be too difficult.
The easiest way is probably to look into a [course file](src/exercises) that makes use of the concepts you need, and infer the correct syntax (Copy-Paste is your friend!).
For instance you could start with an existing exercises sheet and modify the exercises to suit your needs.
Note that for the moment, dEAduction only integrates naive set theory, and a bit of manipulations on numbers.
A minimal knowledge of Lean's syntax will certainly help,
but looking into dEAduction exercises files may be a good way to start understanding (a little bit of) Lean.
* If you want to start a new theory, then the process is more involved.
The first thing to do is to check that dEAduction will be able to handle the theory; 
for instance, as of now, the manipulation of numbers does not include any possibility of fine computing, there is just a "compute" button that can essentially
use linear combinations of inequalities (based on a sophisticated but not very efficient version of Lean's `linarith` tactic).
From a practical viewpoint, your exercises should be provable using only dEAduction buttons and the definitions and theorems that you will put into your Lean file.

Imagine you want to deal with, say, continuous real functions, and they are not integrated in dEAduction.
First you define the property `continuous f` in your Lean file. But dEAduction will not be able to display it properly: to remedy for this,
we will have to add a few lines to some specific file in the Python part of dEAduction (in a file called `display_data.py`).
You can do this by yourself and make a pull request (see the [CONTRIBUTING](https://github.com/dEAduction/dEAduction/blob/master/CONTRIBUTING.md)),
or ask someone in the dEAduction team if he can help. For this you might consider using [issues](https://github.com/dEAduction/dEAduction/issues).

Note that dEAduction's users will not have access to your definition until you put it in the Lean file in the shape of a "definition" lemma. So your continuity definition will appear twice: the first instance is for Lean's usage, like in
```
def continuous (f : X → Y) :=
  ∀ x₀ : X, ∀ ε > 0, ∃ δ > 0, ∀ x, d_[X] x₀ x < δ → d_[Y] (f x₀) (f x) < ε   
```
And the second time to make it available for dEAduction's user, like in
```
lemma definition.continuity
(f : X → Y) :
(continuous f) ↔ ( ∀ x₀ : X, ∀ ε > 0, ∃ δ > 0, ∀ x, d_[X] x₀ x < δ → d_[Y] (f x₀) (f x) < ε )
:=
begin
    sorry
end
```
You might skip the first instance if you use the continuity definition from the mathematical library of Lean instead of redifining it.

## Structure of a Lean file suitable for dEAduction
### Statements
The main ingredients of the file are definitions, theorems, and exercises.
Every definition should be stated as an "iff" lemma, e.g.
```
lemma definition.inclusion
{A B : set X} :
A ⊆ B ↔ ∀ {x:X}, x ∈ A → x ∈ B :=
begin
    exact iff.rfl
end
```
The `begin-end`part contains a proof of the lemma, which often reduces to `exact iff.rfl`. Note that you may fill every such proof using `sorry`, like
```
begin
    sorry
end
```
but take care that your lemma is valid!

Theorems may be any kind of lemmas.
The default behaviour of dEAduction is that every definitions and theorems that occur before a given exercise will be available as tools to solve the exercise
(in the statements list of dEAduction),
but this may be easily customised using the docstrings of the lean file (see [this page](https://github.com/dEAduction/dEAduction/wiki/d%E2%88%83%E2%88%80duction-format-for-Lean-files)).

Exercises are also stated as lemmas. As for definitions and theorems you may choose to provide a proof for them, or just a "proof by sorry";
in any case the proof will be ignored by dEAduction. Note however that every statement must be followed by a `begin - end`part, since will be used by dEAduction to get the precise mathematical content of the statement (adding into it the `hypo_analysis` and `context_analysis` tactics, see below).

### Namespaces
The file may be structured into sections (technically namespaces).
This structure will be reflected by dEAduction to help the user navigate into the different parts of the "course".

# Imports
You file should begin with some imports:
```
import tactic
import structures2
import utils
```
* `tactic` is a standard Lean import,
* `structures2` contains the definitions of the tactics `hypo_analysis`and `targets_analysis`. These tactics prints strings that reflect Lean's structures
of mathematical objects of the context. These tactics are incorporated by dEAduction into the Lean file before sending it to the Lean server,
and the resulting outputs are retrieved by dEAduction in order to build its own version of the mathematical objects of the context.
This allows dEAduction to display mathematics using its own format, and to filter the user's requests before sending them to Lean.
* `utils` contains some less essential tactics used by dEAduction (e.g. `no_meta_vars`that is used to ensure that the context does not contain any meta-variable).
* The `compute` file defines the tactics that are called by dEAduction's `compute`button, and should be also imported if this button is displayed.

# Example
The following is a minimal example of a valid Lean file for dEAduction:
```
import tactic
import structures2
import utils

/- dEAduction
Title
    Naive set theory
Institution
    World University
AvailableMagic
    ALL -compute
-/

local attribute [instance] classical.prop_decidable
-- NB: this is a technical line (allow the use of classical logic).

section course
parameters {X : Type}
open set -- Open the `set`spacename to allow easy access to the instructions.
------------------
-- COURSE TITLE --
------------------
namespace set_theory

namespace definitions

------------------------
-- COURSE DEFINITIONS --
------------------------
lemma definition.inclusion {A B : set X} : A ⊆ B ↔ ∀ {x:X}, x ∈ A → x ∈ B :=
begin
    exact iff.rfl
end

end definitions
namespace exercises

------------------------
-- EXERCISES --
------------------------
lemma exercise.inclusion_transitive
(A B C : set X) :
(A ⊆ B ∧ B ⊆ C) → A ⊆ C
:=
/- dEAduction
PrettyName
    Transitivity of inclusion
Description
    The inclusion is a transitive relation.
-/
begin
    sorry
end

end exercises

end set_theory
end course
