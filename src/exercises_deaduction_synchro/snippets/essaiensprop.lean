/-
This is a d∃∀duction file 
-/

--import data.set
import tactic

-- dEAduction tactics
import structures2      -- hypo_analysis, targets_analysis
import utils            -- no_meta_vars
import user_notations   -- notations that can be used in deaduction UI for a new object
import push_neg_once

-- dEAduction definitions
import set_definitions


-------------------------
-- dEAduction METADATA --
-------------------------
-- logic names ['and', 'or', 'negate', 'implicate', 'iff', 'forall', 'exists']
-- proofs names ['use_proof_methods', 'new_object', 'apply', 'assumption']
-- magic names ['compute']
-- proof methods names ['cbr', 'contrapose', 'absurdum', 'sorry']

/- dEAduction
Title
    ESSAI Propriétés sur ensembles
Author
    Isabelle Dubois
Institution
    Université de Lorraine
Description
    Exercice de logique basé sur les ensembles
-/



local attribute [instance] classical.prop_decidable

---------------------------------------------
-- global parameters = implicit variables --
---------------------------------------------
section course
parameters {X Y : Type}


open set

------------------
-- COURSE TITLE --
------------------
namespace pinocchio
/- dEAduction
PrettyName
    Essai
-/


variables {B C A' : set X}
variables {x x_0 : X} {P : X → Prop }

constant vert : X → Prop

def Pens {X : Type} (A : set X) (P : X → Prop ) :  Prop := ∀ x ∈ A, P x

lemma definition.P_ens {X: Type} {A : set X} {P : X → Prop} {x: X}:
Pens A P ↔ ∀ x ∈ A, P x
:=
/- dEAduction
PrettyName
     Un ensemble qui vérifie une propriété P
-/
begin
     todo
end

def Ttvert (A : set X) :  Prop := ∀ x ∈ A, vert x

lemma definition.Ttvert {A : set X}:
Ttvert A ↔ ∀ x ∈ A, vert x
:=
/- dEAduction
PrettyName
   Un ensemble dont tous les élts sont verts
-/
begin
     todo
end

def nonvide {X : Type} (A : set X) :  Prop := A ≠ ∅

lemma definition.nonvide (A: set X):
nonvide A ↔  (A ≠ ∅) 
:=
/- dEAduction
PrettyName
     Propriété Etre Non vide 
-/
begin
     todo
end




lemma definition.singleton {X : Type} {x y : X}: 
x ∈ ({y} : set X) ↔ x = y
:=
/- dEAduction
PrettyName
    Singleton
-/
begin
    exact mem_singleton_iff,
end




lemma definition.egalite_deux_ensembles {A A' : set X} :
(A = A') ↔ ( ∀ x, x ∈ A ↔ x ∈ A' ) :=
/- dEAduction
PrettyName
    Egalité de deux ensembles
ImplicitUse
    True
-/
begin
     exact set.ext_iff
end







lemma definition.ensemble_non_vide 
(A: set X) :
(A ≠ ∅) ↔ ∃ x : X, x ∈ A
:=
/- dEAduction
PrettyName
  Définition d'un ens non vide
-/
begin
     todo
end

lemma exercise.propensv (A: set X):
(A={x_0}) ∧ (Ttvert A)  → vert x_0
:=
/- dEAduction
PrettyName
   Singleton et tout vert
-/
begin
    todo
end





lemma exercise.exis1 (A: set X):
(Ttvert A)∧ (nonvide A )→  ∃ x ∈ A, vert x
:=
/- dEAduction
PrettyName
     1 - si tous les éléments sont verts et si non vide, alors il existe un élt vert
-/
begin 
 intro H1,
cases H1 with H2 H3,
rw pinocchio.definition.nonvide at H3,
rw Ttvert at H2,
rw pinocchio.definition.ensemble_non_vide at H3,
cases H3 with x H4,
have H6 := H2 _ H4,
use (x),
split, assumption, assumption,
end 

lemma exercise.exis2 :
(Ttvert A)∧ (nonvide A )→  ∃ x : X, x ∈ A ∧ vert x
:=
/- dEAduction
PrettyName
     2 - si tous les éléments sont verts et si non vide, alors il existe un élt vert
-/
begin 
 intro H1, 
 cases H1 with H2 H3,
 rw Ttvert at H2,
end 

lemma exercise.exis3 :
(Ttvert A)∧ (nonvide A )→  ∃ x, x ∈ A ∧ vert x
:=
/- dEAduction
PrettyName
     3 - si tous les éléments sont verts et si non vide, alors il existe un élt vert
-/
begin 
 todo
end 

lemma exercise.propens :
(A={x_0}) ∧ (Pens A P)  → P x_0
:=
/- dEAduction
PrettyName
   prop pour singleton
-/
begin
    todo
end


lemma exercise.nonvide :
 A = { x_0 } → A ≠ ∅
:=
/- dEAduction
PrettyName
    Un singleton est non vide
-/
begin
    todo
end

lemma definition.inclusion {A B : set X} : A ⊆ B ↔ ∀ {x:X}, x ∈ A → x ∈ B :=
/- dEAduction
ImplicitUse
    True
-/
begin
    todo
end

lemma definition.ensemble_vide
(A: set X) :
(A = ∅) ↔ ∀ x : X, x ∉ A
:=
begin
    exact eq_empty_iff_forall_not_mem,
end

lemma definition.ensemble_extension {X: Type}  {P : X → Prop} {x:X} :
 x ∈ {x | P x} ↔ P x
:=
/- dEAduction
PrettyName
    Ensemble en extension
-/
begin
    todo
end

lemma definition.double_inclusion (A B : set X) :
A = B ↔ (A ⊆ B ∧ B ⊆ A) :=
/- dEAduction
PrettyName
    Egalité de deux ensembles : double inclusion
ImplicitUse
    True
-/
begin
    todo
end

end pinocchio

end course
