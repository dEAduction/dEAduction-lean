/-
Feuille d'exercice pour travailler les applications sur les ensembles - Exemples concrets
-/

-- Lean standard imports
import tactic
-- import data.real.basic


-- dEAduction tactics and theorems
-- structures2 and utils are vital
import structures2      -- hypo_analysis, targets_analysis
import utils            -- no_meta_vars
import push_neg_once    -- pushing negation just one step
import induction     -- theorem for the induction proof method
import compute_all   -- tactics for the compute buttons

-- dEAduction definitions
import set_definitions

-- Use classical logic
local attribute [instance] classical.prop_decidable



/- dEAduction
Title
    Théorie des ensembles : applications
Author
    Isabelle Dubois 
Institution
    Université de Lorraine
Description
    Ce cours correspond à un cours standard de théorie "élémentaire" des ensembles. Partie Applications.
AvailableExercises
	NONE
Display
    set.produit --> ( -2, " × ", -1)
-/

---------------------------------------------
-- global parameters = implicit variables --
---------------------------------------------
section course
parameters {X Y Z: Type}
parameters {n p  m : ℕ}
parameters {k l  : int }

open set
open nat


-- namespace generalites
-- /- dEAduction
-- PrettyName
--     Généralités
-- -/

------------------------
-- COURSE DEFINITIONS --
------------------------

variables  {A A': set X}
variables {f: X → Y} {B B': set Y}

variables (g : Y → Z) (h : X → Z)

namespace generalites_ensembles
/- dEAduction
PrettyName
    Généralités sur les ensembles
-/

lemma definition.inclusion {A B : set X} : A ⊆ B ↔ ∀ {x:X}, x ∈ A → x ∈ B :=
/- dEAduction
ImplicitUse
    True
-/
begin
    todo
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
     todo
end
lemma definition.intersection_deux_ensembles {A B : set X} {x : X} :
x ∈ A ∩ B ↔ ( x ∈ A ∧ x ∈ B) :=
/- dEAduction
PrettyName
    Intersection de deux ensembles
ImplicitUse
    True
-/
begin
    exact iff.rfl
end



lemma definition.union_deux_ensembles  {A : set X} {B : set X} {x : X} :
x ∈ A ∪ B ↔ ( x ∈ A ∨ x ∈ B) :=
/- dEAduction
PrettyName
    Union de deux ensembles
ImplicitUse
    True
-/
begin
    exact iff.rfl
end

lemma definition.complement {A : set X} {x : X} : x ∈ set.compl A ↔ x ∉ A :=
/- dEAduction
PrettyName
    Complémentaire
-/
begin
    finish
end



lemma definition.ensemble_vide
(A: set X) :
(A = ∅) ↔ ∀ x : X, x ∉ A
:=
begin
    todo
end

lemma definition.ensemble_extension {X: Type}  {P : X → Prop} {x:X} :
 x ∈ {x | P x} ↔ P x
:=
/- dEAduction
PrettyName
    Ensemble défini en extension
-/
begin
    todo
end

lemma definition.singleton {X : Type} {x y : X}: x ∈ ({y} : set X) ↔ x = y
:=
/- dEAduction
PrettyName
    Ensemble singleton
-/
begin
    todo
end


def set.produit {X : Type } {Y : Type} (A : set X) (B : set Y) :
set (X × Y) := { z : X × Y | ∃ x ∈ A, ∃ y ∈ B, z = (x,y) }


lemma theorem.type_produit2 {X Y : Type} {x:X} {y:Y} :
 ∀ z:X × Y, ∃ x:X, ∃ y:Y, z = (x,y) 
:=
/- dEAduction
PrettyName
    Element général d'un produit cartésien de deux ensembles
-/
begin
     todo
end



lemma definition.type_produit1 {X Y : Type} {A : set X} {B : set Y} {z:X × Y} :
 ( z ∈  set.produit A B ) ↔  ( ∃ x ∈ A, ∃ y ∈ B, z = (x,y) )
:=
/- dEAduction
PrettyName
    Element général d'un produit cartésien de deux ensembles
-/
begin
     todo
end

lemma definition.produit_de_parties {A : set X} {B : set Y} {x:X} {y:Y} :
( (x,y) ∈ set.produit A B ) ↔ x ∈ A ∧ y ∈ B :=
/- dEAduction
PrettyName
    Couple élément d'un produit cartésien de deux parties
-/
begin
    todo
end

lemma theorem.egalite_couple  {x x':X} {y y':Y} :
( (x,y) = (x',y') ) ↔ ( x=x')∧ (y=y') :=
/- dEAduction
PrettyName
    Egalité de couples éléments d'un produit cartésien de deux parties
-/
begin
    todo
end


end generalites_ensembles

namespace generalites_applications
/- dEAduction
PrettyName
    Généralités sur les applications
-/


lemma definition.image_directe (y : Y) : y ∈ f '' A ↔ ∃ x : X, x ∈ A ∧  f x = y :=
begin
    todo
end

lemma definition.image_reciproque (x:X) : x ∈ f  ⁻¹' B ↔ f(x) ∈ B :=
begin
    todo
end

lemma definition.composition {x:X}:
composition g f x = g (f x)
:=
begin
    todo,
end

lemma definition.egalite_fonctions (f' : X → Y) :
f = f' ↔ ∀ x, f x = f' x :=
/- dEAduction
PrettyName
    Egalité de deux fonctions
-/
begin
    exact function.funext_iff,
end


lemma definition.Identite (f₀: X → X) :
f₀ = Identite ↔ ∀ x, f₀ x = x :=
/- dEAduction
PrettyName
    Application identité
-/
begin
    apply definition.egalite_fonctions,
end

end generalites_applications

namespace injection_surjection

lemma definition.injectivite :
injective f ↔ ∀ x y : X, (f x = f y → x = y)
:=
/- dEAduction
PrettyName
    Application injective
ImplicitUse
    True
-/
begin
    refl,
end

lemma definition.surjectivite :
surjective f ↔ ∀ y : Y, ∃ x : X, y = f x
:=
/- dEAduction
PrettyName
    Application surjective
ImplicitUse
    True
-/
begin
    refl,
end




lemma definition.bijectivite_1 :
bijective f ↔ (injective f ∧ surjective f)
:=
/- dEAduction
PrettyName
    Application bijective (première définition)
-/
begin
    todo
end

lemma definition.existe_un_unique
(P : X → Prop) :
(∃! (λx,  P x)) ↔  (∃ x : X, (P x ∧ (∀ x' : X, P x' → x' = x)))
:=
/- dEAduction
PrettyName
    ∃! : existence et unicité
-/
begin
    todo
end

lemma definition.bijectivite_2 :
bijective f ↔ ∀ y : Y, exists_unique (λ x, y = f x)
:=
/- dEAduction
PrettyName
    Application bijective (seconde définition)
-/
begin
    refl,
end

def devers (f : X → Y ) ( A : set X) (B : set Y) := ∀ x ∈ A, (f x) ∈ B




lemma definition.devers {f : X → Y } { A : set X} {B : set Y } :
 ( devers f A B ) ↔  ∀ x ∈ A, (f x) ∈ B
:=
/- dEAduction
PrettyName
    fonction de A vers B
-/
begin
 refl,  
end

def injsur  (f : X → Y ) ( A : set X) := 
∀ x1 ∈ A, ∀ x2 ∈ A, ( (f x1 = f x2) → (x1 = x2) )

lemma definition.injsur   {f : X → Y } { A : set X } :
 ( injsur f A ) ↔ ( ∀ x1 ∈ A, ∀ x2 ∈ A, ( (f x1 = f x2) → (x1 = x2) ) )
:=
/- dEAduction
PrettyName
    injectif sur A
ImplicitUse
  True
-/
begin

    todo
end

def surjsur (f : X → Y ) ( A : set X) (B : set Y) := B ⊆ (f '' A )

lemma definition.surjsur {f : X → Y } { A : set X } {B : set Y} :
 (surjsur f A B) ↔  B ⊆ (f '' A )
:=
/- dEAduction
PrettyName
    surjectif sur B
-/
begin
    todo
end

end injection_surjection

-- end generalites

---------------
-- SECTION 1 --
---------------
namespace injectivite_surjectivite_bijectivite
/- dEAduction
PrettyName
    Images directes et réciproques
-/

open generalites_ensembles
open injection_surjection
open generalites_applications


---------------
-- EXERCICES --
---------------

def pair (k: int) := ∃ l, k = 2*l 

def impair (k: int) := ∃ l, k = 2*l+1 




lemma definition.pair {k: int} : (pair k) ↔ ∃ l, k = 2*l  :=
/- dEAduction
PrettyName
  Pair
ImplicitUse
  True
-/
begin
  todo
end

lemma definition.impair {k: int} : (impair k) ↔ ∃ l, k = 2*l  + 1 :=
/- dEAduction
PrettyName
  Impair
ImplicitUse
  True
-/
begin
  todo
end

lemma theorem.nonimpair {m:ℤ} : (not((impair m))) ↔ (pair m) :=
/- dEAduction
PrettyName
  Non (Impair )
ImplicitUse
  True
-/
begin
 todo
end

lemma theorem.nonpair {m:ℤ } : (not((pair m))) ↔ (impair m) :=
/- dEAduction
PrettyName
  Non (Pair )
ImplicitUse
  True
-/
begin
 todo
end

lemma theorem.pair_ou_impair : ∀ m:ℤ,((pair m) ∨ (impair m) ) :=
/- dEAduction
PrettyName
  Pair ou Impair
ImplicitUse
  True
-/
begin
 todo
end



lemma exercise.inj  (g : ℤ → ℤ )   (H1 : ∀ k:ℤ, pair k -> g k = k/2 ) (H2 : ∀ k:ℤ, impair k -> g k = (k+1)/2 )  :
not ( injective g  )
:=
/- dEAduction
Description
   La fonction g : ℤ → ℤ, g(k) = k/2 si k pair, (k+1)/2 n'est pas injective 
PrettyName
    Non Injectivité de  g(k) = k/2 si k pair, (k+1)/2 sinon - Entiers relatifs

-/
begin
    -- rw definition.injectivite,
    -- push_neg, use 2, use 1, split,
    -- have H12 := H1 2,
    -- have H21 := H2 1,
    todo
end



end injectivite_surjectivite_bijectivite


end course
