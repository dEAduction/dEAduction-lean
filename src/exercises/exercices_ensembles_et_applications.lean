-- import data.set
import tactic

-- dEAduction imports
import structures2
import notations_definitions
import utils

-- General principles :
-- Type should be defined as parameters, in order to be implicit everywhere
-- other parameters are implicit in definitions, i.e. defined using '{}' (e.g. {A : set X} )
-- but explicit everywhere else, i.e. defined using '()' (e.g. (A : set X) )
-- each definition must be an iff statement (since it will be called with 'rw' or 'symp_rw')

---------------------
-- Course metadata --
---------------------
-- logic names ['and', 'or', 'negate', 'implicate', 'iff', 'forall', 'exists']
-- proofs names ['use_proof_methods', 'new_object', 'apply', 'assumption']
-- magic names ['compute']
-- proof methods names ['cbr', 'contrapose', 'absurdum', 'sorry']



/- dEAduction
Title
    Ensembles et applications
Institution
    Université du monde
AvailableMagic
    assumption
-/


local attribute [instance] classical.prop_decidable


---------------------------------------------
-- global parameters = implicit variables --
---------------------------------------------
section course
parameters {X Y Z: Type}

notation [parsing_only] P ` and ` Q := P ∧ Q
notation [parsing_only]  P ` or ` Q := P ∨ Q
notation [parsing_only]  ` not ` P := ¬ P
notation [parsing_only]  P ` implies ` Q := P → Q
notation [parsing_only]  P ` iff ` Q := P ↔ Q

notation [parsing_only]  x ` in ` A := x ∈ A
notation [parsing_only]  A ` cap ` B := A ∩ B
notation [parsing_only]  A ` cup ` B := A ∪ B
notation [parsing_only]  A ` subset ` B := A ⊆ B
notation [parsing_only]  `emptyset` := ∅

notation [parsing_only] P ` et ` Q := P ∧ Q
notation [parsing_only]  P ` ou ` Q := P ∨ Q
notation [parsing_only]  ` non ` P := ¬ P
notation [parsing_only]  P ` implique ` Q := P → Q
notation [parsing_only]  P ` ssi ` Q := P ↔ Q

notation [parsing_only]  x ` dans ` A := x ∈ A
notation [parsing_only]  x ` appartient ` A := x ∈ A
notation [parsing_only]  A ` inter ` B := A ∩ B
notation [parsing_only]  A ` intersection ` B := A ∩ B
notation [parsing_only]  A ` union ` B := A ∪ B
notation [parsing_only]  A ` inclus ` B := A ⊆ B
notation [parsing_only]  `vide` := ∅

notation f `⟮` A `⟯` := f '' A
notation f `⁻¹⟮` A `⟯` := f  ⁻¹' A
notation [parsing_only] f `inverse` A := f  ⁻¹' A
notation g `∘` f := set.composition g f
notation `∃!` P := exists_unique P

open set

------------------
-- COURSE TITLE --
------------------
namespace ensembles_et_applications
/- dEAduction
PrettyName
    Ensembles et applications
-/

namespace definitions
/- dEAduction
PrettyName
    Définitions
-/

namespace generalites
/- dEAduction
PrettyName
    Généralités
-/

------------------------
-- COURSE DEFINITIONS --
------------------------
lemma definition.inclusion {A B : set X} : A ⊆ B ↔ ∀ {x:X}, x ∈ A → x ∈ B :=
begin
    exact iff.rfl
end

lemma definition.egalite_deux_ensembles {A A' : set X} :
(A = A') ↔ ( ∀ x, x ∈ A ↔ x ∈ A' ) :=
/- dEAduction
PrettyName
    Egalité de deux ensembles
-/
begin
     exact set.ext_iff
end

lemma definition.ensemble_vide
(A: set X) :
(A = ∅) ↔ ∀ x : X, x ∉ A
:=
begin
    exact eq_empty_iff_forall_not_mem,
end

-- lemma definition.ensemble_non_vide
-- (A: set X) :
-- (A ≠ ∅) ↔ ∃ x : X, x ∈ A
-- :=
-- begin
--     sorry
-- end

lemma definition.ensemble_extension {X: Type}  {P : X → Prop} {x:X} :
 x ∈ {x | P x} ↔ P x
:=
/- dEAduction
PrettyName
    Ensemble en extension
-/
begin
    refl
end


lemma theorem.double_inclusion (A A' : set X) :
(A ⊆ A' ∧ A' ⊆ A) → A = A' :=
/- dEAduction
PrettyName
    Double inclusion
-/
begin
    exact set.subset.antisymm_iff.mpr
end

end generalites

---------------
-- SECTION 1 --
---------------
namespace unions_et_intersections
-- variables unions_et_intersections --
variables {A B C : set X}

lemma definition.intersection_deux_ensembles {A B : set X} {x : X} :
x ∈ A ∩ B ↔ ( x ∈ A ∧ x ∈ B) :=
/- dEAduction
PrettyName
    Intersection de deux ensembles
-/
begin
    exact iff.rfl
end

lemma definition.union_deux_ensembles  {A : set X} {B : set X} {x : X} :
x ∈ A ∪ B ↔ ( x ∈ A ∨ x ∈ B) :=
/- dEAduction
PrettyName
    Union de deux ensembles
-/
begin
    exact iff.rfl
end

end unions_et_intersections


namespace applications

-- variables applications --

variables  {A A': set X}
variables {f: X → Y} {B B': set Y}

lemma definition.image_directe (y : Y) : y ∈ f '' A ↔ ∃ x : X, x ∈ A ∧  f x = y :=
begin
    sorry
end

lemma definition.image_reciproque (x:X) : x ∈ f  ⁻¹' B ↔ f(x) ∈ B :=
begin
    sorry
end
lemma definition.injectivite :
injective f ↔ ∀ x x' : X, (f x = f x' → x = x')
:=
/- dEAduction
PrettyName
    Application injective
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
-/
begin
    refl,
end

end applications

end definitions


namespace exercices
variables  {A A': set X}
variables {f: X → Y} {B B': set Y}

namespace inclusion

lemma exercise.exercice_inclusion_et_image_directe
(A A' : set X) :
A ⊆ A' → f '' A ⊆ f '' A'
:=
/- dEAduction
PrettyName
    Image directe et inclusion
-/
begin
    sorry
end


lemma exercise.exercice_inclusion_et_image_reciproque
(B B' : set Y) :
B ⊆ B' → f ⁻¹' B ⊆ f ⁻¹' B'
:=
/- dEAduction
PrettyName
    Image directe et inclusion
-/
begin
    sorry
end

end inclusion


namespace quatre_formules

lemma exercise.image_de_reciproque : f '' (f ⁻¹' B)  ⊆ B :=
/- dEAduction
PrettyName
    Image de l'image réciproque
-/
begin
    sorry
end

lemma exercise.reciproque_de_image : A ⊆ f ⁻¹' (f '' A) :=
/- dEAduction
PrettyName
    Image réciproque de l'image
-/
begin
    sorry
end

lemma exercise.image_intersection_1 :
f '' (A∩A') ⊆ f '' (A) ∩ f '' (A')
:=
/- dEAduction
PrettyName
    Image d'une intersection
-/
begin
    sorry
end


lemma exercise.image_union
(A B : set X) :
f '' (A ∪ B)  = f '' A ∪ f '' B
:=
/- dEAduction
PrettyName
    Image d'une union
-/
begin
    sorry
end

end quatre_formules

namespace inclusions_reciproques
/- dEAduction
PrettyName
  Inclusions réciproques
-/

lemma exercise.image_de_reciproque_2
(B : set Y)  (H: surjective f) : f '' (f ⁻¹' B)  = B :=
/- dEAduction
PrettyName
    Image de l'image réciproque, cas surjectif
-/
begin
    sorry
end


lemma exercise.reciproque_de_image_2
(A : set X)  (f: X → Y)  (H: injective f) : A = f ⁻¹' (f '' A) :=
/- dEAduction
PrettyName
    Image réciproque de l'image, cas injectif
-/
begin
    sorry
end

lemma exercise.exercice_image_intersection_2
(A B : set X) (f: X → Y) (H: injective f):
f ''(A ∩ B) = f '' A ∩ f '' B
:=
/- dEAduction
PrettyName
    Image directe d'une intersection, cas injectif
-/
begin
    sorry
end

end inclusions_reciproques


namespace caracterisation
/- dEAduction
PrettyName
    Caractérisation
-/


lemma exercise.image_de_reciproque_3
(f: X → Y) (H : ∀ B : set Y, f '' (f ⁻¹' B)  = B )  :
 surjective f :=
/- dEAduction
PrettyName
    Image de l'image réciproque, caractérisation de la surjectivité
-/
begin
    sorry
end



lemma exercise.reciproque_de_image_3
(f: X → Y) (H : ∀ A : set X, A = f ⁻¹' (f '' A)) :
injective f :=
/- dEAduction
PrettyName
    Image réciproque de l'image, caractérisation de l'injectivité
-/
begin
    sorry
end


lemma exercise.exercice_image_intersection_3
(f: X → Y)  (H : ∀ A B : set X, f ''(A ∩ B) = f '' A ∩ f '' B) :
injective f
:=
/- dEAduction
PrettyName
    Image directe d'une intersection, caractérisation de l'injectivité
-/
begin    
    sorry
end

end caracterisation






namespace unions_et_intersections_quelconques




end unions_et_intersections_quelconques


namespace complementaire
/- dEAduction
PrettyName
  Complémentaire
-/


end complementaire


end exercices

end ensembles_et_applications

end course