/-
Feuille d'exercice pour travailler les applications sur les ensembles - Exercices classiques
-/

import data.set
import tactic

-- dEAduction tactics
import structures2      -- hypo_analysis, targets_analysis
import utils            -- no_meta_vars
import user_notations   -- notations that can be used in deaduction UI for a new object
import push_neg_once


-- dEAduction definitions
import set_definitions

-- General principles :
-- Type should be defined as parameters, in order to be implicit everywhere
-- other parameters are implicit in definitions, i.e. defined using '{}' (e.g. {A : set X} )
-- but explicit everywhere else, i.e. defined using '()' (e.g. (A : set X) )
-- each definition must be an iff statement or an equality
-- (since it will be called with 'rw' or 'symp_rw')

-------------------------
-- dEAduction METADATA --
-------------------------
-- logic names ['and', 'or', 'negate', 'implicate', 'iff', 'forall', 'exists']
-- proofs names ['use_proof_methods', 'new_object', 'apply', 'assumption']
-- magic names ['compute']
-- proof methods names ['cbr', 'contrapose', 'absurdum', 'sorry']

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
-/

local attribute [instance] classical.prop_decidable

---------------------------------------------
-- global parameters = implicit variables --
---------------------------------------------
section course
parameters {X Y Z: Type}


open set



namespace generalites
/- dEAduction
PrettyName
    Généralités
-/

------------------------
-- COURSE DEFINITIONS --
------------------------

variables  {A A': set X}
variables {f: X → Y} {B B': set Y}
variables {I : index_set} {E : set_family I X} {F : set_family I Y}
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

lemma definition.union_quelconque_ensembles {I : index_set} {E : I → set X}  {x : X} :
(x ∈ set.Union E) ↔ (∃ i:I, x ∈ E i) :=
/- dEAduction
PrettyName
    Union d'une famille quelconque d'ensembles
-/
begin
    exact set.mem_Union
end

lemma definition.intersection_quelconque_ensembles {I : index_set} {E : I → set X}  {x : X} :
(x ∈ set.Inter E) ↔ (∀ i:I, x ∈ E i) :=
/- dEAduction
PrettyName
    Intersection d'une famille quelconque d'ensembles
-/
begin
    exact set.mem_Inter
end

lemma definition.ensemble_vide
(A: set X) :
(A = ∅) ↔ ∀ x : X, x ∉ A
:=
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

-- A bouger, mais à enlever de tous les exos où ça ne sert pas !
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

end injection_surjection

end generalites

---------------
-- SECTION 1 --
---------------
namespace images_directes_et_reciproques
/- dEAduction
PrettyName
    Images directes et réciproques
-/
open generalites


variables  {A A': set X}
variables {f: X → Y} {B B': set Y}
variables {I : index_set} {E : set_family I X} {F : set_family I Y}
variables (g : Y → Z) (h : X → Z)

---------------
-- EXERCICES --
---------------

lemma exercise.image_de_reciproque : f '' (f ⁻¹' B)  ⊆ B :=
/- dEAduction
PrettyName
    Image de l'image réciproque
-/
begin
    todo
end

lemma exercise.reciproque_de_image : A ⊆ f ⁻¹' (f '' A) :=
/- dEAduction
PrettyName
    Image réciproque de l'image
-/
begin
    todo
end

lemma exercise.image_reciproque_inter :  f ⁻¹'  (B∩B') = f ⁻¹'  (B) ∩ f ⁻¹'  (B') :=
/- dEAduction
PrettyName
    Image réciproque d'une intersection de deux ensembles
-/
begin
    todo
end

lemma  exercise.image_reciproque_union  : f ⁻¹' (B ∪ B') = f ⁻¹' B ∪ f ⁻¹' B'
:=
/- dEAduction
PrettyName
    Image réciproque d'une union de deux ensembles
-/
begin
    todo
end


lemma exercise.image_reciproque_inter_quelconque :
(f ⁻¹'  (set.Inter (F))) = set.Inter (λ i, f ⁻¹' (F i): set_family I X)
-- (f ⁻¹'  (set.Inter (λ i, F i))) = set.Inter (λ i, f ⁻¹' (F i))
:=
/- dEAduction
PrettyName
    Image réciproque d'une intersection quelconque
-/
begin
    todo
end

lemma exercise.image_reciproque_union_quelconque :
(f ⁻¹'  (set.Union (λ i, F i))) = set.Union (λ i, f ⁻¹' (F i))
:=
/- dEAduction
PrettyName
    Image réciproque d'une union quelconque
-/
begin
    todo
end

lemma exercise.inclusion_image_directe :
A ⊆ A' → f '' (A) ⊆ f '' (A')
:=
/- dEAduction
PrettyName
    L'image directe préserve l'inclusion
-/
begin
    todo
end

lemma exercise.image_union :
f '' (A∪ A') = f '' (A) ∪ f '' (A')
:=
/- dEAduction
PrettyName
    Image directe d'une union
-/
begin
    todo
end

lemma exercise.image_inter_inclus_inter_images :
f '' (A∩A') ⊆ f '' (A) ∩ f '' (A')
:=
/- dEAduction
PrettyName
    Image d'une intersection
-/
begin
    todo
end

lemma exercise.reciproque_complementaire_I :
f ⁻¹' (set.compl B) ⊆ set.compl (f ⁻¹' B)
:=
/- dEAduction
PrettyName
    Image réciproque du complémentaire, inclusion
-/
begin
    todo
end

lemma exercise.reciproque_complementaire_II :
f ⁻¹' (set.compl B) = set.compl (f ⁻¹' B)
:=
/- dEAduction
PrettyName
    Image réciproque du complémentaire, égalité
-/
begin
    todo
end

lemma exercise.image_reciproque_composition
(C: set Z)
:
((composition g f) )⁻¹' C = f ⁻¹' (g ⁻¹' C)
:=
/- dEAduction
PrettyName
    Image réciproque et composition
-/
begin
    todo
end

end images_directes_et_reciproques


---------------
-- SECTION 2 --
---------------

namespace inj_surj
/- dEAduction
PrettyName
    Applications injectives, surjectives, bijectives 
-/
open generalites

-- variables {A B C : set X}
variables  {A A': set X}
variables {f: X → Y} {B B': set Y}
variables {I : index_set} {E : set_family I X} {F : set_family I Y}
variables (g : Y → Z) (h : X → Z)

lemma exercise.composition_injections
(H1 : injective f) (H2 : injective g)
:
injective (composition g f)
:=
/- dEAduction
PrettyName
    Composition d'injections
-/
begin
    todo
end

lemma exercise.composition_surjections
(H1 : surjective f) (H2 : surjective g) :
surjective (composition g f)
:=
/- dEAduction
PrettyName
    Composition de surjections
-/
begin
    todo
end

lemma exercise.injective_si_compo_injective
(H1 : injective (composition g f)) :
injective f
:=
/- dEAduction
PrettyName
    Injective si composition injective
-/
begin
    todo
end

lemma exercise.surjective_si_compo_surjective
(H1 : surjective (composition g f)) :
surjective g
:=
/- dEAduction
PrettyName
    Surjective si composition surjective
-/
begin
    todo
end

lemma exercise.surjective_si_inj_et_compo_surjective
(H1 : surjective (composition g f)) (H2 : injective g) :
surjective f
:=
/- dEAduction
PrettyName
    f surjective si g injective et  g∘f surjective
-/
begin
    todo
end

lemma exercise.injective_si_surj_et_compo_injective
(H1 : injective (composition g f)) (H2 : surjective f) :
injective g
:=
/- dEAduction
PrettyName
    g injective si f surjective et  g∘f injective
-/
begin
    todo
end

lemma exercise.comp_comp_f {f : X → X}
(H : f= composition (composition f f) f )  :
injective f ↔  surjective f
:=
/- dEAduction
PrettyName
   Si f∘f∘f=f alors injectivité équivaut surjectivité
-/
begin
    todo
end



lemma exercise.bij_comp {f: X → Y} :
bijective f ↔ ∀ A : set X, f '' ( set.compl A ) = ( set.compl (f '' A) )
:=
/- dEAduction
PrettyName
   Bijectivité et image du complémentaire
-/
begin
    todo
end

lemma exercise.caracterisation_surj  :
surjective f ↔ ∀ B : set Y, f '' ( (f ⁻¹' B) ) = B
:=
/- dEAduction
PrettyName
   Caractérisation de la surjectivité par image de l'image réciproque
-/
begin
    todo
end

lemma exercise.caracterisation_inj1  :
injective f ↔ ∀ A : set X, f ⁻¹' ( f '' A ) = A
:=
/- dEAduction
PrettyName
   Caractérisation de l'injectivité par image réciproque de l'image 
-/
begin
    todo
end

lemma exercise.caracterisation_inj2  :
injective f ↔ ∀ A  : set X, ∀ A' : set X,  f '' (A∩A') = (f '' A) ∩ (f ''  A')
:=
/- dEAduction
PrettyName
   Caractérisation de l'injectivité par image d'une intersection
-/
begin
    todo
end



end inj_surj
end course
