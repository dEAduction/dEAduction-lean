import data.set
import tactic

-- dEAduction imports
import structures2
import definitions

set_option pp.width 1000

-- General principles :
-- Type should be defined as parameters, in order to be implicit everywhere
-- other parameters are implicit in definitions, i.e. defined using '{}' (e.g. {A : set X} )
-- but explicit everywhere else, i.e. defined using '()' (e.g. (A : set X) )
-- each definition must be an iff statement (since it will be called with 'rw' or 'symp_rw')



local attribute [instance] classical.prop_decidable
---------------------------------------------
-- global parameters = iùmplicit variables --
---------------------------------------------
section course
parameters {X Y Z: Type}


------------------
-- COURSE TITLE --
------------------
namespace theorie_des_ensembles
/- dEAduction
PrettyName
    Théorie des ensembles
-/


------------------------
-- COURSE DEFINITIONS --
------------------------
lemma definition.inclusion {A B : set X} : A ⊆ B ↔ ∀ {x:X}, x ∈ A → x ∈ B :=
iff.rfl

lemma definition.egalite_deux_ensembles {A A' : set X} :
(A = A') ↔ ( ∀ x, x ∈ A ↔ x ∈ A' ) :=
/- dEAduction
PrettyName
    egalité de deux ensembles
-/
by exact set.ext_iff

lemma theorem.double_inclusion (A A' : set X) :
(A ⊆ A' ∧ A' ⊆ A) → A = A' :=
/- dEAduction
PrettyName
    Double inclusion
-/
begin
    exact set.subset.antisymm_iff.mpr
end

---------------
-- SECTION 1 --
---------------
namespace unions_et_intersections
-- variables unions_et_intersections --
variables {A B C : set X}

-----------------
-- DEFINITIONS --
-----------------
lemma definition.intersection_deux_ensembles {A B : set X} {x : X} :
x ∈ A ∩ B ↔ ( x ∈ A ∧ x ∈ B) :=
iff.rfl
/- dEAduction
PrettyName
    Intersection de deux ensembles
-/

lemma definition.intersection_quelconque_ensembles {I : Type} {E : I → set X}  {x : X} :
(x ∈ set.Inter (λ i, E i)) ↔ (∀ i:I, x ∈ E i) :=
set.mem_Inter
/- dEAduction
PrettyName
    Intersection d'une famille d'ensembles quelconque
-/

lemma definition.union_deux_ensembles  {A : set X} {B : set X} {x : X} :
x ∈ A ∪ B ↔ ( x ∈ A ∨ x ∈ B) :=
iff.rfl
/- dEAduction
PrettyName
    Union de deux ensembles
-/

lemma definition.union_quelconque_ensembles {I : Type} {E : I → set X}  {x : X} :
(x ∈ set.Union (λ i, E i)) ↔ (∃ i:I, x ∈ E i) :=
set.mem_Union
/- dEAduction
PrettyName
    Union d'une famille d'ensembles quelconque
-/


---------------
-- EXERCICES --
---------------
lemma exercise.union_distributive_inter : A ∩ (B ∪ C)  = (A ∩ B) ∪ (A ∩ C) :=
/- dEAduction
PrettyName
    Intersection avec une union
Description
    L'intersection est distributive par rapport à l'union
Tools->Logic
    $ALL -negate
Tools->ProofTechniques
    $ALL -contradiction
Tools->Definitions
    $UNTIL_NOW -union_quelconque_ensembles -intersection_quelconque_ensembles
Tools->Theorems
    double_inclusion
ExpectedVarsNumber
    X=3, A=1, B=1
-/

begin
    sorry
end

lemma exercise.inter_distributive_union : A ∪ (B ∩ C)  = (A ∪ B) ∩ (A ∪ C) :=
/- dEAduction
PrettyName
    Union avec une intersection
Description
    L'union est distributive par rapport à l'intersection
-/
begin
    sorry
end

end unions_et_intersections


---------------
-- SECTION 2 --
---------------
namespace complementaire
-- variables complementaire --
variables  {A B : set X}
variables {I : Type} {E F : I → set X}
-- notation Z `\` A := (@set.compl Z) A
-- notation A `ᶜ` := set.compl A

#print set.compl
-----------------
-- DEFINITIONS --
-----------------
lemma definition.complement {A : set X} {x : X} : x ∈ set.compl A ↔ x ∉ A :=
/- dEAduction
PrettyName
    Complémentaire
-/
by finish

--lemma definition.difference_d_ensembles {A B : set X} {x : X} : x ∈ B \ A ↔ (x ∈ B ∧ x ∉ A) :=
-- iff.rfl

---------------
-- EXERCICES --
---------------
lemma exercise.complement_complement : (set.compl (set.compl A)) = A :=
/- dEAduction
PrettyName
    Complémentaire du complémentaire
Description
    Tout ensemble est égal au complémentaire de son complémentaire
-/
begin
    sorry
end

lemma exercise.complement_union_deux :
set.compl (A ∪ B) = (set.compl A) ∩ (set.compl B) :=
/- dEAduction
PrettyName
    Complémentaire d'union I
Description
    Le complémentaire de l'union de deux ensembles égale l'intersection des complémentaires
-/
begin
    sorry
end

open unions_et_intersections

-- set_option pp.all true
lemma exercise.complement_union_quelconque (x:X) :
x ∈ set.compl (set.Union (λ i, E i)) ↔ x ∈ set.Inter (λ i, set.compl (E i)) :=
/- dEAduction
PrettyName
    Complémentaire d'union II
Description
    Le complémentaire d'une réunion quelconque égale l'intersection des complémentaires
-/
begin
    split, intro h1,
    rw unions_et_intersections.definition.intersection_quelconque_ensembles,
    targets_analysis,
    sorry
end


lemma exercise.inclusion_complement_I :
A ⊆ B → set.compl B ⊆ set.compl A
:=
/- dEAduction
PrettyName
    Le passage au complémentaire renverse les inclusions, implication
Description
    Si A est inclus dans B, alors le complémentaire de A contient le complémentaire de B
-/
begin
    sorry
end

lemma exercise.inclusion_complement_II (Φ: set X → set X) (H: Φ = λ A : set X, set.compl A):
A ⊆ B ↔ set.compl B ⊆ set.compl A
:=
/- dEAduction
PrettyName
    Le passage au complémentaire renverse les inclusions, équivalence
Description
    Si A est inclus dans B, alors le complémentaire de A contient le complémentaire de B
-/
begin
    sorry
end

/- Autres : différence-/

end complementaire



-- Ajouter : 3. produit cartésien, 4. relations ?
-- comment définit-on un produit cartésien d'ensembles ?



---------------
-- SECTION 3 --
---------------
namespace applications_I
/- dEAduction
PrettyName
    Applications et opérations ensemblistes
-/


-- variables applications --
notation f `⟮` A `⟯` := f '' A
notation f `⁻¹⟮` A `⟯` := f  ⁻¹' A

variables  {A A': set X}
variables {f: X → Y} {B B': set Y}
variables {I : Type} {E : I → set X} {F : I → set Y}

-- a-t-on besoin de ceci ?
-- lemma theorem.egalite_fonctions : f = f' ↔ ∀ x : X, f(x) = f'(x) :=
--  function.funext_iff


-----------------
-- DEFINITIONS --
-----------------
lemma definition.image_directe (y : Y) : y ∈ f '' A ↔ ∃ x : X, x ∈ A ∧  f x = y :=
/- dEAduction -/
begin
    unfold set.image,
    sorry
end

lemma definition.image_reciproque (x:X) : x ∈ f  ⁻¹' B ↔ f(x) ∈ B :=
/- dEAduction -/
begin
    sorry
end


---------------
-- EXERCICES --
---------------
lemma exercise.image_de_reciproque : f '' (f ⁻¹' B)  ⊆ B :=
begin
    intro y,
    hypo_analysis,
  sorry
end

lemma exercise.reciproque_de_image : A ⊆ f ⁻¹' (f '' A) :=
begin
    sorry
end

lemma exercise.image_reciproque_inter :  f ⁻¹'  (B∩B') = f ⁻¹'  (B) ∩ f ⁻¹'  (B') :=
begin
    sorry
end

lemma  exercise.image_reciproque_union  : f ⁻¹' (B ∪ B') = f ⁻¹' B ∪ f ⁻¹' B'
:=
begin
    sorry
end

lemma exercise.image_reciproque_inter_quelconque :
(f ⁻¹'  (set.Inter (λ i, F i))) = set.Inter (λ i, f ⁻¹' (F i))
:=
/- dEAduction
PrettyName

-/

begin
    targets_analysis,
    sorry
end

example :
(f ⁻¹'  (set.Inter (λ i, F i))) ⊆ set.Inter (λ i, f ⁻¹' (F i))
∧ (f ⁻¹'  (set.Inter (λ i, F i))) ⊆ set.Inter (λ i, f ⁻¹' (F i))
:=
/- dEAduction
PrettyName

-/

begin
    targets_analysis,
    sorry
end


/- Idem union quelconques -/

lemma exercise.image_inter_inclus_inter_images :
f '' (A∩A') ⊆ f '' (A) ∩ f '' (A')
:=
begin
    sorry
end


lemma exercise.reciproque_complementaire_I :
f ⁻¹' (set.compl B) ⊆ set.compl (f ⁻¹' B)
:=
/- dEAduction
PrettyName
    Image réciproque du complémentaire, inclusion
-/
begin
    sorry
end

lemma exercise.reciproque_complementaire_II :
f ⁻¹' (set.compl B) = set.compl (f ⁻¹' B)
:=
/- dEAduction
PrettyName
    Image réciproque du complémentaire, égalité
-/
begin
    sorry
end

end applications_I

----------------
-- SUBSECTION --
----------------
namespace applications_II
/- dEAduction
PrettyName
    Injections et surjections
-/

-- variables injections_surjections --
variables (f: X → Y) (g : Y → Z) (h : X → Z)

-----------------
-- DEFINITIONS --
-----------------
namespace definitions
def injective {X Y : Type} (f₀ : X → Y) := ∀ x y : X, (f₀ x = f₀ y → x = y)
def surjective {X Y : Type} (f₀ : X → Y) := ∀ y : Y, ∃ x : X, f₀ x = y
def composition {X Y Z : Type} (g₀ : Y → Z) (f₀ : X → Y) := λx:X, g₀ (f₀ x)
def Identite {X : Type} := λ x:X, x

lemma definition.injectivite :
injective f ↔ ∀ x y : X, (f x = f y → x = y)
:=
begin
    unfold injective,
end

lemma definition.surjectivite :
surjective f ↔ ∀ y : Y, ∃ x : X, f x = y
:=
begin
    unfold surjective,
end

lemma definition.composition :
h = composition g f ↔ ∀ x : X, h x = g (f x)
:=
begin
    apply function.funext_iff,
end

lemma definition.egalite_fonctions (f' : X → Y) :
f = f' ↔ ∀ x, f x = f' x :=
begin
    exact function.funext_iff,
end


lemma definition.Identite (f₀: X → X) :
f₀ = Identite ↔ ∀ x, f₀ x = x :=
begin
    apply definition.egalite_fonctions,
end

end definitions


---------------
-- EXERCICES --
---------------

------------------
namespace inverses
open applications_II.definitions

lemma exercise.injective_ssi_inverse_gauche : (injective f) ↔
∃ F: Y → X, (composition F f) = Identite :=
begin
    sorry
end

lemma exercise.surjective_ssi_inverse_droite : (surjective f) ↔
∃ F: Y → X, (composition f F) = Identite :=
begin
    targets_analysis,
    sorry
end


end inverses

---------------------
namespace composition
open applications_II.definitions

lemma exercise.composition_injections (H0 : h = composition g f)
(H1 : injective f) (H2 : injective g) :
injective h
:=
begin
    hypo_analysis,
    sorry
end

lemma exercise.composition_surjections
(H1 : surjective f) (H2 : surjective g) :
surjective (composition g f)
:=
begin
    targets_analysis,
    rw definitions.definition.surjectivite,
    intro y,
    have H3 := H2 y,
    hypo_analysis,
    targets_analysis,
    sorry
end

 


lemma exercise.injective_si_coompo_injective (H0 : h = composition g f)
(H1 : injective h) :
injective f
:=
begin
    sorry
end

lemma exercise.surjective_si_coompo_surjective (H0 : h = composition g f)
(H1 : surjective h) :
surjective g
:=
begin
    targets_analysis
end

end composition

end applications_II

end theorie_des_ensembles


lemma toto (P Q : Prop) (H : P ∧ Q) : P :=
begin
    hypo_analysis,
    analyse_contexte_brut,
end




/--------------------------  
Examples for unitary tests 
---------------------------/
-- propositional logic
example
(P Q R: Prop)
(H0: P → P)
(H0 : P ∧ Q  → Q ∧ P)
(H1 : P ∨ Q  ↔ Q ∨ P)
(H2: ¬ ¬ P ↔ P)
(H3: (R ∧ ¬ R → false))
(H4: false)
: true
:=
begin
    hypo_analysis
end

-- set theory
example
(X X': Type)
(f: X → X')
(A B C: set X)
(A' B': set X')
(x: X)
(H0: x ∈ A)
(H1a: C = A ∩ B)
(H1b: C = A ∪ B)
(H1c: A = set.compl B)
(H1d: A' = set.compl B')
(H2: f '' A ⊆ A')
(H4: A ⊆ f ⁻¹' A')
(H6: f ⁻¹' (A' ∩ B') = f ⁻¹' A' ∩ f ⁻¹' B')
(H8: f ⁻¹' (A' ∪ B') = f ⁻¹' A' ∪ f ⁻¹' B')

: true
:=
begin
    hypo_analysis
end


-- set families
example
(X I J: Type)
(A : set X)
(E: I → set X)
(F: J → set X)
(H0: E = (λ i:I, E i))
(H2a: A = set.Union E)
(H2b: A = set.Union (λ i:I, E i))
(H4: A = set.Inter E)
(H6: (set.Union E ∩ set.Union F) = set.Union (λ k : (I × J), (E k.1) ∩ (F k.2)) )

: true
:=
begin
    hypo_analysis
end


-- applications and quantifiers
example 
(X Y Z: Type)
(f:X → Y) (g: Y → Z)
(h:X → Z)
(x:X)
(y:Y)
(z:Z)
(H0: h = theorie_des_ensembles.applications_II.definitions.composition g f)
(H1: theorie_des_ensembles.applications_II.definitions.injective f)
(H2: theorie_des_ensembles.applications_II.definitions.surjective g)
-- (H3: h x = g (f x))
(H3b: h x = (theorie_des_ensembles.applications_II.definitions.composition g f) x)
(H4: ∀ x x':X, f x = f x' → x = x')
(H5: ∃ y:Y, g y = z)
: true
:=
begin
    hypo_analysis
end



end course