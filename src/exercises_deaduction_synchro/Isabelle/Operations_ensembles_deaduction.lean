/-
Feuille d'exercice pour travailler les opérations et autres définitions sur les ensembles 
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
    Théorie des ensembles : opérations
Author
    Isabelle Dubois 
Institution
    Université de Lorraine
Description
    Ce cours correspond à un cours standard de théorie "élémentaire" des ensembles.
-/

local attribute [instance] classical.prop_decidable

---------------------------------------------
-- global parameters = implicit variables --
---------------------------------------------
section course
variables {X Y Z: Type}


open set




namespace generalites
/- dEAduction
PrettyName
    Généralités
-/

------------------------
-- COURSE DEFINITIONS --
------------------------
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

lemma definition.ensemble_vide
(A: set X) :
(A = ∅) ↔ ∀ x : X, x ∉ A
:=
begin
    todo
end

lemma definition.ensemble_non_vide
(A: set X) :
(A ≠ ∅) ↔ ∃ x : X, x ∈ A
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

lemma exercise.double_inclusion (A A' : set X) :
A = A' ↔ (A ⊆ A' ∧ A' ⊆ A) 
:=
/- dEAduction
PrettyName
    Egalité de deux ensembles : double inclusion
-/
begin
    todo
end

lemma exercise.nonvide (A : set X) (x_0 : X) :
 A = { x_0 } → A ≠ ∅
:=
/- dEAduction
PrettyName
    Un singleton est non vide
-/
begin
    todo
end

lemma exercise.inclusion_transitive
(A B C : set X) :
(A ⊆ B ∧ B ⊆ C) → A ⊆ C
:=
/- dEAduction
PrettyName
    Transitivité de l'inclusion
-/
begin
    todo
end




end generalites

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



---------------
-- EXERCICES --
---------------

lemma exercise.intersection_comm :
A ∩ B = B ∩ A
:=
/- dEAduction
PrettyName
    Commutativité de l'intersection
-/
begin
    todo
end


lemma exercise.union_comm :
A ∪ B = B ∪ A
:=
/- dEAduction
PrettyName
    Commutativité de l'union
-/
begin
    todo
end



lemma exercise.intersection_inclus_ensemble :
(A ∩ B ⊆ B ) 
:=
/- dEAduction
PrettyName
    Un ensemble contient son intersection avec un autre
-/
begin
    todo
end

lemma exercise.ensemble_inclus_union :
A  ⊆ A ∪ B
:=
/- dEAduction
PrettyName
    Un ensemble est contenu dans son union avec un autre
-/
begin
    todo
end

lemma exercise.union_distributive_inter : A ∩ (B ∪ C)  = (A ∩ B) ∪ (A ∩ C) :=
/- dEAduction
PrettyName
    Intersection avec une union
Description
    L'intersection est distributive par rapport à l'union
AvailableLogic
    $ALL
AvailableProofs
    $ALL
AvailableDefinitions
    $UNTIL_NOW 
AvailableTheorems
    double_inclusion
ExpectedVarsNumber
    X=3, A=1, B=1
-/
begin
    todo
end

-- NB: 'ExpectedVarsNumber' is not implemented yet
-- planned to be used for naming variables


lemma exercise.inter_distributive_union : A ∪ (B ∩ C)  = (A ∪ B) ∩ (A ∪ C) :=
/- dEAduction
PrettyName
    Union avec une intersection
Description
    L'union est distributive par rapport à l'intersection
AvailableDefinitions
    $UNTIL_NOW 
-/
begin
    todo
end

lemma exercise.inclus_eq_union : A  ⊆ B   ↔ (A ∪ B)=B
:=
/- dEAduction
PrettyName
    Caractérisation de l'inclusion par l'union
Description
    Caractérisation de l'inclusion par l'union
AvailableDefinitions
    $UNTIL_NOW 
-/
begin
    todo
end

lemma exercise.inclus_eq_inter : (A  ⊆ B )  ↔ ( (A ∩ B)=A)
:=
/- dEAduction
PrettyName
    Caractérisation de l'inclusion par l'intersection
Description
    Caractérisation de l'inclusion par l'intersection
AvailableDefinitions
    $UNTIL_NOW 
-/
begin
    todo
end


lemma exercise.cond_egalite : ((A ∩ B)=(A ∪ B) ) → (A=B)
:=
/- dEAduction
PrettyName
     Quand l'intersection égale l'union
Description
     Quand l'intersection égale l'union
AvailableDefinitions
    $UNTIL_NOW 
-/
begin
    todo
end

lemma exercise.cond_egalite2 : ((A ∩ B)= (A ∩ C) ∧  (A ∪ B)= (A ∪ C)) → (B=C)
:=
/- dEAduction
PrettyName
    Même union et même intersection
Description
    Même union et même intersection
AvailableDefinitions
    $UNTIL_NOW 
-/
begin
    todo
end

end unions_et_intersections


---------------
-- SECTION 2 --
---------------
namespace complementaire_difference
/- dEAduction
PrettyName
    Complémentaire et Différence
-/


-- variables complementaire --
variables  {A B C : set X}

-- notation `∁`A := set.compl A

-----------------
-- DEFINITIONS --
-----------------
lemma definition.complement {A : set X} {x : X} : x ∈ set.compl A ↔ x ∉ A :=
/- dEAduction
PrettyName
    Complémentaire
-/
begin
    todo
end

lemma definition.difference
(A B : set X) (x : X) :
x ∈ (A \ B) ↔ x ∈ A ∧ x ∉ B
:=
/- dEAduction
PrettyName
    Différence de deux ensembles
-/
begin
    refl,
end

---------------
-- EXERCICES --
---------------



lemma exercise.complement_complement : (set.compl (set.compl A)) = A :=
/- dEAduction
PrettyName
    Complémentaire du complémentaire
Description
    Tout ensemble est égal au complémentaire de son complémentaire
AvailableDefinitions
    $UNTIL_NOW 
-/
begin
    todo
end

lemma exercise.diff_diff : ((A \ B)\ C) = (A \ (B ∪ C)) :=
/- dEAduction
PrettyName
    Différence d'une différence
Description
    Différence d'une différence
AvailableDefinitions
    $UNTIL_NOW 
-/
begin
    todo
end

lemma exercise.inter_compl :
(A ∩  ((set.compl A) ∪ B) ) = ( A ∩  B) :=
/- dEAduction
PrettyName
    Intersection et complémentaire
Description
    Intersection et complémentaire
AvailableDefinitions
    $UNTIL_NOW 
-/
begin
    todo
end

lemma exercise.decomposition_union_inter :
A = ( A ∩  B) ∪ ( A ∩  (set.compl B)) :=
/- dEAduction
PrettyName
    Décomposition d'un ensemble avec une union
Description
    Décomposition d'un ensemble avec une union
AvailableDefinitions
    $UNTIL_NOW 
-/
begin
    todo
end

lemma exercise.decomposition_inter_union :
A = ( A  ∪   B) ∩ ( A  ∪   (set.compl B)) :=
/- dEAduction
PrettyName
    Décomposition d'un ensemble avec une intersection
Description
    Décomposition d'un ensemble avec une intersection
AvailableDefinitions
    $UNTIL_NOW 
-/
begin
    todo
end


lemma exercise.complement_union_deux :
set.compl (A ∪ B) = (set.compl A) ∩ (set.compl B) :=
/- dEAduction
PrettyName
    Complémentaire d'union 
Description
    Le complémentaire de l'union de deux ensembles égale l'intersection des complémentaires
AvailableDefinitions
    $UNTIL_NOW 
-/
begin
    todo
end

lemma exercise.complement_intersection_2
(A B : set X):
set.compl (A ∩  B) = (set.compl A) ∪ (set.compl B)
:=
/- dEAduction
PrettyName
    Complémentaire d'une intersection
-/
begin
    todo
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
    todo
end

lemma exercise.inclusion_complement_II :
A ⊆ B ↔ set.compl B ⊆ set.compl A
:=
/- dEAduction
PrettyName
    Le passage au complémentaire renverse les inclusions, équivalence
Description
    Si A est inclus dans B, alors le complémentaire de A contient le complémentaire de B
-/
begin
    todo
end




end complementaire_difference




namespace produits_cartesiens
/- dEAduction
PrettyName
    Produits cartésiens
-/


-- Peut-on en faire une définition ?
lemma theorem.type_produit :
∀ z:X × Y, ∃ x:X, ∃ y:Y, z = (x,y)
:=
/- dEAduction
PrettyName
    Element d'un produit cartésien de deux ensembles
-/
begin
    todo
end


lemma definition.produit_de_parties {A : set X} {B : set Y}
{x:X} {y:Y} :
(x,y) ∈ set.prod A B ↔ x ∈ A ∧ y ∈ B
:=
/- dEAduction
PrettyName
    Produit cartésien de deux parties
-/
begin
    todo
end

lemma exercise.produit_non_vide
(A : set X) ( B: set Y) :
(A ≠  ∅) ∧ (B ≠ ∅)  →  (set.prod A B ) ≠  ∅
:=
/- dEAduction
PrettyName
    Si les ensembles sont non vides, le produit est non vide
-/
begin
    todo,
end

lemma exercise.produit_avec_vide
(A : set X) ( B: set Y) :
(B = ∅)  →  (set.prod A B ) = ∅
:=
/- dEAduction
PrettyName
    Le produit avec l'ensemble vide est vide
-/
begin
    todo,
end

lemma exercise.produit_deux_singletons
(A : set X) ( B: set Y) (x: X) (y : Y):
(A = {x}) ∧ (B ={y})  →   ∃ z : X × Y , (set.prod A B ) = {z}
:=
/- dEAduction
PrettyName
    Le produit de deux singletons est un singleton
-/
begin
    todo,
end


lemma exercise.produit_avec_intersection
(A : set X) (B C : set Y) :
set.prod A (B ∩ C) = (set.prod A B) ∩ (set.prod A C)
:=
begin
    todo,
end


end produits_cartesiens





-----------------------------------
-----------------------------------
namespace exercices_supplementaires







lemma exercise.exercice_ensembles_4a
(A B C : set X) :
A ∩ B = A ∩ C ∧ (set.compl A) ∩ B = (set.compl A) ∩ C → B ⊆ C
:=
/- dEAduction
PrettyName
    Caractérisation par intersection avec A et son complémentaire, I
-/
begin
    todo
end

lemma exercise.exercice_ensembles_4b
(A B C : set X) :
A ∩ B = A ∩ C ∧ (set.compl A) ∩ B = (set.compl A) ∩ C → B = C
:=
/- dEAduction
PrettyName
    Caractérisaton par intersection avec A et son complémentaire, II
-/
begin
    todo
end



--def diff {X : Type} (A B : set X) := {x ∈ A | ¬ x ∈ B}
--notation A `\\` B := diff A B

-- def symmetric_difference {X : Type} (A B : set X) := (A ∪ B) \ (A ∩ B)
-- notation A `Δ` B := symmetric_difference A B




lemma definition.difference_symetrique
(A B : set X) :
(A Δ B) =  (A ∪ B) \ (A ∩ B)
:=
/- dEAduction
PrettyName
    Différence symétrique de deux ensembles
-/
begin
    refl,
end



lemma exercise.difference_symetrique_1
(A B : set X) :
(A Δ B) = (A \ B) ∪ (B \ A)
:=
/- dEAduction
PrettyName
    Différence symétrique - autre définition
-/
begin
    todo
end

lemma exercise.difference_symetrique_inter
(A B C : set X) :
(A ∩ (B Δ C)) = ((A ∩ B) Δ (A ∩ C))
:=
/- dEAduction
PrettyName
    Différence symétrique et intersection
-/
begin
    todo
end

lemma exercise.difference_symetrique_egalite
(A B C : set X) :
(A Δ C )= (B Δ C ) →  (A = B)
:=
/- dEAduction
PrettyName
    Egalité et Différence symétrique 
-/
begin
    todo
end


lemma exercise.difference_symetrique_comm
(A B : set X) :
(A Δ B) = (B Δ A)
:=
/- dEAduction
PrettyName
    Commutativité de la différence symétrique 
-/
begin
    todo
end



lemma exercise.difference_symetrique_vide
(A B : set X) :
(A Δ B) = ∅ ↔ A = B
:=
/- dEAduction
PrettyName
    Caractérisation d'une différence symétrique vide
-/
begin
    todo
end


lemma exercise.difference_symetrique_3
(A B C : set X) :
((A Δ B) Δ C) = (A Δ (B Δ C))
:=
/- dEAduction
PrettyName
    Différence symétrique d'une différence symétrique
-/
begin
    todo
end



end exercices_supplementaires


end course
