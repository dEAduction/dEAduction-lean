import data.set
import tactic

-- dEAduction imports
import structures2
import utils          
import push_neg_once
import compute          -- tactics for computation, used by the Goal! button

import data.real.basic
import real_definitions

-- General principles :
-- Type should be defined as parameters, in order to be implicit everywhere
-- other parameters are implicit in definitions, i.e. defined using '{}' (e.g. {A : set X} )
-- but explicit everywhere else, i.e. defined using '()' (e.g. (A : set X) )
-- each definition must be an iff statement (since it will be called with 'rw' or 'symp_rw')


/- dEAduction
Title
    Tutoriel d'utilisation du logiciel dans un contexte de manipulations des entiers ou réels  - Partie 3 - Découverte des Définitions et Théorèmes
Author
    Isabelle Dubois / inspiré du fichier tutoriel de Frédéric
Institution
    Université de Lorraine
Description
    Ce fichier, qui peut servir de tutoriel, contient quelques énoncés de logique  propositionnelle basés sur des exemples concrets.
    Le but n'est pas de les démontrer du point de vue de la logique propositionnelle,
    mais plutôt de voir comment l'interface fonctionne sur ces énoncés.
DefaultAvailableLogic
    ALL -map
AvailableExercises
    NONE
DefaultAvailableProof
    NONE
DefaultAvailableMagic
    Assumption
-/


-- logic names ['and', 'or', 'not', 'implies', 'iff', 'forall', 'exists']
-- proofs names ['proof_methods', 'new_object', 'apply']
-- magic names ['compute', 'assumption']


local attribute [instance] classical.prop_decidable
---------------------------------------------
-- global parameters = implicit variables --
---------------------------------------------
section course
open nat

variables (P Q R: Prop) -- NOT global
notation [parsing_only] P ` \and ` Q := P ∧ Q
notation [parsing_only]  P ` \or ` Q := P ∨ Q
notation [parsing_only]  ` \not ` P := ¬ P
notation [parsing_only]  P ` \implies ` Q := P → Q
notation [parsing_only]  P ` \iff ` Q := P ↔ Q

parameters {m n k: ℕ}


lemma theorem.croissance1 
{ x y : ℝ} :
((0 <= x) \and (0<=y) \and (x <=y)) → x^2 <= y^2
:=
/- dEAduction
PrettyName
  Croissance de la fonction carré - Réels positifs
-/
begin
  todo
end

lemma exercise.utilisation_th { x y : ℝ} (H : 0 <=x)  :
(x <= y) → ((0<=y) \and (x^2 <= y^2))
:=
/- dEAduction
PrettyName
    Utilisation d'un théorème dans le but - Fonction carrée. 
Description
    Utilisation d'un théorème dans le but - Fonction carrée. 

AvailableLogic
     and  implies
AvailableMagic
    assumption
-/
begin
    todo
end


lemma theorem.decroissance 
{ x y : ℝ} :
((x <= 0) \and (y<=0) \and (x <=y)) → y^2 <= x^2
:=
/- dEAduction
PrettyName
  Décroissance de la fonction carré - Réels négatifs
-/
begin
  todo
end

lemma exercise.utilisation_thd2 { x y : ℝ} (H : x <=0)  :
(x <= -2) → ((-2)^2 <= x^2)
:=
/- dEAduction
PrettyName
    Utilisation d'un théorème à choisir parmi deux dans le But - Fonction carrée.
Description
    Utilisation d'un théorème à choisir parmi deux dans le But - Fonction carrée.
AvailableLogic
      and implies
AvailableMagic
    assumption
-/
begin
    todo
end

lemma theorem.eqproduit 
{ x y : ℝ} :
(x*y=0) → ( (x=0) \or (y=0) )
:=
/- dEAduction
PrettyName
  Equation produit
-/
begin
  todo
end





lemma exercise.eq2 { x y : ℝ}  :
((x-1) * x)*y = 0 → ( (x=1) \or (x=0) \or (y=0) )
:=
/- dEAduction
PrettyName
    Utilisation d'un théorème dans une hypothèse  - Equation
Description
    Utilisation d'un théorème dans une hypothèse - Equation.
AvailableLogic
     or  implies
AvailableTheorems
  eqproduit
AvailableMagic
    assumption
-/
begin
    todo
end



def F  (x  : ℝ) : ℝ := (x-1)*(x+2)

lemma definition.F   ( x : ℝ)  :
F (x) = (x-1)*(x+2)
:=
begin
    todo
end

lemma exercise.def  { x  : ℝ} (H: x=1) :
F (x) = 0
:=
/- dEAduction
PrettyName
    Utilisation d'une définition dans un but -- PBME AFFICHAGE F(x)
Description
    Utilisation d'une définition dans un but -- PBME AFFICHAGE F(x)
AvailableLogic
     equal  implies
AvailableTheorems
  eqproduit
AvailableMagic
    assumption
-/
begin
    todo
end

lemma exercise.defbilan  { x  : ℝ} :
( F (x) = 0 ) \iff ( (x=1) \or (x=-2) )
:=
/- dEAduction
PrettyName
    Utilisation d'une définition, d'un théorème -- PBME AFFICHAGE F(x)
Description
    Utilisation d'une définition, d'un théorème -- PBME AFFICHAGE F(x)
AvailableLogic
    or and equal  implies iff 
AvailableTheorems
  eqproduit
AvailableMagic
    assumption
-/
begin
    todo
end



end course

