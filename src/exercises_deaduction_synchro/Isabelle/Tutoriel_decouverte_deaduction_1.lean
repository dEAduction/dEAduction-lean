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
    Tutoriel d'utilisation du logiciel dans un contexte de manipulations des entiers ou réels
    
    - Partie 1 - Découverte des icônes
Author
    Isabelle Dubois / inspiré du fichier tutoriel de Frédéric
Institution
    Université de Lorraine
Description
    Ce fichier, qui peut servir de tutoriel, contient quelques énoncés de logique  propositionnelle basés sur des exemples concrets.
    Le but n'est pas de les démontrer du point de vue de la logique propositionnelle,
    mais plutôt de voir comment l'interface fonctionne sur ces énoncés.
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




lemma exercise.but { a b x y : ℝ} (Hypothese1 : x <= a) (Hypothese2 : y < b):
 x + y < a+b
:=
/- dEAduction
PrettyName
    Bouton But - Enoncé directement vrai pour le logiciel -  Réels et inégalités
Description
    Le bouton "But !" et les tactiques de simplifications automatiques disponibles 
  
AvailableLogic
    NONE
    
AvailableMagic
    assumption
-/
begin
    todo
end



lemma exercise.nonbut { a x y : ℝ} (Hypothese1 : a < 0 ) (Hypothese2 : x > y):
 non( a*x >= a*y )
:=
/- dEAduction
PrettyName
    Transformation d'une proposition NON (P) dans le but - Réels et inégalités.
Description
    Découverte du connecteur NON, pour transformer le But.
AvailableLogic
    not
    
AvailableMagic
    assumption
-/
begin
    todo
end



lemma exercise.nonhyp { a  x y : ℝ} (Hypothese1 : x > y) (Hypothese2 : non (a<=2)) :
 x*a > y*a
:=
/- dEAduction
PrettyName
    Transformation d'une proposition NON (P) dans l'hypothèse  - Réels et inégalités
Description
    Découverte du connecteur NON, pour transformer une hypothèse.
AvailableLogic
    not   
AvailableMagic
    assumption
-/
begin
    todo
end


lemma exercise.connecteur_etdansbut (H1 : (m>2) ) (H2 : n =4) :
(m+n > 6) \and (non(m+n < 1))
:=
/- dEAduction
PrettyName
    Connecteur ET dans le but - Entiers et inégalités
Description
    Le bouton "ET" permet de découper un but à atteindre contenant le connecteur ET en deux sous-buts.
AvailableLogic
    and not
AvailableMagic
    assumption
-/
begin
    todo
end



lemma exercise.connecteur_etdanshyp (H : (2*m = 6) \and (m+n > 10*n^2)) :
m*m <=10
:=
/- dEAduction
PrettyName
    Connecteur ET dans une hypothèse - Entiers
Description
    Le bouton "ET" permet de découper une hypothèse contenant le connecteur ET en deux hypothèses.
AvailableLogic
    and 
AvailableMagic
    assumption
-/
begin
    todo
end


lemma exercise.connecteur_oudansbut (H1 : (m>2) ) (H2 : n =4) :
(m+n > 6) \or (m-n > 2)
:=
/- dEAduction
PrettyName
    Connecteur OU dans le but - Entiers et inégalités.
Description
    Le bouton "OU" permet de choisir quelle proposition peut/doit être démontrée dans le but.
AvailableLogic
      or
AvailableMagic
    assumption
-/
begin
    todo
end

lemma exercise.connecteur_oudanshyp (H : (m=2) \or (n=3)) :
m+n >= 1
:=
/- dEAduction
PrettyName
    Connecteur OU dans une hypothèse - Entiers
Description
    Le bouton "OU" permet de découper une hypothèse contenant le connecteur OU en deux hypothèses successives.
AvailableLogic
    or
AvailableMagic
    assumption
-/
begin
    todo
end

lemma exercise.connecteur_etoudansbuthyp {a x y : ℝ} (H : (x <= y) \and ( (a<0) \or (a>0))) :
( a*x <= a*y) \or (a*y <= a*x)
:=
/- dEAduction
PrettyName
    Connecteurs ET et OU dans une hypothèse, et un OU dans un  but - Réels et inégalités
Description
    Utilisation des boutons "ET" et "OU" combinés.
AvailableLogic
    or and
AvailableMagic
    assumption
-/
begin
    todo
end

lemma exercise.connecteur_impliquedansbut1 :
( m + n >=5) → (m+n >= 3)
:=
/- dEAduction
PrettyName
    Connecteur IMPLIQUE dans but (1) - Cas d'une proposition vraie en prémisse.
Description
    Le bouton "=>" permet de démontrer une implication : pour démontrer
    "P => Q", on suppose P, et on montre Q.
AvailableLogic
    implies
AvailableMagic
    assumption
-/
begin
    todo
end

lemma exercise.connecteur_impliquedansbut2 :
( 1 = 5 ) → (m+n >= 3)
:=
/- dEAduction
PrettyName
    Connecteur IMPLIQUE dans but (2) - Cas d'une proposition fausse en prémisse
Description
    Le bouton "=>" permet de démontrer une implication : pour démontrer
    "P => Q", on suppose P, et on montre Q. Attention : Si P est fausse, alors l'implication "P => Q" est vraie, quelle que soit la proposition Q.
AvailableLogic
    implies
AvailableMagic
    assumption
-/
begin
    todo
end




lemma exercise.connecteur_equal (H1:  (m+3*n =100) ) (H2 : m=10 ):
n = 30  -- utilisation de equal pour arriver au but
:=
/- dEAduction
PrettyName
   Bouton EGALITE - Substitution de valeurs de variables
Description
   
    Le bouton "=" permet de remplacer une expression par une autre qui lui est égale.
AvailableLogic
     equal
AvailableMagic
    assumption
-/
begin
    todo
end

lemma exercise.connecteur_impliquedanshyp (H1: ( m >=5) → (m+n =100) ) (H2 : m=10 ):
10 + n = 100  -- marche, mais par contre n=90 ne fonctionne pas
:=
/- dEAduction
PrettyName
    Connecteur IMPLIQUE dans une hypothèse - Première forme
Description
    Le bouton "=>" permet d'utiliser une implication dans une hypothèse : à partir de  "P => Q" et de "P" on en déduit "Q".
AvailableLogic
    implies
AvailableMagic
    assumption
-/
begin
    todo
end

lemma exercise.connecteur_impliquedanshyp2 (H1: ( m >=5) → (m+n =100) ) (H2 : m=10 ):
n = 90  -- utilisation de equal pour arriver au but
:=
/- dEAduction
PrettyName
    Connecteur IMPLIQUE dans hypothèse et bouton EGALITE - Deuxième forme
Description
   Le bouton "=>" permet d'utiliser une implication dans une hypothèse : à partir de  "P => Q" et de "P" on en déduit "Q".
    
    Le bouton "=" permet de remplacer une expression par une autre qui lui est égale.
AvailableLogic
    implies equal
AvailableMagic
    assumption
-/
begin
    todo
end

lemma exercise.ssi1 { x  : ℝ}:
( (x >= 1) \and ( x>=0 \or x <= -1)) ↔ (x >= 1)
:=
/- dEAduction
PrettyName
    Connecteur EQUIVALENT dans But
Description
    Le bouton "<=>" permet de découper le but en deux implications à démontrer.
AvailableLogic
    and or not implies iff
AvailableMagic
    assumption
-/
begin
    todo
end

lemma exercise.ssi2   (H1: m*n=0 ↔ ( m=0 \or n=0) ) 
 (H2: (m*n = 0) \or (m*n =1) \or (m*n >= 2) ) :
( non(m*n =1))→  ( (m=0) \or (n=0) \or (m*n >= 2) )
:=
/- dEAduction
PrettyName
    Connecteur EQUIVALENT dans une hypothèse
Description
    Le bouton "<=>" permet d'utiliser une des implications de l'hypothèse.
AvailableLogic
    and or not implies iff
AvailableMagic
    assumption
-/
begin
    todo
end

end course

