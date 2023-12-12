
import data.set
import tactic

-- dEAduction imports
import structures2
import utils          
import push_neg_once
import compute        -- tactics for computation, used by the Goal! button

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
Author
    Isabelle / inspiré du fichier tutoriel de Frédéric
Institution
    Université de Lorraine
Description
    Ce fichier, qui peut servir de tutoriel, contient quelques énoncés de logique  propositionnelle basés sur des exemples.
    Le but n'est pas de les démontrer du point de vue de la logique propositionnelle,
    mais plutôt de voir comment l'interface fonctionne sur ces énoncés.
AvailableExercises
    NONE
DefaultAvailableProof
    NONE
DefaultAvailableMagic
    Assumption
DefaultAvailableCompute
    NONE
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
-- parameters { a b x y : ℝ, c d : ℤ}

namespace decouverte_icones_logique

lemma exercise.but (Hypothese1 : m =1) (Hypothese2 : n < 2):
  m+n <3
:=
/- dEAduction
PrettyName
    Bouton BUT - Enoncé directement vrai pour le logiciel -  Entiers
Description
    Le bouton "But !" et les tactiques de simplifications automatiques disponibles 
  
AvailableLogic
    NONE
    
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.but2 { a b x y : ℝ} (Hypothese1 : x <= a) (Hypothese2 : y < b):
 x + y < a+b
:=
/- dEAduction
PrettyName
    Bouton But - Enoncé directement vrai pour le logiciel -  Réels
Description
    Le bouton "But !" et les tactiques de simplifications automatiques disponibles 
  
AvailableLogic
    NONE
    
AvailableMagic
    assumption
-/
begin
    sorry
end


lemma exercise.nonbut (Hypothese1 : m =1) (Hypothese2 : n =2):
 non( m+n  < 0 )
:=
/- dEAduction
PrettyName
    Transformation d'une proposition NON (P) dans le but - Entiers.
Description
    Découverte du connecteur NON, pour transformer le But.
AvailableLogic
    not
    
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.nonbut2 { a x y : ℝ} (Hypothese1 : a < 0 ) (Hypothese2 : x > y):
 non( a*x >= a*y )
:=
/- dEAduction
PrettyName
    Transformation d'une proposition NON (P) dans le but - Réels.
Description
    Découverte du connecteur NON, pour transformer le But.
AvailableLogic
    not
    
AvailableMagic
    assumption
-/
begin
    sorry
end



lemma exercise.nonhyp (Hypothese1 : non(non( m *m <= 1))) (Hypothese2 : (n =2) ):
 m+n  <= 4  
:=
/- dEAduction
PrettyName
    Transformation d'une proposition NON (P) dans l'hypothèse - Entiers - pas convaincant (?) 
Description
    Découverte du connecteur NON, pour transformer l'hypothèse -- trouver un autre exemple ?!
AvailableLogic
    not   
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.nonhyp2 { a  x y : ℝ} (Hypothese1 : x > y) (Hypothese2 : non (a<=2)) :
 x*a > y*a
:=
/- dEAduction
PrettyName
    Transformation d'une proposition NON (P) dans l'hypothèse  - Réels
Description
    Découverte du connecteur NON, pour transformer l'hypothèse - Autre exemple
AvailableLogic
    not   
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.nonhyp3 {  x y : ℝ} (Hypothese1 : non(2*x ≠  y +1)) (Hypothese2 : non(x ≠ 2*y) ):
 x+y =1
:=
/- dEAduction
PrettyName
    Transformation d'une proposition NON (P) dans les hypothèses  -  Réels - Deux NON
Description
    Découverte du connecteur NON, pour transformer l'hypothèse - autre exemple !
AvailableLogic
    not   
AvailableMagic
    assumption
-/
begin
    sorry
end


lemma exercise.connecteur_etdansbut (H1 : (m>2) ) (H2 : n =4) :
(m+n > 6) \and (non(m+n < 1))
:=
/- dEAduction
PrettyName
    Connecteur ET dans le but - Entiers
Description
    Le bouton "ET" permet de découper un but à atteindre contenant le connecteur ET en deux sous-buts
AvailableLogic
    and not
AvailableMagic
    assumption
-/
begin
    sorry
end



lemma exercise.connecteur_etdanshyp (H : (2*m = 6) \and (m+n > 10*n^2)) :
m*m <=10
:=
/- dEAduction
PrettyName
    Connecteur ET dans une hypothèse - Entiers
Description
    Le bouton "ET" permet de découper une hypothèse contenant le connecteur ET en deux hypothèses
AvailableLogic
    and 
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.connecteur_etdanshyp2 { x y : ℝ} (H: ((x+y)^2 =x^2 +2*(x*y) + y^2) \and ((x-y)^2 = x^2 -2*(x*y) +y^2 )) :
((x+y)^2 + (x-y)^2 = 2*(x^2 + y^2)) \and (( x+y)^2 - (x-y)^2 = 4*(x*y))
:=
/- dEAduction
PrettyName
    Connecteur ET dans une hypothèse et dans le but - Réels
Description
    Le bouton "ET" permet de découper une hypothèse contenant le connecteur ET en deux hypothèses, et  de découper un but à atteindre contenant le connecteur ET en deux sous-buts
AvailableLogic
    and 
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.connecteur_oudansbut (H1 : (m>2) ) (H2 : n =4) :
(m+n > 6) \or (m-n > 2)
:=
/- dEAduction
PrettyName
    Connecteur OU dans le but - Entiers
Description
    Le bouton "OU" permet de choisir quelle proposition peut être démontrée dans le but
AvailableLogic
      or
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.connecteur_oudanshyp (H : (m=2) \or (n=3)) :
m+n >= 1
:=
/- dEAduction
PrettyName
    Connecteur OU dans une hypothèse - Entiers
Description
    Le bouton "OU" permet de découper une hypothèse contenant le connecteur OU en deux hypothèses
AvailableLogic
    or
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.connecteur_etoudansbuthyp {a x y : ℝ} (H : (x <= y) \and ( (a<0) \or (a>0))) :
( a*x <= a*y) \or (a*y <= a*x)
:=
/- dEAduction
PrettyName
    Connecteurs ET et OU dans une hypothèse, et un OU dans un  but - Réels
Description
    Le bouton "OU" permet de découper une hypothèse contenant le connecteur OU en deux hypothèses
AvailableLogic
    or and
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.connecteur_impliquedansbut1 :
( m + n >=5) → (m+n >= 3)
:=
/- dEAduction
PrettyName
    Connecteur IMPLIQUE dans but (1) - Cas d'une proposition vraie en prémisse
Description
    Le bouton "=>" permet de démontrer une implication : pour montrer
    "P => Q", on suppose P, et on montre Q.
AvailableLogic
    implies
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.connecteur_impliquedansbut2 :
( 1 = 5 ) → (m+n >= 3)
:=
/- dEAduction
PrettyName
    Connecteur IMPLIQUE dans but (2) - Cas d'une proposition fausse en prémisse
Description
    Le bouton "=>" permet de démontrer une implication : pour montrer
    "P => Q", on suppose P, et on montre Q.
AvailableLogic
    implies
AvailableMagic
    assumption
-/
begin
    sorry
end




lemma exercise.connecteur_equal (H1:  (m+3*n =100) ) (H2 : m=10 ):
n = 30  -- utilisation de equal pour arriver au but
:=
/- dEAduction
PrettyName
   Bouton EGALITE - Substitution de valeurs de variables
Description
   
    Le bouton "=" permet de remplacer une expression par une autre qui lui est égale
AvailableLogic
     equal
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.connecteur_impliquedanshyp (H1: ( m >=5) → (m+n =100) ) (H2 : m=10 ):
10 + n = 100  -- marche, mais par contre n=90 ne fonctionne pas
:=
/- dEAduction
PrettyName
    Connecteur IMPLIQUE dans une hypothèse - Première forme
Description
    Le bouton "=>" permet d'utiliser une implication dans une hypothèse : à partir de  "P => Q" et de "P" on en déduit "Q"
AvailableLogic
    implies
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.connecteur_impliquedanshyp2 (H1: ( m >=5) → (m+n =100) ) (H2 : m=10 ):
n = 90  -- utilisation de equal pour arriver au but
:=
/- dEAduction
PrettyName
    Connecteur IMPLIQUE dans hypothèse et bouton EGALITE - Deuxième forme
Description
   Le bouton "=>" permet d'utiliser une implication dans une hypothèse : à partir de  "P => Q" et de "P" on en déduit "Q".
    
    Le bouton "=" permet de remplacer une expression par une autre qui lui est égale
AvailableLogic
    implies equal
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.ssi1 { x  : ℝ}:
( (x >= 1) \and ( x>=0 \or x <= -1)) ↔ (x >= 1)
:=
/- dEAduction
PrettyName
    Connecteur EQUIVALENT dans But
Description
    Le bouton "↔" permet de découper le but en deux implications.
AvailableLogic
    and or not implies iff
AvailableMagic
    assumption
-/
begin
    sorry
end

-- FLR: pour moi ça ne marche qu'avec le bouton '=>', pas avec '<=>' ?
-- Ou alors le bouton équivalent permet de découper en deux (et ensuite on utilise '=>'.)
lemma exercise.ssi2   (H1: m*n=0 ↔ ( m=0 \or n=0) ) 
 (H2: (m*n = 0) \or (m*n =1) \or (m*n >= 2) ) :
( non(m*n =1))→  ( (m=0) \or (n=0) \or (m*n >= 2) )
:=
/- dEAduction
PrettyName
    Connecteur EQUIVALENT dans une hypothèse
Description
    Le bouton "↔" permet d'utiliser une des implications de l'hypothèse.
AvailableLogic
    and or not implies iff
AvailableMagic
    assumption
-/
begin
    sorry
end


end decouverte_icones_logique

namespace decouverte_theoreme_definition

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
    Utilisation d'un théorème dans un but (1) - Réels
Description
    Utilisation d'un théorème dans un but
AvailableLogic
     and  implies
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.utilisation_th2b { x y : ℝ} (H : 0 <=x) :
(x <= 2) → (x^2 <= 2^2)
:=
/- dEAduction
PrettyName
    Utilisation d'un théorème dans un But (2) - Réels
Description
    Utilisation d'un théorème dans un but (2)
AvailableLogic
      and implies
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.utilisation_th2 { x y : ℝ} (H1 : 0 <=x) (H2: 2^2 = 4) :
(x <= 2) → (x^2 <= 4)
:=
/- dEAduction
PrettyName
    Utilisation d'un théorème dans un But (2bis) - Réels
Description
    Utilisation d'un théorème 2bis dans un But -- Ne marche pas !! Pourquoi ?
AvailableLogic
     and equal  implies
AvailableMagic
    assumption
-/
begin
    sorry
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
    Utilisation d'un théorème à choisir parmi deux dans un But - Réels
Description
    Utilisation d'un théorème à choisir parmi deux dans un But
AvailableLogic
      and implies
AvailableMagic
    assumption
-/
begin
    sorry
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

lemma exercise.eq1 { x y : ℝ}  :
(x-1) * x = 0 → ( (x=1) \or (x=0) )
:=
/- dEAduction
PrettyName
    Utilisation d'un théorème dans une hypothèse (1) - Equation
Description
    Utilisation d'un théorème dans une hypothèse (1) - Equation
AvailableLogic
     or  implies
AvailableTheorems
  eqproduit
AvailableMagic
    assumption

-/
begin
    sorry
end

--AvailableDefinitions
--  UNTIL_NOW -singleton -paire -identite -egalite_fonctions
--AvailableTheorems
--  UNTIL_NOW -eqproduit

lemma exercise.eq2 { x y : ℝ}  :
((x-1) * x)*y = 0 → ( (x=1) \or (x=0) \or (y=0) )
:=
/- dEAduction
PrettyName
    Utilisation d'un théorème dans une hypothèse (2) - Equation
Description
    Utilisation d'un théorème dans une hypothèse (2) - Equation
AvailableLogic
     or  implies
AvailableTheorems
  eqproduit
AvailableMagic
    assumption
-/
begin  
    sorry
end

-- def fonction (f : ℝ →  ℝ) (x  : ℝ) : ℝ := f x

def F  (x  : ℝ) : ℝ := (x-1)*(x+2)

lemma definition.F   ( x : ℝ)  :
F (x) = (x-1)*(x+2)
:=
begin
    todo,
end

lemma exercise.def  { x  : ℝ} (H: x=1) :
F (x) = 0
:=
/- dEAduction
PrettyName
    Utilisation d'une définition dans un but -- PBME AFFICHAGE F(x)
Description
    Utilisation d'une définition dans un but
AvailableLogic
     equal  implies
AvailableTheorems
  eqproduit
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.defbilan  { x  : ℝ} :
( F (x) = 0 ) \iff ( (x=1) \or (x=-2) )
:=
/- dEAduction
PrettyName
    Utilisation d'une définition, d'un théorème, et du bouton application -- PBME AFFICHAGE F(x)
Description
    Utilisation d'une définition, d'un théorème, et du bouton application
AvailableLogic
    or and equal  implies iff map
AvailableTheorems
  eqproduit
AvailableMagic
    assumption
-/
begin
    sorry
end

end decouverte_theoreme_definition


namespace Quantificateurs


lemma exercise.pourtout_hyp1 { x  : ℝ} (H: ∀ y : ℝ, y^2 = y*y ) : 
 ( (x+1)^2= 1 + 2*x +x*x)  
:=
/- dEAduction
PrettyName
    Utilisation du Pour tout dans une hypothèse (1)
Description
     Utilisation  du Pour tout dans une hypothèse (1)
AvailableLogic
    equal forall
AvailableTheorems
  NONE
AvailableDefinitions
  NONE
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.pourtout_hyp2 { x  : ℝ} (H: ∀ y : ℝ, y^2 = y*y ) : 
 ( (x+1)^2= 1 + 2*x +x^2)  
:=
/- dEAduction
PrettyName
    Utilisation du Pour tout dans une hypothèse (2)
Description
     Utilisation  du Pour tout dans une hypothèse (2)
AvailableLogic
    equal forall
AvailableTheorems
  NONE
AvailableDefinitions
  NONE
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.pourtout_but  : 
 ( ∀ x : ℝ, ∀ y : ℝ, ∀ z : ℝ, x*(y+z) = x*y +x*z )  
:=
/- dEAduction
PrettyName
    Démontrer un Pour tout dans un but
Description
      Démontrer un Pour tout dans un but
AvailableLogic
     forall
AvailableTheorems
  NONE
AvailableDefinitions
  NONE
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.pourtout_hypbut (H1: ∀ x : ℝ, x^2 = x*x ) (H2: ∀ y : ℝ, y^3 = y*y*y ) : 
 ( ∀ z : ℝ, (z+1)^3= 1 + 3*z + 3*z^2 + z^3 )  
:=
/- dEAduction
PrettyName
     Pour Tout dans but et hypothèse
Description
    Pour Tout dans but et hypothèse
AvailableLogic
    equal forall
AvailableTheorems
  NONE
AvailableDefinitions
  NONE
AvailableMagic
    assumption
-/
begin
    sorry
end


lemma exercise.ilexiste_but1 : 
 (  ∃ a  :  ℕ, a*a*a = 27  )
:=
/- dEAduction
PrettyName
    Démontrer un Il existe dans un but (1)
Description
     Démontrer un Il existe dans  un but (1)
AvailableLogic
    exists 
AvailableTheorems
  NONE
AvailableDefinitions
  NONE
AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.ilexiste_but2 : 
 (  ∃ a  :  ℕ, ∃ b  :  ℕ, (a*b=143) \and (a > b) )
:=
/- dEAduction
PrettyName
   Démontrer un Il existe dans un but (2)
Description
    Démontrer un Il existe dans  un but (2)
AvailableLogic
   exists and
AvailableTheorems
  NONE
AvailableDefinitions
  NONE
AvailableMagic
    assumption
-/
begin
    sorry
end


lemma exercise.ilexiste_hypbut { n  :  ℕ}  : 
 (  ∃ a  :  ℕ, n = 2*a ) → (  ∃ b  :  ℕ, n*n = 2*b )
:=
/- dEAduction
PrettyName
    Utilisation du bouton Il existe dans une hypothèse et un but 
Description
     Utilisation du bouton Il existe dans une hypothèse et un but 
AvailableLogic
    equal exists implies
AvailableTheorems
  NONE
AvailableDefinitions
  NONE
AvailableMagic
    assumption
-/
begin
    sorry
end


end Quantificateurs


end course
