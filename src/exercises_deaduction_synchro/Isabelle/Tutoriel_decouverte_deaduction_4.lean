import data.set
import tactic
import data.real.basic
import real_definitions
import set_definitions

-- dEAduction imports
import structures2
import utils          
import push_neg_once
import compute          -- tactics for computation, used by the Goal! button
-- import induction




-- General principles :
-- Type should be defined as parameters, in order to be implicit everywhere
-- other parameters are implicit in definitions, i.e. defined using '{}' (e.g. {A : set X} )
-- but explicit everywhere else, i.e. defined using '()' (e.g. (A : set X) )
-- each definition must be an iff statement (since it will be called with 'rw' or 'symp_rw')


/- dEAduction
Title
    Tutoriel d'utilisation du logiciel dans un contexte de manipulations des entiers ou réels - Partie 4 : Méthodes de preuves
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
DefaultAvailableLogic
    ALL -mapsto
DefaultAvailableProof
    proof_methods 
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
open set
parameters {X : Type}

variables (P Q R: Prop) -- NOT global
notation [parsing_only] P ` \and ` Q := P ∧ Q
notation [parsing_only]  P ` \or ` Q := P ∨ Q
notation [parsing_only]  ` \not ` P := ¬ P
notation [parsing_only]  P ` \implies ` Q := P → Q
notation [parsing_only]  P ` \iff ` Q := P ↔ Q

parameters {m n k: ℕ}

namespace decouverte_methodes_preuves
/- dEAduction
PrettyName
 Découverte des méthodes de preuves
-/

lemma exercise.cas1 (H1 : m*m = n*m) (H2: ( (m*m = m*n) \and non(m=0) ) → (m=n) ) :
  (m=0) \or (m=n)
:=
/- dEAduction
PrettyName
    Raisonnement par cas (1) -  Entiers  
Description
    Raisonnement par cas (1) : on choisira de discuter suivant la valeur de m
  
AvailableMagic
    assumption
-/
begin
    todo
end


lemma exercise.cas2 { x : ℝ} (H1 : |x-1| +|2*x-3| =6)  (H2: ∀ y : ℝ, (y>=0) → ( | y| =y) ) (H3: ∀ y : ℝ, (y<0) → ( | y| = -y) ) (H4 : (x-1 <0)→ (2*x - 3<0) ) :
( x=10/3 ) \or (x = -2/3)
:=
/- dEAduction
PrettyName
    Raisonnement par cas (2) -  Réels 
Description
    Raisonnement par cas (2) (et contradiction dans hypothèses) -  Réels - Défi : Se ramener à 3 cas seulement !
AvailableProof
   proof_methods

AvailableMagic
    assumption
-/
begin
    todo
end

-- ( not(x=-3)) → (not( (x+1)/(x+3) = 1)) 

lemma exercise.contraposee0 { x y : ℝ} :
 ( not(x=y)) → (not( (x-1)*(y+1) = (x+1)*(y-1)))
:=
/- dEAduction
PrettyName
    Raisonnement par contraposée (0) - Réels.
Description
    Raisonnement par contraposée - Réels

AvailableMagic
    assumption
-/
begin
    todo
end

lemma exercise.contraposee0b { x y : ℝ} (H1: ∀ a : ℝ, ∀ b : ℝ, (a+a*b =a*(1+b))) (H2: ∀ a : ℝ, ∀ b : ℝ,  (a*b +b = (a+1)*b)) (H3:  ∀ a : ℝ, ∀ b : ℝ, ( (a*b = 0)  → ( (a=0) \or (b=0) ) ) ):
 ( not(x=-1) \and not(y=-1) ) → (not( (x+ x*y)+ (1+ y) =0))
:=
/- dEAduction
PrettyName
    Raisonnement par contraposée (0 bis) - Réels.
Description
    Raisonnement par contraposée (0 bis) - Réels 

AvailableMagic
    assumption
-/
begin
    todo
end


def pair (m: nat) := ∃ k, m = 2*k 

def impair (m: nat) := ∃ k, m = 2*k + 1 



lemma definition.pair {m:nat} : (pair m) ↔ ∃ k, m = 2*k :=
/- dEAduction
PrettyName
  Pair
ImplicitUse
  True
-/
begin
  todo
end

lemma definition.impair {m:nat} : (impair m) ↔ ∃ k, m = 2*k + 1 :=
/- dEAduction
PrettyName
  Impair
ImplicitUse
  True
-/
begin
  todo
end

lemma theorem.nonimpair {m:nat} : (non((impair m))) ↔ (pair m) :=
/- dEAduction
PrettyName
  Non (Impair )
ImplicitUse
  True
-/
begin
 todo
end

lemma theorem.nonpair {m:nat} : (non((pair m))) ↔ (impair m) :=
/- dEAduction
PrettyName
  Non (Pair )
ImplicitUse
  True
-/
begin
 todo
end


lemma exercise.contraposee1  { n : ℕ}:
 (  impair (n*n) ) → (impair n )
:=
/- dEAduction
PrettyName
    Raisonnement par contraposée (1) - Entiers.
Description
    Raisonnement par contraposée (1) - Entiers - Parité.

AvailableMagic
    assumption
-/
begin
    todo
end

lemma exercise.contraposee2  { n : ℕ}:
 (  pair (n*n) ) → (pair n )
:=
/- dEAduction
PrettyName
    Raisonnement par contraposée (2) - Entiers
Description
    Raisonnement par contraposée (2) - Entiers - Parité.

AvailableMagic
    assumption
-/
begin
    todo
end



lemma exercise.contraposee3 { a  : ℝ} :
 (  ∀ y > (0:ℝ), a <= y) → (a<=0)
:=
/- dEAduction
PrettyName
    Raisonnement par contraposée  - Réels.
Description
    Raisonnement par contraposée  - Réels.
AvailableDefinitions
	NONE
AvailableTheorems
	NONE
AvailableMagic
    assumption
-/
begin
    todo
end


lemma exercise.absurde1 { x  : ℝ} (H1: not(x=-3) ) (H2: ∀ a : ℝ, ∀ b : ℝ,  ((a/b = 1) \and (not(b=0)) ) ↔ (a =b ) ) (H3: ∀ a : ℝ, ( not( x+a =0)) ↔ not (x = -a) ):
not( (x+1) / (x+3) =1 )
:=
/- dEAduction
PrettyName
    Raisonnement par l'absurde (1) - Réels
Description
    Raisonnement par l'absurde (1) - Réels
AvailableDefinitions
	NONE
AvailableTheorems
	NONE
AvailableMagic
    assumption
-/
begin
    todo
end


end

lemma theorem.produit_egal_un {m n :ℤ} : (m*n = 1)  <-> (( (m=1 ) \and (n=1) ) \or ( (m=-1) \and (n=-1) ) )  :=
/- dEAduction
PrettyName
  Produit d'entiers relatif égal à 1
ImplicitUse
  True
-/
begin
 todo
end

lemma exercise.absurde2   {m n : ℤ}  
 :
non(18*m +6*n = 1)

:=
/- dEAduction
PrettyName
     Raisonnement par l'absurde (2) - Entiers relatifs
Description
     Raisonnement par l'absurde (2) - Entiers relatifs - Attention : Introduire un nouveau but si nécessaire !
AvailableDefinitions
	NONE
AvailableTheorems
	produit_egal_un

AvailableProof
    proof_methods new_object
AvailableMagic
    assumption
-/
begin
    todo
end

lemma theorem.identite_remarquable {a b : ℤ}  :  a^2 - b^2 = (a-b)*(a+b) :=
/- dEAduction
PrettyName
  Identité Remarquable a^2 -b^2
ImplicitUse
  True
-/
begin
 todo
end

lemma exercise.absurde3  {n : ℤ}  (Hypothese: non(n=0)) 

:
non(∃ m, n^2 +1 = m^2)
:=
/- dEAduction
PrettyName
     Raisonnement par l'absurde (3) - Entiers 
Description
     Raisonnement par l'absurde (3) - Entiers  - Attention : Introduire un nouveau but si nécessaire !
AvailableDefinitions
	NONE
AvailableTheorems
	produit_egal_un, identite_remarquable
AvailableProof
    proof_methods new_object
AvailableMagic
    assumption
-/
begin
    todo
end


def estquotiententier (m: nat) (n: nat) :=
 ∃ k : ℕ, m = k*n

lemma definition.estquotiententier {m: nat} {n: nat} : 
(estquotiententier m n ) ↔ (∃ k : ℕ, m = k*n) 
:=
/- dEAduction
PrettyName
  Est Quotient entier
ImplicitUse
  True
-/
begin
 todo
end



lemma exercise.absurde4  {m n : ℕ}  (H1: ∀ n :ℕ, (∃ k, n = 2*k ) ↔ pair n ) (H2: ∀ k : ℕ, ∀ l : ℕ, k*(2*l) =2*(k*l) ) (H3: pair m) (H4: impair n) :
non(estquotiententier n m )
:=
/- dEAduction
PrettyName
     Raisonnement par l'absurde (4) - bugs sur la version tout-en-un
Description
     Raisonnement par l'absurde (4) - bugs sur la version tout-en-un

AvailableMagic
    assumption
-/
begin
    sorry
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
    todo
end

lemma definition.ensemble_non_vide
(A: set X) :
(non (A = ∅) ) ↔ ∃ x : X, x ∈ A
:=
/- dEAduction
ImplicitUse
  True
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
    todo
end

lemma exercise.absurde5
{A B : set X} :
A  ∩ ( B \ A)  = ∅ 
:=
/- dEAduction
PrettyName
     Raisonnement par l'absurde (5) - Ensembles  
Description
     Raisonnement par l'absurde (5) - Ensembles  
AvailableTheorems
	NONE
AvailableDefinitions
	intersection_deux_ensembles, difference, ensemble_non_vide	
AvailableProof
    proof_methods
AvailableMagic
    assumption
-/
begin
    todo
end




end decouverte_methodes_preuves



end course

