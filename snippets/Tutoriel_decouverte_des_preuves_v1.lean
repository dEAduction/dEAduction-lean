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
    Tutoriel d'utilisation du logiciel dans un contexte de manipulations des entiers ou réels - Partie II : Méthodes de preuves
Author
    Isabelle / inspiré du fichier tutoriel de Frédéric
Institution
    Université de Lorraine
Description
    Ce fichier, qui peut servir de tutoriel, contient quelques énoncés de logique  propositionnelle basés sur des exemples concrets.
    Le but n'est pas de les démontrer du point de vue de la logique propositionnelle,
    mais plutôt de voir comment l'interface fonctionne sur ces énoncés.
AvailableExercises
    NONE
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

variables (P Q R: Prop) -- NOT global
notation [parsing_only] P ` \and ` Q := P ∧ Q
notation [parsing_only]  P ` \or ` Q := P ∨ Q
notation [parsing_only]  ` \not ` P := ¬ P
notation [parsing_only]  P ` \implies ` Q := P → Q
notation [parsing_only]  P ` \iff ` Q := P ↔ Q

parameters {m n k: ℕ}
-- parameters { a b x y : ℝ, c d : ℤ}

namespace decouverte_methodes_preuves

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
    sorry
end

lemma exercise.but2 { x : ℝ} (H1 : |x-1| +|2*x-3| =6)  (H2: ∀ y : ℝ, (y>=0) → ( | y| =y) ) (H3: ∀ y : ℝ, (y<0) → ( | y| = -y) ) :
( x=10/3 ) \or (x = -2/3)
:=
/- dEAduction
PrettyName
    Raisonnement par cas (2) -  Réels 
Description
    Raisonnement par cas (2) -  Réels 
AvailableProof
   proof_methods

AvailableMagic
    assumption
-/
begin
      cases (classical.em ((x-1)>=0)) with H3 H4, rotate,
      push_neg_once at H4,
have
end

lemma exercise.but3 { x : ℝ} (H1 : |x-1| +|2*x-3| =6)  (H2: ∀ y : ℝ, (y>=0) → ( | y| =y) ) (H3: ∀ y : ℝ, (y<0) → ( | y| = -y) ) (H4 : (x-1 <0)→ (2*x - 3<0) ) :
( x=10/3 ) \or (x = -2/3)
:=
/- dEAduction
PrettyName
    Raisonnement par cas (2bis) -  Réels 
Description
    Raisonnement par cas (2bis) et ABSURDE -  Réels - Défi : Se ramener à 3 cas seulement !
AvailableProof
   proof_methods

AvailableMagic
    assumption
-/
begin
    sorry
end

-- ( not(x=-3)) → (not( (x+1)/(x+3) = 1)) 

lemma exercise.contraposee0 { x y : ℝ} :
 ( not(x=y)) → (not( (x-1)*(y+1) = (x+1)*(y-1)))
:=
/- dEAduction
PrettyName
    Contraposée (0) - Réels.
Description
    Raisonnement par Contraposée 

AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.contraposee0b { x y : ℝ} (H1: ∀ a : ℝ, ∀ b : ℝ, (a+a*b =a*(1+b))) (H2: ∀ a : ℝ, ∀ b : ℝ,  (a*b +b = (a+1)*b)) (H3:  ∀ a : ℝ, ∀ b : ℝ, ( (a*b = 0)  → ( (a=0) \or (b=0) ) ) ):
 ( not(x=-1) \and not(y=-1) ) → (not( (x+ x*y)+ (1+ y) =0))
:=
/- dEAduction
PrettyName
    Contraposée (0 bis) - Réels.
Description
    Raisonnement par Contraposée 

AvailableMagic
    assumption
-/
begin
    sorry
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
  refl
end

lemma definition.impair {m:nat} : (impair m) ↔ ∃ k, m = 2*k + 1 :=
/- dEAduction
PrettyName
  Impair
ImplicitUse
  True
-/
begin
  refl
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
    Contraposée (1) - Entiers.
Description
    Raisonnement par Contraposée - Entiers.

AvailableMagic
    assumption
-/
begin
    sorry
end

lemma exercise.contraposee2  { n : ℕ}:
 (  pair (n*n) ) → (pair n )
:=
/- dEAduction
PrettyName
    Contraposée (2) - Entiers.
Description
    Raisonnement par Contraposée - Entiers.

AvailableMagic
    assumption
-/
begin
    sorry
end



lemma exercise.contraposee3 { a  : ℝ} :
 (  ∀ y : ℝ, a <= y) → (a<=0)
:=
/- dEAduction
PrettyName
    Contraposée - Réels.
Description
    Contraposée

AvailableMagic
    assumption
-/
begin
    sorry
end


lemma exercise.absurde1 { x  : ℝ} (H1: not(x=-3) ) (H2: ∀ a : ℝ, ∀ b : ℝ,  ((a/b = 1) \and (not(b=0)) ) ↔ (a =b ) ) (H3: ∀ a : ℝ, ( not( x+a =0)) ↔ not (x = -a) ):
not( (x+1) / (x+3) =1 )
:=
/- dEAduction
PrettyName
    Raisonnement par l'absurde (1)
Description
    Raisonnement par l'absurde (1)

AvailableMagic
    assumption
-/
begin
    sorry
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




lemma exercise.absurde2  {m n : ℕ}  (H1: ∀ n :ℕ, (∃ k, n = 2*k ) ↔ pair n ) (H2: ∀ k : ℕ, ∀ l : ℕ, k*(2*l) =2*(k*l) ) (H3: pair m) (H4: impair n) :
non(estquotiententier n m )
:=
/- dEAduction
PrettyName
     Raisonnement par l'absurde (2) - bugs sur la version tout-en-un
Description
     Raisonnement par l'absurde (2) - bugs sur la version tout-en-un

AvailableMagic
    assumption
-/
begin
    todo
end

end decouverte_methodes_preuves





end course

