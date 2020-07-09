import data.set
import tactic

-- dEAduction imports
import logics
import structures
import definitions

import definitions_test

/- dEAduction
STANDARD_LOGIC 
    ∀, ∃, →, ↔, ET, OU, NON, 
    Absurde, Contraposée, Par_cas, Choix
-/


----------------------------------------------
namespace set_theory -- Course title
/- dEAduction
Section
    Theory
-/
----------------------------------------------
namespace unions_and_intersections -- section 1
/- dEAduction
Section
    Unions and intersections
-/


lemma exercise.union_distributive_inter (X : Type) (A B C : set X) : A ∩ (B ∪ C)  = (A ∩ B) ∪ (A ∩ C) := 
/- dEAduction
Title  
    Intersection d'unions
Description 
    L'intersection est distributive par rapport à l'union
    et ça continue sur la ligne suivante
Tools->Logic
    STANDARD_LOGIC +Contradiction -Choix
    +Toto
Tools->Statements
    union, intersection
    Zorn
ExpectedVariables 
    X=3, A=1, B=1
-/
begin
    sorry,
end    


variables {X : Type} {A B C : set X}

lemma exercise.inter_distributive_union : A ∪ (B ∩ C)  = (A ∪ B) ∩ (A ∪ C) := 
/- dEAduction
Title 
    Union d'intersections
Description 
    L'union est distributive par rapport à l'intersection 
Tools->Logic 
    STANDARD_LOGIC -Par_cas
-/
begin
    hypo_analysis,
    goals_analysis,
    sorry
end

end unions_and_intersections

-----------------------------------------
namespace complements -- section 2
/- dEAduction
section
    Complement
-/


variables {X : Type} {A : set X}


lemma exercise.complement_complement : - - A =A :=
/- dEAduction
Title 
    Complémentaire du complémentaire
Description 
    Tout ensemble est égal au complémentaire de son complémentaire 
    et réciproquement.
-/
begin
    hypo_analysis,
    goals_analysis,
    print_all_definitions,
    print_all_exercises,
    print_all_theorems,
    sorry
end

end complements

end set_theory