import data.set
import tactic

-- dEAduction imports
import logics
import structures
import definitions

-- @Definitions
import definitions_test



/-
@Macro STANDARD_LOGIC = ∀, ∃, →, ↔, ET, OU, NON, \
Absurde, Contraposée, Par_cas, Choix
-/

section unions_et_intersections -- sous-section 1



/- 
@Exercise
@Title = Intersection d'unions
@Description = L'intersection est distributive par rapport à l'union \
et ça continue sur la ligne suivante
@Buttons LOGIC = STANDARD_LOGIC +Contradiction -Choix \
+Toto
@Buttons DEFINITIONS = union, intersection
@Buttons       THEOREM    =   Zorn
@ExpectedVariables = X=3 A=2
-/
lemma union_distributive_inter (X : Type) (A B C : set X) : A ∩ (B ∪ C)  = (A ∩ B) ∪ (A ∩ C) := 
begin
    sorry
end    


variables {X : Type} {A B C : set X}

/- 
@Exercise 
@Title = Union d'intersections
@Description = L'union est distributive par rapport à l'intersection 
@Macro LOGIC = LOGIC -Par_cas
-/
lemma inter_distributive_union : A ∪ (B ∩ C)  = (A ∪ B) ∩ (A ∪ C) := 
begin
    hypo_analysis,
    goals_analysis,
    sorry
end

end unions_et_intersections

-----------------------------------------
-----------------------------------------
section complementaires -- sous-section 2


variables {X : Type} {A : set X}


/- 
@Exercise 
@Title = Complémentaire du complémentaire
@Description = Tout ensemble est égal au complémentaire de son complémentaire \
et réciproquement.
-/
lemma complement_complement : - - A =A :=
begin
    hypo_analysis,
    goals_analysis,
    sorry
end

end complementaires

