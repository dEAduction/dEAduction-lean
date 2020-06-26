import data.set
import tactic
import logics
import definitions
import structures


local attribute [instance] classical.prop_decidable


--------------------------------
-- Commentaire deaduc : lignes à récupérer pour structurer la liste d'exercices
-- pendant les exos qui suivent, le logiciel affichera en titre : 
-- Théorie des ensembles (1) Ensembles
-- Puis, plus loin,
-- Théorie des ensembles (2) Applications

section theorie_des_ensembles


-- Commentaire deaduc : les deux lignes qui suivent indiquent les boutons à intégrer dans les zones correspondantes
-- pour tous les exercices de la section
-- @DEFINITIONS theorie_des_ensembles
-- (inclure toutes les définitions de la section "théorie des ensemble",
-- i.e. celles dont le nom commence par "definitions.theorie_des_ensembles")
-- @LOGIQUE ∀, ∃, →, ↔, ET, OU, NON, contradiction

-----------------------------------------
-----------------------------------------
section unions_et_intersections  -- sous-section 1
-----------------------------------------
-----------------------------------------

variables {X : Type} {A B C : set X}

/- @EXERCICE : L'intersection est distributive par rapport à l'union -/
lemma union_distributive_inter : A ∩ (B ∪ C)  = (A ∩ B) ∪ (A ∩ C) := 
begin
    defi double_inclusion, ET,
    defi inclusion, qqs a, implique,
    defi intersection_deux at H,
    ET H,
    defi union at HB,
    OU HB,
      defi union, OU gauche,
      ET HA HA_1,
      defi intersection_deux at H,
      assumption,
    defi union, OU droite,
    defi intersection_deux, ET, assumption, assumption,
  defi inclusion, qqs a, implique,
  defi union at H,
  OU H,
    defi intersection_deux at HA,
    ET HA,
    OUd HB a ∈ C,  -- évitable en travaillant sur le but
    defi union at H,
    ET HA_1 H,
  defi intersection_deux at H_1,
  assumption,
  defi intersection_deux at HB,
  ET HB,
  defi intersection_deux,
  ET,
  assumption,
  defi union,
  tautology,
end

/- @EXERCICE L'union est distributive par rapport à l'intersection -/
lemma inter_distributive_union : A ∪ (B ∩ C)  = (A ∪ B) ∩ (A ∪ C) := 
begin
    sorry
end

end unions_et_intersections

-----------------------------------------
-----------------------------------------
section complementaire -- sous-section 2
-----------------------------------------
-----------------------------------------
variables {X : Type} {A B : set X}
variables {I : Type} {E F : I → set X}
-- notation X `\` A := @has_neg.neg (set X) _ A
-- notation  ` \` Z := has_neg.neg Z   
-- notation `\ ` Z := -Z

/- @EXERCICE Tout ensemble est égal au complémentaire de son complémentaire-/
lemma complement_complement : - - A =A :=
begin
    sorry
end

/- @EXERCICE Le complémentaire de l'union de deux ensembles égale l'intersection des complémentaires -/
lemma complement_union_deux : @has_neg.neg (set X) _ (A ∪ B) = (- A) ∩ (- B) :=
begin
    hypo_analysis,
    goals_analysis,
    sorry
end



/- @EXERCICE Le complémentaire d'une réunion quelconque égale l'intersection des complémentaires -/
open set
-- set_option pp.all true
lemma complement_union_quelconque  (H : ∀ i, F i = - E i) : - (Union E) = Inter F :=

begin
    hypo_analysis,
    goals_analysis,
    sorry
end

/- @EXERCICE Le complémentaire d'une intersection quelconque égale l'union des complémentaires -/
-- set_option pp.all true
lemma complement_intersection_quelconque  (H : ∀ i, F i = - E i) : - (Inter E) = Union F :=
begin   
    sorry
end
/- @EXERCICE Le complémentaire du vide est X ??? -/ 



/- @EXERCICE A est inclus dans B ssi le complémentaire de A contient le complémentaire de B -/
lemma inclus_ssi_complement_contient : A ⊆ B ↔ - B ⊆ - A :=
begin    
    hypo_analysis,
    goals_analysis,
    defi double_implication,    ET, 
        implique,
        defi inclusion, qqs a, implique, 
        defi complement,
        by_contradiction,
        -- alternative : defi inclusion at H, qqselim H a, impliqueelim H_2 a_1,
        applique H a_1,
        -- alternative : tautology, -- le contexte contient P et non P
        applique H_1 H_2, assumption,
    implique,
    defi inclusion, qqs a, implique,
    by_contradiction,
    applique H a_1,
    applique H_2 H_1, assumption,
    -- alternative :  defi inclusion at H, qqselim H a, impliqueelim H_3 H_2,
    -- tautology -- a remplacer : trop puissant !
end


/- -/
example : A ⊆ B ↔ B - A = ∅ :=
begin
    hypo_analysis,
    goals_analysis,
    sorry
end

-- Comment manipuler l'ensemble vide dans un type ?

/- Autres : différence symétrique-/




end complementaire



-- Ajouter : 3. produit cartésien, 4. relations ?
-- comment définit-on un produit cartésien d'ensembles ?



-----------------------------------------
-----------------------------------------
section applications  -- sous-section 5
-----------------------------------------
-----------------------------------------
notation f `⟮` A `⟯` := f '' A
notation f `⁻¹⟮` A `⟯` := f  ⁻¹' A

variables {X : Type} (A A': set X) 
variables {Y: Type} {f: X → Y} (B B': set Y)
variables {I : Type} {E : I → set X} {F : I → set Y}

/- @EXERCICE -/
lemma image_de_reciproque : f '' (f ⁻¹' B)  ⊆ B :=
begin
    hypo_analysis,
    goals_analysis,
    sorry
end

/- @EXERCICE -/
lemma reciproque_de_image : A ⊆ f ⁻¹' (f '' A) :=
begin
    sorry
end

/- @EXERCICE -/
lemma image_reciproque_inter :  f ⁻¹'  (B∩B') = f ⁻¹'  (B) ∩ f ⁻¹'  (B') :=
begin
    sorry
end


/- @EXERCICE -/
lemma  image_reciproque_union  : f ⁻¹' (B ∪ B') = f ⁻¹' B ∪ f ⁻¹' B'  :=
begin
    defi double_inclusion,
    ET,
        defi inclusion,
        qqs x,
        implique,
        defi image_reciproque at H,
        defi union,
        defi union at H,
        OU H,
        defi image_reciproque at HA,
        OUd HA (f x ∈ B),
            OU gauche, assumption,
        OU droite, assumption, 
-- ici assumption en fait un peu trop, 
-- on voudrait obliger à avoir appliqué la def de l'image réciproque avant
    defi inclusion, 
    qqs x,
    implique,
    defi image_reciproque,
    defi union,
    defi union at H,
    OU H,
        OU gauche, assumption,
    OU droite, assumption,
end


/- Idem union, intersection quelconques -/

/- @EXERCICE -/
lemma image_reciproque_inter_quelconque  (H : ∀ i:I,  (E i = f ⁻¹' (F i))) :  (f ⁻¹'  (set.Inter F)) = set.Inter E :=
begin
    defi double_inclusion, ET,
    {defi inclusion, qqs x,
    implique,
    defi image_reciproque at H_1,
    defi intersection_quelconque at H_1,
    defi intersection_quelconque,
    qqs i,
    applique H_1 i,
    defi image_reciproque at H_2,
    applique H i,
    rw ← H_3 at H_2,
    assumption},
    {




    }
end



/- @EXERCICE -/
lemma image_inter_inclus_inter_images   :  
        f '' (A∩A') ⊆ f '' (A) ∩ f '' (A') :=
begin
    -- Soit b un élément de  f(A'∩A)
    defi inclusion,
    qqsintro b,
    impliqueintro,
    -- ligne non indispensable :
    defi image at H,
    hypo_analysis,
    goals_analysis,
    existeelim a H, ET H,
    defi intersection_deux at HA, ET HA,
    defi intersection_deux, ET,
    defi image,
    existeintro a, ET,
    assumption, assumption,
    existeintro a, ET,
    assumption, assumption,
end

end applications

















end theorie_des_ensembles