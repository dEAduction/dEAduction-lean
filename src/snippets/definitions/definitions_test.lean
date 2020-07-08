import tactic
import data.real.basic
import data.set
import data.set.lattice
import logics
import definitions


set_option trace.simplify.rewrite true
-- set_option pp.all true


------------- Lemmes définitionnels ---------------
namespace definitions


------------ Théorie des ensembles --------------
section theorie_des_ensembles

variables {X : Type} {Y : Type}
-- mem_compl_iff
--lemma complement {A : set X} {x : X} : x ∈ - A ↔ ¬ x ∈ A :=
--iff.rfl

lemma complement {A : set X} {x : X} : x ∈ set.univ \ A ↔ x ∉ A := 
by finish

lemma complement_1 {A : set X} {x : X} : x ∈ set.compl A ↔ x ∉ A := 
by finish

lemma complement_2 {A B : set X} {x : X} : x ∈ B \ A ↔ (x ∈ B ∧ x ∉ A) :=
iff.rfl

lemma inclusion (A B : set X) : A ⊆ B ↔ ∀ {{x:X}}, x ∈ A → x ∈ B := 
iff.rfl

lemma intersection_deux  (A B : set X) (x : X) :  x ∈ A ∩ B ↔ ( x ∈ A ∧ x ∈ B) := 
iff.rfl

-- bof : ce n'est pas une définition, mais une caractérisation
lemma intersection_ensemble  (A B C : set X) : C ⊆ A ∩ B ↔ C ⊆ A ∧ C ⊆ B := 
begin
    exact ball_and_distrib
end

lemma intersection_quelconque (I : Type) (O : I → set X)  (x : X) : (x ∈ set.Inter O) ↔ (∀ i:I, x ∈ O i) :=
set.mem_Inter

-- Les deux lemmes suivants seront à regroupé au sein d'une même tactique : essayer le premier, 
-- en cas d'échec essayer le second. Un seul bouton dans l'interface graphique
lemma union  (A : set X) (B : set X) (x : X) :  x ∈ A ∪ B ↔ ( x ∈ A ∨ x ∈ B) := 
iff.rfl

lemma union_quelconque (I : Type) (O : I → set X)  (x : X) : (x ∈ set.Union O) ↔ (∃ i:I, x ∈ O i) :=
set.mem_Union


-- mem_image_iff_bex
lemma image  (A : set X)  (f : X → Y) (b : Y) : b ∈ f '' A ↔  ∃ a, a ∈ A ∧ f(a) = b :=
begin
    tidy,
end

lemma image_reciproque  {B : set Y}  {f : X → Y} {a : X} :
                             a ∈ f ⁻¹' B ↔  f a ∈ B :=
                             iff.rfl

lemma ensemble_egal {A A' : set X} : (A = A') ↔ ( ∀ x, x ∈ A ↔ x ∈ A' ) :=
by exact set.ext_iff

lemma double_inclusion {A A' : set X} : (A = A') ↔ (A ⊆ A' ∧ A' ⊆ A) :=
begin
    exact le_antisymm_iff
end


end theorie_des_ensembles

end definitions
