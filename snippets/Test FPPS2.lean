import Ensembles_et_applications
local attribute[instance] classical.prop_decidable
section course
namespace ensembles_et_applications
namespace exercices
namespace injectivite_surjectivite_caracterisation
open set

set_option pp.notation false
lemma exercise.ensembles_et_applications.exercices.injectivite_surjectivite_caracterisation.exercise.caracterisation_injectivite_II
 (X: Type) (Y: Type) (f: X→Y) (H1: ∀A: set X, (∀B: set X, (((f '' (A)) ⊆ (f '' (B))) → (A ⊆ B)))) (x: X) (y: X) (H2: (f x ) = (f y ))  :
 x = y :=
begin
  have H3 := @H1 ((singleton x)) ((singleton y)), no_meta_vars,
      targets_analysis2 10,
    all_goals {hypo_analysis2 10},
end
end injectivite_surjectivite_caracterisation
end exercices
end ensembles_et_applications
end course
