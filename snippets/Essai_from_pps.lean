import Ensembles_et_applications
local attribute[instance] classical.prop_decidable
section course
namespace ensembles_et_applications
namespace exercices
namespace composition_et_images
open set
set_option pp.notation false
lemma exercise.ensembles_et_applications.exercices.composition_et_images.exercise.composition_image_directe
 (X: Type) (Y: Type) (Z: Type) (f: X→Y) (g: Y→Z) (A: set X) (z: Z)
 (x: X) (H4: x ∈ A) (H5: (g (f x) ) = z)  :
 z ∈ (g '' (f '' (A))) :=
begin
  have H6 : ∀ f0: X → Y, ∀ f1: Y → Z, (f1(f0(x)) = (function.comp f1 f0) x), rotate,
  -- rw H6 at H5,
  have H7 : g (f x) =z,
  rw H6 at H7,
      targets_analysis2 12,
    all_goals {hypo_analysis2 12},
end
end composition_et_images
end exercices
end ensembles_et_applications
end course