import tactic

-- dEAduction imports
import structures


local attribute [instance] classical.prop_decidable
section all_course
parameters (P Q : Prop)


namespace calcul_propositionnel


namespace connecteurs_logiques

lemma et (H:P) (H':Q): P ∧ Q :=
/- dEAduction
PrettyName
    Utilisation du bouton ET
Description
    Deux façons d'utiliser le bouton ET : 
    sur le but ou en sélectionnant deux hypothèses
-/
begin
    sorry
end









end connecteurs_logiques

namespace theoremes






end theoremes

end calcul_propositionnel





namespace theorie_des_ensemble

example (X Y : Type) (f : X → Y) (x x' : X) : x = x' → f x = f x' :=
begin
    intro H,
    have H' := congr_arg f H,
end


end theorie_des_ensemble
end all_course












