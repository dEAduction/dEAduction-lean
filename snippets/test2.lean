-- Seq num 1
import Ensembles_et_applications
import compute
section course
namespace ensembles_et_applications
namespace exercices
namespace injectivite_surjectivite_composition

open set 


set_option trace.simp_lemmas true
set_option trace.simplify true
set_option trace.debug true

@[simp]
lemma sing_rw {X : Type} {x: X}: sing x = {x} :=
begin
  refl,
end

variables (X Y: Type) (A: set X) (f: X → Y) (x: X)

example : f '' (sing x) = sing (f x) := 
begin
  repeat {rw sing},
  -- simp_rw sing_rw, --> erreur
  -- simp only [sing_rw],
  exact definitions.applications.theorem.image_singleton,
end


example (e: ℝ) (e_pos: e >0) : (2*e >0) :=
begin
  norm_num,
end
example (e: ℝ) (e_pos: e >0) : (e/(2:ℝ) >0) :=
begin
  norm_num,
end


example
 (X: Type) (Y: Type) (Z: Type) (f: X→Y) (g: Y→Z) (H1: @injective X Y f ) (H2: @injective Y Z g )  :
 @injective X Z (@composition X Y Z g f)  :=
begin
rw ensembles_et_applications.definitions.applications.definition.injectivite, intro x, no_meta_vars,
targets_analysis,
all_goals {hypo_analysis},
end
end injectivite_surjectivite_composition
end exercices
end ensembles_et_applications
end course