import data.set
import tactic

-- notation A`ᶜ` := set.compl A 

variable (X : Type)
variables (I : Type) (E F : I → set X)

lemma definition.complement (A : set X) (x : X) : x ∈ set.compl A ↔ x ∉ A := 
begin
    finish
end

lemma exercise.complement_union_quelconque  (H : ∀ i, F i = set.compl (E i)) : ∀ x : X, x ∈ set.compl (set.Union E) ↔ x ∈  set.Inter F :=
begin
    
end

-- set_option pp.all true 
example (A B : set X) (H : A = set.compl B) : ∀ x : X, x ∈ A ↔  x ∈ (set.compl B) :=
begin
    { simp_rw ← definition.complement <|> simp_rw definition.complement },
end

example (A B : set X) (H : A = set.compl B) : ∀ x : X, x ∈ A ↔ x ∈ (set.compl B) :=
begin
    intro x₁,
    { rw ← definition.complement } <|> rw definition.complement },

    sorry,
end

 