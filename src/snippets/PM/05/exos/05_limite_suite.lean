import «05_lib»

/-
Ce fichier concerne la définition de limite d'une suite (de nombres réels).
Une suite u est une fonction de ℕ dans ℝ, Lean écrit donc u : ℕ → ℝ
-/


-- Définition de « u tend vers l »
def limite_suite (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-
On notera dans la définition ci-dessus l'utilisation de « ∀ ε > 0, ... »
qui est une abbréviation de « ∀ ε, ε > 0 → ... ».

En particulier un énoncé de la forme « h : ∀ ε > 0, ... » se spécialise à
un ε₀ fixé par la commande « specialize h ε₀ hε₀ » où hε₀ est une démonstration
de ε₀ > 0.

Astuce : partout où Lean attend une hypothèse, on peut commencer une
démonstration à l'aide du mot clef « by », suivie de la démonstration (entourée
d'accolades si elle comporte plusieurs commandes).
Par exemple, si le contexte contient

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, ...

on peut spécialiser l'énoncé quantifié h au réel δ/2 en tapant
specialize h (δ/2) (by linarith)
où « by linarith » fournit la démonstration de δ/2 > 0 attendue par Lean.
-/

-- Dans toute la suite, u, v et w sont des suites tandis que l et l' sont des
-- nombres réels
variables (u v w : ℕ → ℝ) (l l' : ℝ)

-- Si u est constante de valeur l, alors u tend vers l
example : (∀ n, u n = l) → limite_suite u l :=
begin
  sorry
end

/- Concernant les valeurs absolues, on pourra utiliser les lemmes

abs_inferieur_ssi (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

ineg_triangle (x y : ℝ) : |x + y| ≤ |x| + |y|

abs_diff (x y : ℝ) : |x - y| = |y - x|

Il est conseillé de noter ces lemmes sur une feuille car ils
peuvent être utiles dans chaque exercice.
-/

-- Si u tend vers l strictement positif, alors u n ≥ l/2 pour n assez grand.
example (hl : l > 0) : limite_suite u l → ∃ N, ∀ n ≥ N, u n ≥ l/2 :=
begin
  sorry
end

/- Concernant le maximum de deux nombres, on pourra utiliser les lemmes

superieur_max_ssi (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

inferieur_max_gauche p q : p ≤ max p q

inferieur_max_droite p q : q ≤ max p q

Il est conseillé de noter ces lemmes sur une feuille car ils
peuvent être utiles dans chaque exercice.
-/

-- Si u tend vers l et v tend vers l' alors u+v tend vers l+l'
example (hu : limite_suite u l) (hv : limite_suite v l') :
limite_suite (u + v) (l + l') :=
begin
  -- Soit ε un réel strictement positif
  intros ε ε_pos,
  -- L'hypothèse de limite sur u, appliquée au réel strictement positif ε/2,
  -- fournit un entier N₁ tel ∀ n ≥ N₁, |u n - l| ≤ ε / 2
  cases hu (ε/2) (by linarith) with N₁ hN₁,
  -- L'hypothèse de limite sur v, appliquée au réel strictement positif ε/2,
  -- fournit un entier N₂ tel ∀ n ≥ N₂, |v n - l| ≤ ε / 2
  cases hv (ε/2) (by linarith) with N₂ hN₂,
  -- On veut un entier N tel que ∀ n ≥ N, |(u+v) n - (l+l')| ≤ ε
  -- Montrons que max N₁ N₂ convient.
  use max N₁ N₂,
  -- Soit n ≥ max N₁ N₂
  intros n hn,
  -- Par définition du max, n ≥ N₁ et n ≥ N₂
  rw superieur_max_ssi at hn,
  cases hn with hn₁ hn₂,
  -- Donc |u n - l| ≤ ε/2
  have fait₁ : |u n - l| ≤ ε/2,
    apply hN₁,
    linarith,
  -- et |v n - l| ≤ ε/2
  have fait₂ : |v n - l'| ≤ ε/2,
    exact hN₂ n (by linarith),  -- Notez la variante Lean par rapport à fait₁
  -- On peut alors calculer.
  calc
  |(u + v) n - (l + l')| = |(u n -l) + (v n -l')| : by compute
                     ... ≤ |u n - l| + |v n - l'| : by apply ineg_triangle
                     ... ≤  ε/2 + ε/2             : by linarith
                     ... =  ε                     : by compute,
end

example (hu : limite_suite u l) (hw : limite_suite w l)
(h : ∀ n, u n ≤ v n)
(h' : ∀ n, v n ≤ w n) : limite_suite v l :=
begin
  sorry

end

-- La dernière inégalité dans la définition de limite peut être remplacée par
-- une inégalité stricte.
example (u l) : limite_suite u l ↔
 ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε :=
begin
  sorry
end

/- Dans l'exercice suivant, on pourra utiliser le lemme

egal_si_abs_eps (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y
-/

-- Une suite u admet au plus une limite
example : limite_suite u l → limite_suite u l' → l = l' :=
begin
  sorry
end

-- Définition de « la suite u est croissante »
def croissante (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

-- Définition de « M est borne supérieure des termes de la suite u  »
def est_borne_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

-- Toute suite croissante ayant une borne supérieure tend vers cette borne
example (M : ℝ) (h : est_borne_sup M u) (h' : croissante u) :
limite_suite u M :=
begin
  sorry
end


