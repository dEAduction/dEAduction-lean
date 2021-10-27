import «08_lib» analysis.specific_limits

def majorant (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x
def borne_sup (A : set ℝ) (x : ℝ) := majorant A x ∧ ∀ y, majorant A y → x ≤ y

lemma lt_sup {A : set ℝ} {x : ℝ} (hx : borne_sup A x) :
∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  -- sorry
  intro y,
  contrapose!,
  exact hx.right y,
  -- sorry
end

lemma inferieur_si_inferieur_plus_eps {x y : ℝ} :
  (∀ ε > 0, y ≤ x + ε) →  y ≤ x :=
begin
  -- sorry
  contrapose!,
  intro h,
  use (y-x)/2,
  split,
    linarith,
  linarith,
  -- sorry
end

-- Si u tend vers x et u_n ≤ y pour tout n alors x ≤ y.
lemma lim_le {x y : ℝ} {u : ℕ → ℝ} (hu : limite_suite u x)
  (ineg : ∀ n, u n ≤ y) : x ≤ y :=
begin
  -- sorry
  apply inferieur_si_inferieur_plus_eps,
  intros ε ε_pos,
  cases hu ε ε_pos with N hN,
  specialize hN N (by linarith),
  specialize ineg N,
  rw abs_inferieur_ssi at hN,
--  cases hN,
  linarith',
  -- sorry
end

def limite_infinie_suite (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A

lemma limite_infinie_pas_finie {u : ℕ → ℝ} :
  limite_infinie_suite u → ∀ x, ¬ limite_suite u x :=
begin
  -- sorry
  intros lim_infinie x lim_x,
  cases lim_x 1 (by linarith) with N hN,
  cases lim_infinie (x+2) with N' hN',
  let N₀ := max N N',
  specialize hN N₀ (inferieur_max_gauche _ _),
  specialize hN' N₀ (inferieur_max_droite _ _),
  rw abs_inferieur_ssi at hN,
  linarith',
  -- sorry
end

lemma inv_succ_pos : ∀ n : ℕ, 1/(n + 1 : ℝ) > 0 :=
by apply nat.one_div_pos_of_nat

lemma limite_inv_succ :  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε :=
begin
  convert metric.tendsto_at_top.mp (tendsto_one_div_add_at_top_nhds_0_nat),
  apply propext,
  simp only [real.dist_eq, sub_zero],
  split,
    intros h ε ε_pos,
    cases h (ε/2) (by linarith) with N hN,
    use N,
    intros n hn,
    rw abs_of_pos (inv_succ_pos n),
    specialize hN n hn,
    linarith,
  intros h ε ε_pos,
  cases h ε (by linarith) with N hN,
  use N,
  intros n hn,
  specialize hN n hn,
  rw abs_of_pos (inv_succ_pos n) at hN,
  linarith,
end

lemma lim_constante (x : ℝ) : limite_suite (λ n, x) x :=
λ ε ε_pos, ⟨0, λ _ _, by simp [le_of_lt ε_pos]⟩

lemma limite_si_inferieur_un_sur {u : ℕ → ℝ} {x : ℝ} (h : ∀ n, |u n - x| ≤ 1/(n+1)) :
limite_suite u x :=
begin
  intros ε ε_pos,
  rcases limite_inv_succ ε ε_pos with ⟨N, hN⟩,
  use N,
  intros n hn,
  specialize h n,
  specialize hN n hn,
  linarith,
end

lemma lim_plus_un_sur (x : ℝ) : limite_suite (λ n, x + 1/(n+1)) x :=
limite_si_inferieur_un_sur (λ n, by rw abs_of_pos ; linarith [inv_succ_pos n])

lemma lim_moins_un_sur (x : ℝ) : limite_suite (λ n, x - 1/(n+1)) x :=
begin
  refine limite_si_inferieur_un_sur (λ n, _),
  rw [show x - 1 / (n + 1) - x = -(1/(n+1)), by ring, abs_neg,  abs_of_pos],
  linarith [inv_succ_pos n]
end

lemma gendarmes {u v w : ℕ → ℝ} {l : ℝ}
(lim_u : limite_suite u l) (lim_w : limite_suite w l)
(hu : ∀ n, u n ≤ v n) (hw : ∀ n, v n ≤ w n)  : limite_suite v l :=
begin
  intros ε ε_pos,
  cases lim_u ε ε_pos with N hN,
  cases lim_w ε ε_pos with N' hN',
  use max N N',
  intros n hn,
  rw superieur_max_ssi at hn,
  cases hn with hn hn',
  specialize hN n (by linarith),
  specialize hN' n (by linarith),
  specialize hu n,
  specialize hw n,
  rw abs_inferieur_ssi at *,
  cases hN with hNl hNd,
  cases hN' with hN'l hN'd,
  split,
  -- Ici linarith peut finir, mais sur papier on écrirait
  calc -ε ≤ u n - l : by linarith
      ... ≤ v n - l : by linarith,
  calc v n - l ≤ w n - l : by linarith
      ... ≤ ε : by linarith,
end

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

-- Dans la suite, φ désignera toujours une fonction de ℕ dans ℕ
variable { φ : ℕ → ℕ}


/-- Un réel `a` est valeur d'adhérence d'une suite `u` s'il
existe une suite extraite de `u` qui tend vers `a`. -/
def valeur_adherence (u : ℕ → ℝ) (a : ℝ) :=
∃ φ, extraction φ ∧ limite_suite (u ∘ φ) a

/-- Toute extraction est supérieure à l'identité. -/
lemma extraction_superieur_id : extraction φ → ∀ n, n ≤ φ n :=
begin
  intros hyp n,
  induction n with n hn,
    exact nat.zero_le _,
  exact nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)]),
end

open filter

lemma extraction_machine (ψ : ℕ → ℕ) (hψ : ∀ n, ψ n ≥ n) : ∃ f : ℕ → ℕ, extraction (ψ ∘ f) ∧ ∀ n, f n ≥ n :=
begin
  refine ⟨λ n, nat.rec_on n 0 (λ n ih, ψ ih + 1), λ m n h, _, λ n, _⟩,
  { induction h; dsimp [(∘)],
    { exact hψ _ },
    { exact lt_trans h_ih (hψ _) } },
  { induction n, {apply le_refl},
    exact nat.succ_le_succ (le_trans n_ih (hψ _)) }
end

variables {u : ℕ → ℝ} {l : ℝ}

/-- Si `u` tend vers `l` alors toutes ses suites extraites tendent vers `l`. -/
lemma limite_extraction_si_limite (h : limite_suite u l) (hφ : extraction φ) :
limite_suite (u ∘ φ) l :=
begin
  -- sorry
  intros ε ε_pos,
  cases h ε ε_pos with N hN,
  use N,
  intros n hn,
  apply hN,
  calc N ≤ n   : hn -- on peut écrire « by exact hn » si on a un clavier solide
     ... ≤ φ n : extraction_superieur_id hφ n, -- idem
  -- sorry
end

def segment (a b : ℝ) := {x | a ≤ x ∧ x ≤ b}

notation `[`a `, ` b `]` := segment a b

lemma bolzano_weierstrass {a b : ℝ} {u : ℕ → ℝ} (h : ∀ n, u n ∈ [a, b]) :
∃ c ∈ [a, b], valeur_adherence u c :=
begin
  have cpct : compact [a, b],
    exact compact_Icc,
  have :  map u at_top ≤ principal [a, b],
  { change tendsto u _ _,
    rw tendsto_principal,
    filter_upwards [univ_mem_sets],
    intros n hn,
    exact h n },
  rcases cpct (map u at_top) (map_ne_bot at_top_ne_bot) this with ⟨c, h, h'⟩,
  clear this,
  use [c, h],
  unfold valeur_adherence,
  have : ∀ N, ∃ n ≥ N, |u n -c| ≤ 1/(N+1),
    intro N,
    rw ← forall_sets_neq_empty_iff_neq_bot at h',
    specialize h' (u '' {n | n ≥ N} ∩ {x | |x-c| ≤ 1/(N+1)}) _,
    { simp only [set.not_eq_empty_iff_exists,
                set.mem_image,
                set.mem_inter_eq,
                ne.def,
                set.mem_set_of_eq] at h',
      rcases h' with ⟨_, ⟨n, ⟨hn, rfl⟩⟩, ineg⟩,
      use [n, hn, ineg] },
    { apply inter_mem_inf_sets,
      { apply image_mem_map,
        apply mem_at_top },
      { have fact: (0 : ℝ) < 1/(N+2),
          exact_mod_cast inv_succ_pos (N+1),
        apply mem_sets_of_superset (metric.ball_mem_nhds c fact),
        intros x x_in,
        rw [metric.mem_ball, real.dist_eq] at x_in,
        exact le_of_lt (
          calc |x - c| < 1 / (N + 2) : x_in
                   ... = 1/((N+1)+1) : by { congr' 1, norm_cast }
                   ... ≤ 1 / (N + 1) : nat.one_div_le_one_div (nat.le_succ N)),

       } },
  choose ψ hψ using this,
  cases forall_and_distrib.mp hψ with hψ_id hψ', clear hψ,
  rcases extraction_machine ψ hψ_id with ⟨f, hf, hf'⟩,
  use [ψ ∘ f, hf],
  apply limite_si_inferieur_un_sur ,
  intros n,
  transitivity 1/(f n + 1 : ℝ),
  apply hψ',
  exact nat.one_div_le_one_div (hf' n),
end

lemma limite_suite_id : ∀ A : ℝ, ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) ≥ A:=
begin
  intro A,
  cases exists_nat_gt A with N hN,
  use N,
  intros n hn,
  have : (n : ℝ) ≥ N, exact_mod_cast hn,  --- pfff
  linarith,
end

open real

lemma sup_segment {a b : ℝ} {A : set ℝ} (hnonvide : ∃ x, x ∈ A) (h : A ⊆ [a, b]) :
  ∃ x ∈ [a, b], borne_sup A x :=
begin
  have b_maj :  ∀ (y : ℝ), y ∈ A → y ≤ b,
    from λ y y_in, (h y_in).2,
  have Sup_maj : majorant A (Sup A),
  { apply le_Sup,
    use [b, b_maj] } ,
  refine ⟨real.Sup A, _, _⟩,
  { split,
    { cases hnonvide with x x_in,
      exact le_trans (h x_in).1 (Sup_maj _ x_in) },
    { apply Sup_le_ub A hnonvide b_maj } },
  { use Sup_maj,
    intros y y_in,
    rwa Sup_le _ hnonvide ⟨b, b_maj⟩ },
end
