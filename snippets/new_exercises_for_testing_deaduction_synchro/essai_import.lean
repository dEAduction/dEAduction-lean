import exercices_limites_suites

example
(u : ℕ → ℝ) (l : ℝ)(l' : ℝ) (H : limit u l) (H' : limit u l') :
l = l' 
:=
begin
    by_contradiction,
    
end

example 
(u : ℕ → ℝ)
(l l' : ℝ)
(H : limit u l)
(H' : limit u l')
(H1 : ¬l = l')
: false
:=
begin
  todo
end