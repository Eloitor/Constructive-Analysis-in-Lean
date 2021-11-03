import regular_sequence

def real := quotient regular_sequence.equiv

open regular_sequence

instance : has_coe ℚ real:=
  { coe := λ x, ⟦const x⟧ }

instance : has_zero real :=
  ⟨(0: ℚ)⟩

instance : has_one real :=
  ⟨(1: ℚ)⟩



def real_neg : real → real :=
  quotient.lift (λ x, ⟦regular_sequence.neg x⟧)
  begin
    intros a b h_eq,
    change equivalent a b at h_eq,
    unfold regular_sequence.neg,
    simp only [quotient.eq],
    intros j j_pos,
    specialize h_eq j_pos,
    transitivity |a j - b j|,
    {
      apply le_of_eq,
      unfold_coes,
      rw ←abs_neg,
      simp only [neg_sub_neg, neg_sub],
    },
    {
      assumption,
    },
  end

instance : has_neg real :=
  ⟨real_neg⟩

def add: real → real → real :=
  quotient.lift₂ (λ x y, ⟦regular_sequence.add x y⟧)
  begin
    intros a₁ b₁ a₂ b₂ a₁_eq_a₂ b₁_eq_b₂,
    simp,
    unfold add,
    change equivalent ⟨λ (n : ℕ), a₁ (2 * n) + b₁ (2 * n), _⟩ ⟨λ (n : ℕ), a₂ (2 * n) + b₂ (2 * n), _⟩,

    rw equivalent_iff at *,
    rw equivalent_iff',
    simp at *,
    intros j j_pos,
    have two_j_pos : 0 < 2*j,
    {
      simpa,
    },
    specialize a₁_eq_a₂ (2*j) two_j_pos,
    specialize b₁_eq_b₂ (2*j) two_j_pos,
    obtain ⟨N, hN⟩ := a₁_eq_a₂,
    obtain ⟨M, hM⟩ := b₁_eq_b₂,
    use max N M,
    intros n n_ge_max,
    specialize hN n,
    specialize hM n,
    have : N ≤ n,
    {
      transitivity (max N M),
      exact le_max_left _ _,
      assumption,
    },
    specialize hN this,
    


    sorry,
  end


