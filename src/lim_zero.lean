import regular_sequence

/-- `lim_zero f` holds when `f` approaches 0. -/
def lim_zero (f : regular_sequence) := (∀ (j: ℕ), 0 < j → ∃ N, ∀ n ≥ N, | f n | ≤ (j: ℚ)⁻¹)

theorem add_lim_zero {f g : regular_sequence}
  (hf : lim_zero f) (hg : lim_zero g) : lim_zero (f + g) :=
  begin
    intros j hj,
    obtain ⟨N₁, hN₁⟩ := hf (2*j) (mul_pos zero_lt_two hj),
    obtain ⟨N₂, hN₂⟩ := hg (2*j) (mul_pos zero_lt_two hj),
    use max N₁ N₂,
    intros n hn,
    have h3 : | f (2*n) | + | g (2*n) | ≤ (2*j: ℚ)⁻¹+ (2*j: ℚ)⁻¹,
    {
      have hfg : | f (2*n) | ≤ (2*j: ℚ)⁻¹ ∧ | g (2*n) | ≤ (2*j: ℚ)⁻¹,
      {
        have : 2*n ≥ N₁ ∧ 2*n ≥ N₂,
        {
          have : n ≤ 2 * n,
          {
            obtain h := mul_le_mul one_le_two rfl.ge (zero_le n) (zero_le 2),
            rwa one_mul at h,
          },
          exact ⟨le_trans (le_of_max_le_left hn) this, le_trans (le_of_max_le_right hn) this⟩
        },
        obtain tt := hN₁ (2*n) this.1,
        obtain ttt := hN₂ (2*n) this.2,
        simp only [nat.cast_bit0, nat.cast_one, nat.cast_mul] at *,
        exact ⟨tt,ttt⟩,
      },
      exact add_le_add hfg.1 hfg.2,
    },
    rw [← one_mul (j : ℚ)⁻¹ ,← mul_inv_cancel (@two_ne_zero ℚ _ _), mul_assoc, ← @mul_inv₀ ℚ _ 2 (j : ℚ), two_mul],
    exact le_trans (abs_add (f (2 * n)) (g (2 * n))) h3,
  end

lemma neg_lim_zero{a: regular_sequence}(ha: lim_zero a): lim_zero (-a) :=
  begin
    sorry,
  end

lemma sub_lim_zero{a b: regular_sequence}(ha: lim_zero a)(hb: lim_zero b): lim_zero (a - b) :=
  begin
    sorry,
  end

