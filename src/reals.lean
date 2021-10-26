import data.rat

structure regular(a : ℕ → ℚ) :=
  (regularity {m n: ℕ} (h_m: 0 < m) (h_n: 0 < n): |a m - a n | ≤ (m : ℚ)⁻¹ + (n : ℚ)⁻¹)

def equivalent(a: ℕ → ℚ) (b: ℕ → ℚ) :=
  ∀ n : ℕ, 0 < n → |a n - b n| ≤ (n : ℚ)⁻¹ * 2

notation a `∼` b := equivalent a b

lemma real_equivalent_refl {a: ℕ → ℚ} (h_a: regular a): a ∼ a :=
  λ n h_n, by simp [h_a.regularity h_n]

lemma real_equivalent_symm {a b: ℕ → ℚ} (h_a: regular a) (h_b: regular b) (h_eq: a ∼ b): b ∼ a :=
  λ n h_n,
  begin
    specialize h_eq n h_n,
    have : - (b n - a n) = (a n - b n),
      by simp [h_eq],
    rw [←abs_neg, this],
    assumption,
  end

lemma real_equivalent_iff {a b: ℕ → ℚ} (h_a: regular a) (h_b: regular b): 
    (a ∼ b) ↔ (∀ (j: ℕ), 0 < j → ∃ N, ∀ n ≥ N, | a n - b n | ≤ (j: ℚ)⁻¹) :=
  begin
    split,
    { intros h_eq h_j h_n,
      use 2 * h_j,
      intros h_k h_l,
      unfold equivalent at h_eq,
      specialize h_eq h_k _,
      {
        calc 0 < h_j : h_n
          ... ≤ 2*h_j : by { rw le_mul_iff_one_le_left, exact one_le_two, exact h_n }
          ... ≤ h_k : h_l,
      },
      calc |a h_k - b h_k| ≤ | a h_k | + | b h_k | : by {apply abs_sub,}
        ... ≤ (h_j : ℚ)⁻¹ : by sorry,
    },
    { 
      sorry,
    },
  end

lemma real_equivalent_trans {a b c : ℕ → ℚ} (h_a: regular a) (h_b: regular b) (h_c: regular c)
    (h_eq_ab: a ∼ b) (h_eq_bc: b ∼ c): a ∼ c :=
  begin
    sorry,
  end