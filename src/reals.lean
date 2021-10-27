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
    rwa [←abs_neg, this],
  end

/-instance jaja : ordered_semiring ℕ :=
  begin
    exact nat.ordered_semiring,
  end-/

lemma real_equivalent_iff {a b: ℕ → ℚ} (h_a: regular a) (h_b: regular b): 
    (a ∼ b) ↔ (∀ (j: ℕ), 0 < j → ∃ N, ∀ n ≥ N, | a n - b n | ≤ (j: ℚ)⁻¹) :=
  begin
    split,
    { intros h_eq j h_j_pos,
      use 2 * j,
      intros n h_n_ge_two_j,
      unfold equivalent at h_eq,
      specialize h_eq n _,
      { obtain h2j:= (le_mul_iff_one_le_left h_j_pos).2 one_le_two,
        exact gt_of_ge_of_gt h_n_ge_two_j (gt_of_ge_of_gt h2j h_j_pos) },
      have : (n : ℚ)⁻¹ ≤ (2*j : ℚ)⁻¹,
      { obtain h2j := nat.succ_mul_pos 1 h_j_pos,
        rw le_inv,
        { simp only [inv_inv₀],
          obtain tt := nat.cast_le.mpr h_n_ge_two_j,
          norm_num at tt,
          exact tt,
          exact rat.nontrivial },
        { rw [inv_pos, nat.cast_pos],
          exact gt_of_ge_of_gt h_n_ge_two_j h2j },
        { simp only [zero_lt_bit0, zero_lt_mul_left, nat.cast_pos, zero_lt_one, h_j_pos] } },
      have : (n : ℚ)⁻¹ * 2 ≤ (j : ℚ)⁻¹,
      { haveI : (n : ℚ)⁻¹ * 2 ≤ (2*j : ℚ)⁻¹ * 2,
        { simp only [this, mul_le_mul_right, zero_lt_bit0, zero_lt_one] },
        have hjeq : (2*j : ℚ)⁻¹ * 2 = (j : ℚ)⁻¹,
        { rw [mul_inv₀],
          ring },
        rwa ← hjeq },
      exact le_trans h_eq this },
    { 
     -- cases h_a with ha_regular,
     -- cases h_b with hb_regular,
      sorry,
    },
  end

lemma real_equivalent_trans {a b c : ℕ → ℚ} (h_a: regular a) (h_b: regular b) (h_c: regular c)
    (h_eq_ab: a ∼ b) (h_eq_bc: b ∼ c): a ∼ c :=
  begin
    sorry,
  end
