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

lemma real_equivalent_iff {a b: ℕ → ℚ} (h_a: regular a) (h_b: regular b): 
    (a ∼ b) ↔ (∀ (j: ℕ), 0 < j → ∃ N, ∀ n ≥ N, | a n - b n | ≤ (j: ℚ)⁻¹) :=
  begin
    split,
    { intros h_eq j j_pos,
      use 2 * j,
      intros n n_ge_two_j,
      have n_pos: 0 < n,
        { have j_le_2j: j ≤ 2 * j := (le_mul_iff_one_le_left j_pos).2 one_le_two,
          exact gt_of_ge_of_gt n_ge_two_j (gt_of_ge_of_gt j_le_2j j_pos),},
      specialize h_eq n n_pos,

      have n_inv_pos: 0 < (n : ℚ)⁻¹,
        {rw [inv_pos, nat.cast_pos], exact n_pos,},

      have n_inv_le: (n : ℚ)⁻¹ ≤ (2*j : ℚ)⁻¹,
      { 
        rw le_inv n_inv_pos,
        { simp only [inv_inv₀],
          norm_cast,
          exact n_ge_two_j },
        { norm_cast,
          exact nat.succ_mul_pos 1 j_pos},
      },
  
      calc |a n - b n| ≤ (↑n)⁻¹ * 2: h_eq
                   ... ≤ (2*j)⁻¹ * 2 : by 
                    { simp only [n_inv_le, mul_le_mul_right, zero_lt_bit0, zero_lt_one], }
                   ... = (↑j)⁻¹ :  by { rw [mul_inv₀], ring, },
    },
    { 
      intros h_eq n n_pos,
      have key: ∀ j: ℕ, 0 < j → |a n - b n| < 2 * (n: ℚ)⁻¹ + 3 * (j: ℚ)⁻¹,
      {
        by sorry,
      },
      sorry,
    },
  end

lemma real_equivalent_trans {a b c : ℕ → ℚ} (h_a: regular a) (h_b: regular b) (h_c: regular c)
    (h_eq_ab: a ∼ b) (h_eq_bc: b ∼ c): a ∼ c :=
  begin
    sorry,
  end
