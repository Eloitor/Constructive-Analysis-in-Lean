import data.rat

structure regular(a : ℕ → ℚ) :=
  (regularity {m n: ℕ} (h_m: 0 < m) (h_n: 0 < n): |a m - a n | ≤ (m : ℚ)⁻¹ + (n : ℚ)⁻¹)

def equivalent(a: ℕ → ℚ) (b: ℕ → ℚ) :=
  ∀ n : ℕ, 0 < n → |a n - b n| ≤ 2 * (n : ℚ)⁻¹

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
  
      calc |a n - b n| ≤ 2*(↑n)⁻¹: h_eq
                   ... ≤ 2*(2*j)⁻¹ : by simp only [n_inv_le, mul_le_mul_left, zero_lt_bit0, zero_lt_one]
                   ... = (↑j)⁻¹ :  by { rw [mul_inv₀], ring},
    },
    { 
      intros h_eq n n_pos,
      have key: ∀ j: ℕ, 0 < j → |a n - b n| < 2*(n: ℚ)⁻¹ + 3 * (j: ℚ)⁻¹,
      {
        intros j j_pos,
        obtain ⟨Nj, h_Nj⟩  := h_eq j j_pos,
        let m := max j Nj,
        calc |a n - b n| = |(a n - a m) + ((a m - b m) + (b m - b n))| : by ring_nf
                     ... ≤ |a n - a m| + |(a m - b m) + (b m - b n)| : abs_add _ _
                     ... ≤ |a n - a m| + |a m - b m| + |b m - b n| : by sorry
                     ... ≤ ((n: ℚ)⁻¹ + (m: ℚ)⁻¹) + (j: ℚ)⁻¹ + (n: ℚ)⁻¹ + (m: ℚ)⁻¹ : by sorry
                     ... < 2*(↑n)⁻¹ + 3*(↑j)⁻¹: 
                      begin
                        sorry,
                      end,
      },
      apply le_of_forall_pos_le_add,
      intros ε ε_pos,
      apply le_of_lt,
      have : ∃ j: ℕ, 0 < j ∧ 3*(j: ℚ)⁻¹ ≤ ε,
      {
        sorry,
      },
      obtain ⟨j, j_pos, j_lt_ε⟩ := this,
      specialize key j j_pos,
      calc |a n - b n| < 2 * (↑n)⁻¹ + 3 * (↑j)⁻¹ : key
                    ... ≤ 2 * (↑n)⁻¹ + ε : add_le_add_left j_lt_ε _
    },
  end

lemma real_equivalent_trans {a b c : ℕ → ℚ} (h_a: regular a) (h_b: regular b) (h_c: regular c)
    (h_eq_ab: a ∼ b) (h_eq_bc: b ∼ c): a ∼ c :=
  begin
    rw real_equivalent_iff h_a h_b at h_eq_ab,
    rw real_equivalent_iff h_b h_c at h_eq_bc,
    rw real_equivalent_iff h_a h_c,
    intros j j_pos,
    have two_j_pos: 2 * j > 0,
      { exact nat.succ_mul_pos 1 j_pos },
    specialize h_eq_ab (2*j) two_j_pos,
    specialize h_eq_bc (2*j) two_j_pos,
    obtain ⟨N, h_N⟩ := h_eq_ab,
    obtain ⟨M, h_M⟩ := h_eq_bc,
    use max N M,
    intros n n_ge_max,
    have n_ge_N: n ≥ N,
      { exact le_of_max_le_left n_ge_max },
    have n_ge_M: n ≥ M,
      { exact le_of_max_le_right n_ge_max },
    
    specialize h_N n n_ge_N,
    specialize h_M n n_ge_M,
    calc |a n - c n| ≤ |(a n - b n) + (b n - c n)| : by simp
                 ... ≤ |a n - b n| + |b n - c n| : abs_add _ _
                 ... ≤ |a n - b n| + (↑(2*j))⁻¹ : add_le_add_left h_M (|a n - b n|)
                 ... ≤ (↑(2*j))⁻¹ + (↑(2*j))⁻¹ : add_le_add_right h_N (↑(2*j))⁻¹
                 ... = (j: ℚ)⁻¹ : by { push_cast, rw mul_inv₀, ring}
  
  end


