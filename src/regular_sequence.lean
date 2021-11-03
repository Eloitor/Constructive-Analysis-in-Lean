import data.rat

def is_regular_sequence(seq: ℕ → ℚ) :=
  ∀ {m n: ℕ}, (0 < m) → (0 < n) → |seq m - seq n| ≤ (m : ℚ)⁻¹ + (n : ℚ)⁻¹

def regular_sequence := {f: ℕ → ℚ // is_regular_sequence f}

namespace regular_sequence

instance : has_coe_to_fun regular_sequence (λ _, ℕ → ℚ) :=
  ⟨subtype.val⟩

def equivalent(a b: regular_sequence) :=
  ∀ {n : ℕ}, 0 < n → |a n - b n| ≤ 2 * (n : ℚ)⁻¹

lemma equivalent_refl: reflexive equivalent :=
  λ n h_n, by {simp,}

lemma equivalent_symm: symmetric regular_sequence.equivalent :=
  begin
    intros a b h_eq n h_n,
    specialize h_eq h_n,
    have : - (b n - a n) = (a n - b n),
      by simp [h_eq],
    rwa [←abs_neg, this],
  end

lemma equivalent_iff' {a b: regular_sequence}: 
    (equivalent a b) ↔ (∀ (j: ℕ), 0 < j → ∃ N, ∀ n ≥ N, | a n - b n | ≤ (j: ℚ)⁻¹) :=
  begin
    split,
    { intros h_eq j j_pos,
      use 2 * j,
      intros n n_ge_two_j,
      have n_pos: 0 < n,
        { have j_le_2j: j ≤ 2 * j := (le_mul_iff_one_le_left j_pos).2 one_le_two,
          exact gt_of_ge_of_gt n_ge_two_j (gt_of_ge_of_gt j_le_2j j_pos),},
      specialize h_eq n_pos,

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

lemma equivalent_trans: transitive regular_sequence.equivalent :=
  begin
    intros a b c h_eq_ab h_eq_bc,
    rw regular_sequence.equivalent_iff' at *,
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
                 ... ≤ (↑(2*j))⁻¹ + (↑(2*j))⁻¹ : add_le_add h_N h_M
                 ... = (j: ℚ)⁻¹ : by { push_cast, rw mul_inv₀, ring},
  
  end

instance equiv: setoid regular_sequence :=
  setoid.mk equivalent ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩


lemma equivalent_iff {a b: regular_sequence}: 
    (a ≈ b) ↔ (∀ (j: ℕ), 0 < j → ∃ N, ∀ n ≥ N, | a n - b n | ≤ (j: ℚ)⁻¹) :=
equivalent_iff'

def canonical_bound(x : regular_sequence): ℕ :=
  nat.ceil (x 1) + 2

/-The constant regular sequence-/
def const(x: ℚ): regular_sequence :=
  { val := λ n, x,
  property := 
  begin
    unfold is_regular_sequence,
    intros m n m_pos n_pos,
    simp [zero_le],
    have : 0 < (m: ℚ)⁻¹,
      { rw inv_pos, norm_cast, exact m_pos},
    have : 0 < (n: ℚ)⁻¹,
      { rw inv_pos, norm_cast, exact n_pos},
    apply le_of_lt,
    apply add_pos;
    assumption,
  end
  }

instance : has_zero regular_sequence :=
  ⟨const 0⟩

instance : has_one regular_sequence :=
  ⟨const 1⟩

instance : inhabited regular_sequence :=
  ⟨0⟩

def neg (a: regular_sequence): regular_sequence :=
  { val := (λ x, -(a x)),
      property := 
        begin
         unfold is_regular_sequence,
         intros m n m_pos n_pos,
         rw ←abs_neg,
         simp only [neg_sub_neg, neg_sub],
         exact a.property m_pos n_pos,
        end
  }

def add : regular_sequence → regular_sequence → regular_sequence :=
λ a b,
  { val := λ n, a (2*n) + b (2*n),
    property := 
    begin
      intros m n m_pos n_pos,
      have two_m_pos: 0 < 2 * m,
        { exact nat.succ_mul_pos 1 m_pos },
      have two_n_pos: 0 < 2 * n,
        { exact nat.succ_mul_pos 1 n_pos },
      cases a,
      cases b,
      specialize a_property two_m_pos two_n_pos,
      specialize b_property two_m_pos two_n_pos,

      calc |a_val (2 * m) + b_val (2 * m) - (a_val (2 * n) + b_val (2 * n))| = 
      |(a_val (2 * m) - a_val (2 * n)) + ((b_val (2 * m) - b_val (2 * n)))| : by ring_nf
      ... ≤ |a_val (2 * m) - a_val (2 * n)| + |b_val (2 * m) - b_val (2 * n)| : abs_add _ _
      ... ≤ ((↑(2 * m))⁻¹ + (↑(2 * n))⁻¹) + ((↑(2 * m))⁻¹ + (↑(2 * n))⁻¹) : add_le_add a_property b_property
      ... = (↑m)⁻¹ + (↑n)⁻¹ : by { push_cast, rw mul_inv₀, simp, norm_num, ring_nf, simp, rw mul_inv₀, ring,},
    end
  }

end regular_sequence