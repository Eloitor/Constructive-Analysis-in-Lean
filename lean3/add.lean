import regular_sequence
import reals

namespace regular_sequence

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

def neg (a: regular_sequence): regular_sequence :=
  { val := (λ x, -(a x)),
    property := λ _ _ m_pos n_pos, let h := a.property m_pos n_pos 
        in by rwa [←abs_neg, neg_sub_neg, neg_sub] }

instance : has_neg regular_sequence :=
  ⟨neg⟩

lemma neg_apply (a: regular_sequence) (n: ℕ): -a n = -(a n) := rfl

instance : has_sub regular_sequence :=
  ⟨λ a b, add a (neg b)⟩

@[simp] lemma sub_apply (a b: regular_sequence) (n: ℕ): (a - b) n = a (2*n) - b (2*n) := rfl

lemma subs' {a b : regular_sequence} {n : ℕ}: (a-b) n  =  a (2*n) - b (2*n)  := rfl 

instance : has_add regular_sequence :=
  ⟨add⟩

@[simp] lemma add_apply' (a b: regular_sequence) (n: ℕ): (a + b).val n = a (2*n) + b (2*n) := rfl

@[simp] lemma add_apply (a b: regular_sequence) (n: ℕ): (a + b) n = a (2*n) + b (2*n) := rfl


lemma zero_add {a : regular_sequence} {n : ℕ}: (0 + a) n = a (2*n) :=
  begin
    simp,
    refl,
  end

lemma add_zero {a : regular_sequence} {n : ℕ}: (a + 0) n = a (2*n) :=
  begin
    simp,
    refl,
  end

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

end regular_sequence

namespace real
open regular_sequence

def add: real → real → real :=
  quotient.lift₂ (λ x y, ⟦regular_sequence.add x y⟧)
  begin
    simp only [quotient.eq],
    intros a₁ b₁ a₂ b₂ a₁_eq_a₂ b₁_eq_b₂,
    rw equivalent_iff at *,
    unfold add,
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
    specialize hN (2*n),
    specialize hM (2*n),
    simp only [fn_apply, subtype.val_eq_coe],
    sorry,
  end

end real