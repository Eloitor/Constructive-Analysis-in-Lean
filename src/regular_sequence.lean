import data.rat

def is_regular_sequence(seq: ℕ → ℚ) :=
  ∀ {m n: ℕ}, (0 < m) → (0 < n) → |seq m - seq n| ≤ (m : ℚ)⁻¹ + (n : ℚ)⁻¹

def regular_sequence := {f: ℕ → ℚ // is_regular_sequence f}

namespace regular_sequence

instance : has_coe_to_fun regular_sequence (λ _, ℕ → ℚ) :=
  ⟨subtype.val⟩
 
@[simp] theorem mk_to_fun (f) (hf : is_regular_sequence f) :
  @coe_fn regular_sequence _ _ ⟨f, λ x y, hf⟩ = f := rfl

@[simp] lemma fn_apply (a: regular_sequence) (n) : a n = a.val n := rfl

theorem ext {f g : regular_sequence} (h : ∀ i, f i = g i) : f = g :=
  subtype.eq (funext h)
 
theorem is_reg_seq (f : regular_sequence) : is_regular_sequence f.val := f.property

/-The constant regular sequence-/
def const(x: ℚ): regular_sequence :=
  { val := λ n, x,
    property := λ m n m_pos n_pos, let h1 := (@inv_pos _ _ (m : ℚ)).2 (nat.cast_pos.2 m_pos), 
        h2 := (@inv_pos _ _ (n : ℚ)).2 (nat.cast_pos.2 n_pos), 
        h := le_of_lt (add_pos h1 h2) in by rwa [sub_self, abs_zero] }

instance : has_zero regular_sequence :=
  ⟨const 0⟩

instance : has_one regular_sequence :=
  ⟨const 1⟩

instance : inhabited regular_sequence :=
  ⟨0⟩

def equivalent(a b: regular_sequence) :=
  ∀ {n : ℕ}, 0 < n → |a n - b n| ≤ 2 * (n : ℚ)⁻¹

lemma equivalent_refl: reflexive equivalent :=
  λ n h_n, by {simp,}

/-- `lim_zero f` holds when `f` approaches 0. -/
def lim_zero (f : regular_sequence) := (∀ (j: ℕ), 0 < j → ∃ N, ∀ n ≥ N, | f n | ≤ (j: ℚ)⁻¹)

lemma equivalent_symm : symmetric regular_sequence.equivalent :=
  λ _ _ h_eq _ h_n, let h := h_eq h_n in by rwa [←abs_neg, neg_sub]

lemma equivalent_iff' {a b: regular_sequence}: 
    (equivalent a b) ↔ (∀ j: ℕ, 0 < j → ∃ Nj, ∀ n ≥ Nj, |a n - b n| ≤ (j : ℚ)⁻¹) :=
  begin
    split,
    { intros h_eq j j_pos,
      use 2 * j,
      intros n n_ge_two_j,
      have j_le_2j: j ≤ 2 * j := (le_mul_iff_one_le_left j_pos).2 one_le_two,
      have n_pos := gt_of_ge_of_gt n_ge_two_j (gt_of_ge_of_gt j_le_2j j_pos),
      have hn2n : n ≤ 2 * n,
      {
        obtain h := mul_le_mul one_le_two rfl.ge (zero_le n) (zero_le 2),
        rwa one_mul at h,
      },
      have n2_pos := gt_of_ge_of_gt hn2n n_pos,
      specialize h_eq n_pos,
      have n_inv_pos: 0 < (n : ℚ)⁻¹, by rwa [inv_pos, nat.cast_pos],
      haveI := rat.nontrivial,
      have ninv_lt_2jinv : (n : ℚ)⁻¹ ≤ (2*j)⁻¹,
      {
        rw inv_le_inv,
        norm_cast,
        exact n_ge_two_j,
        exact nat.cast_pos.2 n_pos,
        exact (@zero_lt_mul_left _ _  (j : ℚ) 2 zero_lt_two).2 (nat.cast_pos.2 j_pos),
      },
      calc |a n - b n | ≤ 2*(↑n)⁻¹ : h_eq
                   ... ≤ 2*(2*j)⁻¹ : by rwa @mul_le_mul_left _ _ (n : ℚ)⁻¹ (2*j)⁻¹ 2 zero_lt_two
                   ... = (↑j)⁻¹ :  by { rw [mul_inv₀], ring}
    },
    { 
      intros h_eq n n_pos,
      have key: ∀ j: ℕ, 0 < j → |a n - b n| ≤ 2*(n: ℚ)⁻¹ + 3 * (j: ℚ)⁻¹,
      {
        intros j j_pos,
        obtain ⟨Nj, h_Nj⟩  := h_eq j j_pos,
        set m := max j Nj with hm,
        have m_pos := gt_of_ge_of_gt (le_max_left j Nj) j_pos,
        have inv_m_leq_inv_j : 2*(m : ℚ)⁻¹ ≤ 2*(j : ℚ)⁻¹,
        {
          simp only [mul_le_mul_left, nat.cast_max, zero_lt_bit0, zero_lt_one],
          obtain m_rat_pos := @lt_max_of_lt_left _ _ 0 (j : ℚ) (Nj : ℚ) (nat.cast_pos.mpr j_pos),
          rw inv_le_inv m_rat_pos (nat.cast_pos.mpr j_pos),
          norm_cast,
          exact le_max_left j Nj,
        },
        calc |a n - b n| = |(a n - a m) + ((a m - b m) + (b m - b n))| : by ring_nf
                     ... ≤ |a n - a m| + |(a m - b m) + (b m - b n)| : abs_add _ _
                     ... ≤ |a n - a m| + (|a m - b m| + |b m - b n|) : add_le_add_left (abs_add _ _) _
                     ... ≤ ((n: ℚ)⁻¹ + (m: ℚ)⁻¹) + ((j: ℚ)⁻¹ + ((m: ℚ)⁻¹ + (n: ℚ)⁻¹) ): by exact add_le_add (a.property n_pos m_pos) 
                                                                  (add_le_add (h_Nj m (le_max_right j Nj)) (b.property m_pos n_pos))
                     ... = 2*(↑n)⁻¹ + 2 * (↑m)⁻¹ + (↑j)⁻¹ : by ring_nf
                     ... ≤ 2*(↑n)⁻¹ + 2 * (↑j)⁻¹ + (↑j)⁻¹ : by exact add_le_add_right (add_le_add_left inv_m_leq_inv_j (2 * (↑n)⁻¹)) (↑j)⁻¹
                     ... = 2*(↑n)⁻¹ + 3*(↑j)⁻¹: by ring_nf
      },
      apply le_of_forall_pos_le_add,
      intros ε ε_pos,
      have h1: ↑(int.floor ((3:ℚ)/ε))+1 > 3/ε,
      {
        obtain h := rat.num_lt_succ_floor_mul_denom ((3:ℚ)/ε),
        apply rat.lt_def.2,
        norm_cast,
        simp[h],
      },
      have hh1 := nat.lt_succ_floor (3 / ε),
      have h2 : (↑(int.to_nat (int.floor ((3:ℚ)/ε)))+1)⁻¹ < (3/ε)⁻¹,
      {        
        exact (@inv_lt_inv ℚ _ _ _ (⌊3 / ε⌋.to_nat.cast_add_one_pos) 
            (div_pos zero_lt_three ε_pos)).2 hh1,
      },
      apply le_of_lt,
      have : ∃ j: ℕ, 0 < j ∧ 3*(j: ℚ)⁻¹ < ε,
      {
        use  int.to_nat (int.floor ((3/ε)))+1,
        split,
        {
          exact fin.last_pos,
        },
        {
          calc 3 * (↑(int.to_nat (rat.floor ((3:ℚ)/ε)))+1)⁻¹ < 3* (3/ε)⁻¹ : mul_lt_mul_of_pos_left h2 zero_lt_three
              ... = 3 * (ε/3) : by rw inv_div 
              ... = ε : by ring_nf
        }
      },
      obtain ⟨j, j_pos, j_lt_ε⟩ := this,
      specialize key j j_pos,
      calc |a n - b n| ≤ 2 * (↑n)⁻¹ + 3 * (↑j)⁻¹ : key
                   ... < 2 * (↑n)⁻¹ + ε : add_lt_add_left j_lt_ε _
    },
  end

lemma lim_zero_of_equiv{a b : regular_sequence}(hab: equivalent a b)(a_lim_zero: lim_zero a): lim_zero b :=
begin
  rw equivalent_iff' at *,
  unfold lim_zero at *,
  intros j hj,
  obtain h2j_pos := nat.succ_mul_pos 1 hj,
  obtain ⟨N₁, hN₁⟩ := a_lim_zero (2*j) h2j_pos,
  obtain ⟨N₂, hN₂⟩ := hab (2*j) h2j_pos,
  use max N₁ N₂,
  intros n hn,  
  specialize hN₁ n (le_of_max_le_left hn),
  specialize hN₂ n (le_of_max_le_right hn),
  have h2jNQ : (↑(2 * j))⁻¹ = (((2 : ℚ) * ↑j))⁻¹ := by rw [nat.cast_mul, nat.cast_two],
  calc |b n| = |b n - a n + a n| : by ring_nf
  ... ≤ |b n - a n| + |a n| : abs_add _ _
  ... = |a n - b n| + |a n| : by  rw [←abs_neg, neg_sub]
  ... ≤ (2 * j)⁻¹ + (2 * j)⁻¹: add_le_add (by rwa ← h2jNQ) (by rwa ← h2jNQ)
  ... = (↑j)⁻¹ : by {ring_nf, rw mul_inv₀, simp,},
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
                 ... = (j: ℚ)⁻¹ : by { push_cast, rw mul_inv₀, ring}
  end

instance equiv: setoid regular_sequence :=
  setoid.mk equivalent ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩


lemma equivalent_iff {a b: regular_sequence}: 
    (a ≈ b) ↔ (∀ j: ℕ, 0 < j → ∃ Nj, ∀ n ≥ Nj, |a n - b n| ≤ (j : ℚ)⁻¹) :=
  equivalent_iff'


end regular_sequence