import data.rat

def is_regular_sequence(seq: ℕ → ℚ) :=
  ∀ {m n: ℕ}, (0 < m) → (0 < n) → |seq m - seq n| ≤ (m : ℚ)⁻¹ + (n : ℚ)⁻¹

def regular_sequence := {f: ℕ → ℚ // is_regular_sequence f}

namespace regular_sequence

instance : has_coe_to_fun regular_sequence (λ _, ℕ → ℚ) :=
  ⟨subtype.val⟩
 
@[simp] theorem mk_to_fun (f) (hf : is_regular_sequence f) :
  @coe_fn regular_sequence _ _ ⟨f, λ x y, hf⟩ = f := rfl

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

def neg (a: regular_sequence): regular_sequence :=
  { val := (λ x, -(a x)),
    property := λ _ _ m_pos n_pos, let h := a.property m_pos n_pos 
        in by rwa [←abs_neg, neg_sub_neg, neg_sub] }

instance : has_neg regular_sequence :=
  ⟨neg⟩

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

  instance : has_add regular_sequence :=
  ⟨add⟩

@[simp] lemma add_apply (a b: regular_sequence) (n: ℕ):  (a + b) n = a (2*n) + b (2*n) := rfl

instance : has_sub regular_sequence :=
  ⟨λ a b, add a (neg b)⟩

def canonical_bound(x : regular_sequence): ℕ :=
  nat.ceil (|x 1|) + 2

lemma abs_le_canonical_bound(x : regular_sequence) (n: ℕ) (n_pos: 0 < n): |x n| ≤ canonical_bound x :=
  begin
    calc |x n| = |x n - x 1 + x 1| : by simp
          ... ≤ |x n - x 1| + |x 1| : abs_add _ _
          ... ≤ (n:ℚ)⁻¹ + (1:ℚ)⁻¹ + |x 1|: 
            begin
              apply add_le_add_right,
              {
                have := x.property n_pos (nat.succ_pos 0),
                simp at this,
                exact this,
              },
            end
          ... ≤ 1 + 1 + |x 1| : by { simp, 
            rw inv_le,
            {
              simp only [nat.one_le_cast, inv_one],
              exact n_pos,
            },
            {
              simp,
              exact n_pos,
            },
            {
              exact zero_lt_one,
            },
          }
          ... ≤ canonical_bound x :
          begin
            rw canonical_bound,
            simp,
            norm_num,
            rw add_comm,
            exact add_le_add_right (nat.le_ceil _) 2,
          end
  end

def mul: regular_sequence → regular_sequence → regular_sequence :=
  λ x y,
  { val := let k := max (canonical_bound x) (canonical_bound y) in 
          λ n, x (2*k*n) * y (2*k*n),
    property := 
    begin
      intros m n m_pos n_pos,
      set kx := canonical_bound x with h_kx,
      set ky := canonical_bound y with h_ky,
      set k := max kx ky with hk,
      simp,

      have k_pos: 0 < k,
        {
          rw hk,
          rw lt_max_iff,
          left,
          rw h_kx,
          unfold canonical_bound,
          simp,
        },
      
      have two_k_m_pos: 0 < 2 * k * m,
        {
          apply nat.mul_pos,
          exact nat.succ_mul_pos 1 k_pos,
          assumption,
        },

      have two_k_n_pos: 0 < 2 * k * n,
        {
          apply nat.mul_pos,
          exact nat.succ_mul_pos 1 k_pos,
          assumption,
        },
      
      have hx := abs_le_canonical_bound x,
      have hy := abs_le_canonical_bound y,
      cases x,
      cases y,
      obtain := x_property two_k_m_pos two_k_n_pos,
      obtain := y_property two_k_m_pos two_k_n_pos,

      change |x_val (2 * k * m) * y_val (2 * k * m) - x_val (2 * k * n) * y_val (2 * k * n)| ≤ (m:ℚ)⁻¹ + (n:ℚ)⁻¹,
      
      calc |x_val (2 * k * m) * y_val (2 * k * m) - (x_val (2 * k * n) * y_val (2 * k * n))|
       = |(x_val (2*k*m)) * (y_val (2*k*m) - y_val (2*k*n)) + (y_val (2*k*n)) * (x_val (2*k*m) - x_val (2*k*n))| : by { congr, ring_nf,}
        ... ≤ |(x_val (2*k*m)) * (y_val (2*k*m) - y_val (2*k*n))| + |(y_val (2*k*n)) * (x_val (2*k*m) - x_val (2*k*n))| : abs_add _ _
        ... ≤ k * |(y_val (2*k*m) - y_val (2*k*n))| + k * |(x_val (2*k*m) - x_val (2*k*n))| : 
        begin 
          apply add_le_add,
          {
            rw abs_mul,
            apply mul_le_mul,
            {
              transitivity (kx:ℚ),
              {
                rw h_kx,
                apply hx (2*k*m) two_k_m_pos,
              },
              {
                rw hk,
                norm_cast,
                exact le_max_left kx ky,
              },
            },
            {
              refl,
            },
            {
              exact abs_nonneg (y_val (2 * k * m) - y_val (2 * k * n)),
            },
            {
              exact nat.cast_nonneg k,
            },
          },
          {
            rw abs_mul,
            apply mul_le_mul,
            {
              transitivity (ky:ℚ),
              {
                rw h_ky,
                apply hy (2*k*n) two_k_n_pos,
              },
              {
                rw hk,
                norm_cast,
                exact le_max_right kx ky,
              },
            },
            {
              refl,
            },
            {
              exact abs_nonneg (x_val (2 * k * m) - x_val (2 * k * n)),
            },
            {
              exact nat.cast_nonneg k,
            },
          },
        end
    
        ... ≤ k*((↑(2 * k * m))⁻¹ + (↑(2 * k * n))⁻¹) + k*((↑(2 * k * m))⁻¹ + (↑(2 * k * n))⁻¹) : 
        begin
          apply add_le_add;
          {
            rw mul_le_mul_left,
            {
              assumption,
            },
            {
              exact nat.cast_pos.mpr k_pos,
            },
          },
        end
       ... = (m: ℚ)⁻¹+ (n:ℚ)⁻¹ : 
       begin
         rw ←mul_add,
         rw add_assoc,
         rw add_comm (↑(2 * k * m))⁻¹ (↑(2 * k * n))⁻¹,
         nth_rewrite 1 ←add_assoc,
         push_cast,
         
         simp,
         ring_nf,
         rw add_mul,
         congr;
          {
            rw mul_comm,
            rw ←mul_assoc,
            simp,
            norm_num;
            rw mul_inv₀,
            rw mul_inv₀,
            nth_rewrite 1 mul_assoc,
            rw mul_assoc,
            nth_rewrite 1 ←mul_assoc,
            simp only [one_mul, mul_inv_cancel, ne.def, not_false_iff, bit0_eq_zero, one_ne_zero],
            rw ←mul_assoc,
            rw mul_inv_cancel,
            {
              simp,
            },
            {
              rw hk at k_pos,
              apply ne_of_gt,
              have := (@nat.cast_pos ℚ _  _ (max kx ky)).mpr,
              push_cast at this,
              exact this k_pos,
            },
          },
       end
    end
  }
  
instance : has_mul regular_sequence :=
  ⟨mul⟩

def equivalent(a b: regular_sequence) :=
  ∀ {n : ℕ}, 0 < n → |a n - b n| ≤ 2 * (n : ℚ)⁻¹

lemma equivalent_refl: reflexive equivalent :=
  λ n h_n, by {simp,}

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

lemma equivalent_symm : symmetric regular_sequence.equivalent :=
  λ _ _ h_eq _ h_n, let h := h_eq h_n in by rwa [←abs_neg, neg_sub]

lemma zero_add_lim_zero {a : regular_sequence} {n : ℕ}: (0 + a) n = a (2*n) :=
  begin
    simp,
    refl,
  end

lemma negative_lim_zero {a b : regular_sequence} {n : ℕ}: (a-b) n  =  a (2*n) - b (2*n)  := rfl 

lemma equivalent_iff' {a b: regular_sequence}: 
    (equivalent a b) ↔ lim_zero (a - b) :=
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
      have n2_pos: 0 < 2*n,
      {  
        exact gt_of_ge_of_gt hn2n n_pos,
      },
      specialize h_eq n2_pos,

      have n_inv_pos: 0 < (2*n : ℚ)⁻¹,
        {
          simp, exact n_pos,          
        },

      have n_inv_le: (2*n : ℚ)⁻¹ ≤ (2*j : ℚ)⁻¹,
      { rw le_inv n_inv_pos,
        { simp only [inv_inv₀],
          norm_cast,
          exact le_trans n_ge_two_j hn2n},
        { norm_cast,
          exact nat.succ_mul_pos 1 j_pos},
      },
      
      calc |a (2*n) - b (2*n) | ≤ 2*(↑(2*n))⁻¹: h_eq
                   ... ≤ 2*(2*j)⁻¹ : by simp [n_inv_le]
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
    calc |a (2*n) - c (2*n)| ≤ |(a (2*n) - b (2*n)) + (b (2*n) - c (2*n))| : by simp
                 ... ≤ |a (2*n) - b (2*n)| + |b (2*n) - c (2*n)| : abs_add _ _
                 ... ≤ (↑(2*j))⁻¹ + (↑(2*j))⁻¹ : add_le_add h_N h_M
                 ... = (j: ℚ)⁻¹ : by { push_cast, rw mul_inv₀, ring},
  
  end

instance equiv: setoid regular_sequence :=
  setoid.mk equivalent ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩


lemma equivalent_iff {a b: regular_sequence}: 
    (a ≈ b) ↔ lim_zero (a - b) :=
  equivalent_iff'

def canonical_bound(x : regular_sequence): ℕ :=
  nat.ceil (x 1) + 2



end regular_sequence
