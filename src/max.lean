import reals
import regular_sequence
import lim_zero

lemma max_eq(a b: ℚ): max a b = (a + b + abs (a - b)) / 2 :=
begin
  by_cases h: a ≤ b,
  { 
    have: 0 ≥ a-b,
    {
      linarith,
    },
    rw [abs_of_nonpos this],
    ring_nf,
    simpa,
  },
  { 
    push_neg at h,
    have: 0 < a-b,
    {
      linarith,
    },
    rw [abs_of_pos this],
    ring_nf,
    rw max_comm,
    simp only [max_eq_right_iff],
    apply le_of_lt,
    assumption,
  }
end

def regular_sequence.max(a b: regular_sequence): regular_sequence :=
{ val := λ n, max (a n) (b n),
  property := 
  begin
    intros n m n_pos m_pos,
    sorry,
  end }

@[simp]
lemma regular_sequence.max_val(a b: regular_sequence) (n : ℕ):
  (regular_sequence.max a b) n = max (a n) (b n) :=
  sorry

open regular_sequence

def reals.max: real → real → real :=
  quotient.lift₂ (λ x y, ⟦regular_sequence.max x y⟧) 
    begin
      intros a₁ a₂ b₁ b₂ h₁ h₂,
      rw quotient.eq,
      rw regular_sequence.equivalent_iff at *,
      intros n hn,
      use 37,
      intros m hm,
      simp only [fn_apply, sub_apply, max_val, subtype.val_eq_coe],
      repeat {rw max_eq,},
      

      sorry,
    end

