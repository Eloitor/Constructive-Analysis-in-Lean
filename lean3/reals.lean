import regular_sequence

def real := quotient regular_sequence.equiv

open regular_sequence

instance : has_coe ℚ real:=
  { coe := λ x, ⟦const x⟧ }

instance : has_zero real :=
  ⟨(0: ℚ)⟩

instance : has_one real :=
  ⟨(1: ℚ)⟩



def real_neg : real → real :=
  quotient.lift (λ x, ⟦regular_sequence.neg x⟧)
  begin
    intros a b h_eq,
    change equivalent a b at h_eq,
    unfold regular_sequence.neg,
    simp only [quotient.eq],
    intros j j_pos,
    specialize h_eq j_pos,
    transitivity |a j - b j|,
    {
      apply le_of_eq,
      unfold_coes,
      rw ←abs_neg,
      simp only [neg_sub_neg, neg_sub],
    },
    {
      assumption,
    },
  end

instance : has_neg real :=
  ⟨real_neg⟩




