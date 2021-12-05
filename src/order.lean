import regular_sequence

namespace regular_sequence 

open regular_sequence

def pos(a: regular_sequence) := 
  ∃ n: ℕ, 0 < n → (n: ℚ)⁻¹ < (a n)

def non_neg(a: regular_sequence) := 
  ∃ n: ℕ, 0 < n → -(n: ℚ)⁻¹ ≤ (a n)


lemma pos_iff{a: regular_sequence} : pos a ↔ ∃ N: ℕ, 0 < N → ∀ m > N, (N: ℚ)⁻¹ < (a m) := 
  begin
    split,
    {
      sorry,
    },
    {
      sorry,
    },
  end

lemma pos_of_equiv{a b: regular_sequence} (H: equivalent a b) : pos a → pos b := 
  begin
    sorry,
  end

lemma non_neg_iff{a: regular_sequence} : non_neg a ↔ ∃ N: ℕ, 0 < N → ∀ m > N, -(N: ℚ)⁻¹ ≤ (a m) := 
  begin
    split,
    {
      sorry,
    },
    {
      sorry,
    },
  end

lemma non_neg_of_equiv{a b: regular_sequence} (H: equivalent a b) : non_neg a → non_neg b := 
  begin
    sorry,
  end

end regular_sequence

