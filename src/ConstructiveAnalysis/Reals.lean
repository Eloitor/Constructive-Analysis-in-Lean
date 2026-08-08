import ConstructiveAnalysis.RegularSequence

/-!
# The constructive reals

The reals are the quotient of regular sequences of rationals by
equivalence. The coercion from ℚ is the constant sequence.
-/

namespace ConstructiveAnalysis

/-- The constructive real numbers: quotient of regular sequences. -/
abbrev real := Quotient regular_sequence.equiv

namespace real

instance : Coe ℚ real := ⟨fun x => (⟦regular_sequence.const x⟧ : real)⟩

instance : Zero real := ⟨(0 : ℚ)⟩

instance : One real := ⟨(1 : ℚ)⟩

/-- Negation of reals, well-defined on regular sequences. -/
def neg : real → real :=
  Quotient.lift (fun x => (⟦regular_sequence.neg x⟧ : real)) (by
    intro a b hab
    rw [Quotient.eq]
    intro n hn
    have h := hab hn
    change |(-(a n)) - (-(b n))| ≤ 2 * (n : ℚ)⁻¹
    have hrew : (-(a n)) - (-(b n)) = -(a n - b n) := by ring
    rw [hrew, abs_neg]
    exact h)

instance : Neg real := ⟨neg⟩

end real

end ConstructiveAnalysis
