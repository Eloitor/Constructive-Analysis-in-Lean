import ConstructiveAnalysis.RegularSequence
import ConstructiveAnalysis.Reals

/-!
# Addition of regular sequences and reals

Addition on regular sequences samples at `2n`; addition on the quotient
is well-defined via the `j`-form of equivalence.
-/

namespace ConstructiveAnalysis
namespace regular_sequence

/-- Pointwise addition sampled at `2n`. -/
def add (a b : regular_sequence) : regular_sequence :=
  { val := fun n => a (2 * n) + b (2 * n),
    property := by
      intro m n hm hn
      have two_m_pos : 0 < 2 * m := by positivity
      have two_n_pos : 0 < 2 * n := by positivity
      have a_prop := a.property two_m_pos two_n_pos
      have b_prop := b.property two_m_pos two_n_pos
      have hmq : 0 < (m : ℚ) := by exact_mod_cast hm
      have hnq : 0 < (n : ℚ) := by exact_mod_cast hn
      calc
        |a (2 * m) + b (2 * m) - (a (2 * n) + b (2 * n))|
            = |(a (2 * m) - a (2 * n)) + (b (2 * m) - b (2 * n))| := by
              rw [show (a (2 * m) + b (2 * m)) - (a (2 * n) + b (2 * n)) =
                  (a (2 * m) - a (2 * n)) + (b (2 * m) - b (2 * n)) by ring]
        _ ≤ |a (2 * m) - a (2 * n)| + |b (2 * m) - b (2 * n)| := abs_add_le _ _
        _ ≤ (↑(2 * m) : ℚ)⁻¹ + (↑(2 * n) : ℚ)⁻¹ + ((↑(2 * m) : ℚ)⁻¹ + (↑(2 * n) : ℚ)⁻¹) := by
          exact add_le_add a_prop b_prop
        _ = (m : ℚ)⁻¹ + (n : ℚ)⁻¹ := by
          push_cast
          field_simp [hmq.ne', hnq.ne']
          ring }

instance : Add regular_sequence := ⟨add⟩

instance : Sub regular_sequence := ⟨fun a b => add a (neg b)⟩

@[simp] lemma add_apply (a b : regular_sequence) (n : ℕ) : (a + b) n = a (2 * n) + b (2 * n) :=
  rfl

@[simp] lemma add_apply' (a b : regular_sequence) (n : ℕ) :
    (a + b).val n = a (2 * n) + b (2 * n) := rfl

@[simp] lemma sub_apply (a b : regular_sequence) (n : ℕ) : (a - b) n = a (2 * n) - b (2 * n) := by
  change (a + neg b) n = a (2 * n) - b (2 * n)
  rw [add_apply]
  change a (2 * n) + (-b) (2 * n) = a (2 * n) - b (2 * n)
  rw [neg_apply]
  rw [← sub_eq_add_neg]

lemma zero_add {a : regular_sequence} {n : ℕ} : (0 + a) n = a (2 * n) := by
  change (const (0 : ℚ) + a) n = a (2 * n)
  rw [add_apply]
  simp [const]

lemma add_zero {a : regular_sequence} {n : ℕ} : (a + 0) n = a (2 * n) := by
  change (a + const (0 : ℚ)) n = a (2 * n)
  rw [add_apply]
  simp [const]

/-- Sum of two sequences converging to 0 converges to 0. -/
theorem add_lim_zero {f g : regular_sequence} (hf : lim_zero f) (hg : lim_zero g) :
    lim_zero (f + g) := by
  intro j hj
  have h2j : 0 < 2 * j := by positivity
  rcases hf (2 * j) h2j with ⟨N₁, hN₁⟩
  rcases hg (2 * j) h2j with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn2 : n ≤ 2 * n := by omega
  have hN₁' := hN₁ (2 * n) (le_trans (le_of_max_le_left hn) hn2)
  have hN₂' := hN₂ (2 * n) (le_trans (le_of_max_le_right hn) hn2)
  have hjq0 : (j : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  calc
    |(f + g) n| = |f (2 * n) + g (2 * n)| := by rw [add_apply]
    _ ≤ |f (2 * n)| + |g (2 * n)| := abs_add_le _ _
    _ ≤ (↑(2 * j) : ℚ)⁻¹ + (↑(2 * j) : ℚ)⁻¹ := by
      exact add_le_add hN₁' hN₂'
    _ = (j : ℚ)⁻¹ := by
      push_cast
      field_simp [hjq0]
      ring

end regular_sequence

namespace real

/-- Addition of reals, well-defined on regular sequences. -/
def add : real → real → real :=
  Quotient.lift₂ (fun x y => (⟦regular_sequence.add x y⟧ : real)) (by
    intro a₁ b₁ a₂ b₂ ha₁a₂ hb₁b₂
    rw [Quotient.eq]
    change regular_sequence.equivalent (regular_sequence.add a₁ b₁) (regular_sequence.add a₂ b₂)
    rw [regular_sequence.equivalent_iff']
    intro j hj
    have h2j : 0 < 2 * j := by positivity
    rcases (regular_sequence.equivalent_iff'.1 ha₁a₂) (2 * j) h2j with ⟨N, hN⟩
    rcases (regular_sequence.equivalent_iff'.1 hb₁b₂) (2 * j) h2j with ⟨M, hM⟩
    refine ⟨max N M, ?_⟩
    intro n hn
    have hn2 : n ≤ 2 * n := by omega
    have hN' := hN (2 * n) (le_trans (le_of_max_le_left hn) hn2)
    have hM' := hM (2 * n) (le_trans (le_of_max_le_right hn) hn2)
    have hjq0 : (j : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
    calc
      |regular_sequence.add a₁ b₁ n - regular_sequence.add a₂ b₂ n|
          = |(a₁ (2 * n) + b₁ (2 * n)) - (a₂ (2 * n) + b₂ (2 * n))| := by
            rw [show regular_sequence.add a₁ b₁ n = a₁ (2 * n) + b₁ (2 * n) by rfl]
            rw [show regular_sequence.add a₂ b₂ n = a₂ (2 * n) + b₂ (2 * n) by rfl]
      _ = |(a₁ (2 * n) - a₂ (2 * n)) + (b₁ (2 * n) - b₂ (2 * n))| := by
            rw [show (a₁ (2 * n) + b₁ (2 * n)) - (a₂ (2 * n) + b₂ (2 * n)) =
                (a₁ (2 * n) - a₂ (2 * n)) + (b₁ (2 * n) - b₂ (2 * n)) by ring]
      _ ≤ |a₁ (2 * n) - a₂ (2 * n)| + |b₁ (2 * n) - b₂ (2 * n)| := abs_add_le _ _
      _ ≤ (↑(2 * j) : ℚ)⁻¹ + (↑(2 * j) : ℚ)⁻¹ := by
        exact add_le_add hN' hM'
      _ = (j : ℚ)⁻¹ := by
        push_cast
        field_simp [hjq0]
        ring)

instance : Add real := ⟨add⟩

end real

end ConstructiveAnalysis
