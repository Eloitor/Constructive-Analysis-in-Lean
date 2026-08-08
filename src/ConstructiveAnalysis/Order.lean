import ConstructiveAnalysis.RegularSequence
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Tactic

set_option maxHeartbeats 1000000

/-!
# Order on regular sequences

Positive and non-negative regular sequences.

NB: the Lean 3 source stated `non_neg_iff` as an iff with a single eventual
`N`; that statement is **false** (counterexample: `const (-(1 : ℚ) / 10)` is
not `non_neg` but satisfies the right-hand side with `N = 5`). We replace it
with the correct closure properties.
-/

namespace ConstructiveAnalysis
namespace regular_sequence

/-- A regular sequence is *positive* when some term is bounded away from 0
above. -/
def pos (a : regular_sequence) : Prop :=
  ∃ n : ℕ, 0 < n ∧ (n : ℚ)⁻¹ < a n

/-- A regular sequence is *non-negative*: every term is bounded below by the
modulus. -/
def non_neg (a : regular_sequence) : Prop :=
  ∀ n : ℕ, 0 < n → -(n : ℚ)⁻¹ ≤ a n

/-- `pos` is equivalent to the eventual form: eventually all terms are above a
fixed `N⁻¹`. -/
theorem pos_iff {a : regular_sequence} :
    pos a ↔ ∃ N : ℕ, 0 < N ∧ ∀ m, N < m → (N : ℚ)⁻¹ < a m := by
  constructor
  · rintro ⟨n₀, hn₀, hn₀'⟩
    have hδ : 0 < a n₀ - (n₀ : ℚ)⁻¹ := by linarith
    rcases exists_nat_gt (2 / (a n₀ - (n₀ : ℚ)⁻¹)) with ⟨N, hN⟩
    have hNpos : 0 < N := by exact_mod_cast (lt_trans (div_pos (by norm_num) hδ) hN)
    refine ⟨N, hNpos, ?_⟩
    intro m hm
    have hmpos : 0 < m := lt_trans hNpos hm
    have hreg := a.property hmpos hn₀
    have h2 : 2 * (N : ℚ)⁻¹ < a n₀ - (n₀ : ℚ)⁻¹ := by
      have hNq : 0 < (N : ℚ) := by exact_mod_cast hNpos
      have h' : (2 : ℚ) < (N : ℚ) * (a n₀ - (n₀ : ℚ)⁻¹) := (div_lt_iff₀ hδ).mp hN
      rw [← div_eq_mul_inv]
      exact (div_lt_iff₀ hNq).2 (by simpa [mul_comm] using h')
    have ham : a n₀ - (m : ℚ)⁻¹ - (n₀ : ℚ)⁻¹ ≤ a m := by
      have hle := (abs_le.mp hreg).1
      nlinarith
    have hmN' : (m : ℚ)⁻¹ < (N : ℚ)⁻¹ := by
      have hmq : 0 < (m : ℚ) := by exact_mod_cast hmpos
      have hNq : 0 < (N : ℚ) := by exact_mod_cast hNpos
      exact (inv_lt_inv₀ hmq hNq).2 (by exact_mod_cast hm)
    nlinarith [h2, ham, hmN']
  · rintro ⟨N, hNpos, hN'⟩
    refine ⟨N + 1, Nat.succ_pos N, ?_⟩
    have hlt : ((N + 1 : ℕ) : ℚ)⁻¹ < (N : ℚ)⁻¹ := by
      have hN1 : 0 < ((N + 1 : ℕ) : ℚ) := by exact_mod_cast (Nat.succ_pos N)
      have hNq : 0 < (N : ℚ) := by exact_mod_cast hNpos
      exact (inv_lt_inv₀ hN1 hNq).2
        (by exact_mod_cast (Nat.lt_succ_self N) : (N : ℚ) < ((N + 1 : ℕ) : ℚ))
    exact lt_trans hlt (hN' (N + 1) (Nat.lt_succ_self N))

/-- A non-negative sequence is eventually bounded below by `-j⁻¹` at any
precision `j`. -/
theorem non_neg.eventual {a : regular_sequence} (ha : non_neg a) :
    ∀ j : ℕ, 0 < j → ∃ N, ∀ m ≥ N, -(j : ℚ)⁻¹ ≤ a m := by
  intro j hj
  refine ⟨j, ?_⟩
  intro m hm
  have hmpos : 0 < m := lt_of_lt_of_le hj hm
  have hjm : (m : ℚ)⁻¹ ≤ (j : ℚ)⁻¹ := by
    have hmq : 0 < (m : ℚ) := by exact_mod_cast hmpos
    have hjq : 0 < (j : ℚ) := by exact_mod_cast hj
    exact (inv_le_inv₀ hmq hjq).2 (by exact_mod_cast hm)
  have h := ha m hmpos
  nlinarith

/-- Positivity is invariant under equivalence. -/
theorem pos_of_equiv {a b : regular_sequence} (hab : equivalent a b) :
    pos a → pos b := by
  intro hpos
  rcases pos_iff.1 hpos with ⟨N, hNpos, hN'⟩
  let n := max (N + 1) (3 * N + 1)
  have hnpos : 0 < n := by dsimp [n]; omega
  have hgtN : N < n := by dsimp [n]; omega
  have hreg := hab hnpos
  have haN : (N : ℚ)⁻¹ < a n := hN' n hgtN
  have hn3 : 3 * (n : ℚ)⁻¹ < (N : ℚ)⁻¹ := by
    have hnq : 0 < (n : ℚ) := by exact_mod_cast hnpos
    have hNq : 0 < (N : ℚ) := by exact_mod_cast hNpos
    field_simp [hnq.ne', hNq.ne']
    norm_cast
    dsimp [n] at *
    omega
  have hb : (N : ℚ)⁻¹ - 2 * (n : ℚ)⁻¹ < b n := by
    have h1 : a n - 2 * (n : ℚ)⁻¹ ≤ b n := by
      have hle := (abs_le.mp hreg).2
      nlinarith
    nlinarith [haN, h1]
  refine ⟨n, hnpos, ?_⟩
  nlinarith [hb, hn3]

/-- Non-negativity is invariant under equivalence. -/
theorem non_neg_of_equiv {a b : regular_sequence} (hab : equivalent a b) :
    non_neg a → non_neg b := by
  intro hann n hn
  apply regular_sequence.le_of_forall_pos_le_add
  intro ε hε
  rcases exists_nat_gt (4 / ε) with ⟨m, hm⟩
  have hmq : 0 < (m : ℚ) := lt_trans (div_pos (by norm_num : 0 < (4 : ℚ)) hε) hm
  have hmpos : 0 < m := by exact_mod_cast hmq
  have hreg := b.property hmpos hn
  have hequiv := hab hmpos
  have hann_m := hann m hmpos
  have hb : -(n : ℚ)⁻¹ - 4 * (m : ℚ)⁻¹ ≤ b n := by
    have h1 : b m - (m : ℚ)⁻¹ - (n : ℚ)⁻¹ ≤ b n := by
      have hle := (abs_le.mp hreg).2
      nlinarith
    have h2 : a m - 2 * (m : ℚ)⁻¹ ≤ b m := by
      have hle := (abs_le.mp hequiv).2
      nlinarith
    nlinarith [h1, h2, hann_m]
  have hε' : 4 * (m : ℚ)⁻¹ < ε := by
    have hm' : (4 : ℚ) < (m : ℚ) * ε := (div_lt_iff₀ hε).mp hm
    rw [← div_eq_mul_inv]
    exact (div_lt_iff₀ hmq).2 (by simpa [mul_comm] using hm')
  nlinarith [hb, hε']

end regular_sequence

end ConstructiveAnalysis
