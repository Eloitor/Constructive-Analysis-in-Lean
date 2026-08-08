import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Tactic

set_option maxHeartbeats 1000000

/-!
# Regular sequences

Constructive (Bishop-style) real numbers as a quotient of *regular sequences*
of rationals. A regular sequence carries its own modulus of convergence:
`|seq m - seq n| ≤ m⁻¹ + n⁻¹`.

The whole port is meant to be constructive: no `Classical`, no `choice`.
-/

namespace ConstructiveAnalysis

/-- A regular sequence of rationals: the modulus of convergence is built into
the definition. -/
def is_regular_sequence (seq : ℕ → ℚ) : Prop :=
  ∀ {m n : ℕ}, 0 < m → 0 < n → |seq m - seq n| ≤ (m : ℚ)⁻¹ + (n : ℚ)⁻¹

/-- The type of regular sequences. -/
def regular_sequence : Type := { f : ℕ → ℚ // is_regular_sequence f }

namespace regular_sequence

instance : CoeFun regular_sequence (fun _ => ℕ → ℚ) := ⟨Subtype.val⟩

@[simp] lemma fn_apply (a : regular_sequence) (n : ℕ) : a n = a.val n := rfl

theorem ext {f g : regular_sequence} (h : ∀ i, f i = g i) : f = g :=
  Subtype.ext (funext h)

theorem is_reg_seq (f : regular_sequence) : is_regular_sequence f.val := f.property

/-- The constant regular sequence. -/
def const (x : ℚ) : regular_sequence :=
  { val := fun _ => x,
    property := by
      intro m n hm hn
      have hmq : 0 < (m : ℚ) := by exact_mod_cast hm
      have hnq : 0 < (n : ℚ) := by exact_mod_cast hn
      simp [sub_self]
      positivity }

instance : Zero regular_sequence := ⟨const 0⟩

instance : One regular_sequence := ⟨const 1⟩

instance : Inhabited regular_sequence := ⟨0⟩

/-- Two regular sequences are equivalent when they converge to the same limit. -/
def equivalent (a b : regular_sequence) : Prop :=
  ∀ {n : ℕ}, 0 < n → |a n - b n| ≤ 2 * (n : ℚ)⁻¹

/-- `lim_zero f` holds when `f` approaches 0. -/
def lim_zero (f : regular_sequence) : Prop :=
  ∀ (j : ℕ), 0 < j → ∃ N, ∀ n ≥ N, |f n| ≤ (j : ℚ)⁻¹

theorem equivalent_refl (a : regular_sequence) : equivalent a a := by
  intro n hn
  simp

theorem equivalent_symm {a b : regular_sequence} (hab : equivalent a b) :
    equivalent b a := by
  intro n hn
  rw [← neg_sub, abs_neg]
  exact hab hn

/-- For ℚ: if `a ≤ b + ε` for every positive `ε`, then `a ≤ b`.
Constructive: only uses the decidable order of ℚ. -/
theorem le_of_forall_pos_le_add {a b : ℚ} (h : ∀ ε : ℚ, 0 < ε → a ≤ b + ε) : a ≤ b := by
  by_contra hb
  have hba : b < a := lt_of_not_ge hb
  let ε : ℚ := (a - b) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have h' : a ≤ b + ε := h ε hε
  have : b + ε < a := by dsimp [ε]; linarith
  exact (not_le_of_gt this) h'

-- The `j`-based (eventual) characterisation of equivalence, used to prove
-- transitivity without any choice.
theorem equivalent_iff' {a b : regular_sequence} :
    equivalent a b ↔ ∀ j : ℕ, 0 < j → ∃ Nj, ∀ n ≥ Nj, |a n - b n| ≤ (j : ℚ)⁻¹ := by
  constructor
  · intro h j hj
    refine ⟨2 * j, ?_⟩
    intro n hn
    have h2j : 0 < 2 * j := by positivity
    have hnj : 0 < n := lt_of_lt_of_le h2j hn
    have h2le : 2 * (n : ℚ)⁻¹ ≤ (j : ℚ)⁻¹ := by
      have hjq : 0 < (j : ℚ) := by exact_mod_cast hj
      have hnq : 0 < (n : ℚ) := by exact_mod_cast hnj
      field_simp [hjq.ne', hnq.ne']
      norm_cast
    exact le_trans (h hnj) h2le
  · intro h n hn
    have key : ∀ j : ℕ, 0 < j → |a n - b n| ≤ 2 * (n : ℚ)⁻¹ + 3 * (j : ℚ)⁻¹ := by
      intro j hj
      rcases h j hj with ⟨Nj, hNj⟩
      let m := max j Nj
      have m_pos : 0 < m := lt_of_lt_of_le hj (le_max_left j Nj)
      have hmN : Nj ≤ m := le_max_right j Nj
      calc
        |a n - b n| = |(a n - a m) + ((a m - b m) + (b m - b n))| := by
          rw [show (a n - a m) + ((a m - b m) + (b m - b n)) = a n - b n by ring]
        _ ≤ |a n - a m| + |(a m - b m) + (b m - b n)| := abs_add_le _ _
        _ ≤ |a n - a m| + (|a m - b m| + |b m - b n|) := by
          nlinarith [abs_add_le (a m - b m) (b m - b n)]
        _ ≤ ((n : ℚ)⁻¹ + (m : ℚ)⁻¹) + ((j : ℚ)⁻¹ + ((m : ℚ)⁻¹ + (n : ℚ)⁻¹)) := by
          exact add_le_add (a.property hn m_pos)
            (add_le_add (hNj m hmN) (b.property m_pos hn))
        _ = 2 * (n : ℚ)⁻¹ + 2 * (m : ℚ)⁻¹ + (j : ℚ)⁻¹ := by ring
        _ ≤ 2 * (n : ℚ)⁻¹ + 2 * (j : ℚ)⁻¹ + (j : ℚ)⁻¹ := by
          have hmj : 2 * (m : ℚ)⁻¹ ≤ 2 * (j : ℚ)⁻¹ := by
            have hjq : 0 < (j : ℚ) := by exact_mod_cast hj
            have hmq : 0 < (m : ℚ) := by exact_mod_cast m_pos
            have hjm : (j : ℚ) ≤ (m : ℚ) := by exact_mod_cast le_max_left j Nj
            have hmj' : (m : ℚ)⁻¹ ≤ (j : ℚ)⁻¹ := (inv_le_inv₀ hmq hjq).2 hjm
            exact mul_le_mul_of_nonneg_left hmj' (by norm_num : (0 : ℚ) ≤ 2)
          nlinarith [hmj]
        _ = 2 * (n : ℚ)⁻¹ + 3 * (j : ℚ)⁻¹ := by ring
    apply le_of_forall_pos_le_add
    intro ε hε
    rcases exists_nat_gt (3 / ε) with ⟨j, hj⟩
    have hjq : 0 < (j : ℚ) := lt_trans (div_pos (by norm_num : 0 < (3 : ℚ)) hε) hj
    have hj_pos : 0 < j := by exact_mod_cast hjq
    have h3 : 3 * (j : ℚ)⁻¹ < ε := by
      have hj' : (3 : ℚ) < ε * (j : ℚ) := by
        field_simp [hε.ne'] at hj
        exact hj
      field_simp [hjq.ne']
      nlinarith [hj']
    calc
      |a n - b n| ≤ 2 * (n : ℚ)⁻¹ + 3 * (j : ℚ)⁻¹ := key j hj_pos
      _ ≤ 2 * (n : ℚ)⁻¹ + ε := by nlinarith [h3]

theorem equivalent_trans {a b c : regular_sequence} (hab : equivalent a b)
    (hbc : equivalent b c) : equivalent a c := by
  rw [equivalent_iff'] at hab hbc ⊢
  intro j hj
  have h2j : 0 < 2 * j := by positivity
  rcases hab (2 * j) h2j with ⟨N, hN⟩
  rcases hbc (2 * j) h2j with ⟨M, hM⟩
  refine ⟨max N M, ?_⟩
  intro n hn
  have hN' := hN n (le_of_max_le_left hn)
  have hM' := hM n (le_of_max_le_right hn)
  have hjq0 : (j : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  calc
    |a n - c n| ≤ |(a n - b n) + (b n - c n)| := by
      rw [show (a n - b n) + (b n - c n) = a n - c n by ring]
    _ ≤ |a n - b n| + |b n - c n| := abs_add_le _ _
    _ ≤ (↑(2 * j) : ℚ)⁻¹ + (↑(2 * j) : ℚ)⁻¹ := add_le_add hN' hM'
    _ = (j : ℚ)⁻¹ := by
      push_cast
      field_simp [hjq0]
      ring

theorem lim_zero_of_equiv {a b : regular_sequence} (hab : equivalent a b)
    (ha : lim_zero a) : lim_zero b := by
  intro j hj
  have h2j : 0 < 2 * j := by positivity
  rcases ha (2 * j) h2j with ⟨N₁, hN₁⟩
  rcases (equivalent_iff'.1 hab) (2 * j) h2j with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hN₁' := hN₁ n (le_of_max_le_left hn)
  have hN₂' := hN₂ n (le_of_max_le_right hn)
  have hjq0 : (j : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  calc
    |b n| = |b n - a n + a n| := by
      rw [show b n - a n + a n = b n by ring]
    _ ≤ |b n - a n| + |a n| := abs_add_le _ _
    _ = |a n - b n| + |a n| := by rw [← neg_sub, abs_neg]
    _ ≤ (↑(2 * j) : ℚ)⁻¹ + (↑(2 * j) : ℚ)⁻¹ := add_le_add hN₂' hN₁'
    _ = (j : ℚ)⁻¹ := by
      push_cast
      field_simp [hjq0]
      ring

/-- The equivalence relation on regular sequences. -/
instance equiv : Setoid regular_sequence :=
  { r := equivalent,
    iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩ }

theorem equivalent_iff {a b : regular_sequence} :
    a ≈ b ↔ ∀ j : ℕ, 0 < j → ∃ Nj, ∀ n ≥ Nj, |a n - b n| ≤ (j : ℚ)⁻¹ :=
  equivalent_iff'

/-- Pointwise negation. -/
def neg (a : regular_sequence) : regular_sequence :=
  { val := fun n => -a n,
    property := by
      intro m n hm hn
      have h := a.property hm hn
      have hrew : (-(a m)) - (-(a n)) = -(a m - a n) := by ring
      rw [hrew, abs_neg]
      exact h }

instance : Neg regular_sequence := ⟨neg⟩

@[simp] lemma neg_apply (a : regular_sequence) (n : ℕ) : (-a) n = -(a n) := rfl

theorem neg_lim_zero {a : regular_sequence} (ha : lim_zero a) : lim_zero (-a) := by
  intro j hj
  rcases ha j hj with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rw [neg_apply, abs_neg]
  exact hN n hn

end regular_sequence

end ConstructiveAnalysis
