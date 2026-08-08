# Constructive Analysis in Lean 4

Port to **Lean 4 / mathlib4** of the constructive (Bishop-style) construction of
real analysis: the reals as a **quotient of regular sequences** of rationals,
with the order and topology developed **constructively** — no axiom of choice,
no classical logic.

## Status

| Module | Status | Notes |
|---|---|---|
| `RegularSequence` | ✅ | regular sequences, equivalence, setoid, `lim_zero` |
| `Reals` | ✅ | `real := Quotient regular_sequence.equiv`, `Coe ℚ`, neg |
| `Add` | ✅ | 2n-sampling addition, `real.add` well-defined |
| `LimZero` | ✅ | closure of `lim_zero` under `-` |
| `Order` | ✅ | `pos`, `non_neg` and invariance under equivalence |
| `RayTopology` | ✅ | left-ray topology on ℤ via `TopologicalSpace.generateFrom` |
| `Mul` | ⏳ | canonical bounds, `real.mul` |
| `Max` | ⏳ | pointwise max |
| `Field` | ⏳ | field structure on `real` |

## Build

```bash
elan install  # or: curl -sSf https://elan.lean-lang.org/elan-init.sh | sh
lake build
```

Requires the toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.32.2`)
and mathlib4.

## Design

* A regular sequence carries its own modulus of convergence:
  `|seq m - seq n| ≤ m⁻¹ + n⁻¹`.
* Equivalence `a ≈ b` means `|a n - b n| ≤ 2n⁻¹`; the quotient is `real`.
* Everything is constructive: no `Classical`, no `choice`. Where a proof
  would require non-constructive reasoning, it is tracked as an issue
  instead of being hacked in.
* The original Lean 3 sources are kept under [`lean3/`](lean3/) for reference.

## Original project

The Lean 3 original: [Eloitor/Constructive-Analysis-in-Lean](https://github.com/Eloitor/Constructive-Analysis-in-Lean).
