import ConstructiveAnalysis.RegularSequence
import ConstructiveAnalysis.Add

/-!
# Limit-zero lemmas

`lim_zero` and `add_lim_zero` live in `RegularSequence` / `Add`; this file
collects the derived closure properties.
-/

namespace ConstructiveAnalysis
namespace regular_sequence

/-- Difference of two sequences converging to 0 converges to 0. -/
theorem sub_lim_zero {a b : regular_sequence} (ha : lim_zero a) (hb : lim_zero b) :
    lim_zero (a - b) := by
  change lim_zero (a + (-b))
  exact add_lim_zero ha (neg_lim_zero hb)

end regular_sequence

end ConstructiveAnalysis
