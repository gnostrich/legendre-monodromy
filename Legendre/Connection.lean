module

public import Legendre.Classification
public import Legendre.Period

@[expose] public section

/-!
# The connection formula `F(1-λ) = (4 log 2 · F(λ) - L(λ)) / π`

Interface theorem (signature fixed): `connection`.
-/

open Complex

namespace Legendre

theorem connection {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1 ∩ Metric.ball 1 1) :
    F (1 - z) = (4 * Real.log 2 * F z - L z) / Real.pi := by
  sorry

end Legendre
