module

public import Legendre.Defs

@[expose] public section

/-!
# `F`, `G` and `L` solve the Picard–Fuchs equation; the Wronskian

Interface theorems (signatures fixed; other files depend on them):
`F_eq_tsum`, `F_differentiableOn`, `G_differentiableOn`, `F_solves`,
`L_differentiableOn`, `L_solves`, `wronskian`.
-/

open Complex

namespace Legendre

theorem F_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) : F z = ∑' n : ℕ, coeff n * z ^ n := by
  sorry

theorem F_differentiableOn : DifferentiableOn ℂ F (Metric.ball 0 1) := by
  sorry

theorem G_differentiableOn : DifferentiableOn ℂ G (Metric.ball 0 1) := by
  sorry

theorem F_solves {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) : legendreOp F z = 0 := by
  sorry

theorem L_differentiableOn : DifferentiableOn ℂ L D := by
  sorry

theorem L_solves {z : ℂ} (hz : z ∈ D) : legendreOp L z = 0 := by
  sorry

theorem wronskian {z : ℂ} (hz : z ∈ D) :
    F z * deriv L z - deriv F z * L z = 1 / (z * (1 - z)) := by
  sorry

end Legendre
