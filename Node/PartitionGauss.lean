module

public import Mathlib

@[expose] public section

/-!
# Gaussian–logarithm integrals

We compute `∫₀^∞ e^{-v²} log v dv = -(√π/4)(γ + 2 log 2)` from the value of `Γ'(1/2)`.
-/

open MeasureTheory Set Filter Topology Real

namespace Node

theorem integral_Ioi_rpow_log_exp_half :
    ∫ t in Ioi (0 : ℝ), t ^ ((1 / 2 : ℝ) - 1) * (Real.log t * Real.exp (-t)) =
      -√π * (eulerMascheroniConstant + 2 * Real.log 2) :=
  (Real.hasDerivAt_Gamma_of_pos one_half_pos).unique Real.hasDerivAt_Gamma_one_half

theorem integral_Ioi_log_mul_exp_neg_sq :
    ∫ v in Ioi (0 : ℝ), Real.log v * Real.exp (-v ^ 2) =
      -(√π / 4) * (eulerMascheroniConstant + 2 * Real.log 2) := by
  have h := integral_comp_rpow_Ioi_of_pos (p := 2) two_pos
    (g := fun t : ℝ => t ^ ((1 / 2 : ℝ) - 1) * (Real.log t * Real.exp (-t)))
  rw [integral_Ioi_rpow_log_exp_half] at h
  have h2 : ∫ x in Ioi (0 : ℝ), ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) •
      ((fun t : ℝ => t ^ ((1 / 2 : ℝ) - 1) * (Real.log t * Real.exp (-t))) (x ^ (2 : ℝ))) =
      ∫ x in Ioi (0 : ℝ), 4 * (Real.log x * Real.exp (-x ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx : 0 < x := hx
    simp only [smul_eq_mul]
    rw [← Real.rpow_mul hx.le, Real.log_rpow hx]
    norm_num
    rw [Real.rpow_neg_one]
    field_simp
    ring
  rw [h2, integral_const_mul] at h
  linarith

end Node
