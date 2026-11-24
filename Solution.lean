module

public import Mathlib
public import Legendre

@[expose] public section

/-!
# Solution.lean — comparator bridge for `Challenge.lean`

The identical definitions and theorem statements, with each `sorry` replaced by a
term-level appeal to the named theorem of the development in `Legendre/`. No new
mathematics is introduced.
-/

open Complex

namespace LegendreChallenge

/-! ## Definitions — from `Legendre/Defs.lean` (namespace `Legendre`) -/

/-- The Legendre period function `F(λ) = ₂F₁(1/2, 1/2; 1; λ)`. -/
noncomputable def F (z : ℂ) : ℂ := ordinaryHypergeometric (1 / 2 : ℂ) (1 / 2) 1 z

/-- The Taylor coefficients of `F`: `(C(2n, n) / 4ⁿ)²`. -/
noncomputable def coeff (n : ℕ) : ℂ := ((Nat.centralBinom n : ℂ) / 4 ^ n) ^ 2

/-- The Frobenius correction `∑_{k=1}^{n} 2 / (k (2k - 1))`. -/
noncomputable def harm (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, 2 / (((k : ℂ) + 1) * (2 * k + 1))

/-- The analytic part of the second Frobenius solution at `λ = 0`. -/
noncomputable def G (z : ℂ) : ℂ := ∑' n : ℕ, coeff n * harm n * z ^ n

/-- The logarithmic Frobenius solution `F λ · log λ + G λ`. -/
noncomputable def L (z : ℂ) : ℂ := F z * Complex.log z + G z

/-- The slit unit disc: the open unit disc minus the segment `(-1, 0]`. -/
def D : Set ℂ := Metric.ball 0 1 ∩ Complex.slitPlane

/-- The Legendre Picard–Fuchs operator `λ(1-λ) y'' + (1-2λ) y' - y/4`. -/
noncomputable def legendreOp (y : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (1 - z) * deriv (deriv y) z + (1 - 2 * z) * deriv y z - y z / 4

/-! ## Statements -/

/-- `F` is holomorphic on the unit disc and solves the Picard–Fuchs equation there. -/
theorem F_solves_picardFuchs :
    DifferentiableOn ℂ F (Metric.ball 0 1) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1, legendreOp F z = 0 :=
  ⟨Legendre.F_differentiableOn, fun _ hz => Legendre.F_solves hz⟩

/-- The period integral: `F(λ) = (1/π) ∫₀¹ dx / (√(x(1-x)) (1-λx)^{1/2})` for `|λ| < 1`. -/
theorem F_eq_period_integral (z : ℂ) (hz : ‖z‖ < 1) :
    F z = (1 / (Real.pi : ℂ)) * ∫ x in (0 : ℝ)..1,
      1 / ((Real.sqrt (x * (1 - x)) : ℂ) * (1 - z * x) ^ (1 / 2 : ℂ)) :=
  Legendre.period_integral hz

/-- The Wronskian of the Frobenius basis: `F L' - F' L = 1/(λ(1-λ))` on `D`. -/
theorem wronskian_F_L (z : ℂ) (hz : z ∈ D) :
    F z * deriv L z - deriv F z * L z = 1 / (z * (1 - z)) :=
  Legendre.wronskian hz

/-- The holomorphic solutions of the Picard–Fuchs equation on the slit disc are exactly
the combinations `a F + b L`. -/
theorem solution_space (y : ℂ → ℂ) :
    (DifferentiableOn ℂ y D ∧ ∀ z ∈ D, legendreOp y z = 0) ↔
      ∃ a b : ℂ, ∀ z ∈ D, y z = a * F z + b * L z :=
  Legendre.solution_space y

/-- `F` and `L` are linearly independent on the slit disc. -/
theorem F_L_linearIndependent (a b : ℂ) (h : ∀ z ∈ D, a * F z + b * L z = 0) :
    a = 0 ∧ b = 0 :=
  Legendre.basis_independent a b h

/-- Local monodromy at `λ = 0`: `L` continues holomorphically across the cut `(-1, 0)`
from the upper half-disc to `L + 2πi F` on the lower half-disc. -/
theorem monodromy_at_zero :
    ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (Metric.ball 0 1 \ {z : ℂ | 0 ≤ z.re ∧ z.im = 0}) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < z.im → g z = L z) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, z.im < 0 → g z = L z + 2 * Real.pi * I * F z) :=
  Legendre.monodromy

/-- The connection formula between the Frobenius bases at `λ = 1` and `λ = 0`. -/
theorem connection_formula (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1 ∩ Metric.ball 1 1) :
    F (1 - z) = (4 * Real.log 2 * F z - L z) / Real.pi :=
  Legendre.connection hz

end LegendreChallenge
