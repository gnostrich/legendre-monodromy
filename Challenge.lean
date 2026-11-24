module

public import Mathlib

@[expose] public section

/-!
# Challenge.lean — the Legendre family: Picard–Fuchs equation, period, solution space, monodromy
(Mathlib-only statements)

The Legendre family of elliptic curves `E_λ : y² = x(x-1)(x-λ)` has the period
function `F(λ) = ₂F₁(1/2, 1/2; 1; λ)` (Mathlib's `ordinaryHypergeometric`),
which satisfies the Picard–Fuchs equation
`λ(1-λ) y'' + (1-2λ) y' - y/4 = 0`. Its second Frobenius solution at `λ = 0`
is `L(λ) = F(λ) log λ + G(λ)` with `G(λ) = ∑ₙ aₙ hₙ λⁿ`, where
`aₙ = (C(2n,n)/4ⁿ)²` are the Taylor coefficients of `F` and
`hₙ = ∑_{k=1}^{n} 2/(k(2k-1))`.

This file states, with `sorry` as every proof:

* `F_solves_picardFuchs`: `F` is holomorphic on the unit disc and solves the
  Picard–Fuchs equation there.
* `F_eq_period_integral`: for `|λ| < 1`,
  `F(λ) = (1/π) ∫₀¹ dx / (√(x(1-x)) · (1-λx)^{1/2})` (principal branch),
  i.e. `F` is a period of `E_λ`.
* `wronskian_F_L`: on the slit disc `D = {|λ| < 1} \ (-1, 0]`,
  `F L' - F' L = 1/(λ(1-λ))`.
* `solution_space`: a function `y` is holomorphic on `D` and solves the
  Picard–Fuchs equation there if and only if `y = a F + b L` on `D` for some
  constants `a, b`.
* `F_L_linearIndependent`: `F` and `L` are linearly independent on `D`.
* `monodromy_at_zero`: `L` continues analytically across the cut `(-1, 0)`,
  from the upper half-disc to `L + 2πi F` on the lower half-disc, while `F` is
  holomorphic on the whole disc. In the basis `(F, L)` the local monodromy at
  `λ = 0` is therefore the unipotent matrix `[[1, 2πi], [0, 1]]`.
* `connection_formula`: on the lens `{|λ| < 1} ∩ {|λ - 1| < 1}`,
  `F(1-λ) = (4 log 2 · F(λ) - L(λ)) / π`, which expresses the solution
  regular at `λ = 1` in the Frobenius basis at `λ = 0`.

The file imports **only Mathlib** and inlines every definition it needs,
copied verbatim from `Legendre/Defs.lean`; the one systematic change is that
they live in the namespace `LegendreChallenge` instead of `Legendre`. The
sorry-free proofs are in `Legendre/`. This file makes no axiom claim of its
own.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.
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
      ∀ z ∈ Metric.ball (0 : ℂ) 1, legendreOp F z = 0 := by
  sorry

/-- The period integral: `F(λ) = (1/π) ∫₀¹ dx / (√(x(1-x)) (1-λx)^{1/2})` for `|λ| < 1`. -/
theorem F_eq_period_integral (z : ℂ) (hz : ‖z‖ < 1) :
    F z = (1 / (Real.pi : ℂ)) * ∫ x in (0 : ℝ)..1,
      1 / ((Real.sqrt (x * (1 - x)) : ℂ) * (1 - z * x) ^ (1 / 2 : ℂ)) := by
  sorry

/-- The Wronskian of the Frobenius basis: `F L' - F' L = 1/(λ(1-λ))` on `D`. -/
theorem wronskian_F_L (z : ℂ) (hz : z ∈ D) :
    F z * deriv L z - deriv F z * L z = 1 / (z * (1 - z)) := by
  sorry

/-- The holomorphic solutions of the Picard–Fuchs equation on the slit disc are exactly
the combinations `a F + b L`. -/
theorem solution_space (y : ℂ → ℂ) :
    (DifferentiableOn ℂ y D ∧ ∀ z ∈ D, legendreOp y z = 0) ↔
      ∃ a b : ℂ, ∀ z ∈ D, y z = a * F z + b * L z := by
  sorry

/-- `F` and `L` are linearly independent on the slit disc. -/
theorem F_L_linearIndependent (a b : ℂ) (h : ∀ z ∈ D, a * F z + b * L z = 0) :
    a = 0 ∧ b = 0 := by
  sorry

/-- Local monodromy at `λ = 0`: `L` continues holomorphically across the cut `(-1, 0)`
from the upper half-disc to `L + 2πi F` on the lower half-disc. -/
theorem monodromy_at_zero :
    ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (Metric.ball 0 1 \ {z : ℂ | 0 ≤ z.re ∧ z.im = 0}) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < z.im → g z = L z) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, z.im < 0 → g z = L z + 2 * Real.pi * I * F z) := by
  sorry

/-- The connection formula between the Frobenius bases at `λ = 1` and `λ = 0`. -/
theorem connection_formula (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1 ∩ Metric.ball 1 1) :
    F (1 - z) = (4 * Real.log 2 * F z - L z) / Real.pi := by
  sorry

end LegendreChallenge
