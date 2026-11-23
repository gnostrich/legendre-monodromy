module

public import Mathlib

@[expose] public section

/-!
# Definitions for the Legendre family

* `Legendre.F` — the period function `F(λ) = ₂F₁(1/2, 1/2; 1; λ)`, Mathlib's
  `ordinaryHypergeometric`.
* `Legendre.coeff n = (C(2n, n) / 4ⁿ)²` — its Taylor coefficients.
* `Legendre.harm n = ∑_{k=1}^{n} 2 / (k (2k - 1))` — the Frobenius correction.
* `Legendre.G λ = ∑ coeff n * harm n * λⁿ` — the analytic part of the second
  Frobenius solution.
* `Legendre.L λ = F λ * log λ + G λ` — the logarithmic solution.
* `Legendre.D` — the slit unit disc `{|λ| < 1} ∩ slitPlane`.
* `Legendre.legendreOp y λ = λ(1-λ) y'' + (1-2λ) y' - y/4` — the Picard–Fuchs
  operator of the Legendre family `y² = x(x-1)(x-λ)`.

These definitions are copied verbatim into `Challenge.lean` and `Solution.lean`.
-/

open Complex

namespace Legendre

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

end Legendre
