module

public import Mathlib

@[expose] public section

/-!
# The monomial (normal-crossing) zeta function and the learning coefficient `(λ, m)`

For `K(w) = ∏ⱼ wⱼ^(2kⱼ)` and prior density `∏ⱼ wⱼ^(hⱼ)` on `[0,1]^d`: integrability of
`K^z φ`, the closed form `∏ⱼ 1/(2kⱼ z + hⱼ + 1)`, and the pole of order `m` at `-λ`.

Interface theorems (signatures fixed): `monomial_zeta_integrable`, `monomial_zeta`,
`monomial_pole`.
-/

open MeasureTheory Set Filter Topology

namespace Node

/-- The monomial (normal-crossing) zeta function: for `K(w) = ∏ⱼ wⱼ^(2kⱼ)` and the prior
density `φ(w) = ∏ⱼ wⱼ^(hⱼ)` on `[0,1]^d` (not normalized), `K^z φ` is integrable on the cube
exactly when `2kⱼ z + hⱼ + 1 > 0` for every `j` (real `z`). -/
theorem monomial_zeta_integrable {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (z : ℝ) :
    IntegrableOn (fun w : Fin d → ℝ => (∏ j, w j ^ (2 * k j)) ^ z * ∏ j, w j ^ h j)
        (Set.univ.pi fun _ => Icc (0 : ℝ) 1) ↔
      ∀ j, 0 < 2 * (k j : ℝ) * z + h j + 1 := by
  sorry

/-- The monomial zeta function in closed form:
`∫_{[0,1]^d} K^z φ = ∏ⱼ 1/(2kⱼ z + hⱼ + 1)` whenever every factor is positive. -/
theorem monomial_zeta {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (z : ℝ)
    (hz : ∀ j, 0 < 2 * (k j : ℝ) * z + h j + 1) :
    ∫ w in Set.univ.pi (fun _ => Icc (0 : ℝ) 1), (∏ j, w j ^ (2 * k j)) ^ z * ∏ j, w j ^ h j =
      ∏ j, 1 / (2 * (k j : ℝ) * z + h j + 1) := by
  sorry

/-- The learning coefficient and its multiplicity for the monomial model. Let `λ` be the
smallest of the numbers `(hⱼ + 1)/(2kⱼ)` (all `kⱼ > 0`) and `m ≥ 1` the number of indices
attaining it. Then `(z + λ)^m ζ(z)` tends to a nonzero limit as `z → -λ` from above, where
`ζ(z) = ∫_{[0,1]^d} K^z φ`: the zeta function has a pole of order exactly `m` at `-λ`
(real variable, one-sided; meromorphic continuation is not stated). -/
theorem monomial_pole {d : ℕ} (k : Fin d → ℕ) (hk : ∀ j, 0 < k j) (h : Fin d → ℝ) (lam : ℝ)
    (hmin : ∀ j, lam ≤ (h j + 1) / (2 * (k j : ℝ)))
    (hattain : ∃ j, (h j + 1) / (2 * (k j : ℝ)) = lam) :
    0 < (Finset.univ.filter fun j => (h j + 1) / (2 * (k j : ℝ)) = lam).card ∧
      ∃ c : ℝ, c ≠ 0 ∧
        Tendsto (fun z : ℝ =>
            (z + lam) ^ (Finset.univ.filter fun j => (h j + 1) / (2 * (k j : ℝ)) = lam).card *
              ∫ w in Set.univ.pi (fun _ => Icc (0 : ℝ) 1),
                (∏ j, w j ^ (2 * k j)) ^ z * ∏ j, w j ^ h j)
          (𝓝[>] (-lam)) (𝓝 c) := by
  sorry

end Node
