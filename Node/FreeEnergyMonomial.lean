module

public import Node.FreeEnergyStep

@[expose] public section

/-!
# The free energy of monomial models

`monomial_partition_asymptotic`: `Z(n) ≍ n^(-λ) (log n)^(m-1)`, by induction on the dimension
using `base_theta` and `step_theta`; `monomial_free_energy`: `F(n) = λ log n - (m-1) log log n
+ O(1)`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Node

/-- The partition function of the monomial model: with `λ = minⱼ (hⱼ + 1)/(2kⱼ)` attained by
`m` indices (all `kⱼ > 0`, all `hⱼ > -1`),
`Z(n) = ∫_{[0,1]^d} exp(-n K(w)) φ(w) dw ≍ n^{-λ} (log n)^{m-1}` as real `n → ∞`. -/
theorem monomial_partition_asymptotic {d : ℕ} (k : Fin d → ℕ) (hk : ∀ j, 0 < k j)
    (h : Fin d → ℝ) (hh : ∀ j, -1 < h j) (lam : ℝ)
    (hmin : ∀ j, lam ≤ (h j + 1) / (2 * (k j : ℝ)))
    (hattain : ∃ j, (h j + 1) / (2 * (k j : ℝ)) = lam) :
    (fun n : ℝ => ∫ w in Set.univ.pi (fun _ => Icc (0 : ℝ) 1),
        Real.exp (-n * ∏ j, w j ^ (2 * k j)) * ∏ j, w j ^ h j) =Θ[atTop]
      fun n : ℝ => n ^ (-lam) *
        Real.log n ^ ((Finset.univ.filter fun j => (h j + 1) / (2 * (k j : ℝ)) = lam).card - 1) := by
  sorry

/-- The free energy of the monomial model:
`F(n) = -log Z(n) = λ log n - (m - 1) log log n + O(1)` as real `n → ∞`. -/
theorem monomial_free_energy {d : ℕ} (k : Fin d → ℕ) (hk : ∀ j, 0 < k j)
    (h : Fin d → ℝ) (hh : ∀ j, -1 < h j) (lam : ℝ)
    (hmin : ∀ j, lam ≤ (h j + 1) / (2 * (k j : ℝ)))
    (hattain : ∃ j, (h j + 1) / (2 * (k j : ℝ)) = lam) :
    (fun n : ℝ => -Real.log (∫ w in Set.univ.pi (fun _ => Icc (0 : ℝ) 1),
        Real.exp (-n * ∏ j, w j ^ (2 * k j)) * ∏ j, w j ^ h j) -
        (lam * Real.log n -
          (((Finset.univ.filter fun j => (h j + 1) / (2 * (k j : ℝ)) = lam).card : ℝ) - 1) *
            Real.log (Real.log n))) =O[atTop]
      fun _ : ℝ => (1 : ℝ) := by
  sorry

end Node
