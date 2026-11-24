module

public import Mathlib

@[expose] public section

/-!
# One-variable Laplace-type estimates for the monomial free energy

`base_theta`: `∫₀¹ w^h exp(-n w^(2k)) dw ≍ n^(-a)` with `a = (h+1)/(2k)`.
`step_theta`: if `G` is continuous, positive, antitone and `G(x) ≍ x^(-μ) (log x)^p`, then
`∫₀¹ w^h G(n w^(2k)) dw` is `≍ n^(-a)` if `a < μ`, `≍ n^(-μ) (log n)^(p+1)` if `a = μ`,
and `≍ n^(-μ) (log n)^p` if `a > μ`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Node

theorem base_theta (k : ℕ) (hk : 0 < k) (h : ℝ) (hh : -1 < h) :
    (fun n : ℝ => ∫ w in Ioc (0 : ℝ) 1, w ^ h * Real.exp (-n * w ^ (2 * k))) =Θ[atTop]
      fun n : ℝ => n ^ (-((h + 1) / (2 * (k : ℝ)))) := by
  sorry

theorem step_theta (k : ℕ) (hk : 0 < k) (h : ℝ) (hh : -1 < h) (μ : ℝ) (hμ : 0 < μ) (p : ℕ)
    (G : ℝ → ℝ) (hGc : Continuous G) (hGpos : ∀ x, 0 < G x) (hGanti : Antitone G)
    (hGθ : G =Θ[atTop] fun x : ℝ => x ^ (-μ) * Real.log x ^ p) :
    (fun n : ℝ => ∫ w in Ioc (0 : ℝ) 1, w ^ h * G (n * w ^ (2 * k))) =Θ[atTop]
      fun n : ℝ =>
        if (h + 1) / (2 * (k : ℝ)) < μ then n ^ (-((h + 1) / (2 * (k : ℝ))))
        else if (h + 1) / (2 * (k : ℝ)) = μ then n ^ (-μ) * Real.log n ^ (p + 1)
        else n ^ (-μ) * Real.log n ^ p := by
  sorry

end Node
