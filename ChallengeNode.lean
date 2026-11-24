module

public import Mathlib

@[expose] public section

/-!
# ChallengeNode.lean — one node, one density: period, density of states and the free energy
of a singular learning model (Mathlib-only statements)

The node `f(w) = w₁ w₂` on the unit square `[0,1]²` has one distinguished function,
`P(s) = -log s`. This file states, with `sorry` as every proof:

* `node_density_of_states`: the pushforward of Lebesgue measure on `[0,1]²` under
  `w ↦ w₁ w₂` is the measure with density `-log s` on `(0,1]`. (Equivalently, `-log s` is
  the integral of the Gelfand–Leray form `dw₁ ∧ dw₂ / df` over the fibre `{w₁ w₂ = s}`
  in the square, `∫ₛ¹ dw₁/w₁`.)
* `node_learning_zeta_integrable` and `node_learning_zeta`: for the model with
  `K(w) = (w₁ w₂)²` and uniform prior on `[0,1]²`, the zeta function `ζ(z) = ∫ K^z`
  (real `z`) is finite exactly for `z > -1/2`, where it equals `1/(2z+1)²`. The closed form
  has a double pole at `-1/2`; in Watanabe's singular learning theory this is a learning
  coefficient `1/2` with multiplicity `2`. Meromorphic continuation is not stated.
* `node_partition_sharp`: the partition function `Z(n) = ∫ exp(-n K)` satisfies
  `Z(n) = (√π / (4√n)) (log n + γ + 2 log 2) + O(e^{-n})` as `n → ∞` (real `n`).
* `node_free_energy`: the free energy `F(n) = -log Z(n)` satisfies
  `F(n) = (1/2) log n - log log n + log (4/√π) + o(1)`.
* `node_period_monodromy`: monodromy of the logarithm in Mathlib's sense. For the covering
  map `exp : ℂ → ℂ \ {0}` and the loop `θ ↦ exp(2πiθ)` based at `1` (once counter-clockwise
  around `0`), `IsCoveringMap.monodromy` sends the fibre point `0` to `2πi`. Lifts through
  `exp` are continuations of `log`, so the period `P = -log` continues to `P - 2πi` along this
  loop: unipotent monodromy.

All variables are real except in `node_period_monodromy`; the parameter domain is the closed
unit square with uniform (Lebesgue) prior.

The file imports **only Mathlib** and inlines everything it needs, copied verbatim from
`Node/Monodromy.lean`, in the namespace `NodeChallenge`. The sorry-free proofs are in
`Node/`. This file makes no axiom claim of its own.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.
-/

open MeasureTheory Set Filter Topology

namespace NodeChallenge

/-! ## Definitions — from `Node/Monodromy.lean` (namespace `Node`) -/

/-- The base point `1` of the punctured plane. -/
def basePt : {z : ℂ // z ≠ 0} := ⟨1, one_ne_zero⟩

/-- The loop `θ ↦ exp(2πiθ)`, once counter-clockwise around `0`, based at `1`. -/
noncomputable def unitLoop : Path basePt basePt where
  toFun θ := ⟨Complex.exp (2 * Real.pi * Complex.I * ((θ : ℝ) : ℂ)), Complex.exp_ne_zero _⟩
  continuous_toFun := by fun_prop
  source' := by ext; simp [basePt]
  target' := by ext; simp [basePt]

/-- The point `0` of the fibre of `exp` over the base point `1`. -/
def zeroInFibre :
    (fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) ⁻¹' {basePt} :=
  ⟨0, by ext; simp [basePt]⟩

/-! ## Statements -/

/-- Density of states of the node: the pushforward of Lebesgue measure on the unit square
under `w ↦ w₁ w₂` has density `-log s` on `(0, 1]`. -/
theorem node_density_of_states :
    (volume.restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)).map (fun w : ℝ × ℝ => w.1 * w.2) =
      (volume.restrict (Ioc (0 : ℝ) 1)).withDensity (fun s => ENNReal.ofReal (-Real.log s)) := by
  sorry

/-- The learning zeta function `∫_{[0,1]²} ((w₁w₂)²)^z dw` is finite exactly for `z > -1/2`. -/
theorem node_learning_zeta_integrable (z : ℝ) :
    IntegrableOn (fun w : ℝ × ℝ => ((w.1 * w.2) ^ 2) ^ z) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ↔
      -1 / 2 < z := by
  sorry

/-- The learning zeta function in closed form: `∫_{[0,1]²} ((w₁w₂)²)^z dw = 1/(2z+1)²`
for real `z > -1/2`. -/
theorem node_learning_zeta (z : ℝ) (hz : -1 / 2 < z) :
    ∫ w in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ((w.1 * w.2) ^ 2) ^ z = 1 / (2 * z + 1) ^ 2 := by
  sorry

/-- The partition function `Z(n) = ∫_{[0,1]²} exp(-n (w₁w₂)²) dw` satisfies
`Z(n) = (√π/(4√n)) (log n + γ + 2 log 2) + O(e^{-n})` as real `n → ∞`. -/
theorem node_partition_sharp :
    (fun n : ℝ => (∫ w in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Real.exp (-n * (w.1 * w.2) ^ 2)) -
        Real.sqrt Real.pi / (4 * Real.sqrt n) *
          (Real.log n + Real.eulerMascheroniConstant + 2 * Real.log 2)) =O[atTop]
      fun n : ℝ => Real.exp (-n) := by
  sorry

/-- The free energy `F(n) = -log Z(n)` satisfies
`F(n) - ((1/2) log n - log log n) → log (4/√π)` as real `n → ∞`. -/
theorem node_free_energy :
    Tendsto (fun n : ℝ =>
        -Real.log (∫ w in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Real.exp (-n * (w.1 * w.2) ^ 2)) -
          (1 / 2 * Real.log n - Real.log (Real.log n)))
      atTop (𝓝 (Real.log (4 / Real.sqrt Real.pi))) := by
  sorry

/-- Monodromy of the logarithm: along the loop `θ ↦ exp(2πiθ)` the covering map `exp` sends
the fibre point `0` over `1` to `2πi`. -/
theorem node_period_monodromy :
    (Complex.isCoveringMap_exp.monodromy (Path.Homotopic.Quotient.mk unitLoop) zeroInFibre : ℂ) =
      2 * Real.pi * Complex.I := by
  sorry

end NodeChallenge
