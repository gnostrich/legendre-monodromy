module

public import Mathlib
public import Node

@[expose] public section

/-!
# SolutionNode.lean — comparator bridge for `ChallengeNode.lean`

The identical definitions and theorem statements, with each `sorry` replaced by a
term-level appeal to the named theorem of the development in `Node/`. No new mathematics is
introduced.
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
      (volume.restrict (Ioc (0 : ℝ) 1)).withDensity (fun s => ENNReal.ofReal (-Real.log s)) :=
  Node.node_density_of_states

/-- The learning zeta function `∫_{[0,1]²} ((w₁w₂)²)^z dw` is finite exactly for `z > -1/2`. -/
theorem node_learning_zeta_integrable (z : ℝ) :
    IntegrableOn (fun w : ℝ × ℝ => ((w.1 * w.2) ^ 2) ^ z) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ↔
      -1 / 2 < z :=
  Node.node_learning_zeta_integrable z

/-- The learning zeta function in closed form: `∫_{[0,1]²} ((w₁w₂)²)^z dw = 1/(2z+1)²`
for real `z > -1/2`. -/
theorem node_learning_zeta (z : ℝ) (hz : -1 / 2 < z) :
    ∫ w in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ((w.1 * w.2) ^ 2) ^ z = 1 / (2 * z + 1) ^ 2 :=
  Node.node_learning_zeta z hz

/-- The partition function `Z(n) = ∫_{[0,1]²} exp(-n (w₁w₂)²) dw` satisfies
`Z(n) = (√π/(4√n)) (log n + γ + 2 log 2) + O(e^{-n})` as real `n → ∞`. -/
theorem node_partition_sharp :
    (fun n : ℝ => (∫ w in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Real.exp (-n * (w.1 * w.2) ^ 2)) -
        Real.sqrt Real.pi / (4 * Real.sqrt n) *
          (Real.log n + Real.eulerMascheroniConstant + 2 * Real.log 2)) =O[atTop]
      fun n : ℝ => Real.exp (-n) :=
  Node.node_partition_sharp

/-- The free energy `F(n) = -log Z(n)` satisfies
`F(n) - ((1/2) log n - log log n) → log (4/√π)` as real `n → ∞`. -/
theorem node_free_energy :
    Tendsto (fun n : ℝ =>
        -Real.log (∫ w in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Real.exp (-n * (w.1 * w.2) ^ 2)) -
          (1 / 2 * Real.log n - Real.log (Real.log n)))
      atTop (𝓝 (Real.log (4 / Real.sqrt Real.pi))) :=
  Node.node_free_energy

/-- Monodromy of the logarithm: along the loop `θ ↦ exp(2πiθ)` the covering map `exp` sends
the fibre point `0` over `1` to `2πi`. -/
theorem node_period_monodromy :
    (Complex.isCoveringMap_exp.monodromy (Path.Homotopic.Quotient.mk unitLoop) zeroInFibre : ℂ) =
      2 * Real.pi * Complex.I :=
  Node.node_period_monodromy

end NodeChallenge
