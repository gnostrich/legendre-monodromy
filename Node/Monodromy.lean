module

public import Mathlib

@[expose] public section

/-!
# Monodromy of the logarithm, via Mathlib's `IsCoveringMap.monodromy`

Definitions `basePt`, `unitLoop`, `zeroInFibre` are copied verbatim into `ChallengeNode.lean`.
Main result: `node_period_monodromy`, proved with `IsCoveringMap.monodromy_eq_apply_one` and
the explicit lift `θ ↦ 2πiθ`.
-/

open MeasureTheory Set Filter Topology

namespace Node


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

/-- Monodromy of the logarithm: along the loop `θ ↦ exp(2πiθ)` the covering map `exp` sends
the fibre point `0` over `1` to `2πi`. -/
theorem node_period_monodromy :
    (Complex.isCoveringMap_exp.monodromy (Path.Homotopic.Quotient.mk unitLoop) zeroInFibre : ℂ) =
      2 * Real.pi * Complex.I := by
  let Γ : C(unitInterval, ℂ) :=
    ⟨fun θ ↦ 2 * Real.pi * Complex.I * ((θ : ℝ) : ℂ), by fun_prop⟩
  rw [Complex.isCoveringMap_exp.monodromy_eq_apply_one (Γ := Γ)]
  · simp [Γ]
  · funext θ
    rfl
  · simp [Γ, zeroInFibre]

end Node
