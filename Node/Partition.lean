module

public import Node.Density
public import Node.PartitionGauss

@[expose] public section

/-!
# The partition function and free energy of `K = (w₁ w₂)²`

Interface theorems (signatures fixed): `node_partition_sharp`, `node_free_energy`.

Via `Node.integral_square_comp`, `Z(n) = ∫₀¹ e^{-n s²} (-log s) ds`; the one-variable analysis
(Gaussian–logarithm integral, scaling, exponentially small tail) is in `Node.PartitionGauss`.
-/

open MeasureTheory Set Filter Topology

namespace Node

theorem node_partition_sharp :
    (fun n : ℝ => (∫ w in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Real.exp (-n * (w.1 * w.2) ^ 2)) -
        Real.sqrt Real.pi / (4 * Real.sqrt n) *
          (Real.log n + Real.eulerMascheroniConstant + 2 * Real.log 2)) =O[atTop]
      fun n : ℝ => Real.exp (-n) := by
  have h : ∀ n : ℝ, (∫ w in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Real.exp (-n * (w.1 * w.2) ^ 2)) =
      ∫ s in Ioc (0 : ℝ) 1, -Real.log s * Real.exp (-n * s ^ 2) := fun n =>
    integral_square_comp (fun s => Real.exp (-n * s ^ 2)) (by fun_prop)
  simp only [h]
  exact integral_Ioc_gaussLog_isBigO

theorem node_free_energy :
    Tendsto (fun n : ℝ =>
        -Real.log (∫ w in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Real.exp (-n * (w.1 * w.2) ^ 2)) -
          (1 / 2 * Real.log n - Real.log (Real.log n)))
      atTop (𝓝 (Real.log (4 / Real.sqrt Real.pi))) := by
  obtain ⟨C, hC⟩ := integral_Ioc_gaussLogIntegrand_bound
  refine free_energy_of_bound _ C fun n hn => ?_
  rw [integral_square_comp (fun s => Real.exp (-n * s ^ 2)) (by fun_prop)]
  exact hC n hn

end Node
