module

public import Node.Density
public import Node.ZetaCore

@[expose] public section

/-!
# The learning zeta function of `K = (w₁ w₂)²`

Main results: `node_learning_zeta_integrable`, `node_learning_zeta`, derived from the transfer
lemmas of `Node/Density.lean` and the Mellin transform of `-log s` (`Node/ZetaCore.lean`).
-/

open MeasureTheory Set Filter Topology

namespace Node

lemma measurable_sq_rpow (z : ℝ) : Measurable (fun s : ℝ => (s ^ 2) ^ z) :=
  (measurable_id.pow_const 2).pow_const z

lemma sq_rpow_eq {s : ℝ} (hs : 0 ≤ s) (z : ℝ) : (s ^ 2) ^ z = s ^ (2 * z) := by
  rw [Real.rpow_mul hs, Real.rpow_two]

lemma eqOn_neg_log_mul_sq_rpow (z : ℝ) :
    EqOn (fun s : ℝ => -Real.log s * (s ^ 2) ^ z) (fun s => -Real.log s * s ^ (2 * z))
      (Ioc 0 1) := fun s hs => by
  simp only [sq_rpow_eq hs.1.le]

theorem node_learning_zeta_integrable (z : ℝ) :
    IntegrableOn (fun w : ℝ × ℝ => ((w.1 * w.2) ^ 2) ^ z) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ↔
      -1 / 2 < z := by
  rw [integrableOn_square_comp_iff (fun s : ℝ => (s ^ 2) ^ z) (measurable_sq_rpow z),
    integrableOn_congr_fun (eqOn_neg_log_mul_sq_rpow z) measurableSet_Ioc,
    integrableOn_neg_log_mul_rpow_iff]
  constructor <;> intro h <;> linarith

theorem node_learning_zeta (z : ℝ) (hz : -1 / 2 < z) :
    ∫ w in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ((w.1 * w.2) ^ 2) ^ z = 1 / (2 * z + 1) ^ 2 := by
  rw [integral_square_comp (fun s : ℝ => (s ^ 2) ^ z) (measurable_sq_rpow z),
    setIntegral_congr_fun measurableSet_Ioc (eqOn_neg_log_mul_sq_rpow z),
    integral_neg_log_mul_rpow (by linarith)]

end Node

