module

public import Mathlib

@[expose] public section

/-!
# Density of states of the node `w₁ w₂` on the unit square

Interface theorems (signatures fixed): `node_density_of_states`, `lintegral_square_comp`,
`integral_square_comp`, `integrableOn_square_comp_iff`.

The push-forward of Lebesgue measure on `[0,1]²` under `w ↦ w₁ w₂` has density `-log s` on
`(0,1]`. We prove this by comparing the two (finite) measures on all half-lines `Iic s`: both
equal `s - s log s` for `0 < s ≤ 1`, vanish for `s ≤ 0` and equal `1` for `s ≥ 1`. The left side
is computed slice-wise via `Measure.prod_apply`, the right side via `integral_log_from_zero`.
-/

open MeasureTheory Set Filter Topology

namespace Node

/-- The cumulative mass of the push-forward, expressed as a one-dimensional integral. -/
theorem density_map_Iic (s : ℝ) :
    (volume.restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)).map (fun w : ℝ × ℝ => w.1 * w.2)
        (Iic s) = ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (min 1 (s / x)) := by
  have hf : Measurable (fun w : ℝ × ℝ => w.1 * w.2) := by fun_prop
  have hS : MeasurableSet (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  rw [Measure.map_apply hf measurableSet_Iic, Measure.restrict_apply (hf measurableSet_Iic),
    Measure.volume_eq_prod, Measure.prod_apply ((hf measurableSet_Iic).inter hS),
    ← lintegral_indicator measurableSet_Ioc]
  have h0 : ∀ᵐ x : ℝ, x ∉ ({0} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton)
  refine lintegral_congr_ae ?_
  filter_upwards [h0] with x hx
  simp only [mem_singleton_iff] at hx
  by_cases hxI : x ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hxI]
    have : Prod.mk x ⁻¹' ((fun w : ℝ × ℝ => w.1 * w.2) ⁻¹' Iic s ∩ Icc 0 1 ×ˢ Icc 0 1) =
        Icc 0 (min 1 (s / x)) := by
      ext y
      simp only [mem_preimage, mem_inter_iff, mem_Iic, mem_prod, mem_Icc, le_min_iff]
      rw [le_div_iff₀ hxI.1]
      constructor
      · rintro ⟨h1, -, h2, h3⟩
        exact ⟨h2, h3, by linarith⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨by linarith, ⟨hxI.1.le, hxI.2⟩, h1, h2⟩
    rw [this, Real.volume_Icc, sub_zero]
  · rw [indicator_of_notMem hxI]
    have : Prod.mk x ⁻¹' ((fun w : ℝ × ℝ => w.1 * w.2) ⁻¹' Iic s ∩ Icc 0 1 ×ˢ Icc 0 1) =
        ∅ := by
      ext y
      simp only [mem_preimage, mem_inter_iff, mem_Iic, mem_prod, mem_Icc, mem_empty_iff_false,
        iff_false, not_and]
      intro _ h1 _ _
      exact hxI ⟨lt_of_le_of_ne h1.1 (Ne.symm hx), h1.2⟩
    rw [this, measure_empty]

/-- The cumulative mass of the density measure. -/
theorem density_withDensity_Iic (s : ℝ) :
    (volume.restrict (Ioc (0 : ℝ) 1)).withDensity (fun s => ENNReal.ofReal (-Real.log s))
        (Iic s) = ∫⁻ x in Ioc (0 : ℝ) (min 1 s), ENNReal.ofReal (-Real.log x) := by
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    inter_comm, Ioc_inter_Iic]

theorem lintegral_neg_log_Ioc {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ∫⁻ x in Ioc (0 : ℝ) s, ENNReal.ofReal (-Real.log x) = ENNReal.ofReal (s - s * Real.log s) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_neg, ← intervalIntegral.integral_of_le hs, integral_log_from_zero]
    ring
  · exact (intervalIntegral.intervalIntegrable_log'.neg).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact neg_nonneg.2 (Real.log_nonpos hx.1.le (hx.2.trans hs1))

theorem lintegral_div_Ioc {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∫⁻ x in Ioc s 1, ENNReal.ofReal (s / x) = ENNReal.ofReal (-(s * Real.log s)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← intervalIntegral.integral_of_le hs1]
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hs one_pos, one_div,
      Real.log_inv]
    ring
  · refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_const.div continuousOn_id fun x hx => (hs.trans_le hx.1).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact div_nonneg hs.le (hs.trans hx.1).le

theorem node_density_of_states :
    (volume.restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)).map (fun w : ℝ × ℝ => w.1 * w.2) =
      (volume.restrict (Ioc (0 : ℝ) 1)).withDensity (fun s => ENNReal.ofReal (-Real.log s)) := by
  have : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.2 (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  refine Measure.ext_of_Iic _ _ fun s => ?_
  rw [density_map_Iic, density_withDensity_Iic]
  rcases le_or_gt s 0 with hs | hs
  · rw [Ioc_eq_empty (not_lt.2 (min_le_right _ _ |>.trans hs)), Measure.restrict_empty,
      lintegral_zero_measure]
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 0), lintegral_zero]
    intro x hx
    simp only [ENNReal.ofReal_eq_zero]
    exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg hs hx.1.le)
  rcases le_or_gt s 1 with hs1 | hs1
  · rw [min_eq_right hs1, lintegral_neg_log_Ioc hs.le hs1,
      ← Ioc_union_Ioc_eq_Ioc hs.le hs1, lintegral_union measurableSet_Ioc
        (Ioc_disjoint_Ioc_of_le le_rfl)]
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 1),
      setLIntegral_congr_fun (s := Ioc s 1) measurableSet_Ioc
        (g := fun x => ENNReal.ofReal (s / x)),
      lintegral_div_Ioc hs hs1, setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero,
      ← ENNReal.ofReal_add hs.le]
    · congr 1
    · have := Real.log_nonpos hs.le hs1
      nlinarith
    · intro x hx
      simp only
      rw [min_eq_right ((div_le_one (hs.trans hx.1)).2 hx.1.le)]
    · intro x hx
      simp only
      rw [min_eq_left ((le_div_iff₀ hx.1).2 (by linarith [hx.2])), ENNReal.ofReal_one]
  · rw [min_eq_left hs1.le, lintegral_neg_log_Ioc zero_le_one le_rfl,
      setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 1), setLIntegral_const, one_mul,
      Real.volume_Ioc]
    · simp
    · intro x hx
      simp only
      rw [min_eq_left ((le_div_iff₀ hx.1).2 (by linarith [hx.2])), ENNReal.ofReal_one]

theorem lintegral_square_comp (g : ℝ → ENNReal) (hg : Measurable g) :
    ∫⁻ w in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g (w.1 * w.2) =
      ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (-Real.log s) * g s := by
  rw [← lintegral_map hg (by fun_prop), node_density_of_states,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hg]
  rfl

theorem integral_square_comp (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ w in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g (w.1 * w.2) =
      ∫ s in Ioc (0 : ℝ) 1, -Real.log s * g s := by
  rw [← integral_map (by fun_prop) hg.aestronglyMeasurable, node_density_of_states,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (neg_nonneg.2 (Real.log_nonpos hx.1.le hx.2))]

theorem integrableOn_square_comp_iff (g : ℝ → ℝ) (hg : Measurable g) :
    IntegrableOn (fun w : ℝ × ℝ => g (w.1 * w.2)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ↔
      IntegrableOn (fun s => -Real.log s * g s) (Ioc (0 : ℝ) 1) := by
  change Integrable (g ∘ fun w : ℝ × ℝ => w.1 * w.2) _ ↔ _
  rw [← integrable_map_measure hg.aestronglyMeasurable (by fun_prop), node_density_of_states,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (neg_nonneg.2 (Real.log_nonpos hx.1.le hx.2))]

end Node
