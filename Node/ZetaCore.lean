module

public import Mathlib

@[expose] public section

/-!
# One-variable integrals `∫₀¹ -log s · s^a ds`

For real `a`, the function `s ↦ -log s * s ^ a` is integrable on `(0, 1]` iff `-1 < a`, and
in that case its integral is `1 / (a + 1) ^ 2`.
-/

open MeasureTheory Set Filter Topology Real

namespace Node

lemma aestronglyMeasurable_neg_log_mul_rpow (a : ℝ) (μ : Measure ℝ) :
    AEStronglyMeasurable (fun s : ℝ => -Real.log s * s ^ a) μ :=
  ((Real.measurable_log.neg).mul (measurable_id.pow_const a)).aestronglyMeasurable

lemma integrableOn_neg_log_mul_rpow {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun s : ℝ => -Real.log s * s ^ a) (Ioc 0 1) := by
  set ε := (a + 1) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hb : -1 < a - ε := by rw [hε_def]; linarith
  have hg : IntegrableOn (fun s : ℝ => s ^ (a - ε) / ε) (Ioc 0 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hb).div_const ε
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
  refine hg.mono' (aestronglyMeasurable_neg_log_mul_rpow a _) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
  have hs0 : 0 < s := hs.1
  have hlog : Real.log s ≤ 0 := Real.log_nonpos hs0.le hs.2
  have hpow : 0 < s ^ a := Real.rpow_pos_of_pos hs0 a
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) hpow.le)]
  have h1 : -Real.log s ≤ s ^ (-ε) / ε := by
    have := Real.log_le_rpow_div (inv_nonneg.2 hs0.le) hε
    rwa [Real.log_inv, Real.inv_rpow hs0.le, ← Real.rpow_neg hs0.le] at this
  calc -Real.log s * s ^ a ≤ s ^ (-ε) / ε * s ^ a := mul_le_mul_of_nonneg_right h1 hpow.le
    _ = s ^ (a - ε) / ε := by
      rw [sub_eq_add_neg, Real.rpow_add hs0, div_mul_eq_mul_div, mul_comm]

lemma not_integrableOn_neg_log_mul_rpow {a : ℝ} (ha : a ≤ -1) :
    ¬ IntegrableOn (fun s : ℝ => -Real.log s * s ^ a) (Ioc 0 1) := by
  intro h
  have hT : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  have hT1 : Real.exp (-1) ≤ 1 := by
    rw [Real.exp_le_one_iff]; norm_num
  have h' : IntegrableOn (fun s : ℝ => -Real.log s * s ^ a) (Ioo 0 (Real.exp (-1))) :=
    h.mono_set (fun s hs => ⟨hs.1, hs.2.le.trans hT1⟩)
  have hpow : IntegrableOn (fun s : ℝ => s ^ a) (Ioo 0 (Real.exp (-1))) := by
    refine h'.mono' (measurable_id.pow_const a).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    have hpos : 0 < s ^ a := Real.rpow_pos_of_pos hs0 a
    have hlog : Real.log s ≤ -1 := by
      rw [← Real.log_exp (-1)]
      exact Real.log_le_log hs0 hs.2.le
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    nlinarith
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hT] at hpow
  linarith

theorem integrableOn_neg_log_mul_rpow_iff (a : ℝ) :
    IntegrableOn (fun s : ℝ => -Real.log s * s ^ a) (Ioc 0 1) ↔ -1 < a := by
  refine ⟨fun h => ?_, integrableOn_neg_log_mul_rpow⟩
  by_contra hne
  exact not_integrableOn_neg_log_mul_rpow (not_lt.1 hne) h

theorem integral_neg_log_mul_rpow {a : ℝ} (ha : -1 < a) :
    ∫ s in Ioc (0 : ℝ) 1, -Real.log s * s ^ a = 1 / (a + 1) ^ 2 := by
  have ha1 : 0 < a + 1 := by linarith
  have ha1' : a + 1 ≠ 0 := ha1.ne'
  rw [← intervalIntegral.integral_of_le zero_le_one]
  set F : ℝ → ℝ := fun s => s ^ (a + 1) / (a + 1) ^ 2 - Real.log s * s ^ (a + 1) / (a + 1)
    with hF
  have hint : IntervalIntegrable (fun s : ℝ => -Real.log s * s ^ a) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact integrableOn_neg_log_mul_rpow ha
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one (f := F)
    (fa := 0) (fb := 1 / (a + 1) ^ 2) (hint := hint) (hderiv := ?hd) (ha := ?h0) (hb := ?h1)]
  · ring
  case hd =>
    intro s hs
    have hs0 : 0 < s := hs.1
    have h1 : HasDerivAt (fun s : ℝ => s ^ (a + 1)) ((a + 1) * s ^ a) s := by
      simpa using Real.hasDerivAt_rpow_const (x := s) (p := a + 1) (Or.inl hs0.ne')
    have h2 : HasDerivAt Real.log s⁻¹ s := Real.hasDerivAt_log hs0.ne'
    have := ((h1.div_const ((a + 1) ^ 2)).sub ((h2.mul h1).div_const (a + 1)))
    convert this using 1
    have hsa : s ^ (a + 1) = s * s ^ a := by
      rw [Real.rpow_add hs0, Real.rpow_one, mul_comm]
    rw [hsa]
    field_simp
    ring
  case h0 =>
    have t1 : Tendsto (fun s : ℝ => s ^ (a + 1)) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (a + 1) (Or.inr ha1.le)).tendsto
      rw [Real.zero_rpow ha1'] at this
      exact this.mono_left nhdsWithin_le_nhds
    have t2 := tendsto_log_mul_rpow_nhdsGT_zero ha1
    have := (t1.div_const ((a + 1) ^ 2)).sub (t2.div_const (a + 1))
    simpa [hF] using this
  case h1 =>
    have hc : ContinuousAt F 1 := by
      rw [hF]
      have : ContinuousAt (fun s : ℝ => s ^ (a + 1)) 1 :=
        Real.continuousAt_rpow_const 1 (a + 1) (Or.inl one_ne_zero)
      exact (this.div_const _).sub
        (((Real.continuousAt_log one_ne_zero).mul this).div_const _)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    convert this using 2
    simp [hF]

end Node
