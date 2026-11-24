module

public import Mathlib

@[expose] public section

/-!
# Gaussian–logarithm integrals

We compute `∫₀^∞ e^{-v²} log v dv = -(√π/4)(γ + 2 log 2)` from the value of `Γ'(1/2)`.
-/

open MeasureTheory Set Filter Topology Real

namespace Node

theorem integral_Ioi_rpow_log_exp_half :
    ∫ t in Ioi (0 : ℝ), t ^ ((1 / 2 : ℝ) - 1) * (Real.log t * Real.exp (-t)) =
      -√π * (eulerMascheroniConstant + 2 * Real.log 2) :=
  (Real.hasDerivAt_Gamma_of_pos one_half_pos).unique Real.hasDerivAt_Gamma_one_half

theorem integral_Ioi_log_mul_exp_neg_sq :
    ∫ v in Ioi (0 : ℝ), Real.log v * Real.exp (-v ^ 2) =
      -(√π / 4) * (eulerMascheroniConstant + 2 * Real.log 2) := by
  have h := integral_comp_rpow_Ioi_of_pos (p := 2) two_pos
    (g := fun t : ℝ => t ^ ((1 / 2 : ℝ) - 1) * (Real.log t * Real.exp (-t)))
  rw [integral_Ioi_rpow_log_exp_half] at h
  have h2 : ∫ x in Ioi (0 : ℝ), ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) •
      ((fun t : ℝ => t ^ ((1 / 2 : ℝ) - 1) * (Real.log t * Real.exp (-t))) (x ^ (2 : ℝ))) =
      ∫ x in Ioi (0 : ℝ), 4 * (Real.log x * Real.exp (-x ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx : 0 < x := hx
    simp only [smul_eq_mul]
    rw [← Real.rpow_mul hx.le, Real.log_rpow hx]
    norm_num
    rw [Real.rpow_neg_one]
    field_simp
    ring
  rw [h2, integral_const_mul] at h
  linarith

theorem integrableOn_log_mul_exp_neg_sq :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v ^ 2)) (Ioi 0) := by
  by_contra h
  have h0 := integral_undef h
  rw [integral_Ioi_log_mul_exp_neg_sq] at h0
  have hγ := one_half_lt_eulerMascheroniConstant
  have hl := Real.log_pos one_lt_two
  have hπ := Real.sqrt_pos.2 Real.pi_pos
  nlinarith

theorem integrableOn_exp_neg_sq_Ioi :
    IntegrableOn (fun v : ℝ => Real.exp (-v ^ 2)) (Ioi 0) := by
  simpa using (integrable_exp_neg_mul_sq (b := 1) one_pos).integrableOn (s := Ioi 0)

theorem integral_exp_neg_sq_Ioi :
    ∫ v in Ioi (0 : ℝ), Real.exp (-v ^ 2) = √π / 2 := by
  simpa using integral_gaussian_Ioi 1

/-- The integrand `-log s · e^{-n s²}`. -/
noncomputable def gaussLogIntegrand (n s : ℝ) : ℝ := -Real.log s * Real.exp (-n * s ^ 2)

/-- The main term `√π/(4√n) (log n + γ + 2 log 2)`. -/
noncomputable def gaussLogMain (n : ℝ) : ℝ :=
  √π / (4 * √n) * (Real.log n + eulerMascheroniConstant + 2 * Real.log 2)

theorem gaussLogIntegrand_scale {n x : ℝ} (hn : 0 < n) (hx : 0 < x) :
    gaussLogIntegrand n ((√n)⁻¹ * x) =
      -(Real.log x * Real.exp (-x ^ 2)) + Real.log n / 2 * Real.exp (-x ^ 2) := by
  have hs : 0 < √n := Real.sqrt_pos.2 hn
  unfold gaussLogIntegrand
  rw [Real.log_mul (inv_pos.2 hs).ne' hx.ne', Real.log_inv, Real.log_sqrt hn.le]
  have : -n * ((√n)⁻¹ * x) ^ 2 = -x ^ 2 := by
    rw [mul_pow, inv_pow, Real.sq_sqrt hn.le]
    field_simp
  rw [this]
  ring

theorem integrableOn_gaussLogIntegrand {n : ℝ} (hn : 0 < n) :
    IntegrableOn (gaussLogIntegrand n) (Ioi 0) := by
  have hb : 0 < (√n)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hn)
  have h := integrableOn_Ioi_comp_mul_left_iff (gaussLogIntegrand n) 0 hb
  rw [mul_zero] at h
  refine h.1 ?_
  refine IntegrableOn.congr_fun
    (integrableOn_log_mul_exp_neg_sq.neg.add (integrableOn_exp_neg_sq_Ioi.const_mul _))
    (fun x hx => (gaussLogIntegrand_scale hn hx).symm) measurableSet_Ioi

theorem integral_Ioi_gaussLogIntegrand {n : ℝ} (hn : 0 < n) :
    ∫ s in Ioi (0 : ℝ), gaussLogIntegrand n s = gaussLogMain n := by
  have hs : 0 < √n := Real.sqrt_pos.2 hn
  have hb : 0 < (√n)⁻¹ := inv_pos.2 hs
  have h := integral_comp_mul_left_Ioi (gaussLogIntegrand n) 0 hb
  rw [mul_zero, inv_inv, smul_eq_mul] at h
  have h2 : ∫ x in Ioi (0 : ℝ), gaussLogIntegrand n ((√n)⁻¹ * x) =
      ∫ x in Ioi (0 : ℝ), (-(Real.log x * Real.exp (-x ^ 2)) +
        Real.log n / 2 * Real.exp (-x ^ 2)) :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => gaussLogIntegrand_scale hn hx
  have hi1 : IntegrableOn (fun x : ℝ => -(Real.log x * Real.exp (-x ^ 2))) (Ioi 0) :=
    integrableOn_log_mul_exp_neg_sq.neg
  rw [h2, integral_add hi1 (integrableOn_exp_neg_sq_Ioi.const_mul _), integral_neg, integral_const_mul,
    integral_Ioi_log_mul_exp_neg_sq, integral_exp_neg_sq_Ioi] at h
  have h3 : ∫ s in Ioi (0 : ℝ), gaussLogIntegrand n s =
      (√n)⁻¹ * (√n * ∫ s in Ioi (0 : ℝ), gaussLogIntegrand n s) := by
    field_simp
  rw [h3, ← h]
  unfold gaussLogMain
  field_simp
  ring

theorem integral_Ioc_gaussLogIntegrand {n : ℝ} (hn : 0 < n) :
    ∫ s in Ioc (0 : ℝ) 1, gaussLogIntegrand n s =
      gaussLogMain n - ∫ s in Ioi (1 : ℝ), gaussLogIntegrand n s := by
  have hi := integrableOn_gaussLogIntegrand hn
  rw [← integral_Ioi_gaussLogIntegrand hn, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi zero_le_one))]
  ring

theorem tail_gaussLogIntegrand_bound : ∃ C : ℝ, ∀ n : ℝ, 1 ≤ n →
    |∫ s in Ioi (1 : ℝ), gaussLogIntegrand n s| ≤ C * Real.exp (-n) := by
  refine ⟨Real.exp 1 * ∫ s in Ioi (1 : ℝ), Real.log s * Real.exp (-s ^ 2), fun n hn => ?_⟩
  have hG : IntegrableOn (fun s : ℝ => Real.log s * Real.exp (-s ^ 2)) (Ioi 1) :=
    integrableOn_log_mul_exp_neg_sq.mono_set (Ioi_subset_Ioi zero_le_one)
  rw [← Real.norm_eq_abs, mul_comm, ← mul_assoc, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hG.const_mul _) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
  have hs : 1 < s := hs
  have hl : 0 ≤ Real.log s := Real.log_nonneg hs.le
  unfold gaussLogIntegrand
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hl, abs_of_pos (Real.exp_pos _)]
  have hns : 0 ≤ (n - 1) * (s ^ 2 - 1) := mul_nonneg (by linarith) (by nlinarith)
  calc Real.log s * Real.exp (-n * s ^ 2) ≤ Real.log s * Real.exp (-n + 1 + -s ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hl
    _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

theorem integral_Ioc_gaussLogIntegrand_bound : ∃ C : ℝ, ∀ n : ℝ, 1 ≤ n →
    |(∫ s in Ioc (0 : ℝ) 1, gaussLogIntegrand n s) - gaussLogMain n| ≤ C * Real.exp (-n) := by
  obtain ⟨C, hC⟩ := tail_gaussLogIntegrand_bound
  refine ⟨C, fun n hn => ?_⟩
  rw [integral_Ioc_gaussLogIntegrand (by linarith), sub_sub_cancel_left, abs_neg]
  exact hC n hn

/-- One-variable form of the sharp partition-function asymptotic. -/
theorem integral_Ioc_gaussLog_isBigO :
    (fun n : ℝ => (∫ s in Ioc (0 : ℝ) 1, -Real.log s * Real.exp (-n * s ^ 2)) -
        √π / (4 * √n) * (Real.log n + eulerMascheroniConstant + 2 * Real.log 2)) =O[atTop]
      fun n : ℝ => Real.exp (-n) := by
  obtain ⟨C, hC⟩ := integral_Ioc_gaussLogIntegrand_bound
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hC n hn

/-- Free-energy asymptotic from the sharp bound, as a statement about real functions. -/
theorem free_energy_of_bound (Z : ℝ → ℝ) (C : ℝ)
    (hZ : ∀ n : ℝ, 1 ≤ n → |Z n - gaussLogMain n| ≤ C * Real.exp (-n)) :
    Tendsto (fun n : ℝ => -Real.log (Z n) - (1 / 2 * Real.log n - Real.log (Real.log n)))
      atTop (𝓝 (Real.log (4 / √π))) := by
  have hC : 0 ≤ C := by
    have h1 := hZ 1 le_rfl
    have := (abs_nonneg _).trans h1
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have hπ : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  set c := eulerMascheroniConstant + 2 * Real.log 2
  set T : ℝ → ℝ := fun n => Z n - gaussLogMain n
  set u : ℝ → ℝ := fun n => Z n * (4 * √n) / (√π * Real.log n)
  -- `√n T n → 0`
  have hT : Tendsto (fun n => √n * T n) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℝ => C * (n ^ 1 * Real.exp (-n))) atTop (𝓝 0) := by
      simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul C
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), pow_one]
    have h1 := hZ n hn
    have h2 : √n ≤ n := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    calc √n * |T n| ≤ √n * (C * Real.exp (-n)) :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ ≤ n * (C * Real.exp (-n)) :=
          mul_le_mul_of_nonneg_right h2 (mul_nonneg hC (Real.exp_pos _).le)
      _ = C * (n * Real.exp (-n)) := by ring
  have hL : Tendsto (fun n : ℝ => (Real.log n)⁻¹) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  have hu' : Tendsto (fun n => 1 + c * (Real.log n)⁻¹ + 4 / √π * (√n * T n) * (Real.log n)⁻¹)
      atTop (𝓝 1) := by
    have := ((hL.const_mul c).const_add 1).add ((hT.const_mul (4 / √π)).mul hL)
    simpa using this
  have hu : Tendsto u atTop (𝓝 1) := by
    refine hu'.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hl : 0 < Real.log n := Real.log_pos hn
    have hs : 0 < √n := Real.sqrt_pos.2 (by linarith)
    simp only [u, T, gaussLogMain, c]
    field_simp
    ring
  have hlog : Tendsto (fun n => Real.log (4 / √π) - Real.log (u n)) atTop
      (𝓝 (Real.log (4 / √π) - Real.log 1)) :=
    tendsto_const_nhds.sub ((Real.continuousAt_log one_ne_zero).tendsto.comp hu)
  rw [Real.log_one, sub_zero] at hlog
  refine hlog.congr' ?_
  filter_upwards [eventually_gt_atTop 1, hu.eventually (lt_mem_nhds one_pos)] with n hn hun
  have hl : 0 < Real.log n := Real.log_pos hn
  have hs : 0 < √n := Real.sqrt_pos.2 (by linarith)
  have hZ' : Z n = u n * (4 / √π)⁻¹ * Real.log n * (√n)⁻¹ := by
    simp only [u]
    field_simp
  have h4 : (0 : ℝ) < (4 / √π)⁻¹ := by positivity
  rw [hZ', Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_inv,
    Real.log_sqrt (by linarith)]
  ring

end Node
