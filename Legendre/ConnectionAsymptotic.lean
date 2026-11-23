module

public import Mathlib

@[expose] public section

/-!
# The logarithmic asymptotic of the period integral at `λ = 1`

We prove (using only Mathlib) that for real `x → 0⁺`
`∫₀¹ dt / (√(t(1-t)) √(1-(1-x)t)) + log x → 4 log 2`.

Route: the substitution `t = 1 - s²` turns the integral into
`2 ∫₀¹ ds / (√(1-s²) √(x + (1-x)s²))`; writing `k = √(1-x)`,
`1/√(1-s²) = k + (1/√(1-s²) - k)`, the first part integrates in closed form
(`log (k s + √(x + k² s²))` is an antiderivative of `k/√(x+k²s²)`) and the second part
converges by dominated convergence to `∫₀¹ (1/√(1-s²) - 1)/s ds = log 2`.
-/

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace Legendre.ConnectionAsymptotic

/-- The (real) period integral. -/
noncomputable def J (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, 1 / (√(t * (1 - t)) * √(1 - (1 - x) * t))

/-- Step 1: the substitution `t = 1 - s²`. -/
theorem J_eq_subst {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    J x = ∫ s in (0 : ℝ)..1, 2 / (√(1 - s ^ 2) * √(x + (1 - x) * s ^ 2)) := by
  have himg : (fun s : ℝ => 1 - s ^ 2) '' Ioo 0 1 = Ioo 0 1 := by
    ext t
    simp only [mem_image, mem_Ioo]
    constructor
    · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
      constructor <;> nlinarith
    · rintro ⟨ht0, ht1⟩
      refine ⟨√(1 - t), ⟨Real.sqrt_pos.2 (by linarith), ?_⟩, ?_⟩
      · rw [Real.sqrt_lt' one_pos]; linarith
      · rw [Real.sq_sqrt (by linarith)]; ring
  have hinj : InjOn (fun s : ℝ => 1 - s ^ 2) (Ioo 0 1) := by
    intro a ha b hb hab
    simp only at hab
    have : a ^ 2 = b ^ 2 := by linarith
    exact (pow_left_inj₀ ha.1.le hb.1.le two_ne_zero).1 this
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => 1 - s ^ 2) (-(2 * s)) (Ioo 0 1) s := by
    intro s _
    have := ((hasDerivAt_pow 2 s).const_sub 1).hasDerivWithinAt (s := Ioo 0 1)
    convert this using 1
    simp
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun t => 1 / (√(t * (1 - t)) * √(1 - (1 - x) * t)))
  rw [himg] at key
  rw [J, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, key,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo ?_
  intro s ⟨hs0, hs1⟩
  simp only [smul_eq_mul]
  have h1 : (1 - s ^ 2) * (1 - (1 - s ^ 2)) = (1 - s ^ 2) * s ^ 2 := by ring
  have h2 : 1 - (1 - x) * (1 - s ^ 2) = x + (1 - x) * s ^ 2 := by ring
  have hw : 0 < 1 - s ^ 2 := by nlinarith
  have hQ : 0 < x + (1 - x) * s ^ 2 := by nlinarith
  rw [h1, h2, Real.sqrt_mul hw.le, Real.sqrt_sq hs0.le, abs_of_neg (by linarith)]
  have := Real.sqrt_pos.2 hw
  have := Real.sqrt_pos.2 hQ
  field_simp


/-- `s ↦ √(1 - s²)` and its derivative. -/
theorem hasDerivAt_sqrt_one_sub_sq {s : ℝ} (hs0 : -1 < s) (hs1 : s < 1) :
    HasDerivAt (fun s : ℝ => √(1 - s ^ 2)) (-s / √(1 - s ^ 2)) s := by
  have hw : 0 < 1 - s ^ 2 := by nlinarith
  have := ((hasDerivAt_pow 2 s).const_sub 1).sqrt hw.ne'
  convert this using 1
  have := Real.sqrt_pos.2 hw
  field_simp
  push_cast
  ring

/-- `1/√(1-s²)` is integrable on `[0,1]` (it is the derivative of `arcsin`). -/
theorem intervalIntegrable_inv_sqrt :
    IntervalIntegrable (fun s : ℝ => 1 / √(1 - s ^ 2)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine integrableOn_deriv_of_nonneg continuous_arcsin.continuousOn ?_ ?_
  · intro s ⟨hs0, hs1⟩
    exact hasDerivAt_arcsin (by linarith) hs1.ne
  · intro s _
    positivity

/-- The closed-form part: `∫₀¹ k/√(x + k² s²) ds = log (k + 1) - log x / 2`, `k = √(1-x)`. -/
theorem integral_main {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∫ s in (0 : ℝ)..1, √(1 - x) / √(x + (1 - x) * s ^ 2) =
      Real.log (√(1 - x) + 1) - Real.log x / 2 := by
  set k := √(1 - x) with hk
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hkk : k ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
  have hQ : ∀ s : ℝ, 0 < x + (1 - x) * s ^ 2 := fun s => by
    have : 0 ≤ (1 - x) * s ^ 2 := mul_nonneg (by linarith) (sq_nonneg s)
    linarith
  have hpos : ∀ s : ℝ, 0 ≤ s → 0 < k * s + √(x + (1 - x) * s ^ 2) := fun s hs =>
    add_pos_of_nonneg_of_pos (mul_nonneg hk0 hs) (Real.sqrt_pos.2 (hQ s))
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => Real.log (k * s + √(x + (1 - x) * s ^ 2)))
        (k / √(x + (1 - x) * s ^ 2)) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have h1 : HasDerivAt (fun s : ℝ => x + (1 - x) * s ^ 2) ((1 - x) * (2 * s)) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (1 - x)).const_add x
      convert this using 1; push_cast; ring
    have h2 := ((hasDerivAt_id' s).const_mul k).fun_add (h1.sqrt (hQ s).ne')
    have h3 := h2.log (hpos s hs.1).ne'
    convert h3 using 1
    have hq := Real.sqrt_pos.2 (hQ s)
    have hqq := Real.sq_sqrt (hQ s).le
    have hp := hpos s hs.1
    field_simp
    rw [← hkk]
    ring
  rw [integral_eq_sub_of_hasDerivAt hderiv]
  · have h1 : x + (1 - x) * (1 : ℝ) ^ 2 = 1 := by ring
    have h0 : x + (1 - x) * (0 : ℝ) ^ 2 = x := by ring
    simp only [mul_one, mul_zero, zero_add, h1, h0, Real.sqrt_one, Real.log_sqrt hx0.le]
  · refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const ?_ fun s _ => (Real.sqrt_pos.2 (hQ s)).ne'
    fun_prop

/-- The integrand of the remainder. -/
noncomputable def rem (x s : ℝ) : ℝ := (1 / √(1 - s ^ 2) - √(1 - x)) / √(x + (1 - x) * s ^ 2)

/-- The remainder integral. -/
noncomputable def R (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, rem x s

theorem intervalIntegrable_rem {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    IntervalIntegrable (rem x) volume 0 1 := by
  have hQ : ∀ s : ℝ, 0 < x + (1 - x) * s ^ 2 := fun s => by
    have : 0 ≤ (1 - x) * s ^ 2 := mul_nonneg (by linarith) (sq_nonneg s)
    linarith
  have : rem x = fun s => (1 / √(1 - s ^ 2) - √(1 - x)) * (√(x + (1 - x) * s ^ 2))⁻¹ := by
    funext s; rw [rem, div_eq_mul_inv]
  rw [this]
  refine (intervalIntegrable_inv_sqrt.sub intervalIntegrable_const).mul_continuousOn ?_
  refine ContinuousOn.inv₀ (by fun_prop) fun s _ => (Real.sqrt_pos.2 (hQ s)).ne'

/-- Step 2: `J x + log x = 2 log (√(1-x) + 1) + 2 R x`. -/
theorem J_add_log {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    J x + Real.log x = 2 * Real.log (√(1 - x) + 1) + 2 * R x := by
  have hQ : ∀ s : ℝ, 0 < x + (1 - x) * s ^ 2 := fun s => by
    have : 0 ≤ (1 - x) * s ^ 2 := mul_nonneg (by linarith) (sq_nonneg s)
    linarith
  have hsplit : (fun s : ℝ => 2 / (√(1 - s ^ 2) * √(x + (1 - x) * s ^ 2))) =
      fun s => 2 * (√(1 - x) / √(x + (1 - x) * s ^ 2)) + 2 * rem x s := by
    funext s; rw [rem]; ring
  have hmain : IntervalIntegrable (fun s : ℝ => √(1 - x) / √(x + (1 - x) * s ^ 2)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const ?_ fun s _ => (Real.sqrt_pos.2 (hQ s)).ne'
    fun_prop
  rw [J_eq_subst hx0 hx1, hsplit, intervalIntegral.integral_add (hmain.const_mul 2)
    ((intervalIntegrable_rem hx0 hx1).const_mul 2), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_main hx0 hx1, R]
  ring


/-- The limit integrand `(1/√(1-s²) - 1)/s = s/(√(1-s²)(1+√(1-s²)))`. -/
noncomputable def lim (s : ℝ) : ℝ := s / (√(1 - s ^ 2) * (1 + √(1 - s ^ 2)))

theorem integral_lim : ∫ s in (0 : ℝ)..1, lim s = Real.log 2 := by
  have hcont : ContinuousOn (fun s : ℝ => -Real.log (1 + √(1 - s ^ 2))) (Icc 0 1) := by
    refine (ContinuousOn.log (by fun_prop) fun s _ => ?_).neg
    have := Real.sqrt_nonneg (1 - s ^ 2)
    linarith
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => -Real.log (1 + √(1 - s ^ 2))) (lim s) s := by
    intro s ⟨hs0, hs1⟩
    have hw : 0 < 1 - s ^ 2 := by nlinarith
    have hq := Real.sqrt_pos.2 hw
    have h := (((hasDerivAt_sqrt_one_sub_sq (by linarith) hs1).const_add 1).log
      (by linarith)).neg
    convert h using 1
    rw [lim]
    field_simp
  have hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 ≤ lim s := fun s ⟨hs0, _⟩ => by
    rw [lim]; positivity
  rw [integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      (integrableOn_deriv_of_nonneg hcont hderiv hpos))]
  norm_num

/-- Step 3 (dominated convergence): `R x → log 2` as `x → 0⁺`. -/
theorem tendsto_R : Tendsto R (𝓝[>] 0) (𝓝 (Real.log 2)) := by
  rw [← integral_lim]
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 1 := by
    rw [ae_iff]; simp
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun s => 1 / √(1 - s ^ 2) + 1) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun x => ?_
    refine Measurable.aestronglyMeasurable ?_
    unfold rem
    fun_prop
  · filter_upwards [hev] with x ⟨hx0, hx1⟩
    filter_upwards [hae] with s hs1' hs
    rw [uIoc_of_le zero_le_one] at hs
    obtain ⟨hs0, hs1⟩ := hs
    have hs1 : s < 1 := lt_of_le_of_ne hs1 hs1'
    have hw : 0 < 1 - s ^ 2 := by nlinarith
    have hQ : 0 < x + (1 - x) * s ^ 2 := by nlinarith
    set w := √(1 - s ^ 2) with hw_def
    set q := √(x + (1 - x) * s ^ 2) with hq_def
    set k := √(1 - x) with hk_def
    have hw0 : 0 < w := Real.sqrt_pos.2 hw
    have hww : w ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hw.le
    have hq0 : 0 < q := Real.sqrt_pos.2 hQ
    have hk0 : 0 ≤ k := Real.sqrt_nonneg _
    have hkk : k ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
    have hw1 : w ≤ 1 := by rw [hw_def, Real.sqrt_le_one]; nlinarith
    have hk1 : k ≤ 1 := by rw [hk_def, Real.sqrt_le_one]; linarith
    -- `s ≤ q` and `√x ≤ q`
    have hsq : s ≤ q := by
      rw [hq_def, Real.le_sqrt hs0.le hQ.le]; nlinarith
    have hxq : √x ≤ q := Real.sqrt_le_sqrt (by nlinarith)
    have hsx : 1 - k ≤ √x := by
      have hr := Real.sq_sqrt hx0.le
      have hr0 := Real.sqrt_nonneg x
      have hr1 : √x ≤ 1 := by rw [Real.sqrt_le_one]; linarith
      nlinarith
    have h1w : 1 - w ≤ s := by nlinarith
    have hiw : 1 ≤ 1 / w := by rw [le_div_iff₀ hw0]; linarith
    have hnum : 0 ≤ 1 / w - k := by linarith
    have hrem0 : 0 ≤ rem x s := by
      rw [rem]; exact div_nonneg hnum hq0.le
    rw [Real.norm_eq_abs, abs_of_nonneg hrem0, rem, div_le_iff₀ hq0]
    have hiw' : 1 / w * w = 1 := by field_simp
    have := mul_le_mul_of_nonneg_left (show 1 - q ≤ w by linarith)
      (show (0 : ℝ) ≤ 1 / w by positivity)
    nlinarith
  · exact intervalIntegrable_inv_sqrt.add intervalIntegrable_const
  · filter_upwards [hae] with s hs1' hs
    rw [uIoc_of_le zero_le_one] at hs
    obtain ⟨hs0, hs1⟩ := hs
    have hs1 : s < 1 := lt_of_le_of_ne hs1 hs1'
    have hw : 0 < 1 - s ^ 2 := by nlinarith
    have hne : √((0 : ℝ) + (1 - 0) * s ^ 2) ≠ 0 := by
      rw [zero_add, sub_zero, one_mul, Real.sqrt_sq hs0.le]; exact hs0.ne'
    have hc : ContinuousAt (fun x : ℝ => rem x s) 0 := by
      unfold rem
      exact ContinuousAt.div (by fun_prop) (by fun_prop) hne
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    convert h using 2
    rw [rem, lim, zero_add, sub_zero, one_mul, Real.sqrt_sq hs0.le, Real.sqrt_one]
    have hw0 := Real.sqrt_pos.2 hw
    have hww : √(1 - s ^ 2) ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hw.le
    field_simp
    nlinarith

/-- The real asymptotic: `J x + log x → 4 log 2` as `x → 0⁺`. -/
theorem tendsto_J_add_log :
    Tendsto (fun x => J x + Real.log x) (𝓝[>] 0) (𝓝 (4 * Real.log 2)) := by
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  have h1 : Tendsto (fun x : ℝ => 2 * Real.log (√(1 - x) + 1)) (𝓝[>] 0)
      (𝓝 (2 * Real.log (√(1 - 0) + 1))) := by
    refine (ContinuousAt.tendsto ?_).mono_left nhdsWithin_le_nhds
    refine ContinuousAt.mul continuousAt_const (ContinuousAt.log (by fun_prop) ?_)
    simp
  have h := h1.add (tendsto_R.const_mul 2)
  rw [sub_zero, Real.sqrt_one, one_add_one_eq_two] at h
  convert h.congr' ?_ using 2
  · ring
  · filter_upwards [hev] with x ⟨hx0, hx1⟩
    exact (J_add_log hx0 hx1).symm


/-- The complex period integrand at `z = 1 - x` is real and equals the integrand of `J x`. -/
theorem period_integral_eq_J {x : ℝ} (hx0 : 0 < x) :
    (∫ t in (0 : ℝ)..1,
      1 / ((Real.sqrt (t * (1 - t)) : ℂ) * (1 - (1 - (x : ℂ)) * t) ^ (1 / 2 : ℂ))) =
      (J x : ℂ) := by
  rw [J, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  obtain ⟨ht0, ht1⟩ := ht
  have hr : 0 ≤ 1 - (1 - x) * t := by nlinarith
  have hc : (1 - (1 - (x : ℂ)) * t) ^ (1 / 2 : ℂ) = ((√(1 - (1 - x) * t) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr]
    push_cast
    rfl
  simp only [hc]
  push_cast
  rfl

/-- **Key asymptotic** (complex form, as needed with `Legendre.period_integral` at
`z = 1 - x`): `∫₀¹ dt/(√(t(1-t)) (1-(1-x)t)^{1/2}) + log x → 4 log 2` as `x → 0⁺`. -/
theorem tendsto_period_integral_add_log :
    Tendsto (fun x : ℝ => (∫ t in (0 : ℝ)..1,
      1 / ((Real.sqrt (t * (1 - t)) : ℂ) * (1 - (1 - (x : ℂ)) * t) ^ (1 / 2 : ℂ))) +
        (Real.log x : ℂ)) (𝓝[>] 0) (𝓝 (4 * (Real.log 2 : ℂ))) := by
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  have h := (Complex.continuous_ofReal.tendsto _).comp tendsto_J_add_log
  push_cast at h
  refine h.congr' ?_
  filter_upwards [hev] with x ⟨hx0, hx1⟩
  simp only [Function.comp, period_integral_eq_J hx0]
  push_cast
  rfl

end Legendre.ConnectionAsymptotic

