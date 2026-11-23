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

end Legendre.ConnectionAsymptotic
