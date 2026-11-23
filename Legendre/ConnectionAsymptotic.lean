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

end Legendre.ConnectionAsymptotic
