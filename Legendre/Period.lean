module

public import Legendre.Defs

@[expose] public section

/-!
# The period integral

Interface theorem (signature fixed): `period_integral`.

For `‖z‖ < 1`, `F z = (1/π) ∫₀¹ dx / (√(x(1-x)) (1 - z x)^{1/2})`.

Route: expand `1/(1 - z x)^{1/2}` with the binomial series
(`one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`, coefficient `C(2n,n)/4ⁿ`), integrate term
by term (dominated by `‖z‖ⁿ / √(x(1-x))`), and evaluate the moments as Beta integrals
`B(n + 1/2, 1/2) = π C(2n,n)/4ⁿ`.

Exposed auxiliary results:
* `F_eq_tsum_period` : `F z = ∑' n, coeff n * z ^ n`;
* `intervalIntegrable_period_integrand` : integrability of the integrand on `[0,1]`;
* `hasSum_period_integrand`, `betaIntegral_nat_add_half`, `halfCoeff` and friends.
-/

open Complex MeasureTheory Set Filter
open scoped Nat Real

namespace Legendre

/-- `halfCoeff n = C(2n, n) / 4ⁿ = (1/2)ₙ / n!`, so that `coeff n = halfCoeff n ^ 2`. -/
noncomputable def halfCoeff (n : ℕ) : ℂ := (Nat.centralBinom n : ℂ) / 4 ^ n

lemma coeff_eq_halfCoeff_sq (n : ℕ) : coeff n = halfCoeff n ^ 2 := rfl

lemma halfCoeff_zero : halfCoeff 0 = 1 := by simp [halfCoeff]

lemma halfCoeff_succ (n : ℕ) :
    halfCoeff (n + 1) = halfCoeff n * (((n : ℂ) + 1 / 2) / ((n : ℂ) + 1)) := by
  have h : ((n : ℂ) + 1) * (Nat.centralBinom (n + 1) : ℂ) =
      2 * (2 * n + 1) * Nat.centralBinom n := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  unfold halfCoeff
  rw [pow_succ]
  field_simp
  linear_combination 2 * h

lemma norm_halfCoeff_le_one (n : ℕ) : ‖halfCoeff n‖ ≤ 1 := by
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have : halfCoeff n = (((Nat.centralBinom n : ℝ) / 4 ^ n : ℝ) : ℂ) := by
    simp [halfCoeff]
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    div_le_one h4]
  exact_mod_cast Nat.centralBinom_le_four_pow n

lemma ascPochhammer_half_div_factorial (n : ℕ) :
    (ascPochhammer ℂ n).eval (1 / 2 : ℂ) / (n ! : ℂ) = halfCoeff n := by
  induction n with
  | zero => simp [halfCoeff_zero]
  | succ n ih =>
    rw [halfCoeff_succ, ← ih, ascPochhammer_succ_eval, Nat.factorial_succ]
    have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    push_cast
    field_simp
    ring

lemma choose_half_eq_halfCoeff (n : ℕ) :
    Ring.choose ((1 / 2 : ℂ) + n - 1) n = halfCoeff n := by
  rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval, ← ascPochhammer_half_div_factorial, smul_eq_mul,
    show (1 / 2 : ℂ) + n - 1 - n + 1 = 1 / 2 by ring]
  ring

lemma ordinaryHypergeometricCoefficient_half (n : ℕ) :
    ordinaryHypergeometricCoefficient (1 / 2 : ℂ) (1 / 2) 1 n = coeff n := by
  rw [coeff_eq_halfCoeff_sq, ← ascPochhammer_half_div_factorial]
  unfold ordinaryHypergeometricCoefficient
  rw [ascPochhammer_eval_one]
  have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- The Taylor series of `F` (all `z`; `F` is defined as the `tsum`). -/
theorem F_eq_tsum_period {z : ℂ} (_hz : ‖z‖ < 1) : F z = ∑' n, coeff n * z ^ n := by
  unfold F
  rw [ordinaryHypergeometric_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [smul_eq_mul, ← ordinaryHypergeometricCoefficient_half]

lemma Gamma_nat_add_half (n : ℕ) :
    Gamma ((n : ℂ) + 1 / 2) = (ascPochhammer ℂ n).eval (1 / 2 : ℂ) * Gamma (1 / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : (n : ℂ) + 1 / 2 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    rw [ascPochhammer_succ_eval, show ((n + 1 : ℕ) : ℂ) + 1 / 2 = ((n : ℂ) + 1 / 2) + 1 by
      push_cast; ring, Gamma_add_one _ hne, ih]
    ring

lemma Gamma_one_half_sq : Gamma (1 / 2) ^ 2 = (π : ℂ) := by
  have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.Gamma_ofReal, Real.Gamma_one_half_eq, ← ofReal_pow,
    Real.sq_sqrt Real.pi_pos.le]

lemma betaIntegral_nat_add_half (n : ℕ) :
    betaIntegral ((n : ℂ) + 1 / 2) (1 / 2) = (π : ℂ) * halfCoeff n := by
  have h1 : 0 < ((n : ℂ) + 1 / 2).re := by simp; positivity
  have h2 : 0 < (1 / 2 : ℂ).re := by simp
  have key := Gamma_mul_Gamma_eq_betaIntegral h1 h2
  rw [show (n : ℂ) + 1 / 2 + 1 / 2 = (n : ℂ) + 1 by ring, Gamma_nat_eq_factorial,
    Gamma_nat_add_half] at key
  have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [← ascPochhammer_half_div_factorial, ← Gamma_one_half_sq, mul_div_assoc', eq_div_iff hf]
  linear_combination -key

/-! ### The integrand -/

/-- The real weight `1 / √(x (1 - x))`. -/
noncomputable def weight (x : ℝ) : ℝ := 1 / Real.sqrt (x * (1 - x))

lemma weight_nonneg (x : ℝ) : 0 ≤ weight x := by
  unfold weight; positivity

/-- The Beta integrand at `(n + 1/2, 1/2)` is `xⁿ / √(x(1-x))` on `(0,1)`. -/
lemma beta_integrand_eq (n : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (x : ℂ) ^ ((n : ℂ) + 1 / 2 - 1) * (1 - (x : ℂ)) ^ ((1 / 2 : ℂ) - 1) =
      (x : ℂ) ^ n * (weight x : ℂ) := by
  have e1 : (n : ℂ) + 1 / 2 - 1 = (n : ℂ) + ((-1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 / 2 : ℂ) - 1 = ((-1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have e3 : (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, cpow_add _ _ (by exact_mod_cast hx0.ne'), cpow_natCast, ← ofReal_cpow hx0.le, e3,
    ← ofReal_cpow (by linarith), mul_assoc, ← ofReal_mul]
  congr 2
  rw [weight, Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg (by nlinarith),
    Real.mul_rpow hx0.le (by linarith)]
  norm_num

lemma intervalIntegrable_weight : IntervalIntegrable weight volume 0 1 := by
  have h := (betaIntegral_convergent (u := (0 : ℕ) + 1 / 2) (v := 1 / 2) (by simp)
    (by simp)).norm
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h ⊢
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioo
  dsimp only
  rw [beta_integrand_eq 0 hx.1 hx.2, pow_zero, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (weight_nonneg x)]

/-- Pointwise binomial expansion of the period integrand on `(0,1)`. -/
lemma hasSum_period_integrand {z : ℂ} (hz : ‖z‖ < 1) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => halfCoeff n * z ^ n *
        ((x : ℂ) ^ ((n : ℂ) + 1 / 2 - 1) * (1 - (x : ℂ)) ^ ((1 / 2 : ℂ) - 1)))
      (1 / ((Real.sqrt (x * (1 - x)) : ℂ) * (1 - z * x) ^ (1 / 2 : ℂ))) := by
  have hp := one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℂ)
  have hmem : z * (x : ℂ) ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal, mem_ball_zero_iff, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    nlinarith [norm_nonneg z]
  have hs := (hp.hasSum hmem).mul_left (weight x : ℂ)
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, zero_add, smul_eq_mul] at hs
  convert hs using 1
  · funext n
    rw [beta_integrand_eq n hx0 hx1, choose_half_eq_halfCoeff]
    ring
  · rw [weight]
    push_cast
    rw [one_div_mul_one_div]

lemma norm_period_term_le {z : ℂ} (n : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ‖halfCoeff n * z ^ n *
        ((x : ℂ) ^ ((n : ℂ) + 1 / 2 - 1) * (1 - (x : ℂ)) ^ ((1 / 2 : ℂ) - 1))‖ ≤
      ‖z‖ ^ n * weight x := by
  rw [beta_integrand_eq n hx0 hx1, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0,
    abs_of_nonneg (weight_nonneg x)]
  have h1 := norm_halfCoeff_le_one n
  have h2 : x ^ n ≤ 1 := pow_le_one₀ hx0.le hx1.le
  have h3 := weight_nonneg x
  have h4 : 0 ≤ ‖z‖ ^ n := by positivity
  have h5 : 0 ≤ x ^ n := by positivity
  calc ‖halfCoeff n‖ * ‖z‖ ^ n * (x ^ n * weight x)
      ≤ 1 * ‖z‖ ^ n * (1 * weight x) := by gcongr
    _ = ‖z‖ ^ n * weight x := by ring

lemma ae_mem_Ioo : ∀ᵐ x : ℝ ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 → x ∈ Ioo (0 : ℝ) 1 := by
  have h : ∀ᵐ x : ℝ ∂volume, x ∉ ({1} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := (volume : Measure ℝ)) (1 : ℝ))
  filter_upwards [h] with x hx hmem
  rw [uIoc_of_le zero_le_one] at hmem
  exact ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩

lemma measurable_period_integrand (z : ℂ) :
    Measurable (fun x : ℝ => 1 / ((Real.sqrt (x * (1 - x)) : ℂ) * (1 - z * x) ^ (1 / 2 : ℂ))) := by
  fun_prop

/-- The period integrand is integrable on `[0,1]` for `‖z‖ < 1`. -/
theorem intervalIntegrable_period_integrand {z : ℂ} (hz : ‖z‖ < 1) :
    IntervalIntegrable
      (fun x : ℝ => 1 / ((Real.sqrt (x * (1 - x)) : ℂ) * (1 - z * x) ^ (1 / 2 : ℂ)))
      volume 0 1 := by
  have hg := (intervalIntegrable_weight.const_mul (1 - ‖z‖)⁻¹)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hg ⊢
  refine Integrable.mono' hg (measurable_period_integrand z).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
  have hgeo : HasSum (fun n : ℕ => ‖z‖ ^ n * weight x) ((1 - ‖z‖)⁻¹ * weight x) :=
    (hasSum_geometric_of_lt_one (norm_nonneg z) hz).mul_right _
  exact (hasSum_period_integrand hz hx.1 hx.2).norm_le_of_bounded hgeo
    (fun n => norm_period_term_le n hx.1 hx.2)

/-- Term-by-term integration of the binomial expansion. -/
lemma hasSum_period_integral {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => halfCoeff n * z ^ n * betaIntegral ((n : ℂ) + 1 / 2) (1 / 2))
      (∫ x in (0 : ℝ)..1,
        1 / ((Real.sqrt (x * (1 - x)) : ℂ) * (1 - z * x) ^ (1 / 2 : ℂ))) := by
  simp only [betaIntegral, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n x => ‖z‖ ^ n * weight x) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [ae_mem_Ioo] with x hx hmem
    exact norm_period_term_le n (hx hmem).1 (hx hmem).2
  · exact Eventually.of_forall fun x _ =>
      (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right _
  · have : (fun x => ∑' n : ℕ, ‖z‖ ^ n * weight x) = fun x => (1 - ‖z‖)⁻¹ * weight x := by
      funext x
      rw [tsum_mul_right, tsum_geometric_of_lt_one (norm_nonneg z) hz]
    rw [this]
    exact intervalIntegrable_weight.const_mul _
  · filter_upwards [ae_mem_Ioo] with x hx hmem
    exact hasSum_period_integrand hz (hx hmem).1 (hx hmem).2

theorem period_integral {z : ℂ} (hz : ‖z‖ < 1) :
    F z = (1 / (Real.pi : ℂ)) * ∫ x in (0 : ℝ)..1,
      1 / ((Real.sqrt (x * (1 - x)) : ℂ) * (1 - z * x) ^ (1 / 2 : ℂ)) := by
  have h := hasSum_period_integral hz
  simp only [betaIntegral_nat_add_half] at h
  have h' : HasSum (fun n : ℕ => (π : ℂ) * (coeff n * z ^ n))
      (∫ x in (0 : ℝ)..1,
        1 / ((Real.sqrt (x * (1 - x)) : ℂ) * (1 - z * x) ^ (1 / 2 : ℂ))) := by
    convert h using 2 with n
    rw [coeff_eq_halfCoeff_sq]
    ring
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [← h'.tsum_eq, tsum_mul_left, ← F_eq_tsum_period hz]
  field_simp

end Legendre
