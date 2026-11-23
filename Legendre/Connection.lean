module

public import Legendre.Classification
public import Legendre.Period
public import Legendre.ConnectionAsymptotic

@[expose] public section

/-!
# The connection formula `F(1-λ) = (4 log 2 · F(λ) - L(λ)) / π`

Interface theorem (signature fixed): `connection`.

Proof (blueprint §7): `z ↦ F (1 - z)` solves the Picard–Fuchs equation on the lens
`ball 0 1 ∩ ball 1 1 ⊆ D`, so it equals `α F + β L` there (`solution_space_on`).
Along real `x → 0⁺` we have `F x → 1`, `G x → 0`, `(F x - 1) log x → 0`, and, by the period
integral and `ConnectionAsymptotic.tendsto_period_integral_add_log`,
`F (1 - x) + log x / π → 4 log 2 / π`. Comparing forces `β = -1/π` and `α = 4 log 2 / π`.
-/

open Complex Filter Topology Set

namespace Legendre

namespace ConnectionProof

/-- The lens `ball 0 1 ∩ ball 1 1`. -/
def lens : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ Metric.ball 1 1

theorem one_sub_mem_ball {z : ℂ} (hz : z ∈ Metric.ball (1 : ℂ) 1) :
    1 - z ∈ Metric.ball (0 : ℂ) 1 := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  rw [mem_ball_zero_iff, norm_sub_rev]
  exact hz

theorem lens_subset_D : lens ⊆ D := by
  intro z ⟨hz0, hz1⟩
  refine ⟨hz0, ?_⟩
  rw [mem_slitPlane_iff]
  left
  rw [Metric.mem_ball, dist_eq_norm] at hz1
  have := Complex.abs_re_le_norm (z - 1)
  rw [sub_re, one_re] at this
  have := abs_lt.1 (lt_of_le_of_lt this hz1)
  linarith [this.1]

theorem lens_isOpen : IsOpen lens := Metric.isOpen_ball.inter Metric.isOpen_ball

theorem lens_isPreconnected : IsPreconnected lens :=
  ((convex_ball (0 : ℂ) 1).inter (convex_ball (1 : ℂ) 1)).isPreconnected

theorem lens_nonempty : lens.Nonempty := by
  refine ⟨(1 / 2 : ℂ), ?_, ?_⟩
  · rw [mem_ball_zero_iff]; norm_num
  · rw [Metric.mem_ball, dist_eq_norm]; norm_num

theorem ofReal_mem_lens {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : (x : ℂ) ∈ lens := by
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hx1
  · rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith

/-- `z ↦ F (1 - z)` is a solution on the lens. -/
theorem reflect_solves :
    DifferentiableOn ℂ (fun z => F (1 - z)) lens ∧
      ∀ z ∈ lens, legendreOp (fun z => F (1 - z)) z = 0 := by
  refine ⟨?_, ?_⟩
  · refine F_differentiableOn.comp (differentiableOn_id.const_sub 1) ?_
    intro z hz
    exact one_sub_mem_ball hz.2
  · intro z hz
    have h1 : deriv (fun z => F (1 - z)) = fun z => -deriv F (1 - z) :=
      funext fun z => deriv_comp_const_sub _ _ _
    have h2 : deriv (fun z => -deriv F (1 - z)) z = deriv (deriv F) (1 - z) := by
      rw [deriv.fun_neg, deriv_comp_const_sub _ _ _, neg_neg]
    have h := F_solves (one_sub_mem_ball hz.2)
    rw [legendreOp] at h ⊢
    rw [h1, h2]
    linear_combination h

theorem F_zero : F 0 = 1 := ordinaryHypergeometric_zero _ _ _

theorem G_zero : G 0 = 0 := by
  rw [G, tsum_eq_single 0]
  · simp [harm]
  · intro n hn
    simp [zero_pow hn]

theorem tendsto_F : Tendsto (fun x : ℝ => F x) (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt F ((0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_zero]
    exact (F_differentiableOn.differentiableAt (Metric.ball_mem_nhds 0 one_pos)).continuousAt
  have := (hc.comp Complex.continuous_ofReal.continuousAt).tendsto
  simp only [Function.comp_def, Complex.ofReal_zero, F_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem tendsto_G : Tendsto (fun x : ℝ => G x) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt G ((0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_zero]
    exact (G_differentiableOn.differentiableAt (Metric.ball_mem_nhds 0 one_pos)).continuousAt
  have := (hc.comp Complex.continuous_ofReal.continuousAt).tendsto
  simp only [Function.comp_def, Complex.ofReal_zero, G_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem tendsto_F_sub_one_mul_log :
    Tendsto (fun x : ℝ => (F x - 1) * (Real.log x : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have hd : HasDerivAt F (deriv F 0) ((0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_zero]
    exact (F_differentiableOn.differentiableAt (Metric.ball_mem_nhds 0 one_pos)).hasDerivAt
  have hs := hasDerivAt_iff_tendsto_slope.1 hd.comp_ofReal
  have hs' := hs.mono_left (nhdsWithin_mono _ (fun x (hx : (0 : ℝ) < x) => ne_of_gt hx))
  have hxl : Tendsto (fun x : ℝ => ((x * Real.log x : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := ((Complex.continuous_ofReal.comp Real.continuous_mul_log).tendsto 0)
    simp only [Function.comp_def, zero_mul, Complex.ofReal_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h := hs'.mul hxl
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  rw [slope_def_module, Complex.ofReal_zero, F_zero, sub_zero, Complex.real_smul]
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  push_cast
  field_simp

end ConnectionProof

open ConnectionProof in
theorem connection {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1 ∩ Metric.ball 1 1) :
    F (1 - z) = (4 * Real.log 2 * F z - L z) / Real.pi := by
  obtain ⟨α, β, hab⟩ := (solution_space_on lens_isOpen lens_isPreconnected lens_subset_D
    lens_nonempty _).1 reflect_solves
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  -- the key asymptotic, transported through the period integral
  have hK : Tendsto (fun x : ℝ => F (1 - x) + (Real.log x : ℂ) / Real.pi) (𝓝[>] 0)
      (𝓝 (4 * (Real.log 2 : ℂ) / Real.pi)) := by
    have h := ConnectionAsymptotic.tendsto_period_integral_add_log.const_mul
      (1 / (Real.pi : ℂ))
    rw [show 1 / (Real.pi : ℂ) * (4 * (Real.log 2 : ℂ)) = 4 * (Real.log 2 : ℂ) / Real.pi by
      ring] at h
    refine h.congr' ?_
    filter_upwards [hev] with x ⟨hx0, hx1⟩
    have hn : ‖(1 : ℂ) - x‖ < 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_lt]
      constructor <;> linarith
    rw [period_integral hn]
    ring
  -- the right-hand side
  have hE : Tendsto (fun x : ℝ => (F (1 - x) + (Real.log x : ℂ) / Real.pi) - α * F x -
      β * ((F x - 1) * (Real.log x : ℂ)) - β * G x) (𝓝[>] 0)
      (𝓝 (4 * (Real.log 2 : ℂ) / Real.pi - α * 1 - β * 0 - β * 0)) :=
    ((hK.sub (tendsto_F.const_mul α)).sub (tendsto_F_sub_one_mul_log.const_mul β)).sub
      (tendsto_G.const_mul β)
  simp only [mul_one, mul_zero, sub_zero] at hE
  have hid : ∀ᶠ x in 𝓝[>] (0 : ℝ), (β + 1 / Real.pi) * (Real.log x : ℂ) =
      (F (1 - x) + (Real.log x : ℂ) / Real.pi) - α * F x -
        β * ((F x - 1) * (Real.log x : ℂ)) - β * G x := by
    filter_upwards [hev] with x ⟨hx0, hx1⟩
    rw [hab x (ofReal_mem_lens hx0 hx1), L, ← Complex.ofReal_log hx0.le]
    ring
  have hβ : β = -(1 / Real.pi) := by
    by_contra hne
    have hc : β + 1 / Real.pi ≠ 0 := fun h => hne (eq_neg_of_add_eq_zero_left h)
    have h1 := (hE.congr' (hid.mono fun x hx => hx.symm)).const_mul (β + 1 / Real.pi)⁻¹
    have h2 := (Complex.continuous_re.tendsto _).comp h1
    refine not_tendsto_nhds_of_tendsto_atBot Real.tendsto_log_nhdsGT_zero _ (h2.congr' ?_)
    refine Eventually.of_forall fun x => ?_
    simp only [Function.comp_apply]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul, Complex.ofReal_re]
  have hα : α = 4 * (Real.log 2 : ℂ) / Real.pi := by
    have h0 : Tendsto (fun x : ℝ => (F (1 - x) + (Real.log x : ℂ) / Real.pi) - α * F x -
        β * ((F x - 1) * (Real.log x : ℂ)) - β * G x) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr' (hid.mono fun x hx => ?_)
      beta_reduce
      rw [← hx, hβ, neg_add_cancel, zero_mul]
    have := tendsto_nhds_unique hE h0
    linear_combination -this
  rw [hab z hz, hα, hβ, L]
  field_simp
  ring

end Legendre
