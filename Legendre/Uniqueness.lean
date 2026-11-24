module

public import Legendre.Defs

@[expose] public section

/-!
# Uniqueness for the Picard–Fuchs equation on a connected open set

Interface theorems (signatures fixed; other files depend on them):
`D_isOpen`, `D_isPreconnected`, `eqOn_zero_of_legendreOp`.

Proof of uniqueness: differentiating the equation `k` times gives
`z(1-z) y^{(k+2)} + (k+1)(1-2z) y^{(k+1)} - (k+1/2)² y^{(k)} = 0` on `U`; at an ordinary
point `z₀` with vanishing Cauchy data all derivatives vanish, so the Taylor series shows
`y = 0` near `z₀`, and the identity theorem gives `y = 0` on `U`.
-/

open Complex Filter Topology

namespace Legendre

theorem D_isOpen : IsOpen D := Metric.isOpen_ball.inter isOpen_slitPlane

theorem D_isPreconnected : IsPreconnected D := by
  have h12 : (0 : ℝ) < 1 / 2 := by norm_num
  have hmem : (((1 / 2 : ℝ)) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos h12]
    norm_num
  have hslit : (((1 / 2 : ℝ)) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 h12
  have hs : StarConvex ℝ (((1 / 2 : ℝ)) : ℂ) D :=
    ((convex_ball (0 : ℂ) 1).starConvex hmem).inter (starConvex_ofReal_slitPlane h12)
  exact (hs.isPathConnected ⟨hmem, hslit⟩).isConnected.isPreconnected

/-- Iterated derivatives of a holomorphic function on an open set are holomorphic. -/
theorem differentiableOn_iterate_deriv {U : Set ℂ} (hU : IsOpen U) {y : ℂ → ℂ}
    (hy : DifferentiableOn ℂ y U) : ∀ k : ℕ, DifferentiableOn ℂ (deriv^[k] y) U
  | 0 => hy
  | k + 1 => by
    rw [Function.iterate_succ']
    exact (differentiableOn_iterate_deriv hU hy k).deriv hU

/-- The `k`-th derivative of the Picard–Fuchs equation. -/
theorem legendreOp_iterate_deriv {U : Set ℂ} (hU : IsOpen U) {y : ℂ → ℂ}
    (hy : DifferentiableOn ℂ y U) (hode : ∀ z ∈ U, legendreOp y z = 0) (k : ℕ) :
    ∀ z ∈ U, z * (1 - z) * deriv^[k + 2] y z + ((k : ℂ) + 1) * (1 - 2 * z) * deriv^[k + 1] y z
      - ((k : ℂ) + 1 / 2) ^ 2 * deriv^[k] y z = 0 := by
  induction k with
  | zero =>
    intro z hz
    have := hode z hz
    simp only [legendreOp] at this
    simp only [Nat.cast_zero, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
      id_eq]
    linear_combination this
  | succ k ih =>
    intro z hz
    set g : ℂ → ℂ := fun w => w * (1 - w) * deriv^[k + 2] y w
      + ((k : ℂ) + 1) * (1 - 2 * w) * deriv^[k + 1] y w
      - ((k : ℂ) + 1 / 2) ^ 2 * deriv^[k] y w with hg_def
    have hg : g =ᶠ[𝓝 z] fun _ => 0 :=
      Filter.eventually_of_mem (hU.mem_nhds hz) (fun w hw => ih w hw)
    have hd0 : deriv g z = 0 := by rw [hg.deriv_eq]; simp
    have hdk : ∀ j : ℕ, HasDerivAt (deriv^[j] y) (deriv^[j + 1] y z) z := fun j => by
      have := ((differentiableOn_iterate_deriv hU hy j) z hz).differentiableAt (hU.mem_nhds hz)
      rw [Function.iterate_succ_apply']
      exact this.hasDerivAt
    have h1 : HasDerivAt (fun w : ℂ => w * (1 - w)) (1 - 2 * z) z := by
      have := (hasDerivAt_id' z).mul ((hasDerivAt_id' z).const_sub (1 : ℂ))
      convert this using 1
      ring
    have h2 : HasDerivAt (fun w : ℂ => ((k : ℂ) + 1) * (1 - 2 * w)) (-2 * ((k : ℂ) + 1)) z := by
      have := (((hasDerivAt_id' z).const_mul (2 : ℂ)).const_sub (1 : ℂ)).const_mul
        ((k : ℂ) + 1)
      convert this using 1
      ring
    have hG := ((h1.mul (hdk (k + 2))).add (h2.mul (hdk (k + 1)))).sub
      ((hdk k).const_mul (((k : ℂ) + 1 / 2) ^ 2))
    have hd1 := hG.deriv
    change deriv g z = _ at hd1
    rw [hd0] at hd1
    have e1 : k + 1 + 2 = k + 2 + 1 := rfl
    rw [e1]
    push_cast
    linear_combination -hd1

/-- If the Cauchy data vanish at an ordinary point, all derivatives vanish there. -/
theorem iterate_deriv_eq_zero {U : Set ℂ} (hU : IsOpen U) {y : ℂ → ℂ}
    (hy : DifferentiableOn ℂ y U) (hode : ∀ z ∈ U, legendreOp y z = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hz₀0 : z₀ ≠ 0) (hz₀1 : z₀ ≠ 1)
    (h0 : y z₀ = 0) (h1 : deriv y z₀ = 0) : ∀ k : ℕ, deriv^[k] y z₀ = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simpa using h0
    | 1, _ => simpa using h1
    | k + 2, ih =>
      have h := legendreOp_iterate_deriv hU hy hode k z₀ hz₀
      rw [ih (k + 1) (by omega), ih k (by omega)] at h
      have hne : z₀ * (1 - z₀) ≠ 0 := mul_ne_zero hz₀0 (sub_ne_zero.mpr (Ne.symm hz₀1))
      have : z₀ * (1 - z₀) * deriv^[k + 2] y z₀ = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_left hne

/-- A holomorphic solution on a connected open set with vanishing Cauchy data at an
ordinary point `z₀ ∉ {0, 1}` vanishes identically. -/
theorem eqOn_zero_of_legendreOp {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {y : ℂ → ℂ} (hy : DifferentiableOn ℂ y U) (hode : ∀ z ∈ U, legendreOp y z = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hz₀0 : z₀ ≠ 0) (hz₀1 : z₀ ≠ 1)
    (h0 : y z₀ = 0) (h1 : deriv y z₀ = 0) : ∀ z ∈ U, y z = 0 := by
  have hk := iterate_deriv_eq_zero hU hy hode hz₀ hz₀0 hz₀1 h0 h1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  have hloc : y =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hz
    rw [← Complex.taylorSeries_eq_on_ball' hz (hy.mono hball)]
    simp [iteratedDeriv_eq_iterate, hk]
  intro z hz
  exact (hy.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz₀ hloc hz

end Legendre
