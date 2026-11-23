module

public import Legendre.Defs
public import Legendre.PowerSeries

@[expose] public section

/-!
# `F`, `G` and `L` solve the Picard–Fuchs equation; the Wronskian

Interface theorems (signatures fixed; other files depend on them):
`F_eq_tsum`, `F_differentiableOn`, `G_differentiableOn`, `F_solves`,
`L_differentiableOn`, `L_solves`, `wronskian`.

The proofs go through the power series toolkit of `Legendre.PowerSeries`:
`F = S coeff` on the unit disc and `G = S (coeff * harm)`. The coefficient
recursions `(n+1)² aₙ₊₁ = (n+1/2)² aₙ` and `hₙ₊₁ = hₙ + 2/((n+1)(2n+1))` give
the ODE for `F` and the inhomogeneous ODE
`z(1-z)G'' + (1-2z)G' - G/4 = F - 2(1-z)F'`, from which the ODE for `L` and the
Wronskian identity (via the conserved quantity `(1-z)F² + z(1-z)(F G' - F' G)`) follow.
-/

open Complex Filter Topology

namespace Legendre

open PS

/-! ### Coefficients -/

lemma coeff_zero : coeff 0 = 1 := by simp [coeff]

lemma coeff_rec (n : ℕ) :
    ((n : ℂ) + 1) ^ 2 * coeff (n + 1) = ((n : ℂ) + 1 / 2) ^ 2 * coeff n := by
  unfold coeff
  have hc : ((n : ℂ) + 1) * (Nat.centralBinom (n + 1) : ℂ) =
      2 * (2 * n + 1) * (Nat.centralBinom n : ℂ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  rw [div_pow, div_pow, ← mul_div_assoc, ← mul_pow, hc]
  field_simp
  ring

lemma norm_coeff_le (n : ℕ) : ‖coeff n‖ ≤ 1 := by
  have : coeff n = (((Nat.centralBinom n : ℕ) : ℂ) / ((4 ^ n : ℕ) : ℂ)) ^ 2 := by
    simp [coeff]
  rw [this, norm_pow, norm_div, RCLike.norm_natCast, RCLike.norm_natCast]
  apply pow_le_one₀ (by positivity)
  apply div_le_one_of_le₀ _ (by positivity)
  exact_mod_cast Nat.centralBinom_le_four_pow n

lemma harm_succ (n : ℕ) :
    harm (n + 1) = harm n + 2 / (((n : ℂ) + 1) * (2 * n + 1)) := by
  simp [harm, Finset.sum_range_succ]

lemma norm_harm_term_le (k : ℕ) : ‖(2 : ℂ) / (((k : ℂ) + 1) * (2 * k + 1))‖ ≤ 2 := by
  have : (2 : ℂ) / (((k : ℂ) + 1) * (2 * k + 1)) =
      (((2 : ℝ) / (((k : ℝ) + 1) * (2 * k + 1)) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  apply div_le_self (by norm_num)
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

lemma norm_harm_le (n : ℕ) : ‖harm n‖ ≤ 2 * ((n : ℝ) + 1) := by
  unfold harm
  calc ‖∑ k ∈ Finset.range n, (2 : ℂ) / (((k : ℂ) + 1) * (2 * k + 1))‖
      ≤ ∑ k ∈ Finset.range n, ‖(2 : ℂ) / (((k : ℂ) + 1) * (2 * k + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, (2 : ℝ) := Finset.sum_le_sum fun k _ => norm_harm_term_le k
    _ = 2 * n := by simp; ring
    _ ≤ 2 * ((n : ℝ) + 1) := by linarith

lemma coeff_polyBdd : PolyBdd coeff := PolyBdd.of_bound norm_coeff_le

lemma harm_polyBdd : PolyBdd harm := ⟨2, 1, fun n => by simpa using norm_harm_le n⟩

/-- The coefficients of `G`. -/
noncomputable def gcoeff (n : ℕ) : ℂ := coeff n * harm n

lemma gcoeff_polyBdd : PolyBdd gcoeff := coeff_polyBdd.mul harm_polyBdd

lemma G_eq_S : G = S gcoeff := rfl

lemma gcoeff_rec (n : ℕ) :
    ((n : ℂ) + 1) ^ 2 * gcoeff (n + 1) - ((n : ℂ) + 1 / 2) ^ 2 * gcoeff n =
      (2 * (n : ℂ) + 1) * coeff n - 2 * ((n : ℂ) + 1) * coeff (n + 1) := by
  unfold gcoeff
  rw [harm_succ]
  have hr := coeff_rec n
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hn2 : 2 * (n : ℂ) + 1 ≠ 0 := by
    have : (2 * (n : ℂ) + 1) = ((2 * n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact Nat.cast_ne_zero.mpr (by omega)
  have ha1 : coeff (n + 1) = ((n : ℂ) + 1 / 2) ^ 2 * coeff n / ((n : ℂ) + 1) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hn1)]
    linear_combination hr
  have hn2' : (n : ℂ) * 2 + 1 ≠ 0 := by rw [mul_comm]; exact hn2
  rw [ha1]
  field_simp
  ring

/-! ### `F` as a power series -/

lemma ascPochhammer_eval_half (n : ℕ) :
    (ascPochhammer ℂ n).eval (1 / 2 : ℂ) =
      (n.factorial : ℂ) * ((Nat.centralBinom n : ℂ) / 4 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih, Nat.factorial_succ]
    have hc : ((n : ℂ) + 1) * (Nat.centralBinom (n + 1) : ℂ) =
        2 * (2 * n + 1) * (Nat.centralBinom n : ℂ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    push_cast
    linear_combination (-(n.factorial : ℂ) / 4 ^ (n + 1)) * hc

lemma hyper_coeff (n : ℕ) :
    ((n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval (1 / 2 : ℂ) *
      (ascPochhammer ℂ n).eval (1 / 2 : ℂ) * ((ascPochhammer ℂ n).eval 1)⁻¹) = coeff n := by
  rw [ascPochhammer_eval_half, ascPochhammer_eval_one]
  have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  unfold coeff
  field_simp

theorem F_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) : F z = ∑' n : ℕ, coeff n * z ^ n := by
  have _ := hz
  rw [F, ordinaryHypergeometric_eq_tsum]
  dsimp only
  refine tsum_congr fun n => ?_
  rw [smul_eq_mul, hyper_coeff]

lemma F_eq_S {z : ℂ} (hz : ‖z‖ < 1) : F z = S coeff z := F_eq_tsum hz

lemma F_eventuallyEq {z : ℂ} (hz : ‖z‖ < 1) : F =ᶠ[𝓝 z] S coeff := by
  have hmem : Metric.ball (0 : ℂ) 1 ∈ 𝓝 z :=
    Metric.isOpen_ball.mem_nhds (by simpa using hz)
  filter_upwards [hmem] with w hw
  exact F_eq_S (by simpa using hw)

lemma deriv_F {z : ℂ} (hz : ‖z‖ < 1) : deriv F z = S (dc coeff) z := by
  rw [(F_eventuallyEq hz).deriv_eq, deriv_S coeff_polyBdd hz]

theorem F_differentiableOn : DifferentiableOn ℂ F (Metric.ball 0 1) :=
  (differentiableOn_S coeff_polyBdd).congr fun _ hw => F_eq_S (by simpa using hw)

theorem G_differentiableOn : DifferentiableOn ℂ G (Metric.ball 0 1) :=
  differentiableOn_S gcoeff_polyBdd

/-! ### The ODEs in power series form -/

lemma ode_A {z : ℂ} (hz : ‖z‖ < 1) :
    z * (1 - z) * S (dc (dc coeff)) z + (1 - 2 * z) * S (dc coeff) z - S coeff z / 4 = 0 := by
  rw [ode_S coeff_polyBdd hz]
  have : (fun n : ℕ => ((n : ℂ) + 1) ^ 2 * coeff (n + 1) - ((n : ℂ) + 1 / 2) ^ 2 * coeff n) =
      fun _ => 0 := by
    funext n; rw [coeff_rec]; ring
  rw [this]
  simp [S]

lemma ode_B {z : ℂ} (hz : ‖z‖ < 1) :
    z * (1 - z) * S (dc (dc gcoeff)) z + (1 - 2 * z) * S (dc gcoeff) z - S gcoeff z / 4 =
      S coeff z - 2 * (1 - z) * S (dc coeff) z := by
  rw [ode_S gcoeff_polyBdd hz, S_sub_S_dc coeff_polyBdd hz]
  congr 1
  funext n
  exact gcoeff_rec n

theorem F_solves {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) : legendreOp F z = 0 := by
  have hz' : ‖z‖ < 1 := by simpa using hz
  rw [legendreOp_congr (F_eventuallyEq hz'), legendreOp_S coeff_polyBdd hz']
  have : (fun n : ℕ => ((n : ℂ) + 1) ^ 2 * coeff (n + 1) - ((n : ℂ) + 1 / 2) ^ 2 * coeff n) =
      fun _ => 0 := by
    funext n; rw [coeff_rec]; ring
  rw [this]
  simp [S]

/-! ### The logarithmic solution -/

lemma isOpen_D : IsOpen D := Metric.isOpen_ball.inter isOpen_slitPlane

lemma norm_lt_one_of_mem_D {z : ℂ} (hz : z ∈ D) : ‖z‖ < 1 := by
  simpa using hz.1

lemma ne_zero_of_mem_D {z : ℂ} (hz : z ∈ D) : z ≠ 0 := slitPlane_ne_zero hz.2

lemma one_sub_ne_zero_of_mem_D {z : ℂ} (hz : z ∈ D) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := by linear_combination -h
  have h1 := norm_lt_one_of_mem_D hz
  rw [this, norm_one] at h1
  exact lt_irrefl _ h1

/-- `L` on `D`, written with power series. -/
noncomputable def ell (w : ℂ) : ℂ := S coeff w * Complex.log w + S gcoeff w

/-- The derivative of `ell`. -/
noncomputable def ell1 (w : ℂ) : ℂ :=
  S (dc coeff) w * Complex.log w + S coeff w * w⁻¹ + S (dc gcoeff) w

lemma L_eventuallyEq {z : ℂ} (hz : z ∈ D) : L =ᶠ[𝓝 z] ell := by
  filter_upwards [isOpen_D.mem_nhds hz] with w hw
  simp only [L, ell, F_eq_S (norm_lt_one_of_mem_D hw), G_eq_S]

lemma hasDerivAt_ell {z : ℂ} (hz : z ∈ D) : HasDerivAt ell (ell1 z) z := by
  have hz' := norm_lt_one_of_mem_D hz
  exact ((hasDerivAt_S coeff_polyBdd hz').mul (Complex.hasDerivAt_log hz.2)).add
    (hasDerivAt_S gcoeff_polyBdd hz')

lemma deriv_ell_eventuallyEq {z : ℂ} (hz : z ∈ D) : deriv ell =ᶠ[𝓝 z] ell1 := by
  filter_upwards [isOpen_D.mem_nhds hz] with w hw
  exact (hasDerivAt_ell hw).deriv

lemma hasDerivAt_ell1 {z : ℂ} (hz : z ∈ D) :
    HasDerivAt ell1 (S (dc (dc coeff)) z * Complex.log z + S (dc coeff) z * z⁻¹ +
      (S (dc coeff) z * z⁻¹ + S coeff z * (-(z ^ 2)⁻¹)) + S (dc (dc gcoeff)) z) z := by
  have hz' := norm_lt_one_of_mem_D hz
  exact (((hasDerivAt_S coeff_polyBdd.dc hz').mul (Complex.hasDerivAt_log hz.2)).add
    ((hasDerivAt_S coeff_polyBdd hz').mul (hasDerivAt_inv (ne_zero_of_mem_D hz)))).add
    (hasDerivAt_S gcoeff_polyBdd.dc hz')

lemma deriv_L {z : ℂ} (hz : z ∈ D) : deriv L z = ell1 z := by
  rw [(L_eventuallyEq hz).deriv_eq, (hasDerivAt_ell hz).deriv]

theorem L_differentiableOn : DifferentiableOn ℂ L D := fun _ hw =>
  ((hasDerivAt_ell hw).differentiableAt.congr_of_eventuallyEq
    (L_eventuallyEq hw)).differentiableWithinAt

theorem L_solves {z : ℂ} (hz : z ∈ D) : legendreOp L z = 0 := by
  have hz' := norm_lt_one_of_mem_D hz
  have hz0 := ne_zero_of_mem_D hz
  rw [legendreOp_congr (L_eventuallyEq hz)]
  unfold legendreOp
  rw [(deriv_ell_eventuallyEq hz).deriv_eq, (hasDerivAt_ell1 hz).deriv,
    (hasDerivAt_ell hz).deriv]
  have eqA := ode_A hz'
  have eqB := ode_B hz'
  have hu : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
  simp only [ell, ell1]
  linear_combination (Complex.log z) * eqA + eqB +
    (2 * (1 - z) * S (dc coeff) z - (1 - z) * S coeff z * z⁻¹ - S coeff z) * hu

/-! ### The Wronskian -/

/-- The conserved quantity `(1-z) F² + z(1-z)(F G' - F' G)`. -/
noncomputable def wr (w : ℂ) : ℂ :=
  (1 - w) * (S coeff w * S coeff w) +
    w * (1 - w) * (S coeff w * S (dc gcoeff) w - S (dc coeff) w * S gcoeff w)

lemma hasDerivAt_wr {w : ℂ} (hw : ‖w‖ < 1) : HasDerivAt wr 0 w := by
  have hA := hasDerivAt_S coeff_polyBdd hw
  have hA1 := hasDerivAt_S coeff_polyBdd.dc hw
  have hB := hasDerivAt_S gcoeff_polyBdd hw
  have hB1 := hasDerivAt_S gcoeff_polyBdd.dc hw
  have hid : HasDerivAt (fun x : ℂ => x) 1 w := hasDerivAt_id' w
  have h := ((hid.const_sub 1).mul (hA.mul hA)).add
    ((hid.mul (hid.const_sub 1)).mul ((hA.mul hB1).sub (hA1.mul hB)))
  have eqA := ode_A hw
  have eqB := ode_B hw
  exact h.congr_deriv (by
    simp only [Pi.mul_apply, Pi.sub_apply]
    linear_combination S coeff w * eqB - S gcoeff w * eqA)

lemma wr_eq_one {z : ℂ} (hz : ‖z‖ < 1) : wr z = 1 := by
  have hz' : z ∈ Metric.ball (0 : ℂ) 1 := by simpa using hz
  have hdiff : DifferentiableOn ℂ wr (Metric.ball 0 1) := fun w hw =>
    (hasDerivAt_wr (by simpa using hw)).differentiableAt.differentiableWithinAt
  have h := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    hdiff (fun w hw => (hasDerivAt_wr (by simpa using hw)).deriv) hz'
    (Metric.mem_ball_self one_pos)
  rw [h]
  simp [wr, S_zero, coeff_zero]

theorem wronskian {z : ℂ} (hz : z ∈ D) :
    F z * deriv L z - deriv F z * L z = 1 / (z * (1 - z)) := by
  have hz' := norm_lt_one_of_mem_D hz
  have hz0 := ne_zero_of_mem_D hz
  have hz1 := one_sub_ne_zero_of_mem_D hz
  rw [deriv_L hz, deriv_F hz', F_eq_S hz', (L_eventuallyEq hz).eq_of_nhds,
    eq_div_iff (mul_ne_zero hz0 hz1)]
  have hw := wr_eq_one hz'
  have hu : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
  simp only [wr] at hw
  simp only [ell, ell1]
  linear_combination hw + (1 - z) * S coeff z ^ 2 * hu

end Legendre
