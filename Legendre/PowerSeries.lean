module

public import Legendre.Defs

@[expose] public section

/-!
# A small power series toolkit

For a coefficient sequence `c : ℕ → ℂ` which is polynomially bounded
(`‖c n‖ ≤ C * (n + 1) ^ k`, see `Legendre.PS.PolyBdd`) we consider
`S c z = ∑' n, c n * z ^ n` on the unit disc and prove:

* summability on the unit disc (`Legendre.PS.summable_S`),
* `HasDerivAt (S c) (S (dc c) z) z` where `dc c n = (n + 1) * c (n + 1)`
  (`Legendre.PS.hasDerivAt_S`), and the consequences for `deriv` and `deriv ∘ deriv`,
* multiplication by `z` shifts coefficients (`Legendre.PS.HasSum.mul_z`),
* the coefficient formula for the Legendre operator
  `z(1-z) y'' + (1-2z) y' - y/4` applied to `S c` (`Legendre.PS.ode_S`,
  `Legendre.PS.legendreOp_S`).
-/

open Complex Filter Topology

namespace Legendre

namespace PS

/-- A coefficient sequence is polynomially bounded. -/
def PolyBdd (c : ℕ → ℂ) : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ k

/-- The power series with coefficients `c`. -/
noncomputable def S (c : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, c n * z ^ n

/-- The coefficients of the derivative: `dc c n = (n + 1) * c (n + 1)`. -/
def dc (c : ℕ → ℂ) (n : ℕ) : ℂ := ((n : ℂ) + 1) * c (n + 1)

lemma succ_pow_le (k n : ℕ) : ((n : ℝ) + 1) ^ k ≤ 2 ^ k * ((n : ℝ) ^ k + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 := one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := k)
    have h2 : (0 : ℝ) ≤ 0 ^ k := by positivity
    simp only [Nat.cast_zero, zero_add, one_pow]
    nlinarith
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc ((n : ℝ) + 1) ^ k ≤ (2 * (n : ℝ)) ^ k :=
          pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * (n : ℝ) ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * ((n : ℝ) ^ k + 1) := by
          have : (0 : ℝ) ≤ 2 ^ k := by positivity
          nlinarith

lemma summable_succ_pow_geom (k : ℕ) {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ k * r ^ n := by
  have hr : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg h0]
  have h := ((summable_pow_mul_geometric_of_norm_lt_one k hr).add
    (summable_geometric_of_lt_one h0 h1)).mul_left (2 ^ k)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h
  calc ((n : ℝ) + 1) ^ k * r ^ n ≤ 2 ^ k * ((n : ℝ) ^ k + 1) * r ^ n :=
        mul_le_mul_of_nonneg_right (succ_pow_le k n) (by positivity)
    _ = 2 ^ k * ((n : ℝ) ^ k * r ^ n + r ^ n) := by ring

lemma PolyBdd.exists_nonneg {c : ℕ → ℂ} (h : PolyBdd c) :
    ∃ C : ℝ, ∃ k : ℕ, 0 ≤ C ∧ ∀ n : ℕ, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ k := by
  obtain ⟨C, k, hC⟩ := h
  refine ⟨C, k, ?_, hC⟩
  have := hC 0
  simp only [Nat.cast_zero, zero_add, one_pow, mul_one] at this
  exact (norm_nonneg _).trans this

lemma PolyBdd.of_bound {c : ℕ → ℂ} {C : ℝ} (h : ∀ n, ‖c n‖ ≤ C) : PolyBdd c :=
  ⟨C, 0, fun n => by simpa using h n⟩

lemma PolyBdd.mul {c d : ℕ → ℂ} (hc : PolyBdd c) (hd : PolyBdd d) :
    PolyBdd fun n => c n * d n := by
  obtain ⟨C, k, hC0, hC⟩ := hc.exists_nonneg
  obtain ⟨D, l, hD0, hD⟩ := hd.exists_nonneg
  refine ⟨C * D, k + l, fun n => ?_⟩
  rw [norm_mul]
  calc ‖c n‖ * ‖d n‖ ≤ (C * ((n : ℝ) + 1) ^ k) * (D * ((n : ℝ) + 1) ^ l) :=
        mul_le_mul (hC n) (hD n) (norm_nonneg _) (by positivity)
    _ = C * D * ((n : ℝ) + 1) ^ (k + l) := by ring

lemma norm_natCast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, RCLike.norm_natCast]
  push_cast; ring

lemma PolyBdd.dc {c : ℕ → ℂ} (h : PolyBdd c) : PolyBdd (dc c) := by
  obtain ⟨C, k, hC0, hC⟩ := h.exists_nonneg
  refine ⟨C * 2 ^ k, k + 1, fun n => ?_⟩
  simp only [PS.dc, norm_mul, norm_natCast_add_one]
  have h2 := hC (n + 1)
  push_cast at h2
  have h3 : ((n : ℝ) + 1 + 1) ^ k ≤ 2 ^ k * ((n : ℝ) + 1) ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) k
  calc ((n : ℝ) + 1) * ‖c (n + 1)‖ ≤ ((n : ℝ) + 1) * (C * ((n : ℝ) + 1 + 1) ^ k) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ ((n : ℝ) + 1) * (C * (2 ^ k * ((n : ℝ) + 1) ^ k)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left h3 hC0
    _ = C * 2 ^ k * ((n : ℝ) + 1) ^ (k + 1) := by ring

lemma summable_S {c : ℕ → ℂ} (h : PolyBdd c) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n => c n * z ^ n := by
  obtain ⟨C, k, hC0, hC⟩ := h.exists_nonneg
  refine Summable.of_norm_bounded ((summable_succ_pow_geom k (norm_nonneg z) hz).mul_left C)
    (fun n => ?_)
  rw [norm_mul, norm_pow]
  calc ‖c n‖ * ‖z‖ ^ n ≤ C * ((n : ℝ) + 1) ^ k * ‖z‖ ^ n :=
        mul_le_mul_of_nonneg_right (hC n) (by positivity)
    _ = C * (((n : ℝ) + 1) ^ k * ‖z‖ ^ n) := by ring

lemma hasSum_S {c : ℕ → ℂ} (h : PolyBdd c) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => c n * z ^ n) (S c z) :=
  (summable_S h hz).hasSum

lemma S_zero (c : ℕ → ℂ) : S c 0 = c 0 := by
  unfold S
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

theorem hasDerivAt_S {c : ℕ → ℂ} (h : PolyBdd c) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (S c) (S (dc c) z) z := by
  obtain ⟨C, k, hC0, hC⟩ := h.exists_nonneg
  set r : ℝ := (‖z‖ + 1) / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have hzr : ‖z‖ < r := by rw [hr]; linarith
  have hu : Summable fun n : ℕ => C * (((n : ℝ) + 1) ^ (k + 1) * r ^ n) / r :=
    ((summable_succ_pow_geom (k + 1) hr0.le hr1).mul_left C).div_const r
  have hbound : ∀ (n : ℕ) (y : ℂ), y ∈ Metric.ball (0 : ℂ) r →
      ‖c n * ((n : ℂ) * y ^ (n - 1))‖ ≤ C * (((n : ℝ) + 1) ^ (k + 1) * r ^ n) / r := by
    intro n y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    rcases n with _ | n
    · simp only [Nat.cast_zero, zero_mul, mul_zero, norm_zero]
      positivity
    · rw [norm_mul, norm_mul, norm_pow, Nat.add_sub_cancel]
      rw [show (((n + 1 : ℕ) : ℂ)) = (n : ℂ) + 1 by push_cast; ring, norm_natCast_add_one]
      have h2 := hC (n + 1)
      push_cast at h2 ⊢
      have e2 : ‖y‖ ^ n ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg _) hy.le n
      calc ‖c (n + 1)‖ * (((n : ℝ) + 1) * ‖y‖ ^ n)
          ≤ (C * ((n : ℝ) + 1 + 1) ^ k) * (((n : ℝ) + 1 + 1) * r ^ n) :=
            mul_le_mul h2 (mul_le_mul (by linarith) e2 (by positivity) (by positivity))
              (by positivity) (by positivity)
        _ = C * (((n : ℝ) + 1 + 1) ^ (k + 1) * r ^ (n + 1)) / r := by
            field_simp
            ring
  have hzmem : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]; exact hzr
  have key := hasDerivAt_tsum_of_isPreconnected (g := fun n (y : ℂ) => c n * y ^ n)
    (g' := fun n y => c n * ((n : ℂ) * y ^ (n - 1))) hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected
    (fun n y _ => (hasDerivAt_pow n y).const_mul (c n)) hbound
    (Metric.mem_ball_self hr0) (summable_S h (by simp)) hzmem
  have hs : Summable fun n => c n * ((n : ℂ) * z ^ (n - 1)) :=
    Summable.of_norm_bounded hu (fun n => hbound n z hzmem)
  have heq : ∑' n, c n * ((n : ℂ) * z ^ (n - 1)) = S (dc c) z := by
    rw [hs.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, S, PS.dc]
    congr 1
    funext n
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  rw [← heq]
  exact key

lemma deriv_S {c : ℕ → ℂ} (h : PolyBdd c) {z : ℂ} (hz : ‖z‖ < 1) :
    deriv (S c) z = S (dc c) z :=
  (hasDerivAt_S h hz).deriv

lemma differentiableOn_S {c : ℕ → ℂ} (h : PolyBdd c) :
    DifferentiableOn ℂ (S c) (Metric.ball 0 1) := fun z hz =>
  (hasDerivAt_S h (by simpa using hz)).differentiableAt.differentiableWithinAt

lemma deriv_S_eventuallyEq {c : ℕ → ℂ} (h : PolyBdd c) {z : ℂ} (hz : ‖z‖ < 1) :
    deriv (S c) =ᶠ[𝓝 z] S (dc c) := by
  have hmem : Metric.ball (0 : ℂ) 1 ∈ 𝓝 z :=
    Metric.isOpen_ball.mem_nhds (by simpa using hz)
  filter_upwards [hmem] with w hw
  exact deriv_S h (by simpa using hw)

lemma hasDerivAt_deriv_S {c : ℕ → ℂ} (h : PolyBdd c) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (deriv (S c)) (S (dc (dc c)) z) z :=
  (hasDerivAt_S h.dc hz).congr_of_eventuallyEq (deriv_S_eventuallyEq h hz)

lemma deriv_deriv_S {c : ℕ → ℂ} (h : PolyBdd c) {z : ℂ} (hz : ‖z‖ < 1) :
    deriv (deriv (S c)) z = S (dc (dc c)) z :=
  (hasDerivAt_deriv_S h hz).deriv

/-- Multiplying a power series by `z` shifts the coefficients. -/
lemma HasSum.mul_z {c : ℕ → ℂ} {z s : ℂ} (h : HasSum (fun n => c n * z ^ n) s) :
    HasSum (fun n => (if n = 0 then 0 else c (n - 1)) * z ^ n) (z * s) := by
  have h1 : HasSum (fun n => c n * z ^ (n + 1)) (z * s) := by
    convert h.mul_left z using 1
    funext n
    ring
  have h2 := HasSum.zero_add (f := fun n => (if n = 0 then 0 else c (n - 1)) * z ^ n) (m := z * s)
    (by simpa using h1)
  simpa using h2

/-- The coefficients of `z(1-z) y'' + (1-2z) y' - y/4` for `y = S c`. -/
theorem ode_S {c : ℕ → ℂ} (h : PolyBdd c) {z : ℂ} (hz : ‖z‖ < 1) :
    z * (1 - z) * S (dc (dc c)) z + (1 - 2 * z) * S (dc c) z - S c z / 4 =
      S (fun n => ((n : ℂ) + 1) ^ 2 * c (n + 1) - ((n : ℂ) + 1 / 2) ^ 2 * c n) z := by
  have H0 := hasSum_S h hz
  have H1 := hasSum_S h.dc hz
  have H2 := hasSum_S h.dc.dc hz
  have B := HasSum.mul_z H2
  have A := HasSum.mul_z B
  have C := HasSum.mul_z H1
  have tot := ((((B.add H1).sub A).sub (C.mul_left 2)).sub (H0.div_const 4))
  have tot' : HasSum (fun n => (((n : ℂ) + 1) ^ 2 * c (n + 1) - ((n : ℂ) + 1 / 2) ^ 2 * c n) *
      z ^ n) (z * (1 - z) * S (dc (dc c)) z + (1 - 2 * z) * S (dc c) z - S c z / 4) := by
    convert tot using 1
    · funext n
      rcases n with _ | _ | n
      · simp [PS.dc]
        ring
      · simp [PS.dc]
        ring
      · simp [PS.dc]
        push_cast
        ring
    · ring
  exact tot'.tsum_eq.symm

/-- `S c - 2 (1 - z) S (dc c)` as a power series. -/
theorem S_sub_S_dc {c : ℕ → ℂ} (h : PolyBdd c) {z : ℂ} (hz : ‖z‖ < 1) :
    S c z - 2 * (1 - z) * S (dc c) z =
      S (fun n => (2 * (n : ℂ) + 1) * c n - 2 * ((n : ℂ) + 1) * c (n + 1)) z := by
  have H0 := hasSum_S h hz
  have H1 := hasSum_S h.dc hz
  have C := HasSum.mul_z H1
  have tot := (H0.sub (H1.mul_left 2)).add (C.mul_left 2)
  have tot' : HasSum (fun n => ((2 * (n : ℂ) + 1) * c n - 2 * ((n : ℂ) + 1) * c (n + 1)) *
      z ^ n) (S c z - 2 * (1 - z) * S (dc c) z) := by
    convert tot using 1
    · funext n
      rcases n with _ | n
      · simp [PS.dc]
      · simp [PS.dc]
        push_cast
        ring
    · ring
  exact tot'.tsum_eq.symm

/-- The Legendre operator applied to a power series. -/
theorem legendreOp_S {c : ℕ → ℂ} (h : PolyBdd c) {z : ℂ} (hz : ‖z‖ < 1) :
    legendreOp (S c) z =
      S (fun n => ((n : ℂ) + 1) ^ 2 * c (n + 1) - ((n : ℂ) + 1 / 2) ^ 2 * c n) z := by
  rw [← ode_S h hz, legendreOp, deriv_deriv_S h hz, deriv_S h hz]

/-- `legendreOp` only depends on the germ of the function. -/
theorem legendreOp_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    legendreOp f z = legendreOp g z := by
  unfold legendreOp
  rw [h.deriv_eq, h.deriv.deriv_eq, h.eq_of_nhds]

end PS

end Legendre
