module

public import Mathlib

@[expose] public section

/-!
# Auxiliary estimates for `Node.FreeEnergyStep`

* `Node.fe_cov`: the substitution `t = w^(2k)` on `(0,1]`,
  `∫₀¹ w^h F(w^(2k)) dw = (1/(2k)) ∫₀¹ t^(a-1) F(t) dt` with `a = (h+1)/(2k)`.
* Two-sided bounds for `J(n) = ∫₀¹ t^(a-1) G(n t) dt`, `G` positive, antitone, continuous:
  `Node.fe_J_fast` (`G = O(x^(-ν))`, `ν > a`: `J ≍ n^(-a)`),
  `Node.fe_J_eq` (`G ≍ x^(-a) (log x)^p`: `J ≍ n^(-a) (log n)^(p+1)`),
  `Node.fe_J_slow` (`G ≍ x^(-μ) (log x)^p`, `μ < a`: `J ≍ n^(-μ) (log n)^p`).
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped Interval

namespace Node

theorem fe_cov (k : ℕ) (hk : 0 < k) (h : ℝ) (F : ℝ → ℝ) :
    ∫ w in Ioc (0 : ℝ) 1, w ^ h * F (w ^ (2 * k)) =
      (1 / (2 * (k : ℝ))) * ∫ t in (0 : ℝ)..1, t ^ ((h + 1) / (2 * (k : ℝ)) - 1) * F t := by
  have hp : (0 : ℝ) < 2 * (k : ℝ) := by positivity
  have key := integral_comp_rpow_Ioi_of_pos
    (g := (Iic (1 : ℝ)).indicator (fun t => t ^ ((h + 1) / (2 * (k : ℝ)) - 1) * F t)) hp
  rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic] at key
  rw [intervalIntegral.integral_of_le zero_le_one, ← key]
  have hcongr : ∫ x in Ioi (0 : ℝ), ((2 * (k : ℝ)) * x ^ (2 * (k : ℝ) - 1)) •
      (Iic (1 : ℝ)).indicator (fun t => t ^ ((h + 1) / (2 * (k : ℝ)) - 1) * F t)
        (x ^ (2 * (k : ℝ))) =
      ∫ x in Ioi (0 : ℝ), (Iic (1 : ℝ)).indicator
        (fun w => (2 * (k : ℝ)) * (w ^ h * F (w ^ (2 * k)))) x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx : (0 : ℝ) < x := hx
    have hxp : x ^ (2 * (k : ℝ)) = x ^ (2 * k) := by
      rw [← Real.rpow_natCast]; push_cast; rfl
    by_cases hx1 : x ≤ 1
    · have hle : x ^ (2 * (k : ℝ)) ≤ 1 := Real.rpow_le_one hx.le hx1 hp.le
      rw [indicator_of_mem (show x ^ (2 * (k : ℝ)) ∈ Iic 1 from hle),
        indicator_of_mem (show x ∈ Iic 1 from hx1), smul_eq_mul]
      have e1 : (x ^ (2 * (k : ℝ))) ^ ((h + 1) / (2 * (k : ℝ)) - 1) =
          x ^ (h + 1 - 2 * (k : ℝ)) := by
        rw [← Real.rpow_mul hx.le]; congr 1; field_simp
      have e2 : x ^ (2 * (k : ℝ) - 1) * x ^ (h + 1 - 2 * (k : ℝ)) = x ^ h := by
        rw [← Real.rpow_add hx]; congr 1; ring
      rw [e1, hxp, ← e2]; ring
    · have hgt : 1 < x ^ (2 * (k : ℝ)) := Real.one_lt_rpow (lt_of_not_ge hx1) hp
      rw [indicator_of_notMem (show x ^ (2 * (k : ℝ)) ∉ Iic 1 from
          fun h' => absurd (h' : _ ≤ (1 : ℝ)) (not_le.2 hgt)),
        indicator_of_notMem (show x ∉ Iic 1 from hx1), smul_zero]
  rw [hcongr, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic, integral_const_mul]
  field_simp

section J

variable {a : ℝ} {G : ℝ → ℝ}

theorem fe_ii (ha : 0 < a) (hGc : Continuous G) (n x y : ℝ) :
    IntervalIntegrable (fun t => t ^ (a - 1) * G (n * t)) volume x y :=
  (intervalIntegral.intervalIntegrable_rpow' (by linarith)).mul_continuousOn
    (by fun_prop : Continuous fun t => G (n * t)).continuousOn

theorem fe_ii_const (ha : 0 < a) (c x y : ℝ) :
    IntervalIntegrable (fun t => t ^ (a - 1) * c) volume x y :=
  (intervalIntegral.intervalIntegrable_rpow' (by linarith)).mul_const c

theorem fe_int_rpow (ha : 0 < a) (s : ℝ) : ∫ t in (0 : ℝ)..s, t ^ (a - 1) = s ^ a / a := by
  rw [integral_rpow (Or.inl (by linarith))]
  simp [Real.zero_rpow ha.ne']

theorem fe_integrand_nonneg (hGpos : ∀ x, 0 < G x) (n : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t ^ (a - 1) * G (n * t) :=
  mul_nonneg (Real.rpow_nonneg ht _) (hGpos _).le

theorem fe_J_nonneg (hGpos : ∀ x, 0 < G x) (n : ℝ) :
    0 ≤ ∫ t in (0 : ℝ)..1, t ^ (a - 1) * G (n * t) :=
  intervalIntegral.integral_nonneg zero_le_one (fun _ ht => fe_integrand_nonneg hGpos n ht.1)

theorem fe_split (ha : 0 < a) (hGc : Continuous G) (n s : ℝ) :
    ∫ t in (0 : ℝ)..1, t ^ (a - 1) * G (n * t) =
      (∫ t in (0 : ℝ)..s, t ^ (a - 1) * G (n * t)) + ∫ t in s..1, t ^ (a - 1) * G (n * t) :=
  (intervalIntegral.integral_add_adjacent_intervals (fe_ii ha hGc n _ _)
    (fe_ii ha hGc n _ _)).symm

theorem fe_sub_le (ha : 0 < a) (hGc : Continuous G) (hGpos : ∀ x, 0 < G x) (n : ℝ) {s s' : ℝ}
    (hs : 0 ≤ s) (hss' : s ≤ s') (hs' : s' ≤ 1) :
    ∫ t in s..s', t ^ (a - 1) * G (n * t) ≤ ∫ t in (0 : ℝ)..1, t ^ (a - 1) * G (n * t) := by
  rw [fe_split ha hGc n s,
    ← intervalIntegral.integral_add_adjacent_intervals (fe_ii ha hGc n s s') (fe_ii ha hGc n s' 1)]
  have h1 : 0 ≤ ∫ t in (0 : ℝ)..s, t ^ (a - 1) * G (n * t) :=
    intervalIntegral.integral_nonneg hs (fun t ht => fe_integrand_nonneg hGpos n ht.1)
  have h2 : 0 ≤ ∫ t in s'..1, t ^ (a - 1) * G (n * t) :=
    intervalIntegral.integral_nonneg hs'
      (fun t ht => fe_integrand_nonneg hGpos n (hs.trans (hss'.trans ht.1)))
  linarith

theorem fe_lower_a (ha : 0 < a) (hGc : Continuous G) (hGpos : ∀ x, 0 < G x)
    (hGanti : Antitone G) {n : ℝ} (hn : 1 ≤ n) :
    G 1 / a * n ^ (-a) ≤ ∫ t in (0 : ℝ)..1, t ^ (a - 1) * G (n * t) := by
  have hn0 : 0 < n := by linarith
  have hs : 0 ≤ 1 / n := by positivity
  have hs1 : 1 / n ≤ 1 := by rw [div_le_one hn0]; exact hn
  calc G 1 / a * n ^ (-a) = ∫ t in (0 : ℝ)..1 / n, t ^ (a - 1) * G 1 := by
        rw [intervalIntegral.integral_mul_const, fe_int_rpow ha, Real.div_rpow zero_le_one hn0.le,
          Real.one_rpow, Real.rpow_neg hn0.le]
        ring
    _ ≤ ∫ t in (0 : ℝ)..1 / n, t ^ (a - 1) * G (n * t) := by
        refine intervalIntegral.integral_mono_on hs (fe_ii_const ha _ _ _) (fe_ii ha hGc n _ _) ?_
        intro t ht
        refine mul_le_mul_of_nonneg_left (hGanti ?_) (Real.rpow_nonneg ht.1 _)
        have := ht.2
        rw [le_div_iff₀ hn0] at this
        linarith
    _ ≤ _ := fe_sub_le ha hGc hGpos n le_rfl hs hs1

theorem fe_div_rpow {X n : ℝ} (hX : 0 ≤ X) (hn : 0 < n) (r : ℝ) :
    (X / n) ^ r = X ^ r * n ^ (-r) := by
  rw [Real.div_rpow hX hn.le, Real.rpow_neg hn.le, div_eq_mul_inv]

theorem fe_part1_le (ha : 0 < a) (hGc : Continuous G) (hGanti : Antitone G) {n s : ℝ}
    (hn : 0 ≤ n) (hs : 0 ≤ s) :
    ∫ t in (0 : ℝ)..s, t ^ (a - 1) * G (n * t) ≤ G 0 * s ^ a / a := by
  calc _ ≤ ∫ t in (0 : ℝ)..s, t ^ (a - 1) * G 0 :=
        intervalIntegral.integral_mono_on hs (fe_ii ha hGc n _ _) (fe_ii_const ha _ _ _)
          (fun t ht => mul_le_mul_of_nonneg_left (hGanti (mul_nonneg hn ht.1))
            (Real.rpow_nonneg ht.1 _))
    _ = _ := by rw [intervalIntegral.integral_mul_const, fe_int_rpow ha]; ring

theorem fe_upper_fast (ha : 0 < a) (hGc : Continuous G) (hGanti : Antitone G)
    {ν C X : ℝ} (hν : a < ν) (hX : 0 < X) (hC0 : 0 ≤ C) (hC : ∀ x, X ≤ x → G x ≤ C * x ^ (-ν))
    {n : ℝ} (hn : X ≤ n) :
    ∫ t in (0 : ℝ)..1, t ^ (a - 1) * G (n * t) ≤
      (G 0 * X ^ a / a + C * X ^ (a - ν) / (ν - a)) * n ^ (-a) := by
  have hn0 : 0 < n := by linarith
  set s := X / n with hs_def
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := by rw [hs_def, div_le_one hn0]; exact hn
  rw [fe_split ha hGc n s]
  have h1 := fe_part1_le ha hGc hGanti hn0.le hs0.le
  have h0 : (0 : ℝ) ∉ [[s, 1]] := by
    rw [uIcc_of_le hs1]; exact fun h => absurd h.1 (not_le.2 hs0)
  have h2 : ∫ t in s..1, t ^ (a - 1) * G (n * t) ≤
      ∫ t in s..1, C * n ^ (-ν) * t ^ (a - 1 - ν) := by
    refine intervalIntegral.integral_mono_on hs1 (fe_ii ha hGc n _ _)
      ((intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).const_mul _) ?_
    intro t ht
    have ht0 : 0 < t := hs0.trans_le ht.1
    have hnt : X ≤ n * t := by
      have := ht.1; rw [hs_def, div_le_iff₀ hn0] at this; linarith
    calc t ^ (a - 1) * G (n * t) ≤ t ^ (a - 1) * (C * (n * t) ^ (-ν)) :=
          mul_le_mul_of_nonneg_left (hC _ hnt) (Real.rpow_nonneg ht0.le _)
      _ = C * n ^ (-ν) * t ^ (a - 1 - ν) := by
          rw [Real.mul_rpow hn0.le ht0.le, show a - 1 - ν = (a - 1) + (-ν) by ring,
            Real.rpow_add ht0]
          ring
  have h3 : ∫ t in s..1, C * n ^ (-ν) * t ^ (a - 1 - ν) =
      C * n ^ (-ν) * ((1 - s ^ (a - ν)) / (a - ν)) := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inr ⟨by linarith, h0⟩)]
    simp only [Real.one_rpow, show a - 1 - ν + 1 = a - ν by ring]
  have key : (1 - s ^ (a - ν)) / (a - ν) ≤ s ^ (a - ν) / (ν - a) := by
    rw [show (1 - s ^ (a - ν)) / (a - ν) = (s ^ (a - ν) - 1) / (ν - a) by
      rw [div_eq_div_iff (by linarith) (by linarith)]; ring]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have h4 : C * n ^ (-ν) * ((1 - s ^ (a - ν)) / (a - ν)) ≤
      C * n ^ (-ν) * (s ^ (a - ν) / (ν - a)) :=
    mul_le_mul_of_nonneg_left key (mul_nonneg hC0 (Real.rpow_nonneg hn0.le _))
  have hsa : s ^ a = X ^ a * n ^ (-a) := fe_div_rpow hX.le hn0 a
  have hsb : s ^ (a - ν) = X ^ (a - ν) * n ^ (-(a - ν)) := fe_div_rpow hX.le hn0 _
  have hnn : n ^ (-ν) * n ^ (-(a - ν)) = n ^ (-a) := by
    rw [← Real.rpow_add hn0]; congr 1; ring
  calc _ ≤ G 0 * s ^ a / a + C * n ^ (-ν) * (s ^ (a - ν) / (ν - a)) := by linarith
    _ = _ := by rw [hsa, hsb, ← hnn]; ring

theorem fe_upper_log (ha : 0 < a) (hGc : Continuous G) (hGanti : Antitone G)
    {μ C X : ℝ} {p : ℕ} (hX : 1 ≤ X) (hC0 : 0 ≤ C)
    (hC : ∀ x, X ≤ x → G x ≤ C * (x ^ (-μ) * Real.log x ^ p)) {n : ℝ} (hn : X ≤ n) :
    ∫ t in (0 : ℝ)..1, t ^ (a - 1) * G (n * t) ≤
      G 0 * X ^ a / a * n ^ (-a) +
        C * n ^ (-μ) * Real.log n ^ p * ∫ t in X / n..1, t ^ (a - 1 - μ) := by
  have hn0 : 0 < n := by linarith
  set s := X / n with hs_def
  have hs0 : 0 < s := by have : (0 : ℝ) < X := by linarith
                         positivity
  have hs1 : s ≤ 1 := by rw [hs_def, div_le_one hn0]; exact hn
  rw [fe_split ha hGc n s]
  have h1 := fe_part1_le ha hGc hGanti hn0.le hs0.le
  have h0 : (0 : ℝ) ∉ [[s, 1]] := by
    rw [uIcc_of_le hs1]; exact fun h => absurd h.1 (not_le.2 hs0)
  have h2 : ∫ t in s..1, t ^ (a - 1) * G (n * t) ≤
      ∫ t in s..1, C * n ^ (-μ) * Real.log n ^ p * t ^ (a - 1 - μ) := by
    refine intervalIntegral.integral_mono_on hs1 (fe_ii ha hGc n _ _)
      ((intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).const_mul _) ?_
    intro t ht
    have ht0 : 0 < t := hs0.trans_le ht.1
    have hnt : X ≤ n * t := by
      have := ht.1; rw [hs_def, div_le_iff₀ hn0] at this; linarith
    have hnt' : n * t ≤ n := by nlinarith [ht.2]
    have hlog : Real.log (n * t) ^ p ≤ Real.log n ^ p :=
      pow_le_pow_left₀ (Real.log_nonneg (by linarith))
        (Real.log_le_log (by positivity) hnt') p
    calc t ^ (a - 1) * G (n * t) ≤ t ^ (a - 1) * (C * ((n * t) ^ (-μ) * Real.log (n * t) ^ p)) :=
          mul_le_mul_of_nonneg_left (hC _ hnt) (Real.rpow_nonneg ht0.le _)
      _ ≤ t ^ (a - 1) * (C * ((n * t) ^ (-μ) * Real.log n ^ p)) := by
          gcongr
      _ = C * n ^ (-μ) * Real.log n ^ p * t ^ (a - 1 - μ) := by
          rw [Real.mul_rpow hn0.le ht0.le, show a - 1 - μ = (a - 1) + (-μ) by ring,
            Real.rpow_add ht0]
          ring
  rw [intervalIntegral.integral_const_mul] at h2
  have hsa : s ^ a = X ^ a * n ^ (-a) := fe_div_rpow (by linarith) hn0 a
  calc _ ≤ G 0 * s ^ a / a + C * n ^ (-μ) * Real.log n ^ p * ∫ t in s..1, t ^ (a - 1 - μ) := by
        linarith
    _ = _ := by rw [hsa]; ring

/-- Extract eventual pointwise bounds from `G =O g` with `g` eventually nonnegative. -/
theorem fe_bound_of_isBigO {f g : ℝ → ℝ} (hO : f =O[atTop] g) (hf : ∀ x, 1 ≤ x → 0 ≤ f x)
    (hg : ∀ x, 1 ≤ x → 0 ≤ g x) :
    ∃ C > 0, ∃ X, 1 ≤ X ∧ ∀ x, X ≤ x → f x ≤ C * g x := by
  obtain ⟨C, hC0, hCw⟩ := hO.exists_pos
  obtain ⟨X, hX⟩ := eventually_atTop.1 hCw.bound
  refine ⟨C, hC0, max X 1, le_max_right _ _, fun x hx => ?_⟩
  have := hX x (le_trans (le_max_left _ _) hx)
  rwa [Real.norm_of_nonneg (hf x ((le_max_right _ _).trans hx)),
    Real.norm_of_nonneg (hg x ((le_max_right _ _).trans hx))]
    at this

theorem fe_J_fast (ha : 0 < a) (hGc : Continuous G) (hGpos : ∀ x, 0 < G x)
    (hGanti : Antitone G) {ν : ℝ} (hν : a < ν) (hGO : G =O[atTop] fun x : ℝ => x ^ (-ν)) :
    (fun n : ℝ => ∫ t in (0 : ℝ)..1, t ^ (a - 1) * G (n * t)) =Θ[atTop] fun n => n ^ (-a) := by
  obtain ⟨C, hC0, X, hX1, hC⟩ := fe_bound_of_isBigO hGO (fun x _ => (hGpos x).le)
    (fun x hx => Real.rpow_nonneg (by linarith) _)
  constructor
  · refine IsBigO.of_bound (G 0 * X ^ a / a + C * X ^ (a - ν) / (ν - a))
      (eventually_atTop.2 ⟨X, fun n hn => ?_⟩)
    have hn0 : 0 < n := by linarith
    rw [Real.norm_of_nonneg (fe_J_nonneg hGpos n), Real.norm_of_nonneg (by positivity)]
    exact fe_upper_fast ha hGc hGanti hν (by linarith) hC0.le hC hn
  · refine IsBigO.of_bound (a / G 1) (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have hn0 : 0 < n := by linarith
    rw [Real.norm_of_nonneg (fe_J_nonneg hGpos n), Real.norm_of_nonneg (by positivity)]
    have := fe_lower_a ha hGc hGpos hGanti hn
    have hG1 := hGpos 1
    rw [div_mul_eq_mul_div, div_le_iff₀ ha] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ hG1]
    linarith

theorem fe_J_slow (ha : 0 < a) (hGc : Continuous G) (hGpos : ∀ x, 0 < G x)
    (hGanti : Antitone G) {μ : ℝ} {p : ℕ} (hμa : μ < a)
    (hGθ : G =Θ[atTop] fun x : ℝ => x ^ (-μ) * Real.log x ^ p) :
    (fun n : ℝ => ∫ t in (0 : ℝ)..1, t ^ (a - 1) * G (n * t)) =Θ[atTop]
      fun n => n ^ (-μ) * Real.log n ^ p := by
  have hgnn : ∀ x : ℝ, 1 ≤ x → 0 ≤ x ^ (-μ) * Real.log x ^ p := fun x hx =>
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (pow_nonneg (Real.log_nonneg hx) _)
  obtain ⟨C, hC0, X, hX1, hC⟩ := fe_bound_of_isBigO hGθ.1 (fun x _ => (hGpos x).le) hgnn
  obtain ⟨D, hD0, Y, hY1, hD⟩ := fe_bound_of_isBigO hGθ.2 hgnn (fun x _ => (hGpos x).le)
  constructor
  · refine IsBigO.of_bound (G 0 * X ^ a / a + C / (a - μ))
      (eventually_atTop.2 ⟨max X (Real.exp 1), fun n hn => ?_⟩)
    have hnX : X ≤ n := le_trans (le_max_left _ _) hn
    have hne : Real.exp 1 ≤ n := le_trans (le_max_right _ _) hn
    have hn0 : 0 < n := by linarith
    have hn1 : 1 ≤ n := by linarith
    have hlog1 : 1 ≤ Real.log n := by rw [Real.le_log_iff_exp_le hn0]; exact hne
    rw [Real.norm_of_nonneg (fe_J_nonneg hGpos n), Real.norm_of_nonneg (hgnn n hn1)]
    have hU := fe_upper_log ha hGc hGanti hX1 hC0.le hC hnX
    set s := X / n with hs_def
    have hs0 : 0 < s := by have : (0 : ℝ) < X := by linarith
                           positivity
    have hs1 : s ≤ 1 := by rw [hs_def, div_le_one hn0]; exact hnX
    have hI : ∫ t in s..1, t ^ (a - 1 - μ) ≤ 1 / (a - μ) := by
      rw [integral_rpow (Or.inl (by linarith)), show a - 1 - μ + 1 = a - μ by ring,
        Real.one_rpow]
      have : 0 ≤ s ^ (a - μ) := Real.rpow_nonneg hs0.le _
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hp1 : 1 ≤ Real.log n ^ p := one_le_pow₀ hlog1
    have hna : n ^ (-a) ≤ n ^ (-μ) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hnμ : 0 ≤ n ^ (-μ) := Real.rpow_nonneg hn0.le _
    have hG0 : 0 ≤ G 0 * X ^ a / a := by
      have := hGpos 0; have : 0 ≤ X ^ a := Real.rpow_nonneg (by linarith) _; positivity
    have hlp : 0 ≤ Real.log n ^ p := by linarith
    calc _ ≤ _ := hU
      _ ≤ G 0 * X ^ a / a * (n ^ (-μ) * Real.log n ^ p) +
          C * n ^ (-μ) * Real.log n ^ p * (1 / (a - μ)) := by
        gcongr
        calc n ^ (-a) ≤ n ^ (-μ) := hna
          _ = n ^ (-μ) * 1 := (mul_one _).symm
          _ ≤ n ^ (-μ) * Real.log n ^ p := by gcongr
      _ = _ := by ring
  · refine IsBigO.of_bound (D * (a / (1 - (1 / 2) ^ a)))
      (eventually_atTop.2 ⟨Y, fun n hn => ?_⟩)
    have hn0 : 0 < n := by linarith
    have hn1 : 1 ≤ n := by linarith
    rw [Real.norm_of_nonneg (fe_J_nonneg hGpos n), Real.norm_of_nonneg (hgnn n hn1)]
    have hK : 0 < 1 - (1 / 2 : ℝ) ^ a := by
      have : (1 / 2 : ℝ) ^ a < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha
      linarith
    have hL : G n * ((1 - (1 / 2) ^ a) / a) ≤ ∫ t in (0 : ℝ)..1, t ^ (a - 1) * G (n * t) := by
      calc G n * ((1 - (1 / 2) ^ a) / a) = ∫ t in (1 / 2 : ℝ)..1, t ^ (a - 1) * G n := by
            rw [intervalIntegral.integral_mul_const, integral_rpow (Or.inl (by linarith)),
              sub_add_cancel, Real.one_rpow]
            ring
        _ ≤ ∫ t in (1 / 2 : ℝ)..1, t ^ (a - 1) * G (n * t) := by
            refine intervalIntegral.integral_mono_on (by norm_num) (fe_ii_const ha _ _ _)
              (fe_ii ha hGc n _ _) ?_
            intro t ht
            have ht0 : 0 ≤ t := by linarith [ht.1]
            refine mul_le_mul_of_nonneg_left (hGanti ?_) (Real.rpow_nonneg ht0 _)
            nlinarith [ht.2]
        _ ≤ _ := fe_sub_le ha hGc hGpos n (by norm_num) (by norm_num) le_rfl
    have hDn := hD n hn
    have : G n ≤ (a / (1 - (1 / 2) ^ a)) * ∫ t in (0 : ℝ)..1, t ^ (a - 1) * G (n * t) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hK]
      rw [mul_div_assoc', div_le_iff₀ ha] at hL
      linarith
    calc _ ≤ D * G n := hDn
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left this hD0.le

theorem fe_J_eq (ha : 0 < a) (hGc : Continuous G) (hGpos : ∀ x, 0 < G x)
    (hGanti : Antitone G) {p : ℕ}
    (hGθ : G =Θ[atTop] fun x : ℝ => x ^ (-a) * Real.log x ^ p) :
    (fun n : ℝ => ∫ t in (0 : ℝ)..1, t ^ (a - 1) * G (n * t)) =Θ[atTop]
      fun n => n ^ (-a) * Real.log n ^ (p + 1) := by
  have hgnn : ∀ x : ℝ, 1 ≤ x → 0 ≤ x ^ (-a) * Real.log x ^ p := fun x hx =>
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (pow_nonneg (Real.log_nonneg hx) _)
  have hgnn' : ∀ x : ℝ, 1 ≤ x → 0 ≤ x ^ (-a) * Real.log x ^ (p + 1) := fun x hx =>
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (pow_nonneg (Real.log_nonneg hx) _)
  obtain ⟨C, hC0, X, hX1, hC⟩ := fe_bound_of_isBigO hGθ.1 (fun x _ => (hGpos x).le) hgnn
  obtain ⟨D, hD0, Y, hY1, hD⟩ := fe_bound_of_isBigO hGθ.2 hgnn (fun x _ => (hGpos x).le)
  have hinv : ∀ {s : ℝ}, 0 < s → s ≤ 1 →
      ∫ t in s..1, t ^ (a - 1 - a) = Real.log (1 / s) := by
    intro s hs0 hs1
    have h0 : (0 : ℝ) ∉ [[s, 1]] := by
      rw [uIcc_of_le hs1]; exact fun h => absurd h.1 (not_le.2 hs0)
    have : (fun t : ℝ => t ^ (a - 1 - a)) = fun t => t⁻¹ := by
      funext t; rw [show a - 1 - a = -1 by ring, Real.rpow_neg_one]
    rw [this, integral_inv h0]
  constructor
  · refine IsBigO.of_bound (G 0 * X ^ a / a + C)
      (eventually_atTop.2 ⟨max X (Real.exp 1), fun n hn => ?_⟩)
    have hnX : X ≤ n := le_trans (le_max_left _ _) hn
    have hne : Real.exp 1 ≤ n := le_trans (le_max_right _ _) hn
    have hn0 : 0 < n := by linarith
    have hn1 : 1 ≤ n := by linarith
    have hlog1 : 1 ≤ Real.log n := by rw [Real.le_log_iff_exp_le hn0]; exact hne
    rw [Real.norm_of_nonneg (fe_J_nonneg hGpos n), Real.norm_of_nonneg (hgnn' n hn1)]
    have hU := fe_upper_log ha hGc hGanti hX1 hC0.le hC hnX
    have hX0 : (0 : ℝ) < X := by linarith
    have hs0 : 0 < X / n := by positivity
    have hs1 : X / n ≤ 1 := by rw [div_le_one hn0]; exact hnX
    have hI : ∫ t in X / n..1, t ^ (a - 1 - a) ≤ Real.log n := by
      rw [hinv hs0 hs1, one_div_div, Real.log_div hn0.ne' hX0.ne']
      have := Real.log_nonneg hX1
      linarith
    have hp1 : 1 ≤ Real.log n ^ (p + 1) := one_le_pow₀ hlog1
    have hnμ : 0 ≤ n ^ (-a) := Real.rpow_nonneg hn0.le _
    have hG0 : 0 ≤ G 0 * X ^ a / a := by
      have := hGpos 0; have : 0 ≤ X ^ a := Real.rpow_nonneg (by linarith) _; positivity
    have hlp : 0 ≤ Real.log n ^ p := pow_nonneg (by linarith) _
    calc _ ≤ _ := hU
      _ ≤ G 0 * X ^ a / a * (n ^ (-a) * Real.log n ^ (p + 1)) +
          C * n ^ (-a) * Real.log n ^ p * Real.log n := by
        gcongr
        calc n ^ (-a) = n ^ (-a) * 1 := (mul_one _).symm
          _ ≤ n ^ (-a) * Real.log n ^ (p + 1) := by gcongr
      _ = _ := by ring
  · refine IsBigO.of_bound (D * 2 ^ (p + 1))
      (eventually_atTop.2 ⟨max (Y ^ 2) 1, fun n hn => ?_⟩)
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnY : Y ^ 2 ≤ n := le_trans (le_max_left _ _) hn
    have hn0 : 0 < n := by linarith
    rw [Real.norm_of_nonneg (fe_J_nonneg hGpos n), Real.norm_of_nonneg (hgnn' n hn1)]
    set r := Real.sqrt n with hr_def
    have hr0 : 0 < r := Real.sqrt_pos.2 hn0
    have hrr : r * r = n := Real.mul_self_sqrt hn0.le
    have hrY : Y ≤ r := by
      have := Real.sqrt_le_sqrt hnY
      rwa [Real.sqrt_sq (by linarith)] at this
    have hr1 : 1 ≤ r := hY1.trans hrY
    have hlogr : Real.log r = Real.log n / 2 := Real.log_sqrt hn0.le
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
    set s := 1 / r with hs_def
    have hs0 : 0 < s := by positivity
    have hs1 : s ≤ 1 := by rw [hs_def, div_le_one hr0]; exact hr1
    set c := n ^ (-a) * (Real.log n / 2) ^ p / D with hc_def
    have hL : c * (Real.log n / 2) ≤ ∫ t in (0 : ℝ)..1, t ^ (a - 1) * G (n * t) := by
      calc c * (Real.log n / 2) = ∫ t in s..1, c * t ^ (a - 1 - a) := by
            rw [intervalIntegral.integral_const_mul, hinv hs0 hs1, hs_def, one_div_one_div, hlogr]
        _ ≤ ∫ t in s..1, t ^ (a - 1) * G (n * t) := by
            have h0 : (0 : ℝ) ∉ [[s, 1]] := by
              rw [uIcc_of_le hs1]; exact fun h => absurd h.1 (not_le.2 hs0)
            refine intervalIntegral.integral_mono_on hs1
              ((intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).const_mul _)
              (fe_ii ha hGc n _ _) ?_
            intro t ht
            have ht0 : 0 < t := hs0.trans_le ht.1
            have hnt : r ≤ n * t := by
              have := ht.1; rw [hs_def, div_le_iff₀ hr0] at this; nlinarith
            have hlog : (Real.log n / 2) ^ p ≤ Real.log (n * t) ^ p := by
              rw [← hlogr]
              exact pow_le_pow_left₀ (Real.log_nonneg hr1) (Real.log_le_log hr0 hnt) p
            have hG := hD (n * t) (hrY.trans hnt)
            have hG' : (n * t) ^ (-a) * Real.log (n * t) ^ p / D ≤ G (n * t) := by
              rw [div_le_iff₀ hD0]; linarith
            calc c * t ^ (a - 1 - a) = t ^ (a - 1) * ((n * t) ^ (-a) * (Real.log n / 2) ^ p / D) := by
                  rw [hc_def, Real.mul_rpow hn0.le ht0.le, show a - 1 - a = (a - 1) + (-a) by ring,
                    Real.rpow_add ht0]
                  ring
              _ ≤ t ^ (a - 1) * ((n * t) ^ (-a) * Real.log (n * t) ^ p / D) := by
                  gcongr
              _ ≤ t ^ (a - 1) * G (n * t) := by gcongr
        _ ≤ _ := fe_sub_le ha hGc hGpos n hs0.le hs1 le_rfl
    have : n ^ (-a) * Real.log n ^ (p + 1) = D * 2 ^ (p + 1) * (c * (Real.log n / 2)) := by
      rw [hc_def, div_pow]; field_simp; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hL (by positivity)

end J

end Node
