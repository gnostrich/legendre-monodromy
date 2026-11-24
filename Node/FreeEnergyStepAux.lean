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

end J

end Node
