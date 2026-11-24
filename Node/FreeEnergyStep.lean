module

public import Mathlib
public import Node.FreeEnergyStepAux

@[expose] public section

/-!
# One-variable Laplace-type estimates for the monomial free energy

`base_theta`: `∫₀¹ w^h exp(-n w^(2k)) dw ≍ n^(-a)` with `a = (h+1)/(2k)`.
`step_theta`: if `G` is continuous, positive, antitone and `G(x) ≍ x^(-μ) (log x)^p`, then
`∫₀¹ w^h G(n w^(2k)) dw` is `≍ n^(-a)` if `a < μ`, `≍ n^(-μ) (log n)^(p+1)` if `a = μ`,
and `≍ n^(-μ) (log n)^p` if `a > μ`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Node

theorem base_theta (k : ℕ) (hk : 0 < k) (h : ℝ) (hh : -1 < h) :
    (fun n : ℝ => ∫ w in Ioc (0 : ℝ) 1, w ^ h * Real.exp (-n * w ^ (2 * k))) =Θ[atTop]
      fun n : ℝ => n ^ (-((h + 1) / (2 * (k : ℝ)))) := by
  set a := (h + 1) / (2 * (k : ℝ)) with ha_def
  have ha : 0 < a := by
    have : 0 < h + 1 := by linarith
    positivity
  have hk0 : (1 / (2 * (k : ℝ))) ≠ 0 := by positivity
  have heq : (fun n : ℝ => ∫ w in Ioc (0 : ℝ) 1, w ^ h * Real.exp (-n * w ^ (2 * k))) =
      fun n => (1 / (2 * (k : ℝ))) *
        ∫ t in (0 : ℝ)..1, t ^ (a - 1) * (fun x => Real.exp (-x)) (n * t) := by
    funext n
    have := fe_cov k hk h (fun t => Real.exp (-n * t))
    rw [this]
    simp only [neg_mul, ha_def]
  have hGO : (fun x : ℝ => Real.exp (-x)) =O[atTop] fun x => x ^ (-(a + 1)) := by
    have h1 := (isLittleO_rpow_exp_atTop (a + 1)).isBigO.inv_rev (by
      filter_upwards [eventually_gt_atTop 0] with x hx h0
      exact absurd h0 (Real.rpow_pos_of_pos hx _).ne')
    refine h1.congr' (Eventually.of_forall fun x => (Real.exp_neg x).symm) ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact (Real.rpow_neg hx.le _).symm
  rw [heq, isTheta_const_mul_left hk0]
  exact fe_J_fast ha (by fun_prop) (fun x => Real.exp_pos _)
    (fun x y hxy => Real.exp_le_exp.2 (neg_le_neg hxy)) (by linarith) hGO

theorem step_theta (k : ℕ) (hk : 0 < k) (h : ℝ) (hh : -1 < h) (μ : ℝ) (hμ : 0 < μ) (p : ℕ)
    (G : ℝ → ℝ) (hGc : Continuous G) (hGpos : ∀ x, 0 < G x) (hGanti : Antitone G)
    (hGθ : G =Θ[atTop] fun x : ℝ => x ^ (-μ) * Real.log x ^ p) :
    (fun n : ℝ => ∫ w in Ioc (0 : ℝ) 1, w ^ h * G (n * w ^ (2 * k))) =Θ[atTop]
      fun n : ℝ =>
        if (h + 1) / (2 * (k : ℝ)) < μ then n ^ (-((h + 1) / (2 * (k : ℝ))))
        else if (h + 1) / (2 * (k : ℝ)) = μ then n ^ (-μ) * Real.log n ^ (p + 1)
        else n ^ (-μ) * Real.log n ^ p := by
  set a := (h + 1) / (2 * (k : ℝ)) with ha_def
  have ha : 0 < a := by
    have : 0 < h + 1 := by linarith
    positivity
  have hk0 : (1 / (2 * (k : ℝ))) ≠ 0 := by positivity
  have heq : (fun n : ℝ => ∫ w in Ioc (0 : ℝ) 1, w ^ h * G (n * w ^ (2 * k))) =
      fun n => (1 / (2 * (k : ℝ))) * ∫ t in (0 : ℝ)..1, t ^ (a - 1) * G (n * t) := by
    funext n
    exact fe_cov k hk h (fun t => G (n * t))
  rw [heq, isTheta_const_mul_left hk0]
  rcases lt_trichotomy a μ with hlt | hEq | hgt
  · simp only [hlt, ↓reduceIte]
    have h2 : (fun x : ℝ => x ^ (-μ) * Real.log x ^ p) =O[atTop]
        fun x => x ^ (-((a + μ) / 2)) := by
      have hl := (isLittleO_log_rpow_rpow_atTop (p : ℝ)
        (show 0 < μ - (a + μ) / 2 by linarith)).isBigO
      have := (isBigO_refl (fun x : ℝ => x ^ (-μ)) atTop).mul hl
      refine this.congr' (Eventually.of_forall fun x => by simp only [Real.rpow_natCast]) ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_add hx]; congr 1; ring
    exact fe_J_fast ha hGc hGpos hGanti (by linarith) (hGθ.1.trans h2)
  · simp only [hEq, lt_irrefl, ↓reduceIte]
    exact fe_J_eq hμ hGc hGpos hGanti hGθ
  · simp only [show ¬ a < μ from not_lt.2 hgt.le, hgt.ne', ↓reduceIte]
    exact fe_J_slow ha hGc hGpos hGanti hgt hGθ

end Node
