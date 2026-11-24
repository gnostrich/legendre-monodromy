module

public import Node.FreeEnergyStep
public import Node.FreeEnergyMonomialAux

@[expose] public section

/-!
# The free energy of monomial models

`monomial_partition_asymptotic`: `Z(n) ≍ n^(-λ) (log n)^(m-1)`, by induction on the dimension
using `base_theta` and `step_theta`; `monomial_free_energy`: `F(n) = λ log n - (m-1) log log n
+ O(1)`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Node

/-- The partition function of the monomial model: with `λ = minⱼ (hⱼ + 1)/(2kⱼ)` attained by
`m` indices (all `kⱼ > 0`, all `hⱼ > -1`),
`Z(n) = ∫_{[0,1]^d} exp(-n K(w)) φ(w) dw ≍ n^{-λ} (log n)^{m-1}` as real `n → ∞`. -/
theorem monomial_partition_asymptotic {d : ℕ} (k : Fin d → ℕ) (hk : ∀ j, 0 < k j)
    (h : Fin d → ℝ) (hh : ∀ j, -1 < h j) (lam : ℝ)
    (hmin : ∀ j, lam ≤ (h j + 1) / (2 * (k j : ℝ)))
    (hattain : ∃ j, (h j + 1) / (2 * (k j : ℝ)) = lam) :
    (fun n : ℝ => ∫ w in Set.univ.pi (fun _ => Icc (0 : ℝ) 1),
        Real.exp (-n * ∏ j, w j ^ (2 * k j)) * ∏ j, w j ^ h j) =Θ[atTop]
      fun n : ℝ => n ^ (-lam) *
        Real.log n ^ ((Finset.univ.filter fun j => (h j + 1) / (2 * (k j : ℝ)) = lam).card - 1) := by
  cases d with
  | zero =>
    obtain ⟨j, _⟩ := hattain
    exact j.elim0
  | succ d =>
    rw [NC.cube_restrict_eq]
    exact FEM.Zf_theta d k hk h hh lam hmin hattain

/-- The free energy of the monomial model:
`F(n) = -log Z(n) = λ log n - (m - 1) log log n + O(1)` as real `n → ∞`. -/
theorem monomial_free_energy {d : ℕ} (k : Fin d → ℕ) (hk : ∀ j, 0 < k j)
    (h : Fin d → ℝ) (hh : ∀ j, -1 < h j) (lam : ℝ)
    (hmin : ∀ j, lam ≤ (h j + 1) / (2 * (k j : ℝ)))
    (hattain : ∃ j, (h j + 1) / (2 * (k j : ℝ)) = lam) :
    (fun n : ℝ => -Real.log (∫ w in Set.univ.pi (fun _ => Icc (0 : ℝ) 1),
        Real.exp (-n * ∏ j, w j ^ (2 * k j)) * ∏ j, w j ^ h j) -
        (lam * Real.log n -
          (((Finset.univ.filter fun j => (h j + 1) / (2 * (k j : ℝ)) = lam).card : ℝ) - 1) *
            Real.log (Real.log n))) =O[atTop]
      fun _ : ℝ => (1 : ℝ) := by
  have hT := monomial_partition_asymptotic k hk h hh lam hmin hattain
  rw [NC.cube_restrict_eq] at hT ⊢
  change FEM.Zf k h =Θ[atTop] _ at hT
  change (fun n : ℝ => -Real.log (FEM.Zf k h n) - _) =O[atTop] _
  have hM1 : 1 ≤ (Finset.univ.filter fun j => (h j + 1) / (2 * (k j : ℝ)) = lam).card := by
    obtain ⟨j, hj⟩ := hattain
    exact Finset.card_pos.2 ⟨j, by simp [hj]⟩
  obtain ⟨C, hC, hCb⟩ := hT.1.exists_pos
  obtain ⟨c, hc, hcb⟩ := hT.2.exists_pos
  refine isBigO_iff.2 ⟨max |Real.log C| |Real.log c|, ?_⟩
  filter_upwards [hCb.bound, hcb.bound, eventually_gt_atTop 1] with n h1 h2 hn
  set M := (Finset.univ.filter fun j => (h j + 1) / (2 * (k j : ℝ)) = lam).card
  have hZ := FEM.Zf_pos k h hh n
  have hlog : 0 < Real.log n := Real.log_pos hn
  have hg1 : 0 < n ^ (-lam) := Real.rpow_pos_of_pos (by linarith) _
  have hg2 : 0 < Real.log n ^ (M - 1) := pow_pos hlog _
  have hg : 0 < n ^ (-lam) * Real.log n ^ (M - 1) := mul_pos hg1 hg2
  rw [Real.norm_of_nonneg hZ.le, Real.norm_of_nonneg hg.le] at h1 h2
  have hl1 := Real.log_le_log hZ h1
  have hl2 := Real.log_le_log hg h2
  rw [Real.log_mul hC.ne' hg.ne'] at hl1
  rw [Real.log_mul hc.ne' hZ.ne'] at hl2
  have hlg : Real.log (n ^ (-lam) * Real.log n ^ (M - 1)) =
      -lam * Real.log n + ((M : ℝ) - 1) * Real.log (Real.log n) := by
    rw [Real.log_mul hg1.ne' hg2.ne', Real.log_rpow (by linarith), Real.log_pow,
      Nat.cast_sub hM1, Nat.cast_one]
  rw [hlg] at hl1 hl2
  rw [norm_one, mul_one, Real.norm_eq_abs, abs_le]
  have := le_abs_self (Real.log C)
  have := neg_abs_le (Real.log C)
  have := le_abs_self (Real.log c)
  have := le_max_left |Real.log C| |Real.log c|
  have := le_max_right |Real.log C| |Real.log c|
  constructor <;> linarith

end Node
