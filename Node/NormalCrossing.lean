module

public import Mathlib

@[expose] public section

/-!
# The monomial (normal-crossing) zeta function and the learning coefficient `(λ, m)`

For `K(w) = ∏ⱼ wⱼ^(2kⱼ)` and prior density `∏ⱼ wⱼ^(hⱼ)` on `[0,1]^d`: integrability of
`K^z φ`, the closed form `∏ⱼ 1/(2kⱼ z + hⱼ + 1)`, and the pole of order `m` at `-λ`.

Interface theorems (signatures fixed): `monomial_zeta_integrable`, `monomial_zeta`,
`monomial_pole`.
-/

open MeasureTheory Set Filter Topology

open scoped ENNReal

namespace Node.NC

/-! ### Auxiliary lemmas -/

/-- Lebesgue integral of a product of one-variable functions over a finite product measure. -/
theorem lintegral_fin_prod {n : ℕ} {μ : Fin n → Measure ℝ} [∀ i, SigmaFinite (μ i)]
    (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → ℝ, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : ℝ × (Fin n → ℝ), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i => f i.succ) (fun i => hf _)]
          exact lintegral_prod_mul (μ := μ 0) (ν := Measure.pi fun i => μ i.succ) (f := f 0) (g := fun y : Fin n → ℝ => ∏ i, f i.succ (y i))
            (hf 0).aemeasurable
            (Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]


theorem cube_restrict_eq (d : ℕ) :
    (volume : Measure (Fin d → ℝ)).restrict (Set.univ.pi fun _ => Icc (0 : ℝ) 1) =
      Measure.pi (fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)) := by
  rw [volume_pi, ← Measure.restrict_congr_set (Measure.pi_Ioo_ae_eq_pi_Icc
    (μ := fun _ : Fin d => volume) (f := fun _ => (0 : ℝ)) (g := fun _ => 1)),
    Measure.restrict_pi_pi]

theorem ae_cube (d : ℕ) :
    ∀ᵐ w ∂(Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)), ∀ j, 0 < w j := by
  rw [← Measure.restrict_pi_pi (μ := fun _ : Fin d => (volume : Measure ℝ)) (fun _ => Ioo (0 : ℝ) 1)]
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)] with w hw
  intro j
  exact (hw j (mem_univ j)).1

theorem integrand_eq {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (z : ℝ) (w : Fin d → ℝ)
    (hw : ∀ j, 0 < w j) :
    (∏ j, w j ^ (2 * k j)) ^ z * ∏ j, w j ^ h j = ∏ j, w j ^ (2 * (k j : ℝ) * z + h j) := by
  rw [← Real.finsetProd_rpow _ _ (fun j _ => by have := hw j; positivity), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (hw j).le, ← Real.rpow_add (hw j)]
  push_cast; ring_nf

theorem integrand_ae {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (z : ℝ) :
    (fun w : Fin d → ℝ => (∏ j, w j ^ (2 * k j)) ^ z * ∏ j, w j ^ h j)
      =ᵐ[Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)]
      fun w => ∏ j, w j ^ (2 * (k j : ℝ) * z + h j) := by
  filter_upwards [ae_cube d] with w hw using integrand_eq k h z w hw

theorem integrable_rpow_Ioo_iff (a : ℝ) :
    Integrable (fun x : ℝ => x ^ a) (volume.restrict (Ioo (0 : ℝ) 1)) ↔ -1 < a :=
  intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one

theorem lintegral_enorm_rpow_ne_zero (a : ℝ) :
    ∫⁻ x, ‖x ^ a‖ₑ ∂(volume.restrict (Ioo (0 : ℝ) 1)) ≠ 0 := by
  intro H
  rw [lintegral_eq_zero_iff (by fun_prop)] at H
  have h1 : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), False := by
    filter_upwards [H, ae_restrict_mem measurableSet_Ioo] with x hx hx'
    simp only [Pi.zero_apply, enorm_eq_zero] at hx
    exact (Real.rpow_pos_of_pos hx'.1 a).ne' hx
  rw [ae_iff] at h1
  simp at h1

theorem integrable_prod_rpow_iff {d : ℕ} (a : Fin d → ℝ) :
    Integrable (fun w : Fin d → ℝ => ∏ j, w j ^ a j)
      (Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)) ↔ ∀ j, -1 < a j := by
  constructor
  · intro hG j
    have hfin := hG.2
    rw [hasFiniteIntegral_iff_enorm] at hfin
    have key : ∫⁻ w, ‖∏ j, w j ^ a j‖ₑ
        ∂(Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)) =
        ∏ j, ∫⁻ x, ‖x ^ a j‖ₑ ∂(volume.restrict (Ioo (0 : ℝ) 1)) := by
      rw [← lintegral_fin_prod (fun j x => ‖x ^ a j‖ₑ) (fun j => by fun_prop)]
      congr 1; ext w
      simp only [enorm_eq_nnnorm, nnnorm_prod, ENNReal.ofNNReal_finsetProd]
    rw [key] at hfin
    have hj : ∫⁻ x, ‖x ^ a j‖ₑ ∂(volume.restrict (Ioo (0 : ℝ) 1)) < ∞ := by
      by_contra hc
      rw [not_lt, top_le_iff] at hc
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), hc, ENNReal.top_mul] at hfin
      · exact lt_irrefl _ hfin
      · exact Finset.prod_ne_zero_iff.2 fun i _ => lintegral_enorm_rpow_ne_zero (a i)
    exact (integrable_rpow_Ioo_iff (a j)).1
      ⟨(by fun_prop : Measurable fun x : ℝ => x ^ a j).aestronglyMeasurable, hj⟩
  · intro ha
    exact Integrable.fintype_prod (f := fun j (x : ℝ) => x ^ a j)
      fun j => (integrable_rpow_Ioo_iff _).2 (ha j)

theorem integral_rpow_Ioo {a : ℝ} (ha : -1 < a) :
    ∫ x in Ioo (0 : ℝ) 1, x ^ a = 1 / (a + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl ha), Real.one_rpow, Real.zero_rpow (by linarith)]
  ring

theorem integral_prod_rpow {d : ℕ} (a : Fin d → ℝ) (ha : ∀ j, -1 < a j) :
    ∫ w, ∏ j, w j ^ a j ∂(Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)) =
      ∏ j, 1 / (a j + 1) := by
  rw [integral_fintype_prod_eq_prod (fun j (x : ℝ) => x ^ a j)]
  exact Finset.prod_congr rfl fun j _ => integral_rpow_Ioo (ha j)

end Node.NC

namespace Node

/-- The monomial (normal-crossing) zeta function: for `K(w) = ∏ⱼ wⱼ^(2kⱼ)` and the prior
density `φ(w) = ∏ⱼ wⱼ^(hⱼ)` on `[0,1]^d` (not normalized), `K^z φ` is integrable on the cube
exactly when `2kⱼ z + hⱼ + 1 > 0` for every `j` (real `z`). -/
theorem monomial_zeta_integrable {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (z : ℝ) :
    IntegrableOn (fun w : Fin d → ℝ => (∏ j, w j ^ (2 * k j)) ^ z * ∏ j, w j ^ h j)
        (Set.univ.pi fun _ => Icc (0 : ℝ) 1) ↔
      ∀ j, 0 < 2 * (k j : ℝ) * z + h j + 1 := by
  rw [IntegrableOn, NC.cube_restrict_eq, integrable_congr (NC.integrand_ae k h z),
    NC.integrable_prod_rpow_iff]
  exact forall_congr' fun j => by constructor <;> intro <;> linarith

/-- The monomial zeta function in closed form:
`∫_{[0,1]^d} K^z φ = ∏ⱼ 1/(2kⱼ z + hⱼ + 1)` whenever every factor is positive. -/
theorem monomial_zeta {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (z : ℝ)
    (hz : ∀ j, 0 < 2 * (k j : ℝ) * z + h j + 1) :
    ∫ w in Set.univ.pi (fun _ => Icc (0 : ℝ) 1), (∏ j, w j ^ (2 * k j)) ^ z * ∏ j, w j ^ h j =
      ∏ j, 1 / (2 * (k j : ℝ) * z + h j + 1) := by
  rw [NC.cube_restrict_eq, integral_congr_ae (NC.integrand_ae k h z),
    NC.integral_prod_rpow _ (fun j => by linarith [hz j])]

/-- The learning coefficient and its multiplicity for the monomial model. Let `λ` be the
smallest of the numbers `(hⱼ + 1)/(2kⱼ)` (all `kⱼ > 0`) and `m ≥ 1` the number of indices
attaining it. Then `(z + λ)^m ζ(z)` tends to a nonzero limit as `z → -λ` from above, where
`ζ(z) = ∫_{[0,1]^d} K^z φ`: the zeta function has a pole of order exactly `m` at `-λ`
(real variable, one-sided; meromorphic continuation is not stated). -/
theorem monomial_pole {d : ℕ} (k : Fin d → ℕ) (hk : ∀ j, 0 < k j) (h : Fin d → ℝ) (lam : ℝ)
    (hmin : ∀ j, lam ≤ (h j + 1) / (2 * (k j : ℝ)))
    (hattain : ∃ j, (h j + 1) / (2 * (k j : ℝ)) = lam) :
    0 < (Finset.univ.filter fun j => (h j + 1) / (2 * (k j : ℝ)) = lam).card ∧
      ∃ c : ℝ, c ≠ 0 ∧
        Tendsto (fun z : ℝ =>
            (z + lam) ^ (Finset.univ.filter fun j => (h j + 1) / (2 * (k j : ℝ)) = lam).card *
              ∫ w in Set.univ.pi (fun _ => Icc (0 : ℝ) 1),
                (∏ j, w j ^ (2 * k j)) ^ z * ∏ j, w j ^ h j)
          (𝓝[>] (-lam)) (𝓝 c) := by
  set A := Finset.univ.filter fun j => (h j + 1) / (2 * (k j : ℝ)) = lam with hA
  have hk2 : ∀ j, 0 < 2 * (k j : ℝ) := fun j => by have := hk j; positivity
  have hle : ∀ j, 2 * (k j : ℝ) * lam ≤ h j + 1 := fun j => by
    have := hmin j; rw [le_div_iff₀ (hk2 j)] at this; linarith
  have hmemA : ∀ j, j ∈ A ↔ h j + 1 = 2 * (k j : ℝ) * lam := fun j => by
    rw [hA, Finset.mem_filter, div_eq_iff (hk2 j).ne']
    simp only [Finset.mem_univ, true_and]
    constructor <;> intro e <;> linarith
  have hnotA : ∀ j, j ∉ A → 0 < 2 * (k j : ℝ) * (-lam) + h j + 1 := fun j hj => by
    rw [hmemA] at hj
    have := hle j
    have : 2 * (k j : ℝ) * lam < h j + 1 := lt_of_le_of_ne this (Ne.symm hj)
    linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨j, hj⟩ := hattain
    exact Finset.card_pos.2 ⟨j, by simp [hA, hj]⟩
  set g : ℝ → ℝ := fun z => ∏ j, if j ∈ A then 1 / (2 * (k j : ℝ)) else
      1 / (2 * (k j : ℝ) * z + h j + 1) with hg
  refine ⟨g (-lam), ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    split_ifs with hj
    · exact one_div_ne_zero (hk2 j).ne'
    · exact one_div_ne_zero (hnotA j hj).ne'
  · have hcont : Tendsto g (𝓝[>] (-lam)) (𝓝 (g (-lam))) := by
      refine (tendsto_finsetProd _ fun j _ => ?_).mono_left nhdsWithin_le_nhds
      split_ifs with hj
      · exact tendsto_const_nhds
      · have ht : Tendsto (fun z : ℝ => 2 * (k j : ℝ) * z + h j + 1) (𝓝 (-lam))
            (𝓝 (2 * (k j : ℝ) * (-lam) + h j + 1)) :=
          ((by fun_prop : Continuous fun z : ℝ => 2 * (k j : ℝ) * z + h j + 1).tendsto _)
        exact tendsto_const_nhds.div ht (hnotA j hj).ne'
    refine hcont.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : -lam < z := hz
    have hpos : ∀ j, 0 < 2 * (k j : ℝ) * z + h j + 1 := fun j => by
      have := hle j; have := hk2 j; nlinarith
    rw [monomial_zeta k h z hpos]
    have hpow : (z + lam) ^ A.card = ∏ j, if j ∈ A then (z + lam) else 1 := by
      rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
    rw [hpow, ← Finset.prod_mul_distrib, hg]
    refine Finset.prod_congr rfl fun j _ => ?_
    split_ifs with hj
    · rw [show 2 * (k j : ℝ) * z + h j + 1 = 2 * (k j : ℝ) * (z + lam) by
        rw [hmemA] at hj; linarith]
      have : z + lam ≠ 0 := by linarith
      have := (hk2 j).ne'
      field_simp
    · ring

end Node
