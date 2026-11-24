module

public import Node.FreeEnergyStep
public import Node.NormalCrossing

@[expose] public section

/-!
# Auxiliary facts for the monomial partition function

The partition function `Zf k h n = ∫_{(0,1)^d} exp(-n ∏ wⱼ^(2kⱼ)) ∏ wⱼ^(hⱼ) dw` is integrable,
positive, antitone and continuous in `n`, and splitting off the first coordinate gives
`Zf k h n = ∫₀¹ t^(h₀) Zf k' h' (n t^(2k₀)) dt` (`Zf_succ`).
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Node.FEM

/-- The cube measure `(volume on (0,1))^d`. -/
noncomputable abbrev cube (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)

/-- The partition function of the monomial model on the open cube. -/
noncomputable def Zf {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (n : ℝ) : ℝ :=
  ∫ w, Real.exp (-n * ∏ j, w j ^ (2 * k j)) * ∏ j, w j ^ h j ∂(cube d)

theorem K_mem {d : ℕ} (k : Fin d → ℕ) (w : Fin d → ℝ) (hw : ∀ j, 0 < w j ∧ w j < 1) :
    0 ≤ ∏ j, w j ^ (2 * k j) ∧ ∏ j, w j ^ (2 * k j) ≤ 1 := by
  refine ⟨Finset.prod_nonneg fun j _ => pow_nonneg (hw j).1.le _, ?_⟩
  exact Finset.prod_le_one₀ (fun j _ => pow_nonneg (hw j).1.le _)
    fun j _ => pow_le_one₀ (hw j).1.le (hw j).2.le

theorem ae_cube' (d : ℕ) : ∀ᵐ w ∂(cube d), ∀ j, 0 < w j ∧ w j < 1 := by
  unfold cube
  rw [← Measure.restrict_pi_pi (μ := fun _ : Fin d => (volume : Measure ℝ))
    (fun _ => Ioo (0 : ℝ) 1)]
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)] with w hw
  intro j
  exact hw j (mem_univ j)

theorem integrable_phi {d : ℕ} (h : Fin d → ℝ) (hh : ∀ j, -1 < h j) :
    Integrable (fun w : Fin d → ℝ => ∏ j, w j ^ h j) (cube d) :=
  (NC.integrable_prod_rpow_iff h).2 hh

theorem integrand_bound {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (n : ℝ) :
    ∀ᵐ w ∂(cube d), ‖Real.exp (-n * ∏ j, w j ^ (2 * k j)) * ∏ j, w j ^ h j‖ ≤
      Real.exp |n| * ∏ j, w j ^ h j := by
  filter_upwards [ae_cube' d] with w hw
  obtain ⟨h0, h1⟩ := K_mem k w hw
  have hp : 0 ≤ ∏ j, w j ^ h j := Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hw j).1.le _
  rw [norm_mul, Real.norm_eq_abs, Real.abs_exp, Real.norm_eq_abs, abs_of_nonneg hp]
  gcongr
  calc -n * ∏ j, w j ^ (2 * k j) ≤ |n| * ∏ j, w j ^ (2 * k j) := by
        gcongr; exact neg_le_abs n
    _ ≤ |n| * 1 := by gcongr
    _ = |n| := mul_one _

theorem measurable_integrand {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (n : ℝ) :
    Measurable fun w : Fin d → ℝ => Real.exp (-n * ∏ j, w j ^ (2 * k j)) * ∏ j, w j ^ h j := by
  fun_prop

theorem integrable_integrand {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (hh : ∀ j, -1 < h j)
    (n : ℝ) :
    Integrable (fun w : Fin d → ℝ => Real.exp (-n * ∏ j, w j ^ (2 * k j)) * ∏ j, w j ^ h j)
      (cube d) :=
  Integrable.mono' ((integrable_phi h hh).const_mul _)
    (measurable_integrand k h n).aestronglyMeasurable (integrand_bound k h n)

theorem Zf_pos {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (hh : ∀ j, -1 < h j) (n : ℝ) :
    0 < Zf k h n := by
  have hle : ∫ w, Real.exp (-|n|) * ∏ j, w j ^ h j ∂(cube d) ≤ Zf k h n := by
    refine integral_mono_ae ((integrable_phi h hh).const_mul _)
      (integrable_integrand k h hh n) ?_
    filter_upwards [ae_cube' d] with w hw
    obtain ⟨h0, h1⟩ := K_mem k w hw
    have hp : 0 ≤ ∏ j, w j ^ h j :=
      Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hw j).1.le _
    gcongr
    calc -|n| = -|n| * 1 := (mul_one _).symm
      _ ≤ -|n| * ∏ j, w j ^ (2 * k j) := by
        exact mul_le_mul_of_nonpos_left h1 (neg_nonpos.2 (abs_nonneg n))
      _ ≤ -n * ∏ j, w j ^ (2 * k j) := by gcongr; exact le_abs_self n
  refine lt_of_lt_of_le ?_ hle
  rw [integral_const_mul, NC.integral_prod_rpow h hh]
  refine mul_pos (Real.exp_pos _) (Finset.prod_pos fun j _ => ?_)
  have := hh j
  exact one_div_pos.2 (by linarith)

theorem Zf_anti {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (hh : ∀ j, -1 < h j) :
    Antitone (Zf k h) := by
  intro x y hxy
  refine integral_mono_ae (integrable_integrand k h hh y) (integrable_integrand k h hh x) ?_
  filter_upwards [ae_cube' d] with w hw
  obtain ⟨h0, h1⟩ := K_mem k w hw
  have hp : 0 ≤ ∏ j, w j ^ h j := Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hw j).1.le _
  gcongr

theorem Zf_cont {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (hh : ∀ j, -1 < h j) :
    Continuous (Zf k h) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  refine continuousAt_of_dominated (bound := fun w => Real.exp (|x₀| + 1) * ∏ j, w j ^ h j)
    (Eventually.of_forall fun n => (measurable_integrand k h n).aestronglyMeasurable) ?_
    ((integrable_phi h hh).const_mul _) (Eventually.of_forall fun w => by fun_prop)
  filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with n hn
  filter_upwards [integrand_bound k h n, ae_cube' d] with w hw hw'
  have hp : 0 ≤ ∏ j, w j ^ h j := Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hw' j).1.le _
  refine hw.trans ?_
  gcongr
  rw [Metric.mem_ball, Real.dist_eq] at hn
  calc |n| = |(n - x₀) + x₀| := by ring_nf
    _ ≤ |n - x₀| + |x₀| := abs_add_le _ _
    _ ≤ |x₀| + 1 := by linarith

theorem Zf_succ {d : ℕ} (k : Fin (d + 1) → ℕ) (h : Fin (d + 1) → ℝ) (hh : ∀ j, -1 < h j)
    (n : ℝ) :
    Zf k h n = ∫ t in Ioc (0 : ℝ) 1,
      t ^ h 0 * Zf (fun j => k j.succ) (fun j => h j.succ) (n * t ^ (2 * k 0)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have hmp : MeasurePreserving e (cube (d + 1)) ((volume.restrict (Ioo (0 : ℝ) 1)).prod (cube d)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => volume.restrict (Ioo (0 : ℝ) 1)) 0
  set F : ℝ × (Fin d → ℝ) → ℝ := fun p => p.1 ^ h 0 *
    (Real.exp (-(n * p.1 ^ (2 * k 0)) * ∏ j, p.2 j ^ (2 * k j.succ)) * ∏ j, p.2 j ^ h j.succ)
    with hFdef
  have hF : (fun w : Fin (d + 1) → ℝ => Real.exp (-n * ∏ j, w j ^ (2 * k j)) * ∏ j, w j ^ h j)
      = fun w => F (e w) := by
    funext w
    simp only [hFdef, e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_symm_mk, Fin.prod_univ_succ, Fin.removeNth_zero, Fin.tail]
    ring_nf
  have hFi : Integrable F ((volume.restrict (Ioo (0 : ℝ) 1)).prod (cube d)) := by
    rw [← hmp.integrable_comp_emb e.measurableEmbedding]
    have := integrable_integrand k h hh n
    rw [hF] at this
    exact this
  unfold Zf
  rw [hF, hmp.integral_comp' F, integral_prod F hFi, integral_Ioc_eq_integral_Ioo]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [hFdef]
  rw [integral_const_mul]

theorem Zf_zero (k : Fin 0 → ℕ) (h : Fin 0 → ℝ) (n : ℝ) : Zf k h n = Real.exp (-n) := by
  unfold Zf cube
  rw [Measure.pi_of_empty, integral_dirac]
  simp

theorem a_pos {d : ℕ} (k : Fin d → ℕ) (hk : ∀ j, 0 < k j) (h : Fin d → ℝ) (hh : ∀ j, -1 < h j)
    (j : Fin d) : 0 < (h j + 1) / (2 * (k j : ℝ)) := by
  have := hk j
  have := hh j
  exact div_pos (by linarith) (by positivity)

/-- The asymptotics of `Zf` in dimension `d + 1`, by induction on `d`. -/
theorem Zf_theta (d : ℕ) : ∀ (k : Fin (d + 1) → ℕ) (_hk : ∀ j, 0 < k j)
    (h : Fin (d + 1) → ℝ) (_hh : ∀ j, -1 < h j) (lam : ℝ)
    (_hmin : ∀ j, lam ≤ (h j + 1) / (2 * (k j : ℝ)))
    (_hattain : ∃ j, (h j + 1) / (2 * (k j : ℝ)) = lam),
    Zf k h =Θ[atTop] fun n : ℝ => n ^ (-lam) *
      Real.log n ^ ((Finset.univ.filter fun j => (h j + 1) / (2 * (k j : ℝ)) = lam).card - 1) := by
  induction d with
  | zero =>
    intro k hk h hh lam hmin hattain
    have hlam : lam = (h 0 + 1) / (2 * (k 0 : ℝ)) := by
      obtain ⟨j, hj⟩ := hattain
      rw [show j = 0 from Fin.ext (by have := j.isLt; omega)] at hj
      exact hj.symm
    have hcard : (Finset.univ.filter fun j : Fin 1 => (h j + 1) / (2 * (k j : ℝ)) = lam).card
        = 1 := by
      rw [Finset.filter_true_of_mem fun j _ => by
        rw [show j = 0 from Fin.ext (by have := j.isLt; omega), hlam]]
      rfl
    have hZ : Zf k h = fun n => ∫ t in Ioc (0 : ℝ) 1, t ^ h 0 * Real.exp (-n * t ^ (2 * k 0)) := by
      funext n
      rw [Zf_succ k h hh]
      simp only [Zf_zero, neg_mul]
    rw [hZ, hcard, hlam]
    simpa using base_theta (k 0) (hk 0) (h 0) (hh 0)
  | succ d ih =>
    intro k hk h hh lam hmin hattain
    obtain ⟨j₀, hj₀⟩ := Finite.exists_min fun j : Fin (d + 1) =>
      (h j.succ + 1) / (2 * (k j.succ : ℝ))
    obtain ⟨μ, hμ⟩ : ∃ μ, μ = (h j₀.succ + 1) / (2 * (k j₀.succ : ℝ)) := ⟨_, rfl⟩
    have hμmin : ∀ j : Fin (d + 1), μ ≤ (h j.succ + 1) / (2 * (k j.succ : ℝ)) :=
      fun j => hμ ▸ hj₀ j
    have IH := ih (fun j => k j.succ) (fun j => hk _) (fun j => h j.succ) (fun j => hh _) μ
      hμmin ⟨j₀, hμ.symm⟩
    obtain ⟨M, hM⟩ : ∃ M, M = (Finset.univ.filter fun j : Fin (d + 1) =>
        (h j.succ + 1) / (2 * (k j.succ : ℝ)) = μ).card := ⟨_, rfl⟩
    rw [← hM] at IH
    have hM1 : 1 ≤ M := by
      rw [hM]
      exact Finset.card_pos.2 ⟨j₀, by simp [hμ]⟩
    have hμpos : 0 < μ := hμ ▸ a_pos k hk h hh _
    have S := step_theta (k 0) (hk 0) (h 0) (hh 0) μ hμpos (M - 1)
      (Zf (fun j => k j.succ) (fun j => h j.succ)) (Zf_cont _ _ fun j => hh _)
      (Zf_pos _ _ fun j => hh _) (Zf_anti _ _ fun j => hh _) IH
    have hZ : Zf k h = fun n => ∫ t in Ioc (0 : ℝ) 1,
        t ^ h 0 * Zf (fun j => k j.succ) (fun j => h j.succ) (n * t ^ (2 * k 0)) :=
      funext (Zf_succ k h hh)
    rw [hZ, Fin.card_filter_univ_succ]
    rcases lt_trichotomy ((h 0 + 1) / (2 * (k 0 : ℝ))) μ with hlt | heq | hgt
    · have hlam : lam = (h 0 + 1) / (2 * (k 0 : ℝ)) := by
        obtain ⟨j, hj⟩ := hattain
        refine Fin.cases (fun hj => hj.symm) (fun j hj => ?_) j hj
        have := hmin 0
        have := hμmin j
        linarith
      subst hlam
      have hempty : (Finset.univ.filter fun j : Fin (d + 1) =>
          (h j.succ + 1) / (2 * (k j.succ : ℝ)) = (h 0 + 1) / (2 * (k 0 : ℝ))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _ hj
        have := hμmin j
        linarith
      simp only [hlt, ↓reduceIte] at S
      simpa [hempty] using S
    · have hlam : lam = μ := by
        obtain ⟨j, hj⟩ := hattain
        have h1 : lam ≤ μ := hμ ▸ hmin j₀.succ
        refine Fin.cases (fun hj => ?_) (fun j hj => ?_) j hj
        · linarith
        · have := hμmin j
          linarith
      subst hlam
      simp only [lt_irrefl, heq, ↓reduceIte] at S ⊢
      rw [Nat.add_sub_cancel, ← hM]
      rw [Nat.sub_add_cancel hM1] at S
      exact S
    · have hlam : lam = μ := by
        obtain ⟨j, hj⟩ := hattain
        have h1 : lam ≤ μ := hμ ▸ hmin j₀.succ
        refine Fin.cases (fun hj => ?_) (fun j hj => ?_) j hj
        · linarith
        · have := hμmin j
          linarith
      subst hlam
      simp only [not_lt.2 hgt.le, hgt.ne', ↓reduceIte] at S ⊢
      rw [← hM]
      exact S

end Node.FEM
