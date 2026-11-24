module

public import Legendre.Solutions

@[expose] public section

/-!
# Local monodromy at `λ = 0`

The logarithmic solution `L = F log + G` continues holomorphically across the cut
`(-1, 0)`: the function `g λ = F λ (log (-λ) + iπ) + G λ`, which uses the branch of the
logarithm with argument in `(0, 2π)`, is holomorphic on the unit disc slit along `[0, 1)`,
agrees with `L` on the upper half-disc and with `L + 2πi F` on the lower half-disc.
Since `F` is holomorphic on the whole disc, the local monodromy at `0` in the basis
`(F, L)` is `[[1, 2πi], [0, 1]]`.
-/

open Complex

namespace Legendre

/-- The continuation of `L` across the negative real axis. -/
noncomputable def Lcont (z : ℂ) : ℂ := F z * (Complex.log (-z) + Real.pi * I) + G z

lemma log_neg_add_pi_I_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) + Real.pi * I = Complex.log z := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, arg_neg_eq_arg_sub_pi_of_im_pos hz]

lemma log_neg_add_pi_I_of_im_neg {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) + Real.pi * I = Complex.log z + 2 * Real.pi * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, arg_neg_eq_arg_add_pi_of_im_neg hz]
    ring

lemma Lcont_differentiableOn :
    DifferentiableOn ℂ Lcont (Metric.ball 0 1 \ {z : ℂ | 0 ≤ z.re ∧ z.im = 0}) := by
  intro z hz
  obtain ⟨hzb, hzc⟩ := hz
  have hslit : -z ∈ slitPlane := by
    simp only [Set.mem_ofPred_eq, not_and_or, not_le] at hzc
    rcases hzc with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
  have hF : DifferentiableAt ℂ F z :=
    (F_differentiableOn z hzb).differentiableAt (Metric.isOpen_ball.mem_nhds hzb)
  have hG : DifferentiableAt ℂ G z :=
    (G_differentiableOn z hzb).differentiableAt (Metric.isOpen_ball.mem_nhds hzb)
  have hlog : DifferentiableAt ℂ (fun w : ℂ => Complex.log (-w)) z :=
    (differentiableAt_log hslit).comp z differentiableAt_id.neg
  exact ((hF.mul (hlog.add_const _)).add hG).differentiableWithinAt

theorem monodromy :
    ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (Metric.ball 0 1 \ {z : ℂ | 0 ≤ z.re ∧ z.im = 0}) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < z.im → g z = L z) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, z.im < 0 → g z = L z + 2 * Real.pi * I * F z) := by
  refine ⟨Lcont, Lcont_differentiableOn, fun z _ hz => ?_, fun z _ hz => ?_⟩
  · simp only [Lcont, L, log_neg_add_pi_I_of_im_pos hz]
  · simp only [Lcont, L, log_neg_add_pi_I_of_im_neg hz]
    ring

end Legendre
