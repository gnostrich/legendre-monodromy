module

public import Legendre.Solutions
public import Legendre.Uniqueness

@[expose] public section

/-!
# The solution space on a connected open subset of the slit disc

For an open, preconnected, nonempty `U ⊆ D`, the holomorphic solutions of the
Picard–Fuchs equation on `U` are exactly the combinations `a F + b L`, and `F`, `L` are
linearly independent on `U`. The proof matches the Cauchy data at a point `z₀ ∈ U`,
using that the Wronskian `F L' - F' L = 1/(z₀(1-z₀))` does not vanish, and then applies
`eqOn_zero_of_legendreOp`.

Interface theorems (signatures fixed): `solution_space_on`, `basis_independent_on`.
-/

open Complex Filter Topology

namespace Legendre

lemma ne_one_of_mem_D {z : ℂ} (hz : z ∈ D) : z ≠ 1 := by
  rintro rfl
  have := hz.1
  simp at this

/-- `legendreOp` only depends on the germ of the function. -/
lemma legendreOp_congr {y₁ y₂ : ℂ → ℂ} {z : ℂ} (h : y₁ =ᶠ[𝓝 z] y₂) :
    legendreOp y₁ z = legendreOp y₂ z := by
  simp only [legendreOp, h.deriv.deriv_eq, h.deriv_eq, h.eq_of_nhds]

/-- `legendreOp` is linear on holomorphic functions on an open set. -/
lemma legendreOp_add_smul {U : Set ℂ} (hU : IsOpen U) {y₁ y₂ : ℂ → ℂ}
    (h₁ : DifferentiableOn ℂ y₁ U) (h₂ : DifferentiableOn ℂ y₂ U) (c : ℂ) {z : ℂ}
    (hz : z ∈ U) :
    legendreOp (fun w => y₁ w + c * y₂ w) z = legendreOp y₁ z + c * legendreOp y₂ z := by
  have hd : ∀ w ∈ U, deriv (fun w => y₁ w + c * y₂ w) w = deriv y₁ w + c * deriv y₂ w := by
    intro w hw
    have d₁ := (h₁ w hw).differentiableAt (hU.mem_nhds hw)
    have d₂ := (h₂ w hw).differentiableAt (hU.mem_nhds hw)
    rw [deriv_fun_add d₁ (d₂.const_mul c), deriv_const_mul _ d₂]
  have hev : deriv (fun w => y₁ w + c * y₂ w) =ᶠ[𝓝 z] fun w => deriv y₁ w + c * deriv y₂ w :=
    eventually_of_mem (hU.mem_nhds hz) hd
  have e₁ := ((h₁.deriv hU) z hz).differentiableAt (hU.mem_nhds hz)
  have e₂ := ((h₂.deriv hU) z hz).differentiableAt (hU.mem_nhds hz)
  have h2 : deriv (deriv (fun w => y₁ w + c * y₂ w)) z =
      deriv (deriv y₁) z + c * deriv (deriv y₂) z := by
    rw [hev.deriv_eq, deriv_fun_add e₁ (e₂.const_mul c), deriv_const_mul _ e₂]
  simp only [legendreOp, h2, hd z hz]
  ring

lemma F_differentiableOn_D : DifferentiableOn ℂ F D :=
  F_differentiableOn.mono Set.inter_subset_left

lemma F_solves_D {z : ℂ} (hz : z ∈ D) : legendreOp F z = 0 := F_solves hz.1

/-- The combination `a F + b L` solves the equation on `D`. -/
lemma comb_solves {a b : ℂ} {z : ℂ} (hz : z ∈ D) :
    legendreOp (fun w => a * F w + b * L w) z = 0 := by
  have hFa : DifferentiableOn ℂ (fun w => a * F w) D := F_differentiableOn_D.const_mul a
  have h := legendreOp_add_smul D_isOpen hFa L_differentiableOn b hz
  have h' := legendreOp_add_smul D_isOpen (y₁ := fun _ => (0 : ℂ)) (differentiableOn_const 0)
    F_differentiableOn_D a hz
  simp only [zero_add] at h'
  rw [h, h', L_solves hz, F_solves_D hz]
  simp [legendreOp]

lemma comb_differentiableOn (a b : ℂ) : DifferentiableOn ℂ (fun w => a * F w + b * L w) D :=
  (F_differentiableOn_D.const_mul a).add (L_differentiableOn.const_mul b)

lemma deriv_comb {a b : ℂ} {z : ℂ} (hz : z ∈ D) :
    deriv (fun w => a * F w + b * L w) z = a * deriv F z + b * deriv L z := by
  have dF := (F_differentiableOn_D z hz).differentiableAt (D_isOpen.mem_nhds hz)
  have dL := (L_differentiableOn z hz).differentiableAt (D_isOpen.mem_nhds hz)
  rw [deriv_fun_add (dF.const_mul a) (dL.const_mul b), deriv_const_mul _ dF,
    deriv_const_mul _ dL]

lemma wronskian_ne_zero {z : ℂ} (hz : z ∈ D) : F z * deriv L z - deriv F z * L z ≠ 0 := by
  rw [wronskian hz]
  have h0 := ne_zero_of_mem_D hz
  have h1 : 1 - z ≠ 0 := sub_ne_zero.mpr (ne_one_of_mem_D hz).symm
  exact one_div_ne_zero (mul_ne_zero h0 h1)

theorem solution_space_on {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) (hUD : U ⊆ D)
    (hne : U.Nonempty) (y : ℂ → ℂ) :
    (DifferentiableOn ℂ y U ∧ ∀ z ∈ U, legendreOp y z = 0) ↔
      ∃ a b : ℂ, ∀ z ∈ U, y z = a * F z + b * L z := by
  constructor
  · rintro ⟨hy, hode⟩
    obtain ⟨z₀, hz₀⟩ := hne
    have hz₀D := hUD hz₀
    set W := F z₀ * deriv L z₀ - deriv F z₀ * L z₀ with hW
    have hW0 : W ≠ 0 := wronskian_ne_zero hz₀D
    set a := (y z₀ * deriv L z₀ - deriv y z₀ * L z₀) / W
    set b := (F z₀ * deriv y z₀ - deriv F z₀ * y z₀) / W
    refine ⟨a, b, ?_⟩
    -- the difference `e = y - (a F + b L)` has zero Cauchy data at `z₀`
    have hcomb : DifferentiableOn ℂ (fun w => a * F w + b * L w) U :=
      (comb_differentiableOn a b).mono hUD
    have he : DifferentiableOn ℂ (fun w => y w + (-1) * (a * F w + b * L w)) U :=
      hy.add (hcomb.const_mul (-1))
    have hode_e : ∀ z ∈ U, legendreOp (fun w => y w + (-1) * (a * F w + b * L w)) z = 0 := by
      intro z hz
      rw [legendreOp_add_smul hU hy hcomb (-1) hz, hode z hz,
        legendreOp_congr (y₁ := fun w => a * F w + b * L w) (EventuallyEq.refl _ _),
        comb_solves (hUD hz)]
      ring
    have h0 : y z₀ + (-1) * (a * F z₀ + b * L z₀) = 0 := by
      simp only [a, b]
      field_simp
      ring
    have h1 : deriv (fun w => y w + (-1) * (a * F w + b * L w)) z₀ = 0 := by
      have dy := (hy z₀ hz₀).differentiableAt (hU.mem_nhds hz₀)
      have dc := (hcomb z₀ hz₀).differentiableAt (hU.mem_nhds hz₀)
      rw [deriv_fun_add dy (dc.const_mul (-1)), deriv_const_mul _ dc, deriv_comb hz₀D]
      simp only [a, b]
      field_simp
      ring
    have hzero := eqOn_zero_of_legendreOp hU hUc he hode_e hz₀ (ne_zero_of_mem_D hz₀D)
      (ne_one_of_mem_D hz₀D) h0 h1
    intro z hz
    have := hzero z hz
    linear_combination this
  · rintro ⟨a, b, hab⟩
    have hev : ∀ z ∈ U, y =ᶠ[𝓝 z] fun w => a * F w + b * L w := fun z hz =>
      eventually_of_mem (hU.mem_nhds hz) hab
    refine ⟨?_, fun z hz => ?_⟩
    · exact ((comb_differentiableOn a b).mono hUD).congr hab
    · rw [legendreOp_congr (hev z hz), comb_solves (hUD hz)]

theorem basis_independent_on {U : Set ℂ} (hU : IsOpen U) (hUD : U ⊆ D) (hne : U.Nonempty)
    (a b : ℂ) (h : ∀ z ∈ U, a * F z + b * L z = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hz₀D := hUD hz₀
  have hW0 := wronskian_ne_zero hz₀D
  have h0 := h z₀ hz₀
  have hev : (fun w => a * F w + b * L w) =ᶠ[𝓝 z₀] fun _ => (0 : ℂ) :=
    eventually_of_mem (hU.mem_nhds hz₀) h
  have h1 : a * deriv F z₀ + b * deriv L z₀ = 0 := by
    rw [← deriv_comb hz₀D, hev.deriv_eq]
    simp
  constructor
  · have : a * (F z₀ * deriv L z₀ - deriv F z₀ * L z₀) = 0 := by
      linear_combination deriv L z₀ * h0 - L z₀ * h1
    exact (mul_eq_zero.mp this).resolve_right hW0
  · have : b * (F z₀ * deriv L z₀ - deriv F z₀ * L z₀) = 0 := by
      linear_combination F z₀ * h1 - deriv F z₀ * h0
    exact (mul_eq_zero.mp this).resolve_right hW0

/-- The solution space on the whole slit disc. -/
theorem solution_space (y : ℂ → ℂ) :
    (DifferentiableOn ℂ y D ∧ ∀ z ∈ D, legendreOp y z = 0) ↔
      ∃ a b : ℂ, ∀ z ∈ D, y z = a * F z + b * L z :=
  solution_space_on D_isOpen D_isPreconnected subset_rfl
    ⟨1 / 2, by simp [D, slitPlane]; norm_num⟩ y

theorem basis_independent (a b : ℂ) (h : ∀ z ∈ D, a * F z + b * L z = 0) : a = 0 ∧ b = 0 :=
  basis_independent_on D_isOpen subset_rfl ⟨1 / 2, by simp [D, slitPlane]; norm_num⟩ a b h

end Legendre
