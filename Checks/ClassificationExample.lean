module

import SemiHamiltonian

/-! A coupled system with genuine, freely prescribed smooth axis germs. -/

open scoped Topology ContDiff Classical
open Set Filter SemiHamiltonian SemiHamiltonian.Smooth

namespace ClassificationCheck

abbrev E := Fin 2 → ℝ
abbrev U : Set E := univ

noncomputable def v (i : Fin 2) : Functions U :=
  ofContDiffOn (fun x => x 0 + x 1 + (i.val : ℝ))
    (((contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 0).add
      (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 1)).add contDiff_const).contDiffOn

theorem separated : StrictlyHyperbolic v := by
  intro x i j hij hh
  change (x : E) 0 + (x : E) 1 + (i.val : ℝ) = (x : E) 0 + (x : E) 1 + (j.val : ℝ) at hh
  exact hij (Fin.ext (by exact_mod_cast add_left_cancel hh))

noncomputable def S : System (ι := Fin 2) (U := U) isOpen_univ :=
  ofSpeeds isOpen_univ v separated

theorem semiHamiltonian : S.IsSemiHamiltonian := by
  intro i j k hij hik hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

def p : U := ⟨0, mem_univ _⟩

noncomputable def data : Fin 2 → ScalarGerm 0 := fun i =>
  if i = 0 then ⟨(Real.sin : Germ (𝓝 (0 : ℝ)) ℝ), Real.sin, Real.contDiff_sin, rfl⟩
  else ⟨(Real.exp : Germ (𝓝 (0 : ℝ)) ℝ), Real.exp, Real.contDiff_exp, rfl⟩

example : ∃! g : CommutingSpeedGerm isOpen_univ S p,
    commutingSpeedAxisGerms isOpen_univ S p g = data := by
  let e := commutingSpeedGermEquiv isOpen_univ S p semiHamiltonian
  exact ⟨e.symm data, e.apply_symm_apply data,
    fun g hg => e.injective (hg.trans (e.apply_symm_apply data).symm)⟩

-- The same classification covers all invariant operators, without requiring
-- the symmetry itself to have a simple spectrum.
noncomputable example : HydrodynamicSymmetryGerm isOpen_univ S p ≃ (Fin 2 → ScalarGerm 0) :=
  hydrodynamicSymmetryGermEquiv isOpen_univ S p semiHamiltonian

example : S.IsCommutingSpeed (fun _ => 1) := S.one_isCommutingSpeed

-- Density data carry one additional, independent normalization constant.
noncomputable example : DensityGerm isOpen_univ S p ≃ (ℝ × (Fin 2 → ScalarGerm 0)) :=
  densityGermEquiv isOpen_univ S p semiHamiltonian

example : ∃! g : DensityGerm isOpen_univ S p,
    densityGermEquiv isOpen_univ S p semiHamiltonian g = (7, data) := by
  let e := densityGermEquiv isOpen_univ S p semiHamiltonian
  exact ⟨e.symm (7, data), e.apply_symm_apply (7, data),
    fun g hg => e.injective (hg.trans (e.apply_symm_apply (7, data)).symm)⟩

-- A representative singular away from the base point is admissible: the
-- scalar-germ definition does not require this representative to be global.
example : ∃ g : ScalarGerm (0 : ℝ),
    g.val = ((fun s : ℝ => (1 - s)⁻¹) : Germ (𝓝 (0 : ℝ)) ℝ) := by
  have hf : ContDiffOn ℝ ∞ (fun s : ℝ => (1 - s)⁻¹) (Iio (1 / 2 : ℝ)) := by
    apply (contDiffOn_const.sub contDiffOn_id).inv
    intro s hs
    have hs' : s < 1 / 2 := hs
    change 1 - s ≠ 0
    linarith
  obtain ⟨f, hf, he⟩ := exists_global_smooth_germ isOpen_Iio (by norm_num : (0 : ℝ) ∈ Iio (1 / 2 : ℝ)) hf
  exact ⟨⟨(f : Germ (𝓝 (0 : ℝ)) ℝ), f, hf, rfl⟩, he.germ_eq⟩

end ClassificationCheck
