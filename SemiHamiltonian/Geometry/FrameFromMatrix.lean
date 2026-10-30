module

public import SemiHamiltonian.Geometry.MatrixField

/-! A smooth pointwise invertible matrix defines a basis of smooth sections. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}

theorem inverse_matrix_smooth {S : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hS : ContDiffOn ℝ ∞ S U) (hi : ∀ q ∈ U, (S q).IsInvertible) :
    ContDiffOn ℝ ∞ (fun q => (S q).inverse) U := by
  intro q hq
  exact (hi q hq).contDiffAt_map_inverse.comp_contDiffWithinAt q (hS q hq)

noncomputable def frameEquivOfMatrix (S : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hS : ContDiffOn ℝ ∞ S U) (hi : ∀ q ∈ U, (S q).IsInvertible) :
    Fields U ≃ₗ[Functions U] Fields U := by
  let T := Endomorphism.ofField S hS
  let R := Endomorphism.ofField (fun q => (S q).inverse) (inverse_matrix_smooth hS hi)
  have hl : R.comp T = LinearMap.id := by
    apply LinearMap.ext
    intro X
    funext k
    apply Subtype.ext
    funext x
    have hh : field (Endomorphism.ofField (fun q => (S q).inverse)
        (inverse_matrix_smooth hS hi) (Endomorphism.ofField S hS X)) x = field X x := by
      rw [Endomorphism.field_ofField, Endomorphism.field_ofField,
        (hi x x.property).inverse_apply_self]
    simpa only [T, R, LinearMap.comp_apply, LinearMap.id_apply, field_apply] using congrFun hh k
  have hr : T.comp R = LinearMap.id := by
    apply LinearMap.ext
    intro X
    funext k
    apply Subtype.ext
    funext x
    have hh : field (Endomorphism.ofField S hS (Endomorphism.ofField
        (fun q => (S q).inverse) (inverse_matrix_smooth hS hi) X)) x = field X x := by
      rw [Endomorphism.field_ofField, Endomorphism.field_ofField,
        (hi x x.property).self_apply_inverse]
    simpa only [T, R, LinearMap.comp_apply, LinearMap.id_apply, field_apply] using congrFun hh k
  exact LinearEquiv.ofLinearMap T R hr hl

noncomputable def frameOfMatrix (S : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hS : ContDiffOn ℝ ∞ S U) (hi : ∀ q ∈ U, (S q).IsInvertible) : Frame U :=
  Module.Basis.ofEquivFun (frameEquivOfMatrix S hS hi).symm

theorem frameOfMatrix_field (S : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hS : ContDiffOn ℝ ∞ S U) (hi : ∀ q ∈ U, (S q).IsInvertible) (i : ι) (x : U) :
    field (frameOfMatrix S hS hi i) x = S x (Pi.single i 1) := by
  have hb : frameOfMatrix S hS hi i =
      Endomorphism.ofField S hS (standardField i) := by
    rw [frameOfMatrix, Module.Basis.coe_ofEquivFun]
    simp only [LinearEquiv.symm_symm]
    rfl
  rw [hb, Endomorphism.field_ofField]
  congr 1
  ext k
  simp only [field_apply, standardField, Pi.single_apply]
  split_ifs <;> rfl

end SemiHamiltonian.Smooth
