module

public import SemiHamiltonian.Geometry.SymmetryTransport

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Smooth.Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}
  (b : Frame U)

noncomputable def diagonalEndomorphism (w : ι → Functions U) : Endomorphism U :=
  b.equivFun.symm.toLinearMap.comp ((PSS.FrameData.diagonalMap w).comp b.equivFun.toLinearMap)

omit [DecidableEq ι] in
theorem diagonalEndomorphism_coordinates (w : ι → Functions U) (X : Fields U) :
    b.equivFun (b.diagonalEndomorphism w X) = PSS.FrameData.applyDiagonal w (b.equivFun X) :=
  b.equivFun.apply_symm_apply _

theorem diagonalEndomorphism_eigen (w : ι → Functions U) (i : ι) :
    b.diagonalEndomorphism w (b i) = w i • b i := by
  apply b.equivFun.injective
  rw [diagonalEndomorphism_coordinates, map_smul]
  funext r
  by_cases h : r = i
  · subst r; simp [PSS.FrameData.applyDiagonal]
  · simp [PSS.FrameData.applyDiagonal, h, Ne.symm h]

theorem commute_diagonalEndomorphism (A : Endomorphism U) (v w : ι → Functions U)
    (heigen : ∀ i, A (b i) = v i • b i) :
    Function.Commute A (b.diagonalEndomorphism w) := by
  intro X
  apply b.equivFun.injective
  rw [endomorphism_coordinates b A v heigen, diagonalEndomorphism_coordinates,
    diagonalEndomorphism_coordinates, endomorphism_coordinates b A v heigen]
  funext r
  simp only [PSS.FrameData.applyDiagonal]
  ring

/-- Simple spectrum makes every commuting smooth endomorphism diagonal in the eigenframe. -/
theorem eigen_of_commute (A B : Endomorphism U) (v : ι → Functions U)
    (heigen : ∀ i, A (b i) = v i • b i)
    (hgap : ∀ i j, i ≠ j → IsUnit (v i - v j)) (hc : Function.Commute A B) :
    ∀ i, B (b i) = b.equivFun (B (b i)) i • b i := by
  intro i
  apply b.equivFun.injective
  funext r
  by_cases hri : r = i
  · subst r; simp
  have hh := congrArg (fun X => b.equivFun X r) (hc (b i))
  rw [endomorphism_coordinates b A v heigen, heigen, map_smul, map_smul] at hh
  change v r * b.equivFun (B (b i)) r = v i * b.equivFun (B (b i)) r at hh
  have hz : (v r - v i) * b.equivFun (B (b i)) r = 0 := by
    rw [sub_mul, hh, sub_self]
  have hz' : b.equivFun (B (b i)) r = 0 :=
    (hgap r i hri).mul_left_cancel (by simpa only [mul_zero] using hz)
  simp [hz', hri]

theorem symmetry_coordinates (hU : IsOpen U) (A B : Endomorphism U)
    (v w : ι → Functions U) (hA : ∀ i, A (b i) = v i • b i)
    (hB : ∀ i, B (b i) = w i • b i) (hs : IsHydrodynamicSymmetry hU A B) :
    (b.data hU).IsHydrodynamicSymmetry v w := by
  intro X Y r
  have hh := congrArg (fun Z => b.equivFun Z r)
    (hs.2 (b.equivFun.symm X) (b.equivFun.symm Y))
  simpa only [PSS.polarized, map_add, map_sub, Pi.add_apply, Pi.sub_apply,
    endomorphism_coordinates b A v hA, endomorphism_coordinates b B w hB,
    bracket_coordinates, b.equivFun.apply_symm_apply, map_zero, Pi.zero_apply,
    PSS.FrameData.polarizedSymmetry, PSS.FrameData.applyDiagonal] using hh

end SemiHamiltonian.Smooth.Frame
