module

public import SemiHamiltonian.Geometry.FrameFrobenius
public import SemiHamiltonian.Geometry.MatrixField

/-! Haantjes local coordinates in a smooth eigenframe. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Smooth.Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}

theorem dual_eigen (b : Frame U) (A : Endomorphism U) (v : ι → Functions U)
    (heigen : ∀ i, A (b i) = v i • b i) (x : U) (i : ι) (z : ι → ℝ) :
    b.dual i x (A.matrix x z) = v i x * b.dual i x z := by
  let X : Fields U := constantField z
  have hX : field X x = z := field_constantField z x
  rw [← hX, A.matrix_field, b.dual_field, b.dual_field]
  have hh := b.endomorphism_coordinates A v heigen X
  exact congrArg (fun Z : ι → Functions U => Z i x) hh

/-- Vanishing Haantjes tensor yields genuine smooth diagonalizing coordinates.
This intermediate theorem takes a smooth eigenframe; spectral selection is separate. -/
theorem haantjes_local_coordinates (hU : IsOpen U) (b : Frame U)
    (A : Endomorphism U) (v : ι → Functions U)
    (heigen : ∀ i, A (b i) = v i • b i)
    (hgap : ∀ i j, i ≠ j → IsUnit (v i - v j)) (hH : HaantjesVanish hU A)
    (p : U) :
    ∃ e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ),
      (p : ι → ℝ) ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ q ∈ e.source, ∀ z i,
        fderiv ℝ e q (A.matrix q z) i = extend U (v i) q * fderiv ℝ e q z i := by
  have hc := (b.haantjesVanish_iff_complement_involutive hU A v heigen hgap).mp hH
  apply Geometry.coframe_local_diagonalization hU b.dual_smooth
    (fun i => b.dual_frobenius_of_involutive hU i (hc i))
    (p := (p : ι → ℝ)) (hp := p.property) (hi := b.dual_invertible p)
  intro q hq i z
  simpa only [extend_apply U (v i) ⟨q, hq⟩] using b.dual_eigen A v heigen ⟨q, hq⟩ i z

end SemiHamiltonian.Smooth.Frame
