module

public import SemiHamiltonian.Geometry.PSSTensor
public import SemiHamiltonian.PSS.DiagonalRecipe
public import SemiHamiltonian.Analysis.PSSLocal

@[expose] public section

open Set

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)} (hU : IsOpen U)

theorem fieldBracket_eq_coordinate : fieldBracket hU =
    (PSS.CoordinateDerivations.frame (coordinateDerivations hU)).bracket := by
  funext X Y r
  simp [fieldBracket, fieldDerivation_apply, PSS.FrameData.bracket,
    PSS.CoordinateDerivations.frame, Finset.sum_sub_distrib]

theorem pssTensor_diagonal_eq_recipe (v : ι → Functions U) (X Y Z : Fields U) :
    pssTensor hU (PSS.FrameData.diagonalMap v) X Y Z =
      (PSS.CoordinateDerivations.frame (coordinateDerivations hU)).calculus.pTensor
        (PSS.FrameData.diagonalMap v) X Y Z := by
  simp only [pssTensor_apply, PSS.BracketCalculus.pTensor_apply]
  change PSS.TensorRecipe.P (fieldBracket hU) _ X Y Z =
    PSS.TensorRecipe.P (PSS.CoordinateDerivations.frame (coordinateDerivations hU)).bracket
      _ X Y Z
  rw [fieldBracket_eq_coordinate]

theorem pssTensor_diagonal_basis (v : ι → Functions U) (r a b c : ι) :
    pssTensor hU (PSS.FrameData.diagonalMap v)
      (PSS.FrameData.scaledBasis a 1) (PSS.FrameData.scaledBasis b 1)
      (PSS.FrameData.scaledBasis c 1) r =
      PSS.DiagonalTensor.P (coordinateDerivations hU) v r a b c := by
  rw [pssTensor_diagonal_eq_recipe]
  exact PSS.DiagonalRecipe.P_basis (coordinateDerivations hU) v r a b c

/-- For a diagonal smooth system the intrinsic tensor vanishes exactly when
the actual coefficient functions are semi-Hamiltonian. -/
theorem semiHamiltonian_iff_pssVanish (S : System hU) :
    S.IsSemiHamiltonian ↔ PSSVanish hU (PSS.FrameData.diagonalMap S.speed) := by
  rw [PSS.DiagonalRecipe.semiHamiltonian_iff_tensor_zero]
  unfold PSSVanish
  simp only [pssTensor_apply, PSS.BracketCalculus.pTensor_apply,
    fieldBracket_eq_coordinate]
  rfl

theorem pssVanish_iff_locallyAxisSolvable (S : System hU) :
    PSSVanish hU (PSS.FrameData.diagonalMap S.speed) ↔ LocallyAxisSolvable hU S :=
  (semiHamiltonian_iff_pssVanish hU S).symm.trans
    (semiHamiltonian_iff_locallyAxisSolvable hU S)

end SemiHamiltonian.Smooth
