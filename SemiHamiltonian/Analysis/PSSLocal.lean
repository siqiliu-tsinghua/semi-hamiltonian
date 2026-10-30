module

public import SemiHamiltonian.Analysis.TsarevLocal
public import SemiHamiltonian.PSS.DiagonalTensor

/-! The PSS tensor criterion for actual smooth diagonal systems.
The general-coordinate theorem is in `Geometry/PSSLocal.lean`. -/

@[expose] public section

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)} (hU : IsOpen U)

theorem locallyAxisSolvable_iff_P_zero (S : System hU) :
    LocallyAxisSolvable hU S ↔
      ∀ r a b c, PSS.DiagonalTensor.P (coordinateDerivations hU) S.speed r a b c = 0 :=
  (semiHamiltonian_iff_locallyAxisSolvable hU S).symm.trans
    (PSS.DiagonalTensor.semiHamiltonian_iff_P_zero _ S)

theorem locallyRich_iff_P_zero (S : System hU) :
    LocallyRich hU S ↔
      ∀ r a b c, PSS.DiagonalTensor.P (coordinateDerivations hU) S.speed r a b c = 0 :=
  (semiHamiltonian_iff_locallyRich hU S).symm.trans
    (PSS.DiagonalTensor.semiHamiltonian_iff_P_zero _ S)

end SemiHamiltonian.Smooth
