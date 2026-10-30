module

public import SemiHamiltonian.PSS.DiagonalTensor

/-!
# The link between Tsarev's linear system and the invariant symmetry equation
-/

@[expose] public section

namespace SemiHamiltonian

variable {𝕜 R ι : Type*} [CommRing 𝕜] [CommRing R] [Algebra 𝕜 R]
variable [Fintype ι] [DecidableEq ι]

namespace PSS.FrameData

theorem polarizedSymmetry_at_first (F : PSS.FrameData 𝕜 R ι) (v w : ι → R)
    (i j : ι) (hij : i ≠ j) :
    F.polarizedSymmetry v w (scaledBasis i 1) (scaledBasis j 1) i =
      F.deriv j (w i) * (v j - v i) - F.deriv j (v i) * (w j - w i) := by
  simp [polarizedSymmetry, applyDiagonal_scaledBasis, bracket_scaledBasis, hij]
  rw [F.skew i j i]
  ring

end PSS.FrameData

namespace DiagonalSystem

variable {D : CoordinateDerivations 𝕜 R ι} (S : DiagonalSystem D)

omit [DecidableEq ι] in
theorem coordinate_polarized_eq_sum (w X Y : ι → R) (r : ι) :
    (PSS.CoordinateDerivations.frame D).polarizedSymmetry S.speed w X Y r =
      ∑ p, (X p * Y r + Y p * X r) * S.flowBracketCoeff w r p := by
  simp only [PSS.FrameData.polarizedSymmetry, PSS.FrameData.bracket,
    PSS.FrameData.applyDiagonal, PSS.CoordinateDerivations.frame,
    mul_zero, Finset.sum_const_zero, add_zero, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [flowBracketCoeff, Derivation.leibniz, smul_eq_mul]
  ring

/-- Tsarev's linear PDE is equivalent to the polarized invariant flow-commutation
condition in a coordinate frame. -/
theorem isCommutingSpeed_iff_hydrodynamicSymmetry (w : ι → R) :
    S.IsCommutingSpeed w ↔
      (PSS.CoordinateDerivations.frame D).IsHydrodynamicSymmetry S.speed w := by
  rw [S.isCommutingSpeed_iff_flowBracketCoeff]
  constructor
  · intro h X Y r
    rw [S.coordinate_polarized_eq_sum]
    simp [h]
  · intro h i j
    by_cases hij : i = j
    · subst j; simp [flowBracketCoeff]
    · have hz := h (PSS.FrameData.scaledBasis i 1) (PSS.FrameData.scaledBasis j 1) i
      rw [PSS.FrameData.polarizedSymmetry_at_first _ _ _ i j hij] at hz
      exact hz

omit [Fintype ι] [DecidableEq ι] in
/-- All solutions of the same Tsarev linear system commute with one another.
The ambient speed gaps need not be gaps of either of these two symmetries. -/
theorem commuting_speeds_pairwise (w z : ι → R)
    (hw : S.IsCommutingSpeed w) (hz : S.IsCommutingSpeed z) (i j : ι) :
    D.deriv j (z i) * (w j - w i) - D.deriv j (w i) * (z j - z i) = 0 := by
  classical
  by_cases hij : i = j
  · subst j; simp
  · rw [hw i j hij, hz i j hij]
    ring

end DiagonalSystem
end SemiHamiltonian
