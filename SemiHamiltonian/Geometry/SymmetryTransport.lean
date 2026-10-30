module

public import SemiHamiltonian.Geometry.ChartTransport
public import SemiHamiltonian.Geometry.PSSDiagonal
public import SemiHamiltonian.PSS.InvariantSymmetry

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)} (hU : IsOpen U)

def IsHydrodynamicSymmetry (A B : Endomorphism U) : Prop :=
  PSS.IsInvariantSymmetry (fieldBracket hU) A B

theorem isCommutingSpeed_iff_invariantSymmetry (S : System hU) (w : ι → Functions U) :
    S.IsCommutingSpeed w ↔ IsHydrodynamicSymmetry hU
      (PSS.FrameData.diagonalMap S.speed) (PSS.FrameData.diagonalMap w) := by
  have hpol (X Y : Fields U) :
      PSS.polarized (fieldBracket hU) (PSS.FrameData.diagonalMap S.speed)
        (PSS.FrameData.diagonalMap w) X Y =
      (PSS.CoordinateDerivations.frame (coordinateDerivations hU)).polarizedSymmetry
        S.speed w X Y := by
    funext r
    simp only [PSS.polarized, fieldBracket_eq_coordinate, Pi.add_apply, Pi.sub_apply,
      PSS.FrameData.diagonalMap, LinearMap.coe_mk, AddHom.coe_mk,
      PSS.FrameData.applyDiagonal, PSS.FrameData.polarizedSymmetry]
  rw [S.isCommutingSpeed_iff_hydrodynamicSymmetry]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro X
      funext r
      change S.speed r * (w r * X r) = w r * (S.speed r * X r)
      ring
    · intro X Y
      rw [hpol]
      funext r
      exact h X Y r
  · intro h X Y r
    have hh := h.2 X Y
    rw [hpol] at hh
    exact congrFun hh r

end SemiHamiltonian.Smooth

namespace SemiHamiltonian.Geometry

open Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
  (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)

theorem hydrodynamicSymmetry_chart_iff (A B : Endomorphism e.source)
    (A' B' : Endomorphism e.target)
    (hA : ∀ X, chartPush e he hi (A X) = A' (chartPush e he hi X))
    (hB : ∀ X, chartPush e he hi (B X) = B' (chartPush e he hi X)) :
    IsHydrodynamicSymmetry e.open_source A B ↔
      IsHydrodynamicSymmetry e.open_target A' B' :=
  PSS.invariantSymmetry_map_iff (chartPushEquiv e he hi) (chartPush_bracket e he hi) hA hB

/-- Coordinate conjugation carries actual hydrodynamic symmetries to actual symmetries. -/
theorem hydrodynamicSymmetry_conjugate_iff (A B : Endomorphism e.source) :
    IsHydrodynamicSymmetry e.open_source A B ↔
      IsHydrodynamicSymmetry e.open_target (chartEndomorphism e he hi A)
        (chartEndomorphism e he hi B) :=
  hydrodynamicSymmetry_chart_iff e he hi A B _ _
    (chartEndomorphism_intertwines e he hi A) (chartEndomorphism_intertwines e he hi B)

/-- Every commuting speed in Riemann coordinates yields a smooth symmetry operator
in the original variables. The two operators satisfy PSS (2.4) and (2.5). -/
theorem symmetry_of_commutingSpeed (A : Endomorphism e.source) (S : System e.open_target)
    (hA : ∀ X, chartPush e he hi (A X) =
      PSS.FrameData.diagonalMap S.speed (chartPush e he hi X))
    (w : ι → Functions e.target) (hw : S.IsCommutingSpeed w) :
    IsHydrodynamicSymmetry e.open_source A
      (chartEndomorphism e.symm hi he (PSS.FrameData.diagonalMap w)) := by
  apply (hydrodynamicSymmetry_chart_iff e he hi A _ _ _ hA ?_).mpr
    ((isCommutingSpeed_iff_invariantSymmetry e.open_target S w).mp hw)
  intro X
  change chartPush e he hi
    (chartPush e.symm hi he (PSS.FrameData.diagonalMap w (chartPush e he hi X))) = _
  exact chartPush_inverse e.symm hi he _

end SemiHamiltonian.Geometry
