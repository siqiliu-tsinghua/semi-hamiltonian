module

public import SemiHamiltonian.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The compatibility calculation in Tsarev's theorem

We prove semi-Hamiltonianity equivalent to the vanishing of every mixed-derivative
obstruction in the linear commuting-speed equations. This is the algebraic part of
Tsarev's theorem. Local existence for arbitrary one-variable initial data is a
separate analytic theorem, not assumed or asserted in this file.
-/

@[expose] public section

namespace SemiHamiltonian.DiagonalSystem

variable {𝕜 R ι : Type*} [CommRing 𝕜] [CommRing R] [Algebra 𝕜 R]
variable {D : CoordinateDerivations 𝕜 R ι} (S : DiagonalSystem D)

/-- `∂ₖ∂ⱼwⁱ - ∂ⱼ∂ₖwⁱ`, after substituting the commuting-speed equations.
`w` here denotes arbitrary values, rather than a solution. -/
def mixedObstruction (i j k : ι) (w : ι → R) : R :=
  D.deriv k (S.coeff i j) * (w j - w i) +
    S.coeff i j * (S.coeff j k * (w k - w j) - S.coeff i k * (w k - w i)) -
  D.deriv j (S.coeff i k) * (w k - w i) -
    S.coeff i k * (S.coeff k j * (w j - w k) - S.coeff i j * (w j - w i))

/-- Formal compatibility is stated independently of semi-Hamiltonianity. -/
def FormallyCompatible : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ w, S.mixedObstruction i j k w = 0

/-- The coefficient appearing in the Darboux compatibility equations. -/
def darbouxResidual (i j k : ι) : R :=
  D.deriv k (S.coeff i j) - S.coeff i j * S.coeff j k -
    S.coeff i k * S.coeff k j + S.coeff i j * S.coeff i k

theorem mixedObstruction_eq_of_semiHamiltonian (h : S.IsSemiHamiltonian)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (w : ι → R) :
    S.mixedObstruction i j k w = S.darbouxResidual i j k * (w j - w k) := by
  unfold mixedObstruction darbouxResidual
  rw [← h i j k hij hik hjk]
  ring

/-- Every actual solution satisfies the mixed-derivative obstruction. -/
theorem mixedObstruction_eq_zero_of_solution (w : ι → R) (hw : S.IsCommutingSpeed w)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    S.mixedObstruction i j k w = 0 := by
  have h := D.commute k j (w i)
  rw [hw i j hij, hw i k hik] at h
  simp only [Derivation.leibniz, smul_eq_mul, map_sub] at h
  rw [hw j k hjk, hw i k hik, hw k j hjk.symm, hw i j hij] at h
  dsimp [mixedObstruction]
  linear_combination h

/-- The original speed is itself a solution. Separated speeds therefore remove
the remaining obstruction after the semi-Hamiltonian condition has been imposed. -/
theorem darbouxResidual_eq_zero (h : S.IsSemiHamiltonian)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    S.darbouxResidual i j k = 0 := by
  have hz := S.mixedObstruction_eq_zero_of_solution S.speed S.speed_isCommutingSpeed
    i j k hij hik hjk
  rw [S.mixedObstruction_eq_of_semiHamiltonian h i j k hij hik hjk] at hz
  apply (S.gap_unit k j hjk.symm).mul_right_cancel
  simpa only [zero_mul] using hz

theorem semiHamiltonian_implies_formallyCompatible (h : S.IsSemiHamiltonian) :
    S.FormallyCompatible := by
  intro i j k hij hik hjk w
  rw [S.mixedObstruction_eq_of_semiHamiltonian h i j k hij hik hjk,
    S.darbouxResidual_eq_zero h i j k hij hik hjk, zero_mul]

theorem formallyCompatible_implies_semiHamiltonian (h : S.FormallyCompatible) :
    S.IsSemiHamiltonian := by
  classical
  intro i j k hij hik hjk
  have hz := h i j k hij hik hjk (fun a => if a = i then 1 else 0)
  simp [mixedObstruction, hij.symm, hik.symm] at hz
  linear_combination -hz

/-- The algebraic compatibility theorem. This does not assert local solvability. -/
theorem semiHamiltonian_iff_formallyCompatible :
    S.IsSemiHamiltonian ↔ S.FormallyCompatible :=
  ⟨S.semiHamiltonian_implies_formallyCompatible,
    S.formallyCompatible_implies_semiHamiltonian⟩

end SemiHamiltonian.DiagonalSystem
