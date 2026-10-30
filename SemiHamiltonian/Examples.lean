module

public import SemiHamiltonian.PSS.DiagonalTensor
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Tactic.FinCases

/-!
# Polynomial examples with separated speeds

The example v = (f, f+1, f+2) has constant nonzero speed gaps. Taking
f = u¹ u² gives a non-semi-Hamiltonian system, whereas f = 0 gives a
semi-Hamiltonian system. On evaluating over the reals, the former is strictly
hyperbolic everywhere: hyperbolicity alone does not imply integrability.
-/

@[expose] public section

namespace SemiHamiltonian.Examples

open MvPolynomial

abbrev Poly := MvPolynomial (Fin 3) ℚ

noncomputable def coordinates : CoordinateDerivations ℚ Poly (Fin 3) where
  deriv := pderiv
  commute := pderiv_comm

def offset (i : Fin 3) : ℚ := i.val

private theorem offset_gap (i j : Fin 3) (hij : i ≠ j) : offset j - offset i ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [offset] at *

/-- A concrete class of diagonal systems with fixed gaps 1 and 2. -/
noncomputable def shifted (f : Poly) : DiagonalSystem coordinates where
  speed i := f + C (offset i)
  coeff i j := C ((offset j - offset i)⁻¹) * pderiv j f
  speed_deriv i j hij := by
    change pderiv j (f + C (offset i)) = _
    simp only [map_add, pderiv_C, add_zero]
    have hgap : f + C (offset j) - (f + C (offset i)) = C (offset j - offset i) := by
      rw [map_sub]; ring
    rw [hgap]
    calc
      pderiv j f = (C ((offset j - offset i)⁻¹) * C (offset j - offset i)) * pderiv j f := by
        rw [← map_mul, inv_mul_cancel₀ (offset_gap i j hij), map_one, one_mul]
      _ = _ := by ring
  gap_unit i j hij := by
    have hgap : f + C (offset j) - (f + C (offset i)) = C (offset j - offset i) := by
      rw [map_sub]; ring
    rw [hgap]
    exact (isUnit_iff_ne_zero.mpr (offset_gap i j hij)).map C

theorem constant_isSemiHamiltonian : (shifted 0).IsSemiHamiltonian := by
  intro i j k _ _ _
  simp [shifted]

/-- Three arbitrary one-variable polynomials give actual commuting speeds for
the constant example. This is a concrete family, not an existence assumption. -/
theorem constant_commuting_polynomials (p : Fin 3 → Polynomial ℚ) :
    (shifted 0).IsCommutingSpeed (fun i => Polynomial.aeval (X i : Poly) (p i)) := by
  intro i j hij
  simp [shifted, coordinates, Derivation.map_aeval, pderiv_X_of_ne hij]

/-- Indices are 0,1,2 in Lean: f = X₁ X₂. -/
noncomputable def counterexample : DiagonalSystem coordinates := shifted (X 1 * X 2)

theorem counterexample_not_semiHamiltonian : ¬counterexample.IsSemiHamiltonian := by
  intro h
  have hz := h 0 1 2 (by decide) (by decide) (by decide)
  norm_num [counterexample, shifted, coordinates, offset,
    Derivation.leibniz, smul_eq_mul] at hz
  have hq := congrArg (eval (fun _ : Fin 3 => (0 : ℚ))) hz
  norm_num at hq

theorem counterexample_not_formallyCompatible : ¬counterexample.FormallyCompatible :=
  fun h => counterexample_not_semiHamiltonian
    (counterexample.formallyCompatible_implies_semiHamiltonian h)

theorem counterexample_P_nonzero :
    ∃ r a b c, PSS.DiagonalTensor.P coordinates counterexample.speed r a b c ≠ 0 := by
  by_contra h
  push Not at h
  exact counterexample_not_semiHamiltonian
    ((PSS.DiagonalTensor.semiHamiltonian_iff_P_zero coordinates counterexample).mpr h)

end SemiHamiltonian.Examples
