module

import SemiHamiltonian

/-! End-to-end checks with actual nonconstant speeds and nonzero off-diagonal
couplings on an arbitrary open set. Three indices make compatibility nonvacuous. -/

open scoped ContDiff
open SemiHamiltonian SemiHamiltonian.Smooth

namespace LocalIntegrabilityCheck

abbrev E := Fin 3 → ℝ

noncomputable def total : E →L[ℝ] ℝ := ∑ k : Fin 3, ContinuousLinearMap.proj k

theorem total_single (j : Fin 3) : total (Pi.single j 1) = 1 := by
  simp [total, Pi.single_apply]

variable {U : Set E} (hU : IsOpen U)

noncomputable def speeds : Fin 3 → Functions U := fun i =>
  ofContDiffOn (fun x => total x + (i.val : ℝ)) (total.contDiff.add contDiff_const).contDiffOn

theorem hyperbolic : StrictlyHyperbolic (speeds (U := U)) := by
  intro x i j hij he
  change total x + (i.val : ℝ) = total x + (j.val : ℝ) at he
  have h : (i.val : ℝ) = j.val := add_left_cancel he
  apply hij
  apply Fin.ext
  exact_mod_cast h

noncomputable def system : System hU := ofSpeeds hU speeds hyperbolic

theorem speed_derivative (i j : Fin 3) :
    (coordinateDerivations hU).deriv j (speeds (U := U) i) = 1 := by
  apply Subtype.ext
  funext x
  change directional hU (Pi.single j 1) (ofContDiffOn _ _) x = (1 : ℝ)
  rw [directional_ofContDiffOn]
  rw [(total.hasFDerivAt.add_const (i.val : ℝ)).fderiv]
  exact total_single j

theorem coefficient (i j : Fin 3) (hij : i ≠ j) :
    (system hU).coeff i j = algebraMap ℝ (Functions U) (1 / ((j.val : ℝ) - i.val)) := by
  apply (system hU).coeff_unique i j hij
  change (coordinateDerivations hU).deriv j (speeds i) = _
  rw [speed_derivative]
  apply Subtype.ext
  funext x
  change (1 : ℝ) = (1 / ((j.val : ℝ) - i.val)) *
    ((total x + (j.val : ℝ)) - (total x + (i.val : ℝ)))
  have hne : (j.val : ℝ) - i.val ≠ 0 := by
    intro h
    apply hij
    apply Fin.ext
    have hh := sub_eq_zero.mp h
    exact_mod_cast hh.symm
  rw [show (total x + (j.val : ℝ)) - (total x + (i.val : ℝ)) =
    (j.val : ℝ) - i.val by ring, one_div_mul_cancel hne]

theorem semiHamiltonian : (system hU).IsSemiHamiltonian := by
  intro i j k hij hik _
  rw [coefficient hU i j hij, coefficient hU i k hik]
  simp

-- For every point of any open U, a uniform neighbourhood works for all three
-- arbitrary smooth axis data. The proof invokes actual Darboux PDE existence.
example : LocallyAxisSolvable hU (system hU) :=
  (semiHamiltonian_iff_locallyAxisSolvable hU _).mp (semiHamiltonian hU)

example : LocallyRich hU (system hU) :=
  (semiHamiltonian_iff_locallyRich hU _).mp (semiHamiltonian hU)

-- The PSS tensor vanishes as an actual function on U.
example (r a b c : Fin 3) (x : U) :
    PSS.DiagonalTensor.P (coordinateDerivations hU) (system hU).speed r a b c x = 0 := by
  have h := (locallyAxisSolvable_iff_P_zero hU (system hU)).mp
    ((semiHamiltonian_iff_locallyAxisSolvable hU _).mp (semiHamiltonian hU)) r a b c
  exact congrArg (fun f : Functions U => f x) h

end LocalIntegrabilityCheck
