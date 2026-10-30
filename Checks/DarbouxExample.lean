module

import SemiHamiltonian
import Mathlib.Tactic.FinCases

/-! A nonzero coupled two-component example exercising the analytic theorem. -/

open scoped NNReal
open SemiHamiltonian.Darboux

set_option synthInstance.maxSize 512

private noncomputable abbrev radius : ℝ≥0 := 1 / 100

private noncomputable def coupledCoefficients : JetCoefficients (ι := Fin 2) radius :=
  fun _ _ => (ContinuousMap.const _ (1 : ℝ), 0)

example (φ ψ : Fin 2 → C(ℝ, ℝ))
    (hφ : ∀ i (s : ℝ), HasDerivAt (φ i) (ψ i s) s) :
    ∃! u : Values (ι := Fin 2) radius,
      IsC1DarbouxSolution radius coupledCoefficients (axisDataOfFunctions radius φ) u := by
  have hΓ : ∀ i j, IsCubeJet radius (coupledCoefficients i j) := by
    intro i j x _
    simpa [coupledCoefficients] using (hasFDerivAt_const (1 : ℝ) x)
  have hc : IsDarbouxCompatible radius coupledCoefficients := by
    intro x i j k hij hik hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  have hb : ‖coupledCoefficients‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    change max ‖(ContinuousMap.const (Cube (Fin 2) radius) (1 : ℝ))‖
      ‖(0 : C(Cube (Fin 2) radius, (Fin 2 → ℝ) →L[ℝ] ℝ))‖ ≤ 1
    apply max_le
    · simp
    · apply (ContinuousMap.norm_le _ zero_le_one).mpr
      intro x
      change ‖(0 : (Fin 2 → ℝ) →L[ℝ] ℝ)‖ ≤ 1
      simp
  have hs : 8 * Fintype.card (Fin 2) * (radius : ℝ) * ‖coupledCoefficients‖ < 1 := by
    norm_num [radius] at *
    linarith
  exact existsUnique_C1_darboux_axisData radius (by norm_num [radius]) coupledCoefficients
    hΓ hc hs φ ψ (fun i s _ => hφ i s)
