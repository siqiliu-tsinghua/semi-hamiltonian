module

import SemiHamiltonian
import Mathlib.Tactic.FinCases

/-! Nonconstant coefficient examples for the smooth theorem. -/

open scoped NNReal ContDiff
open SemiHamiltonian.Darboux

private def coupled (i j : Fin 2) (x : Fin 2 → ℝ) : ℝ := x i ^ 2 + x j + 1

private theorem coupled_smooth (i j : Fin 2) : ContDiff ℝ ∞ (coupled i j) := by
  unfold coupled
  fun_prop

-- Both equations have variable, nonzero coupling; axis data remain arbitrary.
example : ∃ r : ℝ≥0, 0 < r ∧ r ≤ 1 ∧
    ∀ (φ : Fin 2 → C(ℝ, ℝ)), (∀ i, ContDiff ℝ ∞ (φ i)) →
      ∃! u : Values (ι := Fin 2) r,
        IsSmoothDarbouxSolution r (smoothCoefficientJets r coupled coupled_smooth) φ u := by
  apply local_existsUnique_smooth_darboux_of_functions 1 (by norm_num) coupled coupled_smooth
  intro x hx i j k hij hik hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

private def triangular (_i j : Fin 3) (x : Fin 3 → ℝ) : ℝ := if j = 0 then x 0 else 0

private theorem triangular_smooth (i j : Fin 3) : ContDiff ℝ ∞ (triangular i j) := by
  unfold triangular
  split_ifs <;> fun_prop

-- Three distinct indices exist here, so compatibility is checked explicitly.
example : ∃ r : ℝ≥0, 0 < r ∧ r ≤ 1 ∧
    ∀ (φ : Fin 3 → C(ℝ, ℝ)), (∀ i, ContDiff ℝ ∞ (φ i)) →
      ∃! u : Values (ι := Fin 3) r,
        IsSmoothDarbouxSolution r (smoothCoefficientJets r triangular triangular_smooth) φ u := by
  apply local_existsUnique_smooth_darboux_of_functions 1 (by norm_num) triangular triangular_smooth
  intro x hx i j k hij hik hjk
  have hd : fderiv ℝ (fun z : Fin 3 → ℝ => z 0) x = ContinuousLinearMap.proj 0 :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).hasFDerivAt.fderiv
  by_cases hj : j = 0
  · have hk : k ≠ 0 := fun hk => hjk (hj.trans hk.symm)
    have he : triangular i j = fun z => z 0 := by funext z; simp [triangular, hj]
    rw [he]
    simp [triangular, hj, hk, hd, Pi.single_apply, Ne.symm hk]
  · have he : triangular i j = fun _ => 0 := by funext z; simp [triangular, hj]
    rw [he]
    simp [triangular, hj]
