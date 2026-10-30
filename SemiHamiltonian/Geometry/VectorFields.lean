module

public import SemiHamiltonian.Analysis.SmoothFunctions
public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.LinearAlgebra.Basis.Defs

/-! Actual smooth vector fields on an open coordinate domain. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}

abbrev Fields (U : Set (ι → ℝ)) := ι → Functions U

/-- An ambient representative, used only for derivatives at points of the open domain. -/
noncomputable def field (X : Fields U) (x : ι → ℝ) : ι → ℝ := fun i => extend U (X i) x

@[simp] theorem field_apply (X : Fields U) (x : U) (i : ι) : field X x i = X i x :=
  extend_apply U (X i) x

theorem field_smooth (X : Fields U) : ContDiffOn ℝ ∞ (field X) U :=
  contDiffOn_pi.mpr (fun i => smooth U (X i))

noncomputable def fieldDerivation (hU : IsOpen U) (X : Fields U) :
    Derivation ℝ (Functions U) (Functions U) :=
  ∑ i, X i • (coordinateDerivations hU).deriv i

theorem fieldDerivation_apply (hU : IsOpen U) (X : Fields U) (f : Functions U) :
    fieldDerivation hU X f = ∑ i, X i * (coordinateDerivations hU).deriv i f := by
  simp [fieldDerivation, Derivation.smul_apply, smul_eq_mul]

theorem fieldDerivation_eval (hU : IsOpen U) (X : Fields U) (f : Functions U) (x : U) :
    fieldDerivation hU X f x = fderiv ℝ (extend U f) x (field X x) := by
  rw [fieldDerivation_apply]
  have he : field X x = ∑ i, (X i x) • (Pi.single i 1 : ι → ℝ) := by
    funext j
    simp [field_apply, Pi.single_apply]
  rw [he, map_sum]
  change (∑ i, X i * (coordinateDerivations hU).deriv i f) x = _
  simp [map_smul, smul_eq_mul, coordinateDerivations, derivation_apply]

noncomputable def fieldBracket (hU : IsOpen U) (X Y : Fields U) : Fields U :=
  fun i => fieldDerivation hU X (Y i) - fieldDerivation hU Y (X i)

theorem fieldBracket_eval (hU : IsOpen U) (X Y : Fields U) (x : U) :
    field (fieldBracket hU X Y) x = _root_.VectorField.lieBracket ℝ (field X) (field Y) x := by
  have hd (Z : Fields U) : ∀ i, DifferentiableAt ℝ (extend U (Z i)) (x : ι → ℝ) :=
    fun i => (hasFDerivAt_extend hU (Z i) x).differentiableAt
  have hdf (Z : Fields U) : fderiv ℝ (field Z) (x : ι → ℝ) =
      ContinuousLinearMap.pi (fun i => fderiv ℝ (extend U (Z i)) (x : ι → ℝ)) :=
    fderiv_pi (hd Z)
  funext i
  rw [field_apply]
  change (fieldDerivation hU X (Y i) - fieldDerivation hU Y (X i)) x = _
  change fieldDerivation hU X (Y i) x - fieldDerivation hU Y (X i) x = _
  rw [fieldDerivation_eval, fieldDerivation_eval]
  simp only [_root_.VectorField.lieBracket, hdf,
    ContinuousLinearMap.pi_apply, Pi.sub_apply]

@[simp] theorem fieldBracket_self (hU : IsOpen U) (X : Fields U) : fieldBracket hU X X = 0 := by
  funext i
  simp [fieldBracket]

theorem fieldBracket_swap (hU : IsOpen U) (X Y : Fields U) :
    fieldBracket hU X Y = -fieldBracket hU Y X := by
  funext i
  simp [fieldBracket, neg_sub]

@[simp] theorem fieldDerivation_smul (hU : IsOpen U) (f : Functions U) (X : Fields U) :
    fieldDerivation hU (f • X) = f • fieldDerivation hU X := by
  simp [fieldDerivation, Finset.smul_sum, mul_smul]

theorem fieldBracket_smul_right (hU : IsOpen U) (X Y : Fields U) (f : Functions U) :
    fieldBracket hU X (f • Y) = (fieldDerivation hU X f) • Y + f • fieldBracket hU X Y := by
  funext i
  simp only [fieldBracket, Pi.smul_apply, smul_eq_mul, Derivation.leibniz,
    fieldDerivation_smul, Derivation.smul_apply, Pi.add_apply]
  ring

theorem fieldBracket_smul_left (hU : IsOpen U) (X Y : Fields U) (f : Functions U) :
    fieldBracket hU (f • X) Y = f • fieldBracket hU X Y - (fieldDerivation hU Y f) • X := by
  rw [fieldBracket_swap, fieldBracket_smul_right, fieldBracket_swap hU Y X]
  module

theorem fieldBracket_sum_left (hU : IsOpen U) {κ : Type} (s : Finset κ)
    (X : κ → Fields U) (Y : Fields U) :
    fieldBracket hU (∑ k ∈ s, X k) Y = ∑ k ∈ s, fieldBracket hU (X k) Y := by
  funext i
  simp only [fieldBracket, fieldDerivation_apply, Finset.sum_apply, map_sum,
    Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

theorem fieldBracket_sum_right (hU : IsOpen U) {κ : Type} (s : Finset κ)
    (X : Fields U) (Y : κ → Fields U) :
    fieldBracket hU X (∑ k ∈ s, Y k) = ∑ k ∈ s, fieldBracket hU X (Y k) := by
  rw [fieldBracket_swap, fieldBracket_sum_left]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [fieldBracket_swap]
  simp

end SemiHamiltonian.Smooth
