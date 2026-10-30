module

public import SemiHamiltonian.Geometry.SmoothFrame
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Pointwise evaluation and the smooth dual coframe of a basis of smooth fields. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}

noncomputable def standardField (i : ι) : Fields U := Pi.single i 1

theorem sum_standardField (X : Fields U) : ∑ i, X i • standardField i = X := by
  funext k
  simp [standardField, Pi.single_apply]

namespace Frame

noncomputable def dual (b : Frame U) (i : ι) (q : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ k, extend U (b.equivFun (standardField k) i) q • ContinuousLinearMap.proj k

theorem dual_smooth (b : Frame U) (i : ι) : ContDiffOn ℝ ∞ (b.dual i) U :=
  ContDiffOn.sum (fun k _ => (smooth U _).smul contDiffOn_const)

theorem dual_apply (b : Frame U) (i : ι) (x : U) (v : ι → ℝ) :
    b.dual i x v = ∑ k, b.equivFun (standardField k) i x * v k := by
  simp [dual, extend_apply, smul_eq_mul]

theorem dual_field (b : Frame U) (i : ι) (X : Fields U) (x : U) :
    b.dual i x (field X x) = b.equivFun X i x := by
  rw [dual_apply]
  conv_rhs => rw [← sum_standardField X]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  change _ = eval x (∑ k, X k * b.equivFun (standardField k) i)
  rw [map_sum]
  simp only [map_mul, field_apply]
  change (∑ k, b.equivFun (standardField k) i x * X k x) =
    ∑ k, X k x * b.equivFun (standardField k) i x
  simp only [mul_comm]

theorem dual_frame (b : Frame U) (i j : ι) (x : U) :
    b.dual i x (field (b j) x) = if i = j then 1 else 0 := by
  rw [dual_field]
  simp only [b.equivFun_self]
  by_cases hij : i = j
  · subst j; simp
  · simp [hij, Ne.symm hij]

theorem field_sum_equivFun (b : Frame U) (X : Fields U) (x : U) :
    field X x = ∑ i, b.equivFun X i x • field (b i) x := by
  have hh := b.sum_equivFun X
  funext k
  have hk := congrArg (fun Z : Fields U => Z k x) hh
  simpa [field_apply] using hk.symm

theorem dual_separates (b : Frame U) (x : U) (v : ι → ℝ)
    (hv : ∀ i, b.dual i x v = 0) : v = 0 := by
  let X : Fields U := fun k => algebraMap ℝ (Functions U) (v k)
  have hX : field X x = v := by ext k; simp [X, field_apply, Algebra.algebraMap_eq_smul_one]
  have he := b.field_sum_equivFun X x
  rw [hX] at he
  have hz (i : ι) : b.equivFun X i x = 0 := by rw [← b.dual_field i X x, hX]; exact hv i
  simp only [hz, zero_smul, Finset.sum_const_zero] at he
  exact he

end Frame
end SemiHamiltonian.Smooth
