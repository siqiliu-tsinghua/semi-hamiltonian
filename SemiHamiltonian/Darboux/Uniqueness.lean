module

public import SemiHamiltonian.Darboux.IntegralEquation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Uniqueness of classical solutions of the Darboux initial value problem

A classical solution on a cube is the restriction of a differentiable function
defined on a neighbourhood of that cube. We prove directly, by the chain rule and
the fundamental theorem of calculus, that it solves the radial integral equation.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal BigOperators

namespace SemiHamiltonian.Darboux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

def affineRadial (i : ι) (x : Cube ι r) (t : ℝ) : ι → ℝ :=
  fun j => if j = i then x j else t * x j

def transverse (i : ι) (x : Cube ι r) : ι → ℝ :=
  fun j => if j = i then 0 else x j

theorem point_radial (i : ι) (x : Cube ι r) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    point r (radial r i t x) = affineRadial r i x t := by
  funext j
  exact radial_apply_of_mem r i j x t ht

omit [Fintype ι] in
theorem hasDerivAt_affineRadial (i : ι) (x : Cube ι r) (t : ℝ) :
    HasDerivAt (affineRadial r i x) (transverse r i x) t := by
  apply hasDerivAt_pi.mpr
  intro j
  by_cases hji : j = i
  · simp only [affineRadial, transverse, hji, ite_true]
    exact hasDerivAt_const t _
  · simp only [affineRadial, transverse, hji, ite_false]
    simpa using (hasDerivAt_id t).mul_const (x j : ℝ)

theorem linearMap_transverse (L : (ι → ℝ) →L[ℝ] ℝ) (i : ι) (x : Cube ι r) :
    L (transverse r i x) = ∑ j, if j = i then 0 else (x j : ℝ) * L (Pi.single j 1) := by
  have hv : transverse r i x = ∑ j : ι, (transverse r i x j) • Pi.single j (1 : ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
  rw [hv, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  by_cases hji : j = i <;> simp [transverse, hji, smul_eq_mul]

/-- Actual differentiable solutions and their prescribed axis data.
No integrability or existence is included in this predicate. -/
def IsClassicalSolution (Γ : Coefficients (ι := ι) r) (φ : AxisData (ι := ι) r)
    (w : Values (ι := ι) r) : Prop :=
  ∃ (W : (ι → ℝ) → ι → ℝ) (J : Cube ι r → ι → (ι → ℝ) →L[ℝ] ℝ),
    (∀ x, W (point r x) = w x) ∧
    (∀ x i, HasFDerivAt (fun y => W y i) (J x i) (point r x)) ∧
    (∀ x i j, i ≠ j → J x i (Pi.single j 1) = Γ x i j * (w x j - w x i)) ∧
    (∀ i x, w (axis r i x) i = φ i (x i))

theorem classicalSolution_fixedPoint (Γ : Coefficients (ι := ι) r)
    (φ : AxisData (ι := ι) r) (w : Values (ι := ι) r)
    (hw : IsClassicalSolution r Γ φ w) : picard r Γ φ w = w := by
  obtain ⟨W, J, hW, hd, he, ha⟩ := hw
  apply ContinuousMap.ext
  intro x
  funext i
  let g : ℝ → ℝ := fun t => ∑ j, if j = i then 0 else
    (x j : ℝ) * kernel r Γ w i j x t
  have hint : IntervalIntegrable g volume 0 1 := by
    have hc : Continuous g := by
      apply continuous_finsetSum
      intro j _
      by_cases hji : j = i
      · simp only [hji, ite_true]; exact continuous_const
      · simp only [hji, ite_false]
        exact continuous_const.mul
          ((continuous_kernel r Γ w i j).comp (continuous_const.prodMk continuous_id))
    exact hc.intervalIntegrable 0 1
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => W (affineRadial r i x s) i) (g t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
    have hf := hd (radial r i t x) i
    rw [point_radial r i x t ht'] at hf
    have hc : HasDerivAt (fun s => W (affineRadial r i x s) i)
        (J (radial r i t x) i (transverse r i x)) t :=
      hf.comp_hasDerivAt t (hasDerivAt_affineRadial r i x t)
    have heval : J (radial r i t x) i (transverse r i x) = g t := by
      rw [linearMap_transverse]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · simp [hji]
      · simp only [hji, ite_false]
        rw [he _ i j (Ne.symm hji)]
        rfl
    simpa only [heval] using hc
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hend : W (affineRadial r i x 1) i = w x i := by
    rw [← point_radial r i x 1 (by constructor <;> norm_num), radial_one, hW]
  have hstart : W (affineRadial r i x 0) i = φ i (x i) := by
    rw [← point_radial r i x 0 (by constructor <;> norm_num), hW]
    exact ha i x
  rw [hend, hstart] at hFTC
  have hsum : ∫ t in (0 : ℝ)..1, g t = integralOperator r Γ w x i := by
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · simp [hji]
      · simp [hji, intervalIntegral.integral_const_mul]
    · intro j _
      by_cases hji : j = i
      · simp only [hji, ite_true]; exact intervalIntegrable_const
      · simp only [hji, ite_false]
        exact (kernel_integrable r Γ w i j x).const_mul _
  rw [hsum] at hFTC
  change φ i (x i) + integralOperator r Γ w x i = w x i
  linarith

/-- Classical uniqueness on a sufficiently small cube, for arbitrary axis data.
Compatibility is needed for existence, not for this uniqueness statement. -/
theorem classicalSolution_unique (Γ : Coefficients (ι := ι) r) (φ : AxisData (ι := ι) r)
    (hsmall : 2 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1)
    {w z : Values (ι := ι) r}
    (hw : IsClassicalSolution r Γ φ w) (hz : IsClassicalSolution r Γ φ z) : w = z :=
  (picard_contraction r Γ φ hsmall).fixedPoint_unique'
    (classicalSolution_fixedPoint r Γ φ w hw) (classicalSolution_fixedPoint r Γ φ z hz)

end SemiHamiltonian.Darboux
