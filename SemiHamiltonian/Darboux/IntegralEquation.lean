module

public import SemiHamiltonian.Darboux.Cube
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Radial integral equation for the Darboux problem

This file constructs its continuous solution by contraction. Compatibility is not
needed for this step. Proving that this fixed point satisfies all the differential
equations is a separate requirement; a fixed point is not called a PDE solution.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators NNReal

namespace SemiHamiltonian.Darboux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

abbrev Values := C(Cube ι r, ι → ℝ)
abbrev Coefficients := C(Cube ι r, ι → ι → ℝ)
abbrev AxisData := ι → C(Set.Icc (-(r : ℝ)) r, ℝ)

noncomputable def initial (φ : AxisData (ι := ι) r) : Values (ι := ι) r where
  toFun x i := φ i (x i)
  continuous_toFun := continuous_pi fun i => (φ i).continuous.comp (continuous_apply i)

noncomputable def kernel (Γ : Coefficients (ι := ι) r) (w : Values (ι := ι) r)
    (i j : ι) (x : Cube ι r) (t : ℝ) : ℝ :=
  Γ (radial r i t x) i j * (w (radial r i t x) j - w (radial r i t x) i)

theorem continuous_kernel (Γ : Coefficients (ι := ι) r) (w : Values (ι := ι) r)
    (i j : ι) : Continuous (Function.uncurry (kernel r Γ w i j)) := by
  have hp : Continuous (fun z : Cube ι r × ℝ => radial r i z.2 z.1) :=
    (continuous_radial r i).comp continuous_swap
  unfold kernel Function.uncurry
  fun_prop

theorem kernel_integrable (Γ : Coefficients (ι := ι) r) (w : Values (ι := ι) r)
    (i j : ι) (x : Cube ι r) : IntervalIntegrable (kernel r Γ w i j x) volume 0 1 :=
  ((continuous_kernel r Γ w i j).comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1

/-- The radial Volterra operator, with i-th coordinate held fixed in its i-th row. -/
noncomputable def integralOperator (Γ : Coefficients (ι := ι) r)
    (w : Values (ι := ι) r) : Values (ι := ι) r where
  toFun x i := ∑ j, if j = i then 0 else
    (x j : ℝ) * ∫ t in (0 : ℝ)..1, kernel r Γ w i j x t
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j _
    by_cases hji : j = i
    · simp only [hji, ite_true]; exact continuous_const
    · simp only [hji, ite_false]
      exact (continuous_subtype_val.comp (continuous_apply j)).mul
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (continuous_kernel r Γ w i j) 0 1)

noncomputable def picard (Γ : Coefficients (ι := ι) r) (φ : AxisData (ι := ι) r)
    (w : Values (ι := ι) r) : Values (ι := ι) r := initial r φ + integralOperator r Γ w

omit [DecidableEq ι] in
theorem component_le_norm (w : Values (ι := ι) r) (x : Cube ι r) (i : ι) :
    ‖w x i‖ ≤ ‖w‖ := (norm_le_pi_norm (w x) i).trans (w.norm_coe_le_norm x)

omit [DecidableEq ι] in
theorem coefficient_le_norm (Γ : Coefficients (ι := ι) r) (x : Cube ι r) (i j : ι) :
    ‖Γ x i j‖ ≤ ‖Γ‖ :=
  (norm_le_pi_norm (Γ x i) j).trans
    ((norm_le_pi_norm (Γ x) i).trans (Γ.norm_coe_le_norm x))

theorem kernel_norm_le (Γ : Coefficients (ι := ι) r) (w : Values (ι := ι) r)
    (i j : ι) (x : Cube ι r) (t : ℝ) :
    ‖kernel r Γ w i j x t‖ ≤ 2 * ‖Γ‖ * ‖w‖ := by
  rw [kernel, norm_mul]
  calc
    _ ≤ ‖Γ‖ * (‖w (radial r i t x) j‖ + ‖w (radial r i t x) i‖) :=
      mul_le_mul (coefficient_le_norm r Γ _ i j) (norm_sub_le _ _) (norm_nonneg _) (norm_nonneg _)
    _ ≤ ‖Γ‖ * (‖w‖ + ‖w‖) := mul_le_mul_of_nonneg_left
      (add_le_add (component_le_norm r w _ j) (component_le_norm r w _ i)) (norm_nonneg _)
    _ = _ := by ring

theorem integralOperator_sub (Γ : Coefficients (ι := ι) r) (w z : Values (ι := ι) r) :
    integralOperator r Γ (w - z) = integralOperator r Γ w - integralOperator r Γ z := by
  apply ContinuousMap.ext
  intro x
  funext i
  change (∑ j : ι, if j = i then 0 else (x j : ℝ) *
    ∫ t in (0 : ℝ)..1, kernel r Γ (w - z) i j x t) =
    (∑ j : ι, if j = i then 0 else (x j : ℝ) * ∫ t in (0 : ℝ)..1, kernel r Γ w i j x t) -
    ∑ j : ι, if j = i then 0 else (x j : ℝ) * ∫ t in (0 : ℝ)..1, kernel r Γ z i j x t
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · simp [hji]
  · simp only [hji, ite_false]
    have hk : kernel r Γ (w - z) i j x =
        fun t => kernel r Γ w i j x t - kernel r Γ z i j x t := by
      funext t
      simp only [kernel, ContinuousMap.sub_apply, Pi.sub_apply]
      ring
    rw [hk, intervalIntegral.integral_sub (kernel_integrable r Γ w i j x)
      (kernel_integrable r Γ z i j x)]
    ring

theorem integralOperator_norm_le (Γ : Coefficients (ι := ι) r) (w : Values (ι := ι) r) :
    ‖integralOperator r Γ w‖ ≤ (2 * Fintype.card ι * (r : ℝ) * ‖Γ‖) * ‖w‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖∑ j, _‖ ≤ _
  calc
    _ ≤ ∑ j : ι, (r : ℝ) * (2 * ‖Γ‖ * ‖w‖) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      by_cases hji : j = i
      · simp [hji]; positivity
      · simp only [hji, ite_false, norm_mul]
        have hi : ‖∫ t in (0 : ℝ)..1, kernel r Γ w i j x t‖ ≤ 2 * ‖Γ‖ * ‖w‖ := by
          simpa using intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
            (fun t _ => kernel_norm_le r Γ w i j x t)
        exact mul_le_mul (abs_coordinate_le r x j) hi (norm_nonneg _) r.coe_nonneg
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

theorem picard_contraction (Γ : Coefficients (ι := ι) r) (φ : AxisData (ι := ι) r)
    (hsmall : 2 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1) :
    ContractingWith ⟨2 * Fintype.card ι * (r : ℝ) * ‖Γ‖, by positivity⟩ (picard r Γ φ) := by
  refine ⟨hsmall, LipschitzWith.of_dist_le_mul fun w z => ?_⟩
  simp only [dist_eq_norm, picard, add_sub_add_left_eq_sub,
    ← integralOperator_sub]
  exact integralOperator_norm_le r Γ (w - z)

/-- Continuous existence and uniqueness for the radial integral equation. -/
theorem existsUnique_integralEquation (Γ : Coefficients (ι := ι) r) (φ : AxisData (ι := ι) r)
    (hsmall : 2 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1) :
    ∃! w : Values (ι := ι) r, picard r Γ φ w = w := by
  let h := picard_contraction r Γ φ hsmall
  exact ⟨h.fixedPoint _, h.fixedPoint_isFixedPt, fun _ hw => h.fixedPoint_unique hw⟩

/-- Every fixed point has exactly the specified values on each coordinate axis. -/
theorem fixedPoint_axis (Γ : Coefficients (ι := ι) r) (φ : AxisData (ι := ι) r)
    (w : Values (ι := ι) r) (hw : picard r Γ φ w = w) (i : ι) (x : Cube ι r) :
    w (axis r i x) i = φ i (x i) := by
  rw [← hw]
  change φ i (axis r i x i) + (∑ j, _) = _
  have ha : axis r i x i = x i := Subtype.ext (axis_coordinate r i x)
  rw [ha]
  have hz : (∑ j, if j = i then 0 else (axis r i x j : ℝ) *
      ∫ t in (0 : ℝ)..1, kernel r Γ w i j (axis r i x) t) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hji : j = i
    · simp [hji]
    · simp [hji, axis_other r i j hji x]
  rw [hz, add_zero]

end SemiHamiltonian.Darboux
