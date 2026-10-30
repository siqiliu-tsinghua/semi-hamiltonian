module

public import SemiHamiltonian.Darboux.SmoothLinear

/-! The radial integral equation for ∂ⱼuᵢ = aᵢⱼuᵢ + bᵢⱼuⱼ.
The two coefficients are independent. This file asserts integral-equation
existence only; differential compatibility is handled separately. -/

@[expose] public section

open MeasureTheory
open scoped BigOperators NNReal

namespace SemiHamiltonian.Darboux.Pair

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

abbrev Values := C(Cube ι r, ι → ℝ)
abbrev Coefficients := Darboux.Coefficients (ι := ι) r × Darboux.Coefficients (ι := ι) r
abbrev AxisData := ι → C(Set.Icc (-(r : ℝ)) r, ℝ)

noncomputable def initial (φ : AxisData (ι := ι) r) : Values (ι := ι) r where
  toFun x i := φ i (x i)
  continuous_toFun := continuous_pi fun i => (φ i).continuous.comp (continuous_apply i)

noncomputable def kernel (Γ : Coefficients (ι := ι) r) (w : Values (ι := ι) r)
    (i j : ι) (x : Cube ι r) (t : ℝ) : ℝ :=
  Γ.1 (radial r i t x) i j * w (radial r i t x) i +
    Γ.2 (radial r i t x) i j * w (radial r i t x) j

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
theorem left_coefficient_le_norm (Γ : Coefficients (ι := ι) r) (x : Cube ι r) (i j : ι) :
    ‖Γ.1 x i j‖ ≤ ‖Γ‖ := (Darboux.coefficient_le_norm r Γ.1 x i j).trans (norm_fst_le Γ)

omit [DecidableEq ι] in
theorem right_coefficient_le_norm (Γ : Coefficients (ι := ι) r) (x : Cube ι r) (i j : ι) :
    ‖Γ.2 x i j‖ ≤ ‖Γ‖ := (Darboux.coefficient_le_norm r Γ.2 x i j).trans (norm_snd_le Γ)

theorem kernel_norm_le (Γ : Coefficients (ι := ι) r) (w : Values (ι := ι) r)
    (i j : ι) (x : Cube ι r) (t : ℝ) :
    ‖kernel r Γ w i j x t‖ ≤ 2 * ‖Γ‖ * ‖w‖ := by
  have h₁ : ‖Γ.1 (radial r i t x) i j * w (radial r i t x) i‖ ≤ ‖Γ‖ * ‖w‖ := by
    rw [norm_mul]
    exact mul_le_mul (left_coefficient_le_norm r Γ _ i j) (component_le_norm r w _ i)
      (norm_nonneg _) (norm_nonneg _)
  have h₂ : ‖Γ.2 (radial r i t x) i j * w (radial r i t x) j‖ ≤ ‖Γ‖ * ‖w‖ := by
    rw [norm_mul]
    exact mul_le_mul (right_coefficient_le_norm r Γ _ i j) (component_le_norm r w _ j)
      (norm_nonneg _) (norm_nonneg _)
  exact (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

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

theorem integralOperator_smul (Γ : Coefficients (ι := ι) r)
    (c : ℝ) (w : Values (ι := ι) r) :
    integralOperator r Γ (c • w) = c • integralOperator r Γ w := by
  ext x i
  change (∑ j, if j = i then 0 else (x j : ℝ) *
    ∫ t in (0 : ℝ)..1, kernel r Γ (c • w) i j x t) =
    c * ∑ j, if j = i then 0 else (x j : ℝ) * ∫ t in (0 : ℝ)..1, kernel r Γ w i j x t
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · simp [hji]
  · simp only [hji, ite_false]
    have hk : kernel r Γ (c • w) i j x = fun t => c * kernel r Γ w i j x t := by
      funext t
      simp only [kernel, Prod.smul_fst, Prod.smul_snd, ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hk, intervalIntegral.integral_const_mul]
    ring

theorem integralOperator_coeff_add (Γ Δ : Coefficients (ι := ι) r) (w : Values (ι := ι) r) :
    integralOperator r (Γ + Δ) w = integralOperator r Γ w + integralOperator r Δ w := by
  ext x i
  change (∑ j, if j = i then 0 else (x j : ℝ) *
    ∫ t in (0 : ℝ)..1, kernel r (Γ + Δ) w i j x t) =
    (∑ j, if j = i then 0 else (x j : ℝ) * ∫ t in (0 : ℝ)..1, kernel r Γ w i j x t) +
    ∑ j, if j = i then 0 else (x j : ℝ) * ∫ t in (0 : ℝ)..1, kernel r Δ w i j x t
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · simp [hji]
  · simp only [hji, ite_false]
    have hk : kernel r (Γ + Δ) w i j x = fun t =>
        kernel r Γ w i j x t + kernel r Δ w i j x t := by
      funext t
      simp only [kernel, Prod.fst_add, Prod.snd_add, ContinuousMap.add_apply, Pi.add_apply]
      ring
    rw [hk, intervalIntegral.integral_add (kernel_integrable r Γ w i j x)
      (kernel_integrable r Δ w i j x)]
    ring

theorem integralOperator_coeff_smul (Γ : Coefficients (ι := ι) r)
    (c : ℝ) (w : Values (ι := ι) r) :
    integralOperator r (c • Γ) w = c • integralOperator r Γ w := by
  ext x i
  change (∑ j, if j = i then 0 else (x j : ℝ) *
    ∫ t in (0 : ℝ)..1, kernel r (c • Γ) w i j x t) =
    c * ∑ j, if j = i then 0 else (x j : ℝ) * ∫ t in (0 : ℝ)..1, kernel r Γ w i j x t
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · simp [hji]
  · simp only [hji, ite_false]
    have hk : kernel r (c • Γ) w i j x = fun t => c * kernel r Γ w i j x t := by
      funext t
      simp only [kernel, Prod.smul_fst, Prod.smul_snd, ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hk, intervalIntegral.integral_const_mul]
    ring

noncomputable def integralOperatorCLM (Γ : Coefficients (ι := ι) r) :
    Values (ι := ι) r →L[ℝ] Values (ι := ι) r :=
  LinearMap.mkContinuous (E := Values (ι := ι) r) (F := Values (ι := ι) r)
    ({ toFun := integralOperator r Γ
       map_add' := by
         intro w z
         have hn : integralOperator r Γ (-z) = -integralOperator r Γ z := by
           simpa only [neg_one_smul] using integralOperator_smul r Γ (-1) z
         simpa only [sub_neg_eq_add, hn] using integralOperator_sub r Γ w (-z)
       map_smul' := integralOperator_smul r Γ } : Values (ι := ι) r →ₗ[ℝ] Values (ι := ι) r)
    (2 * Fintype.card ι * (r : ℝ) * ‖Γ‖) (integralOperator_norm_le r Γ)

theorem integralOperatorCLM_norm_le (Γ : Coefficients (ι := ι) r) :
    ‖integralOperatorCLM r Γ‖ ≤ 2 * Fintype.card ι * (r : ℝ) * ‖Γ‖ :=
  (integralOperatorCLM r Γ).opNorm_le_bound (by positivity) (integralOperator_norm_le r Γ)

noncomputable def integralOperatorBilinear :
    Coefficients (ι := ι) r →L[ℝ] (Values (ι := ι) r →L[ℝ] Values (ι := ι) r) :=
  LinearMap.mkContinuous (E := Coefficients (ι := ι) r)
    (F := Values (ι := ι) r →L[ℝ] Values (ι := ι) r)
    ({ toFun := integralOperatorCLM r
       map_add' := by
         intro Γ Δ
         apply ContinuousLinearMap.ext
         intro w
         exact integralOperator_coeff_add r Γ Δ w
       map_smul' := by
         intro c Γ
         apply ContinuousLinearMap.ext
         intro w
         exact integralOperator_coeff_smul r Γ c w } :
      Coefficients (ι := ι) r →ₗ[ℝ] (Values (ι := ι) r →L[ℝ] Values (ι := ι) r))
    (2 * Fintype.card ι * (r : ℝ)) (integralOperatorCLM_norm_le r)

@[simp] theorem integralOperatorBilinear_apply (Γ : Coefficients (ι := ι) r) (w : Values (ι := ι) r) :
    integralOperatorBilinear r Γ w = integralOperator r Γ w := rfl

end SemiHamiltonian.Darboux.Pair
