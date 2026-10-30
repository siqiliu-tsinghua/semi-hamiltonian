module

public import SemiHamiltonian.Darboux.PairIntegral
public import SemiHamiltonian.Darboux.Residual

/-! The homogeneous residual estimate for two independent Darboux coefficients. -/

@[expose] public section

open scoped NNReal BigOperators
open MeasureTheory

namespace SemiHamiltonian.Darboux.Pair

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

noncomputable def residualKernel (Γ : Coefficients (ι := ι) r) (E : Darboux.Coefficients (ι := ι) r)
    (i j k : ι) (x : Cube ι r) (t : ℝ) : ℝ :=
  let y := radial r i t x
  t * ((Γ.1 y i k * E y i j + Γ.2 y i k * E y k j) -
    (Γ.1 y i j * E y i k + Γ.2 y i j * E y j k))

theorem continuous_residualKernel (Γ : Coefficients (ι := ι) r) (E : Darboux.Coefficients (ι := ι) r) (i j k : ι) :
    Continuous (Function.uncurry (residualKernel r Γ E i j k)) := by
  have hp : Continuous (fun z : Cube ι r × ℝ => radial r i z.2 z.1) :=
    (continuous_radial r i).comp continuous_swap
  unfold residualKernel Function.uncurry
  fun_prop

theorem residualKernel_norm_le (Γ : Coefficients (ι := ι) r) (E : Darboux.Coefficients (ι := ι) r) (i j k : ι)
    (x : Cube ι r) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖residualKernel r Γ E i j k x t‖ ≤ 4 * ‖Γ‖ * ‖E‖ := by
  have hterm (c e : ℝ) (hc : ‖c‖ ≤ ‖Γ‖) (he : ‖e‖ ≤ ‖E‖) :
      ‖c * e‖ ≤ ‖Γ‖ * ‖E‖ := by
    rw [norm_mul]
    exact mul_le_mul hc he (norm_nonneg _) (norm_nonneg _)
  have hleft : ‖Γ.1 (radial r i t x) i k * E (radial r i t x) i j +
      Γ.2 (radial r i t x) i k * E (radial r i t x) k j‖ ≤ 2 * ‖Γ‖ * ‖E‖ := by
    exact (norm_add_le _ _).trans ((add_le_add
      (hterm _ _ (left_coefficient_le_norm r Γ _ i k) (Darboux.coefficient_le_norm r E _ i j))
      (hterm _ _ (right_coefficient_le_norm r Γ _ i k) (Darboux.coefficient_le_norm r E _ k j))).trans_eq (by ring))
  have hright : ‖Γ.1 (radial r i t x) i j * E (radial r i t x) i k +
      Γ.2 (radial r i t x) i j * E (radial r i t x) j k‖ ≤ 2 * ‖Γ‖ * ‖E‖ := by
    exact (norm_add_le _ _).trans ((add_le_add
      (hterm _ _ (left_coefficient_le_norm r Γ _ i j) (Darboux.coefficient_le_norm r E _ i k))
      (hterm _ _ (right_coefficient_le_norm r Γ _ i j) (Darboux.coefficient_le_norm r E _ j k))).trans_eq (by ring))
  rw [residualKernel, norm_mul]
  have ht' : ‖t‖ ≤ 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  exact (mul_le_mul ht' ((norm_sub_le _ _).trans (add_le_add hleft hright))
    (norm_nonneg _) zero_le_one).trans_eq (by ring)

noncomputable def residualOperator (Γ : Coefficients (ι := ι) r) (E : Darboux.Coefficients (ι := ι) r) : Darboux.Coefficients (ι := ι) r where
  toFun x i j := if i = j then 0 else
    ∑ k, if k = i ∨ k = j then 0 else
      (x k : ℝ) * ∫ t in (0 : ℝ)..1, residualKernel r Γ E i j k x t
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hij : i = j
    · simp only [hij, ite_true]; exact continuous_const
    · simp only [hij, ite_false]
      apply continuous_finsetSum
      intro k _
      by_cases hk : k = i ∨ k = j
      · simp only [hk, ite_true]; exact continuous_const
      · simp only [hk, ite_false]
        exact (continuous_subtype_val.comp (continuous_apply k)).mul
          (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
            (continuous_residualKernel r Γ E i j k) 0 1)

theorem residualOperator_norm_le (Γ : Coefficients (ι := ι) r) (E : Darboux.Coefficients (ι := ι) r) :
    ‖residualOperator r Γ E‖ ≤ (4 * Fintype.card ι * (r : ℝ) * ‖Γ‖) * ‖E‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  change ‖if i = j then 0 else ∑ k, _‖ ≤ _
  split_ifs with hij
  · simp; positivity
  · calc
      _ ≤ ∑ _k : ι, (r : ℝ) * (4 * ‖Γ‖ * ‖E‖) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k _
        by_cases hk : k = i ∨ k = j
        · simp [hk]; positivity
        · simp only [hk, ite_false, norm_mul]
          have hi : ‖∫ t in (0 : ℝ)..1, residualKernel r Γ E i j k x t‖ ≤ 4 * ‖Γ‖ * ‖E‖ := by
            apply (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
              (fun t ht => residualKernel_norm_le r Γ E i j k x (by
                have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by simpa using ht
                exact ⟨ht'.1.le, ht'.2⟩))).trans_eq
            simp
          exact mul_le_mul (abs_coordinate_le r x k) hi (norm_nonneg _) r.coe_nonneg
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

/-- Once the homotopy calculation gives this homogeneous integral equation, the
continuous differential residual vanishes. This is not a substitute for deriving
that equation from the PDE compatibility conditions. -/
theorem residual_zero_of_integral_identity (Γ : Coefficients (ι := ι) r) (E : Darboux.Coefficients (ι := ι) r)
    (hsmall : 4 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1)
    (hE : residualOperator r Γ E = E) : E = 0 := by
  have h := residualOperator_norm_le r Γ E
  rw [hE] at h
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg E]

end SemiHamiltonian.Darboux.Pair
