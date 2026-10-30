module

public import SemiHamiltonian.Darboux.IntegralEquation

/-! The homogeneous equation for the differential residual and its small-cube estimate. -/

@[expose] public section

open scoped NNReal BigOperators
open MeasureTheory

namespace SemiHamiltonian.Darboux

variable {ι : Type*}

/-- The coefficient calculation needed after differentiating the integral equation.
Here `J i j` stands for the actual partial derivative `∂ⱼwⁱ`. -/
theorem residual_curl_identity (Γ J : ι → ι → ℝ) (w : ι → ℝ) (i j k : ι)
    (dji dik : ℝ)
    (hji : dji = Γ i k * Γ k j + Γ i j * Γ j k - Γ i k * Γ i j)
    (hik : dik = Γ i j * Γ j k + Γ i k * Γ k j - Γ i j * Γ i k) :
    dji * (w k - w i) + Γ i k * (J k j - J i j) -
      (dik * (w j - w i) + Γ i j * (J j k - J i k)) =
    Γ i k * ((J k j - Γ k j * (w j - w k)) - (J i j - Γ i j * (w j - w i))) -
      Γ i j * ((J j k - Γ j k * (w k - w j)) - (J i k - Γ i k * (w k - w i))) := by
  rw [hji, hik]
  ring

variable [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

noncomputable def residualKernel (Γ E : Coefficients (ι := ι) r)
    (i j k : ι) (x : Cube ι r) (t : ℝ) : ℝ :=
  let y := radial r i t x
  t * (Γ y i k * (E y k j - E y i j) - Γ y i j * (E y j k - E y i k))

theorem continuous_residualKernel (Γ E : Coefficients (ι := ι) r) (i j k : ι) :
    Continuous (Function.uncurry (residualKernel r Γ E i j k)) := by
  have hp : Continuous (fun z : Cube ι r × ℝ => radial r i z.2 z.1) :=
    (continuous_radial r i).comp continuous_swap
  unfold residualKernel Function.uncurry
  fun_prop

theorem residualKernel_norm_le (Γ E : Coefficients (ι := ι) r) (i j k : ι)
    (x : Cube ι r) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖residualKernel r Γ E i j k x t‖ ≤ 4 * ‖Γ‖ * ‖E‖ := by
  have hd (a b c d : ι) :
      ‖E (radial r i t x) a b - E (radial r i t x) c d‖ ≤ 2 * ‖E‖ := by
    have h := (norm_sub_le _ _).trans (add_le_add
      (coefficient_le_norm r E (radial r i t x) a b)
      (coefficient_le_norm r E (radial r i t x) c d))
    linarith
  have hterm (a b c d e : ι) :
      ‖Γ (radial r i t x) i a * (E (radial r i t x) b c - E (radial r i t x) d e)‖ ≤
        2 * ‖Γ‖ * ‖E‖ := by
    rw [norm_mul]
    calc
      _ ≤ ‖Γ‖ * (2 * ‖E‖) := mul_le_mul (coefficient_le_norm r Γ _ i a)
        (hd b c d e) (norm_nonneg _) (norm_nonneg Γ)
      _ = _ := by ring
  rw [residualKernel, norm_mul]
  have ht' : ‖t‖ ≤ 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  calc
    _ ≤ 1 * (2 * ‖Γ‖ * ‖E‖ + 2 * ‖Γ‖ * ‖E‖) := mul_le_mul ht'
      ((norm_sub_le _ _).trans (add_le_add (hterm k k j i j) (hterm j j k i k)))
      (norm_nonneg _) zero_le_one
    _ = _ := by ring

noncomputable def residualOperator (Γ E : Coefficients (ι := ι) r) : Coefficients (ι := ι) r where
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

theorem residualOperator_norm_le (Γ E : Coefficients (ι := ι) r) :
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
theorem residual_zero_of_integral_identity (Γ E : Coefficients (ι := ι) r)
    (hsmall : 4 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1)
    (hE : residualOperator r Γ E = E) : E = 0 := by
  have h := residualOperator_norm_le r Γ E
  rw [hE] at h
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg E]

end SemiHamiltonian.Darboux
