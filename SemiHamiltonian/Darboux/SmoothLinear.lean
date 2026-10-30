module

public import SemiHamiltonian.Darboux.IntegralEquation
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Smooth dependence of the linear integral equation on its data. -/

@[expose] public section

open scoped NNReal Topology ContDiff

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 1024

namespace SemiHamiltonian.Darboux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

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
      simp only [kernel, ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul]
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
      simp only [kernel, ContinuousMap.add_apply, Pi.add_apply]
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
      simp only [kernel, ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul]
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

section Parameters

variable {P B : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- Smoothness of the solution of a parameter-dependent affine contraction.
Only the zeroth-order operator norm has to be small. -/
theorem contDiffOn_linearFixedPoint {U : Set P} (hU : IsOpen U)
    (T : P → B →L[ℝ] B) (A w : P → B)
    (hT : ContDiffOn ℝ ∞ T U) (hA : ContDiffOn ℝ ∞ A U)
    (hsmall : ∀ x ∈ U, ‖T x‖ < 1)
    (hfix : ∀ x ∈ U, A x + T x (w x) = w x) : ContDiffOn ℝ ∞ w U := by
  have he : ∀ x ∈ U, Ring.inverse (1 - T x) (A x) = w x := by
    intro x hx
    have hu := IsUnit.one_sub_of_norm_lt_one (hsmall x hx)
    have hAx : A x = (1 - T x) (w x) := by
      change A x = w x - T x (w x)
      exact eq_sub_iff_add_eq.mpr (hfix x hx)
    rw [hAx]
    change (Ring.inverse (1 - T x) * (1 - T x)) (w x) = w x
    rw [Ring.inverse_mul_cancel _ hu]
    rfl
  apply ContDiffOn.congr (f := fun x => Ring.inverse (1 - T x) (A x)) _
    (fun x hx => (he x hx).symm)
  intro x hx
  have hu := IsUnit.one_sub_of_norm_lt_one (hsmall x hx)
  have hi : ContDiffAt ℝ ∞ Ring.inverse (1 - T x) := by
    simpa only [hu.unit_spec] using (contDiffAt_ringInverse ℝ hu.unit (n := ∞))
  exact (hi.comp x (contDiffAt_const.sub (hT.contDiffAt (hU.mem_nhds hx)))).clm_apply
    (hA.contDiffAt (hU.mem_nhds hx)) |>.contDiffWithinAt

end Parameters

end SemiHamiltonian.Darboux
