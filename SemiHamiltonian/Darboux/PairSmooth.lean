module

public import SemiHamiltonian.Darboux.PairIntegral
public import SemiHamiltonian.Darboux.Scaling

/-! Smoothness of the general two-coefficient radial integral equation. -/

@[expose] public section

open scoped NNReal Topology ContDiff

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 1024

namespace SemiHamiltonian.Darboux.Pair

variable {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

noncomputable def scaledCoefficients (Γ : Coefficients (ι := ι) r) (x : ι → ℝ) :
    Coefficients (ι := ι) 1 :=
  (Darboux.scaledCoefficients r Γ.1 x, Darboux.scaledCoefficients r Γ.2 x)

theorem scaledCoefficients_left (Γ : Coefficients (ι := ι) r) (x : ι → ℝ)
    (y : Cube ι 1) (i j : ι) :
    (scaledCoefficients r Γ x).1 y i j = x j * Γ.1 (scaledPoint r x y) i j :=
  Darboux.scaledCoefficients_apply r Γ.1 x y i j

theorem scaledCoefficients_right (Γ : Coefficients (ι := ι) r) (x : ι → ℝ)
    (y : Cube ι 1) (i j : ι) :
    (scaledCoefficients r Γ x).2 y i j = x j * Γ.2 (scaledPoint r x y) i j :=
  Darboux.scaledCoefficients_apply r Γ.2 x y i j

theorem scaledCoefficients_norm_le (Γ : Coefficients (ι := ι) r) (x : ι → ℝ) :
    ‖scaledCoefficients r Γ x‖ ≤ ‖x‖ * ‖Γ‖ := by
  apply max_le
  · exact (Darboux.scaledCoefficients_norm_le r Γ.1 x).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le Γ) (norm_nonneg x))
  · exact (Darboux.scaledCoefficients_norm_le r Γ.2 x).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le Γ) (norm_nonneg x))

def SmoothCoefficients (Γ : Coefficients (ι := ι) r) : Prop :=
  ContDiffOn ℝ ∞ (fun x => Γ.1 (clamp r x)) (Metric.ball 0 (r : ℝ)) ∧
    ContDiffOn ℝ ∞ (fun x => Γ.2 (clamp r x)) (Metric.ball 0 (r : ℝ))

theorem scaledCoefficients_contDiff (Γ : Coefficients (ι := ι) r)
    (hΓ : SmoothCoefficients r Γ) :
    ContDiffOn ℝ ∞ (scaledCoefficients r Γ) (Metric.ball 0 (r : ℝ)) :=
  (Darboux.scaledCoefficients_contDiff r Γ.1 hΓ.1).prodMk
    (Darboux.scaledCoefficients_contDiff r Γ.2 hΓ.2)

theorem scaledValues_fixedPoint (Γ : Coefficients (ι := ι) r) (φ : ι → C(ℝ, ℝ))
    (w : Values (ι := ι) r) (hw : picard r Γ (axisDataOfFunctions r φ) w = w)
    {x : ι → ℝ} (hx : x ∈ Metric.ball 0 (r : ℝ)) :
    scaledInitial φ x + integralOperator 1 (scaledCoefficients r Γ x) (scaledValues r w x) =
      scaledValues r w x := by
  have hxn : ‖x‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  ext y i
  have h := congrArg (fun z : Values (ι := ι) r => z (scaledPoint r x y) i) hw
  change φ i (scaledPoint r x y i) + (∑ j, if j = i then 0 else
    (scaledPoint r x y j : ℝ) * ∫ t in (0 : ℝ)..1, kernel r Γ w i j (scaledPoint r x y) t) = _ at h
  change scaledInitial φ x y i + (∑ j, if j = i then 0 else
    (y j : ℝ) * ∫ t in (0 : ℝ)..1,
      kernel 1 (scaledCoefficients r Γ x) (scaledValues r w x) i j y t) = _
  rw [scaledInitial_apply, ← scaledPoint_coordinate r hxn.le y i]
  change _ = w (scaledPoint r x y) i
  rw [← h]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · simp [hji]
  · simp only [hji, ite_false]
    have hk : kernel 1 (scaledCoefficients r Γ x) (scaledValues r w x) i j y =
        fun t => x j * kernel r Γ w i j (scaledPoint r x y) t := by
      funext t
      simp only [kernel, scaledCoefficients_left, scaledCoefficients_right, scaledValues, ContinuousMap.comp_apply,
        scaledPoint_radial r hxn]
      ring
    rw [hk, intervalIntegral.integral_const_mul, scaledPoint_coordinate r hxn.le y j]
    ring

/-- A continuous fixed point with smooth data is smooth on the same open cube.
No derivative-order-dependent shrinking of the domain is used. -/
theorem integralFixedPoint_contDiff (Γ : Coefficients (ι := ι) r)
    (φ : ι → C(ℝ, ℝ)) (w : Values (ι := ι) r)
    (hΓ : SmoothCoefficients r Γ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hsmall : 2 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1)
    (hw : picard r Γ (axisDataOfFunctions r φ) w = w) :
    ContDiffOn ℝ ∞ (fun x => w (clamp r x)) (Metric.ball 0 (r : ℝ)) := by
  let T : (ι → ℝ) → Values (ι := ι) 1 →L[ℝ] Values (ι := ι) 1 :=
    fun x => integralOperatorBilinear 1 (scaledCoefficients r Γ x)
  have hT : ContDiffOn ℝ ∞ T (Metric.ball 0 (r : ℝ)) := by
    have hlin : ContDiff ℝ ∞ (integralOperatorBilinear (ι := ι) 1) := ContinuousLinearMap.contDiff _
    exact hlin.comp_contDiffOn (scaledCoefficients_contDiff r Γ hΓ)
  have hs : ∀ x ∈ Metric.ball (0 : ι → ℝ) (r : ℝ), ‖T x‖ < 1 := by
    intro x hx
    have hx' : ‖x‖ ≤ r := (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
    have h₁ := integralOperatorCLM_norm_le 1 (scaledCoefficients r Γ x)
    have h₂ := mul_le_mul_of_nonneg_left (scaledCoefficients_norm_le r Γ x)
      (by positivity : 0 ≤ 2 * (Fintype.card ι : ℝ))
    have h₃ := mul_le_mul_of_nonneg_right hx'
      (by positivity : 0 ≤ 2 * (Fintype.card ι : ℝ) * ‖Γ‖)
    change ‖integralOperatorCLM 1 (scaledCoefficients r Γ x)‖ < 1
    norm_num only [NNReal.coe_one, mul_one] at h₁
    nlinarith
  have hv := contDiffOn_linearFixedPoint Metric.isOpen_ball T (scaledInitial φ) (scaledValues r w)
    hT (scaledInitial_contDiff φ hφ).contDiffOn hs
    (fun x hx => scaledValues_fixedPoint r Γ φ w hw hx)
  let corner : Cube ι 1 := fun _ => ⟨1, by norm_num, by norm_num⟩
  have hcorner : ∀ x : ι → ℝ, scaleFamily corner x = x := by
    intro x
    funext i
    simp [corner]
  have heval : ContDiff ℝ ∞ (ContinuousMap.evalCLM ℝ (M := ι → ℝ) corner) :=
    ContinuousLinearMap.contDiff _
  have h := heval.comp_contDiffOn hv
  simpa only [Function.comp_def, ContinuousMap.evalCLM_apply, scaledValues,
    ContinuousMap.comp_apply, scaledPoint, ContinuousMap.coe_mk, hcorner] using h

end SemiHamiltonian.Darboux.Pair
