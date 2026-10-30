module

public import SemiHamiltonian.Darboux.CurveC1
public import SemiHamiltonian.Darboux.Scaling

/-! Uniform dilations commute with the diagonal data projection. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal Topology ContDiff Classical
open Set Filter MeasureTheory

namespace SemiHamiltonian.Darboux

variable {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

theorem valuesOfJets_integralOperator (Γ : JetCoefficients (ι := ι) r) (w : JetValues (ι := ι) r) :
    valuesOfJets r (jetIntegralOperator r Γ w) =
      integralOperator r (coefficientValues r Γ) (valuesOfJets r w) := by
  ext x i
  change jetEval r x (∑ j, if j = i then 0 else jetMul (coordinateJet r j)
    (∫ t in (0 : ℝ)..1, jetKernel r Γ w i j t)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · simp [hji]
  · simp only [hji, ite_false]
    change (x j : ℝ) * (∫ t in (0 : ℝ)..1, jetKernel r Γ w i j t).1 x = _
    rw [jetEval_integral r x _ (jetKernel_integrable r Γ w i j)]
    rfl

theorem valuesOfJets_curveOperator (Γ : JetCoefficients (ι := ι) r) (w : JetValues (ι := ι) r) :
    valuesOfJets r (curveJetOperator r Γ w) =
      curveOperator r (coefficientValues r Γ) (valuesOfJets r w) := by
  change valuesOfJets r (jetIntegralOperator r Γ w) -
    curveProjection r (valuesOfJets r (jetIntegralOperator r Γ w)) = _
  rw [valuesOfJets_integralOperator]
  rfl

theorem scaledValues_integralOperator (Γ : Coefficients (ι := ι) r) (w : Values (ι := ι) r)
    {x : ι → ℝ} (hx : ‖x‖ < r) :
    scaledValues r (integralOperator r Γ w) x =
      integralOperator 1 (scaledCoefficients r Γ x) (scaledValues r w x) := by
  ext y i
  change (∑ j, if j = i then 0 else (scaledPoint r x y j : ℝ) *
      ∫ t in (0 : ℝ)..1, kernel r Γ w i j (scaledPoint r x y) t) =
    ∑ j, if j = i then 0 else (y j : ℝ) * ∫ t in (0 : ℝ)..1,
      kernel 1 (scaledCoefficients r Γ x) (scaledValues r w x) i j y t
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · simp [hji]
  · simp only [hji, ite_false]
    have hk : kernel 1 (scaledCoefficients r Γ x) (scaledValues r w x) i j y =
        fun t => x j * kernel r Γ w i j (scaledPoint r x y) t := by
      funext t
      simp only [kernel, scaledCoefficients_apply, scaledValues, ContinuousMap.comp_apply,
        scaledPoint_radial r hx]
      ring
    rw [hk, intervalIntegral.integral_const_mul, scaledPoint_coordinate r hx.le y j]
    ring

noncomputable def uniformScale : ℝ →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ ℝ)

@[simp] theorem uniformScale_apply (s : ℝ) (i : ι) : uniformScale (ι := ι) s i = s := rfl

theorem uniformScale_norm_le (s : ℝ) : ‖uniformScale (ι := ι) s‖ ≤ |s| := by
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg s)).mpr
  intro i
  exact le_rfl

theorem uniformScale_maps_ball :
    MapsTo (uniformScale (ι := ι)) (Metric.ball 0 (r : ℝ)) (Metric.ball 0 (r : ℝ)) := by
  intro s hs
  have hn : |s| < r := by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hs
  simpa only [Metric.mem_ball, dist_zero_right] using (uniformScale_norm_le (ι := ι) s).trans_lt hn

theorem scaledValues_curveProjection (w : Values (ι := ι) r) (s : ℝ) :
    scaledValues r (curveProjection r w) (uniformScale s) =
      curveProjection 1 (scaledValues r w (uniformScale s)) := by
  ext y i
  rfl

theorem scaledValues_curve_fixedPoint (Γ : Coefficients (ι := ι) r) (φ : ι → C(ℝ, ℝ))
    (w : Values (ι := ι) r)
    (hw : initial r (axisDataOfFunctions r φ) + curveOperator r Γ w = w)
    {s : ℝ} (hs : s ∈ Metric.ball 0 (r : ℝ)) :
    scaledInitial φ (uniformScale s) +
      curveOperator 1 (scaledCoefficients r Γ (uniformScale s)) (scaledValues r w (uniformScale s)) =
        scaledValues r w (uniformScale s) := by
  have hx : ‖uniformScale (ι := ι) s‖ < r := by
    simpa only [Metric.mem_ball, dist_zero_right] using uniformScale_maps_ball (ι := ι) r hs
  have hh := congrArg (fun z : Values (ι := ι) r => scaledValues r z (uniformScale s)) hw
  have hinit : scaledValues r (initial r (axisDataOfFunctions r φ)) (uniformScale s) =
      scaledInitial φ (uniformScale s) := by
    ext y i
    rw [scaledInitial_apply]
    exact congrArg (φ i) (scaledPoint_coordinate r hx.le y i)
  change scaledValues r (initial r (axisDataOfFunctions r φ)) (uniformScale s) +
    (scaledValues r (integralOperator r Γ w) (uniformScale s) -
      scaledValues r (curveProjection r (integralOperator r Γ w)) (uniformScale s)) = _ at hh
  rw [hinit, scaledValues_curveProjection, scaledValues_integralOperator r Γ w hx] at hh
  exact hh

/-- Smooth dependence on uniform dilation, even before compatibility is used. -/
theorem curveFixedPoint_uniformScale_contDiff (Γ : Coefficients (ι := ι) r)
    (φ : ι → C(ℝ, ℝ)) (w : Values (ι := ι) r)
    (hΓ : ContDiffOn ℝ ∞ (fun x => Γ (clamp r x)) (Metric.ball 0 (r : ℝ)))
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hsmall : 4 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1)
    (hw : initial r (axisDataOfFunctions r φ) + curveOperator r Γ w = w) :
    ContDiffOn ℝ ∞ (fun s => scaledValues r w (uniformScale s)) (Metric.ball 0 (r : ℝ)) := by
  let T := fun s : ℝ => curveOperator 1 (scaledCoefficients r Γ (uniformScale s))
  have hc := (scaledCoefficients_contDiff r Γ hΓ).comp (ContinuousLinearMap.contDiff _).contDiffOn
    (uniformScale_maps_ball (ι := ι) r)
  have hl : ContDiff ℝ ∞ (integralOperatorBilinear (ι := ι) 1) := ContinuousLinearMap.contDiff _
  have ht := hl.comp_contDiffOn hc
  have hT : ContDiffOn ℝ ∞ T (Metric.ball 0 (r : ℝ)) :=
    ht.sub (contDiffOn_const.clm_comp ht)
  have hs : ∀ s ∈ Metric.ball (0 : ℝ) (r : ℝ), ‖T s‖ < 1 := by
    intro s hs
    have hx : ‖uniformScale (ι := ι) s‖ ≤ r := by
      exact (show ‖uniformScale (ι := ι) s‖ < r by
        simpa only [Metric.mem_ball, dist_zero_right] using uniformScale_maps_ball (ι := ι) r hs).le
    have hb := curveOperator_norm_le 1 (scaledCoefficients r Γ (uniformScale s))
    have hc' := scaledCoefficients_norm_le r Γ (uniformScale s)
    have hm := mul_le_mul_of_nonneg_right hx (norm_nonneg Γ)
    have hn := mul_le_mul_of_nonneg_left (hc'.trans hm)
      (by positivity : 0 ≤ 4 * (Fintype.card ι : ℝ))
    norm_num only [NNReal.coe_one, mul_one] at hb
    exact (hb.trans (by nlinarith)).trans_lt hsmall
  exact contDiffOn_linearFixedPoint Metric.isOpen_ball T
    (fun s => scaledInitial φ (uniformScale s)) (fun s => scaledValues r w (uniformScale s))
    hT ((scaledInitial_contDiff φ hφ).comp (ContinuousLinearMap.contDiff _)).contDiffOn hs
    (fun _ hs => scaledValues_curve_fixedPoint r Γ φ w hw hs)

end SemiHamiltonian.Darboux
