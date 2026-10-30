module

public import SemiHamiltonian.Darboux.CurveScaling
public import SemiHamiltonian.Darboux.SmoothExistence

/-! Smooth diagonal-curve Darboux data give a smooth solution on one common
open cube. Uniform dilations first give smooth axis traces; the original
coordinate-dilation argument then gives full joint smoothness. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 1024

open scoped NNReal Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Darboux

variable {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

theorem scaledInitial_contDiff_local (φ : ι → C(ℝ, ℝ))
    (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) (Metric.ball 0 (r : ℝ))) :
    ContDiffOn ℝ ∞ (scaledInitial φ) (Metric.ball 0 (r : ℝ)) := by
  apply contDiffOn_compactLinearFamily (scaleFamily (ι := ι))
    Metric.isOpen_ball Metric.isOpen_ball (scaleFamily_maps_ball r)
  apply contDiffOn_pi.mpr
  intro i
  apply (hφ i).comp (contDiff_apply ℝ (fun _ : ι => ℝ) i).contDiffOn
  intro x hx
  have hn : ‖x‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  simpa only [Metric.mem_ball, dist_zero_right] using (norm_le_pi_norm x i).trans_lt hn

theorem integralFixedPoint_contDiff_localAxis (Γ : Coefficients (ι := ι) r)
    (φ : ι → C(ℝ, ℝ)) (w : Values (ι := ι) r)
    (hΓ : ContDiffOn ℝ ∞ (fun x => Γ (clamp r x)) (Metric.ball 0 (r : ℝ)))
    (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) (Metric.ball 0 (r : ℝ)))
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
    hT (scaledInitial_contDiff_local r φ hφ) hs (fun x hx => scaledValues_fixedPoint r Γ φ w hw hx)
  let corner : Cube ι 1 := fun _ => ⟨1, by norm_num, by norm_num⟩
  have hcorner : ∀ x : ι → ℝ, scaleFamily corner x = x := by
    intro x
    funext i
    simp [corner]
  have heval : ContDiff ℝ ∞ (ContinuousMap.evalCLM ℝ (M := ι → ℝ) corner) :=
    ContinuousLinearMap.contDiff _
  have hh := heval.comp_contDiffOn hv
  simpa only [Function.comp_def, ContinuousMap.evalCLM_apply, scaledValues,
    ContinuousMap.comp_apply, scaledPoint, ContinuousMap.coe_mk, hcorner] using hh

noncomputable def axisTrace (w : Values (ι := ι) r) (i : ι) : C(ℝ, ℝ) :=
  ⟨fun s => w (clamp r (Pi.single i s)) i, by
    have hs : Continuous (fun s : ℝ => (Pi.single i s : ι → ℝ)) := by
      apply continuous_pi
      intro j
      by_cases hji : j = i
      · subst j
        simp only [Pi.single_eq_same]
        exact continuous_id
      · simp only [Pi.single_eq_of_ne hji]
        exact continuous_const
    exact (continuous_apply i).comp (w.continuous.comp ((clamp r).continuous.comp hs))⟩

theorem axis_eq_clamp (i : ι) (x : Cube ι r) :
    axis r i x = clamp r (Pi.single i (x i : ℝ)) := by
  have hn : ‖(Pi.single i (x i : ℝ) : ι → ℝ)‖ ≤ r := by
    simpa only [Pi.norm_single, Real.norm_eq_abs] using abs_coordinate_le r x i
  funext j
  apply Subtype.ext
  have he := congrFun (point_clamp_of_norm_le r hn) j
  change ((clamp r (Pi.single i (x i : ℝ))) j : ℝ) = (Pi.single i (x i : ℝ) : ι → ℝ) j at he
  rw [he]
  by_cases hji : j = i
  · subst j; simp
  · rw [axis_other r i j hji x]; simp [hji]

theorem curveFixedPoint_axisTrace_contDiff (Γ : Coefficients (ι := ι) r)
    (φ : ι → C(ℝ, ℝ)) (w : Values (ι := ι) r)
    (hΓ : ContDiffOn ℝ ∞ (fun x => Γ (clamp r x)) (Metric.ball 0 (r : ℝ)))
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hsmall : 4 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1)
    (hw : initial r (axisDataOfFunctions r φ) + curveOperator r Γ w = w) (i : ι) :
    ContDiffOn ℝ ∞ (axisTrace r w i) (Metric.ball 0 (r : ℝ)) := by
  have hs := curveFixedPoint_uniformScale_contDiff r Γ φ w hΓ hφ hsmall hw
  let y : Cube ι 1 := clamp 1 (Pi.single i 1)
  have hy (s : ℝ) : scaleFamily y (uniformScale s) = Pi.single i s := by
    have hn : ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ ≤ (1 : ℝ≥0) := by
      simp only [Pi.norm_single, norm_one, NNReal.coe_one, le_refl]
    have he := point_clamp_of_norm_le 1 hn
    funext j
    change point 1 y j * s = (Pi.single i s : ι → ℝ) j
    rw [congrFun he j]
    by_cases hji : j = i <;> simp [Pi.single_apply, hji]
  have heval : ContDiff ℝ ∞ (ContinuousMap.evalCLM ℝ (M := ι → ℝ) y) :=
    ContinuousLinearMap.contDiff _
  have hh := (contDiffOn_pi.mp (heval.comp_contDiffOn hs)) i
  simpa only [Function.comp_def, ContinuousMap.evalCLM_apply, scaledValues,
    ContinuousMap.comp_apply, scaledPoint, ContinuousMap.coe_mk, hy, axisTrace] using hh

/-- Full joint C∞ regularity of the actual C¹ curve-data solution. -/
theorem curveC1Solution_contDiff (hr : 0 < r) (Γ : JetCoefficients (ι := ι) r)
    (φ : ι → C(ℝ, ℝ)) (w : JetValues (ι := ι) r)
    (hw : ∀ i, IsCubeJet r (w i))
    (hpde : ∀ (x : Cube ι r) (i j : ι), i ≠ j →
      jetDiff r x (Pi.single j 1) (w i) = (Γ i j).1 x * ((w j).1 x - (w i).1 x))
    (hΓ : ContDiffOn ℝ ∞ (fun x => coefficientValues r Γ (clamp r x)) (Metric.ball 0 (r : ℝ)))
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hsmall : 4 * Fintype.card ι * (r : ℝ) * ‖coefficientValues r Γ‖ < 1)
    (hfix : initial r (axisDataOfFunctions r φ) +
      curveOperator r (coefficientValues r Γ) (valuesOfJets r w) = valuesOfJets r w) :
    ContDiffOn ℝ ∞ (fun x => valuesOfJets r w (clamp r x)) (Metric.ball 0 (r : ℝ)) := by
  have ht := curveFixedPoint_axisTrace_contDiff r (coefficientValues r Γ) φ (valuesOfJets r w)
    hΓ hφ hsmall hfix
  have haxis : ∀ i x, (w i).1 (axis r i x) =
      axisDataOfFunctions r (axisTrace r (valuesOfJets r w)) i (x i) := by
    intro i x
    rw [axis_eq_clamp]
    rfl
  have hs : 2 * Fintype.card ι * (r : ℝ) * ‖coefficientValues r Γ‖ < 1 := by
    have hn : 0 ≤ 2 * Fintype.card ι * (r : ℝ) * ‖coefficientValues r Γ‖ := by positivity
    linarith
  exact integralFixedPoint_contDiff_localAxis r (coefficientValues r Γ)
    (axisTrace r (valuesOfJets r w)) (valuesOfJets r w) hΓ ht hs
    (cubeJet_fixedPoint r hr Γ _ w hw hpde haxis)

theorem exists_smooth_darboux_diagonalCurve (hr : 0 < r)
    (Γ : JetCoefficients (ι := ι) r) (hΓ : ∀ i j, IsCubeJet r (Γ i j))
    (hc : IsDarbouxCompatible r Γ)
    (hΓsmooth : ContDiffOn ℝ ∞ (fun x => coefficientValues r Γ (clamp r x)) (Metric.ball 0 (r : ℝ)))
    (hsmall : 16 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1)
    (φ : ι → C(ℝ, ℝ)) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    ∃ w : JetValues (ι := ι) r,
      (∀ i, IsCubeJet r (w i)) ∧
      (∀ (x : Cube ι r) (i j : ι), i ≠ j →
        jetDiff r x (Pi.single j 1) (w i) = (Γ i j).1 x * ((w j).1 x - (w i).1 x)) ∧
      (∀ (s : Icc (-(r : ℝ)) r) i, (w i).1 (diagonalPoint r s) = φ i s) ∧
      ContDiffOn ℝ ∞ (fun x => valuesOfJets r w (clamp r x)) (Metric.ball 0 (r : ℝ)) := by
  let ψ : ι → C(ℝ, ℝ) := fun i => ⟨deriv (φ i), (hφ i).continuous_deriv (by simp)⟩
  have hd : ∀ i (s : ℝ), |s| < r → HasDerivAt (φ i) (ψ i s) s :=
    fun i s _ => ((hφ i).differentiable (by simp) s).hasDerivAt
  obtain ⟨w, hw, hpde, htrace, hfix⟩ := exists_C1_darboux_diagonalCurve r hr Γ
    (initialJets r φ ψ) hΓ (initialJets_isCubeJet r hr φ ψ hd) hc
    (initialJets_transverse r φ ψ) hsmall
  have hfixv := congrArg (valuesOfJets r) hfix
  change initial r (axisDataOfFunctions r φ) + valuesOfJets r (curveJetOperator r Γ w) = _ at hfixv
  rw [valuesOfJets_curveOperator] at hfixv
  have hs : 4 * Fintype.card ι * (r : ℝ) * ‖coefficientValues r Γ‖ < 1 := by
    have hb := mul_le_mul_of_nonneg_left (coefficientValues_norm_le r Γ)
      (by positivity : 0 ≤ 4 * (Fintype.card ι : ℝ) * (r : ℝ))
    have hn : 0 ≤ 4 * (Fintype.card ι : ℝ) * (r : ℝ) * ‖Γ‖ := by positivity
    nlinarith
  exact ⟨w, hw, hpde, htrace, curveC1Solution_contDiff r hr Γ φ w hw hpde hΓsmooth hφ hs hfixv⟩

end SemiHamiltonian.Darboux
