module

public import SemiHamiltonian.Darboux.Scaling
public import SemiHamiltonian.Darboux.LocalC1
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! C∞ regularity and local existence and uniqueness for the Darboux system. -/

@[expose] public section

open scoped NNReal Topology ContDiff

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 1024

namespace SemiHamiltonian.Darboux

variable {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

/-- A continuous fixed point with smooth data is smooth on the same open cube.
No derivative-order-dependent shrinking of the domain is used. -/
theorem integralFixedPoint_contDiff (Γ : Coefficients (ι := ι) r)
    (φ : ι → C(ℝ, ℝ)) (w : Values (ι := ι) r)
    (hΓ : ContDiffOn ℝ ∞ (fun x => Γ (clamp r x)) (Metric.ball 0 (r : ℝ)))
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

theorem C1DarbouxSolution_contDiff (hr : 0 < r) (Γ : JetCoefficients (ι := ι) r)
    (φ : ι → C(ℝ, ℝ)) {u : Values (ι := ι) r}
    (hu : IsC1DarbouxSolution r Γ (axisDataOfFunctions r φ) u)
    (hΓ : ContDiffOn ℝ ∞ (fun x => coefficientValues r Γ (clamp r x)) (Metric.ball 0 (r : ℝ)))
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hsmall : 2 * Fintype.card ι * (r : ℝ) * ‖coefficientValues r Γ‖ < 1) :
    ContDiffOn ℝ ∞ (fun x => u (clamp r x)) (Metric.ball 0 (r : ℝ)) := by
  obtain ⟨w, rfl, hw, hpw, haw⟩ := hu
  exact integralFixedPoint_contDiff r (coefficientValues r Γ) φ (valuesOfJets r w) hΓ hφ hsmall
    (cubeJet_fixedPoint r hr Γ (axisDataOfFunctions r φ) w hw hpw haw)

/-- Genuine C¹ solutions with all orders of interior regularity. The C¹ part
also records continuous extension of the first derivatives to the boundary. -/
def IsSmoothDarbouxSolution (Γ : JetCoefficients (ι := ι) r) (φ : ι → C(ℝ, ℝ))
    (u : Values (ι := ι) r) : Prop :=
  IsC1DarbouxSolution r Γ (axisDataOfFunctions r φ) u ∧
    ContDiffOn ℝ ∞ (fun x => u (clamp r x)) (Metric.ball 0 (r : ℝ))

theorem existsUnique_smooth_darboux_axisData (hr : 0 < r)
    (Γ : JetCoefficients (ι := ι) r) (hΓ : ∀ i j, IsCubeJet r (Γ i j))
    (hc : IsDarbouxCompatible r Γ)
    (hΓsmooth : ContDiffOn ℝ ∞ (fun x => coefficientValues r Γ (clamp r x)) (Metric.ball 0 (r : ℝ)))
    (hsmall : 8 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1)
    (φ : ι → C(ℝ, ℝ)) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    ∃! u : Values (ι := ι) r, IsSmoothDarbouxSolution r Γ φ u := by
  let ψ : ι → C(ℝ, ℝ) := fun i => ⟨deriv (φ i), (hφ i).continuous_deriv (by simp)⟩
  have hd : ∀ i (s : ℝ), |s| < r → HasDerivAt (φ i) (ψ i s) s :=
    fun i s _ => ((hφ i).differentiable (by simp) s).hasDerivAt
  obtain ⟨u, hu, huniq⟩ := existsUnique_C1_darboux_axisData r hr Γ hΓ hc hsmall φ ψ hd
  have hs : 2 * Fintype.card ι * (r : ℝ) * ‖coefficientValues r Γ‖ < 1 := by
    have hb := mul_le_mul_of_nonneg_left (coefficientValues_norm_le r Γ)
      (by positivity : 0 ≤ 2 * (Fintype.card ι : ℝ) * (r : ℝ))
    have hp : 0 ≤ 2 * (Fintype.card ι : ℝ) * (r : ℝ) * ‖Γ‖ := by positivity
    nlinarith
  exact ⟨u, ⟨hu, C1DarbouxSolution_contDiff r hr Γ φ hu hΓsmooth hφ hs⟩,
    fun v hv => huniq v hv.1⟩

variable {r R : ℝ≥0}

theorem coefficientValues_restrict_contDiff (Γ : JetCoefficients (ι := ι) R) (hr : r ≤ R)
    (hΓ : ContDiffOn ℝ ∞ (fun x => coefficientValues R Γ (clamp R x)) (Metric.ball 0 (R : ℝ))) :
    ContDiffOn ℝ ∞ (fun x => coefficientValues r (restrictJetCoefficients Γ hr) (clamp r x))
      (Metric.ball 0 (r : ℝ)) := by
  apply (hΓ.mono (Metric.ball_subset_ball (show (r : ℝ) ≤ R from hr))).congr
  intro x hx
  have hn : ‖x‖ ≤ r := (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
  have he : cubeInclusion hr (clamp r x) = clamp R x := by
    funext i
    apply Subtype.ext
    exact (congrFun (point_clamp_of_norm_le r hn) i).trans
      (congrFun (point_clamp_of_norm_le R (hn.trans hr)) i).symm
  change coefficientValues R Γ (cubeInclusion hr (clamp r x)) = _
  rw [he]

/-- Local C∞ Darboux existence and uniqueness, uniformly in arbitrary smooth
single-variable axis data. One positive radius works for every derivative order. -/
theorem local_existsUnique_smooth_darboux (hR : 0 < R)
    (Γ : JetCoefficients (ι := ι) R) (hΓ : ∀ i j, IsCubeJet R (Γ i j))
    (hc : IsDarbouxCompatible R Γ)
    (hΓsmooth : ContDiffOn ℝ ∞ (fun x => coefficientValues R Γ (clamp R x)) (Metric.ball 0 (R : ℝ))) :
    ∃ (r : ℝ≥0) (hr : r ≤ R), 0 < r ∧
      ∀ (φ : ι → C(ℝ, ℝ)), (∀ i, ContDiff ℝ ∞ (φ i)) →
        ∃! u : Values (ι := ι) r, IsSmoothDarbouxSolution r (restrictJetCoefficients Γ hr) φ u := by
  obtain ⟨ε, hε, hεsmall⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1)
    (8 * Fintype.card ι * ‖Γ‖)
  let r : ℝ≥0 := min R ⟨ε, hε.le⟩
  have hr : r ≤ R := min_le_left _ _
  have hrpos : 0 < r := lt_min hR hε
  have hrε : (r : ℝ) ≤ ε := min_le_right (R : ℝ) ε
  have hs : 8 * Fintype.card ι * (r : ℝ) * ‖restrictJetCoefficients Γ hr‖ < 1 := by
    have h₁ := mul_le_mul_of_nonneg_left (restrictJetCoefficients_norm_le Γ hr hR)
      (by positivity : 0 ≤ 8 * (Fintype.card ι : ℝ) * (r : ℝ))
    have h₂ := mul_le_mul_of_nonneg_right hrε
      (by positivity : 0 ≤ 8 * (Fintype.card ι : ℝ) * ‖Γ‖)
    nlinarith
  refine ⟨r, hr, hrpos, fun φ hφ => ?_⟩
  exact existsUnique_smooth_darboux_axisData r hrpos (restrictJetCoefficients Γ hr)
    (fun i j => restrictJet_isCubeJet hr hrpos hR _ (hΓ i j))
    (restrictJetCoefficients_compatible Γ hr hrpos hR hc)
    (coefficientValues_restrict_contDiff Γ hr hΓsmooth) hs φ hφ

end SemiHamiltonian.Darboux
