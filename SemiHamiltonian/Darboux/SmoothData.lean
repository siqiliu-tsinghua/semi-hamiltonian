module

public import SemiHamiltonian.Darboux.SmoothExistence

/-! A convenient entry point taking ordinary smooth coefficient functions.
Their first derivatives are constructed, rather than supplied as extra data. -/

@[expose] public section

open scoped NNReal Topology ContDiff
open Filter

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 1024

namespace SemiHamiltonian.Darboux

variable {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

noncomputable def smoothCoefficientJets (γ : ι → ι → (ι → ℝ) → ℝ)
    (hγ : ∀ i j, ContDiff ℝ ∞ (γ i j)) : JetCoefficients (ι := ι) r := fun i j =>
  (⟨fun x => γ i j (point r x),
    (hγ i j).continuous.comp (continuous_pi fun k => continuous_subtype_val.comp (continuous_apply k))⟩,
   ⟨fun x => (r : ℝ) • fderiv ℝ (γ i j) (point r x), by
    have hp : Continuous (point (ι := ι) r) :=
      continuous_pi fun k => continuous_subtype_val.comp (continuous_apply k)
    have hd : Continuous (fun x : Cube ι r => fderiv ℝ (γ i j) (point r x)) :=
      ((hγ i j).fderiv_right (m := ∞) (by simp)).continuous.comp hp
    simpa only [Pi.smul_def] using hd.const_smul (r : ℝ)⟩)

theorem smoothCoefficientJets_isCubeJet (hr : 0 < r) (γ : ι → ι → (ι → ℝ) → ℝ)
    (hγ : ∀ i j, ContDiff ℝ ∞ (γ i j)) (i j : ι) :
    IsCubeJet r (smoothCoefficientJets r γ hγ i j) := by
  intro x hx
  have hn : ‖x‖ ≤ r := (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
  have he : (fun y => γ i j (point r (clamp r y))) =ᶠ[𝓝 x] γ i j := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    have hyn : ‖y‖ ≤ r := (by simpa only [Metric.mem_ball, dist_zero_right] using hy : ‖y‖ < r).le
    rw [point_clamp_of_norm_le r hyn]
  change HasFDerivAt (fun y => γ i j (point r (clamp r y)))
    ((r : ℝ)⁻¹ • ((r : ℝ) • fderiv ℝ (γ i j) (point r (clamp r x)))) x
  rw [inv_smul_smul₀ (ne_of_gt (show (0 : ℝ) < r from hr)), point_clamp_of_norm_le r hn]
  exact ((hγ i j).differentiable (by simp) x).hasFDerivAt.congr_of_eventuallyEq he

theorem smoothCoefficientJets_contDiff (γ : ι → ι → (ι → ℝ) → ℝ)
    (hγ : ∀ i j, ContDiff ℝ ∞ (γ i j)) :
    ContDiffOn ℝ ∞ (fun x => coefficientValues r (smoothCoefficientJets r γ hγ) (clamp r x))
      (Metric.ball 0 (r : ℝ)) := by
  have hg : ContDiff ℝ ∞ (fun x i j => γ i j x) :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (hγ i))
  apply hg.contDiffOn.congr
  intro x hx
  have hn : ‖x‖ ≤ r := (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
  change (fun i j => γ i j (point r (clamp r x))) = _
  rw [point_clamp_of_norm_le r hn]

theorem smoothCoefficientJets_compatible (hr : 0 < r) (γ : ι → ι → (ι → ℝ) → ℝ)
    (hγ : ∀ i j, ContDiff ℝ ∞ (γ i j))
    (hc : ∀ x : ι → ℝ, ‖x‖ ≤ r → ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      fderiv ℝ (γ i j) x (Pi.single k 1) =
        γ i j x * γ j k x + γ i k x * γ k j x - γ i j x * γ i k x) :
    IsDarbouxCompatible r (smoothCoefficientJets r γ hγ) := by
  intro x i j k hij hik hjk
  change (r : ℝ)⁻¹ * ((r : ℝ) * fderiv ℝ (γ i j) (point r x) (Pi.single k 1)) = _
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (show (0 : ℝ) < r from hr)), one_mul]
  exact hc (point r x) (norm_point_le r x) i j k hij hik hjk

variable {r R : ℝ≥0}

theorem restrict_smoothCoefficientJets (hr : r ≤ R) (hR : 0 < R)
    (γ : ι → ι → (ι → ℝ) → ℝ) (hγ : ∀ i j, ContDiff ℝ ∞ (γ i j)) :
    restrictJetCoefficients (smoothCoefficientJets R γ hγ) hr = smoothCoefficientJets r γ hγ := by
  funext i j
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro x
    change ((r : ℝ) / R) • ((R : ℝ) • fderiv ℝ (γ i j) (point r x)) =
      (r : ℝ) • fderiv ℝ (γ i j) (point r x)
    rw [smul_smul, div_mul_cancel₀ _ (ne_of_gt (show (0 : ℝ) < R from hR))]

/-- Ordinary smooth functions can be supplied directly. Compatibility is required
only on the initial cube; the resulting positive radius is uniform in all smooth
axis data and all derivative orders. The more general local-coefficient version
is `local_existsUnique_smooth_darboux`. -/
theorem local_existsUnique_smooth_darboux_of_functions (R : ℝ≥0) (hR : 0 < R)
    (γ : ι → ι → (ι → ℝ) → ℝ) (hγ : ∀ i j, ContDiff ℝ ∞ (γ i j))
    (hc : ∀ x : ι → ℝ, ‖x‖ ≤ R → ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      fderiv ℝ (γ i j) x (Pi.single k 1) =
        γ i j x * γ j k x + γ i k x * γ k j x - γ i j x * γ i k x) :
    ∃ r : ℝ≥0, 0 < r ∧ r ≤ R ∧
      ∀ (φ : ι → C(ℝ, ℝ)), (∀ i, ContDiff ℝ ∞ (φ i)) →
        ∃! u : Values (ι := ι) r, IsSmoothDarbouxSolution r (smoothCoefficientJets r γ hγ) φ u := by
  obtain ⟨r, hr, hrpos, hsol⟩ := local_existsUnique_smooth_darboux hR (smoothCoefficientJets R γ hγ)
    (smoothCoefficientJets_isCubeJet R hR γ hγ)
    (smoothCoefficientJets_compatible R hR γ hγ hc) (smoothCoefficientJets_contDiff R γ hγ)
  refine ⟨r, hrpos, hr, ?_⟩
  simpa only [restrict_smoothCoefficientJets hr hR γ hγ] using hsol

end SemiHamiltonian.Darboux
