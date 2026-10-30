module

public import SemiHamiltonian.Darboux.AxisData
public import SemiHamiltonian.Darboux.Local

/-! Restriction to a positive cube satisfying the C¹ contraction estimate. -/

@[expose] public section

open scoped NNReal Topology
open Filter

namespace SemiHamiltonian.Darboux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r R : ℝ≥0}

noncomputable def restrictJet (hr : r ≤ R) (f : ScalarJet (ι := ι) R) : ScalarJet (ι := ι) r :=
  (f.1.comp (cubeInclusion hr), ⟨fun x => ((r : ℝ) / R) • f.2 (cubeInclusion hr x),
    by
      simpa only [Pi.smul_def', Function.comp_def] using
        ((continuous_const (y := (r : ℝ) / (R : ℝ))).smul
          (f.2.continuous.comp (cubeInclusion hr).continuous))⟩)

theorem restriction_scale (hr : 0 < r) (hR : 0 < R) :
    (r : ℝ)⁻¹ * ((r : ℝ) / R) = (R : ℝ)⁻¹ := by
  field_simp

omit [DecidableEq ι] in
theorem jetDiff_restrictJet (hr : r ≤ R) (hrpos : 0 < r) (hR : 0 < R)
    (f : ScalarJet (ι := ι) R) (x : Cube ι r) (v : ι → ℝ) :
    jetDiff r x v (restrictJet hr f) = jetDiff R (cubeInclusion hr x) v f := by
  change (r : ℝ)⁻¹ * (((r : ℝ) / R) * f.2 (cubeInclusion hr x) v) =
    (R : ℝ)⁻¹ * f.2 (cubeInclusion hr x) v
  rw [← mul_assoc, restriction_scale hrpos hR]

theorem restrictJet_isCubeJet (hr : r ≤ R) (hrpos : 0 < r) (hR : 0 < R)
    (f : ScalarJet (ι := ι) R) (hf : IsCubeJet R f) : IsCubeJet r (restrictJet hr f) := by
  have hclamp : ∀ y ∈ Metric.ball (0 : ι → ℝ) (r : ℝ),
      cubeInclusion hr (clamp r y) = clamp R y := by
    intro y hy
    have hn : ‖y‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hy
    have h₁ := point_clamp_of_norm_le r hn.le
    have h₂ := point_clamp_of_norm_le R (hn.le.trans (show (r : ℝ) ≤ R from hr))
    funext i
    apply Subtype.ext
    exact (congrFun h₁ i).trans (congrFun h₂ i).symm
  intro x hx
  have hxR : x ∈ Metric.ball (0 : ι → ℝ) (R : ℝ) :=
    Metric.ball_subset_ball (show (r : ℝ) ≤ R from hr) hx
  have hfd := hf x hxR
  have he : (fun y => f.1 (cubeInclusion hr (clamp r y))) =ᶠ[𝓝 x]
      (fun y => f.1 (clamp R y)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    rw [hclamp y hy]
  have hd : (r : ℝ)⁻¹ • (((r : ℝ) / R) • f.2 (cubeInclusion hr (clamp r x))) =
      (R : ℝ)⁻¹ • f.2 (clamp R x) := by
    rw [smul_smul, restriction_scale hrpos hR, hclamp x hx]
  change HasFDerivAt (fun y => f.1 (cubeInclusion hr (clamp r y)))
    ((r : ℝ)⁻¹ • (((r : ℝ) / R) • f.2 (cubeInclusion hr (clamp r x)))) x
  rw [hd]
  exact hfd.congr_of_eventuallyEq he

omit [DecidableEq ι] in
theorem restrictJet_norm_le (hr : r ≤ R) (hR : 0 < R) (f : ScalarJet (ι := ι) R) :
    ‖restrictJet hr f‖ ≤ ‖f‖ := by
  have ha : 0 ≤ (r : ℝ) / R := div_nonneg r.coe_nonneg R.coe_nonneg
  have hb : (r : ℝ) / R ≤ 1 := (div_le_one (show (0 : ℝ) < R from hR)).mpr hr
  rw [Prod.norm_def, max_le_iff]
  constructor
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro x
    exact (f.1.norm_coe_le_norm _).trans (norm_fst_le f)
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro x
    change ‖((r : ℝ) / R) • f.2 (cubeInclusion hr x)‖ ≤ ‖f‖
    calc
      _ ≤ ‖(r : ℝ) / R‖ * ‖f.2 (cubeInclusion hr x)‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ 1 * ‖f‖ := mul_le_mul (by simpa only [Real.norm_eq_abs, abs_of_nonneg ha] using hb)
        ((f.2.norm_coe_le_norm _).trans (norm_snd_le f)) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

noncomputable def restrictJetCoefficients (Γ : JetCoefficients (ι := ι) R) (hr : r ≤ R) :
    JetCoefficients (ι := ι) r := fun i j => restrictJet hr (Γ i j)

theorem restrictJetCoefficients_norm_le (Γ : JetCoefficients (ι := ι) R) (hr : r ≤ R) (hR : 0 < R) :
    ‖restrictJetCoefficients Γ hr‖ ≤ ‖Γ‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg Γ)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg Γ)).mpr
  intro j
  exact (restrictJet_norm_le hr hR (Γ i j)).trans
    ((norm_le_pi_norm (Γ i) j).trans (norm_le_pi_norm Γ i))

theorem restrictJetCoefficients_compatible (Γ : JetCoefficients (ι := ι) R)
    (hr : r ≤ R) (hrpos : 0 < r) (hR : 0 < R) (hc : IsDarbouxCompatible R Γ) :
    IsDarbouxCompatible r (restrictJetCoefficients Γ hr) := by
  intro x i j k hij hik hjk
  change jetDiff r x (Pi.single k 1) (restrictJet hr (Γ i j)) = _
  rw [jetDiff_restrictJet hr hrpos hR]
  exact hc (cubeInclusion hr x) i j k hij hik hjk

/-- Local C¹ Darboux existence and uniqueness on a positive cube. The chosen
radius depends only on the coefficients, uniformly for all single-variable C¹
axis data. -/
theorem local_existsUnique_C1_darboux (hR : 0 < R)
    (Γ : JetCoefficients (ι := ι) R) (hΓ : ∀ i j, IsCubeJet R (Γ i j))
    (hc : IsDarbouxCompatible R Γ) :
    ∃ (r : ℝ≥0) (hr : r ≤ R), 0 < r ∧
      ∀ (φ ψ : ι → C(ℝ, ℝ)),
        (∀ i (s : ℝ), |s| < r → HasDerivAt (φ i) (ψ i s) s) →
        ∃! u : Values (ι := ι) r,
          IsC1DarbouxSolution r (restrictJetCoefficients Γ hr) (axisDataOfFunctions r φ) u := by
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
  refine ⟨r, hr, hrpos, fun φ ψ hφ => ?_⟩
  exact existsUnique_C1_darboux_axisData r hrpos (restrictJetCoefficients Γ hr)
    (fun i j => restrictJet_isCubeJet hr hrpos hR _ (hΓ i j))
    (restrictJetCoefficients_compatible Γ hr hrpos hR hc) hs φ ψ hφ

end SemiHamiltonian.Darboux
