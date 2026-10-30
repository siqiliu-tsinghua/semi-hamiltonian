module

public import SemiHamiltonian.Darboux.PairValueUniqueness
public import SemiHamiltonian.Darboux.PairSmooth
public import SemiHamiltonian.Darboux.SmoothExistence

/-! Local C∞ existence and uniqueness with arbitrary smooth axis data for
the general two-coefficient Darboux system. -/

@[expose] public section

open scoped NNReal Topology ContDiff

namespace SemiHamiltonian.Darboux.Pair

variable {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

theorem existsUnique_C1_darboux_axisData (hr : 0 < r)
    (Γ : JetCoefficients (ι := ι) r) (hΓ : ∀ i j, IsCubeJet r (Γ.1 i j) ∧ IsCubeJet r (Γ.2 i j))
    (hcompat : IsDarbouxCompatible r Γ)
    (hsmall : 8 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1)
    (φ ψ : ι → C(ℝ, ℝ)) (hφ : ∀ i (s : ℝ), |s| < r → HasDerivAt (φ i) (ψ i s) s) :
    ∃! u : Values (ι := ι) r, IsC1DarbouxSolution r Γ (axisDataOfFunctions r φ) u :=
  existsUnique_C1_darboux r hr Γ (axisDataOfFunctions r φ) (initialJets r φ ψ) hΓ
    (initialJets_isCubeJet r hr φ ψ hφ) hcompat
    (initialJets_transverse r φ ψ) (initialJets_trace r φ ψ) hsmall

theorem C1DarbouxSolution_contDiff (hr : 0 < r) (Γ : JetCoefficients (ι := ι) r)
    (φ : ι → C(ℝ, ℝ)) {u : Values (ι := ι) r}
    (hu : IsC1DarbouxSolution r Γ (axisDataOfFunctions r φ) u)
    (hΓ : SmoothCoefficients r (coefficientValues r Γ))
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
    (Γ : JetCoefficients (ι := ι) r) (hΓ : ∀ i j, IsCubeJet r (Γ.1 i j) ∧ IsCubeJet r (Γ.2 i j))
    (hc : IsDarbouxCompatible r Γ)
    (hΓsmooth : SmoothCoefficients r (coefficientValues r Γ))
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

noncomputable def restrictJetCoefficients (Γ : JetCoefficients (ι := ι) R) (hr : r ≤ R) :
    JetCoefficients (ι := ι) r :=
  (Darboux.restrictJetCoefficients Γ.1 hr, Darboux.restrictJetCoefficients Γ.2 hr)

theorem restrictJetCoefficients_norm_le (Γ : JetCoefficients (ι := ι) R) (hr : r ≤ R) (hR : 0 < R) :
    ‖restrictJetCoefficients Γ hr‖ ≤ ‖Γ‖ := by
  apply max_le
  · exact (Darboux.restrictJetCoefficients_norm_le Γ.1 hr hR).trans (norm_fst_le Γ)
  · exact (Darboux.restrictJetCoefficients_norm_le Γ.2 hr hR).trans (norm_snd_le Γ)

theorem restrictJetCoefficients_compatible (Γ : JetCoefficients (ι := ι) R)
    (hr : r ≤ R) (hrpos : 0 < r) (hR : 0 < R) (hc : IsDarbouxCompatible R Γ) :
    IsDarbouxCompatible r (restrictJetCoefficients Γ hr) := by
  intro x i j k hij hik hjk
  constructor
  · change jetDiff r x (Pi.single k 1) (restrictJet hr (Γ.1 i j)) =
      jetDiff r x (Pi.single j 1) (restrictJet hr (Γ.1 i k))
    rw [jetDiff_restrictJet hr hrpos hR, jetDiff_restrictJet hr hrpos hR]
    exact (hc (cubeInclusion hr x) i j k hij hik hjk).1
  · change jetDiff r x (Pi.single k 1) (restrictJet hr (Γ.2 i j)) = _
    rw [jetDiff_restrictJet hr hrpos hR]
    exact (hc (cubeInclusion hr x) i j k hij hik hjk).2

theorem coefficientValues_restrict_contDiff (Γ : JetCoefficients (ι := ι) R) (hr : r ≤ R)
    (hΓ : SmoothCoefficients R (coefficientValues R Γ)) :
    SmoothCoefficients r (coefficientValues r (restrictJetCoefficients Γ hr)) :=
  ⟨Darboux.coefficientValues_restrict_contDiff Γ.1 hr hΓ.1,
    Darboux.coefficientValues_restrict_contDiff Γ.2 hr hΓ.2⟩

/-- Local C∞ Darboux existence and uniqueness, uniformly in arbitrary smooth
single-variable axis data. One positive radius works for every derivative order. -/
theorem local_existsUnique_smooth_darboux (hR : 0 < R)
    (Γ : JetCoefficients (ι := ι) R) (hΓ : ∀ i j, IsCubeJet R (Γ.1 i j) ∧ IsCubeJet R (Γ.2 i j))
    (hc : IsDarbouxCompatible R Γ)
    (hΓsmooth : SmoothCoefficients R (coefficientValues R Γ)) :
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
    (fun i j => ⟨restrictJet_isCubeJet hr hrpos hR _ (hΓ i j).1,
      restrictJet_isCubeJet hr hrpos hR _ (hΓ i j).2⟩)
    (restrictJetCoefficients_compatible Γ hr hrpos hR hc)
    (coefficientValues_restrict_contDiff Γ hr hΓsmooth) hs φ hφ

end SemiHamiltonian.Darboux.Pair
