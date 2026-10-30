module

public import SemiHamiltonian.Darboux.CurveSmooth
public import SemiHamiltonian.Darboux.LocalSmoothData

/-! Smooth diagonal-curve data on arbitrary open coefficient domains. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Darboux

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem local_smooth_solution_diagonalCurve (R : ℝ≥0) (hR : 0 < R)
    {V : Set (ι → ℝ)} (hV : IsOpen V) (hbox : ∀ x : Cube ι R, point R x ∈ V)
    (γ : ι → ι → (ι → ℝ) → ℝ) (hγ : ∀ i j, ContDiffOn ℝ ∞ (γ i j) V)
    (hc : ∀ x ∈ V, ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      fderiv ℝ (γ i j) x (Pi.single k 1) =
        γ i j x * γ j k x + γ i k x * γ k j x - γ i j x * γ i k x) :
    ∃ r : ℝ≥0, 0 < r ∧ r ≤ R ∧
      ∀ (φ : ι → C(ℝ, ℝ)), (∀ i, ContDiff ℝ ∞ (φ i)) →
        ∃ f : (ι → ℝ) → (ι → ℝ),
          ContDiffOn ℝ ∞ f (Metric.ball 0 (r : ℝ)) ∧
          (∀ x ∈ Metric.ball 0 (r : ℝ), ∀ i j, i ≠ j →
            fderiv ℝ (fun y => f y i) x (Pi.single j 1) = γ i j x * (f x j - f x i)) ∧
          ∀ i (s : ℝ), |s| < r → f (fun _ => s) i = φ i s := by
  let Γ := localCoefficientJets R hV hbox γ hγ
  obtain ⟨ε, hε, hεsmall⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1)
    (16 * Fintype.card ι * ‖Γ‖)
  let r : ℝ≥0 := min R ⟨ε, hε.le⟩
  have hr : r ≤ R := min_le_left _ _
  have hrpos : 0 < r := lt_min hR hε
  have hrε : (r : ℝ) ≤ ε := min_le_right (R : ℝ) ε
  have hs : 16 * Fintype.card ι * (r : ℝ) * ‖restrictJetCoefficients Γ hr‖ < 1 := by
    have h₁ := mul_le_mul_of_nonneg_left (restrictJetCoefficients_norm_le Γ hr hR)
      (by positivity : 0 ≤ 16 * (Fintype.card ι : ℝ) * (r : ℝ))
    have h₂ := mul_le_mul_of_nonneg_right hrε
      (by positivity : 0 ≤ 16 * (Fintype.card ι : ℝ) * ‖Γ‖)
    nlinarith
  refine ⟨r, hrpos, hr, fun φ hφ => ?_⟩
  obtain ⟨w, hw, hpde, htrace, hsm⟩ := exists_smooth_darboux_diagonalCurve r hrpos
    (restrictJetCoefficients Γ hr)
    (fun i j => restrictJet_isCubeJet hr hrpos hR _
      (localCoefficientJets_isCubeJet R hV hbox γ hγ hR i j))
    (restrictJetCoefficients_compatible Γ hr hrpos hR
      (localCoefficientJets_compatible R hV hbox γ hγ hR hc))
    (coefficientValues_restrict_contDiff Γ hr (localCoefficientJets_contDiff R hV hbox γ hγ)) hs φ hφ
  refine ⟨fun x => valuesOfJets r w (clamp r x), hsm, ?_, ?_⟩
  · intro x hx i j hij
    change fderiv ℝ (fun y => (w i).1 (clamp r y)) x (Pi.single j 1) = _
    rw [(hw i x hx).fderiv]
    have hh := hpde (clamp r x) i j hij
    have hn : ‖x‖ ≤ r := (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
    change _ = γ i j (point r (clamp r x)) * _ at hh
    rw [point_clamp_of_norm_le r hn] at hh
    exact hh
  · intro i s hs
    have he : clamp (ι := ι) r (fun _ => s) = diagonalPoint r ⟨s, abs_le.mp hs.le⟩ := by
      funext j
      apply Subtype.ext
      simp only [clamp, ContinuousMap.coe_mk, diagonalPoint]
      exact congrArg Subtype.val (Set.projIcc_of_mem (neg_le_self r.coe_nonneg) (abs_le.mp hs.le))
    change (w i).1 (clamp r (fun _ => s)) = _
    rw [he]
    exact htrace ⟨s, abs_le.mp hs.le⟩ i

theorem curvePicard_contraction (r : ℝ≥0) (Γ : Coefficients (ι := ι) r)
    (φ : AxisData (ι := ι) r)
    (hsmall : 4 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1) :
    ContractingWith ⟨4 * Fintype.card ι * (r : ℝ) * ‖Γ‖, by positivity⟩
      (fun w => initial r φ + curveOperator r Γ w) := by
  refine ⟨hsmall, LipschitzWith.of_dist_le_mul fun w z => ?_⟩
  simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← map_sub]
  exact ((curveOperator r Γ).le_opNorm (w - z)).trans
    (mul_le_mul_of_nonneg_right (curveOperator_norm_le r Γ) (norm_nonneg _))

theorem cubeJet_curveFixedPoint (r : ℝ≥0) (hr : 0 < r)
    (Γ : JetCoefficients (ι := ι) r) (φ : AxisData (ι := ι) r) (w : JetValues (ι := ι) r)
    (hw : ∀ i, IsCubeJet r (w i))
    (hpde : ∀ (x : Cube ι r) (i j : ι), i ≠ j →
      jetDiff r x (Pi.single j 1) (w i) = (Γ i j).1 x * ((w j).1 x - (w i).1 x))
    (htrace : ∀ (s : Icc (-(r : ℝ)) r) i, (w i).1 (diagonalPoint r s) = φ i s) :
    initial r φ + curveOperator r (coefficientValues r Γ) (valuesOfJets r w) = valuesOfJets r w := by
  let ψ := axisDataOfFunctions r (axisTrace r (valuesOfJets r w))
  have hf := cubeJet_fixedPoint r hr Γ ψ w hw hpde (fun i x => by rw [axis_eq_clamp]; rfl)
  have hp : curveProjection r (valuesOfJets r w) = initial r φ := by
    ext x i
    exact htrace (x i) i
  have hh := congrArg (curveProjection r) hf
  change curveProjection r (initial r ψ + integralOperator r (coefficientValues r Γ) (valuesOfJets r w)) = _ at hh
  rw [map_add, hp] at hh
  change initial r ψ + curveProjection r (integralOperator r (coefficientValues r Γ) (valuesOfJets r w)) = _ at hh
  change initial r φ + (integralOperator r (coefficientValues r Γ) (valuesOfJets r w) -
    curveProjection r (integralOperator r (coefficientValues r Γ) (valuesOfJets r w))) = _
  rw [← hh]
  convert hf using 1 <;> dsimp only [picard] <;> abel

/-- Uniqueness is for actual C¹ solution values with the same curve trace. -/
theorem C1_diagonalCurve_unique (r : ℝ≥0) (hr : 0 < r)
    (Γ : JetCoefficients (ι := ι) r) (φ : AxisData (ι := ι) r)
    (hsmall : 4 * Fintype.card ι * (r : ℝ) * ‖coefficientValues r Γ‖ < 1)
    (w z : JetValues (ι := ι) r)
    (hw : ∀ i, IsCubeJet r (w i)) (hz : ∀ i, IsCubeJet r (z i))
    (hpw : ∀ (x : Cube ι r) (i j : ι), i ≠ j →
      jetDiff r x (Pi.single j 1) (w i) = (Γ i j).1 x * ((w j).1 x - (w i).1 x))
    (hpz : ∀ (x : Cube ι r) (i j : ι), i ≠ j →
      jetDiff r x (Pi.single j 1) (z i) = (Γ i j).1 x * ((z j).1 x - (z i).1 x))
    (htw : ∀ (s : Icc (-(r : ℝ)) r) i, (w i).1 (diagonalPoint r s) = φ i s)
    (htz : ∀ (s : Icc (-(r : ℝ)) r) i, (z i).1 (diagonalPoint r s) = φ i s) :
    valuesOfJets r w = valuesOfJets r z :=
  (curvePicard_contraction r (coefficientValues r Γ) φ hsmall).fixedPoint_unique'
    (cubeJet_curveFixedPoint r hr Γ φ w hw hpw htw) (cubeJet_curveFixedPoint r hr Γ φ z hz hpz htz)

end SemiHamiltonian.Darboux
