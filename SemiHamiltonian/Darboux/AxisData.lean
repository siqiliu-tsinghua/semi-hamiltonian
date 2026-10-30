module

public import SemiHamiltonian.Darboux.ValueUniqueness
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Supplying arbitrary single-variable C¹ data to the Darboux theorem. -/

@[expose] public section

open scoped NNReal Topology
open Filter

namespace SemiHamiltonian.Darboux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

noncomputable def axisDataOfFunctions (φ : ι → C(ℝ, ℝ)) : AxisData (ι := ι) r :=
  fun i => ⟨fun s => φ i s, (φ i).continuous.comp continuous_subtype_val⟩

noncomputable def initialJets (φ ψ : ι → C(ℝ, ℝ)) : JetValues (ι := ι) r := fun i =>
  (⟨fun x => φ i (x i), (φ i).continuous.comp (continuous_subtype_val.comp (continuous_apply i))⟩,
    ⟨fun x => ((r : ℝ) * ψ i (x i)) • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ),
      (continuous_const.mul ((ψ i).continuous.comp
        (continuous_subtype_val.comp (continuous_apply i)))).smul continuous_const⟩)

theorem initialJets_isCubeJet (hr : 0 < r) (φ ψ : ι → C(ℝ, ℝ))
    (hφ : ∀ i (s : ℝ), |s| < r → HasDerivAt (φ i) (ψ i s) s) (i : ι) :
    IsCubeJet r (initialJets r φ ψ i) := by
  intro x hx
  have hn : ‖x‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hi : |x i| < r := (norm_le_pi_norm x i).trans_lt hn
  have hc := (hφ i (x i) hi).comp_hasFDerivAt x
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt
  have he : (fun y : ι → ℝ => φ i ((clamp r y) i)) =ᶠ[𝓝 x] (fun y => φ i (y i)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    have hyn : ‖y‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hy
    have hcoord := congrFun (point_clamp_of_norm_le r hyn.le) i
    exact congrArg (φ i) hcoord
  have hcoord := congrFun (point_clamp_of_norm_le r hn.le) i
  change ((clamp r x) i : ℝ) = x i at hcoord
  change HasFDerivAt (fun y => φ i ((clamp r y) i))
    ((r : ℝ)⁻¹ • (((r : ℝ) * ψ i ((clamp r x) i)) •
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))) x
  rw [hcoord, smul_smul]
  have heq : (r : ℝ)⁻¹ * ((r : ℝ) * ψ i (x i)) = ψ i (x i) := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (show (0 : ℝ) < r from hr)), one_mul]
  rw [heq]
  exact hc.congr_of_eventuallyEq he

theorem initialJets_transverse (φ ψ : ι → C(ℝ, ℝ)) (x : Cube ι r) (i j : ι) (hij : i ≠ j) :
    jetDiff r x (Pi.single j 1) (initialJets r φ ψ i) = 0 := by
  simp [jetDiff_apply, initialJets, smul_apply, hij]

theorem initialJets_trace (φ ψ : ι → C(ℝ, ℝ)) (i : ι) (x : Cube ι r) :
    (initialJets r φ ψ i).1 (axis r i x) = axisDataOfFunctions r φ i (x i) := by
  simp [initialJets, axisDataOfFunctions]

/-- Arbitrary single-variable C¹ data determine a unique genuine local C¹ solution
of the compatible Darboux system. The smallness bound is independent of the data. -/
theorem existsUnique_C1_darboux_axisData (hr : 0 < r)
    (Γ : JetCoefficients (ι := ι) r) (hΓ : ∀ i j, IsCubeJet r (Γ i j))
    (hcompat : IsDarbouxCompatible r Γ)
    (hsmall : 8 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1)
    (φ ψ : ι → C(ℝ, ℝ)) (hφ : ∀ i (s : ℝ), |s| < r → HasDerivAt (φ i) (ψ i s) s) :
    ∃! u : Values (ι := ι) r, IsC1DarbouxSolution r Γ (axisDataOfFunctions r φ) u :=
  existsUnique_C1_darboux r hr Γ (axisDataOfFunctions r φ) (initialJets r φ ψ) hΓ
    (initialJets_isCubeJet r hr φ ψ hφ) hcompat
    (initialJets_transverse r φ ψ) (initialJets_trace r φ ψ) hsmall

end SemiHamiltonian.Darboux
