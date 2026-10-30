module

public import SemiHamiltonian.Geometry.LocalInverse

@[expose] public section

open scoped Topology ContDiff
open Filter Set

namespace SemiHamiltonian.Geometry

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem chart_fderiv_left_inverse (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {q : E} (hq : q ∈ e.source) :
    (fderiv ℝ e.symm (e q)).comp (fderiv ℝ e q) = ContinuousLinearMap.id ℝ E := by
  have hd := ((he.contDiffAt (e.open_source.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  have hid := ((hi.contDiffAt (e.open_target.mem_nhds (e.map_source hq))).differentiableAt
    (by simp)).hasFDerivAt
  have hh : (e.symm ∘ e) =ᶠ[𝓝 q] id := by
    filter_upwards [e.open_source.mem_nhds hq] with x hx
    exact e.left_inv hx
  exact (hid.comp q hd).unique ((hasFDerivAt_id q).congr_of_eventuallyEq hh)

theorem chart_fderiv_injective (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {q : E} (hq : q ∈ e.source) : Function.Injective (fderiv ℝ e q) := by
  have hh := chart_fderiv_left_inverse e he hi hq
  have hl : Function.LeftInverse (fderiv ℝ e.symm (e q)) (fderiv ℝ e q) := by
    intro v
    exact congrArg (fun L : E →L[ℝ] E => L v) hh
  exact hl.injective

end SemiHamiltonian.Geometry
