module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Order.Filter.Germ.Basic

@[expose] public section

open scoped Topology ContDiff
open Set Filter

namespace SemiHamiltonian.Smooth

/-- Every genuinely smooth local scalar function on the line has a globally
smooth representative of the same germ. -/
theorem exists_global_smooth_germ {U : Set ℝ} (hU : IsOpen U) {p : ℝ} (hp : p ∈ U)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 p] f := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU p hp
  let b : ContDiffBump p := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hs : tsupport b ⊆ U := by
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by change ε / 2 < ε; linarith)).trans hball
  refine ⟨fun x => b x * f x, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact b.contDiff.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
    · have hb : b =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hh => hx (hs hh))
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hb] with y hy
      simp [hy]
  · filter_upwards [b.eventuallyEq_one] with x hx
    simp [hx]

/-- Smooth scalar germs, with smoothness on one actual neighbourhood. -/
def ScalarGerm (p : ℝ) :=
  {g : Filter.Germ (𝓝 p) ℝ // ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ (f : Filter.Germ (𝓝 p) ℝ) = g}

end SemiHamiltonian.Smooth
