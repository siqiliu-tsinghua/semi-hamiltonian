module

public import SemiHamiltonian.Geometry.RadialFlat

/-! Local smooth potentials for closed one-forms, derived from the proved
radial Frobenius theorem. -/

@[expose] public section

open scoped Topology ContDiff
open Set Filter

set_option backward.isDefEq.respectTransparency.types false

namespace SemiHamiltonian.Geometry

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_local_potential {U : Set E} (hU : IsOpen U) {α : E → E →L[ℝ] ℝ}
    (hα : ContDiffOn ℝ ∞ α U)
    (hc : ∀ x ∈ U, ∀ v w : E, fderiv ℝ α x v w = fderiv ℝ α x w v)
    {p : E} (hp : p ∈ U) (c : ℝ) :
    ∃ (V : Set E) (f : E → ℝ), IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ f V ∧ f p = c ∧ ∀ x ∈ V, fderiv ℝ f x = α x := by
  let T : Set (E × ℝ) := {q | p + q.1 ∈ U}
  let A : E × ℝ → E →L[ℝ] ℝ := fun q => α (p + q.1)
  have hT : IsOpen T := hU.preimage (continuous_const.add continuous_fst)
  have hA : ContDiffOn ℝ ∞ A T := hα.comp (contDiffOn_const.add contDiffOn_fst) (fun _ hx => hx)
  have hAder (q : E × ℝ) (hq : q ∈ T) (v : E) (z : ℝ) :
      fderiv ℝ A q (v, z) = fderiv ℝ α (p + q.1) v := by
    have hqmap : HasFDerivAt (fun z : E × ℝ => p + z.1) (ContinuousLinearMap.fst ℝ E ℝ) q :=
      (hasFDerivAt_fst (p := q)).const_add p
    have hd := ((hα.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt.comp q hqmap
    change fderiv ℝ (α ∘ fun z : E × ℝ => p + z.1) q (v, z) = _
    rw [hd.fderiv]
    rfl
  have hflat : FlatConnection A T := by
    intro q hq v w
    rw [hAder q hq, hAder q hq]
    exact hc _ hq v w
  have hbase : ((0 : E), c) ∈ T := by simpa [T] using hp
  obtain ⟨W, u, hW, hpW, huSmooth, huBase, huSol⟩ := exists_smooth_radial_solution hT hA hbase
  have hu : IsRadialSolution A T W u := ⟨huSmooth,
    fun q hq => (huSol q hq).1, fun q hq => (huSol q hq).2⟩
  let V : Set E := {x | (x - p, c) ∈ W}
  let f : E → ℝ := fun x => u (x - p, c) timeOne
  have hV : IsOpen V := hW.preimage ((continuous_id.sub continuous_const).prodMk continuous_const)
  have hpV : p ∈ V := by simpa [V] using hpW
  have hVU : V ⊆ U := by
    intro x hx
    have hh := hu.maps (x - p, c) hx timeOne
    simpa only [T, mem_ofPred_eq, timeOne, one_smul, add_sub_cancel] using hh
  have hslice : ContDiff ℝ ∞ (fun x : E => (x - p, c)) :=
    (contDiff_id.sub contDiff_const).prodMk contDiff_const
  have hf0 : ContDiffOn ℝ ∞ (fun q => u q timeOne) W :=
    (ContinuousLinearMap.contDiff (ContinuousMap.evalCLM ℝ (M := ℝ) timeOne)).comp_contDiffOn huSmooth
  have hf : ContDiffOn ℝ ∞ f V := hf0.comp hslice.contDiffOn (fun _ hx => hx)
  refine ⟨V, f, hV, hpV, hVU, hf, ?_, ?_⟩
  · simp only [f, sub_self, huBase, constPathCLM_apply]
  · intro x hx
    have hxm : HasFDerivAt (fun y : E => (y - p, c))
        ((ContinuousLinearMap.id ℝ E).prod 0) x :=
      ((hasFDerivAt_id x).sub_const p).prodMk (hasFDerivAt_const c x)
    have hd := ((hf0.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.comp x
      hxm
    change fderiv ℝ ((fun q => u q timeOne) ∘ fun y : E => (y - p, c)) x = α x
    rw [hd.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    change fderiv ℝ (fun q => u q timeOne) (x - p, c) (v, 0) = α x v
    rw [hu.horizontalDerivative hT hW hA hflat hx]
    simp only [A, add_sub_cancel]

theorem potential_germ_unique {U : Set E} (hU : IsOpen U) {f g : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) {p : E} (hp : p ∈ U)
    (hv : f p = g p) (hd : fderiv ℝ f =ᶠ[𝓝 p] fderiv ℝ g) : f =ᶠ[𝓝 p] g := by
  have hn : ∀ᶠ x in 𝓝 p, x ∈ U ∧ fderiv ℝ f x = fderiv ℝ g x := by
    filter_upwards [hU.mem_nhds hp, hd] with x hx he
    exact ⟨hx, he⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hn
  have hsub : Metric.ball p r ⊆ U := fun x hx => (hball hx).1
  have he := Metric.isOpen_ball.eqOn_of_fderiv_eq (convex_ball p r).isPreconnected
    ((hf.mono hsub).differentiableOn (by simp)) ((hg.mono hsub).differentiableOn (by simp))
    (fun x hx => (hball hx).2) (Metric.mem_ball_self hr) hv
  filter_upwards [Metric.ball_mem_nhds p hr] with x hx
  exact he hx

end SemiHamiltonian.Geometry
