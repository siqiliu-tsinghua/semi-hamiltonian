module

public import SemiHamiltonian.Geometry.RadialFlat

/-! Smooth local coordinates for a flat graph distribution. -/

@[expose] public section

open scoped Topology ContDiff
open Filter Set

namespace SemiHamiltonian.Geometry

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem isInvertible_graph {f : E × F → F} {p : E × F}
    (hf : ContDiffAt ℝ ∞ f p)
    (hi : ((fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ E F)).IsInvertible) :
    (fderiv ℝ (fun q : E × F => (q.1, f q)) p).IsInvertible := by
  let d := (hf.hasStrictFDerivAt (by simp)).implicitFunctionDataOfProdDomain hi
  have hdp : d.pt = p := by simp [d]
  have hprod : d.prodFun = fun q => (f q, q.1) := by
    funext q
    simp [d, ImplicitFunctionData.prodFun_apply]
  let swap := ContinuousLinearEquiv.prodComm ℝ F E
  have he : (fun q : E × F => (q.1, f q)) = swap ∘ d.prodFun := by
    funext q
    simp [hprod, swap]
  have hdiff : DifferentiableAt ℝ d.prodFun p := by
    simpa only [hdp] using d.hasStrictFDerivAt.hasFDerivAt.differentiableAt
  have hinv : (fderiv ℝ d.prodFun p).IsInvertible := by
    simpa only [hdp] using d.isInvertible_fderiv_prodFun
  rw [he, fderiv_comp p swap.differentiableAt hdiff, swap.hasFDerivAt.fderiv]
  exact ContinuousLinearMap.IsInvertible.comp ContinuousLinearMap.isInvertible_equiv hinv

/-- Frobenius for a graph distribution: there are genuine smooth local coordinates
in which all vectors `(h, A(q) h)` become horizontal coordinate vectors. -/
theorem flatConnection_local_coordinates {V : Set (E × F)} (hV : IsOpen V)
    {A : E × F → E →L[ℝ] F} (hA : ContDiffOn ℝ ∞ A V) (hc : FlatConnection A V)
    {y₀ : F} (hy₀ : (0, y₀) ∈ V) :
    ∃ e : OpenPartialHomeomorph (E × F) (E × F),
      (0, y₀) ∈ e.source ∧ e.source ⊆ V ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ q ∈ e.source, (e q).1 = q.1 ∧
        ∀ h : E, fderiv ℝ e q (h, A q h) = (h, 0) := by
  obtain ⟨W, u, hW, hpW, huSmooth, huBase, huSol⟩ := exists_smooth_radial_solution hV hA hy₀
  have hu : IsRadialSolution A V W u := ⟨huSmooth, fun p hp => (huSol p hp).1,
    fun p hp => (huSol p hp).2⟩
  let f : E × F → F := fun p => u p timeOne
  have hf : ContDiffOn ℝ ∞ f W :=
    (ContinuousLinearMap.contDiff (ContinuousMap.evalCLM ℝ (M := F) timeOne)).comp_contDiffOn huSmooth
  have hfp := hf.contDiffAt (hW.mem_nhds hpW)
  have hslice : (fun y => f (0, y)) =ᶠ[𝓝 y₀] id := by
    have hn : ∀ᶠ y in 𝓝 y₀, ((0 : E), y) ∈ W :=
      (continuous_const.prodMk continuous_id).continuousAt.eventually (hW.mem_nhds hpW)
    filter_upwards [hn] with y hy
    change u (0, y) timeOne = y
    rw [hu.fixed (0, y) hy]
    simp only [radialKernel_zero, map_zero, add_zero, constPathCLM_apply]
  have hpart : (fderiv ℝ f (0, y₀)).comp (ContinuousLinearMap.inr ℝ E F) =
      ContinuousLinearMap.id ℝ F := by
    have hd := (hfp.differentiableAt (by simp)).hasFDerivAt.comp y₀
      ((hasFDerivAt_const (0 : E) y₀).prodMk (hasFDerivAt_id y₀))
    exact hd.unique ((hasFDerivAt_id y₀).congr_of_eventuallyEq hslice)
  have hi : ((fderiv ℝ f (0, y₀)).comp (ContinuousLinearMap.inr ℝ E F)).IsInvertible := by
    rw [hpart]
    exact ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩
  let G : E × F → E × F := fun p => (p.1, f p)
  have hG : ContDiffOn ℝ ∞ G W := contDiffOn_fst.prodMk hf
  have hGi := isInvertible_graph hfp hi
  obtain ⟨e, he, hep, heW, heSmooth, heInvSmooth⟩ := exists_smooth_local_inverse hW hG hpW hGi
  have hbase : e (0, y₀) = (0, y₀) := by simp only [he, G, f, huBase, constPathCLM_apply]
  have heV : e.target ⊆ V := by
    intro q hq
    have hm := hu.maps (e.symm q) (heW (e.map_target hq)) timeOne
    have hm' : G (e.symm q) ∈ V := by simpa only [timeOne, one_smul, G, f] using hm
    rwa [← he, e.right_inv hq] at hm'
  refine ⟨e.symm, ?_, heV, heInvSmooth, heSmooth, ?_⟩
  · change (0, y₀) ∈ e.target
    simpa only [hbase] using e.map_source hep
  · intro q hq
    have hq' : q ∈ e.target := hq
    have hr := e.map_target hq'
    have hrW := heW hr
    have hGq : G (e.symm q) = q := by rw [← he, e.right_inv hq']
    have hfirst : (e.symm q).1 = q.1 := by simpa only [G] using congrArg Prod.fst hGq
    refine ⟨hfirst, fun h => ?_⟩
    have hdf := ((hf.contDiffAt (hW.mem_nhds hrW)).differentiableAt (by simp)).hasFDerivAt
    have hdG : HasFDerivAt G
        ((ContinuousLinearMap.fst ℝ E F).prod (fderiv ℝ f (e.symm q))) (e.symm q) :=
      hasFDerivAt_fst.prodMk hdf
    have hhorizontal : fderiv ℝ G (e.symm q) (h, 0) = (h, A q h) := by
      rw [hdG.fderiv]
      change (h, fderiv ℝ f (e.symm q) (h, 0)) = _
      rw [hu.horizontalDerivative hV hW hA hc hrW h]
      change (h, A (G (e.symm q)) h) = _
      rw [hGq]
    have hidentity : (e.symm ∘ G) =ᶠ[𝓝 (e.symm q)] id := by
      filter_upwards [e.open_source.mem_nhds hr] with z hz
      exact (by simpa only [he, Function.comp_def, id_eq] using e.left_inv hz)
    have hdi := ((heInvSmooth.contDiffAt (e.open_target.mem_nhds hq')).differentiableAt (by simp)).hasFDerivAt
    have hcomp := (hGq ▸ hdi).comp (e.symm q) hdG
    have hid := hcomp.unique ((hasFDerivAt_id (e.symm q)).congr_of_eventuallyEq hidentity)
    have hh := congrArg (fun L : (E × F) →L[ℝ] (E × F) => L (h, 0)) hid
    rw [← hdG.fderiv] at hh
    simpa only [ContinuousLinearMap.comp_apply, hhorizontal, ContinuousLinearMap.id_apply, hGq] using hh

end SemiHamiltonian.Geometry
