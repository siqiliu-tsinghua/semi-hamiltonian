module

public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! A smooth inverse on one open neighbourhood, with all derivative orders on
that same neighbourhood. -/

@[expose] public section

open scoped Topology ContDiff
open Filter Set

namespace SemiHamiltonian.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_local_inverse {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {p : E} (hp : p ∈ U)
    (hinv : (fderiv ℝ f p).IsInvertible) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ p ∈ e.source ∧
      e.source ⊆ U ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let V := {x | x ∈ U ∧ (fderiv ℝ f x).IsInvertible}
  have hV : IsOpen V := by
    exact (hf.fderiv_of_isOpen hU (m := ∞) (by simp)).continuousOn.isOpen_inter_preimage hU
      ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hvp : p ∈ V := ⟨hp, hinv⟩
  obtain ⟨L, hL⟩ := hinv
  have hfp := hf.contDiffAt (hU.mem_nhds hp)
  have hdf : HasFDerivAt f (L : E →L[ℝ] F) p := by
    rw [hL]
    exact (hfp.differentiableAt (by simp)).hasFDerivAt
  let e₀ := hfp.toOpenPartialHomeomorph f hdf (by simp)
  let e := e₀.restrOpen V hV
  have hes : e.source = e₀.source ∩ V := rfl
  have hef : (e : E → F) = f := rfl
  have hsub : e.source ⊆ U := fun x hx => (hes ▸ hx).2.1
  refine ⟨e, hef, ?_, hsub, ?_, ?_⟩
  · exact ⟨hfp.mem_toOpenPartialHomeomorph_source hdf (by simp), hvp⟩
  · simpa only [hef] using hf.mono hsub
  · intro y hy
    have hx := e.map_target hy
    have hxU := hsub hx
    have hxV := (hes ▸ hx).2.2
    obtain ⟨M, hM⟩ := hxV
    have hs := hf.contDiffAt (hU.mem_nhds hxU)
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm hy (f₀' := M)
    · rw [hef, hM]
      exact (hs.differentiableAt (by simp)).hasFDerivAt
    · simpa only [hef] using hs

variable [CompleteSpace F]

/-- A C∞ implicit graph on one fixed open set, including uniqueness in an open
neighbourhood of the base point. This avoids interpreting `ContDiffAt ∞` as
smoothness on a single neighbourhood. -/
theorem exists_smooth_implicit {U : Set (E × F)} (hU : IsOpen U) {f : E × F → F}
    (hf : ContDiffOn ℝ ∞ f U) {p : E × F} (hp : p ∈ U)
    (hinv : ((fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ E F)).IsInvertible) :
    ∃ (W : Set E) (B : Set (E × F)) (ψ : E → F),
      IsOpen W ∧ p.1 ∈ W ∧ IsOpen B ∧ p ∈ B ∧ B ⊆ U ∧
      ψ p.1 = p.2 ∧ ContDiffOn ℝ ∞ ψ W ∧
      (∀ x ∈ W, (x, ψ x) ∈ B ∧ f (x, ψ x) = f p) ∧
      ∀ x ∈ W, ∀ y, (x, y) ∈ B → f (x, y) = f p → y = ψ x := by
  have hfp := hf.contDiffAt (hU.mem_nhds hp)
  let d := (hfp.hasStrictFDerivAt (by simp)).implicitFunctionDataOfProdDomain hinv
  have hdprod : d.prodFun = fun q => (f q, q.1) := by
    funext q
    simp [d, ImplicitFunctionData.prodFun_apply]
  have hdpt : d.pt = p := by simp [d]
  have hg : ContDiffOn ℝ ∞ d.prodFun U := by
    rw [hdprod]
    exact hf.prodMk contDiffOn_fst
  have hdInv : (fderiv ℝ d.prodFun p).IsInvertible := by
    simpa only [hdpt] using d.isInvertible_fderiv_prodFun
  obtain ⟨e, he, hep, heU, hes, hei⟩ := exists_smooth_local_inverse hU hg hp hdInv
  rw [hdprod] at he
  let W : Set E := (fun x => (f p, x)) ⁻¹' e.target
  let ψ : E → F := fun x => (e.symm (f p, x)).2
  have hW : IsOpen W := e.open_target.preimage (continuous_const.prodMk continuous_id)
  have hpW : p.1 ∈ W := by
    change (f p, p.1) ∈ e.target
    simpa only [he] using e.map_source hep
  have hgraph (x : E) (hx : x ∈ W) : (x, ψ x) = e.symm (f p, x) := by
    have hh := congrArg Prod.snd (e.right_inv hx)
    change (e (e.symm (f p, x))).2 = x at hh
    rw [he] at hh
    exact Prod.ext hh.symm rfl
  refine ⟨W, e.source, ψ, hW, hpW, e.open_source, hep, heU, ?_, ?_, ?_, ?_⟩
  · have hh := congrArg Prod.snd (e.left_inv hep)
    change (e.symm (e p)).2 = p.2 at hh
    simpa only [he] using hh
  · exact (hei.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => hx)).snd
  · intro x hx
    rw [hgraph x hx]
    refine ⟨e.map_target hx, ?_⟩
    have hh := congrArg Prod.fst (e.right_inv hx)
    simpa only [he] using hh
  · intro x hx y hy hfxy
    have hh := e.left_inv hy
    have hexy : e (x, y) = (f p, x) := by
      rw [he]
      exact Prod.ext hfxy rfl
    rw [hexy] at hh
    exact (congrArg Prod.snd hh).symm

end SemiHamiltonian.Geometry
