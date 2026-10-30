module

public import SemiHamiltonian.Geometry.ConservationJetSufficiency

/-! Coordinate invariance of the critical Hessian freedom and the full
conservation-law jet criterion. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Geometry

open Smooth PSS.FrameData

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {U : Set (ι → ℝ)} {M N : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)}

noncomputable def pullbackBilinear
    (B : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (ι → ℝ) (ι → ℝ) ℝ).flip L).comp (B.comp L)

theorem pullbackBilinear_apply (B : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ)
    (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) (x y : ι → ℝ) :
    pullbackBilinear B L x y = B (L x) (L y) := rfl

/-- At a critical point the second derivative of the inverse chart drops out. -/
theorem chartScalar_hessian_at_critical
    (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    (hi : ContDiffOn ℝ ∞ e.symm e.target) (f : Functions e.source) (r : e.target)
    (hf : fderiv ℝ (extend e.source f) (e.symm r) = 0) (x y : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (extend e.target (chartScalar e hi f))) r x y =
      fderiv ℝ (fderiv ℝ (extend e.source f)) (e.symm r)
        (fderiv ℝ e.symm r x) (fderiv ℝ e.symm r y) := by
  have heq : fderiv ℝ (extend e.target (chartScalar e hi f)) =ᶠ[𝓝 (r : ι → ℝ)]
      fun z => (fderiv ℝ (extend e.source f) (e.symm z)).comp (fderiv ℝ e.symm z) := by
    filter_upwards [e.open_target.mem_nhds r.property] with z hz
    exact chartScalar_fderiv e hi f ⟨z, hz⟩
  have hdf := (((smooth e.source f).fderiv_of_isOpen e.open_source (m := ∞) (by simp)).contDiffAt
    (e.open_source.mem_nhds (e.map_target r.property))).differentiableAt (by simp)
  have hdi := (hi.contDiffAt (e.open_target.mem_nhds r.property)).differentiableAt (by simp)
  have hddi := ((hi.fderiv_of_isOpen e.open_target (m := ∞) (by simp)).contDiffAt
    (e.open_target.mem_nhds r.property)).differentiableAt (by simp)
  have hder := ((hdf.hasFDerivAt.comp (r : ι → ℝ) hdi.hasFDerivAt).clm_comp hddi.hasFDerivAt).fderiv
  change fderiv ℝ (fun z => (fderiv ℝ (extend e.source f) (e.symm z)).comp (fderiv ℝ e.symm z)) r = _ at hder
  rw [heq.fderiv_eq, hder]
  simp [hf, Function.comp_def]

theorem RealizesConservationHessians.chart
    (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hd : ∀ (p : e.source) z, fderiv ℝ e p (M p z) = N (e p) (fderiv ℝ e p z))
    (p : e.source) (h : RealizesConservationHessians M e.source p) :
    RealizesConservationHessians N e.target (e p) := by
  intro B hsym hcompat
  let L := fderiv ℝ e p
  let C := pullbackBilinear B L
  have hCs (x y : ι → ℝ) : C x y = C y x := hsym (L x) (L y)
  have hCc (x y : ι → ℝ) : C (M p x) y = C x (M p y) := by
    change B (fderiv ℝ e p (M p x)) (L y) = B (L x) (fderiv ℝ e p (M p y))
    rw [hd p x, hd p y]
    exact hcompat (L x) (L y)
  obtain ⟨f, q, hq, hf, hff⟩ := h C hCs hCc
  have hfi : fderiv ℝ (extend e.source f) (e.symm (e p)) = 0 := by rw [e.left_inv p.property]; exact hf
  have hinv (z : ι → ℝ) : L (fderiv ℝ e.symm (e p) z) = z := by
    have hh := congrArg (fun D : (ι → ℝ) →L[ℝ] (ι → ℝ) => D z)
      (chart_fderiv_left_inverse e.symm hi he (e.map_source p.property))
    simpa only [OpenPartialHomeomorph.symm_symm, e.left_inv p.property, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hh
  refine ⟨chartScalar e hi f, chartScalar e hi q, matrixConservationLaw_chart e he hi hd hq, ?_, ?_⟩
  · rw [chartScalar_fderiv e hi f ⟨e p, e.map_source p.property⟩, e.left_inv p.property, hf, ContinuousLinearMap.zero_comp]
  · apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    rw [chartScalar_hessian_at_critical e hi f ⟨e p, e.map_source p.property⟩ hfi,
      e.left_inv p.property, hff]
    change B (L (fderiv ℝ e.symm (e p) x)) (L (fderiv ℝ e.symm (e p) y)) = B x y
    rw [hinv, hinv]

theorem LocallyRichConservationLaws.chart
    (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hd : ∀ (p : e.source) z, fderiv ℝ e p (M p z) = N (e p) (fderiv ℝ e p z))
    (h : LocallyRichConservationLaws M e.source) : LocallyRichConservationLaws N e.target := by
  intro r hr
  obtain ⟨V, hV, hVe, hpV, hg, hh⟩ := h (e.symm r) (e.map_target hr)
  let g := (chartTargetRestrict e.symm hV hVe).symm
  have hge : ContDiffOn ℝ ∞ g g.source := he.mono hVe
  have hgi : ContDiffOn ℝ ∞ g.symm g.target := hi.mono inter_subset_left
  have hdiag : ∀ (p : g.source) z, fderiv ℝ g p (M p z) = N (g p) (fderiv ℝ g p z) :=
    fun p z => hd ⟨p, hVe p.property⟩ z
  refine ⟨g.target, g.open_target, inter_subset_left, ⟨hr, hpV⟩, ?_, ?_⟩
  · have ht := hg.chart g hge hgi hdiag ⟨e.symm r, hpV⟩
    change RealizesConservationGradients N g.target (e (e.symm r)) at ht
    rwa [e.right_inv hr] at ht
  · have ht := hh.chart g hge hgi hdiag ⟨e.symm r, hpV⟩
    change RealizesConservationHessians N g.target (e (e.symm r)) at ht
    rwa [e.right_inv hr] at ht

theorem LocallySemiHamiltonian.locallyRichConservationLaws
    (h : LocallySemiHamiltonian M U) : LocallyRichConservationLaws M U := by
  intro p hp
  obtain ⟨e, he, hi, S, hep, heU, hd, hS⟩ := h p hp
  have ht := locallyRichConservationLaws_of_semiHamiltonian e.open_target S hS
  have hinv := chart_intertwining_symm e he hi (diagonalChart_matrix_equation e S hd)
  have hs := ht.chart e.symm hi he hinv
  obtain ⟨V, hV, hVe, hpV, hg, hh⟩ := hs p hep
  exact ⟨V, hV, hVe.trans heU, hpV, hg, hh⟩

theorem locallyRichConservationLaws_iff_locallySemiHamiltonian (hU : IsOpen U)
    (hM : ContDiffOn ℝ ∞ M U) (hs : ∀ p ∈ U, StrictHyperbolicAt M p) :
    LocallyRichConservationLaws M U ↔ LocallySemiHamiltonian M U :=
  ⟨fun h => h.locallySemiHamiltonian hU hM hs, fun h => h.locallyRichConservationLaws⟩

theorem locallyRichConservationLaws_iff_tensors (hU : IsOpen U)
    (hM : ContDiffOn ℝ ∞ M U) (hs : ∀ p ∈ U, StrictHyperbolicAt M p) :
    LocallyRichConservationLaws M U ↔
      MatrixHaantjesVanish M U ∧ PSSVanish hU (Endomorphism.ofField M hM) :=
  (locallyRichConservationLaws_iff_locallySemiHamiltonian hU hM hs).trans
    ((locallyRichMatrix_iff_locallySemiHamiltonian hU hM hs).symm.trans
      (locallyRichMatrix_iff_tensors hU hM hs))

end SemiHamiltonian.Geometry
