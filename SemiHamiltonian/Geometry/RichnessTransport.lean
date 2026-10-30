module

public import SemiHamiltonian.Geometry.MatrixRichness
public import SemiHamiltonian.Geometry.PSSExistence

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Geometry

open Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
  (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)

theorem chartEndomorphism_matrix_intertwines (A : Endomorphism e.source)
    (p : e.source) (z : ι → ℝ) :
    fderiv ℝ e p (A.matrix p z) =
      (chartEndomorphism e he hi A).matrix (e p) (fderiv ℝ e p z) := by
  have hh := congrArg (fun X : Fields e.target => field X (⟨e p, e.map_source p.property⟩ : e.target))
    (chartEndomorphism_intertwines e he hi A (constantField z))
  rw [← Endomorphism.matrix_field] at hh
  rw [chartPush_eval, chartPush_eval] at hh
  simp only [e.left_inv p.property] at hh
  rw [← A.matrix_field, field_constantField] at hh
  exact hh

theorem chartPush_ofField
    {M N : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hM : ContDiffOn ℝ ∞ M e.source) (hN : ContDiffOn ℝ ∞ N e.target)
    (hd : ∀ (q : e.source) z, fderiv ℝ e q (M q z) = N (e q) (fderiv ℝ e q z))
    (X : Fields e.source) :
    chartPush e he hi (Endomorphism.ofField M hM X) =
      Endomorphism.ofField N hN (chartPush e he hi X) := by
  funext i
  apply Subtype.ext
  funext r
  have hh := chartPush_eval e he hi (Endomorphism.ofField M hM X) r
  rw [Endomorphism.field_ofField M hM X ⟨e.symm r, e.map_target r.property⟩,
    hd ⟨e.symm r, e.map_target r.property⟩, e.right_inv r.property] at hh
  have hh' := Endomorphism.field_ofField N hN (chartPush e he hi X) r
  rw [chartPush_eval] at hh'
  simpa only [field_apply] using congrFun (hh.trans hh'.symm) i

theorem chartEndomorphism_ofField
    {M N : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hM : ContDiffOn ℝ ∞ M e.source) (hN : ContDiffOn ℝ ∞ N e.target)
    (hd : ∀ (q : e.source) z, fderiv ℝ e q (M q z) = N (e q) (fderiv ℝ e q z)) :
    chartEndomorphism e he hi (Endomorphism.ofField M hM) = Endomorphism.ofField N hN := by
  apply LinearMap.ext
  intro X
  obtain ⟨Y, rfl⟩ := (chartPushEquiv e he hi).surjective X
  change chartEndomorphism e he hi (Endomorphism.ofField M hM) (chartPush e he hi Y) = _
  rw [← chartEndomorphism_intertwines]
  exact chartPush_ofField e he hi hM hN hd Y

include he hi

omit [DecidableEq ι] in
theorem chart_intertwining_symm
    {M N : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hd : ∀ (q : e.source) z, fderiv ℝ e q (M q z) = N (e q) (fderiv ℝ e q z)) :
    ∀ (r : e.target) z,
      fderiv ℝ e.symm r (N r z) = M (e.symm r) (fderiv ℝ e.symm r z) := by
  intro r z
  apply chart_fderiv_injective e he hi (e.map_target r.property)
  have hr (y : ι → ℝ) : fderiv ℝ e (e.symm r) (fderiv ℝ e.symm r y) = y :=
    congrArg (fun L : (ι → ℝ) →L[ℝ] (ι → ℝ) => L y)
      (chart_fderiv_left_inverse e.symm hi he r.property)
  rw [hd ⟨e.symm r, e.map_target r.property⟩, hr, hr, e.right_inv r.property]

/-- Prescribed values in the centralizer are preserved by an actual smooth chart. -/
theorem RealizesCentralizer.chart
    {M N : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hM : ContDiffOn ℝ ∞ M e.source) (hN : ContDiffOn ℝ ∞ N e.target)
    (hd : ∀ (q : e.source) z, fderiv ℝ e q (M q z) = N (e q) (fderiv ℝ e q z))
    (p : e.source) (h : RealizesCentralizer e.open_source hM p) :
    RealizesCentralizer e.open_target hN (e p) := by
  intro T hT
  let D := fderiv ℝ e p
  have hD : D.IsInvertible := chart_fderiv_invertible e he hi p.property
  let R := D.inverse.comp (T.comp D)
  have hR (z : ι → ℝ) : D (R z) = T (D z) := hD.self_apply_inverse _
  have hc : Function.Commute (M p) R := by
    intro z
    apply hD.injective
    rw [hd p, hR, hR, hd p, hT]
  obtain ⟨B, hB, hval⟩ := h R hc
  refine ⟨chartEndomorphism e he hi B, ?_, ?_⟩
  · have hh := (hydrodynamicSymmetry_conjugate_iff e he hi _ _).mp hB
    rwa [chartEndomorphism_ofField e he hi hM hN hd] at hh
  · apply ContinuousLinearMap.ext
    intro z
    obtain ⟨y, rfl⟩ := hD.surjective z
    rw [← chartEndomorphism_matrix_intertwines e he hi B p y, hval]
    exact hR y

/-- Local richness is coordinate invariant, including the domain chosen before values. -/
theorem LocallyRichMatrix.chart
    {M N : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hM : ContDiffOn ℝ ∞ M e.source) (hN : ContDiffOn ℝ ∞ N e.target)
    (hd : ∀ (q : e.source) z, fderiv ℝ e q (M q z) = N (e q) (fderiv ℝ e q z))
    (h : LocallyRichMatrix hM) : LocallyRichMatrix hN := by
  intro r hr
  obtain ⟨V, hV, hVe, hpV, hreal⟩ := h (e.symm r) (e.map_target hr)
  let g := (chartTargetRestrict e.symm hV hVe).symm
  have hg : ContDiffOn ℝ ∞ g g.source := he.mono hVe
  have hgi : ContDiffOn ℝ ∞ g.symm g.target := hi.mono inter_subset_left
  have hgt : g.target ⊆ e.target := inter_subset_left
  have hdiag : ∀ (q : g.source) z,
      fderiv ℝ g q (M q z) = N (g q) (fderiv ℝ g q z) := fun q z => hd ⟨q, hVe q.property⟩ z
  refine ⟨g.target, g.open_target, hgt, ⟨hr, hpV⟩, ?_⟩
  have hh := hreal.chart g hg hgi (hM.mono hVe) (hN.mono hgt) hdiag ⟨e.symm r, hpV⟩
  change RealizesCentralizer g.open_target (hN.mono hgt) (e (e.symm r)) at hh
  rwa [e.right_inv hr] at hh

end SemiHamiltonian.Geometry
