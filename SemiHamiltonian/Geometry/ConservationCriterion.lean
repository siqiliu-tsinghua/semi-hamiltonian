module

public import SemiHamiltonian.Geometry.ConservationJets
public import SemiHamiltonian.Geometry.Integrability
public import SemiHamiltonian.Analysis.ConservationLaws

/-! Necessity in PSS theorem 5 for general smooth matrix fields. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Geometry

open Smooth PSS.FrameData

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {U V : Set (ι → ℝ)} {M N : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)}

theorem chartScalar_fderiv
    (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    (hi : ContDiffOn ℝ ∞ e.symm e.target) (f : Functions e.source) (r : e.target) :
    fderiv ℝ (extend e.target (chartScalar e hi f)) r =
      (fderiv ℝ (extend e.source f) (e.symm r)).comp (fderiv ℝ e.symm r) := by
  unfold chartScalar
  rw [(extend_ofContDiffOn_eventuallyEq e.open_target _ _ r.property).fderiv_eq]
  exact ((hasFDerivAt_extend e.open_source f ⟨e.symm r, e.map_target r.property⟩).comp (r : ι → ℝ)
    ((hi.contDiffAt (e.open_target.mem_nhds r.property)).differentiableAt
      (by simp)).hasFDerivAt).fderiv

theorem matrixConservationLaw_chart
    (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hd : ∀ (p : e.source) z, fderiv ℝ e p (M p z) = N (e p) (fderiv ℝ e p z))
    {h q : Functions e.source} (hq : IsMatrixConservationLaw M h q) :
    IsMatrixConservationLaw N (chartScalar e hi h) (chartScalar e hi q) := by
  intro r
  rw [chartScalar_fderiv, chartScalar_fderiv, hq ⟨e.symm r, e.map_target r.property⟩]
  ext z
  change fderiv ℝ (extend e.source h) (e.symm r) (M (e.symm r) (fderiv ℝ e.symm r z)) =
    fderiv ℝ (extend e.source h) (e.symm r) (fderiv ℝ e.symm r (N r z))
  rw [chart_intertwining_symm e he hi hd r z]

theorem RealizesConservationGradients.chart
    (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hd : ∀ (p : e.source) z, fderiv ℝ e p (M p z) = N (e p) (fderiv ℝ e p z))
    (p : e.source) (h : RealizesConservationGradients M e.source p) :
    RealizesConservationGradients N e.target (e p) := by
  intro a
  obtain ⟨f, q, hq, hf⟩ := h (a.comp (fderiv ℝ e p))
  refine ⟨chartScalar e hi f, chartScalar e hi q, matrixConservationLaw_chart e he hi hd hq, ?_⟩
  rw [chartScalar_fderiv e hi f ⟨e p, e.map_source p.property⟩, e.left_inv p.property, hf,
    ContinuousLinearMap.comp_assoc]
  have hh := chart_fderiv_left_inverse e.symm hi he (e.map_source p.property)
  simp only [OpenPartialHomeomorph.symm_symm, e.left_inv p.property] at hh
  rw [hh, ContinuousLinearMap.comp_id]

def LocallyConservationGradientRich (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (U : Set (ι → ℝ)) : Prop :=
  ∀ p ∈ U, ∃ V, IsOpen V ∧ V ⊆ U ∧ p ∈ V ∧ RealizesConservationGradients M V p

theorem LocallyRichConservationLaws.gradientRich (h : LocallyRichConservationLaws M U) :
    LocallyConservationGradientRich M U := by
  intro p hp
  obtain ⟨V, hV, hVU, hpV, hg, _⟩ := h p hp
  exact ⟨V, hV, hVU, hpV, hg⟩

theorem LocallyConservationGradientRich.chart
    (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hd : ∀ (p : e.source) z, fderiv ℝ e p (M p z) = N (e p) (fderiv ℝ e p z))
    (h : LocallyConservationGradientRich M e.source) :
    LocallyConservationGradientRich N e.target := by
  intro r hr
  obtain ⟨V, hV, hVe, hpV, hreal⟩ := h (e.symm r) (e.map_target hr)
  let g := (chartTargetRestrict e.symm hV hVe).symm
  have hg : ContDiffOn ℝ ∞ g g.source := he.mono hVe
  have hgi : ContDiffOn ℝ ∞ g.symm g.target := hi.mono inter_subset_left
  have hdiag : ∀ (p : g.source) z,
      fderiv ℝ g p (M p z) = N (g p) (fderiv ℝ g p z) := fun p z => hd ⟨p, hVe p.property⟩ z
  refine ⟨g.target, g.open_target, inter_subset_left, ⟨hr, hpV⟩, ?_⟩
  have hh := hreal.chart g hg hgi hdiag ⟨e.symm r, hpV⟩
  change RealizesConservationGradients N g.target (e (e.symm r)) at hh
  rwa [e.right_inv hr] at hh

theorem semiHamiltonian_of_conservationGradientRich (hU : IsOpen U) (S : System hU)
    (h : LocallyConservationGradientRich (Endomorphism.matrix (diagonalMap S.speed)) U) :
    S.IsSemiHamiltonian := by
  intro i j k hij hik hjk
  apply Subtype.ext
  funext p
  obtain ⟨V, hV, hVU, hpV, hreal⟩ := h p p.property
  obtain ⟨f, q, hq, hf⟩ := hreal (ContinuousLinearMap.proj i)
  let SV := restrictSystem hU hV hVU S
  have hq' : SV.IsConservationLaw f q := by
    intro a
    apply Subtype.ext
    funext x
    change directional hV (Pi.single a 1) q x =
      Smooth.restrict hVU (S.speed a) x * directional hV (Pi.single a 1) f x
    rw [directional_apply, directional_apply, Smooth.restrict_apply]
    rw [hq x]
    change fderiv ℝ (extend V f) x (Endomorphism.matrix (diagonalMap S.speed) x (Pi.single a 1)) = _
    have hd : Endomorphism.matrix (diagonalMap S.speed) x (Pi.single a 1) =
        S.speed a ⟨x, hVU x.property⟩ • Pi.single a 1 := by
      ext b
      rw [diagonalMap_matrix_apply S.speed ⟨x, hVU x.property⟩]
      by_cases hab : a = b <;> simp [Pi.single_apply, hab, eq_comm]
    rw [hd, map_smul, smul_eq_mul]
  let a : ι → Functions V := fun r => (coordinateDerivations hV).deriv r f
  have ha : SV.IsDensityGradient a := SV.conservationLaw_density hq'
  have hav (r : ι) : eval (⟨p, hpV⟩ : V) (a r) = if r = i then 1 else 0 := by
    change fderiv ℝ (extend V f) p (Pi.single r 1) = _
    rw [hf]
    simp [Pi.single_apply, eq_comm]
  have hz := SV.densityObstruction_eq_zero_of_solution ha i j k hij hik hjk
  rw [SV.densityObstruction_eq] at hz
  have hh := congrArg (eval (⟨p, hpV⟩ : V)) hz
  simp only [map_sub, map_add, map_mul, map_zero, hav] at hh
  simp only [ite_true, hij.symm, hik.symm, ite_false, mul_one, mul_zero, add_zero,
    sub_zero] at hh
  have hd (r s t : ι) : eval (⟨p, hpV⟩ : V) ((coordinateDerivations hV).deriv t (SV.coeff r s)) =
      (coordinateDerivations hU).deriv t (S.coeff r s) p := by
    change derivation hV (Pi.single t 1) (Smooth.restrict hVU (S.coeff r s)) ⟨p, hpV⟩ = _
    rw [← restrict_derivation hU hV, Smooth.restrict_apply]
    rfl
  rw [hd, hd] at hh
  exact sub_eq_zero.mp hh

/-- PSS theorem 5, necessity: actual conservation-law jet freedom implies
both actual Riemann coordinates and the semi-Hamiltonian equations. -/
theorem LocallyRichConservationLaws.locallySemiHamiltonian (hU : IsOpen U)
    (hM : ContDiffOn ℝ ∞ M U) (h : LocallyRichConservationLaws M U)
    (hs : ∀ p ∈ U, StrictHyperbolicAt M p) : LocallySemiHamiltonian M U := by
  have hH := h.haantjesVanish hM hs
  intro p hp
  obtain ⟨e, v, hep, heU, he, hi, hv, hvsep, hd⟩ :=
    haantjes_local_diagonalization hU hM hH hp (hs p hp)
  let w : ι → Functions e.target := fun i =>
    ofContDiffOn (fun r => v i (e.symm r)) ((hv i).comp hi e.symm.mapsTo)
  have hw : StrictlyHyperbolic w := by
    intro r i j hij hval
    exact hij (hvsep (e.symm r) (e.map_target r.property) hval)
  let S : System e.open_target := ofSpeeds e.open_target w hw
  have hdiag : ∀ (q : e.source) z i, fderiv ℝ e q (M q z) i =
      S.speed i ⟨e q, e.map_source q.property⟩ * fderiv ℝ e q z i := by
    intro q z i
    change _ = v i (e.symm (e q)) * _
    rw [e.left_inv q.property]
    exact hd q q.property z i
  have ht := (h.restrict e.open_source heU).gradientRich.chart e he hi
    (diagonalChart_matrix_equation e S hdiag)
  exact ⟨e, he, hi, S, hep, heU, hdiag,
    semiHamiltonian_of_conservationGradientRich e.open_target S ht⟩

theorem LocallyRichConservationLaws.tensors_vanish (hU : IsOpen U)
    (hM : ContDiffOn ℝ ∞ M U) (h : LocallyRichConservationLaws M U)
    (hs : ∀ p ∈ U, StrictHyperbolicAt M p) :
    MatrixHaantjesVanish M U ∧ PSSVanish hU (Endomorphism.ofField M hM) :=
  (locallyRichMatrix_iff_tensors hU hM hs).mp
    ((h.locallySemiHamiltonian hU hM hs).locallyRichMatrix hM)

end SemiHamiltonian.Geometry
