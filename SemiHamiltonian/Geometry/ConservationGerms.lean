module

public import SemiHamiltonian.Geometry.ConservationJetTransport

/-! Intrinsic germs of actual conservation densities and their transport.
The flux is existential; density and flux constants are kept distinct. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Smooth

open PSS.FrameData

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def IsMatrixDensityGerm (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (U : Set (ι → ℝ)) (p : ι → ℝ) (g : Germ (𝓝 p) ℝ) : Prop :=
  ∃ V, IsOpen V ∧ V ⊆ U ∧ p ∈ V ∧ ∃ h q : Functions V,
    IsMatrixConservationLaw M h q ∧ (extend V h : Germ (𝓝 p) ℝ) = g

def MatrixDensityGerm (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (U : Set (ι → ℝ)) (p : ι → ℝ) :=
  {g : Germ (𝓝 p) ℝ // IsMatrixDensityGerm M U p g}

variable {U V : Set (ι → ℝ)} {M N : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)}
  {p : ι → ℝ}

theorem IsMatrixDensityGerm.restrict {g : Germ (𝓝 p) ℝ}
    (h : IsMatrixDensityGerm M U p g) (hV : IsOpen V) (hpV : p ∈ V) :
    IsMatrixDensityGerm M V p g := by
  obtain ⟨T, hT, hTU, hpT, f, q, hq, hfg⟩ := h
  refine ⟨T ∩ V, hT.inter hV, inter_subset_right, ⟨hpT, hpV⟩,
    Smooth.restrict inter_subset_left f, Smooth.restrict inter_subset_left q,
    hq.restrict (hT.inter hV) inter_subset_left, ?_⟩
  exact (extend_restrict_eventually (hT.inter hV) inter_subset_left f ⟨p, hpT, hpV⟩).germ_eq.trans hfg

theorem IsMatrixDensityGerm.mono {g : Germ (𝓝 p) ℝ}
    (h : IsMatrixDensityGerm M V p g) (hVU : V ⊆ U) : IsMatrixDensityGerm M U p g := by
  obtain ⟨T, hT, hTV, hpT, f, q, hq, hfg⟩ := h
  exact ⟨T, hT, hTV.trans hVU, hpT, f, q, hq, hfg⟩

/-- Restriction changes representatives, not the intrinsic scalar germ. -/
noncomputable def matrixDensityGermRestrictEquiv (hV : IsOpen V) (hVU : V ⊆ U) (hpV : p ∈ V) :
    MatrixDensityGerm M U p ≃ MatrixDensityGerm M V p where
  toFun g := ⟨g.val, g.property.restrict hV hpV⟩
  invFun g := ⟨g.val, g.property.mono hVU⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Pullback through a smooth map intertwining the two matrix fields. -/
theorem IsMatrixDensityGerm.pullback {T : Set (ι → ℝ)} (hT : IsOpen T)
    (f : (ι → ℝ) → (ι → ℝ)) (hf : ContDiffOn ℝ ∞ f T) (hm : MapsTo f T U)
    (hd : ∀ x ∈ T, ∀ z, fderiv ℝ f x (N x z) = M (f x) (fderiv ℝ f x z))
    {r : ι → ℝ} (hr : r ∈ T) (ht : Tendsto f (𝓝 r) (𝓝 p))
    {g : Germ (𝓝 p) ℝ} (h : IsMatrixDensityGerm M U p g) :
    IsMatrixDensityGerm N T r (g.compTendsto f ht) := by
  obtain ⟨V, hV, hVU, hpV, a, b, hab, hag⟩ := h
  let W := T ∩ f ⁻¹' V
  have hW : IsOpen W := hf.continuousOn.isOpen_inter_preimage hT hV
  have hfr : f r = p := tendsto_nhds_unique (hf.continuousOn.continuousAt (hT.mem_nhds hr)) ht
  have hrW : r ∈ W := ⟨hr, show f r ∈ V from hfr.symm ▸ hpV⟩
  have hs (c : Functions V) : ContDiffOn ℝ ∞ (fun x => extend V c (f x)) W :=
    (smooth V c).comp (hf.mono inter_subset_left) (fun _ hx => hx.2)
  let C := fun c : Functions V => ofContDiffOn (fun x => extend V c (f x)) (hs c)
  have hder (c : Functions V) (x : W) : fderiv ℝ (extend W (C c)) x =
      (fderiv ℝ (extend V c) (f x)).comp (fderiv ℝ f x) := by
    rw [(extend_ofContDiffOn_eventuallyEq hW _ (hs c) x.property).fderiv_eq]
    exact ((hasFDerivAt_extend hV c ⟨f x, x.property.2⟩).comp (x : ι → ℝ)
      ((hf.contDiffAt (hT.mem_nhds x.property.1)).differentiableAt (by simp)).hasFDerivAt).fderiv
  refine ⟨W, hW, inter_subset_left, hrW, C a, C b, ?_, ?_⟩
  · intro x
    rw [hder, hder, hab ⟨f x, x.property.2⟩]
    apply ContinuousLinearMap.ext
    intro z
    change fderiv ℝ (extend V a) (f x) (M (f x) (fderiv ℝ f x z)) =
      fderiv ℝ (extend V a) (f x) (fderiv ℝ f x (N x z))
    rw [hd x x.property.1 z]
  · rw [← hag, Germ.coe_compTendsto]
    apply Filter.EventuallyEq.germ_eq
    exact extend_ofContDiffOn_eventuallyEq hW _ (hs a) hrW

theorem matrixDensityGerm_diagonal_iff (hU : IsOpen U) (S : System hU) (p : U)
    (g : Germ (𝓝 (p : ι → ℝ)) ℝ) :
    IsMatrixDensityGerm (Endomorphism.matrix (diagonalMap S.speed)) U p g ↔
      ∃ V, ∃ hV : IsOpen V, ∃ hVU : V ⊆ U, (p : ι → ℝ) ∈ V ∧
        ∃ h : Functions V, (restrictSystem hU hV hVU S).IsDensity h ∧
          (extend V h : Germ (𝓝 (p : ι → ℝ)) ℝ) = g := by
  constructor
  · rintro ⟨V, hV, hVU, hpV, h, q, hh, hg⟩
    exact ⟨V, hV, hVU, hpV, h, (restrictSystem hU hV hVU S).conservationLaw_density
      ((diagonal_conservationLaw_iff hU hV hVU S h q).mpr hh), hg⟩
  · rintro ⟨V, hV, hVU, hpV, h, hh, hg⟩
    obtain ⟨T, hT, hTV, hpT, q, _, hq⟩ := exists_local_flux hV _ h hh ⟨p, hpV⟩ 0
    have he : (restrictSystem hU hT (hTV.trans hVU) S).IsConservationLaw (Smooth.restrict hTV h) q := by
      rw [← restrictSystem_trans hU hV hT hVU hTV S]
      exact hq
    exact ⟨T, hT, hTV.trans hVU, hpT, Smooth.restrict hTV h, q,
      (diagonal_conservationLaw_iff hU hT (hTV.trans hVU) S _ _).mp he,
      (extend_restrict_eventually hT hTV h ⟨p, hpT⟩).germ_eq.trans hg⟩

noncomputable def matrixDensityGermDiagonalEquiv (hU : IsOpen U) (S : System hU) (p : U) :
    MatrixDensityGerm (Endomorphism.matrix (diagonalMap S.speed)) U p ≃ DensityGerm hU S p where
  toFun g := ⟨g.val, (matrixDensityGerm_diagonal_iff hU S p g.val).mp g.property⟩
  invFun g := ⟨g.val, (matrixDensityGerm_diagonal_iff hU S p g.val).mpr g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end SemiHamiltonian.Smooth

namespace SemiHamiltonian.Geometry

open Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {M N : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)}
  (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
  (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
  (p : e.source)

theorem chart_inverse_tendsto : Tendsto e.symm (𝓝 (e p)) (𝓝 (p : ι → ℝ)) := by
  have hh := (e.continuousAt_symm (e.map_source p.property)).tendsto
  rwa [e.left_inv p.property] at hh

noncomputable def scalarGermChartEquiv : Germ (𝓝 (p : ι → ℝ)) ℝ ≃ Germ (𝓝 (e p)) ℝ where
  toFun g := g.compTendsto e.symm (chart_inverse_tendsto e p)
  invFun g := g.compTendsto e (e.continuousAt p.property).tendsto
  left_inv g := by
    induction g using Germ.inductionOn with | h f =>
      change ((fun x => f (e.symm (e x))) : Germ (𝓝 (p : ι → ℝ)) ℝ) = (f : Germ (𝓝 (p : ι → ℝ)) ℝ)
      apply Filter.EventuallyEq.germ_eq
      filter_upwards [e.open_source.mem_nhds p.property] with x hx
      exact congrArg f (e.left_inv hx)
  right_inv g := by
    induction g using Germ.inductionOn with | h f =>
      change ((fun x => f (e (e.symm x))) : Germ (𝓝 (e p)) ℝ) = (f : Germ (𝓝 (e p)) ℝ)
      apply Filter.EventuallyEq.germ_eq
      filter_upwards [e.open_target.mem_nhds (e.map_source p.property)] with x hx
      exact congrArg f (e.right_inv hx)

/-- Every original-coordinate conservation density germ is transported, and
the inverse transport recovers it as a germ. -/
noncomputable def matrixDensityGermChartEquiv
    (hd : ∀ (x : e.source) z, fderiv ℝ e x (M x z) = N (e x) (fderiv ℝ e x z)) :
    MatrixDensityGerm M e.source p ≃ MatrixDensityGerm N e.target (e p) where
  toFun g := ⟨scalarGermChartEquiv e p g.val,
    g.property.pullback e.open_target e.symm hi e.symm.mapsTo
      (fun r hr z => chart_intertwining_symm e he hi hd ⟨r, hr⟩ z)
      (e.map_source p.property) (chart_inverse_tendsto e p)⟩
  invFun g := ⟨(scalarGermChartEquiv e p).symm g.val,
    g.property.pullback e.open_source e he e.mapsTo
      (fun x hx z => hd ⟨x, hx⟩ z) p.property (e.continuousAt p.property).tendsto⟩
  left_inv g := Subtype.ext ((scalarGermChartEquiv e p).left_inv g.val)
  right_inv g := Subtype.ext ((scalarGermChartEquiv e p).right_inv g.val)

end SemiHamiltonian.Geometry
