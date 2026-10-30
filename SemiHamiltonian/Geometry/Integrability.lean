module

public import SemiHamiltonian.Geometry.RichnessTransport
public import SemiHamiltonian.Geometry.DiagonalRichness

/-! The local C∞ Tsarev--PSS integrability equivalence for a general matrix field
with pairwise distinct real eigenvalues. The symmetry-richness hypothesis is
intrinsic and makes no prior assumption of diagonalizing coordinates. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Geometry

open Smooth PSS.FrameData

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {U : Set (ι → ℝ)} {M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)}

/-- Riemann coordinates exist locally and the resulting speeds are semi-Hamiltonian. -/
def LocallySemiHamiltonian (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (U : Set (ι → ℝ)) : Prop :=
  ∀ p ∈ U, ∃ e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ),
    ∃ _he : ContDiffOn ℝ ∞ e e.source, ∃ _hi : ContDiffOn ℝ ∞ e.symm e.target,
      ∃ S : System e.open_target,
        p ∈ e.source ∧ e.source ⊆ U ∧
        (∀ (q : e.source) z i, fderiv ℝ e q (M q z) i =
          S.speed i ⟨e q, e.map_source q.property⟩ * fderiv ℝ e q z i) ∧
        S.IsSemiHamiltonian

theorem locallySemiHamiltonian_iff_locallyAxisIntegrable :
    LocallySemiHamiltonian M U ↔ LocallyAxisIntegrable M U := by
  constructor
  · intro h p hp
    obtain ⟨e, he, hi, S, hep, heU, hd, hS⟩ := h p hp
    exact ⟨e, he, hi, S, hep, heU, hd,
      (semiHamiltonian_iff_locallyAxisSolvable e.open_target S).mp hS⟩
  · intro h p hp
    obtain ⟨e, he, hi, S, hep, heU, hd, hS⟩ := h p hp
    exact ⟨e, he, hi, S, hep, heU, hd,
      (semiHamiltonian_iff_locallyAxisSolvable e.open_target S).mpr hS⟩

theorem diagonalChart_matrix_equation
    (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ)) (S : System e.open_target)
    (hd : ∀ (q : e.source) z i, fderiv ℝ e q (M q z) i =
      S.speed i ⟨e q, e.map_source q.property⟩ * fderiv ℝ e q z i) :
    ∀ (q : e.source) z, fderiv ℝ e q (M q z) =
      Endomorphism.matrix (diagonalMap S.speed) (e q) (fderiv ℝ e q z) := by
  intro q z
  funext i
  rw [diagonalMap_matrix_apply S.speed ⟨e q, e.map_source q.property⟩]
  exact hd q z i

/-- Necessity: pointwise freedom of actual local symmetries supplies both the
Riemann coordinates and the semi-Hamiltonian compatibility equations. -/
theorem LocallyRichMatrix.locallySemiHamiltonian (hU : IsOpen U)
    {hM : ContDiffOn ℝ ∞ M U} (h : LocallyRichMatrix hM)
    (hs : ∀ p ∈ U, StrictHyperbolicAt M p) : LocallySemiHamiltonian M U := by
  have hH := h.haantjesVanish hs
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
  have htarget := (h.restrict e.open_source heU).chart e he hi (hM.mono heU)
    (Endomorphism.matrix_smooth (diagonalMap S.speed)) (diagonalChart_matrix_equation e S hdiag)
  refine ⟨e, he, hi, S, hep, heU, hdiag, ?_⟩
  exact semiHamiltonian_of_locallyRich e.open_target S
    ((locallyRichMatrix_iff_locallyRich e.open_target S).mp htarget)

/-- Sufficiency: actual Darboux solutions give all centralizer values on a
common neighbourhood in the original dependent variables. -/
theorem LocallySemiHamiltonian.locallyRichMatrix (hM : ContDiffOn ℝ ∞ M U)
    (h : LocallySemiHamiltonian M U) : LocallyRichMatrix hM := by
  intro p hp
  obtain ⟨e, he, hi, S, hep, heU, hd, hS⟩ := h p hp
  have ht : LocallyRichMatrix (Endomorphism.matrix_smooth (diagonalMap S.speed)) :=
    (locallyRichMatrix_iff_locallyRich e.open_target S).mpr
      ((semiHamiltonian_iff_locallyRich e.open_target S).mp hS)
  have hinv := chart_intertwining_symm e he hi (diagonalChart_matrix_equation e S hd)
  have hsource := ht.chart e.symm hi he (Endomorphism.matrix_smooth (diagonalMap S.speed))
    (hM.mono heU) hinv
  obtain ⟨V, hV, hVe, hpV, hreal⟩ := hsource p hep
  exact ⟨V, hV, hVe.trans heU, hpV, hreal⟩

/-- The intrinsic local integrability equivalence under a simple real spectrum. -/
theorem locallyRichMatrix_iff_locallySemiHamiltonian (hU : IsOpen U)
    (hM : ContDiffOn ℝ ∞ M U) (hs : ∀ p ∈ U, StrictHyperbolicAt M p) :
    LocallyRichMatrix hM ↔ LocallySemiHamiltonian M U :=
  ⟨fun h => h.locallySemiHamiltonian hU hs, fun h => h.locallyRichMatrix hM⟩

/-- Pointwise freedom of local actual symmetry operators is equivalent to
local actual solutions with n arbitrary smooth one-variable axis data. -/
theorem locallyRichMatrix_iff_locallyAxisIntegrable (hU : IsOpen U)
    (hM : ContDiffOn ℝ ∞ M U) (hs : ∀ p ∈ U, StrictHyperbolicAt M p) :
    LocallyRichMatrix hM ↔ LocallyAxisIntegrable M U :=
  (locallyRichMatrix_iff_locallySemiHamiltonian hU hM hs).trans
    locallySemiHamiltonian_iff_locallyAxisIntegrable

/-- The coordinate-free PSS tensor criterion for intrinsic symmetry richness. -/
theorem locallyRichMatrix_iff_tensors (hU : IsOpen U)
    (hM : ContDiffOn ℝ ∞ M U) (hs : ∀ p ∈ U, StrictHyperbolicAt M p) :
    LocallyRichMatrix hM ↔
      MatrixHaantjesVanish M U ∧ PSSVanish hU (Endomorphism.ofField M hM) :=
  (locallyRichMatrix_iff_locallyAxisIntegrable hU hM hs).trans
    (pss_iff_locallyAxisIntegrable hU hM hs).symm

end SemiHamiltonian.Geometry
