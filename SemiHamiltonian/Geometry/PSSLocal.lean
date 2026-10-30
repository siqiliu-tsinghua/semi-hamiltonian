module

public import SemiHamiltonian.Geometry.ChartTransport
public import SemiHamiltonian.Geometry.PSSDiagonal
public import SemiHamiltonian.Geometry.PSSRestriction
public import SemiHamiltonian.Geometry.HaantjesConverse

/-! The invariant PSS criterion for a general strictly hyperbolic smooth matrix
field: vanishing of H and P is equivalent to local Riemann coordinates with
arbitrary smooth single-variable data for the commuting-flow equations. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Geometry

open Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem chartPush_ofField_diagonal
    (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)) (hM : ContDiffOn ℝ ∞ M e.source)
    (S : System e.open_target)
    (hd : ∀ (q : e.source) z i,
      fderiv ℝ e q (M q z) i = S.speed i ⟨e q, e.map_source q.property⟩ * fderiv ℝ e q z i)
    (X : Fields e.source) :
    chartPush e he hi (Endomorphism.ofField M hM X) =
      PSS.FrameData.diagonalMap S.speed (chartPush e he hi X) := by
  funext i
  apply Subtype.ext
  funext r
  have hr := e.map_target r.property
  have hp := chartPush_eval e he hi (Endomorphism.ofField M hM X) r
  rw [Endomorphism.field_ofField M hM X (⟨e.symm r, hr⟩ : e.source)] at hp
  have hh := congrFun hp i
  rw [hd ⟨e.symm r, hr⟩] at hh
  simp only [field_apply, e.right_inv r.property] at hh
  change chartPush e he hi (Endomorphism.ofField M hM X) i r =
    S.speed i r * fderiv ℝ e (e.symm r) (field X (e.symm r)) i
  exact hh

/-- The tensor test in an actual diagonalizing chart, with no assumed covariance. -/
theorem pssVanish_iff_axisSolvable_in_chart
    (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)) (hM : ContDiffOn ℝ ∞ M e.source)
    (S : System e.open_target)
    (hd : ∀ (q : e.source) z i,
      fderiv ℝ e q (M q z) i = S.speed i ⟨e q, e.map_source q.property⟩ * fderiv ℝ e q z i) :
    PSSVanish e.open_source (Endomorphism.ofField M hM) ↔
      LocallyAxisSolvable e.open_target S :=
  (pssVanish_chart_iff e he hi _ _ (chartPush_ofField_diagonal e he hi M hM S hd)).trans
    (pssVanish_iff_locallyAxisSolvable e.open_target S)

/-- Local solutions with n arbitrary C∞ single-variable data in Riemann coordinates.
The chart, and the radius in `LocallyAxisSolvable`, are selected before the data.
The chart is part of the conclusion, not an assumption on the original matrix field. -/
def LocallyAxisIntegrable (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (U : Set (ι → ℝ)) : Prop :=
  ∀ p ∈ U, ∃ e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ),
    ∃ _he : ContDiffOn ℝ ∞ e e.source, ∃ _hi : ContDiffOn ℝ ∞ e.symm e.target,
      ∃ S : System e.open_target,
        p ∈ e.source ∧ e.source ⊆ U ∧
        (∀ (q : e.source) z i,
          fderiv ℝ e q (M q z) i =
            S.speed i ⟨e q, e.map_source q.property⟩ * fderiv ℝ e q z i) ∧
        LocallyAxisSolvable e.open_target S

theorem locallyAxisIntegrable_of_tensors {U : Set (ι → ℝ)} (hU : IsOpen U)
    {M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)} (hM : ContDiffOn ℝ ∞ M U)
    (hs : ∀ p ∈ U, StrictHyperbolicAt M p)
    (hH : MatrixHaantjesVanish M U) (hP : PSSVanish hU (Endomorphism.ofField M hM)) :
    LocallyAxisIntegrable M U := by
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
  refine ⟨e, he, hi, S, hep, heU, hdiag, ?_⟩
  exact (pssVanish_iff_axisSolvable_in_chart e he hi M (hM.mono heU) S hdiag).mp
    (pssVanish_restrict hU e.open_source heU M hM hP)

theorem tensors_of_locallyAxisIntegrable {U : Set (ι → ℝ)} (hU : IsOpen U)
    {M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)} (hM : ContDiffOn ℝ ∞ M U)
    (hI : LocallyAxisIntegrable M U) :
    MatrixHaantjesVanish M U ∧ PSSVanish hU (Endomorphism.ofField M hM) := by
  constructor
  · intro p hp
    obtain ⟨e, he, hi, S, hep, heU, hd, _⟩ := hI p hp
    let v : ι → (ι → ℝ) → ℝ := fun i q => extend e.target (S.speed i) (e q)
    have hv : ∀ i, ContDiffOn ℝ ∞ (v i) e.source := fun i =>
      (smooth e.target (S.speed i)).comp he e.mapsTo
    apply matrixHaantjesVanish_of_diagonalization e he hi (hM.mono heU) v hv _ p hep
    intro q hq z i
    simpa only [v, extend_apply e.target (S.speed i) ⟨e q, e.map_source hq⟩] using
      hd ⟨q, hq⟩ z i
  · apply pssVanish_of_local hU M hM
    intro p hp
    obtain ⟨e, he, hi, S, hep, heU, hd, hsol⟩ := hI p hp
    exact ⟨e.source, e.open_source, heU, hep,
      (pssVanish_iff_axisSolvable_in_chart e he hi M (hM.mono heU) S hd).mpr hsol⟩

/-- PSS's invariant test, joined to actual C∞ local existence and Haantjes coordinates. -/
theorem pss_iff_locallyAxisIntegrable {U : Set (ι → ℝ)} (hU : IsOpen U)
    {M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)} (hM : ContDiffOn ℝ ∞ M U)
    (hs : ∀ p ∈ U, StrictHyperbolicAt M p) :
    (MatrixHaantjesVanish M U ∧ PSSVanish hU (Endomorphism.ofField M hM)) ↔
      LocallyAxisIntegrable M U :=
  ⟨fun h => locallyAxisIntegrable_of_tensors hU hM hs h.1 h.2,
    tensors_of_locallyAxisIntegrable hU hM⟩

end SemiHamiltonian.Geometry
