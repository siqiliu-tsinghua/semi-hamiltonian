module

public import SemiHamiltonian.Geometry.PSSLocal
public import SemiHamiltonian.Geometry.SymmetryTransport

/-! The arbitrary-data solutions supplied by the invariant PSS criterion,
expressed as actual smooth symmetry operators in the original variables. -/

@[expose] public section

open scoped Topology ContDiff Classical NNReal
open Set

namespace SemiHamiltonian.Geometry

open Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Restrict a chart to a prescribed open subset of its target. The target is
definitionally that subset, avoiding any extension of the local PDE solutions. -/
def chartTargetRestrict (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    {V : Set (ι → ℝ)} (hV : IsOpen V) (hVe : V ⊆ e.target) :
    OpenPartialHomeomorph (ι → ℝ) (ι → ℝ) where
  toFun := e
  invFun := e.symm
  source := e.source ∩ e ⁻¹' V
  target := V
  map_source' q hq := hq.2
  map_target' r hr := ⟨e.map_target (hVe hr), by simpa only [mem_preimage, e.right_inv (hVe hr)]⟩
  left_inv' q hq := e.left_inv hq.1
  right_inv' r hr := e.right_inv (hVe hr)
  open_source := e.continuousOn.isOpen_inter_preimage e.open_source hV
  open_target := hV
  continuousOn_toFun := e.continuousOn.mono inter_subset_left
  continuousOn_invFun := e.continuousOn_symm.mono hVe

/-- A common chart and neighbourhood work for every smooth set of axis data.
The resulting operators are genuine symmetries in the original dependent
variables, and their conjugates have the prescribed diagonal axis values. -/
theorem LocallyAxisIntegrable.exists_symmetries {U : Set (ι → ℝ)}
    {M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)} (hM : ContDiffOn ℝ ∞ M U)
    (hI : LocallyAxisIntegrable M U) {p : ι → ℝ} (hp : p ∈ U) :
    ∃ e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ),
    ∃ he : ContDiffOn ℝ ∞ e e.source, ∃ hi : ContDiffOn ℝ ∞ e.symm e.target,
    ∃ hsub : e.source ⊆ U, ∃ S : System e.open_target,
      p ∈ e.source ∧
      (∀ (q : e.source) z i, fderiv ℝ e q (M q z) i =
        S.speed i ⟨e q, e.map_source q.property⟩ * fderiv ℝ e q z i) ∧
      ∃ (r : ℝ≥0), 0 < r ∧ e.target = Metric.ball (e p) r ∧
      ∀ (φ : ι → C(ℝ, ℝ)), (∀ i, ContDiff ℝ ∞ (φ i)) →
        ∃ (w : ι → Functions e.target) (B : Endomorphism e.source),
          S.IsCommutingSpeed w ∧
          IsHydrodynamicSymmetry e.open_source (Endomorphism.ofField M (hM.mono hsub)) B ∧
          (∀ X, chartPush e he hi (B X) = PSS.FrameData.diagonalMap w (chartPush e he hi X)) ∧
          ∀ i (s : ℝ) (q : e.target),
            (q : ι → ℝ) = e p + Pi.single i s → w i q = φ i s := by
  obtain ⟨e, he, hi, S, hep, heU, hd, hsol⟩ := hI p hp
  obtain ⟨r, hr, hball, hdata⟩ := hsol ⟨e p, e.map_source hep⟩
  let g := chartTargetRestrict e Metric.isOpen_ball hball
  have hg : ContDiffOn ℝ ∞ g g.source := he.mono inter_subset_left
  have hgi : ContDiffOn ℝ ∞ g.symm g.target := hi.mono hball
  have hgU : g.source ⊆ U := inter_subset_left.trans heU
  let T : System g.open_target := restrictSystem e.open_target Metric.isOpen_ball hball S
  have hgp : p ∈ g.source := ⟨hep, Metric.mem_ball_self (by exact hr)⟩
  have hdiag : ∀ (q : g.source) z i, fderiv ℝ g q (M q z) i =
      T.speed i ⟨g q, g.map_source q.property⟩ * fderiv ℝ g q z i := by
    intro q z i
    have hh := hd ⟨q, q.property.1⟩ z i
    change _ = restrict hball (S.speed i) ⟨e q, q.property.2⟩ * _
    erw [Smooth.restrict_apply]
    exact hh
  refine ⟨g, hg, hgi, hgU, T, hgp, hdiag, r, hr, rfl, ?_⟩
  intro φ hφ
  obtain ⟨w, hw, haxis⟩ := hdata φ hφ
  let B := chartEndomorphism g.symm hgi hg (PSS.FrameData.diagonalMap w)
  have hM' := chartPush_ofField_diagonal g hg hgi M (hM.mono hgU) T hdiag
  refine ⟨w, B, hw, symmetry_of_commutingSpeed g hg hgi _ T hM' w hw, ?_, haxis⟩
  intro X
  change chartPush g hg hgi
    (chartPush g.symm hgi hg (PSS.FrameData.diagonalMap w (chartPush g hg hgi X))) = _
  exact chartPush_inverse g.symm hgi hg _

end SemiHamiltonian.Geometry
