module

public import SemiHamiltonian.Geometry.FrameFromMatrix
public import SemiHamiltonian.Geometry.ChartDerivative
public import SemiHamiltonian.Geometry.CoframeCoordinates

/-! The commuting frame induced by a genuine smooth local coordinate chart. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Filter Set

namespace SemiHamiltonian.Geometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem chart_fderiv_invertible (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {q : ι → ℝ} (hq : q ∈ e.source) : (fderiv ℝ e q).IsInvertible :=
  isInvertible_of_injective _ (chart_fderiv_injective e he hi hq)

theorem exists_coordinate_frame (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) :
    ∃ b : Smooth.Frame e.source,
      (∀ i, ∀ x : e.source, fderiv ℝ e x (Smooth.field (b i) x) = Pi.single i 1) ∧
      ∀ i j, Smooth.fieldBracket e.open_source (b i) (b j) = 0 := by
  let D := fderiv ℝ e
  have hD : ContDiffOn ℝ ∞ D e.source := he.fderiv_of_isOpen e.open_source (by simp)
  have hDi : ∀ q ∈ e.source, (D q).IsInvertible := fun q hq =>
    chart_fderiv_invertible e he hi hq
  let S := fun q => (D q).inverse
  have hS := Smooth.inverse_matrix_smooth hD hDi
  have hSi : ∀ q ∈ e.source, (S q).IsInvertible := fun q hq => (hDi q hq).inverse
  let b := Smooth.frameOfMatrix S hS hSi
  have hb (i : ι) (x : e.source) : D x (Smooth.field (b i) x) = Pi.single i 1 := by
    rw [Smooth.frameOfMatrix_field]
    exact (hDi x x.property).self_apply_inverse _
  refine ⟨b, hb, ?_⟩
  intro i j
  funext k
  apply Subtype.ext
  funext x
  have hd (r : ι) (v : ι → ℝ) :
      fderiv ℝ D x v (Smooth.field (b r) x) +
        D x (fderiv ℝ (Smooth.field (b r)) x v) = 0 := by
    have hdD := ((hD.contDiffAt (e.open_source.mem_nhds x.property)).differentiableAt
      (by simp)).hasFDerivAt
    have hdX := (((Smooth.field_smooth (b r)).contDiffAt
      (e.open_source.mem_nhds x.property)).differentiableAt (by simp)).hasFDerivAt
    have hh : (fun q => D q (Smooth.field (b r) q)) =ᶠ[𝓝 (x : ι → ℝ)] fun _ => Pi.single r 1 := by
      filter_upwards [e.open_source.mem_nhds x.property] with q hq
      exact hb r ⟨q, hq⟩
    have hzero := (hdD.clm_apply hdX).unique
      ((hasFDerivAt_const (Pi.single r 1) (x : ι → ℝ)).congr_of_eventuallyEq hh)
    have hv := congrArg (fun L : (ι → ℝ) →L[ℝ] (ι → ℝ) => L v) hzero
    simpa [add_comm] using hv
  have hij := hd j (Smooth.field (b i) x)
  have hji := hd i (Smooth.field (b j) x)
  have hs := (he.contDiffAt (e.open_source.mem_nhds x.property)).isSymmSndFDerivAt (by simp)
    (Smooth.field (b i) x) (Smooth.field (b j) x)
  change fderiv ℝ D x (Smooth.field (b i) x) (Smooth.field (b j) x) =
    fderiv ℝ D x (Smooth.field (b j) x) (Smooth.field (b i) x) at hs
  have hbr : D x (_root_.VectorField.lieBracket ℝ (Smooth.field (b i))
      (Smooth.field (b j)) x) = 0 := by
    simp only [_root_.VectorField.lieBracket, map_sub]
    rw [hs] at hij
    exact sub_eq_zero.mpr ((add_left_cancel (hij.trans hji.symm)))
  have hz : _root_.VectorField.lieBracket ℝ (Smooth.field (b i)) (Smooth.field (b j)) x = 0 := by
    apply chart_fderiv_injective e he hi x.property
    simpa only [map_zero] using hbr
  rw [← Smooth.fieldBracket_eval e.open_source (b i) (b j) x] at hz
  change Smooth.fieldBracket e.open_source (b i) (b j) k x = 0
  simpa only [Smooth.field_apply, Pi.zero_apply] using congrFun hz k

end SemiHamiltonian.Geometry
