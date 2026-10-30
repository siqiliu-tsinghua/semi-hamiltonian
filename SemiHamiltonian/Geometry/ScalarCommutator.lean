module

public import SemiHamiltonian.Geometry.FrameEvaluation
public import SemiHamiltonian.PSS.ConservationNecessity

/-! Scalar differentiation in an actual smooth frame, including the second
jet at a critical point. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}

theorem fieldDerivation_eventually (hU : IsOpen U) (X : Fields U)
    (f : Functions U) (p : U) :
    extend U (fieldDerivation hU X f) =ᶠ[𝓝 (p : ι → ℝ)]
      fun x => fderiv ℝ (extend U f) x (field X x) := by
  filter_upwards [hU.mem_nhds p.property] with x hx
  rw [extend_apply U _ (⟨x, hx⟩ : U), fieldDerivation_eval]

theorem fieldDerivation_commutator (hU : IsOpen U) (X Y : Fields U)
    (f : Functions U) :
    fieldDerivation hU X (fieldDerivation hU Y f) -
      fieldDerivation hU Y (fieldDerivation hU X f) =
        fieldDerivation hU (fieldBracket hU X Y) f := by
  apply Subtype.ext
  funext p
  change fieldDerivation hU X (fieldDerivation hU Y f) p -
    fieldDerivation hU Y (fieldDerivation hU X f) p = _
  rw [fieldDerivation_eval, fieldDerivation_eval, fieldDerivation_eval,
    fieldBracket_eval, (fieldDerivation_eventually hU Y f p).fderiv_eq,
    (fieldDerivation_eventually hU X f p).fderiv_eq]
  exact (_root_.VectorField.fderiv_apply_lieBracket
    ((smooth U f).contDiffAt (hU.mem_nhds p.property)) (by simp)
    (((field_smooth Y).contDiffAt (hU.mem_nhds p.property)).differentiableAt (by simp))
    (((field_smooth X).contDiffAt (hU.mem_nhds p.property)).differentiableAt (by simp))).symm

theorem Frame.hasScalarCommutator (hU : IsOpen U) (b : Frame U) :
    (b.data hU).HasScalarCommutator := by
  intro i j f
  change fieldDerivation hU (b i) (fieldDerivation hU (b j) f) -
    fieldDerivation hU (b j) (fieldDerivation hU (b i) f) = _
  rw [fieldDerivation_commutator]
  apply Subtype.ext
  funext p
  rw [fieldDerivation_eval, b.field_sum_equivFun, map_sum]
  simp only [map_smul, smul_eq_mul]
  change _ = eval p (∑ a, (b.data hU).structureCoeff a i j * (b.data hU).deriv a f)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [map_mul]
  change _ = b.equivFun (fieldBracket hU (b i) (b j)) a p * fieldDerivation hU (b a) f p
  rw [fieldDerivation_eval]

/-- At a critical point, derivatives of the vector fields do not contribute
to the second scalar jet. -/
theorem fieldDerivation_second_at_critical (hU : IsOpen U)
    (X Y : Fields U) (f : Functions U) (p : U)
    (hf : fderiv ℝ (extend U f) p = 0) :
    fieldDerivation hU X (fieldDerivation hU Y f) p =
      fderiv ℝ (fderiv ℝ (extend U f)) p (field X p) (field Y p) := by
  rw [fieldDerivation_eval, (fieldDerivation_eventually hU Y f p).fderiv_eq]
  have hd := (((smooth U f).fderiv_of_isOpen hU (m := ∞) (by simp)).contDiffAt
    (hU.mem_nhds p.property)).differentiableAt (by simp)
  have hY := ((field_smooth Y).contDiffAt (hU.mem_nhds p.property)).differentiableAt (by simp)
  rw [(hd.hasFDerivAt.clm_apply hY.hasFDerivAt).fderiv]
  simp [hf]

end SemiHamiltonian.Smooth
