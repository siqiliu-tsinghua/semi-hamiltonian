module

public import SemiHamiltonian.Geometry.MatrixField

/-! Pointwise Nijenhuis and Haantjes tensors of a general smooth matrix field. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Filter Set

namespace SemiHamiltonian.Smooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def matrixNijenhuis (A : E → E →L[ℝ] E) (q v w : E) : E :=
  fderiv ℝ A q (A q v) w - fderiv ℝ A q (A q w) v +
    A q (fderiv ℝ A q w v) - A q (fderiv ℝ A q v w)

noncomputable def matrixHaantjes (A : E → E →L[ℝ] E) (q v w : E) : E :=
  matrixNijenhuis A q (A q v) (A q w) + A q (A q (matrixNijenhuis A q v w)) -
    A q (matrixNijenhuis A q v (A q w)) - A q (matrixNijenhuis A q (A q v) w)

def MatrixHaantjesVanish (A : E → E →L[ℝ] E) (U : Set E) : Prop :=
  ∀ q ∈ U, ∀ v w, matrixHaantjes A q v w = 0

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}

@[simp] theorem field_add (X Y : Fields U) (x : U) : field (X + Y) x = field X x + field Y x := by
  ext k; simp [field_apply]

@[simp] theorem field_sub (X Y : Fields U) (x : U) : field (X - Y) x = field X x - field Y x := by
  ext k; simp [field_apply]

@[simp] theorem field_zero (x : U) : field (0 : Fields U) x = 0 := by
  ext k; simp [field_apply]

theorem nijenhuis_ofField_eval (hU : IsOpen U)
    {M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)} (hM : ContDiffOn ℝ ∞ M U)
    (X Y : Fields U) (x : U) :
    field (nijenhuis hU (Endomorphism.ofField M hM) X Y) x =
      matrixNijenhuis M x (field X x) (field Y x) := by
  let A := Endomorphism.ofField M hM
  have hder (Z : Fields U) : fderiv ℝ (field (A Z)) x =
      (M x).comp (fderiv ℝ (field Z) x) + (fderiv ℝ M x).flip (field Z x) := by
    have hdM := ((hM.contDiffAt (hU.mem_nhds x.property)).differentiableAt (by simp)).hasFDerivAt
    have hdZ := (((field_smooth Z).contDiffAt (hU.mem_nhds x.property)).differentiableAt
      (by simp)).hasFDerivAt
    have he : field (A Z) =ᶠ[𝓝 (x : ι → ℝ)] fun q => M q (field Z q) := by
      filter_upwards [hU.mem_nhds x.property] with q hq
      exact Endomorphism.field_ofField M hM Z ⟨q, hq⟩
    exact (hdM.clm_apply hdZ |>.congr_of_eventuallyEq he).fderiv
  simp only [A] at hder
  simp only [nijenhuis, field_sub, field_add, Endomorphism.field_ofField, fieldBracket_eval]
  simp only [_root_.VectorField.lieBracket, hder, Endomorphism.field_ofField, matrixNijenhuis,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply, map_add, map_sub]
  module

theorem haantjes_ofField_eval (hU : IsOpen U)
    {M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)} (hM : ContDiffOn ℝ ∞ M U)
    (X Y : Fields U) (x : U) :
    field (haantjes hU (Endomorphism.ofField M hM) X Y) x =
      matrixHaantjes M x (field X x) (field Y x) := by
  simp only [haantjes, field_sub, field_add, Endomorphism.field_ofField,
    nijenhuis_ofField_eval hU hM, matrixHaantjes]

theorem matrixHaantjesVanish_iff (hU : IsOpen U)
    {M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)} (hM : ContDiffOn ℝ ∞ M U) :
    MatrixHaantjesVanish M U ↔ HaantjesVanish hU (Endomorphism.ofField M hM) := by
  constructor
  · intro hh X Y
    funext k
    apply Subtype.ext
    funext x
    have he := hh x x.property (field X x) (field Y x)
    rw [← haantjes_ofField_eval hU hM X Y x] at he
    change haantjes hU (Endomorphism.ofField M hM) X Y k x = 0
    simpa only [field_apply, Pi.zero_apply] using congrFun he k
  · intro hh q hq v w
    have he := congrArg (fun X : Fields U => field X (⟨q, hq⟩ : U))
      (hh (constantField v) (constantField w))
    rw [haantjes_ofField_eval hU hM (constantField v) (constantField w) ⟨q, hq⟩,
      field_constantField v ⟨q, hq⟩, field_constantField w ⟨q, hq⟩, field_zero ⟨q, hq⟩] at he
    exact he

end SemiHamiltonian.Smooth
