module

public import SemiHamiltonian.Geometry.CoordinateFrame
public import SemiHamiltonian.Geometry.PSSTensor

/-! Actual pushforward of smooth vector fields by a C∞ coordinate chart.
The Lie-bracket preservation is proved from mathlib's second-derivative theorem. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Geometry

open Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
  (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)

include he hi

theorem chart_push_smooth (X : Fields e.source) :
    ContDiffOn ℝ ∞ (fun r => fderiv ℝ e (e.symm r) (field X (e.symm r))) e.target := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ e) e.source :=
    he.fderiv_of_isOpen e.open_source (by simp)
  exact (hd.clm_apply (field_smooth X)).comp hi e.symm.mapsTo

noncomputable def chartPush (X : Fields e.source) : Fields e.target := fun i =>
  ofContDiffOn (fun r => fderiv ℝ e (e.symm r) (field X (e.symm r)) i)
    (contDiffOn_pi.mp (chart_push_smooth e he hi X) i)

theorem chartPush_eval (X : Fields e.source) (r : e.target) :
    field (chartPush e he hi X) r = fderiv ℝ e (e.symm r) (field X (e.symm r)) := by
  funext i
  rw [field_apply]
  rfl

theorem chartPush_add (X Y : Fields e.source) :
    chartPush e he hi (X + Y) = chartPush e he hi X + chartPush e he hi Y := by
  funext i
  apply Subtype.ext
  funext r
  change fderiv ℝ e (e.symm r) (field (X + Y) (e.symm r)) i = _
  have hxy : field (X + Y) (e.symm r) = field X (e.symm r) + field Y (e.symm r) := by
    funext j
    simp only [field_apply (x := ⟨e.symm r, e.map_target r.property⟩),
      Pi.add_apply]
    rfl
  rw [hxy, map_add]
  rfl

noncomputable def chartPushAdd : Fields e.source →+ Fields e.target :=
  AddMonoidHom.mk' (chartPush e he hi) (chartPush_add e he hi)

theorem chartPush_inverse (X : Fields e.source) :
    chartPush e.symm hi he (chartPush e he hi X) = X := by
  funext i
  apply Subtype.ext
  funext x
  have h := chart_fderiv_left_inverse e he hi x.property
  have hp := chartPush_eval e.symm hi he (chartPush e he hi X) x
  simp only [OpenPartialHomeomorph.symm_symm] at hp
  erw [chartPush_eval e he hi X (r := ⟨e x, e.map_source x.property⟩),
    e.left_inv x.property] at hp
  have hh := congrArg (fun L : (ι → ℝ) →L[ℝ] (ι → ℝ) => L (field X x)) h
  change fderiv ℝ e.symm (e x) (fderiv ℝ e x (field X x)) = field X x at hh
  rw [hh] at hp
  simpa only [field_apply] using congrFun hp i

noncomputable def chartPushEquiv : Fields e.source ≃+ Fields e.target where
  toFun := chartPush e he hi
  invFun := chartPush e.symm hi he
  left_inv := chartPush_inverse e he hi
  right_inv := chartPush_inverse e.symm hi he
  map_add' := chartPush_add e he hi

theorem chart_inverse_fderiv {r : ι → ℝ} (hr : r ∈ e.target) :
    (fderiv ℝ e.symm r).inverse = fderiv ℝ e (e.symm r) := by
  have h := chart_fderiv_left_inverse e.symm hi he hr
  have hInv := chart_fderiv_invertible e.symm hi he hr
  have hh := congrArg
    (fun L : (ι → ℝ) →L[ℝ] (ι → ℝ) => L.comp (fderiv ℝ e.symm r).inverse) h
  simpa only [ContinuousLinearMap.comp_assoc, hInv.self_comp_inverse,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp,
    OpenPartialHomeomorph.symm_symm] using hh.symm

theorem chartPush_eventually (X : Fields e.source) {r : ι → ℝ} (hr : r ∈ e.target) :
    field (chartPush e he hi X) =ᶠ[𝓝 r] _root_.VectorField.pullback ℝ e.symm (field X) := by
  filter_upwards [e.open_target.mem_nhds hr] with y hy
  rw [chartPush_eval e he hi X (⟨y, hy⟩ : e.target)]
  simp only [_root_.VectorField.pullback, chart_inverse_fderiv e he hi hy]

/-- The actual coordinate pushforward preserves the actual Lie bracket. -/
theorem chartPush_bracket (X Y : Fields e.source) :
    chartPush e he hi (fieldBracket e.open_source X Y) =
      fieldBracket e.open_target (chartPush e he hi X) (chartPush e he hi Y) := by
  funext i
  apply Subtype.ext
  funext r
  have hr := e.map_target r.property
  have hX := (field_smooth X).contDiffAt (e.open_source.mem_nhds hr)
  have hY := (field_smooth Y).contDiffAt (e.open_source.mem_nhds hr)
  have hbr := _root_.VectorField.pullback_lieBracket (by simp : minSmoothness ℝ 2 ≤ ∞)
    (hi.contDiffAt (e.open_target.mem_nhds r.property))
    (hX.differentiableAt (by simp)) (hY.differentiableAt (by simp))
  have hcongr := (chartPush_eventually e he hi X r.property).lieBracket_vectorField_eq (𝕜 := ℝ)
    (chartPush_eventually e he hi Y r.property)
  have hh : field (chartPush e he hi (fieldBracket e.open_source X Y)) r =
      field (fieldBracket e.open_target (chartPush e he hi X) (chartPush e he hi Y)) r := by
    rw [chartPush_eval, fieldBracket_eval e.open_source X Y (⟨e.symm r, hr⟩ : e.source),
      fieldBracket_eval, hcongr, ← hbr]
    simp only [_root_.VectorField.pullback, chart_inverse_fderiv e he hi r.property]
  simpa only [field_apply] using congrFun hh i

/-- Naturality of the intrinsic PSS tensor under an actual smooth chart. -/
theorem chartPush_pss (A : Endomorphism e.source) (B : Endomorphism e.target)
    (hA : ∀ X, chartPush e he hi (A X) = B (chartPush e he hi X))
    (X Y Z : Fields e.source) :
    chartPush e he hi (pssTensor e.open_source A X Y Z) =
      pssTensor e.open_target B (chartPush e he hi X) (chartPush e he hi Y)
        (chartPush e he hi Z) :=
  PSS.TensorRecipe.map_P (chartPushAdd e he hi) (chartPush_bracket e he hi) hA X Y Z

theorem pssVanish_chart_iff (A : Endomorphism e.source) (B : Endomorphism e.target)
    (hA : ∀ X, chartPush e he hi (A X) = B (chartPush e he hi X)) :
    PSSVanish e.open_source A ↔ PSSVanish e.open_target B := by
  constructor
  · intro h X Y Z
    obtain ⟨X, rfl⟩ := (chartPushEquiv e he hi).surjective X
    obtain ⟨Y, rfl⟩ := (chartPushEquiv e he hi).surjective Y
    obtain ⟨Z, rfl⟩ := (chartPushEquiv e he hi).surjective Z
    change pssTensor e.open_target B (chartPush e he hi X) (chartPush e he hi Y)
      (chartPush e he hi Z) = 0
    rw [← chartPush_pss e he hi A B hA, h X Y Z]
    exact (chartPushAdd e he hi).map_zero
  · intro h X Y Z
    apply (chartPushEquiv e he hi).injective
    change chartPush e he hi (pssTensor e.open_source A X Y Z) = chartPush e he hi 0
    rw [chartPush_pss e he hi A B hA, h]
    exact (chartPushAdd e he hi).map_zero.symm

noncomputable def chartScalar (f : Functions e.source) : Functions e.target :=
  ofContDiffOn (fun r => extend e.source f (e.symm r))
    ((smooth e.source f).comp hi e.symm.mapsTo)

theorem chartScalar_eval (f : Functions e.source) (r : e.target) :
    chartScalar e hi f r = f ⟨e.symm r, e.map_target r.property⟩ :=
  extend_apply e.source f ⟨e.symm r, e.map_target r.property⟩

theorem chartScalar_inverse (f : Functions e.source) :
    chartScalar e.symm he (chartScalar e hi f) = f := by
  apply Subtype.ext
  funext x
  erw [chartScalar_eval e.symm hi he, chartScalar_eval e he hi]
  simp only [OpenPartialHomeomorph.symm_symm, e.left_inv x.property]
  rfl

theorem chartPush_smul (f : Functions e.source) (X : Fields e.source) :
    chartPush e he hi (f • X) = chartScalar e hi f • chartPush e he hi X := by
  funext i
  apply Subtype.ext
  funext r
  have hfx : field (f • X) (e.symm r) =
      f ⟨e.symm r, e.map_target r.property⟩ • field X (e.symm r) := by
    funext j
    simp only [Pi.smul_apply, field_apply (x := ⟨e.symm r, e.map_target r.property⟩)]
    rfl
  change fderiv ℝ e (e.symm r) (field (f • X) (e.symm r)) i = _
  rw [hfx, map_smul]
  change _ = chartScalar e hi f r * _
  rw [chartScalar_eval e he hi]
  rfl

/-- Conjugation by the actual differential of the coordinate change, preserving
linearity over smooth functions (whose scalar rings also change). -/
noncomputable def chartEndomorphism (A : Endomorphism e.source) : Endomorphism e.target where
  toFun X := chartPush e he hi (A (chartPush e.symm hi he X))
  map_add' X Y := by erw [chartPush_add e.symm hi he, map_add, chartPush_add]
  map_smul' f X := by
    have hs : chartPush e.symm hi he (f • X) =
        (chartScalar e.symm he f : Functions e.source) • chartPush e.symm hi he X :=
      chartPush_smul e.symm hi he f X
    have hf : chartScalar e hi (chartScalar e.symm he f) = f :=
      chartScalar_inverse e.symm hi he f
    erw [hs]
    erw [A.map_smul (chartScalar e.symm he f : Functions e.source),
      chartPush_smul e he hi, hf]
    rfl

theorem chartEndomorphism_intertwines (A : Endomorphism e.source) (X : Fields e.source) :
    chartPush e he hi (A X) = chartEndomorphism e he hi A (chartPush e he hi X) := by
  change _ = chartPush e he hi (A (chartPush e.symm hi he (chartPush e he hi X)))
  rw [chartPush_inverse]

theorem pssVanish_conjugate_iff (A : Endomorphism e.source) :
    PSSVanish e.open_source A ↔ PSSVanish e.open_target (chartEndomorphism e he hi A) :=
  pssVanish_chart_iff e he hi A _ (chartEndomorphism_intertwines e he hi A)

end SemiHamiltonian.Geometry
