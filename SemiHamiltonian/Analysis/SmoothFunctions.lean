module

public import SemiHamiltonian.Richness
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The differential algebra of actual smooth real functions on an open set. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Filter Set

namespace SemiHamiltonian.Smooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Zero extension is only used to write ambient derivatives. All equalities in
the algebra concern values on `U`. -/
noncomputable def extend (U : Set E) (f : U → ℝ) (x : E) : ℝ :=
  if h : x ∈ U then f ⟨x, h⟩ else 0

@[simp] theorem extend_apply (U : Set E) (f : U → ℝ) (x : U) : extend U f x = f x := by
  simp [extend, x.property]

noncomputable def algebra (U : Set E) : Subalgebra ℝ (U → ℝ) where
  carrier := {f | ContDiffOn ℝ ∞ (extend U f) U}
  mul_mem' := by
    intro f g hf hg
    apply (hf.mul hg).congr
    intro x hx
    simp [extend, hx]
  add_mem' := by
    intro f g hf hg
    apply (hf.add hg).congr
    intro x hx
    simp [extend, hx]
  algebraMap_mem' := by
    intro c
    apply (show ContDiffOn ℝ ∞ (fun _ : E => c) U from contDiffOn_const).congr
    intro x hx
    simp [extend, hx, Algebra.algebraMap_eq_smul_one]

abbrev Functions (U : Set E) := ↥(algebra U)

instance {U : Set E} : CoeFun (Functions U) (fun _ => U → ℝ) := ⟨fun f => f.val⟩

theorem smooth (U : Set E) (f : Functions U) : ContDiffOn ℝ ∞ (extend U f) U := f.property

noncomputable def ofContDiffOn {U : Set E} (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U) : Functions U :=
  ⟨fun x => f x, hf.congr (fun x hx => by simp [extend, hx])⟩

@[simp] theorem ofContDiffOn_apply {U : Set E} (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U) (x : U) :
    ofContDiffOn f hf x = f x := rfl

theorem extend_ofContDiffOn_eventuallyEq {U : Set E} (hU : IsOpen U)
    (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U) :
    extend U (ofContDiffOn f hf) =ᶠ[𝓝 x] f := by
  filter_upwards [hU.mem_nhds hx] with y hy
  simp [extend, hy]

noncomputable def directional {U : Set E} (hU : IsOpen U) (v : E) (f : Functions U) : Functions U :=
  ofContDiffOn (fun x => fderiv ℝ (extend U f) x v)
    (((smooth U f).fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const)

@[simp] theorem directional_apply {U : Set E} (hU : IsOpen U) (v : E) (f : Functions U) (x : U) :
    directional hU v f x = fderiv ℝ (extend U f) x v := rfl

theorem directional_ofContDiffOn {U : Set E} (hU : IsOpen U) (v : E)
    (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U) (x : U) :
    directional hU v (ofContDiffOn f hf) x = fderiv ℝ f x v := by
  rw [directional_apply, (extend_ofContDiffOn_eventuallyEq hU f hf x.property).fderiv_eq]

theorem hasFDerivAt_extend {U : Set E} (hU : IsOpen U) (f : Functions U) (x : U) :
    HasFDerivAt (extend U f) (fderiv ℝ (extend U f) x) x :=
  ((smooth U f).contDiffAt (hU.mem_nhds x.property)).differentiableAt (by simp) |>.hasFDerivAt

noncomputable def derivation {U : Set E} (hU : IsOpen U) (v : E) :
    Derivation ℝ (Functions U) (Functions U) where
  toFun := directional hU v
  map_add' := by
    intro f g
    apply Subtype.ext
    funext x
    have he : extend U (f + g) =ᶠ[𝓝 (x : E)] (fun y => extend U f y + extend U g y) := by
      filter_upwards [hU.mem_nhds x.property] with y hy
      simp [extend, hy]
    change fderiv ℝ (extend U (f + g)) x v = _
    have hd := (hasFDerivAt_extend hU f x).add (hasFDerivAt_extend hU g x)
    simp only [Pi.add_def] at hd
    rw [he.fderiv_eq, hd.fderiv]
    rfl
  map_smul' := by
    intro c f
    apply Subtype.ext
    funext x
    have he : extend U (c • f) =ᶠ[𝓝 (x : E)] (fun y => c • extend U f y) := by
      filter_upwards [hU.mem_nhds x.property] with y hy
      simp [extend, hy]
    change fderiv ℝ (extend U (c • f)) x v = _
    have hd := (hasFDerivAt_extend hU f x).const_smul c
    simp only [Pi.smul_def] at hd
    rw [he.fderiv_eq, hd.fderiv]
    rfl
  leibniz' := by
    intro f g
    apply Subtype.ext
    funext x
    have he : extend U (f * g) =ᶠ[𝓝 (x : E)] (fun y => extend U f y * extend U g y) := by
      filter_upwards [hU.mem_nhds x.property] with y hy
      simp [extend, hy]
    change fderiv ℝ (extend U (f * g)) x v = _
    have hd := (hasFDerivAt_extend hU f x).mul (hasFDerivAt_extend hU g x)
    simp only [Pi.mul_def] at hd
    rw [he.fderiv_eq, hd.fderiv]
    simp [extend_apply, directional, ofContDiffOn, smul_eq_mul]
  map_one_eq_zero' := by
    apply Subtype.ext
    funext x
    have he : extend U (1 : Functions U) =ᶠ[𝓝 (x : E)] (fun _ => (1 : ℝ)) := by
      filter_upwards [hU.mem_nhds x.property] with y hy
      simp [extend, hy]
    change fderiv ℝ (extend U (1 : Functions U)) x v = 0
    rw [he.fderiv_eq]
    simp

@[simp] theorem derivation_apply {U : Set E} (hU : IsOpen U) (v : E) (f : Functions U) (x : U) :
    derivation hU v f x = fderiv ℝ (extend U f) x v := rfl

theorem derivation_commute {U : Set E} (hU : IsOpen U) (v w : E) (f : Functions U) :
    derivation hU v (derivation hU w f) = derivation hU w (derivation hU v f) := by
  apply Subtype.ext
  funext x
  have hf := (smooth U f).contDiffAt (hU.mem_nhds x.property)
  have hdf : DifferentiableAt ℝ (fderiv ℝ (extend U f)) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hformula (a b : E) : directional hU a (directional hU b f) x =
      fderiv ℝ (fderiv ℝ (extend U f)) x a b := by
    rw [show directional hU b f = ofContDiffOn _ _ from rfl, directional_ofContDiffOn]
    rw [fderiv_clm_apply hdf (differentiableAt_const b)]
    simp
  change directional hU v (directional hU w f) x = directional hU w (directional hU v f) x
  rw [hformula, hformula]
  exact hf.isSymmSndFDerivAt (by simp) v w

noncomputable def eval {U : Set E} (x : U) : Functions U →+* ℝ where
  toFun f := f x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def evaluations (U : Set E) : SeparatingEvaluations (Functions U) ℝ U where
  eval := eval
  separates := by intro f g h; apply Subtype.ext; exact funext h

/-- A nowhere-zero smooth function is a unit in the smooth function algebra. -/
theorem isUnit_of_ne_zero {U : Set E} (f : Functions U) (hf : ∀ x : U, f x ≠ 0) : IsUnit f := by
  have hs : ContDiffOn ℝ ∞ (fun x => (extend U f x)⁻¹) U :=
    (smooth U f).inv (fun x hx => by simpa [extend, hx] using hf ⟨x, hx⟩)
  refine ⟨⟨f, ofContDiffOn _ hs, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    funext x
    change f x * (extend U f x)⁻¹ = 1
    rw [extend_apply, mul_inv_cancel₀ (hf x)]
  · apply Subtype.ext
    funext x
    change (extend U f x)⁻¹ * f x = 1
    rw [extend_apply, inv_mul_cancel₀ (hf x)]

noncomputable def restrict {U V : Set E} (hVU : V ⊆ U) : Functions U →ₐ[ℝ] Functions V where
  toFun f := ofContDiffOn (extend U f) ((smooth U f).mono hVU)
  map_one' := by apply Subtype.ext; funext x; simp [ofContDiffOn, extend, hVU x.property]
  map_mul' := by intro f g; apply Subtype.ext; funext x; simp [ofContDiffOn, extend, hVU x.property]
  map_zero' := by apply Subtype.ext; funext x; simp [ofContDiffOn, extend, hVU x.property]
  map_add' := by intro f g; apply Subtype.ext; funext x; simp [ofContDiffOn, extend, hVU x.property]
  commutes' := by intro c; apply Subtype.ext; funext x; simp [ofContDiffOn, extend, hVU x.property]

@[simp] theorem restrict_apply {U V : Set E} (hVU : V ⊆ U) (f : Functions U) (x : V) :
    restrict hVU f x = f ⟨x, hVU x.property⟩ := by simp [restrict, ofContDiffOn, extend, hVU x.property]

theorem restrict_derivation {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) (v : E) (f : Functions U) :
    restrict hVU (derivation hU v f) = derivation hV v (restrict hVU f) := by
  apply Subtype.ext
  funext x
  rw [restrict_apply, derivation_apply]
  exact (directional_ofContDiffOn hV v (extend U f) ((smooth U f).mono hVU) x).symm

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def coordinateDerivations {U : Set (ι → ℝ)} (hU : IsOpen U) :
    CoordinateDerivations ℝ (Functions U) ι where
  deriv i := derivation hU (Pi.single i 1)
  commute i j f := derivation_commute hU (Pi.single i 1) (Pi.single j 1) f

end SemiHamiltonian.Smooth
