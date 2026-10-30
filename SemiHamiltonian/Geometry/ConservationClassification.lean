module

public import SemiHamiltonian.Geometry.ConservationGerms

/-! The natural arbitrary-function parametrization and the intrinsic jet
criterion are equivalent. Parametrization means the specified trace map is
bijective, not merely that the underlying sets have the same cardinality. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {U : Set (ι → ℝ)} (hU : IsOpen U) (S : System hU) (p : U)

/-- The prescribed parametrization: density value and the own-axis traces of
its gradient, all taken as actual smooth germs. -/
noncomputable def densityGermData (g : DensityGerm hU S p) : ℝ × (ι → ScalarGerm 0) :=
  (germValue (p : ι → ℝ) g.val,
    densityGradientAxisGerms hU S p (densityGradientGerm hU S p g))

theorem densityGermData_injective : Function.Injective (densityGermData hU S p) := by
  intro f g h
  apply densityValueGradient_injective hU S p
  apply Prod.ext
  · exact congrArg (fun z : ℝ × (ι → ScalarGerm 0) => z.1) h
  · apply densityGradientAxisGerms_injective hU S p
    exact congrArg (fun z : ℝ × (ι → ScalarGerm 0) => z.2) h

theorem densityGermData_bijective (hS : S.IsSemiHamiltonian) :
    Function.Bijective (densityGermData hU S p) :=
  (densityGermEquiv hU S p hS).bijective

omit p in
theorem semiHamiltonian_of_densityGermData_surjective
    (h : ∀ p : U, Function.Surjective (densityGermData hU S p)) : S.IsSemiHamiltonian := by
  intro i j k hij hik hjk
  apply Subtype.ext
  funext p
  let a : ι → ℝ := fun l => if l = i then 1 else 0
  let φ : ι → ScalarGerm 0 := fun l =>
    ⟨((fun _ : ℝ => a l) : Germ (𝓝 (0 : ℝ)) ℝ), fun _ => a l, contDiff_const, rfl⟩
  obtain ⟨g, hg⟩ := h p (0, φ)
  obtain ⟨V, hV, hVU, hpV, f, hf, hfg⟩ := g.property
  let SV := restrictSystem hU hV hVU S
  let b := fun l => (coordinateDerivations hV).deriv l f
  have hb (l : ι) : eval (⟨p, hpV⟩ : V) (b l) = a l := by
    have he := congrArg (fun z : ℝ × (ι → ScalarGerm 0) => (z.2 l).val) hg
    change axisGerm p l (germGradient (p : ι → ℝ) g.val) = ((fun _ : ℝ => a l) : Germ (𝓝 (0 : ℝ)) ℝ) at he
    rw [← hfg, germGradient_coe, axisGerm_coe] at he
    have hh := (Germ.coe_eq.mp he).eq_of_nhds
    change fderiv ℝ (extend V f) (p : ι → ℝ) (Pi.single l 1) = a l
    simpa only [Pi.single_zero, add_zero, gradientFunction] using hh
  have hz := SV.densityObstruction_eq_zero_of_solution hf i j k hij hik hjk
  rw [SV.densityObstruction_eq] at hz
  have hh := congrArg (eval (⟨p, hpV⟩ : V)) hz
  simp only [map_sub, map_add, map_mul, map_zero] at hh
  have hb' (l : ι) : eval (⟨p, hpV⟩ : V) ((coordinateDerivations hV).deriv l f) = a l := hb l
  rw [hb' i, hb' j, hb' k] at hh
  simp only [a, ite_true, hij.symm, hik.symm, ite_false, mul_one, mul_zero, sub_zero, add_zero] at hh
  have hd (r s t : ι) :
      eval (⟨p, hpV⟩ : V) ((coordinateDerivations hV).deriv t (SV.coeff r s)) =
        (coordinateDerivations hU).deriv t (S.coeff r s) p := by
    change derivation hV (Pi.single t 1) (Smooth.restrict hVU (S.coeff r s)) ⟨p, hpV⟩ = _
    rw [← restrict_derivation hU hV, Smooth.restrict_apply]
    rfl
  rw [hd, hd] at hh
  exact sub_eq_zero.mp hh

omit p in
theorem semiHamiltonian_iff_densityGermData_bijective :
    S.IsSemiHamiltonian ↔ ∀ p : U, Function.Bijective (densityGermData hU S p) :=
  ⟨fun h p => densityGermData_bijective hU S p h,
    fun h => semiHamiltonian_of_densityGermData_surjective hU S (fun p => (h p).2)⟩

end SemiHamiltonian.Smooth

namespace SemiHamiltonian.Geometry

open Smooth PSS.FrameData

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {U : Set (ι → ℝ)} {M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)}

/-- Local Riemann charts with the natural density value/axis-trace map
bijective at every point. No semi-Hamiltonian condition is included here. -/
def LocallyConservationParametrized (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (U : Set (ι → ℝ)) : Prop :=
  ∀ p ∈ U, ∃ e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ),
    ∃ _he : ContDiffOn ℝ ∞ e e.source, ∃ _hi : ContDiffOn ℝ ∞ e.symm e.target,
      ∃ S : System e.open_target,
        p ∈ e.source ∧ e.source ⊆ U ∧
        (∀ (q : e.source) z i, fderiv ℝ e q (M q z) i =
          S.speed i ⟨e q, e.map_source q.property⟩ * fderiv ℝ e q z i) ∧
        ∀ r : e.target, Function.Bijective (densityGermData e.open_target S r)

theorem locallySemiHamiltonian_iff_locallyConservationParametrized :
    LocallySemiHamiltonian M U ↔ LocallyConservationParametrized M U := by
  constructor
  · intro h p hp
    obtain ⟨e, he, hi, S, hep, heU, hd, hS⟩ := h p hp
    exact ⟨e, he, hi, S, hep, heU, hd,
      (semiHamiltonian_iff_densityGermData_bijective e.open_target S).mp hS⟩
  · intro h p hp
    obtain ⟨e, he, hi, S, hep, heU, hd, hdata⟩ := h p hp
    exact ⟨e, he, hi, S, hep, heU, hd,
      (semiHamiltonian_iff_densityGermData_bijective e.open_target S).mpr hdata⟩

/-- PSS theorem 5: finite-jet richness is equivalent to the specified
arbitrary-single-variable-function parametrization. -/
theorem locallyRichConservationLaws_iff_locallyConservationParametrized (hU : IsOpen U)
    (hM : ContDiffOn ℝ ∞ M U) (hs : ∀ p ∈ U, StrictHyperbolicAt M p) :
    LocallyRichConservationLaws M U ↔ LocallyConservationParametrized M U :=
  (locallyRichConservationLaws_iff_locallySemiHamiltonian hU hM hs).trans
    locallySemiHamiltonian_iff_locallyConservationParametrized

variable (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
  (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
  (S : System e.open_target) (heU : e.source ⊆ U)
  (hd : ∀ (q : e.source) z i, fderiv ℝ e q (M q z) i =
    S.speed i ⟨e q, e.map_source q.property⟩ * fderiv ℝ e q z i)
  (p : e.source)

/-- Transport all original-coordinate density germs to the diagonal system.
The original definition requires an actual local flux. -/
noncomputable def originalDensityGermChartEquiv :
    MatrixDensityGerm M U p ≃ DensityGerm e.open_target S ⟨e p, e.map_source p.property⟩ :=
  (matrixDensityGermRestrictEquiv e.open_source heU p.property).trans
    ((matrixDensityGermChartEquiv e he hi p (diagonalChart_matrix_equation e S hd)).trans
      (matrixDensityGermDiagonalEquiv e.open_target S ⟨e p, e.map_source p.property⟩))

noncomputable def originalConservationData (g : MatrixDensityGerm M U p) : ℝ × (ι → ScalarGerm 0) :=
  densityGermData e.open_target S ⟨e p, e.map_source p.property⟩
    (originalDensityGermChartEquiv e he hi S heU hd p g)

/-- The first datum is the original density value, unaffected by the chart. -/
theorem originalConservationData_value (g : MatrixDensityGerm M U p) :
    (originalConservationData e he hi S heU hd p g).1 = germValue (p : ι → ℝ) g.val := by
  obtain ⟨V, hV, hVU, hpV, f, q, hq, hfg⟩ := g.property
  change germValue (e p) (g.val.compTendsto e.symm (chart_inverse_tendsto e p)) = _
  rw [← hfg, Germ.coe_compTendsto, germValue_coe, germValue_coe]
  exact congrArg (extend V f) (e.left_inv p.property)

/-- The other data are exactly the axis germs of the gradient of h ∘ e⁻¹. -/
theorem originalConservationData_axes (g : MatrixDensityGerm M U p) (i : ι) :
    ((originalConservationData e he hi S heU hd p g).2 i).val =
      axisGerm (⟨e p, e.map_source p.property⟩ : e.target) i
        (germGradient (e p) (g.val.compTendsto e.symm (chart_inverse_tendsto e p))) := rfl

theorem originalConservationData_bijective
    (hb : Function.Bijective (densityGermData e.open_target S ⟨e p, e.map_source p.property⟩)) :
    Function.Bijective (originalConservationData e he hi S heU hd p) :=
  hb.comp (originalDensityGermChartEquiv e he hi S heU hd p).bijective

theorem originalConservationData_bijective_iff :
    Function.Bijective (originalConservationData e he hi S heU hd p) ↔
      Function.Bijective (densityGermData e.open_target S ⟨e p, e.map_source p.property⟩) := by
  let E := originalDensityGermChartEquiv e he hi S heU hd p
  constructor
  · intro h
    constructor
    · intro f g hfg
      have hh : originalConservationData e he hi S heU hd p (E.symm f) =
          originalConservationData e he hi S heU hd p (E.symm g) := by
        change densityGermData _ _ _ (E (E.symm f)) = densityGermData _ _ _ (E (E.symm g))
        simpa only [E.apply_symm_apply] using hfg
      exact E.symm.injective (h.1 hh)
    · intro a
      obtain ⟨g, hg⟩ := h.2 a
      exact ⟨E g, hg⟩
  · exact originalConservationData_bijective e he hi S heU hd p

/-- An explicit equivalence, whose forward map is the prescribed data map. -/
noncomputable def originalConservationGermEquiv
    (hb : Function.Bijective (densityGermData e.open_target S ⟨e p, e.map_source p.property⟩)) :
    MatrixDensityGerm M U p ≃ (ℝ × (ι → ScalarGerm 0)) :=
  Equiv.ofBijective (originalConservationData e he hi S heU hd p)
    (originalConservationData_bijective e he hi S heU hd p hb)

omit e he hi S heU hd p in
/-- The intrinsic criterion supplies an actual chart and a bijective natural
parametrization of every original-coordinate conservation density germ. -/
theorem LocallyRichConservationLaws.exists_densityGerm_parametrization (hU : IsOpen U)
    (hM : ContDiffOn ℝ ∞ M U) (hs : ∀ p ∈ U, StrictHyperbolicAt M p)
    (h : LocallyRichConservationLaws M U) (p : U) :
    ∃ (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
      (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
      (S : System e.open_target) (heU : e.source ⊆ U)
      (hd : ∀ (q : e.source) z i, fderiv ℝ e q (M q z) i =
        S.speed i ⟨e q, e.map_source q.property⟩ * fderiv ℝ e q z i)
      (hp : (p : ι → ℝ) ∈ e.source),
      Function.Bijective (originalConservationData e he hi S heU hd ⟨p, hp⟩) := by
  obtain ⟨e, he, hi, S, hep, heU, hd, hb⟩ :=
    ((locallyRichConservationLaws_iff_locallyConservationParametrized hU hM hs).mp h) p p.property
  exact ⟨e, he, hi, S, heU, hd, hep,
    originalConservationData_bijective e he hi S heU hd ⟨p, hep⟩ (hb ⟨e p, e.map_source hep⟩)⟩

omit e he hi S heU hd p in
/-- The parametrization stated entirely for original-coordinate density germs.
The supplied coordinates specify the actual trace map; every germ admits a flux. -/
def LocallyOriginalConservationParametrized (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (U : Set (ι → ℝ)) : Prop :=
  ∀ p ∈ U, ∃ (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (S : System e.open_target) (heU : e.source ⊆ U)
    (hd : ∀ (q : e.source) z i, fderiv ℝ e q (M q z) i =
      S.speed i ⟨e q, e.map_source q.property⟩ * fderiv ℝ e q z i),
      p ∈ e.source ∧ ∀ q : e.source,
        Function.Bijective (originalConservationData e he hi S heU hd q)

omit e he hi S heU hd p in
theorem locallyConservationParametrized_iff_original :
    LocallyConservationParametrized M U ↔ LocallyOriginalConservationParametrized M U := by
  constructor
  · intro h p hp
    obtain ⟨e, he, hi, S, hep, heU, hd, hb⟩ := h p hp
    exact ⟨e, he, hi, S, heU, hd, hep, fun q =>
      originalConservationData_bijective e he hi S heU hd q (hb ⟨e q, e.map_source q.property⟩)⟩
  · intro h p hp
    obtain ⟨e, he, hi, S, heU, hd, hep, hb⟩ := h p hp
    refine ⟨e, he, hi, S, hep, heU, hd, ?_⟩
    intro r
    let q : e.source := ⟨e.symm r, e.map_target r.property⟩
    have hh := (originalConservationData_bijective_iff e he hi S heU hd q).mp (hb q)
    have hqr : (⟨e q, e.map_source q.property⟩ : e.target) = r := Subtype.ext (e.right_inv r.property)
    rwa [hqr] at hh

omit e he hi S heU hd p in
/-- The completed intrinsic PSS conservation-law equivalence, using the
natural bijective data map on all original-variable density germs. -/
theorem locallyRichConservationLaws_iff_originalParametrized (hU : IsOpen U)
    (hM : ContDiffOn ℝ ∞ M U) (hs : ∀ p ∈ U, StrictHyperbolicAt M p) :
    LocallyRichConservationLaws M U ↔ LocallyOriginalConservationParametrized M U :=
  (locallyRichConservationLaws_iff_locallyConservationParametrized hU hM hs).trans
    locallyConservationParametrized_iff_original

end SemiHamiltonian.Geometry
