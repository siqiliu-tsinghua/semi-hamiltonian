module

public import SemiHamiltonian.Analysis.ConservationLaws

/-! Classification of actual conservation density germs, keeping the additive
constant separate from the freely prescribed gradient axis germs. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def gradientFunction (f : (ι → ℝ) → ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

noncomputable def germValue (p : ι → ℝ) (g : Germ (𝓝 p) ℝ) : ℝ :=
  g.liftOn (fun f => f p) (fun _ _ he => he.eq_of_nhds)

noncomputable def germGradient (p : ι → ℝ) : Germ (𝓝 p) ℝ → Germ (𝓝 p) (ι → ℝ) :=
  Germ.map' gradientFunction (fun _ _ he => (he.fderiv (𝕜 := ℝ)).mono fun _ hx =>
    funext fun i => congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) hx)

omit [Fintype ι] [DecidableEq ι] in
theorem germValue_coe (p : ι → ℝ) (f : (ι → ℝ) → ℝ) : germValue p (f : Germ (𝓝 p) ℝ) = f p := rfl

omit [Fintype ι] in
theorem germGradient_coe (p : ι → ℝ) (f : (ι → ℝ) → ℝ) :
    germGradient p (f : Germ (𝓝 p) ℝ) = (gradientFunction f : Germ (𝓝 p) (ι → ℝ)) := rfl

theorem fderiv_eq_of_gradient_eq {f g : (ι → ℝ) → ℝ} {x : ι → ℝ}
    (hh : gradientFunction f x = gradientFunction g x) : fderiv ℝ f x = fderiv ℝ g x := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul]
  exact congrArg (fun z => v i • z) (congrFun hh i)

variable {U : Set (ι → ℝ)} (hU : IsOpen U) (S : System hU) (p : U)

def DensityGerm :=
  {g : Germ (𝓝 (p : ι → ℝ)) ℝ //
    ∃ V, ∃ hV : IsOpen V, ∃ hVU : V ⊆ U, (p : ι → ℝ) ∈ V ∧
      ∃ h : Functions V, (restrictSystem hU hV hVU S).IsDensity h ∧
        (extend V h : Germ (𝓝 (p : ι → ℝ)) ℝ) = g}

omit S p in
theorem gradientFunction_field (h : Functions U) (x : U) :
    gradientFunction (extend U h) x = field (fun i => (coordinateDerivations hU).deriv i h) x := by
  funext i
  rw [field_apply]
  rfl

noncomputable def densityGradientGerm (g : DensityGerm hU S p) : DensityGradientGerm hU S p :=
  ⟨germGradient (p : ι → ℝ) g.val, by
    obtain ⟨V, hV, hVU, hpV, h, hh, hhg⟩ := g.property
    let a := fun i => (coordinateDerivations hV).deriv i h
    refine ⟨field a, localDensityGradient_of_section hU S p hV hVU hpV a hh, ?_⟩
    rw [← hhg, germGradient_coe]
    apply Filter.EventuallyEq.germ_eq
    filter_upwards [hV.mem_nhds hpV] with x hx
    exact (gradientFunction_field hV h ⟨x, hx⟩).symm⟩

noncomputable def densityValueGradient (g : DensityGerm hU S p) : ℝ × DensityGradientGerm hU S p :=
  (germValue (p : ι → ℝ) g.val, densityGradientGerm hU S p g)

theorem densityValueGradient_injective : Function.Injective (densityValueGradient hU S p) := by
  intro g k he
  obtain ⟨V, hV, hVU, hpV, h, hh, hhg⟩ := g.property
  obtain ⟨T, hT, hTU, hpT, f, hf, hfk⟩ := k.property
  have hv := congrArg Prod.fst he
  have hd := congrArg (fun z : ℝ × DensityGradientGerm hU S p => z.2.val) he
  change germValue (p : ι → ℝ) g.val = germValue (p : ι → ℝ) k.val at hv
  change germGradient (p : ι → ℝ) g.val = germGradient (p : ι → ℝ) k.val at hd
  rw [← hhg, ← hfk, germValue_coe, germValue_coe] at hv
  rw [← hhg, ← hfk, germGradient_coe, germGradient_coe] at hd
  apply Subtype.ext
  rw [← hhg, ← hfk]
  apply Filter.EventuallyEq.germ_eq
  apply Geometry.potential_germ_unique (hV.inter hT) ((smooth V h).mono inter_subset_left)
    ((smooth T f).mono inter_subset_right) ⟨hpV, hpT⟩ hv
  exact (Germ.coe_eq.mp hd).mono fun x hx => fderiv_eq_of_gradient_eq hx

theorem densityValueGradient_surjective : Function.Surjective (densityValueGradient hU S p) := by
  rintro ⟨c, g⟩
  obtain ⟨W, hW, hWg⟩ := g.property
  obtain ⟨V, hV, hVU, hpV, a, ha, he⟩ := localDensityGradient_section hU S p hW
  let SV := restrictSystem hU hV hVU S
  obtain ⟨T, hT, hTV, hpT, h, hhp, hhd⟩ := exists_local_primitive hV a
    (SV.densityGradient_closed ha) ⟨p, hpV⟩ c
  have hh : (restrictSystem hU hT (hTV.trans hVU) S).IsDensity h := by
    rw [← restrictSystem_trans hU hV hT hVU hTV S]
    exact primitive_is_density hV hT hTV SV ha hhd
  let k : DensityGerm hU S p := ⟨(extend T h : Germ (𝓝 (p : ι → ℝ)) ℝ),
    T, hT, hTV.trans hVU, hpT, h, hh, rfl⟩
  refine ⟨k, Prod.ext ?_ ?_⟩
  · change extend T h p = c
    rw [extend_apply T h ⟨p, hpT⟩]
    exact hhp
  · apply Subtype.ext
    change germGradient (p : ι → ℝ) (extend T h : Germ (𝓝 (p : ι → ℝ)) ℝ) = g.val
    rw [germGradient_coe, ← hWg]
    apply Filter.EventuallyEq.germ_eq
    filter_upwards [hT.mem_nhds hpT] with x hx
    rw [gradientFunction_field hT h ⟨x, hx⟩, ← he x (hTV hx)]
    funext i
    rw [field_apply _ ⟨x, hx⟩, field_apply a ⟨x, hTV hx⟩, hhd i, Smooth.restrict_apply]

noncomputable def densityValueGradientEquiv :
    DensityGerm hU S p ≃ (ℝ × DensityGradientGerm hU S p) :=
  Equiv.ofBijective (densityValueGradient hU S p)
    ⟨densityValueGradient_injective hU S p, densityValueGradient_surjective hU S p⟩

/-- A conservation density germ is uniquely specified by its value at the base
point and n arbitrary smooth germs of its gradient components on their axes. -/
noncomputable def densityGermEquiv (hS : S.IsSemiHamiltonian) :
    DensityGerm hU S p ≃ (ℝ × (ι → ScalarGerm 0)) :=
  (densityValueGradientEquiv hU S p).trans
    (Equiv.prodCongr (Equiv.refl ℝ) (densityGradientGermEquiv hU S p hS))

/-- The flux is unique as a germ after fixing its independent additive constant. -/
theorem flux_germ_unique {h q z : Functions U}
    (hq : S.IsConservationLaw h q) (hz : S.IsConservationLaw h z) (hval : q p = z p) :
    extend U q =ᶠ[𝓝 (p : ι → ℝ)] extend U z := by
  apply Geometry.potential_germ_unique hU (smooth U q) (smooth U z) p.property
    (by simpa only [extend_apply] using hval)
  filter_upwards [hU.mem_nhds p.property] with x hx
  apply fderiv_eq_of_gradient_eq
  funext i
  change (coordinateDerivations hU).deriv i q ⟨x, hx⟩ =
    (coordinateDerivations hU).deriv i z ⟨x, hx⟩
  rw [hq i, hz i]

end SemiHamiltonian.Smooth
