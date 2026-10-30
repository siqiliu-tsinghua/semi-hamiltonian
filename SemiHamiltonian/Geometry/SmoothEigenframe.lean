module

public import SemiHamiltonian.Geometry.SmoothEigenpair
public import SemiHamiltonian.Geometry.FrameFromMatrix

/-! A local smooth eigenframe from a simple real spectrum at a single point. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Geometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def columns (X : ι → (ι → ℝ)) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (X i)).comp (ContinuousLinearMap.proj i)

theorem columns_apply (X : ι → (ι → ℝ)) (v : ι → ℝ) : columns X v = ∑ i, v i • X i := by
  simp [columns]

@[simp] theorem columns_single (X : ι → (ι → ℝ)) (i : ι) : columns X (Pi.single i 1) = X i := by
  simp [columns_apply, Pi.single_apply]

theorem columns_smooth {V : Set (ι → ℝ)} {X : ι → (ι → ℝ) → (ι → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ ∞ (X i) V) :
    ContDiffOn ℝ ∞ (fun q => columns (fun i => X i q)) V := by
  apply contDiffOn_clm_apply.mpr
  intro v
  simp only [columns_apply]
  exact ContDiffOn.sum (fun i _ => (contDiffOn_const (c := v i)).smul (hX i))

/-- Strict hyperbolicity here is a pointwise spectral condition, with no smooth
eigenvector or coordinate assumption. -/
def StrictHyperbolicAt (A : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)) (p : ι → ℝ) : Prop :=
  ∃ b : Module.Basis ι ℝ (ι → ℝ), ∃ v : ι → ℝ,
    Function.Injective v ∧ ∀ i, A p (b i) = v i • b i

theorem exists_smooth_eigenframe {U : Set (ι → ℝ)} (hU : IsOpen U)
    {A : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)} (hA : ContDiffOn ℝ ∞ A U)
    {p : ι → ℝ} (hp : p ∈ U) (hs : StrictHyperbolicAt A p) :
    ∃ V : Set (ι → ℝ), ∃ hVU : V ⊆ U, ∃ b : Smooth.Frame V, ∃ v : ι → Smooth.Functions V,
      IsOpen V ∧ p ∈ V ∧
      (∀ i, Smooth.Endomorphism.ofField A (hA.mono hVU) (b i) = v i • b i) ∧
      ∀ i j, i ≠ j → IsUnit (v i - v j) := by
  obtain ⟨b₀, v₀, hg₀, he₀⟩ := hs
  choose W X speed hW hpW hWU hX hv hXp hvp he using
    fun i => exists_smooth_eigenpair hU hA hp b₀ v₀ he₀ hg₀ i
  let W₀ := U ∩ ⋂ i, W i
  have hW₀ : IsOpen W₀ := hU.inter (isOpen_iInter_of_finite hW)
  have hp₀ : p ∈ W₀ := ⟨hp, mem_iInter.mpr hpW⟩
  have hsub (i : ι) : W₀ ⊆ W i := fun _ hx => mem_iInter.mp hx.2 i
  let S := fun q => columns (fun i => X i q)
  have hS : ContDiffOn ℝ ∞ S W₀ := columns_smooth (fun i => (hX i).mono (hsub i))
  have hSp : S p = (b₀.equivFun.toContinuousLinearEquiv.symm : (ι → ℝ) →L[ℝ] (ι → ℝ)) := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [S, columns_apply, hXp]
    exact (b₀.equivFun_symm_apply z).symm
  let B := {q | q ∈ W₀ ∧ (S q).IsInvertible}
  have hB : IsOpen B := hS.continuousOn.isOpen_inter_preimage hW₀
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hpB : p ∈ B := by
    refine ⟨hp₀, ?_⟩
    rw [hSp]
    exact ContinuousLinearMap.isInvertible_equiv
  let G (i j : ι) := {q | q ∈ W₀ ∧ (i = j ∨ speed i q ≠ speed j q)}
  have hG (i j : ι) : IsOpen (G i j) := by
    by_cases hij : i = j
    · simpa [G, hij] using hW₀
    · have ho := (((hv i).mono (hsub i)).sub ((hv j).mono (hsub j))).continuousOn.isOpen_inter_preimage
        hW₀ (isOpen_ne (x := (0 : ℝ)))
      convert ho using 1
      ext q
      simp [G, hij, sub_ne_zero]
  let V := B ∩ ⋂ i, ⋂ j, G i j
  have hV : IsOpen V := hB.inter (isOpen_iInter_of_finite
    (fun i => isOpen_iInter_of_finite (hG i)))
  have hpV : p ∈ V := by
    refine ⟨hpB, mem_iInter.mpr (fun i => mem_iInter.mpr (fun j => ?_))⟩
    refine ⟨hp₀, ?_⟩
    by_cases hij : i = j
    · exact Or.inl hij
    · exact Or.inr (by simpa only [hvp] using fun h => hij (hg₀ h))
  have hVW : V ⊆ W₀ := fun _ hx => hx.1.1
  have hVU : V ⊆ U := fun _ hx => (hVW hx).1
  have hSV := hS.mono hVW
  have hSi : ∀ q ∈ V, (S q).IsInvertible := fun _ hq => hq.1.2
  let b := Smooth.frameOfMatrix S hSV hSi
  let v : ι → Smooth.Functions V := fun i => Smooth.ofContDiffOn (speed i)
    ((hv i).mono (fun _ hx => hsub i (hVW hx)))
  have hb (i : ι) (x : V) : Smooth.field (b i) x = X i x := by
    rw [Smooth.frameOfMatrix_field]
    exact columns_single _ i
  refine ⟨V, hVU, b, v, hV, hpV, ?_, ?_⟩
  · intro i
    funext k
    apply Subtype.ext
    funext x
    have hh := Smooth.Endomorphism.field_ofField A (hA.mono hVU) (b i) x
    rw [hb, he i x (hsub i (hVW x.property))] at hh
    have hk := congrFun hh k
    change Smooth.Endomorphism.ofField A (hA.mono hVU) (b i) k x = speed i x • b i k x
    rw [← Smooth.field_apply (b i) x k, hb]
    simpa only [Smooth.field_apply, Pi.smul_apply] using hk
  · intro i j hij
    apply Smooth.isUnit_of_ne_zero
    intro x
    have hg := (mem_iInter.mp (mem_iInter.mp x.property.2 i) j).2
    exact sub_ne_zero.mpr (hg.resolve_left hij)

end SemiHamiltonian.Geometry
