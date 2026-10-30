module

public import SemiHamiltonian.Geometry.SpectralLinear

/-! Smooth local selection of a simple normalized real eigenpair. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Geometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_eigenpair {U : Set E} (hU : IsOpen U)
    {A : E → E →L[ℝ] E} (hA : ContDiffOn ℝ ∞ A U)
    {p : E} (hp : p ∈ U) (b : Module.Basis ι ℝ E) (v : ι → ℝ)
    (he : ∀ i, A p (b i) = v i • b i) (hg : Function.Injective v) (i : ι) :
    ∃ W : Set E, ∃ X : E → E, ∃ speed : E → ℝ,
      IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ContDiffOn ℝ ∞ X W ∧
      ContDiffOn ℝ ∞ speed W ∧ X p = b i ∧ speed p = v i ∧
      ∀ q ∈ W, A q (X q) = speed q • X q := by
  let ℓ : E →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp
    (b.equivFun.toContinuousLinearEquiv : E →L[ℝ] (ι → ℝ))
  have hℓ : ℓ (b i) = 1 := by simp [ℓ, b.equivFun_self]
  let f : E × (E × ℝ) → E × ℝ := fun q =>
    (A q.1 q.2.1 - q.2.2 • q.2.1, ℓ q.2.1 - 1)
  let V : Set (E × (E × ℝ)) := Prod.fst ⁻¹' U
  have hV : IsOpen V := hU.preimage continuous_fst
  have hf : ContDiffOn ℝ ∞ f V := by
    exact ((hA.comp contDiffOn_fst (fun _ hq => hq)).clm_apply contDiffOn_snd.fst |>.sub
      (contDiffOn_snd.snd.smul contDiffOn_snd.fst)).prodMk
      ((ℓ.contDiff.comp_contDiffOn contDiffOn_snd.fst).sub contDiffOn_const)
  have hpV : (p, (b i, v i)) ∈ V := hp
  have hfd := ((hf.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)).hasFDerivAt
  have hslice := hfd.comp (b i, v i)
    ((hasFDerivAt_const p (b i, v i)).prodMk (hasFDerivAt_id (b i, v i)))
  have hexp := (((A p).hasFDerivAt.comp (b i, v i) hasFDerivAt_fst).sub
    (hasFDerivAt_snd.smul hasFDerivAt_fst)).prodMk
    (((ℓ.hasFDerivAt.comp (b i, v i) hasFDerivAt_fst)).sub
      (hasFDerivAt_const (1 : ℝ) (b i, v i)))
  have hpart : (fderiv ℝ f (p, (b i, v i))).comp (ContinuousLinearMap.inr ℝ E (E × ℝ)) =
      eigenpairLinear (A p) (v i) (b i) ℓ := by
    have hh := hslice.unique hexp
    change (fderiv ℝ f (p, (b i, v i))).comp
      (ContinuousLinearMap.inr ℝ E (E × ℝ)) = _ at hh
    rw [hh]
    apply ContinuousLinearMap.ext
    intro z
    change (A p z.1 - (v i • z.1 + z.2 • b i), ℓ z.1 - 0) =
      (A p z.1 - v i • z.1 - z.2 • b i, ℓ z.1)
    simp only [sub_zero, sub_add_eq_sub_sub]
  have hi : ((fderiv ℝ f (p, (b i, v i))).comp
      (ContinuousLinearMap.inr ℝ E (E × ℝ))).IsInvertible := by
    rw [hpart]
    exact eigenpairLinear_invertible b (A p) v he hg i
  obtain ⟨W, B, ψ, hW, hpW, hB, hpB, hBV, hψp, hψ, hsol, huniq⟩ :=
    exists_smooth_implicit hV hf hpV hi
  refine ⟨W, fun q => (ψ q).1, fun q => (ψ q).2, hW, hpW, ?_, hψ.fst, hψ.snd,
    congrArg Prod.fst hψp, congrArg Prod.snd hψp, ?_⟩
  · intro q hq
    exact hBV (hsol q hq).1
  · intro q hq
    have hh := congrArg Prod.fst (hsol q hq).2
    change A q (ψ q).1 - (ψ q).2 • (ψ q).1 = A p (b i) - v i • b i at hh
    rw [he i, sub_self, sub_eq_zero] at hh
    exact hh

end SemiHamiltonian.Geometry
