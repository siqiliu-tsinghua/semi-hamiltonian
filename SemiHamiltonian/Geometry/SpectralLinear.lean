module

public import SemiHamiltonian.Geometry.CoframeCoordinates
public import Mathlib.LinearAlgebra.Basis.Defs

/-! The nonsingular linearization of a normalized simple eigenpair. -/

@[expose] public section

open scoped BigOperators Classical

namespace SemiHamiltonian.Geometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem eigenbasis_coordinates (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E)
    (v : ι → ℝ) (he : ∀ i, A (b i) = v i • b i) (z : E) (j : ι) :
    b.equivFun (A z) j = v j * b.equivFun z j := by
  nth_rw 1 [← b.sum_equivFun z]
  simp only [map_sum, map_smul, he, smul_smul]
  simp [Finsupp.single_apply, mul_comm]

noncomputable def eigenpairLinear (A : E →L[ℝ] E) (v : ℝ) (z : E) (ℓ : E →L[ℝ] ℝ) :
    E × ℝ →L[ℝ] E × ℝ :=
  ((A.comp (ContinuousLinearMap.fst ℝ E ℝ) - v • ContinuousLinearMap.fst ℝ E ℝ) -
    (ContinuousLinearMap.toSpanSingleton ℝ z).comp (ContinuousLinearMap.snd ℝ E ℝ)).prod
    (ℓ.comp (ContinuousLinearMap.fst ℝ E ℝ))

@[simp] theorem eigenpairLinear_apply (A : E →L[ℝ] E) (v : ℝ) (z : E)
    (ℓ : E →L[ℝ] ℝ) (h : E × ℝ) :
    eigenpairLinear A v z ℓ h = (A h.1 - v • h.1 - h.2 • z, ℓ h.1) := rfl

theorem eigenpairLinear_invertible (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E)
    (v : ι → ℝ) (he : ∀ i, A (b i) = v i • b i)
    (hg : Function.Injective v) (i : ι) :
    (eigenpairLinear A (v i) (b i)
      ((ContinuousLinearMap.proj i).comp
        (b.equivFun.toContinuousLinearEquiv : E →L[ℝ] (ι → ℝ)))).IsInvertible := by
  apply isInvertible_of_injective
  apply (eigenpairLinear A (v i) (b i) _).ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro ⟨z, s⟩ hz
  have hfst : A z - v i • z - s • b i = 0 := congrArg Prod.fst hz
  have hsnd : b.equivFun z i = 0 := congrArg Prod.snd hz
  have hcoords (j : ι) : (v j - v i) * b.equivFun z j - s * (if i = j then 1 else 0) = 0 := by
    have hh := congrArg (fun x : E => b.equivFun x j) hfst
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      eigenbasis_coordinates b A v he, b.equivFun_self, map_zero, Pi.zero_apply] at hh
    simpa only [sub_mul] using hh
  have hs : s = 0 := by simpa using hcoords i
  have hz0 : z = 0 := by
    apply b.equivFun.injective
    rw [map_zero]
    ext j
    by_cases hji : j = i
    · subst j; exact hsnd
    · have hgap : v j - v i ≠ 0 := sub_ne_zero.mpr (fun h => hji (hg h))
      have hh := hcoords j
      rw [hs, zero_mul, sub_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left hgap
  exact Prod.ext hz0 hs

end SemiHamiltonian.Geometry
