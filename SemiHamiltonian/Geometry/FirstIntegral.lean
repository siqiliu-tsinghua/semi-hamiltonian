module

public import SemiHamiltonian.Geometry.OneFormGraph
public import SemiHamiltonian.Geometry.HyperplaneSplit

/-! Smooth first integrals of regular codimension-one Frobenius distributions. -/

@[expose] public section

open scoped Topology ContDiff
open Filter Set

set_option backward.isDefEq.respectTransparency.types false

namespace SemiHamiltonian.Geometry

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Frobenius for a nonvanishing smooth one-form, on a fixed open neighbourhood.
The conclusion identifies the entire kernel of the differential of the first integral. -/
theorem frobenius_first_integral {U : Set E} (hU : IsOpen U)
    {α : E → E →L[ℝ] ℝ} (hα : ContDiffOn ℝ ∞ α U)
    (hc : FrobeniusOneForm α U) {p : E} (hp : p ∈ U) (hn : α p ≠ 0) :
    ∃ W : Set E, ∃ f : E → ℝ,
      IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ContDiffOn ℝ ∞ f W ∧
      ∀ q ∈ W, ∀ v, fderiv ℝ f q v = 0 ↔ α q v = 0 := by
  obtain ⟨t₀, ht₀⟩ : ∃ t : E, α p t ≠ 0 := by
    by_contra! hh
    apply hn
    ext v
    exact hh v
  let t := (α p t₀)⁻¹ • t₀
  have ht : α p t = 1 := by simp [t, ht₀]
  let L := hyperplaneSplit (α p) t ht
  let C : (α p).ker × ℝ → E := fun q => p + L.symm q
  let D : E → (α p).ker × ℝ := fun x => L (x - p)
  have hC : ContDiff ℝ ∞ C := contDiff_const.add L.symm.contDiff
  have hD : ContDiff ℝ ∞ D := L.contDiff.comp (contDiff_id.sub contDiff_const)
  have hCD (x : E) : C (D x) = x := by simp [C, D]
  have hDC (q : (α p).ker × ℝ) : D (C q) = q := by simp [C, D]
  have hCp : C (0, 0) = p := by simp [C]
  have hDp : D p = (0, 0) := by change L (p - p) = _; rw [sub_self, map_zero]; rfl
  let U₀ : Set E := {x | x ∈ U ∧ α x t ≠ 0}
  have hU₀ : IsOpen U₀ :=
    (hα.clm_apply contDiffOn_const).continuousOn.isOpen_inter_preimage hU isOpen_ne
  let V := C ⁻¹' U₀
  have hV : IsOpen V := hU₀.preimage hC.continuous
  have hVp : (0, 0) ∈ V := by change C (0, 0) ∈ U₀; simp [hCp, U₀, hp, ht]
  let β : (α p).ker × ℝ → ((α p).ker × ℝ) →L[ℝ] ℝ :=
    fun q => (α (C q)).comp (L.symm : ((α p).ker × ℝ) →L[ℝ] E)
  have hβ : ContDiffOn ℝ ∞ β V :=
    (hα.comp hC.contDiffOn (fun _ hq => hq.1)).clm_comp contDiffOn_const
  have hβn : ∀ q ∈ V, β q (0, 1) ≠ 0 := by
    intro q hq
    simpa [β, L] using hq.2
  have hβd (q : (α p).ker × ℝ) (hq : q ∈ V) (v w : (α p).ker × ℝ) :
      fderiv ℝ β q v w = fderiv ℝ α (C q) (L.symm v) (L.symm w) := by
    have hd := ((hα.contDiffAt (hU.mem_nhds hq.1)).differentiableAt (by simp)).hasFDerivAt
    have hCd : HasFDerivAt C (L.symm : ((α p).ker × ℝ) →L[ℝ] E) q := by
      convert (hasFDerivAt_const p q).add L.symm.hasFDerivAt using 1 <;> simp
    have hh := (hd.comp q hCd).clm_comp (hasFDerivAt_const
      (L.symm : ((α p).ker × ℝ) →L[ℝ] E) q)
    change HasFDerivAt β _ q at hh
    rw [hh.fderiv]
    simp
  have hβc : FrobeniusOneForm β V := by
    intro q hq v w hv hw
    rw [hβd q hq, hβd q hq]
    exact hc (C q) hq.1 (L.symm v) (L.symm w) hv hw
  obtain ⟨B, g, hB, hpB, hBV, hg, hgker⟩ :=
    oneFormGraph_first_integral hV hβ hβn hβc hVp
  let W := D ⁻¹' B
  have hW : IsOpen W := hB.preimage hD.continuous
  have hWU : W ⊆ U := by
    intro x hx
    have hh := (hBV hx).1
    simpa only [hCD] using hh
  refine ⟨W, g ∘ D, hW, ?_, hWU,
    hg.comp hD.contDiffOn (fun _ hx => hx), ?_⟩
  · change D p ∈ B
    simpa only [hDp] using hpB
  · intro q hq v
    have hd := ((hg.contDiffAt (hB.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
    have hDd : HasFDerivAt D (L : E →L[ℝ] ((α p).ker × ℝ)) q := by
      convert L.hasFDerivAt.comp q ((hasFDerivAt_id q).sub (hasFDerivAt_const p q)) using 1 <;>
        simp [D, Function.comp_def, Pi.sub_def]
    rw [(hd.comp q hDd).fderiv, ContinuousLinearMap.comp_apply, hgker (D q) hq]
    simp [β, hCD]

end SemiHamiltonian.Geometry
