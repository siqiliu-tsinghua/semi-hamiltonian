module

public import SemiHamiltonian.Geometry.FrobeniusGraph
public import SemiHamiltonian.Geometry.ChartDerivative

/-! The Frobenius condition for a nonvanishing one-form, in graph coordinates. -/

@[expose] public section

open scoped Topology ContDiff
open Filter Set

namespace SemiHamiltonian.Geometry

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The exterior derivative of the one-form vanishes on its kernel. -/
def FrobeniusOneForm (α : E → E →L[ℝ] ℝ) (U : Set E) : Prop :=
  ∀ q ∈ U, ∀ v w, α q v = 0 → α q w = 0 →
    fderiv ℝ α q v w = fderiv ℝ α q w v

noncomputable def oneFormGraph (α : E × ℝ → (E × ℝ) →L[ℝ] ℝ)
    (q : E × ℝ) : E →L[ℝ] ℝ :=
  -(α q (0, 1))⁻¹ • (α q).comp (ContinuousLinearMap.inl ℝ E ℝ)

theorem oneFormGraph_kernel {α : E × ℝ → (E × ℝ) →L[ℝ] ℝ} {q : E × ℝ}
    (hq : α q (0, 1) ≠ 0) (h : E) : α q (h, oneFormGraph α q h) = 0 := by
  have he : (h, oneFormGraph α q h) =
      (h, (0 : ℝ)) + (oneFormGraph α q h) • (0, 1) := by ext <;> simp
  rw [he, map_add, map_smul]
  simp only [oneFormGraph, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, smul_eq_mul]
  field_simp
  <;> ring

theorem oneFormGraph_smooth {V : Set (E × ℝ)} {α : E × ℝ → (E × ℝ) →L[ℝ] ℝ}
    (hα : ContDiffOn ℝ ∞ α V) (hn : ∀ q ∈ V, α q (0, 1) ≠ 0) :
    ContDiffOn ℝ ∞ (oneFormGraph α) V := by
  exact ((hα.clm_apply contDiffOn_const).inv hn).neg.smul
    (hα.clm_comp contDiffOn_const)

theorem oneFormGraph_kernel_iff {α : E × ℝ → (E × ℝ) →L[ℝ] ℝ} {q : E × ℝ}
    (hq : α q (0, 1) ≠ 0) (v : E × ℝ) :
    α q v = 0 ↔ v.2 = oneFormGraph α q v.1 := by
  have he : v = (v.1, oneFormGraph α q v.1) +
      (v.2 - oneFormGraph α q v.1) • (0, 1) := by ext <;> simp
  have hh : α q v = (v.2 - oneFormGraph α q v.1) * α q (0, 1) := by
    conv_lhs => rw [he, map_add, map_smul, oneFormGraph_kernel hq, zero_add]
    rfl
  rw [hh, mul_eq_zero, or_iff_left hq, sub_eq_zero]

theorem oneFormGraph_flat {V : Set (E × ℝ)} (hV : IsOpen V)
    {α : E × ℝ → (E × ℝ) →L[ℝ] ℝ} (hα : ContDiffOn ℝ ∞ α V)
    (hn : ∀ q ∈ V, α q (0, 1) ≠ 0) (hc : FrobeniusOneForm α V) :
    FlatConnection (oneFormGraph α) V := by
  let A := oneFormGraph α
  have hA := oneFormGraph_smooth hα hn
  intro q hq v w
  have hαd := ((hα.contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  have hAd := ((hA.contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  have hz (h k : E) :
      fderiv ℝ α q (k, A q k) (h, A q h) +
        α q (0, fderiv ℝ A q (k, A q k) h) = 0 := by
    have hd := hαd.clm_apply ((hasFDerivAt_const h q).prodMk
      (hAd.clm_apply (hasFDerivAt_const h q)))
    have he : (fun z => α z (h, A z h)) =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [hV.mem_nhds hq] with z hz
      exact oneFormGraph_kernel (hn z hz) h
    have hh := hd.unique ((hasFDerivAt_const (0 : ℝ) q).congr_of_eventuallyEq he)
    have hh' := congrArg (fun L : (E × ℝ) →L[ℝ] ℝ => L (k, A q k)) hh
    simpa [A, add_comm] using hh'
  have hs := hc q hq (v, A q v) (w, A q w)
    (oneFormGraph_kernel (hn q hq) v) (oneFormGraph_kernel (hn q hq) w)
  have hv := hz v w
  have hw := hz w v
  rw [hs] at hw
  have he : α q (0, fderiv ℝ A q (v, A q v) w) =
      α q (0, fderiv ℝ A q (w, A q w) v) := by linarith
  have hev (s : ℝ) : α q (0, s) = s * α q (0, 1) := by
    have he : ((0 : E), s) = s • (0, (1 : ℝ)) := by simp
    rw [he, map_smul, smul_eq_mul]
  rw [hev (fderiv ℝ A q (v, A q v) w), hev (fderiv ℝ A q (w, A q w) v)] at he
  exact mul_right_cancel₀ (hn q hq) he

/-- A first integral whose differential has exactly the prescribed kernel. -/
theorem oneFormGraph_first_integral {V : Set (E × ℝ)} (hV : IsOpen V)
    {α : E × ℝ → (E × ℝ) →L[ℝ] ℝ} (hα : ContDiffOn ℝ ∞ α V)
    (hn : ∀ q ∈ V, α q (0, 1) ≠ 0) (hc : FrobeniusOneForm α V)
    {y₀ : ℝ} (hy₀ : (0, y₀) ∈ V) :
    ∃ W : Set (E × ℝ), ∃ f : E × ℝ → ℝ,
      IsOpen W ∧ (0, y₀) ∈ W ∧ W ⊆ V ∧ ContDiffOn ℝ ∞ f W ∧
      ∀ q ∈ W, ∀ v, fderiv ℝ f q v = 0 ↔ α q v = 0 := by
  obtain ⟨e, hep, heV, hes, hei, heh⟩ := flatConnection_local_coordinates hV
    (oneFormGraph_smooth hα hn) (oneFormGraph_flat hV hα hn hc) hy₀
  let f : E × ℝ → ℝ := fun q => (e q).2
  refine ⟨e.source, f, e.open_source, hep, heV, hes.snd, ?_⟩
  intro q hq v
  have hed := ((hes.contDiffAt (e.open_source.mem_nhds hq)).differentiableAt
    (by simp)).hasFDerivAt
  have hf := hed.snd
  have hh : (fun z => (e z).1) =ᶠ[𝓝 q] Prod.fst := by
    filter_upwards [e.open_source.mem_nhds hq] with z hz
    exact (heh z hz).1
  have hfst := hed.fst.unique (hasFDerivAt_fst.congr_of_eventuallyEq hh)
  have hcoord (w : E × ℝ) : fderiv ℝ e q w = (w.1, fderiv ℝ f q w) := by
    apply Prod.ext
    · exact congrArg (fun L : (E × ℝ) →L[ℝ] E => L w) hfst
    · exact congrArg (fun L : (E × ℝ) →L[ℝ] ℝ => L w) hf.fderiv.symm
  rw [oneFormGraph_kernel_iff (hn q (heV hq)) v]
  constructor
  · intro hv
    have heq : fderiv ℝ e q v = fderiv ℝ e q (v.1, oneFormGraph α q v.1) := by
      rw [hcoord v, hv, (heh q hq).2]
    exact congrArg Prod.snd (chart_fderiv_injective e hes hei hq heq)
  · intro hv
    have heq : v = (v.1, oneFormGraph α q v.1) := Prod.ext rfl hv
    have hh := congrArg Prod.snd ((heh q hq).2 v.1)
    rw [hcoord] at hh
    simpa only [← heq] using hh

end SemiHamiltonian.Geometry
