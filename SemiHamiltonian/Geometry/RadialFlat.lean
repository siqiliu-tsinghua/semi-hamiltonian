module

public import SemiHamiltonian.Geometry.RadialVariations
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Frobenius compatibility eliminates the radial solution's transverse defect. -/

@[expose] public section

open scoped Topology ContDiff
open Filter Set

set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency.types false

namespace SemiHamiltonian.Geometry

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def FlatConnection (A : E × F → E →L[ℝ] F) (V : Set (E × F)) : Prop :=
  ∀ q ∈ V, ∀ v w : E,
    fderiv ℝ A q (v, A q v) w = fderiv ℝ A q (w, A q w) v

private theorem radial_linear_identity (D : (E × F) →L[ℝ] (E →L[ℝ] F))
    (B : E →L[ℝ] F) (x h : E) (v : F) (s : ℝ)
    (hc : D (h, B h) x = D (x, B x) h) :
    (B h + D (s • h, v) x) - (s • D (x, B x) h + B h) =
      D (0, v - s • B h) x := by
  have he : (0, v - s • B h) = (s • h, v) - s • (h, B h) := by
    ext <;> simp
  rw [he, map_sub, map_smul]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
  rw [hc]
  abel

private theorem linear_path_unique (B : C(Time, F →L[ℝ] F)) {e : ℝ → F}
    (he : ∀ s ∈ Ioo (-2 : ℝ) 2, HasDerivAt e (B (timeClamp s) (e s)) s)
    (h0 : e 0 = 0) : e 1 = 0 := by
  have hLip (s : ℝ) : LipschitzWith ‖B‖₊ (B (timeClamp s)) :=
    ContinuousLinearMap.opNorm_le_iff_lipschitzWith.mp (B.norm_coe_le_norm (timeClamp s))
  have hh := ODE_solution_unique_of_mem_Ioo
    (f := e) (g := fun _ : ℝ => (0 : F))
    (s := fun _ => Set.univ) (fun s _ => (hLip s).lipschitzOnWith)
    (by norm_num : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2)
    (fun s hs => ⟨he s hs, Set.mem_univ _⟩)
    (fun s _ => ⟨by simpa only [map_zero] using hasDerivAt_const s (0 : F), Set.mem_univ _⟩) h0
  exact hh (by norm_num : (1 : ℝ) ∈ Ioo (-2 : ℝ) 2)

namespace IsRadialSolution

variable {V W : Set (E × F)} (hV : IsOpen V) (hW : IsOpen W)
  {A : E × F → E →L[ℝ] F} (hA : ContDiffOn ℝ ∞ A V)
  {u : E × F → C(Time, F)} (hu : IsRadialSolution A V W u)

include hV hW hA hu

theorem horizontalDerivative (hc : FlatConnection A V) {p : E × F} (hp : p ∈ W) (h : E) :
    fderiv ℝ (fun q => u q timeOne) p (h, 0) = A (p.1, u p timeOne) h := by
  let e : ℝ → F := fun s => fderiv ℝ u p (h, 0) (timeClamp s) -
    s • A (s • p.1, u p (timeClamp s)) h
  let dA : C(Time, (E × F) →L[ℝ] (E →L[ℝ] F)) :=
    superpose (fderiv ℝ A) (liftPathCLM (p.1, u p))
  have hdf := hA.fderiv_of_isOpen hV (m := ∞) (by simp)
  have hdAe (s : Time) : dA s = fderiv ℝ A ((s : ℝ) • p.1, u p s) := by
    have hm : liftPathCLM (p.1, u p) ∈ PathDomain V := hu.maps p hp
    exact superpose_apply hdf.continuousOn hm s
  let B : C(Time, F →L[ℝ] F) :=
    ⟨fun s => ((dA s).comp (ContinuousLinearMap.inr ℝ E F)).flip p.1, by
      have hcomp := dA.continuous.clm_comp (continuous_const (y := ContinuousLinearMap.inr ℝ E F))
      have hflip := (ContinuousLinearMap.flipₗᵢ ℝ F E F).continuous.comp hcomp
      exact hflip.clm_apply continuous_const⟩
  have hB (s : ℝ) (hs : s ∈ Ioo (-2 : ℝ) 2) (z : F) :
      B (timeClamp s) z = fderiv ℝ A (s • p.1, u p (timeClamp s)) (0, z) p.1 := by
    change dA (timeClamp s) (0, z) p.1 = _
    rw [hdAe, timeClamp_val (Ioo_subset_Icc_self hs)]
  have hder (s : ℝ) (hs : s ∈ Ioo (-2 : ℝ) 2) : HasDerivAt e (B (timeClamp s) (e s)) s := by
    have hqs : (s • p.1, u p (timeClamp s)) ∈ V := by
      simpa only [timeClamp_val (Ioo_subset_Icc_self hs)] using hu.maps p hp (timeClamp s)
    have hqu := hu.timeDerivative hA hp hs
    have hq : HasDerivAt (fun t => (t • p.1, u p (timeClamp t)))
        (p.1, A (s • p.1, u p (timeClamp s)) p.1) s := by
      simpa only [one_smul, id_eq] using HasDerivAt.prodMk ((hasDerivAt_id s).smul_const p.1) hqu
    have hAt := ((hA.contDiffAt (hV.mem_nhds hqs)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s hq
    have hAh := hAt.clm_apply (hasDerivAt_const s h)
    simp only [map_zero, add_zero, Function.comp_def] at hAh
    have hprod := (hasDerivAt_id s).smul hAh
    have hvar := hu.parameterDerivative_time hV hW hA hp (h, 0) hs
    have hres := hvar.sub hprod
    simp only [Pi.smul_def', one_smul] at hres
    rw [hB s hs]
    change HasDerivAt e
      (fderiv ℝ A (s • p.1, u p (timeClamp s))
        (0, fderiv ℝ u p (h, 0) (timeClamp s) - s • A (s • p.1, u p (timeClamp s)) h) p.1) s
    rw [← radial_linear_identity _ _ p.1 h _ s (hc _ hqs h p.1)]
    exact hres
  have h0 : e 0 = 0 := by
    have hh := congrArg (fun z : C(Time, F) => z timeZero)
      (hu.parameterDerivative_fixed hV hW hA hp (h, 0))
    simp only [ContinuousMap.add_apply, constPathCLM_apply, timeZero, primitiveCLM_zero, add_zero,
      zero_add] at hh
    simpa only [e, timeClamp_zero, timeZero, zero_smul, sub_zero] using hh
  have he := linear_path_unique B hder h0
  have hdu := ((hu.smooth.contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hev := (ContinuousMap.evalCLM ℝ (M := F) timeOne).hasFDerivAt.comp p hdu
  simp only [Function.comp_def, ContinuousMap.evalCLM_apply] at hev
  rw [hev.fderiv]
  simpa only [e, timeClamp_one, one_smul, sub_eq_zero,
    ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply] using he

end IsRadialSolution
end SemiHamiltonian.Geometry
