module

public import SemiHamiltonian.Geometry.RadialEquation

/-! Variational equations for the smooth family of radial integral curves. -/

@[expose] public section

open scoped Topology ContDiff
open Filter Set

set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency.types false

namespace SemiHamiltonian.Geometry

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

structure IsRadialSolution (A : E × F → E →L[ℝ] F) (V W : Set (E × F))
    (u : E × F → C(Time, F)) : Prop where
  smooth : ContDiffOn ℝ ∞ u W
  maps : ∀ p ∈ W, ∀ s : Time, ((s : ℝ) • p.1, u p s) ∈ V
  fixed : ∀ p ∈ W, u p = constPathCLM p.2 + primitiveCLM (radialKernel A p.1 (u p))

namespace IsRadialSolution

variable {V W : Set (E × F)} (hV : IsOpen V) (hW : IsOpen W)
  {A : E × F → E →L[ℝ] F} (hA : ContDiffOn ℝ ∞ A V)
  {u : E × F → C(Time, F)} (hu : IsRadialSolution A V W u)

include hu

theorem initial {p : E × F} (hp : p ∈ W) : u p ⟨0, by norm_num⟩ = p.2 := by
  rw [hu.fixed p hp]
  simp

include hA

theorem timeDerivative {p : E × F} (hp : p ∈ W) {s : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun t => u p (timeClamp t)) (A (s • p.1, u p (timeClamp s)) p.1) s := by
  have hd := (primitiveCLM_hasDerivAt (radialKernel A p.1 (u p)) hs).const_add p.2
  rw [radialKernel_apply hA.continuousOn (hu.maps p hp), timeClamp_val (Ioo_subset_Icc_self hs)] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with t
  have he := congrArg (fun z : C(Time, F) => z (timeClamp t)) (hu.fixed p hp)
  simpa only [ContinuousMap.add_apply, constPathCLM_apply] using he

include hV

theorem kernel_smooth :
    ContDiffOn ℝ ∞ (fun p : E × F => radialKernel A p.1 (u p)) W := by
  have hl : ContDiffOn ℝ ∞ (fun p : E × F => liftPathCLM (p.1, u p)) W :=
    (ContinuousLinearMap.contDiff _).comp_contDiffOn (contDiffOn_fst.prodMk hu.smooth)
  have hs : ContDiffOn ℝ ∞ (fun p : E × F => superpose A (liftPathCLM (p.1, u p))) W :=
    (contDiffOn_superpose hV hA).comp hl (fun p hp => hu.maps p hp)
  have hpoint : ContDiff ℝ ∞ (pointwiseCLM (K := Time) (E := E) (F := F)) :=
    ContinuousLinearMap.contDiff _
  have hconst : ContDiff ℝ ∞ (fun p : E × F => constPathCLM p.1) := by fun_prop
  exact (hpoint.comp_contDiffOn hs).clm_apply hconst.contDiffOn

include hW

theorem kernel_derivative {p : E × F} (hp : p ∈ W) (h : E × F) (s : Time) :
    fderiv ℝ (fun q : E × F => radialKernel A q.1 (u q)) p h s =
      A ((s : ℝ) • p.1, u p s) h.1 +
        fderiv ℝ A ((s : ℝ) • p.1, u p s)
          ((s : ℝ) • h.1, fderiv ℝ u p h s) p.1 := by
  have hdu := ((hu.smooth.contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hdk := (((hu.kernel_smooth hV hA).contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have he : (fun q : E × F => radialKernel A q.1 (u q) s) =ᶠ[𝓝 p]
      (fun q => A ((s : ℝ) • q.1, u q s) q.1) := by
    filter_upwards [hW.mem_nhds hp] with q hq
    exact radialKernel_apply hA.continuousOn (hu.maps q hq) s
  have hpath := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).const_smul (s : ℝ) |>.prodMk
    ((ContinuousMap.evalCLM ℝ s).hasFDerivAt.comp p hdu)
  have ha := ((hA.contDiffAt (hV.mem_nhds (hu.maps p hp s))).differentiableAt (by simp)).hasFDerivAt
  have hh := (ha.comp p hpath).clm_apply (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  simp only [Function.comp_def, Pi.smul_def, ContinuousMap.evalCLM_apply] at hh
  have hkeval : HasFDerivAt (fun q : E × F => radialKernel A q.1 (u q) s)
      ((ContinuousMap.evalCLM ℝ (M := F) s).comp
        (fderiv ℝ (fun q : E × F => radialKernel A q.1 (u q)) p)) p :=
    (ContinuousMap.evalCLM ℝ (M := F) s).hasFDerivAt.comp p hdk
  have heq := hkeval.unique
    (hh.congr_of_eventuallyEq he)
  have hev := congrArg (fun L : (E × F) →L[ℝ] F => L h) heq
  simpa [Function.comp_def, Pi.smul_def] using hev

theorem parameterDerivative_fixed {p : E × F} (hp : p ∈ W) (h : E × F) :
    fderiv ℝ u p h = constPathCLM h.2 +
      primitiveCLM (fderiv ℝ (fun q : E × F => radialKernel A q.1 (u q)) p h) := by
  have he : u =ᶠ[𝓝 p] (fun q => constPathCLM q.2 + primitiveCLM (radialKernel A q.1 (u q))) := by
    filter_upwards [hW.mem_nhds hp] with q hq
    exact hu.fixed q hq
  have hdk := (((hu.kernel_smooth hV hA).contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hd := ((constPathCLM (E := F)).hasFDerivAt.comp p hasFDerivAt_snd).add
    ((primitiveCLM (E := F)).hasFDerivAt.comp p hdk)
  have hdf := he.fderiv_eq (𝕜 := ℝ)
  simp only [Pi.add_def, Function.comp_def] at hd
  rw [hd.fderiv] at hdf
  exact congrArg (fun L : (E × F) →L[ℝ] C(Time, F) => L h) hdf

theorem parameterDerivative_time {p : E × F} (hp : p ∈ W) (h : E × F)
    {s : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun t => fderiv ℝ u p h (timeClamp t))
      (A (s • p.1, u p (timeClamp s)) h.1 +
        fderiv ℝ A (s • p.1, u p (timeClamp s))
          (s • h.1, fderiv ℝ u p h (timeClamp s)) p.1) s := by
  have hd := (primitiveCLM_hasDerivAt
    (fderiv ℝ (fun q : E × F => radialKernel A q.1 (u q)) p h) hs).const_add h.2
  rw [hu.kernel_derivative hV hW hA hp h (timeClamp s),
    timeClamp_val (Ioo_subset_Icc_self hs)] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with t
  have he := congrArg (fun z : C(Time, F) => z (timeClamp t))
    (hu.parameterDerivative_fixed hV hW hA hp h)
  simpa only [ContinuousMap.add_apply, constPathCLM_apply] using he

end IsRadialSolution
end SemiHamiltonian.Geometry
