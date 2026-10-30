module

public import SemiHamiltonian.Geometry.PathIntegral
public import SemiHamiltonian.Geometry.LocalInverse

/-! Smooth solutions of a radial nonlinear ODE, obtained by the Banach implicit
function theorem on continuous paths. No ODE parameter-regularity axiom is used. -/

@[expose] public section

open scoped Topology ContDiff
open Filter Set

set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency.types false

namespace SemiHamiltonian.Geometry

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

noncomputable def constPathCLM : E →L[ℝ] C(Time, E) :=
  Darboux.compactFlip (ContinuousMap.const Time (ContinuousLinearMap.id ℝ E))

@[simp] theorem constPathCLM_apply (x : E) (s : Time) : constPathCLM x s = x := rfl

noncomputable def liftPathCLM : E × C(Time, F) →L[ℝ] C(Time, E × F) :=
  LinearMap.mkContinuous (E := E × C(Time, F)) (F := C(Time, E × F))
    ({ toFun := fun p => ⟨fun s => ((s : ℝ) • p.1, p.2 s),
         (continuous_subtype_val.smul continuous_const).prodMk p.2.continuous⟩
       map_add' := by intros; ext s <;> simp [smul_add]
       map_smul' := by
         intro c p
         apply ContinuousMap.ext
         intro s
         apply Prod.ext
         · exact smul_comm (s : ℝ) c p.1
         · rfl } :
      E × C(Time, F) →ₗ[ℝ] C(Time, E × F))
    2 (by
      intro p
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro s
      change ‖((s : ℝ) • p.1, p.2 s)‖ ≤ _
      rw [Prod.norm_def, max_le_iff]
      have hs : |(s : ℝ)| ≤ 2 := abs_le.mpr s.property
      constructor
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul hs (norm_fst_le p) (norm_nonneg _) (by norm_num)
      · have hp := (p.2.norm_coe_le_norm s).trans (norm_snd_le p)
        nlinarith [norm_nonneg p])

@[simp] theorem liftPathCLM_apply (x : E) (u : C(Time, F)) (s : Time) :
    liftPathCLM (x, u) s = ((s : ℝ) • x, u s) := rfl

noncomputable def radialKernel (A : E × F → E →L[ℝ] F) (x : E) (u : C(Time, F)) : C(Time, F) :=
  pointwiseCLM (superpose A (liftPathCLM (x, u))) (constPathCLM x)

theorem radialKernel_apply {V : Set (E × F)} {A : E × F → E →L[ℝ] F}
    (hA : ContinuousOn A V) {x : E} {u : C(Time, F)}
    (hxu : ∀ s : Time, ((s : ℝ) • x, u s) ∈ V) (s : Time) :
    radialKernel A x u s = A ((s : ℝ) • x, u s) x := by
  unfold radialKernel
  have hm : liftPathCLM (x, u) ∈ PathDomain V := by
    intro t
    simpa only [liftPathCLM_apply] using hxu t
  rw [pointwiseCLM_apply, superpose_apply hA hm]
  rfl

@[simp] theorem radialKernel_zero (A : E × F → E →L[ℝ] F) (u : C(Time, F)) :
    radialKernel A 0 u = 0 := by simp [radialKernel]

noncomputable def radialResidual (A : E × F → E →L[ℝ] F)
    (q : (E × F) × C(Time, F)) : C(Time, F) :=
  q.2 - constPathCLM q.1.2 - primitiveCLM (radialKernel A q.1.1 q.2)

@[simp] theorem radialResidual_zero (A : E × F → E →L[ℝ] F) (y : F) (u : C(Time, F)) :
    radialResidual A ((0, y), u) = u - constPathCLM y := by simp [radialResidual]

def RadialDomain (V : Set (E × F)) : Set ((E × F) × C(Time, F)) :=
  {q | ∀ s : Time, ((s : ℝ) • q.1.1, q.2 s) ∈ V}

theorem isOpen_radialDomain {V : Set (E × F)} (hV : IsOpen V) : IsOpen (RadialDomain V) :=
  (isOpen_pathDomain (K := Time) hV).preimage
    (liftPathCLM.continuous.comp (continuous_fst.fst.prodMk continuous_snd))

theorem radialResidual_contDiff {V : Set (E × F)} (hV : IsOpen V)
    {A : E × F → E →L[ℝ] F} (hA : ContDiffOn ℝ ∞ A V) :
    ContDiffOn ℝ ∞ (radialResidual A) (RadialDomain V) := by
  have hl : ContDiff ℝ ∞ (fun q : (E × F) × C(Time, F) => liftPathCLM (q.1.1, q.2)) := by
    fun_prop
  have hs : ContDiffOn ℝ ∞ (fun q : (E × F) × C(Time, F) =>
      superpose A (liftPathCLM (q.1.1, q.2))) (RadialDomain V) :=
    (contDiffOn_superpose hV hA).comp hl.contDiffOn (fun _ hx => hx)
  have hpoint : ContDiff ℝ ∞ (pointwiseCLM (K := Time) (E := E) (F := F)) :=
    ContinuousLinearMap.contDiff _
  have hconst : ContDiff ℝ ∞ (fun q : (E × F) × C(Time, F) => constPathCLM q.1.1) := by
    fun_prop
  have hk : ContDiffOn ℝ ∞ (fun q : (E × F) × C(Time, F) =>
      radialKernel A q.1.1 q.2) (RadialDomain V) :=
    (hpoint.comp_contDiffOn hs).clm_apply hconst.contDiffOn
  have hprim : ContDiff ℝ ∞ (primitiveCLM (E := F)) := ContinuousLinearMap.contDiff _
  have hy : ContDiff ℝ ∞ (fun q : (E × F) × C(Time, F) => constPathCLM q.1.2) := by
    fun_prop
  exact (contDiffOn_snd.sub hy.contDiffOn).sub (hprim.comp_contDiffOn hk)

/-- A radial path solution depends smoothly on both its horizontal endpoint and
its initial vertical value, on a single neighbourhood independent of derivative order. -/
theorem exists_smooth_radial_solution {V : Set (E × F)} (hV : IsOpen V)
    {A : E × F → E →L[ℝ] F} (hA : ContDiffOn ℝ ∞ A V) {y₀ : F} (hy₀ : (0, y₀) ∈ V) :
    ∃ (W : Set (E × F)) (u : E × F → C(Time, F)), IsOpen W ∧ (0, y₀) ∈ W ∧
      ContDiffOn ℝ ∞ u W ∧ u (0, y₀) = constPathCLM y₀ ∧
      ∀ p ∈ W, (∀ s : Time, ((s : ℝ) • p.1, u p s) ∈ V) ∧
        u p = constPathCLM p.2 + primitiveCLM (radialKernel A p.1 (u p)) := by
  let q₀ : (E × F) × C(Time, F) := ((0, y₀), constPathCLM y₀)
  have hq₀ : q₀ ∈ RadialDomain V := by
    intro s
    simpa only [q₀, zero_smul, smul_zero, constPathCLM_apply] using hy₀
  have hd := radialResidual_contDiff hV hA
  have hopen := isOpen_radialDomain (F := F) hV
  have hda := (hd.contDiffAt (hopen.mem_nhds hq₀)).differentiableAt (by simp)
  have hpartial : ((fderiv ℝ (radialResidual A) q₀).comp
      (ContinuousLinearMap.inr ℝ (E × F) C(Time, F))) = ContinuousLinearMap.id ℝ C(Time, F) := by
    have hc := hda.hasFDerivAt.comp (constPathCLM y₀)
      ((hasFDerivAt_const ((0 : E), y₀) (constPathCLM y₀)).prodMk (hasFDerivAt_id (constPathCLM y₀)))
    have he : (radialResidual A ∘ fun z : C(Time, F) => ((0, y₀), z)) =
        fun z => z - constPathCLM y₀ := by funext z; simp
    rw [he] at hc
    exact hc.unique ((hasFDerivAt_id (constPathCLM y₀)).sub_const _)
  have hinv : ((fderiv ℝ (radialResidual A) q₀).comp
      (ContinuousLinearMap.inr ℝ (E × F) C(Time, F))).IsInvertible := by
    rw [hpartial]
    exact ⟨ContinuousLinearEquiv.refl ℝ C(Time, F), rfl⟩
  obtain ⟨W, B, u, hW, hpW, hB, hpB, hBU, hup, hu, hsol, huniq⟩ :=
    exists_smooth_implicit hopen hd hq₀ hinv
  refine ⟨W, u, hW, hpW, hu, hup, ?_⟩
  intro p hp
  obtain ⟨hpB, hpEq⟩ := hsol p hp
  refine ⟨hBU hpB, ?_⟩
  have hzero : radialResidual A q₀ = 0 := by simp [q₀]
  rw [hzero] at hpEq
  change u p - constPathCLM p.2 - primitiveCLM (radialKernel A p.1 (u p)) = 0 at hpEq
  have hh := eq_add_of_sub_eq (sub_eq_zero.mp hpEq)
  simpa only [add_comm] using hh

end SemiHamiltonian.Geometry
