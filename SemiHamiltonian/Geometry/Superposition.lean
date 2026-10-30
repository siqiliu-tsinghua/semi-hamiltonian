module

public import SemiHamiltonian.Darboux.CompactSmooth

/-! Smooth nonlinear substitution on spaces of continuous paths. This is used
to apply the Banach implicit function theorem to the ODE integral equation. -/

@[expose] public section

open scoped Topology ContDiff
open Filter Set

set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency.types false

namespace SemiHamiltonian.Geometry

universe u
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  {E F P : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def pointwiseCLM : C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
  LinearMap.mkContinuous (E := C(K, E →L[ℝ] F)) (F := C(K, E) →L[ℝ] C(K, F))
    ({ toFun := fun g => LinearMap.mkContinuous (E := C(K, E)) (F := C(K, F))
        ({ toFun := fun v => ⟨fun k => g k (v k), g.continuous.clm_apply v.continuous⟩
           map_add' := by intros; ext; simp
           map_smul' := by intros; ext; simp } : C(K, E) →ₗ[ℝ] C(K, F))
        ‖g‖ (by
          intro v
          apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg g) (norm_nonneg v))).mpr
          intro k
          exact (g k).le_opNorm (v k) |>.trans
            (mul_le_mul (g.norm_coe_le_norm k) (v.norm_coe_le_norm k) (norm_nonneg _) (norm_nonneg g)))
       map_add' := by intros; ext; rfl
       map_smul' := by intros; ext; rfl } :
      C(K, E →L[ℝ] F) →ₗ[ℝ] (C(K, E) →L[ℝ] C(K, F)))
    1 (by
      intro g
      simp only [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
      intro v
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg g) (norm_nonneg v))).mpr
      intro k
      exact (g k).le_opNorm (v k) |>.trans
        (mul_le_mul (g.norm_coe_le_norm k) (v.norm_coe_le_norm k) (norm_nonneg _) (norm_nonneg g)))

@[simp] theorem pointwiseCLM_apply (g : C(K, E →L[ℝ] F)) (v : C(K, E)) (k : K) :
    pointwiseCLM g v k = g k (v k) := rfl

/-- Uniform differentiability does not require the evaluation maps themselves
to depend continuously in operator norm on the compact parameter. -/
theorem hasFDerivAt_uniformFamily {W : Set P} (hW : IsOpen W)
    (f : P → C(K, F)) (g : P → P →L[ℝ] C(K, F)) {x : P} (hx : x ∈ W)
    (hg : ContinuousAt g x)
    (hd : ∀ y ∈ W, ∀ k, HasFDerivAt (fun z => f z k)
      ((ContinuousMap.evalCLM ℝ k).comp (g y)) y) : HasFDerivAt f (g x) x := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have ht : Tendsto (fun y => ‖g y - g x‖) (𝓝 x) (𝓝 (0 : ℝ)) := by
    simpa only [ContinuousAt, Function.comp_def, Pi.sub_apply, sub_self, norm_zero] using
      (hg.sub (continuousAt_const (y := g x))).norm
  have hnb : ∀ᶠ y in 𝓝 x, y ∈ W ∧ ‖g y - g x‖ < ε := by
    filter_upwards [hW.mem_nhds hx, ht.eventually (gt_mem_nhds hε)] with y hy he
    exact ⟨hy, he⟩
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp hnb
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro k
  change ‖f y k - f x k - g x (y - x) k‖ ≤ ε * ‖y - x‖
  change ‖f y k - f x k - ((ContinuousMap.evalCLM ℝ k).comp (g x)) (y - x)‖ ≤ ε * ‖y - x‖
  apply (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (hd z (hb hz).1 k).hasFDerivWithinAt) _ (Metric.mem_ball_self hδ) hy
  intro z hz
  apply le_trans _ (hb hz).2.le
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (g z - g x))
  intro v
  change ‖((g z - g x) v) k‖ ≤ ‖g z - g x‖ * ‖v‖
  exact ((g z - g x) v).norm_coe_le_norm k |>.trans ((g z - g x).le_opNorm v)

def PathDomain (V : Set E) : Set C(K, E) := {z | ∀ k, z k ∈ V}

theorem isOpen_pathDomain {V : Set E} (hV : IsOpen V) : IsOpen (PathDomain (K := K) V) := by
  simpa only [PathDomain, Set.MapsTo, Set.mem_univ, forall_true_left] using
    ContinuousMap.isOpen_setOfPred_mapsTo (X := K) (Y := E) isCompact_univ hV

noncomputable def superpose (f : E → F) (z : C(K, E)) : C(K, F) :=
  ContinuousMap.mkD (fun k => f (z k)) 0

theorem superpose_apply {V : Set E} {f : E → F} (hf : ContinuousOn f V)
    {z : C(K, E)} (hz : z ∈ PathDomain V) (k : K) : superpose f z k = f (z k) :=
  ContinuousMap.mkD_apply_of_continuous (hf.comp_continuous z.continuous hz)

theorem continuousOn_superpose {V : Set E} {f : E → F} (hf : ContinuousOn f V) :
    ContinuousOn (superpose (K := K) f) (PathDomain V) := by
  apply ContinuousMap.continuousOn_mkD_of_uncurry
  exact hf.comp continuous_eval.continuousOn (fun p hp => hp.1 p.2)

theorem contDiffOn_superpose_nat (n : ℕ) {V : Set E} (hV : IsOpen V) {f : E → F}
    (hf : ContDiffOn ℝ n f V) : ContDiffOn ℝ n (superpose (K := K) f) (PathDomain V) := by
  induction n generalizing F with
  | zero => exact contDiffOn_zero.mpr (continuousOn_superpose hf.continuousOn)
  | succ n ih =>
    have hW := isOpen_pathDomain (K := K) hV
    have hdf : ContDiffOn ℝ n (fderiv ℝ f) V := hf.fderiv_of_isOpen hV (by simp)
    let G : C(K, E) → C(K, E) →L[ℝ] C(K, F) := fun z => pointwiseCLM (superpose (fderiv ℝ f) z)
    have hpc : ContDiff ℝ n (pointwiseCLM (K := K) (E := E) (F := F)) :=
      ContinuousLinearMap.contDiff _
    have hG : ContDiffOn ℝ n G (PathDomain V) := by
      simpa only [Function.comp_def, G] using hpc.comp_contDiffOn (ih hdf)
    have hd : ∀ z ∈ PathDomain V, HasFDerivAt (superpose (K := K) f) (G z) z := by
      intro z hz
      apply hasFDerivAt_uniformFamily hW _ G hz
        (hG.continuousOn.continuousAt (hW.mem_nhds hz))
      intro y hy k
      have he : (fun w : C(K, E) => superpose f w k) =ᶠ[𝓝 y] (fun w => f (w k)) := by
        filter_upwards [hW.mem_nhds hy] with w hw
        exact superpose_apply hf.continuousOn hw k
      have hdy := ((hf.contDiffAt (hV.mem_nhds (hy k))).differentiableAt (by simp)).hasFDerivAt
      have h := hdy.comp y (ContinuousMap.evalCLM ℝ k).hasFDerivAt
      have heq : (ContinuousMap.evalCLM ℝ k).comp (G y) =
          (fderiv ℝ f (y k)).comp (ContinuousMap.evalCLM ℝ k) := by
        ext v
        change superpose (fderiv ℝ f) y k (v k) = _
        rw [superpose_apply hdf.continuousOn hy]
        rfl
      rw [heq]
      exact h.congr_of_eventuallyEq he
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hW.uniqueDiffOn]
    exact ⟨by simp, G, hG, fun z hz => (hd z hz).hasFDerivWithinAt⟩

theorem contDiffOn_superpose {V : Set E} (hV : IsOpen V) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f V) : ContDiffOn ℝ ∞ (superpose (K := K) f) (PathDomain V) := by
  rw [contDiffOn_infty]
  intro n
  exact contDiffOn_superpose_nat n hV (hf.of_le (by simp))

end SemiHamiltonian.Geometry
