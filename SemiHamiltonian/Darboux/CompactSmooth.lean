module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.MeanValue

/-! Smooth families of continuous functions on a compact parameter space. -/

@[expose] public section

open scoped Topology ContDiff
open Filter Set

set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency.types false

namespace SemiHamiltonian.Darboux

universe u

variable {K : Type*} {E D F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Exchange a compact continuous parameter with a continuous linear argument. -/
noncomputable def compactFlip : C(K, E →L[ℝ] F) →L[ℝ] (E →L[ℝ] C(K, F)) :=
  LinearMap.mkContinuous (E := C(K, E →L[ℝ] F)) (F := E →L[ℝ] C(K, F))
    ({ toFun := fun g => LinearMap.mkContinuous
        ({ toFun := fun v => ⟨fun k => g k v, g.continuous.clm_apply continuous_const⟩
           map_add' := by intros; ext; simp
           map_smul' := by intros; ext; simp } : E →ₗ[ℝ] C(K, F))
        ‖g‖ (by
          intro v
          apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg g) (norm_nonneg v))).mpr
          intro k
          exact (g k).le_opNorm v |>.trans
            (mul_le_mul_of_nonneg_right (g.norm_coe_le_norm k) (norm_nonneg v)))
       map_add' := by intros; ext; rfl
       map_smul' := by intros; ext; rfl } : C(K, E →L[ℝ] F) →ₗ[ℝ] (E →L[ℝ] C(K, F)))
    1 (by
      intro g
      simp only [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
      intro v
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg g) (norm_nonneg v))).mpr
      intro k
      exact (g k).le_opNorm v |>.trans
        (mul_le_mul_of_nonneg_right (g.norm_coe_le_norm k) (norm_nonneg v)))

@[simp] theorem compactFlip_apply (g : C(K, E →L[ℝ] F)) (v : E) (k : K) :
    compactFlip g v k = g k v := rfl

/-- Pointwise derivatives continuous in the uniform norm give the derivative in
the Banach space of continuous functions. -/
theorem hasFDerivAt_compactFamily {U : Set E} (hU : IsOpen U)
    (f : E → C(K, F)) (g : E → C(K, E →L[ℝ] F)) {x : E} (hx : x ∈ U)
    (hg : ContinuousAt g x)
    (hd : ∀ y ∈ U, ∀ k, HasFDerivAt (fun z => f z k) (g y k) y) :
    HasFDerivAt f (compactFlip (g x)) x := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hn : Continuous (fun a : C(K, E →L[ℝ] F) => ‖a‖) :=
    continuous_norm (E := C(K, E →L[ℝ] F))
  have ht : Tendsto (fun y => ‖g y - g x‖) (𝓝 x) (𝓝 (0 : ℝ)) := by
    simpa only [ContinuousAt, Function.comp_def, Pi.sub_apply, sub_self,
      norm_zero (E := C(K, E →L[ℝ] F))] using
      hn.continuousAt.comp (hg.sub (continuousAt_const (y := g x)))
  have hclose : ∀ᶠ y in 𝓝 x, ‖g y - g x‖ < ε :=
    ht.eventually (gt_mem_nhds hε)
  have hnb : ∀ᶠ y in 𝓝 x, y ∈ U ∧ ‖g y - g x‖ < ε := by
    filter_upwards [hU.mem_nhds hx, hclose] with y hy hc
    exact ⟨hy, hc⟩
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp hnb
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro k
  change ‖f y k - f x k - g x k (y - x)‖ ≤ ε * ‖y - x‖
  exact (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (hd z (hb hz).1 k).hasFDerivWithinAt)
    (fun z hz => ((g z - g x).norm_coe_le_norm k).trans (hb hz).2.le)
    (Metric.mem_ball_self hδ) hy

/-- Apply a continuous family of linear maps to a smooth function. `mkD` only
supplies irrelevant values outside the open parameter domain. -/
noncomputable def compactLinearFamily (q : C(K, E →L[ℝ] D)) (f : D → F)
    (x : E) : C(K, F) := ContinuousMap.mkD (fun k => f (q k x)) 0

theorem compactLinearFamily_apply (q : C(K, E →L[ℝ] D)) {f : D → F}
    {V : Set D} (hf : ContinuousOn f V) {x : E} (hx : ∀ k, q k x ∈ V) (k : K) :
    compactLinearFamily q f x k = f (q k x) :=
  ContinuousMap.mkD_apply_of_continuous
    (hf.comp_continuous (q.continuous.clm_apply continuous_const) hx)

theorem continuousOn_compactLinearFamily (q : C(K, E →L[ℝ] D)) {f : D → F}
    {U : Set E} {V : Set D} (hf : ContinuousOn f V)
    (hm : ∀ x ∈ U, ∀ k, q k x ∈ V) : ContinuousOn (compactLinearFamily q f) U := by
  apply ContinuousMap.continuousOn_mkD_of_uncurry
  exact hf.comp (q.continuous.comp continuous_snd |>.clm_apply continuous_fst).continuousOn
    (fun p hp => hm p.1 hp.1 p.2)

/-- Compose a compact family of operators with a fixed compact family. -/
noncomputable def compactPrecomp (q : C(K, E →L[ℝ] D)) :
    C(K, D →L[ℝ] F) →L[ℝ] C(K, E →L[ℝ] F) :=
  LinearMap.mkContinuous (E := C(K, D →L[ℝ] F)) (F := C(K, E →L[ℝ] F))
    ({ toFun := fun g => ⟨fun k => (g k).comp (q k), g.continuous.clm_comp q.continuous⟩
       map_add' := by intros; ext; simp
       map_smul' := by intros; ext; simp } :
      C(K, D →L[ℝ] F) →ₗ[ℝ] C(K, E →L[ℝ] F))
    ‖q‖ (by
      intro g
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg q) (norm_nonneg g))).mpr
      intro k
      calc
        ‖(g k).comp (q k)‖ ≤ ‖g k‖ * ‖q k‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖g‖ * ‖q‖ := mul_le_mul (g.norm_coe_le_norm k) (q.norm_coe_le_norm k)
          (norm_nonneg _) (norm_nonneg g)
        _ = _ := mul_comm _ _)

@[simp] theorem compactPrecomp_apply (q : C(K, E →L[ℝ] D))
    (g : C(K, D →L[ℝ] F)) (k : K) : compactPrecomp q g k = (g k).comp (q k) := rfl

/-- Uniform smoothness of a family on a compact set of linear substitutions.
The parameter domain is fixed for all orders of differentiability. -/
theorem contDiffOn_compactLinearFamily_nat (n : ℕ) (q : C(K, E →L[ℝ] D))
    {U : Set E} {V : Set D} (hU : IsOpen U) (hV : IsOpen V)
    (hm : ∀ x ∈ U, ∀ k, q k x ∈ V) {f : D → F}
    (hf : ContDiffOn ℝ n f V) : ContDiffOn ℝ n (compactLinearFamily q f) U := by
  induction n generalizing F with
  | zero =>
      exact contDiffOn_zero.mpr (continuousOn_compactLinearFamily q hf.continuousOn hm)
  | succ n ih =>
      have hdf : ContDiffOn ℝ n (fderiv ℝ f) V := hf.fderiv_of_isOpen hV (by simp)
      let G : E → C(K, E →L[ℝ] F) := fun x =>
        compactPrecomp q (compactLinearFamily q (fderiv ℝ f) x)
      have hpc : ContDiff ℝ n (compactPrecomp (K := K) (E := E) (D := D) (F := F) q) :=
        ContinuousLinearMap.contDiff _
      have hG : ContDiffOn ℝ n G U := by
        simpa only [Function.comp_def, G] using hpc.comp_contDiffOn (ih hdf)
      have hd : ∀ x ∈ U, HasFDerivAt (compactLinearFamily q f) (compactFlip (G x)) x := by
        intro x hx
        apply hasFDerivAt_compactFamily hU _ G hx
          (hG.continuousOn.continuousAt (hU.mem_nhds hx))
        intro y hy k
        have hyV := hm y hy k
        have hder := (hf.differentiableOn (by simp) (q k y) hyV).differentiableAt (hV.mem_nhds hyV)
        have he : (fun z => compactLinearFamily q f z k) =ᶠ[𝓝 y] (fun z => f (q k z)) := by
          filter_upwards [hU.mem_nhds hy] with z hz
          exact compactLinearFamily_apply q hf.continuousOn (hm z hz) k
        have hh := hder.hasFDerivAt.comp y (q k).hasFDerivAt
        change HasFDerivAt _ ((compactLinearFamily q (fderiv ℝ f) y k).comp (q k)) y
        rw [compactLinearFamily_apply q hdf.continuousOn (hm y hy) k]
        exact hh.congr_of_eventuallyEq he
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
        contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn]
      refine ⟨by simp, fun x => compactFlip (G x), ?_, fun x hx => (hd x hx).hasFDerivWithinAt⟩
      exact (ContinuousLinearMap.contDiff (E := C(K, E →L[ℝ] F)) (F := E →L[ℝ] C(K, F))
        compactFlip).comp_contDiffOn hG

theorem contDiffOn_compactLinearFamily (q : C(K, E →L[ℝ] D))
    {U : Set E} {V : Set D} (hU : IsOpen U) (hV : IsOpen V)
    (hm : ∀ x ∈ U, ∀ k, q k x ∈ V) {f : D → F}
    (hf : ContDiffOn ℝ ∞ f V) : ContDiffOn ℝ ∞ (compactLinearFamily q f) U := by
  rw [contDiffOn_infty]
  intro n
  exact contDiffOn_compactLinearFamily_nat n q hU hV hm (hf.of_le (by simp))

end SemiHamiltonian.Darboux
