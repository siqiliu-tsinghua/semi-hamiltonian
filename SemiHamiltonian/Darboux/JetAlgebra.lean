module

public import SemiHamiltonian.Darboux.C1FixedPoint
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Module.Basic

/-! Operations on functions with a recorded, scaled derivative. -/

@[expose] public section

open scoped Topology NNReal
open MeasureTheory
open Filter

namespace SemiHamiltonian.Darboux

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsFunctionJet.intervalIntegral {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    {R : E → K} {U : Set E} (hU : IsOpen U) {a : ℝ}
    (f : ℝ → FunctionJet K E F) (hf : ∀ t, IsFunctionJet R U a (f t))
    (b c : ℝ) : IsFunctionJet R U a (∫ t in b..c, f t) := by
  let S : Submodule ℝ (FunctionJet K E F) := functionJets R U a
  have hs : IsClosed (S : Set (FunctionJet K E F)) := isClosed_isFunctionJet R hU a
  let : CompleteSpace S := hs.isComplete.completeSpace_coe
  let : NormedSpace ℝ S := Submodule.normedSpace (𝕜 := ℝ) (R := ℝ)
    (E := FunctionJet K E F) S
  let g : ℝ → S := fun t => ⟨f t, hf t⟩
  have h := LinearIsometry.intervalIntegral_comp_comm (𝕜 := ℝ) (E := S)
    (F := FunctionJet K E F) (a := b) (b := c) (μ := volume)
    (Submodule.subtypeₗᵢ (R' := ℝ) (E := FunctionJet K E F) S) g
  change (∫ t in b..c, f t) ∈ S
  rw [show (∫ t in b..c, f t) = ((∫ t in b..c, g t : S) : FunctionJet K E F) from h]
  exact (∫ t in b..c, g t : S).property

noncomputable def jetMul (f g : FunctionJet K E ℝ) : FunctionJet K E ℝ :=
  (f.1 * g.1, ⟨fun x => f.1 x • g.2 x + g.1 x • f.2 x,
    (f.1.continuous.smul g.2.continuous).add (g.1.continuous.smul f.2.continuous)⟩)

omit [CompactSpace K] in
theorem IsFunctionJet.mul {R : E → K} {U : Set E} {a : ℝ}
    {f g : FunctionJet K E ℝ} (hf : IsFunctionJet R U a f)
    (hg : IsFunctionJet R U a g) : IsFunctionJet R U a (jetMul f g) := by
  intro x hx
  have h := (hf x hx).mul (hg x hx)
  convert h using 1
  · rfl
  · simp only [jetMul, ContinuousMap.coe_mk, smul_add, smul_comm a]

theorem jetMul_norm_le (f g : FunctionJet K E ℝ) :
    ‖jetMul f g‖ ≤ 2 * ‖f‖ * ‖g‖ := by
  rw [Prod.norm_def, max_le_iff]
  constructor
  · change ‖f.1 * g.1‖ ≤ _
    have h := (norm_mul_le f.1 g.1).trans
      (mul_le_mul (norm_fst_le f) (norm_fst_le g) (norm_nonneg g.1) (norm_nonneg f))
    nlinarith [norm_nonneg f, norm_nonneg g]
  · apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    change ‖f.1 x • g.2 x + g.1 x • f.2 x‖ ≤ _
    calc
      _ ≤ ‖f.1 x‖ * ‖g.2 x‖ + ‖g.1 x‖ * ‖f.2 x‖ := by
        simpa only [norm_smul] using norm_add_le (f.1 x • g.2 x) (g.1 x • f.2 x)
      _ ≤ ‖f‖ * ‖g‖ + ‖g‖ * ‖f‖ := add_le_add
        (mul_le_mul ((f.1.norm_coe_le_norm x).trans (norm_fst_le f))
          ((g.2.norm_coe_le_norm x).trans (norm_snd_le g)) (norm_nonneg (g.2 x)) (norm_nonneg f))
        (mul_le_mul ((g.1.norm_coe_le_norm x).trans (norm_fst_le g))
          ((f.2.norm_coe_le_norm x).trans (norm_snd_le f)) (norm_nonneg (f.2 x)) (norm_nonneg g))
      _ = _ := by ring

noncomputable def jetPull (P : C(K, K)) (B : E →L[ℝ] E) (f : FunctionJet K E ℝ) :
    FunctionJet K E ℝ :=
  (f.1.comp P, ⟨fun x => (f.2 (P x)).comp B,
    (f.2.continuous.comp P.continuous).clm_comp continuous_const⟩)

omit [CompactSpace K] in
theorem IsFunctionJet.pull {R : E → K} {U : Set E} (hU : IsOpen U) {a : ℝ}
    {f : FunctionJet K E ℝ} (hf : IsFunctionJet R U a f)
    (P : C(K, K)) (B : E →L[ℝ] E)
    (hB : Set.MapsTo B U U) (hP : ∀ x ∈ U, P (R x) = R (B x)) :
    IsFunctionJet R U a (jetPull P B f) := by
  intro x hx
  have h := (hf (B x) (hB hx)).comp x B.hasFDerivAt
  have he : (fun y => f.1 (P (R y))) =ᶠ[𝓝 x] (fun y => f.1 (R (B y))) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [hP y hy]
  have hd : a • (f.2 (P (R x))).comp B = (a • f.2 (R (B x))).comp B := by
    rw [hP x hx, ContinuousLinearMap.smul_comp]
  change HasFDerivAt (fun y => f.1 (P (R y))) (a • (f.2 (P (R x))).comp B) x
  rw [hd]
  exact h.congr_of_eventuallyEq he

theorem jetPull_norm_le (P : C(K, K)) (B : E →L[ℝ] E) (hB : ‖B‖ ≤ 1)
    (f : FunctionJet K E ℝ) : ‖jetPull P B f‖ ≤ ‖f‖ := by
  rw [Prod.norm_def, max_le_iff]
  constructor
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro x
    exact (f.1.norm_coe_le_norm _).trans (norm_fst_le f)
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro x
    calc
      ‖(f.2 (P x)).comp B‖ ≤ ‖f.2 (P x)‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖f‖ * 1 := mul_le_mul ((f.2.norm_coe_le_norm _).trans (norm_snd_le f))
        hB (norm_nonneg B) (norm_nonneg f)
      _ = _ := mul_one _

omit [CompactSpace K] in
theorem jetMul_sub (f g h : FunctionJet K E ℝ) :
    jetMul f (g - h) = jetMul f g - jetMul f h := by
  apply Prod.ext
  · apply ContinuousMap.ext
    intro x
    change f.1 x * (g.1 x - h.1 x) = f.1 x * g.1 x - f.1 x * h.1 x
    ring
  · apply ContinuousMap.ext
    intro x
    change f.1 x • (g.2 x - h.2 x) + (g.1 x - h.1 x) • f.2 x =
      (f.1 x • g.2 x + g.1 x • f.2 x) - (f.1 x • h.2 x + h.1 x • f.2 x)
    rw [smul_sub, sub_smul]
    abel

omit [CompactSpace K] in
theorem jetPull_sub (P : C(K, K)) (B : E →L[ℝ] E) (f g : FunctionJet K E ℝ) :
    jetPull P B (f - g) = jetPull P B f - jetPull P B g := by
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro x
    exact ContinuousLinearMap.sub_comp _ _ _

end SemiHamiltonian.Darboux
