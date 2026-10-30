module

public import SemiHamiltonian.Darboux.JetAlgebra
public import SemiHamiltonian.Darboux.CubeGeometry
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The radial integral operator acting on functions and their scaled derivatives. -/

@[expose] public section

set_option synthInstance.maxSize 512

open scoped NNReal Topology BigOperators
open MeasureTheory Filter

namespace SemiHamiltonian.Darboux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

abbrev ScalarJet := FunctionJet (Cube ι r) (ι → ℝ) ℝ
abbrev JetValues := ι → ScalarJet (ι := ι) r
abbrev JetCoefficients := ι → ι → ScalarJet (ι := ι) r

noncomputable instance instNormedAddCommGroupScalarJet : NormedAddCommGroup (ScalarJet (ι := ι) r) :=
  inferInstanceAs (NormedAddCommGroup
    (C(Cube ι r, ℝ) × C(Cube ι r, (ι → ℝ) →L[ℝ] ℝ)))

noncomputable instance instNormedAddCommGroupJetValues : NormedAddCommGroup (JetValues (ι := ι) r) :=
  inferInstanceAs (NormedAddCommGroup (ι → ScalarJet (ι := ι) r))

noncomputable instance instNormedSpaceScalarJet : NormedSpace ℝ (ScalarJet (ι := ι) r) where
  norm_smul_le c x := by
    change max ‖c • x.1‖ ‖c • x.2‖ ≤ ‖c‖ * max ‖x.1‖ ‖x.2‖
    have h₂ : ‖c • x.2‖ ≤ ‖c‖ * ‖x.2‖ := by
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro y
      change ‖c • x.2 y‖ ≤ ‖c‖ * ‖x.2‖
      exact (ContinuousLinearMap.opNorm_smul_le c (x.2 y)).trans
        (mul_le_mul_of_nonneg_left (x.2.norm_coe_le_norm y) (norm_nonneg c))
    rw [norm_smul c x.1]
    exact max_le
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg c))
      (h₂.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg c)))

def IsCubeJet (f : ScalarJet (ι := ι) r) : Prop :=
  IsFunctionJet (clamp r) (Metric.ball 0 (r : ℝ)) (r : ℝ)⁻¹ f

noncomputable def coordinateJet (j : ι) : ScalarJet (ι := ι) r :=
  (⟨fun x => x j, continuous_subtype_val.comp (continuous_apply j)⟩,
    ContinuousMap.const _ ((r : ℝ) • ContinuousLinearMap.proj j))

theorem coordinateJet_norm_le (j : ι) : ‖coordinateJet r j‖ ≤ r := by
  have hp : ‖(ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa using norm_le_pi_norm x j
  rw [Prod.norm_def, max_le_iff]
  constructor
  · apply (ContinuousMap.norm_le _ r.coe_nonneg).mpr
    intro x
    exact abs_coordinate_le r x j
  · apply (ContinuousMap.norm_le _ r.coe_nonneg).mpr
    intro x
    change ‖(r : ℝ) • (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ r
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg]
    exact (mul_le_mul_of_nonneg_left hp r.coe_nonneg).trans_eq (mul_one _)

theorem coordinateJet_isCubeJet (hr : 0 < r) (j : ι) : IsCubeJet r (coordinateJet r j) := by
  intro x hx
  have hn : ‖x‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have he : (fun y => ((clamp r y) j : ℝ)) =ᶠ[𝓝 x] (fun y : ι → ℝ => y j) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    have hy' : ‖y‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hy
    exact congrFun (point_clamp_of_norm_le r hy'.le) j
  have hp := (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hr' : (r : ℝ) ≠ 0 := ne_of_gt hr
  change HasFDerivAt (fun y => ((clamp r y) j : ℝ))
    ((r : ℝ)⁻¹ • ((r : ℝ) • (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ))) x
  rw [inv_smul_smul₀ hr']
  exact hp.congr_of_eventuallyEq he

noncomputable def radialJet (i : ι) (t : ℝ) (f : ScalarJet (ι := ι) r) :
    ScalarJet (ι := ι) r := jetPull (radialMap r i t) (radialLinear i t) f

theorem radialJet_norm_le (i : ι) (t : ℝ) (f : ScalarJet (ι := ι) r) :
    ‖radialJet r i t f‖ ≤ ‖f‖ :=
  jetPull_norm_le _ _ (radialLinear_norm_le i t) f

theorem radialJet_isCubeJet (i : ι) (t : ℝ) {f : ScalarJet (ι := ι) r}
    (hf : IsCubeJet r f) : IsCubeJet r (radialJet r i t f) :=
  hf.pull Metric.isOpen_ball _ _ (radialLinear_maps_ball r i t) (fun _ hx => radial_clamp r i t hx)

theorem continuous_radialLinear (i : ι) : Continuous (fun t : ℝ => radialLinear i t) := by
  let p : ℝ → ℝ := fun t => Set.projIcc (0 : ℝ) 1 zero_le_one t
  have hp : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have he : (fun t : ℝ => radialLinear i t) = fun t =>
      p t • ContinuousLinearMap.id ℝ (ι → ℝ) + (1 - p t) • radialLinear i 0 := by
    funext t
    apply ContinuousLinearMap.ext
    intro x
    funext j
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.id_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, radialLinear_apply]
    by_cases hji : j = i
    · simp [hji]; ring
    · simp [hji, p]
  rw [he]
  exact (hp.smul continuous_const).add ((continuous_const.sub hp).smul continuous_const)

theorem continuous_radialJet (i : ι) (f : ScalarJet (ι := ι) r) :
    Continuous (fun t : ℝ => radialJet r i t f) := by
  apply Continuous.prodMk
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact f.1.continuous.comp (continuous_radial r i)
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact (f.2.continuous.comp (continuous_radial r i)).clm_comp
      ((continuous_radialLinear i).comp continuous_fst)

noncomputable def jetKernel (Γ : JetCoefficients (ι := ι) r) (w : JetValues (ι := ι) r)
    (i j : ι) (t : ℝ) : ScalarJet (ι := ι) r :=
  radialJet r i t (jetMul (Γ i j) (w j - w i))

noncomputable def jetIntegralOperator (Γ : JetCoefficients (ι := ι) r)
    (w : JetValues (ι := ι) r) : JetValues (ι := ι) r := fun i =>
  ∑ j, if j = i then 0 else jetMul (coordinateJet r j) (∫ t in (0 : ℝ)..1, jetKernel r Γ w i j t)

theorem jetKernel_integrable (Γ : JetCoefficients (ι := ι) r) (w : JetValues (ι := ι) r)
    (i j : ι) : IntervalIntegrable (jetKernel r Γ w i j) volume 0 1 :=
  (continuous_radialJet r i _).intervalIntegrable 0 1

theorem jetKernel_norm_le (Γ : JetCoefficients (ι := ι) r) (w : JetValues (ι := ι) r)
    (i j : ι) (t : ℝ) : ‖jetKernel r Γ w i j t‖ ≤ 4 * ‖Γ‖ * ‖w‖ := by
  have hΓ : ‖Γ i j‖ ≤ ‖Γ‖ := (norm_le_pi_norm (Γ i) j).trans (norm_le_pi_norm Γ i)
  have hw : ‖w j - w i‖ ≤ 2 * ‖w‖ := by
    have h := (norm_sub_le (w j) (w i)).trans (add_le_add (norm_le_pi_norm w j) (norm_le_pi_norm w i))
    linarith
  calc
    _ ≤ ‖jetMul (Γ i j) (w j - w i)‖ := radialJet_norm_le r i t _
    _ ≤ 2 * ‖Γ i j‖ * ‖w j - w i‖ := jetMul_norm_le _ _
    _ ≤ 2 * ‖Γ‖ * (2 * ‖w‖) := mul_le_mul
      (mul_le_mul_of_nonneg_left hΓ (by norm_num)) hw (norm_nonneg (w j - w i)) (by positivity)
    _ = _ := by ring

theorem jetIntegralOperator_norm_le (Γ : JetCoefficients (ι := ι) r)
    (w : JetValues (ι := ι) r) :
    ‖jetIntegralOperator r Γ w‖ ≤ (8 * Fintype.card ι * (r : ℝ) * ‖Γ‖) * ‖w‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖∑ j, _‖ ≤ _
  calc
    _ ≤ ∑ _j : ι, 8 * (r : ℝ) * ‖Γ‖ * ‖w‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      by_cases hji : j = i
      · simp [hji]; positivity
      · simp only [hji, ite_false]
        have hi : ‖∫ t in (0 : ℝ)..1, jetKernel r Γ w i j t‖ ≤ 4 * ‖Γ‖ * ‖w‖ := by
          simpa using intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
            (fun t _ => jetKernel_norm_le r Γ w i j t)
        calc
          _ ≤ 2 * ‖coordinateJet r j‖ * ‖∫ t in (0 : ℝ)..1, jetKernel r Γ w i j t‖ :=
            jetMul_norm_le _ _
          _ ≤ 2 * (r : ℝ) * (4 * ‖Γ‖ * ‖w‖) := mul_le_mul
            (mul_le_mul_of_nonneg_left (coordinateJet_norm_le r j) (by norm_num))
            hi (norm_nonneg _) (by positivity)
          _ = _ := by ring
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

theorem jetIntegralOperator_preserves (hr : 0 < r) (Γ : JetCoefficients (ι := ι) r)
    (hΓ : ∀ i j, IsCubeJet r (Γ i j)) (w : JetValues (ι := ι) r)
    (hw : ∀ i, IsCubeJet r (w i)) : ∀ i, IsCubeJet r (jetIntegralOperator r Γ w i) := by
  intro i
  let S := functionJets (F := ℝ) (clamp (ι := ι) r) (Metric.ball 0 (r : ℝ)) (r : ℝ)⁻¹
  change (∑ j, if j = i then 0 else jetMul (coordinateJet r j)
    (∫ t in (0 : ℝ)..1, jetKernel r Γ w i j t)) ∈ S
  apply S.sum_mem
  intro j _
  by_cases hji : j = i
  · simp only [hji, ite_true]; exact S.zero_mem
  · simp only [hji, ite_false]
    apply (coordinateJet_isCubeJet r hr j).mul
    apply IsFunctionJet.intervalIntegral Metric.isOpen_ball
    intro t
    apply radialJet_isCubeJet r i t
    apply (hΓ i j).mul
    exact S.sub_mem (hw j) (hw i)

theorem jetKernel_sub (Γ : JetCoefficients (ι := ι) r) (w z : JetValues (ι := ι) r)
    (i j : ι) (t : ℝ) :
    jetKernel r Γ (w - z) i j t = jetKernel r Γ w i j t - jetKernel r Γ z i j t := by
  simp only [jetKernel, Pi.sub_apply]
  have hv : (w j - z j) - (w i - z i) = (w j - w i) - (z j - z i) := by abel
  rw [hv, jetMul_sub]
  exact jetPull_sub _ _ _ _

theorem jetIntegralOperator_sub (Γ : JetCoefficients (ι := ι) r)
    (w z : JetValues (ι := ι) r) :
    jetIntegralOperator r Γ (w - z) = jetIntegralOperator r Γ w - jetIntegralOperator r Γ z := by
  funext i
  change (∑ j : ι, if j = i then 0 else jetMul (coordinateJet r j)
    (∫ t in (0 : ℝ)..1, jetKernel r Γ (w - z) i j t)) =
    (∑ j : ι, if j = i then 0 else jetMul (coordinateJet r j)
      (∫ t in (0 : ℝ)..1, jetKernel r Γ w i j t)) -
    ∑ j : ι, if j = i then 0 else jetMul (coordinateJet r j)
      (∫ t in (0 : ℝ)..1, jetKernel r Γ z i j t)
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · simp [hji]
  · simp only [hji, ite_false, jetKernel_sub]
    rw [intervalIntegral.integral_sub (jetKernel_integrable r Γ w i j)
      (jetKernel_integrable r Γ z i j), jetMul_sub]

theorem jetPicard_contraction (Γ : JetCoefficients (ι := ι) r) (A : JetValues (ι := ι) r)
    (hsmall : 8 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1) :
    ContractingWith ⟨8 * Fintype.card ι * (r : ℝ) * ‖Γ‖, by positivity⟩
      (fun w => A + jetIntegralOperator r Γ w) := by
  refine ⟨hsmall, LipschitzWith.of_dist_le_mul fun w z => ?_⟩
  simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← jetIntegralOperator_sub]
  exact jetIntegralOperator_norm_le r Γ (w - z)

/-- The radial integral equation has a fixed point with actual continuous
derivatives. Compatibility is not yet used in this analytic construction. -/
theorem existsUnique_C1_integralEquation (hr : 0 < r)
    (Γ : JetCoefficients (ι := ι) r) (A : JetValues (ι := ι) r)
    (hΓ : ∀ i j, IsCubeJet r (Γ i j)) (hA : ∀ i, IsCubeJet r (A i))
    (hsmall : 8 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1) :
    ∃! w : JetValues (ι := ι) r,
      A + jetIntegralOperator r Γ w = w ∧ ∀ i, IsCubeJet r (w i) := by
  let T : JetValues (ι := ι) r → JetValues (ι := ι) r := fun w => A + jetIntegralOperator r Γ w
  let hT := jetPicard_contraction r Γ A hsmall
  have hit : ∀ n : ℕ, ∀ i, IsCubeJet r (T^[n] 0 i) := by
    intro n
    induction n with
    | zero =>
        intro i x _
        simpa using (hasFDerivAt_const (0 : ℝ) x)
    | succ n ih =>
        intro i
        rw [Function.iterate_succ_apply']
        exact (functionJets (F := ℝ) (clamp (ι := ι) r) (Metric.ball 0 (r : ℝ)) (r : ℝ)⁻¹).add_mem
          (hA i) (jetIntegralOperator_preserves r hr Γ hΓ _ ih i)
  have hjet : ∀ i, IsCubeJet r (hT.fixedPoint T i) := by
    intro i
    apply (isClosed_isFunctionJet (clamp (ι := ι) r) Metric.isOpen_ball (r : ℝ)⁻¹).mem_of_tendsto
      ((continuous_apply i).tendsto _ |>.comp (hT.tendsto_iterate_fixedPoint 0))
    exact Eventually.of_forall (fun n => hit n i)
  refine ⟨hT.fixedPoint T, ⟨hT.fixedPoint_isFixedPt, hjet⟩, ?_⟩
  intro w hw
  exact hT.fixedPoint_unique hw.1

end SemiHamiltonian.Darboux
