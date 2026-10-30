module

public import SemiHamiltonian.Darboux.Existence
public import SemiHamiltonian.Darboux.SmoothLinear

/-! Projection onto data on the diagonal curve. Subtracting the projection
of the usual integral operator replaces axis data by diagonal-curve data. -/

@[expose] public section

open scoped NNReal Topology Classical
open Set Filter

namespace SemiHamiltonian.Darboux

variable {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

def diagonalPoint (s : Icc (-(r : ℝ)) r) : Cube ι r := fun _ => s

def diagonalSection (i : ι) : C(Cube ι r, Cube ι r) :=
  ⟨fun x => diagonalPoint r (x i), continuous_pi fun _ => continuous_apply i⟩

noncomputable def diagonalLinear (i : ι) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.proj i)

@[simp] theorem diagonalLinear_apply (i : ι) (x : ι → ℝ) (j : ι) :
    diagonalLinear (ι := ι) i x j = x i := rfl

theorem diagonalLinear_norm_le (i : ι) : ‖diagonalLinear (ι := ι) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro j
  exact norm_le_pi_norm x i

theorem diagonalLinear_maps_ball (i : ι) :
    MapsTo (diagonalLinear (ι := ι) i) (Metric.ball 0 (r : ℝ)) (Metric.ball 0 (r : ℝ)) := by
  intro x hx
  have hn : ‖x‖ < r := by simpa using hx
  have hb := (ContinuousLinearMap.le_opNorm (diagonalLinear (ι := ι) i) x).trans
    (mul_le_mul_of_nonneg_right (diagonalLinear_norm_le i) (norm_nonneg x))
  rw [one_mul] at hb
  simpa only [Metric.mem_ball, dist_zero_right] using hb.trans_lt hn

theorem diagonalSection_clamp (i : ι) (x : ι → ℝ) :
    diagonalSection r i (clamp r x) = clamp r (diagonalLinear i x) := rfl

noncomputable def curveJetProjection (w : JetValues (ι := ι) r) : JetValues (ι := ι) r :=
  fun i => jetPull (diagonalSection r i) (diagonalLinear i) (w i)

theorem curveJetProjection_sub (w z : JetValues (ι := ι) r) :
    curveJetProjection r (w - z) = curveJetProjection r w - curveJetProjection r z := by
  funext i
  exact jetPull_sub _ _ _ _

theorem curveJetProjection_norm_le (w : JetValues (ι := ι) r) :
    ‖curveJetProjection r w‖ ≤ ‖w‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
  intro i
  exact (jetPull_norm_le _ _ (diagonalLinear_norm_le i) _).trans (norm_le_pi_norm w i)

theorem curveJetProjection_preserves (w : JetValues (ι := ι) r)
    (hw : ∀ i, IsCubeJet r (w i)) : ∀ i, IsCubeJet r (curveJetProjection r w i) := by
  intro i
  exact (hw i).pull Metric.isOpen_ball _ _ (diagonalLinear_maps_ball r i)
    (fun x _ => diagonalSection_clamp r i x)

theorem curveJetProjection_offDiagonal (w : JetValues (ι := ι) r)
    (x : Cube ι r) (i j : ι) (hij : i ≠ j) :
    jetDiff r x (Pi.single j 1) (curveJetProjection r w i) = 0 := by
  have hz : diagonalLinear (ι := ι) i (Pi.single j 1) = 0 := by
    ext k
    simp [hij.symm]
  change (r : ℝ)⁻¹ * (w i).2 (diagonalSection r i x) (diagonalLinear i (Pi.single j 1)) = 0
  rw [hz, map_zero, mul_zero]

@[simp] theorem curveJetProjection_diagonal (w : JetValues (ι := ι) r)
    (s : Icc (-(r : ℝ)) r) (i : ι) :
    (curveJetProjection r w i).1 (diagonalPoint r s) = (w i).1 (diagonalPoint r s) := rfl

noncomputable def curveJetOperator (Γ : JetCoefficients (ι := ι) r)
    (w : JetValues (ι := ι) r) : JetValues (ι := ι) r :=
  jetIntegralOperator r Γ w - curveJetProjection r (jetIntegralOperator r Γ w)

theorem curveJetOperator_sub (Γ : JetCoefficients (ι := ι) r) (w z : JetValues (ι := ι) r) :
    curveJetOperator r Γ (w - z) = curveJetOperator r Γ w - curveJetOperator r Γ z := by
  simp only [curveJetOperator, jetIntegralOperator_sub, curveJetProjection_sub]
  abel

theorem curveJetOperator_norm_le (Γ : JetCoefficients (ι := ι) r) (w : JetValues (ι := ι) r) :
    ‖curveJetOperator r Γ w‖ ≤ (16 * Fintype.card ι * (r : ℝ) * ‖Γ‖) * ‖w‖ := by
  have hn := norm_sub_le (jetIntegralOperator r Γ w) (curveJetProjection r (jetIntegralOperator r Γ w))
  have hp := curveJetProjection_norm_le r (jetIntegralOperator r Γ w)
  have ht := jetIntegralOperator_norm_le r Γ w
  dsimp only [curveJetOperator]
  nlinarith

theorem curveJetOperator_preserves (hr : 0 < r) (Γ : JetCoefficients (ι := ι) r)
    (hΓ : ∀ i j, IsCubeJet r (Γ i j)) (w : JetValues (ι := ι) r)
    (hw : ∀ i, IsCubeJet r (w i)) : ∀ i, IsCubeJet r (curveJetOperator r Γ w i) := by
  have ht := jetIntegralOperator_preserves r hr Γ hΓ w hw
  intro i
  exact (functionJets (F := ℝ) (clamp (ι := ι) r) (Metric.ball 0 (r : ℝ)) (r : ℝ)⁻¹).sub_mem
    (ht i) (curveJetProjection_preserves r _ ht i)

noncomputable def curveProjection : Values (ι := ι) r →L[ℝ] Values (ι := ι) r :=
  LinearMap.mkContinuous
    ({ toFun := fun w => ⟨fun x i => w (diagonalSection r i x) i,
         continuous_pi fun i => (continuous_apply i).comp (w.continuous.comp (diagonalSection r i).continuous)⟩
       map_add' := by intros; rfl
       map_smul' := by intros; rfl } : Values (ι := ι) r →ₗ[ℝ] Values (ι := ι) r)
    1 (by
      intro w
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg w)).mpr
      intro x
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
      intro i
      exact component_le_norm r w _ i)

theorem curveProjection_norm_le : ‖curveProjection (ι := ι) r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  simp only [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg w)).mpr
  intro x
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
  intro i
  exact component_le_norm r w _ i

noncomputable def curveOperator (Γ : Coefficients (ι := ι) r) :
    Values (ι := ι) r →L[ℝ] Values (ι := ι) r :=
  integralOperatorCLM r Γ - (curveProjection r).comp (integralOperatorCLM r Γ)

theorem curveOperator_norm_le (Γ : Coefficients (ι := ι) r) :
    ‖curveOperator r Γ‖ ≤ 4 * Fintype.card ι * (r : ℝ) * ‖Γ‖ := by
  have hn := norm_sub_le (integralOperatorCLM r Γ) ((curveProjection r).comp (integralOperatorCLM r Γ))
  have hp := ContinuousLinearMap.opNorm_comp_le (curveProjection r) (integralOperatorCLM r Γ)
  have hq := mul_le_mul_of_nonneg_right (curveProjection_norm_le (ι := ι) r)
    (norm_nonneg (integralOperatorCLM r Γ))
  have ht := integralOperatorCLM_norm_le r Γ
  dsimp only [curveOperator]
  nlinarith

end SemiHamiltonian.Darboux
