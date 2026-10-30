module

public import SemiHamiltonian.Darboux.C1Operator
public import SemiHamiltonian.Darboux.PairIntegral

/-! C¹ fixed points for the general two-coefficient Darboux integral equation. -/

@[expose] public section

set_option synthInstance.maxSize 1024

open scoped NNReal Topology BigOperators
open MeasureTheory Filter

namespace SemiHamiltonian.Darboux.Pair

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

abbrev JetCoefficients := Darboux.JetCoefficients (ι := ι) r × Darboux.JetCoefficients (ι := ι) r

noncomputable def jetKernel (Γ : JetCoefficients (ι := ι) r) (w : JetValues (ι := ι) r)
    (i j : ι) (t : ℝ) : ScalarJet (ι := ι) r :=
  radialJet r i t (jetMul (Γ.1 i j) (w i) + jetMul (Γ.2 i j) (w j))

noncomputable def jetIntegralOperator (Γ : JetCoefficients (ι := ι) r)
    (w : JetValues (ι := ι) r) : JetValues (ι := ι) r := fun i =>
  ∑ j, if j = i then 0 else jetMul (coordinateJet r j) (∫ t in (0 : ℝ)..1, jetKernel r Γ w i j t)

theorem jetKernel_integrable (Γ : JetCoefficients (ι := ι) r) (w : JetValues (ι := ι) r)
    (i j : ι) : IntervalIntegrable (jetKernel r Γ w i j) volume 0 1 :=
  (continuous_radialJet r i _).intervalIntegrable 0 1

theorem jetKernel_norm_le (Γ : JetCoefficients (ι := ι) r) (w : JetValues (ι := ι) r)
    (i j : ι) (t : ℝ) : ‖jetKernel r Γ w i j t‖ ≤ 4 * ‖Γ‖ * ‖w‖ := by
  have h₁ : ‖Γ.1 i j‖ ≤ ‖Γ‖ :=
    ((norm_le_pi_norm (Γ.1 i) j).trans (norm_le_pi_norm Γ.1 i)).trans (norm_fst_le Γ)
  have h₂ : ‖Γ.2 i j‖ ≤ ‖Γ‖ :=
    ((norm_le_pi_norm (Γ.2 i) j).trans (norm_le_pi_norm Γ.2 i)).trans (norm_snd_le Γ)
  have hterm (c z : ScalarJet (ι := ι) r) (hc : ‖c‖ ≤ ‖Γ‖) (hz : ‖z‖ ≤ ‖w‖) :
      ‖jetMul c z‖ ≤ 2 * ‖Γ‖ * ‖w‖ :=
    (jetMul_norm_le c z).trans (mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num))
      hz (norm_nonneg z) (by positivity))
  exact (radialJet_norm_le r i t _).trans ((norm_add_le _ _).trans
    ((add_le_add (hterm _ _ h₁ (norm_le_pi_norm w i)) (hterm _ _ h₂ (norm_le_pi_norm w j))).trans_eq (by ring)))

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
    (hΓ : ∀ i j, IsCubeJet r (Γ.1 i j) ∧ IsCubeJet r (Γ.2 i j)) (w : JetValues (ι := ι) r)
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
    exact S.add_mem ((hΓ i j).1.mul (hw i)) ((hΓ i j).2.mul (hw j))

theorem jetKernel_sub (Γ : JetCoefficients (ι := ι) r) (w z : JetValues (ι := ι) r)
    (i j : ι) (t : ℝ) :
    jetKernel r Γ (w - z) i j t = jetKernel r Γ w i j t - jetKernel r Γ z i j t := by
  simp only [jetKernel, Pi.sub_apply]
  have hv : jetMul (Γ.1 i j) (w i - z i) + jetMul (Γ.2 i j) (w j - z j) =
      (jetMul (Γ.1 i j) (w i) + jetMul (Γ.2 i j) (w j)) -
        (jetMul (Γ.1 i j) (z i) + jetMul (Γ.2 i j) (z j)) := by
    rw [jetMul_sub, jetMul_sub]
    abel
  rw [hv]
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
    (hΓ : ∀ i j, IsCubeJet r (Γ.1 i j) ∧ IsCubeJet r (Γ.2 i j)) (hA : ∀ i, IsCubeJet r (A i))
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

end SemiHamiltonian.Darboux.Pair
