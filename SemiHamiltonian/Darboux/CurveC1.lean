module

public import SemiHamiltonian.Darboux.CurveProjection

/-! Actual C¹ Darboux solutions with data on the diagonal curve. -/

@[expose] public section

open scoped NNReal Topology Classical
open Set Filter

namespace SemiHamiltonian.Darboux

variable {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

theorem curveJetPicard_contraction (Γ : JetCoefficients (ι := ι) r) (A : JetValues (ι := ι) r)
    (hsmall : 16 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1) :
    ContractingWith ⟨16 * Fintype.card ι * (r : ℝ) * ‖Γ‖, by positivity⟩
      (fun w => A + curveJetOperator r Γ w) := by
  refine ⟨hsmall, LipschitzWith.of_dist_le_mul fun w z => ?_⟩
  simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← curveJetOperator_sub]
  exact curveJetOperator_norm_le r Γ (w - z)

theorem existsUnique_C1_curveIntegralEquation (hr : 0 < r)
    (Γ : JetCoefficients (ι := ι) r) (A : JetValues (ι := ι) r)
    (hΓ : ∀ i j, IsCubeJet r (Γ i j)) (hA : ∀ i, IsCubeJet r (A i))
    (hsmall : 16 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1) :
    ∃! w : JetValues (ι := ι) r,
      A + curveJetOperator r Γ w = w ∧ ∀ i, IsCubeJet r (w i) := by
  let T : JetValues (ι := ι) r → JetValues (ι := ι) r := fun w => A + curveJetOperator r Γ w
  let hT := curveJetPicard_contraction r Γ A hsmall
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
          (hA i) (curveJetOperator_preserves r hr Γ hΓ _ ih i)
  have hjet : ∀ i, IsCubeJet r (hT.fixedPoint T i) := by
    intro i
    apply (isClosed_isFunctionJet (clamp (ι := ι) r) Metric.isOpen_ball (r : ℝ)⁻¹).mem_of_tendsto
      ((continuous_apply i).tendsto _ |>.comp (hT.tendsto_iterate_fixedPoint 0))
    exact Eventually.of_forall (fun n => hit n i)
  exact ⟨hT.fixedPoint T, ⟨hT.fixedPoint_isFixedPt, hjet⟩, fun w hw => hT.fixedPoint_unique hw.1⟩

/-- The curve fixed point is a solution of every PDE, not merely a solution
of its integral equation. The curve is noncharacteristic for every row. -/
theorem exists_C1_darboux_diagonalCurve (hr : 0 < r)
    (Γ : JetCoefficients (ι := ι) r) (A : JetValues (ι := ι) r)
    (hΓ : ∀ i j, IsCubeJet r (Γ i j)) (hA : ∀ i, IsCubeJet r (A i))
    (hcompat : IsDarbouxCompatible r Γ)
    (hAaxis : ∀ (x : Cube ι r) (i j : ι), i ≠ j → jetDiff r x (Pi.single j 1) (A i) = 0)
    (hsmall : 16 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1) :
    ∃ w : JetValues (ι := ι) r,
      (∀ i, IsCubeJet r (w i)) ∧
      (∀ (x : Cube ι r) (i j : ι), i ≠ j →
        jetDiff r x (Pi.single j 1) (w i) = (Γ i j).1 x * ((w j).1 x - (w i).1 x)) ∧
      (∀ (s : Icc (-(r : ℝ)) r) i, (w i).1 (diagonalPoint r s) = (A i).1 (diagonalPoint r s)) ∧
      A + curveJetOperator r Γ w = w := by
  obtain ⟨w, ⟨hfix, hw⟩, _⟩ := existsUnique_C1_curveIntegralEquation r hr Γ A hΓ hA hsmall
  let A' := A - curveJetProjection r (jetIntegralOperator r Γ w)
  have hfix' : A' + jetIntegralOperator r Γ w = w := by
    calc
      _ = A + curveJetOperator r Γ w := by dsimp only [A', curveJetOperator]; abel
      _ = w := hfix
  have hA' (x : Cube ι r) (i j : ι) (hij : i ≠ j) :
      jetDiff r x (Pi.single j 1) (A' i) = 0 := by
    change jetDiff r x (Pi.single j 1) (A i - curveJetProjection r (jetIntegralOperator r Γ w) i) = 0
    rw [map_sub, hAaxis x i j hij, curveJetProjection_offDiagonal r _ x i j hij, sub_self]
  have hs : 4 * Fintype.card ι * (r : ℝ) * ‖coefficientValues r Γ‖ < 1 := by
    have hb := mul_le_mul_of_nonneg_left (coefficientValues_norm_le r Γ)
      (by positivity : 0 ≤ 4 * (Fintype.card ι : ℝ) * (r : ℝ))
    have hp : 0 ≤ 4 * (Fintype.card ι : ℝ) * (r : ℝ) * ‖Γ‖ := by positivity
    nlinarith
  have hz := residual_zero_of_integral_identity r (coefficientValues r Γ) (differentialResidual r Γ w) hs
    (fixedPoint_residual_identity r hr Γ A' w hΓ hw hcompat hA' hfix')
  refine ⟨w, hw, ?_, ?_, hfix⟩
  · intro x i j hij
    have hh := congrArg (fun E : Coefficients (ι := ι) r => E x i j) hz
    simpa only [differentialResidual, ContinuousMap.coe_mk, hij, ite_false,
      ContinuousMap.zero_apply, Pi.zero_apply, sub_eq_zero] using hh
  · intro s i
    have hh := congrArg (fun z : JetValues (ι := ι) r => (z i).1 (diagonalPoint r s)) hfix
    change (A i).1 (diagonalPoint r s) + ((jetIntegralOperator r Γ w i).1 (diagonalPoint r s) -
      (curveJetProjection r (jetIntegralOperator r Γ w) i).1 (diagonalPoint r s)) = _ at hh
    simpa only [curveJetProjection_diagonal, sub_self, add_zero] using hh.symm

end SemiHamiltonian.Darboux
