module

public import SemiHamiltonian.Darboux.Homotopy
public import SemiHamiltonian.Darboux.Residual
public import SemiHamiltonian.Darboux.Interior

/-! C¹ existence for the compatible linear Darboux system on a small cube. -/

@[expose] public section

open scoped NNReal BigOperators

namespace SemiHamiltonian.Darboux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

noncomputable def coefficientValues (Γ : JetCoefficients (ι := ι) r) : Coefficients (ι := ι) r :=
  ⟨fun x i j => (Γ i j).1 x, continuous_pi fun i => continuous_pi fun j => (Γ i j).1.continuous⟩

def IsDarbouxCompatible (Γ : JetCoefficients (ι := ι) r) : Prop :=
  ∀ (x : Cube ι r) (i j k : ι), i ≠ j → i ≠ k → j ≠ k →
    jetDiff r x (Pi.single k 1) (Γ i j) =
      (Γ i j).1 x * (Γ j k).1 x + (Γ i k).1 x * (Γ k j).1 x - (Γ i j).1 x * (Γ i k).1 x

noncomputable def differentialResidual (Γ : JetCoefficients (ι := ι) r)
    (w : JetValues (ι := ι) r) : Coefficients (ι := ι) r where
  toFun x i j := if i = j then 0 else jetDiff r x (Pi.single j 1) (w i) -
    (Γ i j).1 x * ((w j).1 x - (w i).1 x)
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hij : i = j
    · simp only [hij, ite_true]; exact continuous_const
    · simp only [hij, ite_false, jetDiff_apply]
      fun_prop

noncomputable def rowForm (Γ : JetCoefficients (ι := ι) r)
    (w : JetValues (ι := ι) r) (i : ι) : JetValues (ι := ι) r :=
  fun j => jetMul (Γ i j) (w j - w i)

theorem rowForm_curl (Γ : JetCoefficients (ι := ι) r) (hΓ : IsDarbouxCompatible r Γ)
    (w : JetValues (ι := ι) r) (x : Cube ι r) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    jetDiff r x (Pi.single j 1) (rowForm r Γ w i k) -
      jetDiff r x (Pi.single k 1) (rowForm r Γ w i j) =
    (Γ i k).1 x * (differentialResidual r Γ w x k j - differentialResidual r Γ w x i j) -
      (Γ i j).1 x * (differentialResidual r Γ w x j k - differentialResidual r Γ w x i k) := by
  have h := residual_curl_identity (fun a b => (Γ a b).1 x)
    (fun a b => jetDiff r x (Pi.single b 1) (w a)) (fun a => (w a).1 x) i j k
    _ _ (hΓ x i k j hik hij (Ne.symm hjk)) (hΓ x i j k hij hik hjk)
  simp only [rowForm, jetDiff_mul, map_sub, Prod.fst_sub, ContinuousMap.sub_apply,
    differentialResidual, ContinuousMap.coe_mk, hij, hik, hjk, Ne.symm hjk, ite_false]
  linarith [h]

omit [DecidableEq ι] in
theorem coefficientValues_norm_le (Γ : JetCoefficients (ι := ι) r) :
    ‖coefficientValues r Γ‖ ≤ ‖Γ‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg Γ)).mpr
  intro x
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg Γ)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg Γ)).mpr
  intro j
  exact ((Γ i j).1.norm_coe_le_norm x).trans ((norm_fst_le (Γ i j)).trans
    ((norm_le_pi_norm (Γ i) j).trans (norm_le_pi_norm Γ i)))

theorem fixedPoint_residual_identity (hr : 0 < r)
    (Γ : JetCoefficients (ι := ι) r) (A w : JetValues (ι := ι) r)
    (hΓ : ∀ i j, IsCubeJet r (Γ i j)) (hw : ∀ i, IsCubeJet r (w i))
    (hcompat : IsDarbouxCompatible r Γ)
    (hA : ∀ (x : Cube ι r) (i j : ι), i ≠ j → jetDiff r x (Pi.single j 1) (A i) = 0)
    (hfix : A + jetIntegralOperator r Γ w = w) :
    residualOperator r (coefficientValues r Γ) (differentialResidual r Γ w) = differentialResidual r Γ w := by
  apply continuousMap_eq_of_interior r hr
  intro x hx
  funext i j
  by_cases hij : i = j
  · simp [residualOperator, differentialResidual, hij]
  · have hF : IsCubeJet r (rowForm r Γ w i j) :=
      (hΓ i j).mul ((functionJets (F := ℝ) (clamp (ι := ι) r)
        (Metric.ball 0 (r : ℝ)) (r : ℝ)⁻¹).sub_mem (hw j) (hw i))
    have hderiv : jetDiff r x (Pi.single j 1) (w i) =
        jetDiff r x (Pi.single j 1) (rowHomotopy r i (rowForm r Γ w i)) := by
      conv_lhs => rw [← hfix]
      change jetDiff r x (Pi.single j 1) (A i + jetIntegralOperator r Γ w i) = _
      rw [map_add, hA x i j hij, zero_add]
      rfl
    have hhom := rowHomotopy_defect r hr i j (Ne.symm hij) (rowForm r Γ w i) hF x hx
    simp only [residualOperator, ContinuousMap.coe_mk, hij, ite_false]
    change (∑ k, if k = i ∨ k = j then 0 else (x k : ℝ) *
      ∫ t in (0 : ℝ)..1, residualKernel r (coefficientValues r Γ) (differentialResidual r Γ w) i j k x t) = _
    have hval : differentialResidual r Γ w x i j =
        jetDiff r x (Pi.single j 1) (rowHomotopy r i (rowForm r Γ w i)) - (rowForm r Γ w i j).1 x := by
      simp only [differentialResidual, ContinuousMap.coe_mk, hij, ite_false, rowForm,
        jetMul, Prod.fst_sub, ContinuousMap.mul_apply, ContinuousMap.sub_apply]
      rw [hderiv]
    rw [hval, hhom]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = i ∨ k = j
    · simp [hk]
    · simp only [hk, ite_false]
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [rowForm_curl r Γ hcompat w (radial r i t x) i j k hij
        (fun h => hk (Or.inl h.symm)) (fun h => hk (Or.inr h.symm))]
      rfl

/-- A genuine C¹ solution of all the Darboux PDEs exists when the coefficients
are compatible and the cube is small enough. `A i` is any C¹ initial extension
constant in coordinates other than `i`.

The derivative asserted by `IsCubeJet` is a mathlib `HasFDerivAt`, not a formal
derivation or an assumed differentiability of a continuous fixed point. -/
theorem exists_C1_darboux (hr : 0 < r)
    (Γ : JetCoefficients (ι := ι) r) (A : JetValues (ι := ι) r)
    (hΓ : ∀ i j, IsCubeJet r (Γ i j)) (hA : ∀ i, IsCubeJet r (A i))
    (hcompat : IsDarbouxCompatible r Γ)
    (hAaxis : ∀ (x : Cube ι r) (i j : ι), i ≠ j → jetDiff r x (Pi.single j 1) (A i) = 0)
    (hsmall : 8 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1) :
    ∃ w : JetValues (ι := ι) r,
      (∀ i, IsCubeJet r (w i)) ∧
      (∀ (x : Cube ι r) (i j : ι), i ≠ j →
        jetDiff r x (Pi.single j 1) (w i) = (Γ i j).1 x * ((w j).1 x - (w i).1 x)) ∧
      A + jetIntegralOperator r Γ w = w := by
  obtain ⟨w, ⟨hfix, hw⟩, _⟩ := existsUnique_C1_integralEquation r hr Γ A hΓ hA hsmall
  have hs : 4 * Fintype.card ι * (r : ℝ) * ‖coefficientValues r Γ‖ < 1 := by
    have hb := mul_le_mul_of_nonneg_left (coefficientValues_norm_le r Γ)
      (by positivity : 0 ≤ 4 * (Fintype.card ι : ℝ) * (r : ℝ))
    have hp : 0 ≤ 4 * (Fintype.card ι : ℝ) * (r : ℝ) * ‖Γ‖ := by positivity
    nlinarith
  have hz := residual_zero_of_integral_identity r (coefficientValues r Γ) (differentialResidual r Γ w) hs
    (fixedPoint_residual_identity r hr Γ A w hΓ hw hcompat hAaxis hfix)
  refine ⟨w, hw, ?_, hfix⟩
  intro x i j hij
  have h := congrArg (fun E : Coefficients (ι := ι) r => E x i j) hz
  simpa only [differentialResidual, ContinuousMap.coe_mk, hij, ite_false,
    ContinuousMap.zero_apply, Pi.zero_apply, sub_eq_zero] using h

end SemiHamiltonian.Darboux
