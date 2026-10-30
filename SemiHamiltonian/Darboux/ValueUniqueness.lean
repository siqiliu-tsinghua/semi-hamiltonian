module

public import SemiHamiltonian.Darboux.Existence

/-! Uniqueness of the actual C¹ solution values, including their axis data. -/

@[expose] public section

open scoped NNReal BigOperators
open MeasureTheory

namespace SemiHamiltonian.Darboux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

noncomputable def valuesOfJets (w : JetValues (ι := ι) r) : Values (ι := ι) r :=
  ⟨fun x i => (w i).1 x, continuous_pi fun i => (w i).1.continuous⟩

theorem jetFixedPoint_axis (Γ : JetCoefficients (ι := ι) r) (A w : JetValues (ι := ι) r)
    (hfix : A + jetIntegralOperator r Γ w = w) (i : ι) (x : Cube ι r) :
    (w i).1 (axis r i x) = (A i).1 (axis r i x) := by
  have h := congrArg (fun v : JetValues (ι := ι) r => jetEval r (axis r i x) (v i)) hfix
  change jetEval r (axis r i x) (A i + jetIntegralOperator r Γ w i) = _ at h
  rw [map_add] at h
  have hz : jetEval r (axis r i x) (jetIntegralOperator r Γ w i) = 0 := by
    rw [jetIntegralOperator, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hji : j = i
    · simp [hji]
    · simp only [hji, ite_false, jetEval_apply]
      change (axis r i x j : ℝ) * _ = 0
      rw [axis_other r i j hji x, zero_mul]
  rw [hz, add_zero] at h
  exact h.symm

theorem cubeJet_fixedPoint (hr : 0 < r) (Γ : JetCoefficients (ι := ι) r)
    (φ : AxisData (ι := ι) r) (w : JetValues (ι := ι) r)
    (hw : ∀ i, IsCubeJet r (w i))
    (hPDE : ∀ (x : Cube ι r) (i j : ι), i ≠ j →
      jetDiff r x (Pi.single j 1) (w i) = (Γ i j).1 x * ((w j).1 x - (w i).1 x))
    (haxis : ∀ i x, (w i).1 (axis r i x) = φ i (x i)) :
    picard r (coefficientValues r Γ) φ (valuesOfJets r w) = valuesOfJets r w := by
  apply continuousMap_eq_of_interior r hr
  intro x hx
  funext i
  let W : (ι → ℝ) → ℝ := fun y => (w i).1 (clamp r y)
  let g : ℝ → ℝ := fun t => ∑ j, if j = i then 0 else
    (x j : ℝ) * kernel r (coefficientValues r Γ) (valuesOfJets r w) i j x t
  have hint : IntervalIntegrable g volume 0 1 := by
    have hc : Continuous g := by
      apply continuous_finsetSum
      intro j _
      by_cases hji : j = i
      · simp only [hji, ite_true]; exact continuous_const
      · simp only [hji, ite_false]
        exact continuous_const.mul
          ((continuous_kernel r _ _ i j).comp (continuous_const.prodMk continuous_id))
    exact hc.intervalIntegrable 0 1
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => W (affineRadial r i x s)) (g t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
    have hy : point r (radial r i t x) ∈ Metric.ball 0 (r : ℝ) := by
      rw [point_radialLinear]
      exact radialLinear_maps_ball r i t hx
    have hfd := hw i (point r (radial r i t x)) hy
    rw [clamp_point, point_radial r i x t ht'] at hfd
    have hc := hfd.comp_hasDerivAt t (hasDerivAt_affineRadial r i x t)
    have he : ((r : ℝ)⁻¹ • (w i).2 (radial r i t x)) (transverse r i x) = g t := by
      rw [linearMap_transverse]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · simp [hji]
      · simp only [hji, ite_false]
        change (x j : ℝ) * jetDiff r (radial r i t x) (Pi.single j 1) (w i) = _
        rw [hPDE _ i j (Ne.symm hji)]
        rfl
    change HasDerivAt (fun s => W (affineRadial r i x s))
      (((r : ℝ)⁻¹ • (w i).2 (radial r i t x)) (transverse r i x)) t at hc
    simpa only [he] using hc
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  have hend : W (affineRadial r i x 1) = (w i).1 x := by
    rw [← point_radial r i x 1 (by constructor <;> norm_num), radial_one]
    simp only [W, clamp_point]
  have hstart : W (affineRadial r i x 0) = φ i (x i) := by
    rw [← point_radial r i x 0 (by constructor <;> norm_num)]
    simp only [W, clamp_point]
    exact haxis i x
  rw [hend, hstart] at hFTC
  have hsum : (∫ t in (0 : ℝ)..1, g t) =
      integralOperator r (coefficientValues r Γ) (valuesOfJets r w) x i := by
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · simp [hji]
      · simp [hji, intervalIntegral.integral_const_mul]
    · intro j _
      by_cases hji : j = i
      · simp only [hji, ite_true]; exact intervalIntegrable_const
      · simp only [hji, ite_false]
        exact (kernel_integrable r _ _ i j x).const_mul _
  rw [hsum] at hFTC
  change φ i (x i) + integralOperator r (coefficientValues r Γ) (valuesOfJets r w) x i = (w i).1 x
  linarith

def IsC1DarbouxSolution (Γ : JetCoefficients (ι := ι) r) (φ : AxisData (ι := ι) r)
    (u : Values (ι := ι) r) : Prop :=
  ∃ w : JetValues (ι := ι) r, valuesOfJets r w = u ∧
    (∀ i, IsCubeJet r (w i)) ∧
    (∀ (x : Cube ι r) (i j : ι), i ≠ j →
      jetDiff r x (Pi.single j 1) (w i) = (Γ i j).1 x * ((w j).1 x - (w i).1 x)) ∧
    (∀ i x, (w i).1 (axis r i x) = φ i (x i))

theorem C1DarbouxSolution_unique (hr : 0 < r) (Γ : JetCoefficients (ι := ι) r)
    (φ : AxisData (ι := ι) r)
    (hsmall : 2 * Fintype.card ι * (r : ℝ) * ‖coefficientValues r Γ‖ < 1)
    {u v : Values (ι := ι) r}
    (hu : IsC1DarbouxSolution r Γ φ u) (hv : IsC1DarbouxSolution r Γ φ v) : u = v := by
  obtain ⟨w, rfl, hw, hpw, haw⟩ := hu
  obtain ⟨z, rfl, hz, hpz, haz⟩ := hv
  exact (picard_contraction r _ φ hsmall).fixedPoint_unique'
    (cubeJet_fixedPoint r hr Γ φ w hw hpw haw) (cubeJet_fixedPoint r hr Γ φ z hz hpz haz)

/-- Darboux existence and uniqueness of actual C¹ solution values with arbitrary
axis data possessing a C¹ extension constant in the transverse coordinates. -/
theorem existsUnique_C1_darboux (hr : 0 < r)
    (Γ : JetCoefficients (ι := ι) r) (φ : AxisData (ι := ι) r) (A : JetValues (ι := ι) r)
    (hΓ : ∀ i j, IsCubeJet r (Γ i j)) (hA : ∀ i, IsCubeJet r (A i))
    (hcompat : IsDarbouxCompatible r Γ)
    (hAaxis : ∀ (x : Cube ι r) (i j : ι), i ≠ j → jetDiff r x (Pi.single j 1) (A i) = 0)
    (hAtrace : ∀ i x, (A i).1 (axis r i x) = φ i (x i))
    (hsmall : 8 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1) :
    ∃! u : Values (ι := ι) r, IsC1DarbouxSolution r Γ φ u := by
  obtain ⟨w, hw, hpw, hfix⟩ := exists_C1_darboux r hr Γ A hΓ hA hcompat hAaxis hsmall
  have haw : ∀ i x, (w i).1 (axis r i x) = φ i (x i) := by
    intro i x
    rw [jetFixedPoint_axis r Γ A w hfix, hAtrace]
  have hu : IsC1DarbouxSolution r Γ φ (valuesOfJets r w) := ⟨w, rfl, hw, hpw, haw⟩
  refine ⟨valuesOfJets r w, hu, fun v hv => ?_⟩
  apply C1DarbouxSolution_unique r hr Γ φ _ hv hu
  have hb := mul_le_mul_of_nonneg_left (coefficientValues_norm_le r Γ)
    (by positivity : 0 ≤ 2 * (Fintype.card ι : ℝ) * (r : ℝ))
  have hp : 0 ≤ 2 * (Fintype.card ι : ℝ) * (r : ℝ) * ‖Γ‖ := by positivity
  nlinarith

end SemiHamiltonian.Darboux
