module

public import SemiHamiltonian.Darboux.Uniqueness

/-! Choosing a positive radius for the radial integral equation and classical uniqueness. -/

@[expose] public section

open scoped NNReal

namespace SemiHamiltonian.Darboux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r R : ℝ≥0}

def cubeInclusion (hr : r ≤ R) : C(Cube ι r, Cube ι R) where
  toFun x i := ⟨x i, by
    have h := (x i).property
    have hr' : (r : ℝ) ≤ R := hr
    constructor <;> linarith [h.1, h.2]⟩
  continuous_toFun := continuous_pi fun i =>
    (continuous_subtype_val.comp (continuous_apply i)).subtype_mk _

noncomputable def restrictCoefficients (Γ : Coefficients (ι := ι) R) (hr : r ≤ R) :
    Coefficients (ι := ι) r := Γ.comp (cubeInclusion hr)

omit [DecidableEq ι] in
theorem restrictCoefficients_norm_le (Γ : Coefficients (ι := ι) R) (hr : r ≤ R) :
    ‖restrictCoefficients Γ hr‖ ≤ ‖Γ‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  exact Γ.norm_coe_le_norm _

/-- The required small cube always has positive radius; the radius does not
depend on the prescribed axis data. -/
theorem exists_positive_contraction_radius (hR : 0 < R)
    (Γ : Coefficients (ι := ι) R) :
    ∃ (r : ℝ≥0) (hr : r ≤ R), 0 < r ∧
      2 * Fintype.card ι * (r : ℝ) * ‖restrictCoefficients Γ hr‖ < 1 := by
  obtain ⟨ε, hε, hεsmall⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1)
    (2 * Fintype.card ι * ‖Γ‖)
  let r : ℝ≥0 := min R ⟨ε, hε.le⟩
  have hr : r ≤ R := min_le_left _ _
  have hrε : (r : ℝ) ≤ ε := min_le_right (R : ℝ) ε
  refine ⟨r, hr, lt_min hR hε, ?_⟩
  calc
    _ ≤ 2 * Fintype.card ι * (r : ℝ) * ‖Γ‖ :=
      mul_le_mul_of_nonneg_left (restrictCoefficients_norm_le Γ hr) (by positivity)
    _ ≤ ε * (2 * Fintype.card ι * ‖Γ‖) := by
      nlinarith [mul_le_mul_of_nonneg_right hrε
        (by positivity : 0 ≤ 2 * (Fintype.card ι : ℝ) * ‖Γ‖)]
    _ < 1 := by simpa [mul_comm] using hεsmall

/-- Continuous integral-equation existence and classical PDE uniqueness on a
single positive cube, uniformly for all axis data on that cube.

The first conclusion is deliberately an integral equation, not PDE existence.
-/
theorem local_integral_existence_and_classical_uniqueness (hR : 0 < R)
    (Γ : Coefficients (ι := ι) R) :
    ∃ (r : ℝ≥0) (hr : r ≤ R), 0 < r ∧
      ∀ φ : AxisData (ι := ι) r,
        (∃! w : Values (ι := ι) r, picard r (restrictCoefficients Γ hr) φ w = w) ∧
        (∀ w z : Values (ι := ι) r,
          IsClassicalSolution r (restrictCoefficients Γ hr) φ w →
          IsClassicalSolution r (restrictCoefficients Γ hr) φ z → w = z) := by
  obtain ⟨r, hr, hrpos, hsmall⟩ := exists_positive_contraction_radius hR Γ
  refine ⟨r, hr, hrpos, fun φ => ⟨?_, ?_⟩⟩
  · exact existsUnique_integralEquation r _ φ hsmall
  · intro w z hw hz
    exact classicalSolution_unique r _ φ hsmall hw hz

end SemiHamiltonian.Darboux
