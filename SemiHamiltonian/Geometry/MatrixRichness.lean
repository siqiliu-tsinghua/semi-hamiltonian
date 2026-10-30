module

public import SemiHamiltonian.Geometry.SymmetryRestriction
public import SemiHamiltonian.Geometry.SymmetryFrame
public import SemiHamiltonian.Geometry.SmoothEigenframe
public import SemiHamiltonian.Geometry.MatrixTorsion

/-! Intrinsic richness means that actual local symmetry operators realize every
value in the pointwise centralizer. No eigenframe or Riemann chart is assumed. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Geometry

open Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {U V : Set (ι → ℝ)} {M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)}

def RealizesCentralizer (hU : IsOpen U) (hM : ContDiffOn ℝ ∞ M U) (p : ι → ℝ) : Prop :=
  ∀ T : (ι → ℝ) →L[ℝ] (ι → ℝ), Function.Commute (M p) T →
    ∃ B : Endomorphism U,
      IsHydrodynamicSymmetry hU (Endomorphism.ofField M hM) B ∧ B.matrix p = T

/-- The neighbourhood is selected before the prescribed centralizer value. -/
def LocallyRichMatrix (hM : ContDiffOn ℝ ∞ M U) : Prop :=
  ∀ p ∈ U, ∃ V, ∃ hV : IsOpen V, ∃ hVU : V ⊆ U,
    p ∈ V ∧ RealizesCentralizer hV (hM.mono hVU) p

theorem RealizesCentralizer.restrict (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (hM : ContDiffOn ℝ ∞ M U) {p : ι → ℝ} (hp : p ∈ V)
    (h : RealizesCentralizer hU hM p) : RealizesCentralizer hV (hM.mono hVU) p := by
  intro T hc
  obtain ⟨B, hB, hval⟩ := h T hc
  refine ⟨B.restrict hVU, ?_, ?_⟩
  · have hh := hB.restrict hU hV hVU
    rw [Endomorphism.restrict_ofField] at hh
    exact hh
  · rw [Endomorphism.restrict_matrix hVU B ⟨p, hp⟩, hval]

theorem LocallyRichMatrix.restrict (hV : IsOpen V) (hVU : V ⊆ U)
    {hM : ContDiffOn ℝ ∞ M U} (h : LocallyRichMatrix hM) :
    LocallyRichMatrix (hM.mono hVU) := by
  intro p hp
  obtain ⟨W, hW, hWU, hpW, hreal⟩ := h p (hVU hp)
  refine ⟨W ∩ V, hW.inter hV, inter_subset_right, ⟨hpW, hp⟩, ?_⟩
  exact hreal.restrict hW (hW.inter hV) inter_subset_left (hM.mono hWU) ⟨hpW, hp⟩

/-- On an eigenframe, intrinsic freedom gives arbitrary diagonal symmetry values. -/
theorem RealizesCentralizer.frame_values (hU : IsOpen U) (hM : ContDiffOn ℝ ∞ M U)
    (b : Frame U) (v : ι → Functions U)
    (heigen : ∀ i, Endomorphism.ofField M hM (b i) = v i • b i)
    (hgap : ∀ i j, i ≠ j → IsUnit (v i - v j)) (p : U)
    (h : RealizesCentralizer hU hM p) (a : ι → ℝ) :
    ∃ w : ι → Functions U, (b.data hU).IsHydrodynamicSymmetry v w ∧
      ∀ i, w i p = a i := by
  let A := Endomorphism.ofField M hM
  let c : ι → Functions U := fun i => algebraMap ℝ (Functions U) (a i)
  let C := b.diagonalEndomorphism c
  have hc : Function.Commute (M p) (C.matrix p) := by
    have hh := (Endomorphism.commute_iff_matrix A C).mp
      (b.commute_diagonalEndomorphism A v c heigen) p
    rwa [Endomorphism.matrix_ofField] at hh
  obtain ⟨B, hB, hval⟩ := h (C.matrix p) hc
  let w := fun i => b.equivFun (B (b i)) i
  have heB : ∀ i, B (b i) = w i • b i := b.eigen_of_commute A B v heigen hgap hB.1
  refine ⟨w, b.symmetry_coordinates hU A B v w heigen heB hB, ?_⟩
  intro i
  change b.equivFun (B (b i)) i p = a i
  rw [← b.dual_field, ← B.matrix_field, hval, C.matrix_field, b.dual_field]
  rw [b.diagonalEndomorphism_eigen, map_smul]
  simp [c, Algebra.algebraMap_eq_smul_one]

theorem RealizesCentralizer.haantjes_zero_at (hU : IsOpen U) (hM : ContDiffOn ℝ ∞ M U)
    (b : Frame U) (v : ι → Functions U)
    (heigen : ∀ i, Endomorphism.ofField M hM (b i) = v i • b i)
    (hgap : ∀ i j, i ≠ j → IsUnit (v i - v j)) (p : U)
    (h : RealizesCentralizer hU hM p) :
    ∀ x y, matrixHaantjes M p x y = 0 := by
  have hcoeff (r i j : ι) (hri : r ≠ i) (hrj : r ≠ j) (hij : i ≠ j) :
      (b.data hU).structureCoeff r i j p = 0 := by
    obtain ⟨w, hw, hv⟩ := h.frame_values hU hM b v heigen hgap p
      (fun k => if k = r then 1 else 0)
    have hz := congrArg (eval p)
      ((b.data hU).symmetryValuesAdmissible_of_symmetry v w hw r i j hri hrj hij)
    simp only [map_mul, map_add, map_sub, map_zero] at hz
    change _ = (0 : ℝ) at hz
    change (b.data hU).structureCoeff r i j p *
      ((v i p - v j p) * w r p + (v j p - v r p) * w i p +
        (v r p - v i p) * w j p) = 0 at hz
    rw [hv r, hv i, hv j] at hz
    simp only [ite_true, Ne.symm hri, Ne.symm hrj, ite_false,
      mul_one, mul_zero, add_zero] at hz
    have hu : IsUnit (v i p - v j p) := by
      change IsUnit (eval p (v i - v j))
      exact (hgap i j hij).map (eval p)
    exact hu.mul_right_cancel (by simpa only [zero_mul] using hz)
  let A := Endomorphism.ofField M hM
  have hb (i j : ι) : field (haantjes hU A (b i) (b j)) p = 0 := by
    apply b.dual_separates p
    intro r
    rw [b.dual_field, b.haantjes_basis_coordinates hU A v heigen]
    change eval p ((v i - v r) ^ 2 * (v j - v r) ^ 2 * (b.data hU).structureCoeff r i j) = 0
    simp only [map_mul, map_pow, map_sub]
    by_cases hri : r = i
    · subst r; simp
    by_cases hrj : r = j
    · subst r; simp
    by_cases hij : i = j
    · subst j; simp only [(b.data hU).self, map_zero, mul_zero]
    · change _ * (b.data hU).structureCoeff r i j p = 0
      rw [hcoeff r i j hri hrj hij, mul_zero]
  have hfield (X Y : Fields U) : field (haantjes hU A X Y) p = 0 := by
    rw [← b.sum_equivFun X, ← b.sum_equivFun Y, haantjes_sum_left]
    simp_rw [haantjes_sum_right, haantjes_smul_left, haantjes_smul_right]
    funext k
    have hb' (i j : ι) : haantjes hU A (b i) (b j) k p = 0 := by
      simpa only [field_apply, Pi.zero_apply] using congrFun (hb i j) k
    simp [field_apply, hb']
  intro x y
  have hh := hfield (constantField x) (constantField y)
  rwa [haantjes_ofField_eval hU hM, field_constantField, field_constantField] at hh

/-- Actual local symmetry richness forces Haantjes vanishing. -/
theorem LocallyRichMatrix.haantjesVanish
    {hM : ContDiffOn ℝ ∞ M U} (h : LocallyRichMatrix hM)
    (hs : ∀ p ∈ U, StrictHyperbolicAt M p) : MatrixHaantjesVanish M U := by
  intro p hp
  obtain ⟨W, hW, hWU, hpW, hreal⟩ := h p hp
  obtain ⟨V, hVW, b, v, hV, hpV, heigen, hgap⟩ :=
    exists_smooth_eigenframe hW (hM.mono hWU) hpW (hs p hp)
  have hrealV := hreal.restrict hW hV hVW (hM.mono hWU) hpV
  exact hrealV.haantjes_zero_at hV ((hM.mono hWU).mono hVW) b v heigen hgap ⟨p, hpV⟩

end SemiHamiltonian.Geometry
