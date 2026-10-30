module

public import SemiHamiltonian.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The eigenframe calculation of Pavlov--Sharipov--Svinolupov

The bracket is calculated from frame derivatives and structure coefficients.
The results below are algebraic identities in these data; their interpretation as
vector fields on a manifold, and the construction of Riemann coordinates, are
separate geometric steps.
-/

@[expose] public section

namespace SemiHamiltonian.PSS

variable (𝕜 R ι : Type*) [CommRing 𝕜] [CommRing R] [Algebra 𝕜 R]

/-- Data needed to calculate vector-field brackets in a frame. The index order of
`structureCoeff r i j` is output index, first input, second input. -/
structure FrameData where
  deriv : ι → Derivation 𝕜 R R
  structureCoeff : ι → ι → ι → R
  self : ∀ r i, structureCoeff r i i = 0
  skew : ∀ r i j, structureCoeff r i j = -structureCoeff r j i

variable {𝕜 R ι} [Fintype ι] [DecidableEq ι]

namespace FrameData

variable (F : FrameData 𝕜 R ι)

def scaledBasis (i : ι) (a : R) : ι → R := fun r => if r = i then a else 0

def applyDiagonal (v X : ι → R) : ι → R := fun r => v r * X r

/-- Lie-bracket formula in a frame, expressed using its structure coefficients. -/
def bracket (X Y : ι → R) (r : ι) : R :=
  (∑ p, (X p * F.deriv p (Y r) - Y p * F.deriv p (X r))) +
    ∑ p, ∑ q, X p * Y q * F.structureCoeff r p q

omit [Fintype ι] in
theorem applyDiagonal_scaledBasis (v : ι → R) (i : ι) (a : R) :
    applyDiagonal v (scaledBasis i a) = scaledBasis i (v i * a) := by
  funext r
  by_cases h : r = i
  · subst r; simp [applyDiagonal, scaledBasis]
  · simp [applyDiagonal, scaledBasis, h]

theorem bracket_scaledBasis (i j r : ι) (a b : R) :
    F.bracket (scaledBasis i a) (scaledBasis j b) r =
      (if r = j then a * F.deriv i b else 0) -
      (if r = i then b * F.deriv j a else 0) + a * b * F.structureCoeff r i j := by
  simp only [bracket, scaledBasis, Finset.sum_sub_distrib, ite_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hi : r = i <;> by_cases hj : r = j <;> simp_all

/-- Nijenhuis torsion, using the bracket definition, rather than its simplified
eigenframe components. -/
def nijenhuis (v X Y : ι → R) (r : ι) : R :=
  F.bracket (applyDiagonal v X) (applyDiagonal v Y) r +
    v r ^ 2 * F.bracket X Y r -
    v r * F.bracket X (applyDiagonal v Y) r -
    v r * F.bracket (applyDiagonal v X) Y r

theorem nijenhuis_scaledBasis (v : ι → R) (i j r : ι) (a b : R) :
    F.nijenhuis v (scaledBasis i a) (scaledBasis j b) r =
      a * b * ((v i - v r) * (v j - v r) * F.structureCoeff r i j +
        (if r = j then (v i - v j) * F.deriv i (v j) else 0) +
        (if r = i then (v i - v j) * F.deriv j (v i) else 0)) := by
  simp only [nijenhuis, applyDiagonal_scaledBasis, bracket_scaledBasis,
    Derivation.leibniz, smul_eq_mul]
  by_cases hi : r = i <;> by_cases hj : r = j
  all_goals simp_all
  all_goals ring

/-- Haantjes tensor, formed from Nijenhuis torsion by its defining formula. -/
def haantjes (v X Y : ι → R) (r : ι) : R :=
  F.nijenhuis v (applyDiagonal v X) (applyDiagonal v Y) r +
    v r ^ 2 * F.nijenhuis v X Y r -
    v r * F.nijenhuis v X (applyDiagonal v Y) r -
    v r * F.nijenhuis v (applyDiagonal v X) Y r

/-- PSS's eigenframe factorization of the Haantjes tensor. -/
theorem haantjes_basis (v : ι → R) (i j r : ι) :
    F.haantjes v (scaledBasis i 1) (scaledBasis j 1) r =
      (v i - v r) ^ 2 * (v j - v r) ^ 2 * F.structureCoeff r i j := by
  simp only [haantjes, applyDiagonal_scaledBasis, nijenhuis_scaledBasis]
  by_cases hi : r = i <;> by_cases hj : r = j
  all_goals simp_all
  all_goals ring

def NoTripleStructure : Prop :=
  ∀ r i j, r ≠ i → r ≠ j → i ≠ j → F.structureCoeff r i j = 0

def HaantjesComponentsVanish (v : ι → R) : Prop :=
  ∀ i j r, F.haantjes v (scaledBasis i 1) (scaledBasis j 1) r = 0

theorem haantjes_vanish_iff (v : ι → R)
    (hgap : ∀ i j, i ≠ j → IsUnit (v i - v j)) :
    F.HaantjesComponentsVanish v ↔ F.NoTripleStructure := by
  constructor
  · intro h r i j hri hrj _
    have hz := h i j r
    rw [F.haantjes_basis] at hz
    apply ((hgap i r hri.symm).pow 2 |>.mul ((hgap j r hrj.symm).pow 2)).mul_left_cancel
    simpa only [mul_zero] using hz
  · intro h i j r
    rw [F.haantjes_basis]
    by_cases hri : r = i
    · subst r; simp
    by_cases hrj : r = j
    · subst r; simp
    by_cases hij : i = j
    · subst j; rw [F.self, mul_zero]
    · rw [h r i j hri hrj hij, mul_zero]

/-- The algebraic symmetry constraint (PSS equation (2.9)). -/
def SymmetryValuesAdmissible (v w : ι → R) : Prop :=
  ∀ r i j, r ≠ i → r ≠ j → i ≠ j →
    F.structureCoeff r i j *
      ((v i - v j) * w r + (v j - v r) * w i + (v r - v i) * w j) = 0

omit [Fintype ι] in
/-- Freedom of all values in (2.9) is exactly the vanishing of the triple
structure coefficients. This alone does not assert existence of symmetries. -/
theorem all_values_admissible_iff (v : ι → R)
    (hgap : ∀ i j, i ≠ j → IsUnit (v i - v j)) :
    (∀ w, F.SymmetryValuesAdmissible v w) ↔ F.NoTripleStructure := by
  constructor
  · intro h r i j hri hrj hij
    have hz := h (scaledBasis r 1) r i j hri hrj hij
    simp [scaledBasis, hri.symm, hrj.symm] at hz
    apply (hgap i j hij).mul_right_cancel
    simpa only [zero_mul] using hz
  · intro h w r i j hri hrj hij
    rw [h r i j hri hrj hij, zero_mul]

/-- Polarization of PSS equation (2.5), for two diagonal operators in the frame. -/
def polarizedSymmetry (v w X Y : ι → R) (r : ι) : R :=
  F.bracket (applyDiagonal v X) (applyDiagonal w Y) r +
    F.bracket (applyDiagonal v Y) (applyDiagonal w X) r -
    v r * F.bracket X (applyDiagonal w Y) r -
    v r * F.bracket Y (applyDiagonal w X) r -
    w r * F.bracket (applyDiagonal v X) Y r -
    w r * F.bracket (applyDiagonal v Y) X r

/-- The triple-distinct component of the invariant commutation equation gives
exactly PSS equation (2.9), including its sign. -/
theorem polarizedSymmetry_offDiagonal (v w : ι → R) (r i j : ι)
    (hri : r ≠ i) (hrj : r ≠ j) :
    F.polarizedSymmetry v w (scaledBasis i 1) (scaledBasis j 1) r =
      -F.structureCoeff r i j *
        ((v i - v j) * w r + (v j - v r) * w i + (v r - v i) * w j) := by
  simp [polarizedSymmetry, applyDiagonal_scaledBasis, bracket_scaledBasis, hri, hrj]
  rw [F.skew r j i]
  ring

/-- The polarized invariant equation holds for arbitrary vector fields. -/
def IsHydrodynamicSymmetry (v w : ι → R) : Prop :=
  ∀ X Y r, F.polarizedSymmetry v w X Y r = 0

theorem symmetryValuesAdmissible_of_symmetry (v w : ι → R)
    (h : F.IsHydrodynamicSymmetry v w) : F.SymmetryValuesAdmissible v w := by
  intro r i j hri hrj _
  have hz := h (scaledBasis i 1) (scaledBasis j 1) r
  rw [F.polarizedSymmetry_offDiagonal v w r i j hri hrj] at hz
  linear_combination -hz

end FrameData
end SemiHamiltonian.PSS
