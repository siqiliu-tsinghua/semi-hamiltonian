module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic.Ring

/-!
# Diagonal hydrodynamic systems over a differential algebra

`Analysis.SmoothFunctions` instantiates the algebra by actual smooth functions on a
coordinate neighbourhood. There strict hyperbolicity makes the speed differences units.
Mere inequality of two elements of a ring of smooth functions would not suffice.
-/

@[expose] public section

namespace SemiHamiltonian

variable (𝕜 R ι : Type*) [CommRing 𝕜] [CommRing R] [Algebra 𝕜 R]

/-- Commuting coordinate derivatives. No infinite jet space is used here. -/
structure CoordinateDerivations where
  deriv : ι → Derivation 𝕜 R R
  commute : ∀ i j f, deriv i (deriv j f) = deriv j (deriv i f)

variable {𝕜 R ι}

/-- A diagonal system with everywhere separated speeds. `coeff i j` represents
`∂ⱼvⁱ / (vʲ - vⁱ)` for distinct indices; diagonal entries are unused. -/
structure DiagonalSystem (D : CoordinateDerivations 𝕜 R ι) where
  speed : ι → R
  coeff : ι → ι → R
  speed_deriv : ∀ i j, i ≠ j →
    D.deriv j (speed i) = coeff i j * (speed j - speed i)
  gap_unit : ∀ i j, i ≠ j → IsUnit (speed j - speed i)

namespace DiagonalSystem

variable {D : CoordinateDerivations 𝕜 R ι} (S : DiagonalSystem D)

/-- Build the coefficients from the speeds and unit gaps; users do not have to
supply Tsarev's coefficients separately. -/
noncomputable def ofSpeeds (D : CoordinateDerivations 𝕜 R ι) (v : ι → R)
    (hgap : ∀ i j, i ≠ j → IsUnit (v j - v i)) : DiagonalSystem D where
  speed := v
  coeff i j := D.deriv j (v i) * Ring.inverse (v j - v i)
  speed_deriv i j hij := by
    rw [mul_assoc, Ring.inverse_mul_cancel _ (hgap i j hij), mul_one]
  gap_unit := hgap

/-- Off the diagonal the derivative equation uniquely determines the coefficient. -/
theorem coeff_unique (i j : ι) (hij : i ≠ j) (b : R)
    (hb : D.deriv j (S.speed i) = b * (S.speed j - S.speed i)) : S.coeff i j = b := by
  apply (S.gap_unit i j hij).mul_right_cancel
  rw [← S.speed_deriv i j hij, hb]

/-- Tsarev's semi-Hamiltonian condition, only on triples of distinct indices. -/
def IsSemiHamiltonian : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    D.deriv k (S.coeff i j) = D.deriv j (S.coeff i k)

/-- The linear PDE for a commuting hydrodynamic speed. This is a predicate on an
actual element of the differential algebra, not a formal compatibility condition. -/
def IsCommutingSpeed (w : ι → R) : Prop :=
  ∀ i j, i ≠ j → D.deriv j (w i) = S.coeff i j * (w j - w i)

theorem speed_isCommutingSpeed : S.IsCommutingSpeed S.speed := S.speed_deriv

theorem one_isCommutingSpeed : S.IsCommutingSpeed (fun _ => 1) := by
  intro i j _
  simp

/-- Coefficient of `uₓⁱ uₓʲ` in the commutator of the two diagonal flows.
The `uₓₓ` terms cancel because the velocity matrices are diagonal. -/
def flowBracketCoeff (w : ι → R) (i j : ι) : R :=
  D.deriv j (w i) * (S.speed j - S.speed i) -
    D.deriv j (S.speed i) * (w j - w i)

theorem isCommutingSpeed_iff_flowBracketCoeff (w : ι → R) :
    S.IsCommutingSpeed w ↔ ∀ i j, S.flowBracketCoeff w i j = 0 := by
  constructor
  · intro hw i j
    by_cases hij : i = j
    · subst j
      simp [flowBracketCoeff]
    · rw [flowBracketCoeff, hw i j hij, S.speed_deriv i j hij]
      ring
  · intro hw i j hij
    apply (S.gap_unit i j hij).mul_right_cancel
    have h := sub_eq_zero.mp (hw i j)
    rw [h, S.speed_deriv i j hij]
    ring

end DiagonalSystem
end SemiHamiltonian
