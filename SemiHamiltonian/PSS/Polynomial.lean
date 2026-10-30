module

public import SemiHamiltonian.Tsarev

/-!
# PSS's polynomial semi-Hamiltonian obstruction

Equation (4.7) of PSS clears the denominators in Tsarev's condition. The proof here
works in a commutative algebra, including algebras of smooth functions: only the
speed differences, rather than arbitrary nonzero elements, are required to be units.
-/

@[expose] public section

namespace SemiHamiltonian.PSS

variable {𝕜 R ι : Type*} [CommRing 𝕜] [CommRing R] [Algebra 𝕜 R]

/-- PSS equation (4.7), with index order `(k,i,j)` from the paper.
The target velocity is `v k`. -/
def alpha (D : CoordinateDerivations 𝕜 R ι) (v : ι → R) (k i j : ι) : R :=
  -(v i - v j) * (v i - v k) * (v j - v k) * D.deriv i (D.deriv j (v k)) -
    (v i - v j) * (v i + v j - 2 * v k) * D.deriv i (v k) * D.deriv j (v k) +
    (v i - v k) ^ 2 * D.deriv i (v j) * D.deriv j (v k) -
    (v j - v k) ^ 2 * D.deriv j (v i) * D.deriv i (v k)

private theorem cleared_identity (a b p q s t d gj gk cj ck : R)
    (hp : p = cj * a) (hq : q = ck * b)
    (hj : d = gj * a + cj * (t - q))
    (hk : d = gk * b + ck * (s - p)) :
    (b - a) * a * b * d + (b ^ 2 - a ^ 2) * p * q +
      a ^ 2 * s * q - b ^ 2 * t * p = a ^ 2 * b ^ 2 * (gj - gk) := by
  subst p q
  linear_combination a * b ^ 2 * hj - a ^ 2 * b * hk

/-- Exact denominator-clearing identity, proved from the derivative equations. -/
theorem alpha_eq (D : CoordinateDerivations 𝕜 R ι) (S : DiagonalSystem D)
    (k i j : ι) (hki : k ≠ i) (hkj : k ≠ j) :
    alpha D S.speed k i j = (S.speed i - S.speed k) ^ 2 *
      (S.speed j - S.speed k) ^ 2 *
        (D.deriv j (S.coeff k i) - D.deriv i (S.coeff k j)) := by
  have hi : D.deriv i (D.deriv j (S.speed k)) =
      D.deriv j (S.coeff k i) * (S.speed i - S.speed k) +
        S.coeff k i * (D.deriv j (S.speed i) - D.deriv j (S.speed k)) := by
    rw [D.commute i j, S.speed_deriv k i hki]
    simp only [Derivation.leibniz, smul_eq_mul, map_sub]
    ring
  have hj : D.deriv i (D.deriv j (S.speed k)) =
      D.deriv i (S.coeff k j) * (S.speed j - S.speed k) +
        S.coeff k j * (D.deriv i (S.speed j) - D.deriv i (S.speed k)) := by
    rw [S.speed_deriv k j hkj]
    simp only [Derivation.leibniz, smul_eq_mul, map_sub]
    ring
  have h := cleared_identity (S.speed i - S.speed k) (S.speed j - S.speed k)
    (D.deriv i (S.speed k)) (D.deriv j (S.speed k))
    (D.deriv i (S.speed j)) (D.deriv j (S.speed i))
    (D.deriv i (D.deriv j (S.speed k)))
    (D.deriv j (S.coeff k i)) (D.deriv i (S.coeff k j))
    (S.coeff k i) (S.coeff k j) (S.speed_deriv k i hki) (S.speed_deriv k j hkj) hi hj
  dsimp [alpha]
  linear_combination h

theorem semiHamiltonian_iff_alpha_zero (D : CoordinateDerivations 𝕜 R ι)
    (S : DiagonalSystem D) :
    S.IsSemiHamiltonian ↔
      ∀ k i j, k ≠ i → k ≠ j → i ≠ j → alpha D S.speed k i j = 0 := by
  constructor
  · intro h k i j hki hkj hij
    rw [alpha_eq D S k i j hki hkj, h k i j hki hkj hij, sub_self, mul_zero]
  · intro h k i j hki hkj hij
    have hz := h k i j hki hkj hij
    rw [alpha_eq D S k i j hki hkj] at hz
    apply sub_eq_zero.mp
    apply ((S.gap_unit k i hki).pow 2 |>.mul ((S.gap_unit k j hkj).pow 2)).mul_left_cancel
    simpa only [mul_zero] using hz

end SemiHamiltonian.PSS
