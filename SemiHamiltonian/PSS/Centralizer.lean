module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Ring

/-! The linear algebra step preceding PSS equation (2.9). -/

@[expose] public section

namespace SemiHamiltonian.PSS

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- A matrix commuting with a separated diagonal velocity matrix must itself be
diagonal. Unit gaps let this hold in algebras of smooth functions as well as fields. -/
theorem commuting_matrix_is_diagonal (v : ι → R)
    (hgap : ∀ i j, i ≠ j → IsUnit (v i - v j)) (B : Matrix ι ι R)
    (h : Matrix.diagonal v * B = B * Matrix.diagonal v) :
    B = Matrix.diagonal (fun i => B i i) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · have he := congrArg (fun M : Matrix ι ι R => M i j) h
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    have hz : (v i - v j) * B i j = 0 := by
      calc
        (v i - v j) * B i j = v i * B i j - B i j * v j := by ring
        _ = 0 := sub_eq_zero.mpr he
    have hb : B i j = 0 := (hgap i j hij).mul_left_cancel (by simpa using hz)
    simp [Matrix.diagonal, hij, hb]

end SemiHamiltonian.PSS
