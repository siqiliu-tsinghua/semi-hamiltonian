module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Tactic.Module

/-! The intrinsic PSS recipes (4.6), (4.9), (4.12), (4.15), (4.18).
Naturality uses only preservation of the bracket and of the endomorphism.
Tensoriality is proved separately, using the Leibniz rule for vector fields. -/

@[expose] public section

namespace SemiHamiltonian.PSS.TensorRecipe

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

def N (br : V → V → V) (A : V → V) (X Y : V) : V :=
  br (A X) (A Y) + A (A (br X Y)) - A (br X (A Y)) - A (br (A X) Y)

/-- One cyclic summand of three times the Frölicher–Nijenhuis bracket. -/
def FNcycle (br : V → V → V) (B : V → V) (T : V → V → V) (X Y Z : V) : V :=
  B (br X (T Y Z)) - br (B X) (T Y Z) +
    B (T X (br Y Z)) + T X (B (br Y Z)) -
    T X (br (B Y) Z) - T X (br Y (B Z))

def FN (br : V → V → V) (B : V → V) (T : V → V → V) (X Y Z : V) : V :=
  FNcycle br B T X Y Z + FNcycle br B T Y Z X + FNcycle br B T Z X Y

def K (br : V → V → V) (A : V → V) : V → V → V → V :=
  FN br (fun X => A (A X)) (N br A)

def M (br : V → V → V) (A : V → V) (X Y Z : V) : V :=
  N br A X (A (N br A Y Z)) + N br A (A X) (N br A Y Z) -
    N br A (N br A X Z) (A Y) + N br A (N br A X Y) (A Z) -
    N br A X (N br A (A Y) Z) - N br A X (N br A Y (A Z))

def Q (br : V → V → V) (A : V → V) (X Y Z : V) : V :=
  K br A (A X) (A Y) Z - K br A (A (A X)) Y Z -
    K br A X (A Y) (A Z) + K br A (A X) Y (A Z) +
    4 • M br A (A X) Y Z - 2 • M br A X (A Y) Z - 2 • M br A X Y (A Z)

def P (br : V → V → V) (A : V → V) (X Y Z : V) : V :=
  A (Q br A X (A Y) Z) + A (Q br A X Y (A Z)) -
    A (A (Q br A X Y Z)) - Q br A X (A Y) (A Z)

section Naturality

variable (f : V →+ W) {br : V → V → V} {br' : W → W → W}
  {A : V → V} {A' : W → W}
  (hbr : ∀ X Y, f (br X Y) = br' (f X) (f Y))
  (hA : ∀ X, f (A X) = A' (f X))

include hbr hA

theorem map_N (X Y : V) : f (N br A X Y) = N br' A' (f X) (f Y) := by
  simp only [N, map_add, map_sub, hA, hbr]

theorem map_FNcycle {T : V → V → V} {T' : W → W → W}
    (hT : ∀ X Y, f (T X Y) = T' (f X) (f Y)) (X Y Z : V) :
    f (FNcycle br A T X Y Z) = FNcycle br' A' T' (f X) (f Y) (f Z) := by
  simp only [FNcycle, map_add, map_sub, hA, hbr, hT]

theorem map_K (X Y Z : V) : f (K br A X Y Z) = K br' A' (f X) (f Y) (f Z) := by
  simp only [K, FN, map_add]
  have hAA : ∀ X, f (A (A X)) = A' (A' (f X)) := fun X => by rw [hA, hA]
  simp only [map_FNcycle f (A := fun X => A (A X)) (A' := fun X => A' (A' X))
    hbr hAA (map_N f hbr hA)]

theorem map_M (X Y Z : V) : f (M br A X Y Z) = M br' A' (f X) (f Y) (f Z) := by
  simp only [M, map_add, map_sub, map_N f hbr hA, hA]

theorem map_Q (X Y Z : V) : f (Q br A X Y Z) = Q br' A' (f X) (f Y) (f Z) := by
  simp only [Q, map_add, map_sub, map_nsmul, map_K f hbr hA, map_M f hbr hA, hA]

/-- Covariance of the actual recipe, rather than an extra assumption on `P`. -/
theorem map_P (X Y Z : V) : f (P br A X Y Z) = P br' A' (f X) (f Y) (f Z) := by
  simp only [P, map_add, map_sub, hA, map_Q f hbr hA]

end Naturality
end SemiHamiltonian.PSS.TensorRecipe
