module

public import SemiHamiltonian.PSS.TensorRecipe
public import Mathlib.Tactic.Abel

/-! Tensoriality of the PSS recipe. The proof needs only the additive and
Leibniz identities of the vector-field bracket, not a choice of coordinates. -/

@[expose] public section

namespace SemiHamiltonian.PSS

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- The bracket identities used by the tensor calculation. The anchor is the
directional derivative of a scalar function. No integrability hypothesis is included. -/
structure BracketCalculus where
  bracket : V → V → V
  anchor : V → R → R
  add_left : ∀ X Y Z, bracket (X + Y) Z = bracket X Z + bracket Y Z
  add_right : ∀ X Y Z, bracket X (Y + Z) = bracket X Y + bracket X Z
  skew : ∀ X Y, bracket X Y = -bracket Y X
  smul_left : ∀ f X Y, bracket (f • X) Y = f • bracket X Y - anchor Y f • X
  smul_right : ∀ f X Y, bracket X (f • Y) = anchor X f • Y + f • bracket X Y

variable {R V}

namespace BracketCalculus

open TensorRecipe

variable (C : BracketCalculus R V) (A : V →ₗ[R] V)

theorem N_add_left (X Y Z : V) :
    N C.bracket A (X + Y) Z = N C.bracket A X Z + N C.bracket A Y Z := by
  simp only [N, map_add, C.add_left]
  abel

theorem N_add_right (X Y Z : V) :
    N C.bracket A X (Y + Z) = N C.bracket A X Y + N C.bracket A X Z := by
  simp only [N, map_add, C.add_right]
  abel

theorem N_smul_left (f : R) (X Y : V) :
    N C.bracket A (f • X) Y = f • N C.bracket A X Y := by
  simp only [N, map_smul, C.smul_left, map_sub]
  module

theorem N_smul_right (f : R) (X Y : V) :
    N C.bracket A X (f • Y) = f • N C.bracket A X Y := by
  simp only [N, map_smul, C.smul_right, map_add]
  module

theorem N_skew (X Y : V) : N C.bracket A X Y = -N C.bracket A Y X := by
  unfold N
  rw [C.skew (A X) (A Y), C.skew X Y, C.skew X (A Y), C.skew (A X) Y]
  simp only [map_neg]
  abel

/-- Nijenhuis torsion as a bilinear map over the scalar function ring. -/
def nijenhuis : V →ₗ[R] V →ₗ[R] V where
  toFun X :=
    { toFun := N C.bracket A X
      map_add' := C.N_add_right A X
      map_smul' := fun f Y => C.N_smul_right A f X Y }
  map_add' X Y := LinearMap.ext (fun Z => C.N_add_left A X Y Z)
  map_smul' f X := LinearMap.ext (fun Y => C.N_smul_left A f X Y)

@[simp] theorem nijenhuis_apply (X Y : V) :
    C.nijenhuis A X Y = N C.bracket A X Y := rfl

section FN

variable (B : V →ₗ[R] V) (T : V →ₗ[R] V →ₗ[R] V)
  (hT : ∀ X Y, T X Y = -T Y X)

theorem FN_add_left (X X' Y Z : V) :
    FN C.bracket B (fun X Y => T X Y) (X + X') Y Z =
      FN C.bracket B (fun X Y => T X Y) X Y Z +
        FN C.bracket B (fun X Y => T X Y) X' Y Z := by
  simp only [FN, FNcycle, map_add, C.add_left, C.add_right, LinearMap.add_apply]
  abel

theorem FN_cyclic (X Y Z : V) :
    FN C.bracket B (fun X Y => T X Y) X Y Z =
      FN C.bracket B (fun X Y => T X Y) Y Z X := by
  unfold FN
  abel

include hT in
theorem FN_smul_left (f : R) (X Y Z : V) :
    FN C.bracket B (fun X Y => T X Y) (f • X) Y Z =
      f • FN C.bracket B (fun X Y => T X Y) X Y Z := by
  simp only [FN, FNcycle, map_smul, C.smul_left, C.smul_right,
    map_add, map_sub, LinearMap.smul_apply]
  rw [hT Y X, hT Z X, hT Z (B X), hT Y (B X)]
  simp only [map_neg]
  module

theorem FN_add_middle (X Y Y' Z : V) :
    FN C.bracket B (fun X Y => T X Y) X (Y + Y') Z =
      FN C.bracket B (fun X Y => T X Y) X Y Z +
        FN C.bracket B (fun X Y => T X Y) X Y' Z := by
  rw [C.FN_cyclic, C.FN_add_left, C.FN_cyclic B T Y, C.FN_cyclic B T Y',
    C.FN_cyclic B T Z, C.FN_cyclic B T Z]

theorem FN_add_right (X Y Z Z' : V) :
    FN C.bracket B (fun X Y => T X Y) X Y (Z + Z') =
      FN C.bracket B (fun X Y => T X Y) X Y Z +
        FN C.bracket B (fun X Y => T X Y) X Y Z' := by
  rw [C.FN_cyclic, C.FN_add_middle, ← C.FN_cyclic B T X,
    ← C.FN_cyclic B T X]

include hT in
theorem FN_smul_middle (f : R) (X Y Z : V) :
    FN C.bracket B (fun X Y => T X Y) X (f • Y) Z =
      f • FN C.bracket B (fun X Y => T X Y) X Y Z := by
  rw [C.FN_cyclic, C.FN_smul_left B T hT, ← C.FN_cyclic B T X]

include hT in
theorem FN_smul_right (f : R) (X Y Z : V) :
    FN C.bracket B (fun X Y => T X Y) X Y (f • Z) =
      f • FN C.bracket B (fun X Y => T X Y) X Y Z := by
  rw [C.FN_cyclic, C.FN_smul_middle B T hT, ← C.FN_cyclic B T X]

end FN

/-- Package a function known to be linear in its three arguments. -/
def mkTrilinear (F : V → V → V → V)
    (ha : ∀ X X' Y Z, F (X + X') Y Z = F X Y Z + F X' Y Z)
    (hb : ∀ X Y Y' Z, F X (Y + Y') Z = F X Y Z + F X Y' Z)
    (hc : ∀ X Y Z Z', F X Y (Z + Z') = F X Y Z + F X Y Z')
    (sa : ∀ (f : R) X Y Z, F (f • X) Y Z = f • F X Y Z)
    (sb : ∀ (f : R) X Y Z, F X (f • Y) Z = f • F X Y Z)
    (sc : ∀ (f : R) X Y Z, F X Y (f • Z) = f • F X Y Z) :
    V →ₗ[R] V →ₗ[R] V →ₗ[R] V where
  toFun X :=
    { toFun Y :=
        { toFun := F X Y
          map_add' := hc X Y
          map_smul' := fun f Z => sc f X Y Z }
      map_add' Y Y' := LinearMap.ext (hb X Y Y')
      map_smul' f Y := LinearMap.ext (sb f X Y) }
  map_add' X X' := LinearMap.ext (fun Y => LinearMap.ext (ha X X' Y))
  map_smul' f X := LinearMap.ext (fun Y => LinearMap.ext (sa f X Y))

/-- The FN bracket appearing in PSS, as a genuine trilinear tensor. -/
def kTensor : V →ₗ[R] V →ₗ[R] V →ₗ[R] V :=
  mkTrilinear (K C.bracket A)
    (C.FN_add_left (A.comp A) (C.nijenhuis A))
    (C.FN_add_middle (A.comp A) (C.nijenhuis A))
    (C.FN_add_right (A.comp A) (C.nijenhuis A))
    (C.FN_smul_left (A.comp A) (C.nijenhuis A) (C.N_skew A))
    (C.FN_smul_middle (A.comp A) (C.nijenhuis A) (C.N_skew A))
    (C.FN_smul_right (A.comp A) (C.nijenhuis A) (C.N_skew A))

@[simp] theorem kTensor_apply (X Y Z : V) :
    C.kTensor A X Y Z = K C.bracket A X Y Z := rfl

def mTensor : V →ₗ[R] V →ₗ[R] V →ₗ[R] V := by
  apply mkTrilinear (M C.bracket A)
  all_goals
    intros
    simp only [M, ← C.nijenhuis_apply A, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply]
    module

@[simp] theorem mTensor_apply (X Y Z : V) :
    C.mTensor A X Y Z = M C.bracket A X Y Z := rfl

def qTensor : V →ₗ[R] V →ₗ[R] V →ₗ[R] V := by
  apply mkTrilinear (Q C.bracket A)
  all_goals
    intros
    simp only [Q, ← C.kTensor_apply A, ← C.mTensor_apply A,
      map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    module

@[simp] theorem qTensor_apply (X Y Z : V) :
    C.qTensor A X Y Z = Q C.bracket A X Y Z := rfl

/-- The PSS (1,3)-tensor on a module of vector fields. -/
def pTensor : V →ₗ[R] V →ₗ[R] V →ₗ[R] V := by
  apply mkTrilinear (P C.bracket A)
  all_goals
    intros
    simp only [P, ← C.qTensor_apply A, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply]
    module

@[simp] theorem pTensor_apply (X Y Z : V) :
    C.pTensor A X Y Z = P C.bracket A X Y Z := rfl

end BracketCalculus
end SemiHamiltonian.PSS
