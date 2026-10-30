module

public import SemiHamiltonian.PSS.InvariantSymmetry
public import SemiHamiltonian.PSS.Tensoriality

@[expose] public section

namespace SemiHamiltonian.PSS.BracketCalculus

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  (C : BracketCalculus R V) (A B : V →ₗ[R] V)

theorem polarized_symmetric (X Y : V) :
    polarized C.bracket A B X Y = polarized C.bracket A B Y X := by
  unfold polarized
  abel

theorem polarized_add_left (X Y Z : V) :
    polarized C.bracket A B (X + Y) Z =
      polarized C.bracket A B X Z + polarized C.bracket A B Y Z := by
  simp only [polarized, map_add, C.add_left, C.add_right]
  abel

theorem polarized_smul_left (hc : Function.Commute A B) (f : R) (X Y : V) :
    polarized C.bracket A B (f • X) Y = f • polarized C.bracket A B X Y := by
  simp only [polarized, map_smul, C.smul_left, C.smul_right, map_add, map_sub]
  rw [hc X]
  module

/-- The polarized commutation equation is a tensor when the operators commute. -/
def symmetryTensor (hc : Function.Commute A B) : V →ₗ[R] V →ₗ[R] V where
  toFun X :=
    { toFun := polarized C.bracket A B X
      map_add' Y Z := by
        rw [C.polarized_symmetric, C.polarized_add_left,
          C.polarized_symmetric A B Y, C.polarized_symmetric A B Z]
      map_smul' f Y := by
        simp only [RingHom.id_apply]
        rw [C.polarized_symmetric, C.polarized_smul_left A B hc,
          C.polarized_symmetric A B Y] }
  map_add' X Y := LinearMap.ext (fun Z => C.polarized_add_left A B X Y Z)
  map_smul' f X := LinearMap.ext (fun Y => C.polarized_smul_left A B hc f X Y)

@[simp] theorem symmetryTensor_apply (hc : Function.Commute A B) (X Y : V) :
    C.symmetryTensor A B hc X Y = polarized C.bracket A B X Y := rfl

end SemiHamiltonian.PSS.BracketCalculus
