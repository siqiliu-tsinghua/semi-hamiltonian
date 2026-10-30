module

public import SemiHamiltonian.PSS.TensorRecipe

@[expose] public section

namespace SemiHamiltonian.PSS

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

/-- Polarization of PSS (2.5). Together with AB = BA this is the condition
that the two first-order hydrodynamic flows commute. -/
def polarized (br : V → V → V) (A B : V → V) (X Y : V) : V :=
  br (A X) (B Y) + br (A Y) (B X) - A (br X (B Y)) - A (br Y (B X)) -
    B (br (A X) Y) - B (br (A Y) X)

def IsInvariantSymmetry (br : V → V → V) (A B : V → V) : Prop :=
  Function.Commute A B ∧ ∀ X Y, polarized br A B X Y = 0

theorem map_polarized (f : V →+ W) {br : V → V → V} {br' : W → W → W}
    {A B : V → V} {A' B' : W → W}
    (hbr : ∀ X Y, f (br X Y) = br' (f X) (f Y))
    (hA : ∀ X, f (A X) = A' (f X)) (hB : ∀ X, f (B X) = B' (f X)) (X Y : V) :
    f (polarized br A B X Y) = polarized br' A' B' (f X) (f Y) := by
  simp only [polarized, map_add, map_sub, hA, hB, hbr]

theorem invariantSymmetry_map_iff (f : V ≃+ W)
    {br : V → V → V} {br' : W → W → W} {A B : V → V} {A' B' : W → W}
    (hbr : ∀ X Y, f (br X Y) = br' (f X) (f Y))
    (hA : ∀ X, f (A X) = A' (f X)) (hB : ∀ X, f (B X) = B' (f X)) :
    IsInvariantSymmetry br A B ↔ IsInvariantSymmetry br' A' B' := by
  have hc (X : V) : A (B X) = B (A X) ↔ A' (B' (f X)) = B' (A' (f X)) := by
    rw [← f.injective.eq_iff]
    simp only [hA, hB]
  have hp (X Y : V) : polarized br A B X Y = 0 ↔
      polarized br' A' B' (f X) (f Y) = 0 := by
    rw [← f.injective.eq_iff, map_zero]
    simp only [polarized, map_add, map_sub, hA, hB, hbr]
  constructor
  · rintro ⟨hcomm, hpol⟩
    constructor
    · intro X
      obtain ⟨X, rfl⟩ := f.surjective X
      exact (hc X).mp (hcomm X)
    · intro X Y
      obtain ⟨X, rfl⟩ := f.surjective X
      obtain ⟨Y, rfl⟩ := f.surjective Y
      exact (hp X Y).mp (hpol X Y)
  · rintro ⟨hcomm, hpol⟩
    exact ⟨fun X => (hc X).mpr (hcomm (f X)),
      fun X Y => (hp X Y).mpr (hpol (f X) (f Y))⟩

end SemiHamiltonian.PSS
