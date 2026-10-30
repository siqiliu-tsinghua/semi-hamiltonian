module

public import SemiHamiltonian.Geometry.SmoothFrame

/-! Nijenhuis and Haantjes tensors of smooth endomorphisms, with actual smooth
vector-field brackets, and the involutivity consequence for an eigenframe. -/

@[expose] public section

open scoped Classical
open Set

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}
  (hU : IsOpen U)

abbrev Endomorphism (U : Set (ι → ℝ)) := Fields U →ₗ[Functions U] Fields U

noncomputable def nijenhuis (A : Endomorphism U) (X Y : Fields U) : Fields U :=
  fieldBracket hU (A X) (A Y) + A (A (fieldBracket hU X Y)) -
    A (fieldBracket hU X (A Y)) - A (fieldBracket hU (A X) Y)

noncomputable def haantjes (A : Endomorphism U) (X Y : Fields U) : Fields U :=
  nijenhuis hU A (A X) (A Y) + A (A (nijenhuis hU A X Y)) -
    A (nijenhuis hU A X (A Y)) - A (nijenhuis hU A (A X) Y)

def HaantjesVanish (A : Endomorphism U) : Prop := ∀ X Y, haantjes hU A X Y = 0

theorem nijenhuis_smul_left (A : Endomorphism U) (X Y : Fields U) (f : Functions U) :
    nijenhuis hU A (f • X) Y = f • nijenhuis hU A X Y := by
  simp only [nijenhuis, map_smul, fieldBracket_smul_left, map_sub]
  module

theorem nijenhuis_smul_right (A : Endomorphism U) (X Y : Fields U) (f : Functions U) :
    nijenhuis hU A X (f • Y) = f • nijenhuis hU A X Y := by
  simp only [nijenhuis, map_smul, fieldBracket_smul_right, map_add]
  module

theorem haantjes_smul_left (A : Endomorphism U) (X Y : Fields U) (f : Functions U) :
    haantjes hU A (f • X) Y = f • haantjes hU A X Y := by
  simp only [haantjes, map_smul, nijenhuis_smul_left]
  module

theorem haantjes_smul_right (A : Endomorphism U) (X Y : Fields U) (f : Functions U) :
    haantjes hU A X (f • Y) = f • haantjes hU A X Y := by
  simp only [haantjes, map_smul, nijenhuis_smul_right]
  module

theorem nijenhuis_sum_left (A : Endomorphism U) {κ : Type} (s : Finset κ)
    (X : κ → Fields U) (Y : Fields U) :
    nijenhuis hU A (∑ k ∈ s, X k) Y = ∑ k ∈ s, nijenhuis hU A (X k) Y := by
  simp only [nijenhuis, map_sum, fieldBracket_sum_left, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

theorem nijenhuis_sum_right (A : Endomorphism U) {κ : Type} (s : Finset κ)
    (X : Fields U) (Y : κ → Fields U) :
    nijenhuis hU A X (∑ k ∈ s, Y k) = ∑ k ∈ s, nijenhuis hU A X (Y k) := by
  simp only [nijenhuis, map_sum, fieldBracket_sum_right, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

theorem haantjes_sum_left (A : Endomorphism U) {κ : Type} (s : Finset κ)
    (X : κ → Fields U) (Y : Fields U) :
    haantjes hU A (∑ k ∈ s, X k) Y = ∑ k ∈ s, haantjes hU A (X k) Y := by
  simp only [haantjes, map_sum, nijenhuis_sum_left, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

theorem haantjes_sum_right (A : Endomorphism U) {κ : Type} (s : Finset κ)
    (X : Fields U) (Y : κ → Fields U) :
    haantjes hU A X (∑ k ∈ s, Y k) = ∑ k ∈ s, haantjes hU A X (Y k) := by
  simp only [haantjes, map_sum, nijenhuis_sum_right, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

namespace Frame

variable (b : Frame U) (A : Endomorphism U) (v : ι → Functions U)
  (heigen : ∀ i, A (b i) = v i • b i)

include heigen

theorem endomorphism_coordinates (X : Fields U) :
    b.equivFun (A X) = PSS.FrameData.applyDiagonal v (b.equivFun X) := by
  nth_rw 1 [← b.sum_equivFun X]
  simp only [map_sum, map_smul, heigen, smul_smul]
  funext r
  simp [PSS.FrameData.applyDiagonal, Finsupp.single_apply, mul_comm]

theorem nijenhuis_coordinates (X Y : Fields U) :
    b.equivFun (nijenhuis hU A X Y) = (b.data hU).nijenhuis v (b.equivFun X) (b.equivFun Y) := by
  funext r
  simp only [nijenhuis, map_add, map_sub, Pi.add_apply, Pi.sub_apply,
    endomorphism_coordinates b A v heigen, bracket_coordinates,
    PSS.FrameData.nijenhuis, PSS.FrameData.applyDiagonal]
  ring

theorem haantjes_coordinates (X Y : Fields U) :
    b.equivFun (haantjes hU A X Y) = (b.data hU).haantjes v (b.equivFun X) (b.equivFun Y) := by
  funext r
  simp only [haantjes, map_add, map_sub, Pi.add_apply, Pi.sub_apply,
    endomorphism_coordinates b A v heigen, nijenhuis_coordinates hU b A v heigen,
    PSS.FrameData.haantjes, PSS.FrameData.applyDiagonal]
  ring

theorem haantjes_basis_coordinates (i j r : ι) :
    b.equivFun (haantjes hU A (b i) (b j)) r =
      (v i - v r) ^ 2 * (v j - v r) ^ 2 * (b.data hU).structureCoeff r i j := by
  rw [haantjes_coordinates hU b A v heigen]
  have hb (k : ι) : b.equivFun (b k) = PSS.FrameData.scaledBasis k 1 := by
    funext a
    simp [PSS.FrameData.scaledBasis, eq_comm]
  rw [hb, hb]
  exact (b.data hU).haantjes_basis v i j r

theorem haantjesVanish_iff_components :
    HaantjesVanish hU A ↔ (b.data hU).HaantjesComponentsVanish v := by
  constructor
  · intro h i j r
    have he := congrArg (fun X => b.equivFun X r) (h (b i) (b j))
    rw [haantjes_basis_coordinates hU b A v heigen] at he
    simpa only [(b.data hU).haantjes_basis, map_zero, Pi.zero_apply] using he
  · intro h X Y
    have hb (i j : ι) : haantjes hU A (b i) (b j) = 0 := by
      apply b.equivFun.injective
      funext r
      rw [haantjes_basis_coordinates hU b A v heigen]
      simpa only [(b.data hU).haantjes_basis, map_zero, Pi.zero_apply] using h i j r
    rw [← b.sum_equivFun X, ← b.sum_equivFun Y, haantjes_sum_left]
    simp_rw [haantjes_sum_right, haantjes_smul_left, haantjes_smul_right, hb, smul_zero,
      Finset.sum_const_zero]

/-- Haantjes vanishing for the actual endomorphism is equivalent to closure of
each complementary eigen-distribution under the actual Lie bracket. -/
theorem haantjesVanish_iff_complement_involutive
    (hgap : ∀ i j, i ≠ j → IsUnit (v i - v j)) :
    HaantjesVanish hU A ↔ ∀ r, b.Involutive hU {r}ᶜ :=
  (b.haantjesVanish_iff_components hU A v heigen).trans
    (b.haantjes_iff_complement_involutive hU v hgap)

end Frame
end SemiHamiltonian.Smooth
