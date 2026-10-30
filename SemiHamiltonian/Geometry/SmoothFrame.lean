module

public import SemiHamiltonian.Geometry.VectorFields
public import SemiHamiltonian.PSS.Eigenframe

/-! Smooth frames, their actual structure coefficients, and spectral distributions. -/

@[expose] public section

open scoped Classical
open Set

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}

abbrev Frame (U : Set (ι → ℝ)) := Module.Basis ι (Functions U) (Fields U)

namespace Frame

variable (hU : IsOpen U) (b : Frame U)

noncomputable def data : PSS.FrameData ℝ (Functions U) ι where
  deriv i := fieldDerivation hU (b i)
  structureCoeff r i j := b.equivFun (fieldBracket hU (b i) (b j)) r
  self r i := by simp
  skew r i j := by rw [fieldBracket_swap]; simp

theorem bracket_coordinates (X Y : Fields U) :
    b.equivFun (fieldBracket hU X Y) = (data hU b).bracket (b.equivFun X) (b.equivFun Y) := by
  classical
  nth_rw 1 [← b.sum_equivFun X, ← b.sum_equivFun Y]
  rw [fieldBracket_sum_left]
  simp_rw [fieldBracket_sum_right, fieldBracket_smul_left, fieldBracket_smul_right,
    fieldDerivation_smul, Derivation.smul_apply]
  funext r
  simp only [map_sum, map_sub, map_add, map_smul, Finset.sum_apply, Pi.sub_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, b.equivFun_self]
  simp only [PSS.FrameData.bracket, data]
  simp_rw [mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

/-- Sections of the subbundle spanned by the chosen frame directions. -/
def InDistribution (I : Set ι) (X : Fields U) : Prop := ∀ r, r ∉ I → b.equivFun X r = 0

def Involutive (I : Set ι) : Prop :=
  ∀ X Y, b.InDistribution I X → b.InDistribution I Y →
    b.InDistribution I (fieldBracket hU X Y)

theorem involutive_of_noTripleStructure (h : (b.data hU).NoTripleStructure) (I : Set ι) :
    b.Involutive hU I := by
  intro X Y hX hY r hr
  rw [bracket_coordinates]
  unfold PSS.FrameData.bracket
  have hx := hX r hr
  have hy := hY r hr
  simp only [hx, hy, map_zero, mul_zero, sub_self, Finset.sum_const_zero, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hi : i ∈ I
  · by_cases hj : j ∈ I
    · by_cases hij : i = j
      · subst j; rw [(b.data hU).self, mul_zero]
      · rw [h r i j (fun he => hr (he ▸ hi)) (fun he => hr (he ▸ hj)) hij, mul_zero]
    · rw [hY j hj, mul_zero, zero_mul]
  · rw [hX i hi, zero_mul, zero_mul]

theorem noTripleStructure_of_complement_involutive
    (h : ∀ r, b.Involutive hU {r}ᶜ) : (b.data hU).NoTripleStructure := by
  intro r i j hri hrj _
  have hi : b.InDistribution {r}ᶜ (b i) := by
    intro k hk
    have hk' : k = r := by simpa using hk
    subst k
    simp [hri.symm]
  have hj : b.InDistribution {r}ᶜ (b j) := by
    intro k hk
    have hk' : k = r := by simpa using hk
    subst k
    simp [hrj.symm]
  exact h r (b i) (b j) hi hj r (by simp)

/-- The Haantjes algebraic condition is precisely involutivity of all the
codimension-one spectral distributions, for actual smooth section brackets. -/
theorem haantjes_iff_complement_involutive (v : ι → Functions U)
    (hgap : ∀ i j, i ≠ j → IsUnit (v i - v j)) :
    (b.data hU).HaantjesComponentsVanish v ↔ ∀ r, b.Involutive hU {r}ᶜ := by
  rw [(b.data hU).haantjes_vanish_iff v hgap]
  exact ⟨fun h r => b.involutive_of_noTripleStructure hU h _,
    b.noTripleStructure_of_complement_involutive hU⟩

end Frame
end SemiHamiltonian.Smooth
