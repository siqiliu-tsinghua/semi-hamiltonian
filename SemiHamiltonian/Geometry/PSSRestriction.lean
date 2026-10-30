module

public import SemiHamiltonian.Geometry.PSSTensor
public import SemiHamiltonian.Geometry.MatrixField

/-! Locality of the intrinsic PSS tensor, proved by restricting actual fields. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U V : Set (ι → ℝ)}

theorem Endomorphism.ofField_matrix (A : Endomorphism U) :
    Endomorphism.ofField A.matrix A.matrix_smooth = A := by
  apply LinearMap.ext
  intro X
  funext i
  apply Subtype.ext
  funext x
  have hh := Endomorphism.field_ofField A.matrix A.matrix_smooth X x
  rw [A.matrix_field] at hh
  simpa only [field_apply] using congrFun hh i

noncomputable def restrictFields (hVU : V ⊆ U) : Fields U →+ Fields V where
  toFun X i := restrict hVU (X i)
  map_zero' := by funext i; exact map_zero _
  map_add' X Y := by funext i; exact map_add _ _ _

theorem field_restrictFields (hVU : V ⊆ U) (X : Fields U) (x : V) :
    field (restrictFields hVU X) x = field X (⟨x, hVU x.property⟩ : U) := by
  funext i
  rw [field_apply, field_apply X (⟨x, hVU x.property⟩ : U)]
  exact restrict_apply hVU (X i) x

theorem restrictFields_bracket (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (X Y : Fields U) :
    restrictFields hVU (fieldBracket hU X Y) =
      fieldBracket hV (restrictFields hVU X) (restrictFields hVU Y) := by
  funext i
  change restrict hVU (fieldDerivation hU X (Y i) - fieldDerivation hU Y (X i)) = _
  simp only [fieldBracket, fieldDerivation_apply, map_sub, map_sum, map_mul,
    coordinateDerivations, restrict_derivation hU hV hVU, restrictFields, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]

theorem restrictFields_ofField (hVU : V ⊆ U)
    (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)) (hM : ContDiffOn ℝ ∞ M U)
    (X : Fields U) :
    restrictFields hVU (Endomorphism.ofField M hM X) =
      Endomorphism.ofField M (hM.mono hVU) (restrictFields hVU X) := by
  funext i
  apply Subtype.ext
  funext x
  have hh := field_restrictFields hVU (Endomorphism.ofField M hM X) x
  rw [Endomorphism.field_ofField] at hh
  have hh' := Endomorphism.field_ofField M (hM.mono hVU) (restrictFields hVU X) x
  rw [field_restrictFields] at hh'
  simpa only [field_apply] using congrFun (hh.trans hh'.symm) i

theorem restrictFields_standard (hVU : V ⊆ U) (i : ι) :
    restrictFields hVU (standardField i) = standardField i := by
  funext j
  simp [restrictFields, standardField, Pi.single_apply]

theorem pssVanish_iff_standard (hU : IsOpen U) (A : Endomorphism U) :
    PSSVanish hU A ↔ ∀ i j k,
      pssTensor hU A (standardField i) (standardField j) (standardField k) = 0 := by
  constructor
  · intro h i j k; exact h _ _ _
  · intro h X Y Z
    rw [← sum_standardField X, ← sum_standardField Y, ← sum_standardField Z]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      h, smul_zero, Finset.sum_const_zero]

theorem restrictFields_pss (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)) (hM : ContDiffOn ℝ ∞ M U)
    (X Y Z : Fields U) :
    restrictFields hVU (pssTensor hU (Endomorphism.ofField M hM) X Y Z) =
      pssTensor hV (Endomorphism.ofField M (hM.mono hVU))
        (restrictFields hVU X) (restrictFields hVU Y) (restrictFields hVU Z) :=
  PSS.TensorRecipe.map_P (restrictFields hVU) (restrictFields_bracket hU hV hVU)
    (restrictFields_ofField hVU M hM) X Y Z

theorem pssVanish_restrict (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)) (hM : ContDiffOn ℝ ∞ M U)
    (hP : PSSVanish hU (Endomorphism.ofField M hM)) :
    PSSVanish hV (Endomorphism.ofField M (hM.mono hVU)) := by
  apply (pssVanish_iff_standard hV _).mpr
  intro i j k
  have hh := restrictFields_pss hU hV hVU M hM
    (standardField i) (standardField j) (standardField k)
  rw [hP] at hh
  simpa only [restrictFields_standard, map_zero] using hh.symm

/-- Vanishing is local; no extension of local smooth sections is assumed. -/
theorem pssVanish_of_local (hU : IsOpen U)
    (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)) (hM : ContDiffOn ℝ ∞ M U)
    (hloc : ∀ p ∈ U, ∃ V, ∃ hV : IsOpen V, ∃ hVU : V ⊆ U,
      p ∈ V ∧ PSSVanish hV (Endomorphism.ofField M (hM.mono hVU))) :
    PSSVanish hU (Endomorphism.ofField M hM) := by
  apply (pssVanish_iff_standard hU _).mpr
  intro i j k
  funext r
  apply Subtype.ext
  funext x
  obtain ⟨V, hV, hVU, hx, hP⟩ := hloc x x.property
  have hh := restrictFields_pss hU hV hVU M hM
    (standardField i) (standardField j) (standardField k)
  rw [hP] at hh
  have hev := congrArg (fun X : Fields V => X r ⟨x, hx⟩) hh
  change restrict hVU (pssTensor hU (Endomorphism.ofField M hM)
    (standardField i) (standardField j) (standardField k) r) ⟨x, hx⟩ = 0 at hev
  rw [restrict_apply] at hev
  exact hev

end SemiHamiltonian.Smooth
