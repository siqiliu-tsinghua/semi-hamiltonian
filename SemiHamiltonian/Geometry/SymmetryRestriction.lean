module

public import SemiHamiltonian.Geometry.SymmetryTransport
public import SemiHamiltonian.Geometry.PSSRestriction
public import SemiHamiltonian.PSS.SymmetryCalculus

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U V : Set (ι → ℝ)}

theorem Endomorphism.commute_iff_matrix (A B : Endomorphism U) :
    Function.Commute A B ↔ ∀ x : U, Function.Commute (A.matrix x) (B.matrix x) := by
  constructor
  · intro h x z
    have hh := congrArg (fun X => field X x) (h (constantField z))
    simpa only [← matrix_field, field_constantField] using hh
  · intro h X
    funext i
    apply Subtype.ext
    funext x
    have hh := h x (field X x)
    simpa only [matrix_field, field_apply] using congrFun hh i

noncomputable def Endomorphism.restrict (hVU : V ⊆ U) (B : Endomorphism U) :
    Endomorphism V := ofField B.matrix (B.matrix_smooth.mono hVU)

theorem Endomorphism.restrict_matrix (hVU : V ⊆ U) (B : Endomorphism U) (x : V) :
    (B.restrict hVU).matrix x = B.matrix x := matrix_ofField _ _ x

theorem restrictFields_endomorphism (hVU : V ⊆ U) (B : Endomorphism U) (X : Fields U) :
    restrictFields hVU (B X) = B.restrict hVU (restrictFields hVU X) := by
  have hh := restrictFields_ofField hVU B.matrix B.matrix_smooth X
  rw [Endomorphism.ofField_matrix] at hh
  exact hh

theorem invariantSymmetry_iff_standard (hU : IsOpen U) (A B : Endomorphism U) :
    IsHydrodynamicSymmetry hU A B ↔ Function.Commute A B ∧
      ∀ i j, PSS.polarized (fieldBracket hU) A B (standardField i) (standardField j) = 0 := by
  constructor
  · intro h; exact ⟨h.1, fun i j => h.2 _ _⟩
  · rintro ⟨hc, hh⟩
    refine ⟨hc, ?_⟩
    intro X Y
    change (bracketCalculus hU).symmetryTensor A B hc X Y = 0
    rw [← sum_standardField X, ← sum_standardField Y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      PSS.BracketCalculus.symmetryTensor_apply, bracketCalculus, hh, smul_zero, Finset.sum_const_zero]

theorem IsHydrodynamicSymmetry.restrict (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    {A B : Endomorphism U} (h : IsHydrodynamicSymmetry hU A B) :
    IsHydrodynamicSymmetry hV (A.restrict hVU) (B.restrict hVU) := by
  apply (invariantSymmetry_iff_standard hV _ _).mpr
  constructor
  · apply (Endomorphism.commute_iff_matrix _ _).mpr
    intro x
    simp only [Endomorphism.restrict_matrix]
    exact (Endomorphism.commute_iff_matrix A B).mp h.1 ⟨x, hVU x.property⟩
  · intro i j
    have hh := PSS.map_polarized (restrictFields hVU) (restrictFields_bracket hU hV hVU)
      (restrictFields_endomorphism hVU A) (restrictFields_endomorphism hVU B)
      (standardField i) (standardField j)
    rw [h.2] at hh
    simpa only [map_zero, restrictFields_standard] using hh.symm

theorem Endomorphism.restrict_ofField (hVU : V ⊆ U)
    (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)) (hM : ContDiffOn ℝ ∞ M U) :
    (ofField M hM).restrict hVU = ofField M (hM.mono hVU) := by
  unfold Endomorphism.restrict
  apply LinearMap.ext
  intro X
  funext i
  apply Subtype.ext
  funext x
  have hh := field_ofField (ofField M hM).matrix ((ofField M hM).matrix_smooth.mono hVU) X x
  rw [matrix_ofField M hM (⟨x, hVU x.property⟩ : U)] at hh
  have hh' := field_ofField M (hM.mono hVU) X x
  simpa only [field_apply] using congrFun (hh.trans hh'.symm) i

end SemiHamiltonian.Smooth
