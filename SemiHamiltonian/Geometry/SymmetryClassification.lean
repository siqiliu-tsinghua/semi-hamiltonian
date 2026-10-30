module

public import SemiHamiltonian.Analysis.SymmetryClassification
public import SemiHamiltonian.Geometry.DiagonalRichness

/-! Classification of all actual hydrodynamic symmetry operator germs in
Riemann coordinates. The representatives are genuine smooth endomorphisms
satisfying the invariant polarized Lie bracket equation. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Smooth

open PSS.FrameData

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}
  (hU : IsOpen U) (S : System hU) (p : U)

omit hU S p in
noncomputable def diagonalMatrix (v : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (diagonalMap v).toContinuousLinearMap

omit hU S p in
theorem diagonalMatrix_apply (v z : ι → ℝ) (i : ι) : diagonalMatrix v z i = v i * z i := rfl

omit hU S p in
theorem diagonalMatrix_injective : Function.Injective (diagonalMatrix (ι := ι)) := by
  intro v w hh
  funext i
  have he := congrArg (fun T : (ι → ℝ) →L[ℝ] (ι → ℝ) => T (Pi.single i 1) i) hh
  simpa only [diagonalMatrix_apply, Pi.single_eq_same, mul_one] using he

omit hU S p in
theorem diagonalMap_matrix_eq (v : ι → Functions U) (x : U) :
    Endomorphism.matrix (diagonalMap v) x = diagonalMatrix (field v x) := by
  ext z i
  rw [diagonalMap_matrix_apply, diagonalMatrix_apply, field_apply]

/-- Normal form for every invariant symmetry, derived from simple spectrum. -/
theorem symmetry_eq_diagonal (B : Endomorphism U)
    (hB : IsHydrodynamicSymmetry hU (diagonalMap S.speed) B) :
    ∃ w : ι → Functions U, S.IsCommutingSpeed w ∧ B = diagonalMap w := by
  let w := fun i => B (scaledBasis i 1) i
  have he : B = diagonalMap w := diagonalMap_eq_of_commute S.speed
    (fun i j hij => S.gap_unit j i hij.symm) B hB.1
  exact ⟨w, (isCommutingSpeed_iff_invariantSymmetry hU S w).mpr (he ▸ hB), he⟩

def HydrodynamicSymmetryGerm :=
  {g : Filter.Germ (𝓝 (p : ι → ℝ)) ((ι → ℝ) →L[ℝ] (ι → ℝ)) //
    ∃ V, ∃ hV : IsOpen V, ∃ hVU : V ⊆ U, (p : ι → ℝ) ∈ V ∧
      ∃ B : Endomorphism V,
        IsHydrodynamicSymmetry hV (diagonalMap (restrictSystem hU hV hVU S).speed) B ∧
          (B.matrix : Filter.Germ (𝓝 (p : ι → ℝ)) ((ι → ℝ) →L[ℝ] (ι → ℝ))) = g}

noncomputable def commutingSpeedToSymmetryGerm (g : CommutingSpeedGerm hU S p) :
    HydrodynamicSymmetryGerm hU S p :=
  ⟨g.val.map diagonalMatrix, by
    obtain ⟨W, hW, hWg⟩ := g.property
    obtain ⟨V, hV, hVU, hpV, w, hw, he⟩ := localCommutingSpeed_section hU S p hW
    refine ⟨V, hV, hVU, hpV, diagonalMap w,
      (isCommutingSpeed_iff_invariantSymmetry hV _ w).mp hw, ?_⟩
    rw [← hWg]
    apply Filter.EventuallyEq.germ_eq
    filter_upwards [hV.mem_nhds hpV] with x hx
    rw [diagonalMap_matrix_eq w ⟨x, hx⟩, he x hx]
    rfl⟩

theorem commutingSpeedToSymmetryGerm_injective :
    Function.Injective (commutingSpeedToSymmetryGerm hU S p) := by
  intro g k hh
  apply Subtype.ext
  obtain ⟨W, hW, hWg⟩ := g.property
  obtain ⟨Z, hZ, hZk⟩ := k.property
  have he := congrArg Subtype.val hh
  change g.val.map diagonalMatrix = k.val.map diagonalMatrix at he
  rw [← hWg, ← hZk] at he ⊢
  apply Filter.EventuallyEq.germ_eq
  have he' : (fun x => diagonalMatrix (W x)) =ᶠ[𝓝 (p : ι → ℝ)]
      (fun x => diagonalMatrix (Z x)) := Filter.Germ.coe_eq.mp he
  exact he'.mono fun x hx => diagonalMatrix_injective hx

theorem commutingSpeedToSymmetryGerm_surjective :
    Function.Surjective (commutingSpeedToSymmetryGerm hU S p) := by
  intro g
  obtain ⟨V, hV, hVU, hpV, B, hB, hBg⟩ := g.property
  obtain ⟨w, hw, hBw⟩ := symmetry_eq_diagonal hV (restrictSystem hU hV hVU S) B hB
  let k : CommutingSpeedGerm hU S p := ⟨(field w : Filter.Germ (𝓝 (p : ι → ℝ)) (ι → ℝ)),
    field w, localCommutingSpeed_of_section hU S p hV hVU hpV w hw, rfl⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  change (field w : Filter.Germ (𝓝 (p : ι → ℝ)) (ι → ℝ)).map diagonalMatrix = g.val
  rw [← hBg, hBw]
  apply Filter.EventuallyEq.germ_eq
  filter_upwards [hV.mem_nhds hpV] with x hx
  exact (diagonalMap_matrix_eq w ⟨x, hx⟩).symm

noncomputable def commutingSpeedSymmetryGermEquiv :
    CommutingSpeedGerm hU S p ≃ HydrodynamicSymmetryGerm hU S p :=
  Equiv.ofBijective (commutingSpeedToSymmetryGerm hU S p)
    ⟨commutingSpeedToSymmetryGerm_injective hU S p,
      commutingSpeedToSymmetryGerm_surjective hU S p⟩

/-- The full invariant symmetry space, including symmetries with repeated
eigenvalues, is classified without repetitions by n arbitrary scalar germs. -/
noncomputable def hydrodynamicSymmetryGermEquiv (hS : S.IsSemiHamiltonian) :
    HydrodynamicSymmetryGerm hU S p ≃ (ι → ScalarGerm 0) :=
  (commutingSpeedSymmetryGermEquiv hU S p).symm.trans (commutingSpeedGermEquiv hU S p hS)

end SemiHamiltonian.Smooth
