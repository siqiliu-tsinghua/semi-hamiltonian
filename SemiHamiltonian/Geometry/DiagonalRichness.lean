module

public import SemiHamiltonian.Geometry.MatrixRichness
public import SemiHamiltonian.PSS.DiagonalCentralizer

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Smooth

open PSS.FrameData

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U V : Set (ι → ℝ)}

theorem diagonalMap_matrix_apply (v : ι → Functions U) (p : U) (z : ι → ℝ) (i : ι) :
    Endomorphism.matrix (diagonalMap v) p z i = v i p * z i := by
  have hh := Endomorphism.matrix_field (diagonalMap v) (constantField z) p
  rw [field_constantField] at hh
  have hi := congrFun hh i
  rw [field_apply] at hi
  exact hi

theorem Endomorphism.restrict_diagonalMap (hVU : V ⊆ U) (v : ι → Functions U) :
    Endomorphism.restrict hVU (diagonalMap v) = diagonalMap (fun i => Smooth.restrict hVU (v i)) := by
  apply LinearMap.ext
  intro X
  funext i
  apply Subtype.ext
  funext p
  have hh := Endomorphism.field_ofField (Endomorphism.matrix (diagonalMap v))
    ((Endomorphism.matrix_smooth (diagonalMap v)).mono hVU) X p
  have hi := congrFun hh i
  rw [diagonalMap_matrix_apply v ⟨p, hVU p.property⟩, field_apply] at hi
  change Endomorphism.ofField (Endomorphism.matrix (diagonalMap v)) _ X i p =
    Smooth.restrict hVU (v i) p * X i p
  rw [Smooth.restrict_apply]
  simpa only [field_apply] using hi

theorem ofField_diagonal_restrict (hVU : V ⊆ U) (v : ι → Functions U) :
    Endomorphism.ofField (Endomorphism.matrix (diagonalMap v))
      ((Endomorphism.matrix_smooth (diagonalMap v)).mono hVU) =
      diagonalMap (fun i => Smooth.restrict hVU (v i)) :=
  Endomorphism.restrict_diagonalMap hVU v

end SemiHamiltonian.Smooth

namespace SemiHamiltonian.Geometry

open Smooth PSS.FrameData

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)} (hU : IsOpen U)

/-- The intrinsic definition agrees with the actual local Tsarev solution definition. -/
theorem locallyRichMatrix_iff_locallyRich (S : System hU) :
    LocallyRichMatrix (Endomorphism.matrix_smooth (diagonalMap S.speed)) ↔ LocallyRich hU S := by
  constructor
  · intro h p
    obtain ⟨V, hV, hVU, hpV, hreal⟩ := h p p.property
    let SV := restrictSystem hU hV hVU S
    refine ⟨V, hV, hVU, hpV, ?_⟩
    intro a
    let c : ι → Functions V := fun i => algebraMap ℝ (Functions V) (a i)
    let C : Endomorphism V := diagonalMap c
    have hc : Function.Commute (Endomorphism.matrix (diagonalMap S.speed) p) (C.matrix p) := by
      intro z
      funext i
      simp only [C, diagonalMap_matrix_apply S.speed p,
        diagonalMap_matrix_apply c ⟨p, hpV⟩]
      ring
    obtain ⟨B, hB, hval⟩ := hreal (C.matrix p) hc
    rw [ofField_diagonal_restrict] at hB
    change IsHydrodynamicSymmetry hV (diagonalMap SV.speed) B at hB
    let w := fun i => B (scaledBasis i 1) i
    have he : B = diagonalMap w := diagonalMap_eq_of_commute SV.speed
      (fun i j hij => SV.gap_unit j i hij.symm) B hB.1
    refine ⟨w, (isCommutingSpeed_iff_invariantSymmetry hV SV w).mpr (he ▸ hB), ?_⟩
    intro i
    rw [he] at hval
    have hh := congrArg (fun T : (ι → ℝ) →L[ℝ] (ι → ℝ) => T (Pi.single i 1) i) hval
    rw [diagonalMap_matrix_apply w ⟨p, hpV⟩, diagonalMap_matrix_apply c ⟨p, hpV⟩] at hh
    simpa [c, Algebra.algebraMap_eq_smul_one] using hh
  · intro h p hp
    obtain ⟨V, hV, hVU, hpV, hsol⟩ := h ⟨p, hp⟩
    let SV := restrictSystem hU hV hVU S
    refine ⟨V, hV, hVU, hpV, ?_⟩
    intro T hT
    let v : ι → ℝ := fun i => S.speed i ⟨p, hp⟩
    have hgap (i j : ι) (hij : i ≠ j) : IsUnit (v i - v j) := by
      change IsUnit (eval ⟨p, hp⟩ (S.speed i - S.speed j))
      exact (S.gap_unit j i hij.symm).map (eval ⟨p, hp⟩)
    have hv : Endomorphism.matrix (diagonalMap S.speed) p = (diagonalMap v).toContinuousLinearMap := by
      ext z i
      exact diagonalMap_matrix_apply S.speed ⟨p, hp⟩ z i
    have hc : Function.Commute (diagonalMap v) T.toLinearMap := by
      intro z
      have hh := hT z
      rw [hv] at hh
      exact hh
    let a := fun i => T (scaledBasis i 1) i
    have he : T.toLinearMap = diagonalMap a := diagonalMap_eq_of_commute v hgap T.toLinearMap hc
    obtain ⟨w, hw, hval⟩ := hsol a
    refine ⟨diagonalMap w, ?_, ?_⟩
    · rw [ofField_diagonal_restrict]
      exact (isCommutingSpeed_iff_invariantSymmetry hV SV w).mp hw
    · ext z i
      rw [diagonalMap_matrix_apply w ⟨p, hpV⟩, hval]
      exact (congrArg (fun L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) => L z i) he).symm

end SemiHamiltonian.Geometry
