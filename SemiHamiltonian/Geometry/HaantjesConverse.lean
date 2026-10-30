module

public import SemiHamiltonian.Geometry.CoordinateFrame
public import SemiHamiltonian.Geometry.HaantjesLocal

/-! Necessity and the local equivalence in Haantjes' coordinate theorem. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Geometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Any smoothly diagonalizable matrix field has zero Haantjes tensor.
Distinct eigenvalues are not needed for this direction. -/
theorem matrixHaantjesVanish_of_diagonalization
    (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {A : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)} (hA : ContDiffOn ℝ ∞ A e.source)
    (speed : ι → (ι → ℝ) → ℝ) (hv : ∀ i, ContDiffOn ℝ ∞ (speed i) e.source)
    (hd : ∀ q ∈ e.source, ∀ z i,
      fderiv ℝ e q (A q z) i = speed i q * fderiv ℝ e q z i) :
    Smooth.MatrixHaantjesVanish A e.source := by
  obtain ⟨b, hb, hbr⟩ := exists_coordinate_frame e he hi
  let v : ι → Smooth.Functions e.source := fun i => Smooth.ofContDiffOn (speed i) (hv i)
  let M := Smooth.Endomorphism.ofField A hA
  have hAe (i : ι) (x : e.source) :
      A x (Smooth.field (b i) x) = speed i x • Smooth.field (b i) x := by
    apply chart_fderiv_injective e he hi x.property
    ext j
    rw [hd x x.property, map_smul, hb]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    by_cases hij : i = j
    · subst j; simp
    · simp [hij, Ne.symm hij]
  have heigen (i : ι) : M (b i) = v i • b i := by
    funext k
    apply Subtype.ext
    funext x
    have hh := Smooth.Endomorphism.field_ofField A hA (b i) x
    rw [hAe] at hh
    change M (b i) k x = speed i x • b i k x
    simpa only [Smooth.field_apply, Pi.smul_apply] using congrFun hh k
  apply (Smooth.matrixHaantjesVanish_iff e.open_source hA).mpr
  apply (b.haantjesVanish_iff_components e.open_source M v heigen).mpr
  intro i j r
  rw [(b.data e.open_source).haantjes_basis]
  simp only [Smooth.Frame.data, hbr, map_zero, Pi.zero_apply, mul_zero]

/-- A genuine local diagonalization, including smooth inverse and smooth diagonal entries. -/
def LocallyDiagonalizable (A : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (U : Set (ι → ℝ)) : Prop :=
  ∀ p ∈ U, ∃ e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ),
    ∃ speed : ι → (ι → ℝ) → ℝ,
      p ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ i, ContDiffOn ℝ ∞ (speed i) e.source) ∧
      ∀ q ∈ e.source, ∀ z i,
        fderiv ℝ e q (A q z) i = speed i q * fderiv ℝ e q z i

/-- Haantjes' coordinate criterion for a general C∞ strictly hyperbolic matrix field. -/
theorem haantjes_iff_locally_diagonalizable {U : Set (ι → ℝ)} (hU : IsOpen U)
    {A : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)} (hA : ContDiffOn ℝ ∞ A U)
    (hs : ∀ p ∈ U, StrictHyperbolicAt A p) :
    Smooth.MatrixHaantjesVanish A U ↔ LocallyDiagonalizable A U := by
  constructor
  · intro hH p hp
    obtain ⟨e, v, hep, heU, he, hi, hv, _, hd⟩ :=
      haantjes_local_diagonalization hU hA hH hp (hs p hp)
    exact ⟨e, v, hep, heU, he, hi, hv, hd⟩
  · intro hdiag p hp
    obtain ⟨e, v, hep, heU, he, hi, hv, hd⟩ := hdiag p hp
    exact matrixHaantjesVanish_of_diagonalization e he hi (hA.mono heU) v hv hd p hep

end SemiHamiltonian.Geometry
