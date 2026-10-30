module

public import SemiHamiltonian.Geometry.HaantjesCoordinates
public import SemiHamiltonian.Geometry.SmoothEigenframe
public import SemiHamiltonian.Geometry.MatrixTorsion

/-! Haantjes local diagonalization for general smooth strictly hyperbolic matrix fields. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Geometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Haantjes' local coordinate theorem for a general matrix field. Strict
hyperbolicity is required only at the base point. Both the chart and its inverse
are C∞ on fixed open domains; no smooth eigenframe is assumed. -/
theorem haantjes_local_diagonalization {U : Set (ι → ℝ)} (hU : IsOpen U)
    {A : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)} (hA : ContDiffOn ℝ ∞ A U)
    (hH : Smooth.MatrixHaantjesVanish A U) {p : ι → ℝ} (hp : p ∈ U)
    (hs : StrictHyperbolicAt A p) :
    ∃ e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ), ∃ speed : ι → (ι → ℝ) → ℝ,
      p ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ i, ContDiffOn ℝ ∞ (speed i) e.source) ∧
      (∀ q ∈ e.source, Function.Injective (fun i => speed i q)) ∧
      ∀ q ∈ e.source, ∀ z i,
        fderiv ℝ e q (A q z) i = speed i q * fderiv ℝ e q z i := by
  obtain ⟨V, hVU, b, v, hV, hpV, heigen, hgap⟩ := exists_smooth_eigenframe hU hA hp hs
  have hHV : Smooth.MatrixHaantjesVanish A V := fun q hq => hH q (hVU hq)
  have hH' := (Smooth.matrixHaantjesVanish_iff hV (hA.mono hVU)).mp hHV
  obtain ⟨e, hep, heV, hes, hei, hediag⟩ :=
    b.haantjes_local_coordinates hV (Smooth.Endomorphism.ofField A (hA.mono hVU))
      v heigen hgap hH' ⟨p, hpV⟩
  refine ⟨e, fun i => Smooth.extend V (v i), hep, heV.trans hVU, hes, hei,
    fun i => (Smooth.smooth V (v i)).mono heV, ?_, ?_⟩
  · intro q hq i j heq
    by_contra hij
    have hh := (hgap i j hij).map (Smooth.eval (⟨q, heV hq⟩ : V))
    have hn : v i ⟨q, heV hq⟩ - v j ⟨q, heV hq⟩ ≠ 0 := hh.ne_zero
    apply hn
    simpa only [Smooth.extend_apply V (v i) ⟨q, heV hq⟩,
      Smooth.extend_apply V (v j) ⟨q, heV hq⟩, sub_eq_zero] using heq
  · intro q hq z i
    have hh := hediag q hq z i
    rw [Smooth.Endomorphism.matrix_ofField A (hA.mono hVU) ⟨q, heV hq⟩] at hh
    exact hh

end SemiHamiltonian.Geometry
