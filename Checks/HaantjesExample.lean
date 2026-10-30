module

import SemiHamiltonian

/-! A nonconstant, nondiagonal three-dimensional strictly hyperbolic field.
In ordinary coordinates its matrix is [[1,0,0],[x₀,2,0],[0,0,3]].
This checks the pointwise tensor formula and the complete coordinate theorem. -/

open scoped ContDiff
open SemiHamiltonian SemiHamiltonian.Geometry SemiHamiltonian.Smooth

namespace HaantjesCheck

abbrev E := Fin 3 → ℝ

noncomputable def diag : E →L[ℝ] E := ContinuousLinearMap.pi
  (fun i => ((i.val : ℝ) + 1) • ContinuousLinearMap.proj i)

noncomputable def shearTerm : E →L[ℝ] E :=
  (ContinuousLinearMap.toSpanSingleton ℝ (Pi.single 1 1)).comp (ContinuousLinearMap.proj 0)

noncomputable def A (q : E) : E →L[ℝ] E := diag + q 0 • shearTerm

theorem A_smooth : ContDiff ℝ ∞ A :=
  contDiff_const.add ((ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).contDiff.smul contDiff_const)

theorem A_derivative (q : E) :
    fderiv ℝ A q = (ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).smulRight shearTerm := by
  exact ((ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).hasFDerivAt.smul_const shearTerm
    |>.const_add diag).fderiv

theorem haantjes_zero : MatrixHaantjesVanish A Set.univ := by
  intro q _ v w
  ext k
  fin_cases k <;>
    simp [matrixHaantjes, matrixNijenhuis, A_derivative, A, diag, shearTerm,
      Pi.single_apply, ContinuousLinearMap.smulRight_apply] <;> ring

noncomputable def eigenChange (q : E) : E ≃ₗ[ℝ] E where
  toFun z := ![z 0, z 1 - q 0 * z 0, z 2]
  invFun z := ![z 0, z 1 + q 0 * z 0, z 2]
  left_inv z := by ext i; fin_cases i <;> simp
  right_inv z := by ext i; fin_cases i <;> simp
  map_add' z w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' s z := by ext i; fin_cases i <;> simp <;> ring

theorem hyperbolic (q : E) : StrictHyperbolicAt A q := by
  let b := (Pi.basisFun ℝ (Fin 3)).map (eigenChange q)
  refine ⟨b, fun i => (i.val : ℝ) + 1, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact_mod_cast (add_right_cancel hij)
  · intro i
    ext k
    fin_cases i <;> fin_cases k <;>
      simp [b, Module.Basis.map_apply, Pi.basisFun_apply, eigenChange, A, diag, shearTerm,
        Pi.single_apply] <;> ring

-- Calls the theorem requiring only smoothness, pointwise strict hyperbolicity,
-- and the actual matrix Haantjes tensor. No smooth eigenframe is supplied.
example : LocallyDiagonalizable A Set.univ :=
  (haantjes_iff_locally_diagonalizable isOpen_univ A_smooth.contDiffOn
    (fun q _ => hyperbolic q)).mp haantjes_zero

-- A three-dimensional obstruction: [[1,0,0],[0,2,0],[0,-x₀,3]].
-- Its H(e₀,e₁) has third component 4 at the origin.
noncomputable def twistTerm : E →L[ℝ] E :=
  (ContinuousLinearMap.toSpanSingleton ℝ (Pi.single 2 1)).comp (ContinuousLinearMap.proj 1)

noncomputable def twisted (q : E) : E →L[ℝ] E := diag - q 0 • twistTerm

theorem twisted_smooth : ContDiff ℝ ∞ twisted :=
  contDiff_const.sub ((ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).contDiff.smul contDiff_const)

theorem twisted_derivative (q : E) :
    fderiv ℝ twisted q = -(ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).smulRight twistTerm := by
  have hd := (hasFDerivAt_const diag q).sub
    ((ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).hasFDerivAt.smul_const twistTerm)
  change HasFDerivAt twisted _ q at hd
  simpa only [zero_sub] using hd.fderiv

theorem twisted_obstruction :
    matrixHaantjes twisted 0 (Pi.single 0 1) (Pi.single 1 1) 2 = 4 := by
  norm_num [matrixHaantjes, matrixNijenhuis, twisted_derivative, twisted, diag, twistTerm,
    Pi.single_apply, ContinuousLinearMap.smulRight_apply]

noncomputable def twistedEigenChange (q : E) : E ≃ₗ[ℝ] E where
  toFun z := ![z 0, z 1, z 2 + q 0 * z 1]
  invFun z := ![z 0, z 1, z 2 - q 0 * z 1]
  left_inv z := by ext i; fin_cases i <;> simp
  right_inv z := by ext i; fin_cases i <;> simp
  map_add' z w := by ext i; fin_cases i <;> simp; ring
  map_smul' s z := by ext i; fin_cases i <;> simp; ring

theorem twisted_hyperbolic (q : E) : StrictHyperbolicAt twisted q := by
  let b := (Pi.basisFun ℝ (Fin 3)).map (twistedEigenChange q)
  refine ⟨b, fun i => (i.val : ℝ) + 1, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact_mod_cast (add_right_cancel hij)
  · intro i
    ext k
    fin_cases i <;> fin_cases k <;>
      simp [b, Module.Basis.map_apply, Pi.basisFun_apply, twistedEigenChange,
        twisted, diag, twistTerm]; ring

-- Simple real spectrum alone is insufficient: intrinsic richness would force H = 0.
example : ¬ LocallyRichMatrix (U := Set.univ) twisted_smooth.contDiffOn := by
  intro h
  have hz := h.haantjesVanish (fun q _ => twisted_hyperbolic q) 0 (Set.mem_univ _)
    (Pi.single 0 1) (Pi.single 1 1)
  have hc := congrFun hz 2
  rw [twisted_obstruction] at hc
  norm_num at hc

example : ¬ LocallyDiagonalizable twisted Set.univ := by
  intro hh
  obtain ⟨e, speed, hep, _, he, hi, hv, hd⟩ := hh 0 (Set.mem_univ _)
  have hz := matrixHaantjesVanish_of_diagonalization e he hi twisted_smooth.contDiffOn
    speed hv hd 0 hep (Pi.single 0 1) (Pi.single 1 1)
  have hc := congrFun hz 2
  rw [twisted_obstruction] at hc
  norm_num at hc

-- The independent conservation-law criterion detects the same obstruction.
example : ¬ LocallyRichConservationLaws twisted Set.univ := by
  intro h
  have hz := h.haantjesVanish twisted_smooth.contDiffOn (fun q _ => twisted_hyperbolic q)
    0 (Set.mem_univ _) (Pi.single 0 1) (Pi.single 1 1)
  have hc := congrFun hz 2
  rw [twisted_obstruction] at hc
  norm_num at hc

end HaantjesCheck
