module

import SemiHamiltonian

/-! Regression checks for the intrinsic PSS tensor: actual smooth nonconstant
coefficients, a nonintegrable strictly hyperbolic example, and nonlinear chart
conjugation of both examples. -/

open scoped Topology ContDiff Classical
open SemiHamiltonian SemiHamiltonian.Smooth SemiHamiltonian.Geometry

namespace PSSCheck

set_option maxRecDepth 4000

abbrev E := Fin 3 → ℝ
abbrev U : Set E := Set.univ

noncomputable def coord (i : Fin 3) : Functions U :=
  ofContDiffOn (fun x => x i) (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) i).contDiffOn

theorem coord_deriv (i j : Fin 3) :
    (coordinateDerivations isOpen_univ).deriv j (coord i) = if i = j then 1 else 0 := by
  apply Subtype.ext
  funext x
  change directional isOpen_univ (Pi.single j 1) (ofContDiffOn _ _) x = _
  erw [directional_ofContDiffOn,
    (ContinuousLinearMap.proj i : E →L[ℝ] ℝ).hasFDerivAt.fderiv]
  by_cases h : i = j <;> simp [h]

noncomputable def speeds (f : Functions U) (i : Fin 3) : Functions U :=
  f + algebraMap ℝ (Functions U) (i.val : ℝ)

theorem speeds_hyperbolic (f : Functions U) : StrictlyHyperbolic (speeds f) := by
  intro x i j hij hh
  change f x + (i.val : ℝ) = f x + (j.val : ℝ) at hh
  apply hij
  apply Fin.ext
  exact_mod_cast (add_left_cancel hh)

noncomputable def system (f : Functions U) : System (ι := Fin 3) (U := U) isOpen_univ :=
  ofSpeeds isOpen_univ (speeds f) (speeds_hyperbolic f)

noncomputable def diagOp (f : Functions U) : Endomorphism U :=
  PSS.FrameData.diagonalMap (speeds f)

theorem pss_component (f : Functions U) (r a b c : Fin 3) :
    pssTensor isOpen_univ (diagOp f)
      (PSS.FrameData.scaledBasis a 1) (PSS.FrameData.scaledBasis b 1)
      (PSS.FrameData.scaledBasis c 1) r =
      PSS.DiagonalTensor.P (coordinateDerivations isOpen_univ) (speeds f) r a b c := by
  exact pssTensor_diagonal_basis isOpen_univ (speeds f) r a b c

noncomputable def good : Functions U := coord 0 + coord 1 + coord 2
noncomputable def bad : Functions U := coord 1 * coord 2

theorem good_deriv (j : Fin 3) : (coordinateDerivations isOpen_univ).deriv j good = 1 := by
  fin_cases j <;> simp [good, map_add, coord_deriv]

theorem good_pss_zero : PSSVanish isOpen_univ (diagOp good) := by
  apply (semiHamiltonian_iff_pssVanish isOpen_univ (system good)).mp
  apply (PSS.DiagonalTensor.semiHamiltonian_iff_P_zero _ _).mpr
  intro r a b c
  change PSS.DiagonalTensor.P _ (speeds good) r a b c = 0
  rw [PSS.DiagonalTensor.P_eq]
  have hα : PSS.alpha (coordinateDerivations isOpen_univ) (speeds good) a b c = 0 := by
    simp only [PSS.alpha, speeds, map_add, Derivation.map_algebraMap, add_zero,
      good_deriv, Derivation.map_one_eq_zero, mul_zero, zero_sub, mul_one]
    ring
  rw [hα]
  simp

-- In dimension three compatibility is nonvacuous. All three off-diagonal
-- directions are coupled, and the density classification still applies.
noncomputable example (p : U) :
    DensityGerm isOpen_univ (system good) p ≃ (ℝ × (Fin 3 → ScalarGerm 0)) :=
  densityGermEquiv isOpen_univ (system good) p
    ((semiHamiltonian_iff_pssVanish isOpen_univ (system good)).mpr good_pss_zero)

-- P^0_{012}(0) = 8, so the obstruction is genuinely nonzero in dimension three.
theorem bad_component :
    pssTensor isOpen_univ (diagOp bad)
      (PSS.FrameData.scaledBasis 0 1) (PSS.FrameData.scaledBasis 1 1)
      (PSS.FrameData.scaledBasis 2 1) 0 ⟨0, Set.mem_univ _⟩ = 8 := by
  rw [pss_component, PSS.DiagonalTensor.P_target _ _ _ _ _ (by decide) (by decide)]
  simp [PSS.alpha, speeds, bad, map_add, Derivation.leibniz, smul_eq_mul, coord_deriv]
  norm_num [coord, ofContDiffOn]

theorem bad_pss_nonzero : ¬ PSSVanish isOpen_univ (diagOp bad) := by
  intro hh
  have hS := (semiHamiltonian_iff_pssVanish isOpen_univ (system bad)).mpr hh
  have hz := (PSS.DiagonalTensor.semiHamiltonian_iff_P_zero _ _).mp hS 0 0 1 2
  have he := congrArg (fun f : Functions U => f ⟨0, Set.mem_univ _⟩) hz
  change PSS.DiagonalTensor.P (coordinateDerivations isOpen_univ)
    (speeds bad) 0 0 1 2 ⟨0, Set.mem_univ _⟩ = 0 at he
  rw [PSS.DiagonalTensor.P_target _ _ _ _ _ (by decide) (by decide)] at he
  simp [PSS.alpha, speeds, bad, map_add, Derivation.leibniz, smul_eq_mul,
    coord_deriv] at he
  norm_num [coord, ofContDiffOn] at he

theorem matrix_apply (f : Functions U) (x : U) (z : E) (i : Fin 3) :
    (diagOp f).matrix x z i = speeds f i x * z i := by
  have hh := (diagOp f).matrix_field (constantField z) x
  rw [field_constantField] at hh
  have hc := congrFun hh i
  rw [field_apply] at hc
  exact hc

theorem matrix_hyperbolic (f : Functions U) (x : E) :
    StrictHyperbolicAt (diagOp f).matrix x := by
  refine ⟨Pi.basisFun ℝ (Fin 3), fun i => speeds f i ⟨x, Set.mem_univ _⟩, ?_, ?_⟩
  · intro i j h
    by_contra hij
    exact speeds_hyperbolic f ⟨x, Set.mem_univ _⟩ i j hij h
  · intro i
    ext j
    rw [matrix_apply f ⟨x, Set.mem_univ _⟩]
    by_cases h : i = j <;> simp [Pi.basisFun_apply, h, eq_comm]

theorem matrix_haantjes_zero (f : Functions U) : MatrixHaantjesVanish (diagOp f).matrix U := by
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.refl E
  have he : ContDiffOn ℝ ∞ e e.source := contDiffOn_id
  apply matrixHaantjesVanish_of_diagonalization e he he (diagOp f).matrix_smooth
    (fun i => extend U (speeds f i)) (fun i => smooth U (speeds f i))
  intro q hq z i
  change fderiv ℝ id q ((diagOp f).matrix q z) i =
    extend U (speeds f i) q * fderiv ℝ id q z i
  rw [fderiv_id]
  rw [extend_apply U (speeds f i) ⟨q, hq⟩]
  exact matrix_apply f ⟨q, hq⟩ z i

-- End-to-end invocation: the main theorem constructs coordinates and actual
-- arbitrary-data local solutions from the two intrinsic tensor conditions.
theorem good_locally_integrable : LocallyAxisIntegrable (diagOp good).matrix U := by
  apply (pss_iff_locallyAxisIntegrable isOpen_univ (diagOp good).matrix_smooth
    (fun p _ => matrix_hyperbolic good p)).mp
  refine ⟨matrix_haantjes_zero good, ?_⟩
  rw [Endomorphism.ofField_matrix]
  exact good_pss_zero

-- The complete theorem now supplies intrinsic richness in the original variables.
theorem good_locally_rich : LocallyRichMatrix (diagOp good).matrix_smooth :=
  (locallyRichMatrix_iff_locallyAxisIntegrable isOpen_univ (diagOp good).matrix_smooth
    (fun p _ => matrix_hyperbolic good p)).mpr good_locally_integrable

-- The missing sufficiency direction now produces both density jets and fluxes.
theorem good_conservation_rich : LocallyRichConservationLaws (diagOp good).matrix U :=
  locallyRichConservationLaws_of_semiHamiltonian isOpen_univ (system good)
    ((semiHamiltonian_iff_pssVanish isOpen_univ (system good)).mpr good_pss_zero)

example : LocallyOriginalConservationParametrized (diagOp good).matrix U :=
  (locallyRichConservationLaws_iff_originalParametrized isOpen_univ (diagOp good).matrix_smooth
    (fun p _ => matrix_hyperbolic good p)).mp good_conservation_rich

example : LocallySemiHamiltonian (diagOp good).matrix U :=
  (locallyRichMatrix_iff_locallySemiHamiltonian isOpen_univ (diagOp good).matrix_smooth
    (fun p _ => matrix_hyperbolic good p)).mp good_locally_rich

-- A nonzero P rules out even the weaker, purely intrinsic richness premise.
example : ¬ LocallyRichMatrix (diagOp bad).matrix_smooth := by
  intro h
  have hp := ((locallyRichMatrix_iff_tensors isOpen_univ (diagOp bad).matrix_smooth
    (fun p _ => matrix_hyperbolic bad p)).mp h).2
  rw [Endomorphism.ofField_matrix] at hp
  exact bad_pss_nonzero hp

example : ¬ LocallyAxisIntegrable (diagOp bad).matrix U := by
  intro h
  have hp := (tensors_of_locallyAxisIntegrable isOpen_univ (diagOp bad).matrix_smooth h).2
  rw [Endomorphism.ofField_matrix] at hp
  exact bad_pss_nonzero hp

-- A genuinely nonlinear change of dependent variables.
example : ¬ LocallyRichConservationLaws (diagOp bad).matrix U := by
  intro h
  have hp := (h.tensors_vanish isOpen_univ (diagOp bad).matrix_smooth
    (fun p _ => matrix_hyperbolic bad p)).2
  rw [Endomorphism.ofField_matrix] at hp
  exact bad_pss_nonzero hp

example : ¬ LocallyOriginalConservationParametrized (diagOp bad).matrix U := by
  intro hh
  have h := (locallyRichConservationLaws_iff_originalParametrized isOpen_univ (diagOp bad).matrix_smooth
    (fun p _ => matrix_hyperbolic bad p)).mpr hh
  have hp := (h.tensors_vanish isOpen_univ (diagOp bad).matrix_smooth
    (fun p _ => matrix_hyperbolic bad p)).2
  rw [Endomorphism.ofField_matrix] at hp
  exact bad_pss_nonzero hp

def shear (x : E) : E := fun i => if i = 1 then x 1 + (x 0) ^ 2 else x i
def unshear (x : E) : E := fun i => if i = 1 then x 1 - (x 0) ^ 2 else x i

theorem shear_smooth : ContDiff ℝ ∞ shear := by
  apply contDiff_pi.mpr
  intro i
  by_cases h : i = 1
  · subst i
    exact (show ContDiff ℝ ∞ (fun x : E => x 1 + (x 0) ^ 2) from
      (ContinuousLinearMap.proj 1 : E →L[ℝ] ℝ).contDiff.add
        ((ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).contDiff.pow 2))
  · simp only [shear, h, ↓reduceIte]
    exact contDiff_apply ℝ (fun _ : Fin 3 => ℝ) i

theorem unshear_smooth : ContDiff ℝ ∞ unshear := by
  apply contDiff_pi.mpr
  intro i
  by_cases h : i = 1
  · subst i
    exact (show ContDiff ℝ ∞ (fun x : E => x 1 - (x 0) ^ 2) from
      (ContinuousLinearMap.proj 1 : E →L[ℝ] ℝ).contDiff.sub
        ((ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).contDiff.pow 2))
  · simp only [unshear, h, ↓reduceIte]
    exact contDiff_apply ℝ (fun _ : Fin 3 => ℝ) i

noncomputable def chart : OpenPartialHomeomorph E E :=
  Homeomorph.toOpenPartialHomeomorph
    { toFun := shear
      invFun := unshear
      left_inv := by intro x; ext i; fin_cases i <;> simp [shear, unshear]
      right_inv := by intro x; ext i; fin_cases i <;> simp [shear, unshear]
      continuous_toFun := shear_smooth.continuous
      continuous_invFun := unshear_smooth.continuous }

theorem chart_smooth : ContDiffOn ℝ ∞ chart chart.source := shear_smooth.contDiffOn
theorem inverse_smooth : ContDiffOn ℝ ∞ chart.symm chart.target := unshear_smooth.contDiffOn

noncomputable def transformed (f : Functions U) : Endomorphism U :=
  chartEndomorphism chart.symm inverse_smooth chart_smooth (diagOp f)

theorem transformed_conservation_rich : LocallyRichConservationLaws (transformed good).matrix U := by
  apply good_conservation_rich.chart chart.symm inverse_smooth chart_smooth
  intro q z
  exact chartEndomorphism_matrix_intertwines chart.symm inverse_smooth chart_smooth (diagOp good) q z

theorem transformed_diagonalization (q : chart.source) (z : E) (i : Fin 3) :
    fderiv ℝ chart q ((transformed good).matrix q z) i =
      (system good).speed i ⟨chart q, chart.map_source q.property⟩ * fderiv ℝ chart q z i := by
  have hh := chart_intertwining_symm chart.symm inverse_smooth chart_smooth
    (fun r z => chartEndomorphism_matrix_intertwines chart.symm inverse_smooth chart_smooth (diagOp good) r z) q z
  exact (congrFun hh i).trans
    (matrix_apply good ⟨chart q, chart.map_source q.property⟩ (fderiv ℝ chart q z) i)

-- Nonlinear coordinate change, genuine coupling and nonpolynomial data.
noncomputable def conservationData : Fin 3 → ScalarGerm 0 := fun i =>
  if i = 0 then ⟨(Real.sin : Filter.Germ (𝓝 (0 : ℝ)) ℝ), Real.sin, Real.contDiff_sin, rfl⟩
  else ⟨(Real.exp : Filter.Germ (𝓝 (0 : ℝ)) ℝ), Real.exp, Real.contDiff_exp, rfl⟩

example (p : chart.source) : ∃! g : MatrixDensityGerm (transformed good).matrix U p,
    originalConservationData chart chart_smooth inverse_smooth (system good)
      (fun _ hx => hx) transformed_diagonalization p g = (7, conservationData) := by
  let E := originalConservationGermEquiv chart chart_smooth inverse_smooth (system good)
    (fun _ hx => hx) transformed_diagonalization p
    (densityGermData_bijective isOpen_univ (system good) ⟨chart p, chart.map_source p.property⟩
      ((semiHamiltonian_iff_pssVanish isOpen_univ (system good)).mpr good_pss_zero))
  exact ⟨E.symm (7, conservationData), E.apply_symm_apply _,
    fun g hg => E.injective (hg.trans (E.apply_symm_apply _).symm)⟩

-- The intrinsic richness property survives an actual nonlinear coordinate change.
example : LocallyRichMatrix (transformed good).matrix_smooth := by
  apply good_locally_rich.chart chart.symm inverse_smooth chart_smooth
    (diagOp good).matrix_smooth (transformed good).matrix_smooth
  intro q z
  exact chartEndomorphism_matrix_intertwines chart.symm inverse_smooth chart_smooth
    (diagOp good) q z

-- Nonlinear conjugation produces nondiagonal matrix fields while preserving the test.
example : PSSVanish isOpen_univ (transformed good) :=
  (pssVanish_conjugate_iff chart.symm inverse_smooth chart_smooth (diagOp good)).mp good_pss_zero

example : ¬ PSSVanish isOpen_univ (transformed bad) := by
  intro hh
  exact bad_pss_nonzero
    ((pssVanish_conjugate_iff chart.symm inverse_smooth chart_smooth (diagOp bad)).mpr hh)

-- Actual commuting speeds give actual original-coordinate symmetry operators.
example (w : Fin 3 → Functions U) (hw : (system good).IsCommutingSpeed w) :
    IsHydrodynamicSymmetry isOpen_univ (transformed good)
      (chartEndomorphism chart.symm inverse_smooth chart_smooth (PSS.FrameData.diagonalMap w)) :=
  (hydrodynamicSymmetry_conjugate_iff chart.symm inverse_smooth chart_smooth (diagOp good)
    (PSS.FrameData.diagonalMap w)).mp
      ((isCommutingSpeed_iff_invariantSymmetry isOpen_univ (system good) w).mp hw)

end PSSCheck
