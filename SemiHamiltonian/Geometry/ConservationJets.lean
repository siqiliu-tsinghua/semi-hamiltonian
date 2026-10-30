module

public import SemiHamiltonian.Geometry.ScalarCommutator
public import SemiHamiltonian.Geometry.MatrixRichness
public import SemiHamiltonian.Geometry.HaantjesCoordinates

/-! Intrinsic first and second jet freedom of actual conservation laws.
At a critical point the Hessian is a bilinear tensor, so the second-jet
condition does not require a connection or a choice of Riemann coordinates. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U V : Set (ι → ℝ)}

/-- The actual flux equation `dq = dh ∘ M`. -/
def IsMatrixConservationLaw (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (h q : Functions U) : Prop :=
  ∀ p : U, fderiv ℝ (extend U q) p = (fderiv ℝ (extend U h) p).comp (M p)

theorem extend_restrict_eventually (hV : IsOpen V) (hVU : V ⊆ U)
    (f : Functions U) (p : V) :
    extend V (restrict hVU f) =ᶠ[𝓝 (p : ι → ℝ)] extend U f := by
  filter_upwards [hV.mem_nhds p.property] with x hx
  rw [extend_apply V _ (⟨x, hx⟩ : V), restrict_apply,
    extend_apply U _ (⟨x, hVU hx⟩ : U)]

theorem IsMatrixConservationLaw.restrict
    {M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)} {h q : Functions U}
    (hq : IsMatrixConservationLaw M h q) (hV : IsOpen V) (hVU : V ⊆ U) :
    IsMatrixConservationLaw M (restrict hVU h) (restrict hVU q) := by
  intro p
  rw [(extend_restrict_eventually hV hVU q p).fderiv_eq,
    (extend_restrict_eventually hV hVU h p).fderiv_eq]
  exact hq ⟨p, hVU p.property⟩

theorem IsMatrixConservationLaw.frame (hU : IsOpen U)
    {M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)} (hM : ContDiffOn ℝ ∞ M U)
    (b : Frame U) (v : ι → Functions U)
    (heigen : ∀ i, Endomorphism.ofField M hM (b i) = v i • b i)
    {h q : Functions U} (hq : IsMatrixConservationLaw M h q) (i : ι) :
    (b.data hU).deriv i q = v i * (b.data hU).deriv i h := by
  apply Subtype.ext
  funext p
  change fieldDerivation hU (b i) q p = v i p * fieldDerivation hU (b i) h p
  rw [fieldDerivation_eval, fieldDerivation_eval, hq p]
  change fderiv ℝ (extend U h) p (M p (field (b i) p)) = _
  rw [← Endomorphism.field_ofField M hM (b i) p, heigen]
  have hs : field (v i • b i) p = v i p • field (b i) p := by ext a; simp [field_apply]
  rw [hs, map_smul, smul_eq_mul]

end SemiHamiltonian.Smooth

namespace SemiHamiltonian.Geometry

open Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {U V : Set (ι → ℝ)} {M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)}

def RealizesConservationGradients (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (U : Set (ι → ℝ)) (p : ι → ℝ) : Prop :=
  ∀ a : (ι → ℝ) →L[ℝ] ℝ, ∃ h q : Functions U,
    IsMatrixConservationLaw M h q ∧ fderiv ℝ (extend U h) p = a

def RealizesConservationHessians (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (U : Set (ι → ℝ)) (p : ι → ℝ) : Prop :=
  ∀ B : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ,
    (∀ x y, B x y = B y x) → (∀ x y, B (M p x) y = B x (M p y)) →
    ∃ h q : Functions U, IsMatrixConservationLaw M h q ∧
      fderiv ℝ (extend U h) p = 0 ∧ fderiv ℝ (fderiv ℝ (extend U h)) p = B

/-- A finite-jet formulation of the freedom supplied by `n` arbitrary
single-variable functions. The neighbourhood is selected before the jets. -/
def LocallyRichConservationLaws (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (U : Set (ι → ℝ)) : Prop :=
  ∀ p ∈ U, ∃ V, IsOpen V ∧ V ⊆ U ∧ p ∈ V ∧
    RealizesConservationGradients M V p ∧ RealizesConservationHessians M V p

theorem RealizesConservationGradients.restrict (hV : IsOpen V) (hVU : V ⊆ U)
    {p : ι → ℝ} (hp : p ∈ V) (h : RealizesConservationGradients M U p) :
    RealizesConservationGradients M V p := by
  intro a
  obtain ⟨f, q, hq, hf⟩ := h a
  exact ⟨Smooth.restrict hVU f, Smooth.restrict hVU q, hq.restrict hV hVU,
    ((extend_restrict_eventually hV hVU f ⟨p, hp⟩).fderiv_eq).trans hf⟩

theorem RealizesConservationHessians.restrict (hV : IsOpen V) (hVU : V ⊆ U)
    {p : ι → ℝ} (hp : p ∈ V) (h : RealizesConservationHessians M U p) :
    RealizesConservationHessians M V p := by
  intro B hsym hcompat
  obtain ⟨f, q, hq, hf, hff⟩ := h B hsym hcompat
  have he := extend_restrict_eventually hV hVU f ⟨p, hp⟩
  exact ⟨Smooth.restrict hVU f, Smooth.restrict hVU q, hq.restrict hV hVU,
    he.fderiv_eq.trans hf, he.fderiv.fderiv_eq.trans hff⟩

theorem LocallyRichConservationLaws.restrict (hV : IsOpen V) (hVU : V ⊆ U)
    (h : LocallyRichConservationLaws M U) : LocallyRichConservationLaws M V := by
  intro p hp
  obtain ⟨W, hW, hWU, hpW, hg, hh⟩ := h p (hVU hp)
  exact ⟨W ∩ V, hW.inter hV, inter_subset_right, ⟨hpW, hp⟩,
    hg.restrict (hW.inter hV) inter_subset_left ⟨hpW, hp⟩,
    hh.restrict (hW.inter hV) inter_subset_left ⟨hpW, hp⟩⟩

theorem RealizesConservationHessians.noTripleStructure_at
    (hU : IsOpen U) (hM : ContDiffOn ℝ ∞ M U)
    (b : Frame U) (v : ι → Functions U)
    (heigen : ∀ i, Endomorphism.ofField M hM (b i) = v i • b i)
    (hgap : ∀ i j, i ≠ j → IsUnit (v i - v j)) (p : U)
    (h : RealizesConservationHessians M U p)
    (k i j : ι) (hki : k ≠ i) (hkj : k ≠ j) :
    (b.data hU).structureCoeff k i j p = 0 := by
  let a := b.dual k p
  let B := a.smulRight a
  have ha (z : ι → ℝ) : a (M p z) = v k p * a z := by
    have hh := b.dual_eigen (Endomorphism.ofField M hM) v heigen p k z
    rwa [Endomorphism.matrix_ofField] at hh
  obtain ⟨f, q, hq, hf, hff⟩ := h B
    (by intro x y; change a x * a y = a y * a x; ring)
    (by intro x y; change a (M p x) * a y = a x * a (M p y); rw [ha, ha]; ring)
  have hz (r : ι) : eval p ((b.data hU).deriv r f) = 0 := by
    change fieldDerivation hU (b r) f p = 0
    rw [fieldDerivation_eval, hf, zero_apply]
  have hj (r s : ι) : eval p ((b.data hU).deriv r ((b.data hU).deriv s f)) =
      if r = k ∧ s = k then 1 else 0 := by
    change fieldDerivation hU (b r) (fieldDerivation hU (b s) f) p = _
    rw [fieldDerivation_second_at_critical hU _ _ f p hf, hff]
    change b.dual k p (field (b r) p) * b.dual k p (field (b s) p) = _
    rw [b.dual_frame, b.dual_frame]
    by_cases hr : r = k <;> by_cases hs : s = k <;> simp [hr, hs] <;> aesop
  have hv (r : ι) (hkr : k ≠ r) : eval p (v k) ≠ eval p (v r) := by
    have hh := (hgap k r hkr).map (eval p)
    simpa only [map_sub, isUnit_iff_ne_zero, sub_ne_zero] using hh
  exact (b.data hU).structureCoeff_eq_zero_of_conservation_jet
    (b.hasScalarCommutator hU) v f q (hq.frame hU hM b v heigen)
    (eval p) k hz hj i j hki.symm hkj.symm (hv j hkj) (hv i hki)

theorem RealizesConservationHessians.haantjes_zero_at
    (hU : IsOpen U) (hM : ContDiffOn ℝ ∞ M U)
    (b : Frame U) (v : ι → Functions U)
    (heigen : ∀ i, Endomorphism.ofField M hM (b i) = v i • b i)
    (hgap : ∀ i j, i ≠ j → IsUnit (v i - v j)) (p : U)
    (h : RealizesConservationHessians M U p) :
    ∀ x y, matrixHaantjes M p x y = 0 := by
  let A := Endomorphism.ofField M hM
  have hb (i j : ι) : field (haantjes hU A (b i) (b j)) p = 0 := by
    apply b.dual_separates p
    intro r
    rw [b.dual_field, b.haantjes_basis_coordinates hU A v heigen]
    change eval p ((v i - v r) ^ 2 * (v j - v r) ^ 2 * (b.data hU).structureCoeff r i j) = 0
    simp only [map_mul, map_pow, map_sub]
    by_cases hri : r = i
    · subst r; simp
    by_cases hrj : r = j
    · subst r; simp
    · change _ * (b.data hU).structureCoeff r i j p = 0
      rw [h.noTripleStructure_at hU hM b v heigen hgap p r i j hri hrj, mul_zero]
  have hfield (X Y : Fields U) : field (haantjes hU A X Y) p = 0 := by
    rw [← b.sum_equivFun X, ← b.sum_equivFun Y, haantjes_sum_left]
    simp_rw [haantjes_sum_right, haantjes_smul_left, haantjes_smul_right]
    funext k
    have hb' (i j : ι) : haantjes hU A (b i) (b j) k p = 0 := by
      simpa only [field_apply, Pi.zero_apply] using congrFun (hb i j) k
    simp [field_apply, hb']
  intro x y
  have hh := hfield (constantField x) (constantField y)
  rwa [haantjes_ofField_eval hU hM, field_constantField, field_constantField] at hh

/-- Conservation-law freedom produces the missing geometric condition;
diagonalizing coordinates are not assumed. -/
theorem LocallyRichConservationLaws.haantjesVanish
    (hM : ContDiffOn ℝ ∞ M U) (h : LocallyRichConservationLaws M U)
    (hs : ∀ p ∈ U, StrictHyperbolicAt M p) : MatrixHaantjesVanish M U := by
  intro p hp
  obtain ⟨W, hW, hWU, hpW, _, hreal⟩ := h p hp
  obtain ⟨V, hVW, b, v, hV, hpV, heigen, hgap⟩ :=
    exists_smooth_eigenframe hW (hM.mono hWU) hpW (hs p hp)
  exact (hreal.restrict hV hVW hpV).haantjes_zero_at hV
    ((hM.mono hWU).mono hVW) b v heigen hgap ⟨p, hpV⟩

end SemiHamiltonian.Geometry
