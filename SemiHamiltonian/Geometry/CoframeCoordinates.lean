module

public import SemiHamiltonian.Geometry.FirstIntegral

/-! Simultaneous local coordinates for a Frobenius coframe. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Geometry

theorem isInvertible_of_injective {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : E →L[ℝ] E) (hL : Function.Injective L) : L.IsInvertible := by
  refine ⟨(LinearEquiv.ofInjectiveEndo L.toLinearMap hL).toContinuousLinearEquiv, ?_⟩
  ext v
  rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Independent integrable one-forms admit simultaneous smooth local coordinates. -/
theorem frobenius_coframe_coordinates {U : Set (ι → ℝ)} (hU : IsOpen U)
    {α : ι → (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ}
    (hα : ∀ i, ContDiffOn ℝ ∞ (α i) U)
    (hc : ∀ i, FrobeniusOneForm (α i) U) {p : ι → ℝ} (hp : p ∈ U)
    (hi : (ContinuousLinearMap.pi (fun i => α i p)).IsInvertible) :
    ∃ e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ),
      p ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ q ∈ e.source, ∀ v i, fderiv ℝ e q v i = 0 ↔ α i q v = 0 := by
  obtain ⟨L, hL⟩ := hi
  have hn (i : ι) : α i p ≠ 0 := by
    intro hz
    have hh := congrArg (fun z : ι → ℝ => z i) (L.apply_symm_apply (Pi.single i 1))
    have ha : L.toContinuousLinearMap = ContinuousLinearMap.pi (fun i => α i p) := hL
    change L.toContinuousLinearMap (L.symm (Pi.single i 1)) i = _ at hh
    rw [ha] at hh
    simp [hz] at hh
  choose W f hW hpW hWU hf hk using fun i =>
    frobenius_first_integral hU (hα i) (hc i) hp (hn i)
  let V := ⋂ i, W i
  have hV : IsOpen V := isOpen_iInter_of_finite hW
  have hpV : p ∈ V := mem_iInter.mpr hpW
  let G : (ι → ℝ) → (ι → ℝ) := fun q i => f i q
  have hG : ContDiffOn ℝ ∞ G V :=
    contDiffOn_pi.mpr (fun i => (hf i).mono (iInter_subset W i))
  have hGd (q : ι → ℝ) (hq : q ∈ V) : fderiv ℝ G q =
      ContinuousLinearMap.pi (fun i => fderiv ℝ (f i) q) := by
    exact fderiv_pi (fun i => ((hf i).contDiffAt
      ((hW i).mem_nhds (mem_iInter.mp hq i))).differentiableAt (by simp))
  have hGker (q : ι → ℝ) (hq : q ∈ V) (v : ι → ℝ) (i : ι) :
      fderiv ℝ G q v i = 0 ↔ α i q v = 0 := by
    rw [hGd q hq]
    exact hk i q (mem_iInter.mp hq i) v
  have hGi : (fderiv ℝ G p).IsInvertible := by
    apply isInvertible_of_injective
    apply (fderiv ℝ G p).ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply L.injective
    rw [map_zero]
    change L.toContinuousLinearMap v = 0
    rw [hL]
    funext i
    exact (hGker p hpV v i).mp (congrFun hv i)
  obtain ⟨e, he, hep, heV, hes, hei⟩ := exists_smooth_local_inverse hV hG hpV hGi
  refine ⟨e, hep, ?_, hes, hei, ?_⟩
  · intro q hq
    -- The extra intersection with U also covers the zero-dimensional case.
    by_cases hι : Nonempty ι
    · obtain ⟨i⟩ := hι
      exact hWU i (mem_iInter.mp (heV hq) i)
    · have hqp : q = p := by ext i; exact (hι ⟨i⟩).elim
      simpa [hqp] using hp
  · intro q hq v i
    rw [he]
    exact hGker q (heV hq) v i

/-- Applying the coframe theorem to left eigenforms gives the actual derivative
conjugacy to a diagonal matrix field. -/
theorem coframe_local_diagonalization {U : Set (ι → ℝ)} (hU : IsOpen U)
    {α : ι → (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ}
    (hα : ∀ i, ContDiffOn ℝ ∞ (α i) U)
    (hc : ∀ i, FrobeniusOneForm (α i) U)
    {A : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ)} {speed : ι → (ι → ℝ) → ℝ}
    (heigen : ∀ q ∈ U, ∀ i v, α i q (A q v) = speed i q * α i q v)
    {p : ι → ℝ} (hp : p ∈ U)
    (hi : (ContinuousLinearMap.pi (fun i => α i p)).IsInvertible) :
    ∃ e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ),
      p ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ q ∈ e.source, ∀ v i, fderiv ℝ e q (A q v) i = speed i q * fderiv ℝ e q v i := by
  obtain ⟨e, hep, heU, hes, hei, hk⟩ := frobenius_coframe_coordinates hU hα hc hp hi
  refine ⟨e, hep, heU, hes, hei, ?_⟩
  intro q hq v i
  have ha : α i q (A q v - speed i q • v) = 0 := by
    rw [map_sub, map_smul, heigen q (heU hq) i v, smul_eq_mul, sub_self]
  have hh := (hk q hq (A q v - speed i q • v) i).mpr ha
  simpa only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero] using hh

end SemiHamiltonian.Geometry

