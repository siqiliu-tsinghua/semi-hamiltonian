module

public import SemiHamiltonian.Darboux.C1Operator
public import SemiHamiltonian.Darboux.Uniqueness

/-! Evaluation and actual derivatives of the scaled derivative pairs. -/

@[expose] public section

open scoped NNReal Topology BigOperators
open MeasureTheory Filter

namespace SemiHamiltonian.Darboux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

noncomputable def jetEval (x : Cube ι r) : ScalarJet (ι := ι) r →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ x).comp (ContinuousLinearMap.fst ℝ _ _)

noncomputable def jetDiff (x : Cube ι r) (v : ι → ℝ) : ScalarJet (ι := ι) r →L[ℝ] ℝ :=
  (r : ℝ)⁻¹ • (ContinuousLinearMap.apply ℝ ℝ v).comp
    ((ContinuousMap.evalCLM ℝ x).comp (ContinuousLinearMap.snd ℝ _ _))

omit [DecidableEq ι] in
@[simp] theorem jetEval_apply (x : Cube ι r) (f : ScalarJet (ι := ι) r) : jetEval r x f = f.1 x := rfl

omit [DecidableEq ι] in
@[simp] theorem jetDiff_apply (x : Cube ι r) (v : ι → ℝ) (f : ScalarJet (ι := ι) r) :
    jetDiff r x v f = (r : ℝ)⁻¹ * f.2 x v := rfl

omit [DecidableEq ι] in
theorem jetDiff_mul (x : Cube ι r) (v : ι → ℝ) (f g : ScalarJet (ι := ι) r) :
    jetDiff r x v (jetMul f g) =
      f.1 x * jetDiff r x v g + g.1 x * jetDiff r x v f := by
  simp only [jetDiff_apply, jetMul, ContinuousMap.coe_mk, add_apply, smul_apply, smul_eq_mul]
  ring

omit [DecidableEq ι] in
theorem jetDiff_coordinate (hr : 0 < r) (x : Cube ι r) (v : ι → ℝ) (j : ι) :
    jetDiff r x v (coordinateJet r j) = v j := by
  change (r : ℝ)⁻¹ * ((r : ℝ) * v j) = v j
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (show (0 : ℝ) < r from hr)), one_mul]

theorem jetDiff_radial (i : ι) (t : ℝ) (x : Cube ι r) (v : ι → ℝ)
    (f : ScalarJet (ι := ι) r) :
    jetDiff r x v (radialJet r i t f) = jetDiff r (radial r i t x) (radialLinear i t v) f := rfl

theorem radialLinear_single (i j : ι) (hji : j ≠ i) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    radialLinear i t (Pi.single j 1) = t • Pi.single j 1 := by
  funext k
  rw [radialLinear_apply]
  by_cases hki : k = i
  · subst k
    simp [Ne.symm hji]
  · simp [hki, Set.projIcc_of_mem zero_le_one ht, Pi.smul_apply, smul_eq_mul]

theorem jetDiff_radial_single (i j : ι) (hji : j ≠ i) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Cube ι r) (f : ScalarJet (ι := ι) r) :
    jetDiff r x (Pi.single j 1) (radialJet r i t f) =
      t * jetDiff r (radial r i t x) (Pi.single j 1) f := by
  rw [jetDiff_radial, radialLinear_single i j hji ht]
  simp only [jetDiff_apply, map_smul, smul_eq_mul]
  ring

omit [DecidableEq ι] in
theorem jetEval_integral (x : Cube ι r) (f : ℝ → ScalarJet (ι := ι) r)
    {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, f t).1 x = ∫ t in a..b, (f t).1 x :=
  ((jetEval r x).intervalIntegral_comp_comm hf).symm

omit [DecidableEq ι] in
theorem jetDiff_integral (x : Cube ι r) (v : ι → ℝ) (f : ℝ → ScalarJet (ι := ι) r)
    {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    jetDiff r x v (∫ t in a..b, f t) = ∫ t in a..b, jetDiff r x v (f t) :=
  ((jetDiff r x v).intervalIntegral_comp_comm hf).symm

/-- The fundamental theorem of calculus for a scalar field along a radial path.
It supplies the homotopy identity used to compare the different PDE components. -/
theorem radial_FTC (f : ScalarJet (ι := ι) r) (hf : IsCubeJet r f)
    (i : ι) (x : Cube ι r) (hx : point r x ∈ Metric.ball 0 (r : ℝ)) :
    (∫ t in (0 : ℝ)..1,
      f.1 (radial r i t x) + t * jetDiff r (radial r i t x) (transverse r i x) f) = f.1 x := by
  let W : (ι → ℝ) → ℝ := fun y => f.1 (clamp r y)
  have hvalue (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      W (affineRadial r i x t) = f.1 (radial r i t x) := by
    rw [← point_radial r i x t ht]
    simp only [W, clamp_point]
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
      (fun s => s * W (affineRadial r i x s))
      (f.1 (radial r i t x) + t * jetDiff r (radial r i t x) (transverse r i x) f) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
    have hy : point r (radial r i t x) ∈ Metric.ball 0 (r : ℝ) := by
      rw [point_radialLinear]
      exact radialLinear_maps_ball r i t hx
    have hfd := hf (point r (radial r i t x)) hy
    rw [clamp_point, point_radial r i x t ht'] at hfd
    have hc := hfd.comp_hasDerivAt t (hasDerivAt_affineRadial r i x t)
    have hm := (hasDerivAt_id t).mul hc
    change HasDerivAt (fun s => s * W (affineRadial r i x s))
      (1 * W (affineRadial r i x t) + t * ((r : ℝ)⁻¹ * f.2 (radial r i t x) (transverse r i x))) t at hm
    simpa only [one_mul, hvalue t ht', jetDiff_apply] using hm
  have hc : Continuous (fun t : ℝ =>
      f.1 (radial r i t x) + t * jetDiff r (radial r i t x) (transverse r i x) f) := by
    have hp : Continuous (fun t : ℝ => radial r i t x) :=
      (continuous_radial r i).comp (continuous_id.prodMk continuous_const)
    change Continuous (fun t : ℝ => f.1 (radial r i t x) +
      t * ((r : ℝ)⁻¹ * f.2 (radial r i t x) (transverse r i x)))
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 1)
  simpa only [one_mul, zero_mul, sub_zero,
    hvalue 1 (show (1 : ℝ) ∈ Set.Icc 0 1 by simp), radial_one] using h

end SemiHamiltonian.Darboux
