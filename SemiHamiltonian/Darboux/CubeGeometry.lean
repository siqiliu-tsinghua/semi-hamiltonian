module

public import SemiHamiltonian.Darboux.Cube
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Normed.Module.Basic

/-! The ambient normed space and linear radial contractions of a coordinate cube. -/

@[expose] public section

open scoped NNReal

namespace SemiHamiltonian.Darboux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

noncomputable def clamp : C(ι → ℝ, Cube ι r) where
  toFun x i := Set.projIcc (-(r : ℝ)) r (neg_le_self r.coe_nonneg) (x i)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact (continuous_projIcc (h := neg_le_self r.coe_nonneg)).comp (continuous_apply i)

omit [DecidableEq ι] in
theorem point_clamp_of_norm_le {x : ι → ℝ} (hx : ‖x‖ ≤ r) :
    point r (clamp r x) = x := by
  funext i
  have hi : x i ∈ Set.Icc (-(r : ℝ)) r := abs_le.mp ((norm_le_pi_norm x i).trans hx)
  simp only [point, clamp, ContinuousMap.coe_mk,
    Set.projIcc_of_mem (neg_le_self r.coe_nonneg) hi]

theorem norm_point_le (x : Cube ι r) : ‖point r x‖ ≤ r := by
  apply (pi_norm_le_iff_of_nonneg r.coe_nonneg).mpr
  intro i
  exact abs_coordinate_le r x i

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem clamp_point (x : Cube ι r) : clamp r (point r x) = x := by
  funext i
  simp only [clamp, point, ContinuousMap.coe_mk,
    Set.projIcc_of_mem (neg_le_self r.coe_nonneg) (x i).property]

noncomputable def radialLinear (i : ι) (t : ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    (if j = i then (1 : ℝ) else (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ)) •
      ContinuousLinearMap.proj j

omit [Fintype ι] in
theorem radialLinear_apply (i j : ι) (t : ℝ) (x : ι → ℝ) :
    radialLinear i t x j = if j = i then x j else
      (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) * x j := by
  by_cases h : j = i <;> simp [radialLinear, h]

theorem radialLinear_norm_le (i : ι) (t : ℝ) : ‖radialLinear i t‖ ≤ 1 := by
  apply (radialLinear i t).opNorm_le_bound (by norm_num)
  intro x
  simp only [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro j
  rw [radialLinear_apply]
  split_ifs with h
  · exact norm_le_pi_norm x j
  · rw [norm_mul]
    have ht := (Set.projIcc (0 : ℝ) 1 zero_le_one t).property
    have hn : ‖(Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact ht.2
    exact (mul_le_mul hn (norm_le_pi_norm x j) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem radialLinear_maps_ball (i : ι) (t : ℝ) :
    Set.MapsTo (radialLinear i t) (Metric.ball 0 (r : ℝ)) (Metric.ball 0 (r : ℝ)) := by
  intro x hx
  simp only [Metric.mem_ball, dist_zero_right] at hx ⊢
  exact ((radialLinear i t).le_opNorm x |>.trans
    (mul_le_mul_of_nonneg_right (radialLinear_norm_le i t) (norm_nonneg x))).trans_lt
    (by simpa using hx)

noncomputable def radialMap (i : ι) (t : ℝ) : C(Cube ι r, Cube ι r) :=
  ⟨radial r i t, (continuous_radial r i).comp (continuous_const.prodMk continuous_id)⟩

theorem point_radialLinear (i : ι) (t : ℝ) (x : Cube ι r) :
    point r (radial r i t x) = radialLinear i t (point r x) := by
  funext j
  rw [radialLinear_apply]
  by_cases h : j = i <;> simp [point, radial, h]

theorem radial_clamp (i : ι) (t : ℝ) {x : ι → ℝ} (hx : x ∈ Metric.ball 0 (r : ℝ)) :
    radialMap r i t (clamp r x) = clamp r (radialLinear i t x) := by
  have hxn : ‖x‖ ≤ r := (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
  have hB := radialLinear_maps_ball r i t hx
  have hBn : ‖radialLinear i t x‖ ≤ r :=
    (by simpa only [Metric.mem_ball, dist_zero_right] using hB : ‖radialLinear i t x‖ < r).le
  apply funext
  intro j
  apply Subtype.ext
  have h := point_radialLinear r i t (clamp r x)
  rw [point_clamp_of_norm_le r hxn] at h
  have h' := point_clamp_of_norm_le r hBn
  exact (congrFun h j).trans (congrFun h' j).symm

end SemiHamiltonian.Darboux
