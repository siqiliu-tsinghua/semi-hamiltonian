module

public import SemiHamiltonian.Darboux.JetCalculus

/-! Radial homotopy of a row of scalar one-form coefficients. -/

@[expose] public section

open scoped NNReal Topology BigOperators
open MeasureTheory

namespace SemiHamiltonian.Darboux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

noncomputable def rowHomotopy (i : ι) (F : JetValues (ι := ι) r) : ScalarJet (ι := ι) r :=
  ∑ k, if k = i then 0 else jetMul (coordinateJet r k) (∫ t in (0 : ℝ)..1, radialJet r i t (F k))

theorem continuous_radial_value (i : ι) (x : Cube ι r) (f : ScalarJet (ι := ι) r) :
    Continuous (fun t => f.1 (radial r i t x)) :=
  f.1.continuous.comp ((continuous_radial r i).comp (continuous_id.prodMk continuous_const))

theorem continuous_radial_diff (i : ι) (x : Cube ι r) (v : ι → ℝ) (f : ScalarJet (ι := ι) r) :
    Continuous (fun t => jetDiff r (radial r i t x) v f) := by
  have hp : Continuous (fun t : ℝ => radial r i t x) :=
    (continuous_radial r i).comp (continuous_id.prodMk continuous_const)
  simp only [jetDiff_apply]
  fun_prop

theorem jetDiff_transverse (i : ι) (x y : Cube ι r) (f : ScalarJet (ι := ι) r) :
    jetDiff r y (transverse r i x) f =
      ∑ k, if k = i then 0 else (x k : ℝ) * jetDiff r y (Pi.single k 1) f := by
  exact linearMap_transverse r ((r : ℝ)⁻¹ • f.2 y) i x

theorem rowHomotopy_diff (hr : 0 < r) (i j : ι) (hji : j ≠ i)
    (F : JetValues (ι := ι) r) (x : Cube ι r) :
    jetDiff r x (Pi.single j 1) (rowHomotopy r i F) =
      (∫ t in (0 : ℝ)..1, (F j).1 (radial r i t x)) +
      ∑ k, if k = i then 0 else (x k : ℝ) *
        ∫ t in (0 : ℝ)..1, t * jetDiff r (radial r i t x) (Pi.single j 1) (F k) := by
  have hterm (k : ι) :
      jetDiff r x (Pi.single j 1)
        (jetMul (coordinateJet r k) (∫ t in (0 : ℝ)..1, radialJet r i t (F k))) =
      (x k : ℝ) * (∫ t in (0 : ℝ)..1, t * jetDiff r (radial r i t x) (Pi.single j 1) (F k)) +
        (if k = j then (∫ t in (0 : ℝ)..1, (F k).1 (radial r i t x)) else 0) := by
    rw [jetDiff_mul, jetDiff_coordinate r hr,
      jetDiff_integral r x _ _ ((continuous_radialJet r i (F k)).intervalIntegrable 0 1),
      jetEval_integral r x _ ((continuous_radialJet r i (F k)).intervalIntegrable 0 1)]
    have he : (∫ t in (0 : ℝ)..1, jetDiff r x (Pi.single j 1) (radialJet r i t (F k))) =
        ∫ t in (0 : ℝ)..1, t * jetDiff r (radial r i t x) (Pi.single j 1) (F k) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact jetDiff_radial_single r i j hji (by simpa using ht) x (F k)
    rw [he]
    by_cases hkj : k = j <;> simp [coordinateJet, hkj, radialJet, jetPull, radialMap]
  rw [rowHomotopy, map_sum]
  calc
    _ = (∑ k : ι, if k = i then 0 else (x k : ℝ) *
        ∫ t in (0 : ℝ)..1, t * jetDiff r (radial r i t x) (Pi.single j 1) (F k)) +
        ∑ k : ι, if k = i then 0 else
          (if k = j then (∫ t in (0 : ℝ)..1, (F k).1 (radial r i t x)) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hki : k = i
      · simp [hki]
      · simp only [hki, ite_false]
        exact hterm k
    _ = _ := by
      have he : (∑ k : ι, if k = i then 0 else
          (if k = j then (∫ t in (0 : ℝ)..1, (F k).1 (radial r i t x)) else 0)) =
          ∫ t in (0 : ℝ)..1, (F j).1 (radial r i t x) := by
        rw [Finset.sum_eq_single j]
        · simp [hji]
        · intro k _ hkj
          by_cases hki : k = i <;> simp [hki, hkj]
        · simp
      rw [he, add_comm]

theorem radial_FTC_expanded (f : ScalarJet (ι := ι) r) (hf : IsCubeJet r f)
    (i : ι) (x : Cube ι r) (hx : point r x ∈ Metric.ball 0 (r : ℝ)) :
    f.1 x = (∫ t in (0 : ℝ)..1, f.1 (radial r i t x)) +
      ∑ k, if k = i then 0 else (x k : ℝ) *
        ∫ t in (0 : ℝ)..1, t * jetDiff r (radial r i t x) (Pi.single k 1) f := by
  have ht (k : ι) : IntervalIntegrable
      (fun t => t * jetDiff r (radial r i t x) (Pi.single k 1) f) volume 0 1 :=
    (continuous_id.mul (continuous_radial_diff r i x (Pi.single k 1) f)).intervalIntegrable 0 1
  have htrans : IntervalIntegrable
      (fun t : ℝ => t * jetDiff r (radial r i t x) (transverse r i x) f) volume 0 1 :=
    (continuous_id.mul (continuous_radial_diff r i x (transverse r i x) f)).intervalIntegrable 0 1
  rw [← radial_FTC r f hf i x hx]
  rw [intervalIntegral.integral_add ((continuous_radial_value r i x f).intervalIntegrable 0 1)
    htrans]
  congr 1
  simp_rw [jetDiff_transverse, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    by_cases hki : k = i
    · simp [hki]
    · simp only [hki, ite_false]
      simp_rw [show ∀ t : ℝ, t * ((x k : ℝ) * jetDiff r (radial r i t x) (Pi.single k 1) f) =
          (x k : ℝ) * (t * jetDiff r (radial r i t x) (Pi.single k 1) f) by intro t; ring]
      exact intervalIntegral.integral_const_mul _ _
  · intro k _
    by_cases hki : k = i
    · simp only [hki, ite_true, mul_zero]; exact intervalIntegrable_const
    · simp only [hki, ite_false]
      convert (ht k).const_mul (x k : ℝ) using 1
      funext t
      ring

/-- The differential defect of radial integration is the radial integral of
the antisymmetric derivatives. The excluded repeated indices contribute zero. -/
theorem rowHomotopy_defect (hr : 0 < r) (i j : ι) (hji : j ≠ i)
    (F : JetValues (ι := ι) r) (hF : IsCubeJet r (F j))
    (x : Cube ι r) (hx : point r x ∈ Metric.ball 0 (r : ℝ)) :
    jetDiff r x (Pi.single j 1) (rowHomotopy r i F) - (F j).1 x =
      ∑ k, if k = i ∨ k = j then 0 else (x k : ℝ) *
        ∫ t in (0 : ℝ)..1, t * (jetDiff r (radial r i t x) (Pi.single j 1) (F k) -
          jetDiff r (radial r i t x) (Pi.single k 1) (F j)) := by
  rw [rowHomotopy_diff r hr i j hji F x, radial_FTC_expanded r (F j) hF i x hx,
    add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hki : k = i
  · simp [hki]
  · by_cases hkj : k = j
    · simp [hkj, hji]
    · simp only [hki, hkj, or_self, ite_false]
      have h₁ : IntervalIntegrable (fun t : ℝ =>
          t * jetDiff r (radial r i t x) (Pi.single j 1) (F k)) volume 0 1 :=
        (continuous_id.mul (continuous_radial_diff r i x _ _)).intervalIntegrable 0 1
      have h₂ : IntervalIntegrable (fun t : ℝ =>
          t * jetDiff r (radial r i t x) (Pi.single k 1) (F j)) volume 0 1 :=
        (continuous_id.mul (continuous_radial_diff r i x _ _)).intervalIntegrable 0 1
      simp_rw [mul_sub]
      rw [intervalIntegral.integral_sub h₁ h₂]
      ring

end SemiHamiltonian.Darboux
