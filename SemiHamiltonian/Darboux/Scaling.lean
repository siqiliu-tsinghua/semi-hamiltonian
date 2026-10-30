module

public import SemiHamiltonian.Darboux.CompactSmooth
public import SemiHamiltonian.Darboux.SmoothLinear
public import SemiHamiltonian.Darboux.AxisData

/-! Coordinate dilations put all parameter-dependent integral equations on the
same unit cube. -/

@[expose] public section

open scoped NNReal Topology ContDiff
open Filter

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 1024

namespace SemiHamiltonian.Darboux

variable {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

noncomputable def scaleFamily : C(Cube ι 1, (ι → ℝ) →L[ℝ] (ι → ℝ)) :=
  ⟨fun y => ContinuousLinearMap.mul ℝ (ι → ℝ) (point 1 y),
    (ContinuousLinearMap.mul ℝ (ι → ℝ)).continuous.comp
      (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))⟩

@[simp] theorem scaleFamily_apply (y : Cube ι 1) (x : ι → ℝ) (i : ι) :
    scaleFamily y x i = (y i : ℝ) * x i := rfl

theorem scaleFamily_norm_le (y : Cube ι 1) (x : ι → ℝ) : ‖scaleFamily y x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  rw [scaleFamily_apply, norm_mul]
  exact (mul_le_mul (abs_coordinate_le 1 y i) (norm_le_pi_norm x i)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem scaleFamily_maps_ball (x : ι → ℝ) (hx : x ∈ Metric.ball 0 (r : ℝ))
    (y : Cube ι 1) : scaleFamily y x ∈ Metric.ball 0 (r : ℝ) := by
  simp only [Metric.mem_ball, dist_zero_right] at hx ⊢
  exact (scaleFamily_norm_le y x).trans_lt hx

noncomputable def scaledPoint (x : ι → ℝ) : C(Cube ι 1, Cube ι r) :=
  ⟨fun y => clamp r (scaleFamily y x),
    (clamp r).continuous.comp (scaleFamily.continuous.clm_apply continuous_const)⟩

theorem scaledPoint_coordinate {x : ι → ℝ} (hx : ‖x‖ ≤ r) (y : Cube ι 1) (j : ι) :
    (scaledPoint r x y j : ℝ) = (y j : ℝ) * x j :=
  congrFun (point_clamp_of_norm_le r ((scaleFamily_norm_le y x).trans hx)) j

theorem scaledPoint_radial {x : ι → ℝ} (hx : ‖x‖ < r) (y : Cube ι 1)
    (i : ι) (t : ℝ) :
    scaledPoint r x (radial 1 i t y) = radial r i t (scaledPoint r x y) := by
  have hy : scaleFamily y x ∈ Metric.ball 0 (r : ℝ) := by
    simpa only [Metric.mem_ball, dist_zero_right] using (scaleFamily_norm_le y x).trans_lt hx
  have he : scaleFamily (radial 1 i t y) x = radialLinear i t (scaleFamily y x) := by
    funext j
    simp only [scaleFamily_apply, radialLinear_apply]
    by_cases hji : j = i
    · simp [radial, hji]
    · simp [radial, hji, mul_assoc]
  change clamp r (scaleFamily (radial 1 i t y) x) = radialMap r i t (clamp r (scaleFamily y x))
  rw [radial_clamp r i t hy, he]

noncomputable def columnFactor : (ι → ℝ) →L[ℝ] Coefficients (ι := ι) 1 :=
  (ContinuousLinearMap.const ℝ (Cube ι 1)).comp
    (ContinuousLinearMap.pi fun _ : ι => ContinuousLinearMap.id ℝ (ι → ℝ))

@[simp] theorem columnFactor_apply (x : ι → ℝ) (y : Cube ι 1) (i j : ι) :
    columnFactor x y i j = x j := rfl

noncomputable def scaledCoefficients (Γ : Coefficients (ι := ι) r) (x : ι → ℝ) :
    Coefficients (ι := ι) 1 :=
  columnFactor x * compactLinearFamily scaleFamily (fun z => Γ (clamp r z)) x

theorem scaledCoefficients_apply (Γ : Coefficients (ι := ι) r) (x : ι → ℝ)
    (y : Cube ι 1) (i j : ι) :
    scaledCoefficients r Γ x y i j = x j * Γ (scaledPoint r x y) i j := by
  have hcont : Continuous (fun z => Γ (clamp r z)) := Γ.continuous.comp (clamp r).continuous
  change x j * compactLinearFamily scaleFamily (fun z => Γ (clamp r z)) x y i j = _
  rw [compactLinearFamily_apply scaleFamily hcont.continuousOn (V := Set.univ) (fun _ => Set.mem_univ _) y]
  rfl

theorem scaledCoefficients_norm_le (Γ : Coefficients (ι := ι) r) (x : ι → ℝ) :
    ‖scaledCoefficients r Γ x‖ ≤ ‖x‖ * ‖Γ‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg x) (norm_nonneg Γ))).mpr
  intro y
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  rw [scaledCoefficients_apply, norm_mul]
  exact mul_le_mul (norm_le_pi_norm x j) (coefficient_le_norm r Γ _ i j)
    (norm_nonneg _) (norm_nonneg x)

theorem scaledCoefficients_contDiff (Γ : Coefficients (ι := ι) r)
    (hΓ : ContDiffOn ℝ ∞ (fun x => Γ (clamp r x)) (Metric.ball 0 (r : ℝ))) :
    ContDiffOn ℝ ∞ (scaledCoefficients r Γ) (Metric.ball 0 (r : ℝ)) := by
  have hcol : ContDiff ℝ ∞ (columnFactor (ι := ι)) := ContinuousLinearMap.contDiff _
  have hg : ContDiffOn ℝ ∞
      (compactLinearFamily (scaleFamily (ι := ι)) (fun z => Γ (clamp r z)))
      (Metric.ball 0 (r : ℝ)) :=
    contDiffOn_compactLinearFamily (scaleFamily (ι := ι))
      Metric.isOpen_ball Metric.isOpen_ball (scaleFamily_maps_ball r) hΓ
  change ContDiffOn ℝ ∞ (fun x => columnFactor x *
    compactLinearFamily (scaleFamily (ι := ι)) (fun z => Γ (clamp r z)) x) _
  exact hcol.contDiffOn.mul hg

noncomputable def scaledValues (w : Values (ι := ι) r) (x : ι → ℝ) : Values (ι := ι) 1 :=
  w.comp (scaledPoint r x)

noncomputable def ambientInitial (φ : ι → C(ℝ, ℝ)) : C(ι → ℝ, ι → ℝ) :=
  ⟨fun x i => φ i (x i), continuous_pi fun i => (φ i).continuous.comp (continuous_apply i)⟩

noncomputable def scaledInitial (φ : ι → C(ℝ, ℝ)) (x : ι → ℝ) : Values (ι := ι) 1 :=
  compactLinearFamily scaleFamily (ambientInitial φ) x

theorem scaledInitial_apply (φ : ι → C(ℝ, ℝ)) (x : ι → ℝ) (y : Cube ι 1) (i : ι) :
    scaledInitial φ x y i = φ i ((y i : ℝ) * x i) := by
  rw [scaledInitial, compactLinearFamily_apply scaleFamily (ambientInitial φ).continuous.continuousOn
    (V := Set.univ) (fun _ => Set.mem_univ _) y]
  rfl

theorem scaledInitial_contDiff (φ : ι → C(ℝ, ℝ)) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    ContDiff ℝ ∞ (scaledInitial φ) := by
  rw [← contDiffOn_univ]
  change ContDiffOn ℝ ∞ (compactLinearFamily (scaleFamily (ι := ι)) (ambientInitial φ)) Set.univ
  apply contDiffOn_compactLinearFamily (scaleFamily (ι := ι)) isOpen_univ isOpen_univ
    (fun _ _ _ => Set.mem_univ _)
  apply ContDiff.contDiffOn
  exact contDiff_pi.mpr (fun i => (hφ i).comp (contDiff_apply ℝ (fun _ : ι => ℝ) i))

theorem scaledValues_fixedPoint (Γ : Coefficients (ι := ι) r) (φ : ι → C(ℝ, ℝ))
    (w : Values (ι := ι) r) (hw : picard r Γ (axisDataOfFunctions r φ) w = w)
    {x : ι → ℝ} (hx : x ∈ Metric.ball 0 (r : ℝ)) :
    scaledInitial φ x + integralOperator 1 (scaledCoefficients r Γ x) (scaledValues r w x) =
      scaledValues r w x := by
  have hxn : ‖x‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  ext y i
  have h := congrArg (fun z : Values (ι := ι) r => z (scaledPoint r x y) i) hw
  change φ i (scaledPoint r x y i) + (∑ j, if j = i then 0 else
    (scaledPoint r x y j : ℝ) * ∫ t in (0 : ℝ)..1, kernel r Γ w i j (scaledPoint r x y) t) = _ at h
  change scaledInitial φ x y i + (∑ j, if j = i then 0 else
    (y j : ℝ) * ∫ t in (0 : ℝ)..1,
      kernel 1 (scaledCoefficients r Γ x) (scaledValues r w x) i j y t) = _
  rw [scaledInitial_apply, ← scaledPoint_coordinate r hxn.le y i]
  change _ = w (scaledPoint r x y) i
  rw [← h]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · simp [hji]
  · simp only [hji, ite_false]
    have hk : kernel 1 (scaledCoefficients r Γ x) (scaledValues r w x) i j y =
        fun t => x j * kernel r Γ w i j (scaledPoint r x y) t := by
      funext t
      simp only [kernel, scaledCoefficients_apply, scaledValues, ContinuousMap.comp_apply,
        scaledPoint_radial r hxn]
      ring
    rw [hk, intervalIntegral.integral_const_mul, scaledPoint_coordinate r hxn.le y j]
    ring

end SemiHamiltonian.Darboux
