module

public import SemiHamiltonian.Darboux.PairIntegral
public import SemiHamiltonian.Darboux.LocalUniqueness

/-! Classical and germ uniqueness for the two-coefficient Darboux system. -/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal BigOperators Topology ContDiff Classical

set_option backward.isDefEq.respectTransparency.types false

namespace SemiHamiltonian.Darboux.Pair

variable {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

def IsClassicalSolution (Γ : Coefficients (ι := ι) r) (φ : AxisData (ι := ι) r)
    (w : Values (ι := ι) r) : Prop :=
  ∃ (W : (ι → ℝ) → ι → ℝ) (J : Cube ι r → ι → (ι → ℝ) →L[ℝ] ℝ),
    (∀ x, W (point r x) = w x) ∧
    (∀ x i, HasFDerivAt (fun y => W y i) (J x i) (point r x)) ∧
    (∀ x i j, i ≠ j → J x i (Pi.single j 1) = (Γ.1 x i j * w x i + Γ.2 x i j * w x j)) ∧
    (∀ i x, w (axis r i x) i = φ i (x i))

theorem classicalSolution_fixedPoint (Γ : Coefficients (ι := ι) r)
    (φ : AxisData (ι := ι) r) (w : Values (ι := ι) r)
    (hw : IsClassicalSolution r Γ φ w) : picard r Γ φ w = w := by
  obtain ⟨W, J, hW, hd, he, ha⟩ := hw
  apply ContinuousMap.ext
  intro x
  funext i
  let g : ℝ → ℝ := fun t => ∑ j, if j = i then 0 else
    (x j : ℝ) * kernel r Γ w i j x t
  have hint : IntervalIntegrable g volume 0 1 := by
    have hc : Continuous g := by
      apply continuous_finsetSum
      intro j _
      by_cases hji : j = i
      · simp only [hji, ite_true]; exact continuous_const
      · simp only [hji, ite_false]
        exact continuous_const.mul
          ((continuous_kernel r Γ w i j).comp (continuous_const.prodMk continuous_id))
    exact hc.intervalIntegrable 0 1
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => W (affineRadial r i x s) i) (g t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
    have hf := hd (radial r i t x) i
    rw [point_radial r i x t ht'] at hf
    have hc : HasDerivAt (fun s => W (affineRadial r i x s) i)
        (J (radial r i t x) i (transverse r i x)) t :=
      hf.comp_hasDerivAt t (hasDerivAt_affineRadial r i x t)
    have heval : J (radial r i t x) i (transverse r i x) = g t := by
      rw [linearMap_transverse]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · simp [hji]
      · simp only [hji, ite_false]
        rw [he _ i j (Ne.symm hji)]
        rfl
    simpa only [heval] using hc
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hend : W (affineRadial r i x 1) i = w x i := by
    rw [← point_radial r i x 1 (by constructor <;> norm_num), radial_one, hW]
  have hstart : W (affineRadial r i x 0) i = φ i (x i) := by
    rw [← point_radial r i x 0 (by constructor <;> norm_num), hW]
    exact ha i x
  rw [hend, hstart] at hFTC
  have hsum : ∫ t in (0 : ℝ)..1, g t = integralOperator r Γ w x i := by
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · simp [hji]
      · simp [hji, intervalIntegral.integral_const_mul]
    · intro j _
      by_cases hji : j = i
      · simp only [hji, ite_true]; exact intervalIntegrable_const
      · simp only [hji, ite_false]
        exact (kernel_integrable r Γ w i j x).const_mul _
  rw [hsum] at hFTC
  change φ i (x i) + integralOperator r Γ w x i = w x i
  linarith

/-- Classical uniqueness on a sufficiently small cube, for arbitrary axis data.
Compatibility is needed for existence, not for this uniqueness statement. -/
theorem classicalSolution_unique (Γ : Coefficients (ι := ι) r) (φ : AxisData (ι := ι) r)
    (hsmall : 2 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1)
    {w z : Values (ι := ι) r}
    (hw : IsClassicalSolution r Γ φ w) (hz : IsClassicalSolution r Γ φ z) : w = z :=
  (picard_contraction r Γ φ hsmall).fixedPoint_unique'
    (classicalSolution_fixedPoint r Γ φ w hw) (classicalSolution_fixedPoint r Γ φ z hz)

variable {r R : ℝ≥0}

noncomputable def restrictCoefficients (Γ : Coefficients (ι := ι) R) (hr : r ≤ R) :
    Coefficients (ι := ι) r :=
  (Darboux.restrictCoefficients Γ.1 hr, Darboux.restrictCoefficients Γ.2 hr)

theorem restrictCoefficients_norm_le (Γ : Coefficients (ι := ι) R) (hr : r ≤ R) :
    ‖restrictCoefficients Γ hr‖ ≤ ‖Γ‖ := by
  apply max_le
  · exact (Darboux.restrictCoefficients_norm_le Γ.1 hr).trans (norm_fst_le Γ)
  · exact (Darboux.restrictCoefficients_norm_le Γ.2 hr).trans (norm_snd_le Γ)

theorem exists_positive_contraction_radius (hR : 0 < R)
    (Γ : Coefficients (ι := ι) R) :
    ∃ (r : ℝ≥0) (hr : r ≤ R), 0 < r ∧
      2 * Fintype.card ι * (r : ℝ) * ‖restrictCoefficients Γ hr‖ < 1 := by
  obtain ⟨ε, hε, hεsmall⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1)
    (2 * Fintype.card ι * ‖Γ‖)
  let r : ℝ≥0 := min R ⟨ε, hε.le⟩
  have hr : r ≤ R := min_le_left _ _
  have hrε : (r : ℝ) ≤ ε := min_le_right (R : ℝ) ε
  refine ⟨r, hr, lt_min hR hε, ?_⟩
  calc
    _ ≤ 2 * Fintype.card ι * (r : ℝ) * ‖Γ‖ :=
      mul_le_mul_of_nonneg_left (restrictCoefficients_norm_le Γ hr) (by positivity)
    _ ≤ ε * (2 * Fintype.card ι * ‖Γ‖) := by
      nlinarith [mul_le_mul_of_nonneg_right hrε
        (by positivity : 0 ≤ 2 * (Fintype.card ι : ℝ) * ‖Γ‖)]
    _ < 1 := by simpa [mul_comm] using hεsmall

theorem unique_on_cube (r : ℝ≥0) {U : Set (ι → ℝ)} (hU : IsOpen U) (p : ι → ℝ)
    (hbox : ∀ x : Cube ι r, p + point r x ∈ U)
    (Γ : Coefficients (ι := ι) r)
    (hsmall : 2 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1)
    (W Z : (ι → ℝ) → (ι → ℝ))
    (hW : ContDiffOn ℝ ∞ W U) (hZ : ContDiffOn ℝ ∞ Z U)
    (hPW : ∀ (x : Cube ι r) i j, i ≠ j →
      fderiv ℝ (fun y => W y i) (p + point r x) (Pi.single j 1) =
        (Γ.1 x i j * W (p + point r x) i + Γ.2 x i j * W (p + point r x) j))
    (hPZ : ∀ (x : Cube ι r) i j, i ≠ j →
      fderiv ℝ (fun y => Z y i) (p + point r x) (Pi.single j 1) =
        (Γ.1 x i j * Z (p + point r x) i + Γ.2 x i j * Z (p + point r x) j))
    (haxis : ∀ i (s : ℝ), |s| ≤ r → W (p + Pi.single i s) i = Z (p + Pi.single i s) i) :
    ∀ x : Cube ι r, W (p + point r x) = Z (p + point r x) := by
  have hc : Continuous (fun x : Cube ι r => p + point r x) := continuous_const.add (continuous_point r)
  let w : Values (ι := ι) r := ⟨fun x => W (p + point r x), hW.continuousOn.comp_continuous hc hbox⟩
  let z : Values (ι := ι) r := ⟨fun x => Z (p + point r x), hZ.continuousOn.comp_continuous hc hbox⟩
  let φ : AxisData (ι := ι) r := fun i =>
    ⟨fun s => W (p + Pi.single i (s : ℝ)) i, by
      apply (contDiffOn_pi.mp hW i).continuousOn.comp_continuous
        (continuous_const.add ((continuous_single i).comp continuous_subtype_val))
      intro s
      have hh := hbox (clamp r (Pi.single i (s : ℝ)))
      have hs := point_clamp_of_norm_le r (show ‖(Pi.single i (s : ℝ) : ι → ℝ)‖ ≤ r by
        simpa only [Pi.norm_single, Real.norm_eq_abs] using abs_le.mpr s.property)
      rwa [hs] at hh⟩
  have hclass (F : (ι → ℝ) → (ι → ℝ)) (hF : ContDiffOn ℝ ∞ F U)
      (f : Values (ι := ι) r) (hf : ∀ x, F (p + point r x) = f x)
      (hPF : ∀ (x : Cube ι r) i j, i ≠ j →
        fderiv ℝ (fun y => F y i) (p + point r x) (Pi.single j 1) =
          (Γ.1 x i j * F (p + point r x) i + Γ.2 x i j * F (p + point r x) j))
      (ha : ∀ i x, f (axis r i x) i = φ i (x i)) : IsClassicalSolution r Γ φ f := by
    refine ⟨fun x => F (p + x), fun x i => fderiv ℝ (fun y => F y i) (p + point r x), hf, ?_, ?_, ha⟩
    · intro x i
      have hd := (((contDiffOn_pi.mp hF i).contDiffAt (hU.mem_nhds (hbox x))).differentiableAt
        (by simp)).hasFDerivAt
      convert hd.comp (point r x) ((hasFDerivAt_id (point r x)).const_add p) using 1 <;> rfl
    · intro x i j hij
      simpa only [hf] using hPF x i j hij
  have hw := hclass W hW w (fun _ => rfl) hPW (by intro i x; change W _ i = _; rw [point_axis_eq]; rfl)
  have hz := hclass Z hZ z (fun _ => rfl) hPZ (by
    intro i x
    change Z (p + point r (axis r i x)) i = W (p + Pi.single i (x i : ℝ)) i
    rw [point_axis_eq]
    exact (haxis i (x i) (abs_coordinate_le r x i)).symm)
  exact fun x => congrArg (fun f : Values (ι := ι) r => f x) (classicalSolution_unique r Γ φ hsmall hw hz)

/-- Equal axis germs determine the entire smooth solution germ. No compatibility
assumption is required for uniqueness. -/
theorem germ_unique {U : Set (ι → ℝ)} (hU : IsOpen U) {p : ι → ℝ} (hp : p ∈ U)
    (γ β : ι → ι → (ι → ℝ) → ℝ) (hγ : ∀ i j, ContinuousOn (γ i j) U)
    (hβ : ∀ i j, ContinuousOn (β i j) U)
    (W Z : (ι → ℝ) → (ι → ℝ)) (hW : ContDiffOn ℝ ∞ W U) (hZ : ContDiffOn ℝ ∞ Z U)
    (hPW : ∀ x ∈ U, ∀ i j, i ≠ j → fderiv ℝ (fun y => W y i) x (Pi.single j 1) =
      (γ i j x * W x i + β i j x * W x j))
    (hPZ : ∀ x ∈ U, ∀ i j, i ≠ j → fderiv ℝ (fun y => Z y i) x (Pi.single j 1) =
      (γ i j x * Z x i + β i j x * Z x j))
    (ha : ∀ i, (fun s => W (p + Pi.single i s) i) =ᶠ[𝓝 0]
      (fun s => Z (p + Pi.single i s) i)) : W =ᶠ[𝓝 p] Z := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU p hp
  have hall : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i, W (p + Pi.single i s) i = Z (p + Pi.single i s) i :=
    eventually_all.mpr ha
  obtain ⟨δ, hδ, hδa⟩ := Metric.eventually_nhds_iff.mp hall
  let R : ℝ≥0 := ⟨min ε δ / 2, by positivity⟩
  have hR : 0 < R := by change 0 < min ε δ / 2; positivity
  have hRε : (R : ℝ) < ε := by change min ε δ / 2 < ε; have := min_le_left ε δ; have := lt_min hε hδ; linarith
  have hRδ : (R : ℝ) < δ := by change min ε δ / 2 < δ; have := min_le_right ε δ; have := lt_min hε hδ; linarith
  have hbox : ∀ x : Cube ι R, p + point R x ∈ U := by
    intro x
    apply hεU
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using (norm_point_le R x).trans_lt hRε
  let Γ : Coefficients (ι := ι) R :=
    (⟨fun x i j => γ i j (p + point R x), continuous_pi fun i => continuous_pi fun j =>
      (hγ i j).comp_continuous (continuous_const.add (continuous_point R)) hbox⟩,
     ⟨fun x i j => β i j (p + point R x), continuous_pi fun i => continuous_pi fun j =>
      (hβ i j).comp_continuous (continuous_const.add (continuous_point R)) hbox⟩)
  obtain ⟨r, hrR, hr, hsmall⟩ := exists_positive_contraction_radius hR Γ
  have hboxr : ∀ x : Cube ι r, p + point r x ∈ U := fun x => hbox (cubeInclusion hrR x)
  have haxes (i : ι) (s : ℝ) (hs : |s| ≤ r) :
      W (p + Pi.single i s) i = Z (p + Pi.single i s) i := by
    apply hδa (i := i)
    simpa only [dist_zero_right, Real.norm_eq_abs] using
      hs.trans_lt ((show (r : ℝ) ≤ R from hrR).trans_lt hRδ)
  have heq := unique_on_cube r hU p hboxr (restrictCoefficients Γ hrR) hsmall W Z hW hZ
    (fun x i j hij => hPW _ (hboxr x) i j hij) (fun x i j hij => hPZ _ (hboxr x) i j hij) haxes
  filter_upwards [Metric.ball_mem_nhds p (show (0 : ℝ) < r from hr)] with q hq
  have hn : ‖q - p‖ ≤ r := (by simpa only [Metric.mem_ball, dist_eq_norm] using hq : ‖q - p‖ < r).le
  have hh := heq (clamp r (q - p))
  rw [point_clamp_of_norm_le r hn, show p + (q - p) = q by abel] at hh
  exact hh

end SemiHamiltonian.Darboux.Pair
