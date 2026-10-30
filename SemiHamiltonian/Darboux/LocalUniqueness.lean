module

public import SemiHamiltonian.Darboux.LocalSmoothData

@[expose] public section

open scoped Topology ContDiff NNReal Classical
open Set Filter

set_option backward.isDefEq.respectTransparency.types false

namespace SemiHamiltonian.Darboux

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem point_axis_eq (r : ℝ≥0) (i : ι) (x : Cube ι r) :
    point r (axis r i x) = Pi.single i (x i : ℝ) := by
  funext j
  by_cases h : j = i
  · subst j; simp [point]
  · simp [point, axis_other r i j h, h]

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_point (r : ℝ≥0) : Continuous (point (ι := ι) r) :=
  continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)

/-- Classical uniqueness applies to arbitrary smooth functions defined near a
closed cube, without imposing a chosen boundary extension on the original germ. -/
theorem unique_on_cube (r : ℝ≥0) {U : Set (ι → ℝ)} (hU : IsOpen U) (p : ι → ℝ)
    (hbox : ∀ x : Cube ι r, p + point r x ∈ U)
    (Γ : Coefficients (ι := ι) r)
    (hsmall : 2 * Fintype.card ι * (r : ℝ) * ‖Γ‖ < 1)
    (W Z : (ι → ℝ) → (ι → ℝ))
    (hW : ContDiffOn ℝ ∞ W U) (hZ : ContDiffOn ℝ ∞ Z U)
    (hPW : ∀ (x : Cube ι r) i j, i ≠ j →
      fderiv ℝ (fun y => W y i) (p + point r x) (Pi.single j 1) =
        Γ x i j * (W (p + point r x) j - W (p + point r x) i))
    (hPZ : ∀ (x : Cube ι r) i j, i ≠ j →
      fderiv ℝ (fun y => Z y i) (p + point r x) (Pi.single j 1) =
        Γ x i j * (Z (p + point r x) j - Z (p + point r x) i))
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
          Γ x i j * (F (p + point r x) j - F (p + point r x) i))
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
    (γ : ι → ι → (ι → ℝ) → ℝ) (hγ : ∀ i j, ContinuousOn (γ i j) U)
    (W Z : (ι → ℝ) → (ι → ℝ)) (hW : ContDiffOn ℝ ∞ W U) (hZ : ContDiffOn ℝ ∞ Z U)
    (hPW : ∀ x ∈ U, ∀ i j, i ≠ j → fderiv ℝ (fun y => W y i) x (Pi.single j 1) =
      γ i j x * (W x j - W x i))
    (hPZ : ∀ x ∈ U, ∀ i j, i ≠ j → fderiv ℝ (fun y => Z y i) x (Pi.single j 1) =
      γ i j x * (Z x j - Z x i))
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
  let Γ : Coefficients (ι := ι) R := ⟨fun x i j => γ i j (p + point R x),
    continuous_pi fun i => continuous_pi fun j =>
      (hγ i j).comp_continuous (continuous_const.add (continuous_point R)) hbox⟩
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

end SemiHamiltonian.Darboux
