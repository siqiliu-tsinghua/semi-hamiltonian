module

public import SemiHamiltonian.Darboux.SmoothData

/-! Darboux coefficient data smooth on an arbitrary open neighbourhood of the cube. -/

@[expose] public section

open scoped NNReal Topology ContDiff
open Filter Set

namespace SemiHamiltonian.Darboux

variable {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)
  {V : Set (ι → ℝ)} (hV : IsOpen V) (hbox : ∀ x : Cube ι r, point r x ∈ V)
  (γ : ι → ι → (ι → ℝ) → ℝ) (hγ : ∀ i j, ContDiffOn ℝ ∞ (γ i j) V)

noncomputable def localCoefficientJets : JetCoefficients (ι := ι) r := fun i j =>
  (⟨fun x => γ i j (point r x), (hγ i j).continuousOn.comp_continuous
      (continuous_pi fun k => continuous_subtype_val.comp (continuous_apply k)) hbox⟩,
   ⟨fun x => (r : ℝ) • fderiv ℝ (γ i j) (point r x), by
    have hd : Continuous (fun x : Cube ι r => fderiv ℝ (γ i j) (point r x)) :=
      ((hγ i j).fderiv_of_isOpen hV (m := ∞) (by simp)).continuousOn.comp_continuous
        (continuous_pi fun k => continuous_subtype_val.comp (continuous_apply k)) hbox
    simpa only [Pi.smul_def] using hd.const_smul (r : ℝ)⟩)

include hbox in
theorem ball_subset_of_cube : Metric.ball (0 : ι → ℝ) (r : ℝ) ⊆ V := by
  intro x hx
  have hn : ‖x‖ ≤ r := (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
  simpa only [point_clamp_of_norm_le r hn] using hbox (clamp r x)

theorem localCoefficientJets_isCubeJet (hr : 0 < r) (i j : ι) :
    IsCubeJet r (localCoefficientJets r hV hbox γ hγ i j) := by
  intro x hx
  have hn : ‖x‖ ≤ r := (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
  have he : (fun y => γ i j (point r (clamp r y))) =ᶠ[𝓝 x] γ i j := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    have hyn : ‖y‖ ≤ r := (by simpa only [Metric.mem_ball, dist_zero_right] using hy : ‖y‖ < r).le
    rw [point_clamp_of_norm_le r hyn]
  change HasFDerivAt (fun y => γ i j (point r (clamp r y)))
    ((r : ℝ)⁻¹ • ((r : ℝ) • fderiv ℝ (γ i j) (point r (clamp r x)))) x
  rw [inv_smul_smul₀ (ne_of_gt (show (0 : ℝ) < r from hr)), point_clamp_of_norm_le r hn]
  exact ((hγ i j).contDiffAt (hV.mem_nhds (ball_subset_of_cube r hbox hx))).differentiableAt
    (by simp) |>.hasFDerivAt.congr_of_eventuallyEq he

theorem localCoefficientJets_contDiff :
    ContDiffOn ℝ ∞ (fun x => coefficientValues r (localCoefficientJets r hV hbox γ hγ) (clamp r x))
      (Metric.ball 0 (r : ℝ)) := by
  have hg : ContDiffOn ℝ ∞ (fun x i j => γ i j x) V :=
    contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (hγ i))
  apply (hg.mono (ball_subset_of_cube r hbox)).congr
  intro x hx
  have hn : ‖x‖ ≤ r := (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
  change (fun i j => γ i j (point r (clamp r x))) = _
  rw [point_clamp_of_norm_le r hn]

theorem localCoefficientJets_compatible (hr : 0 < r)
    (hc : ∀ x ∈ V, ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      fderiv ℝ (γ i j) x (Pi.single k 1) =
        γ i j x * γ j k x + γ i k x * γ k j x - γ i j x * γ i k x) :
    IsDarbouxCompatible r (localCoefficientJets r hV hbox γ hγ) := by
  intro x i j k hij hik hjk
  change (r : ℝ)⁻¹ * ((r : ℝ) * fderiv ℝ (γ i j) (point r x) (Pi.single k 1)) = _
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (show (0 : ℝ) < r from hr)), one_mul]
  exact hc (point r x) (hbox x) i j k hij hik hjk

variable {r}

theorem IsSmoothDarbouxSolution.pde {Γ : JetCoefficients (ι := ι) r}
    {φ : ι → C(ℝ, ℝ)} {u : Values (ι := ι) r} (hu : IsSmoothDarbouxSolution r Γ φ u)
    {x : ι → ℝ} (hx : x ∈ Metric.ball 0 (r : ℝ)) (i j : ι) (hij : i ≠ j) :
    fderiv ℝ (fun y => u (clamp r y) i) x (Pi.single j 1) =
      (Γ i j).1 (clamp r x) * (u (clamp r x) j - u (clamp r x) i) := by
  obtain ⟨w, rfl, hw, hp, ha⟩ := hu.1
  change fderiv ℝ (fun y => (w i).1 (clamp r y)) x (Pi.single j 1) = _
  rw [(hw i x hx).fderiv]
  exact hp (clamp r x) i j hij

theorem IsSmoothDarbouxSolution.axis {Γ : JetCoefficients (ι := ι) r}
    {φ : ι → C(ℝ, ℝ)} {u : Values (ι := ι) r} (hu : IsSmoothDarbouxSolution r Γ φ u)
    (i : ι) (s : ℝ) (hs : |s| < r) : u (clamp r (Pi.single i s)) i = φ i s := by
  obtain ⟨w, rfl, hw, hp, ha⟩ := hu.1
  have hn : ‖(Pi.single i s : ι → ℝ)‖ ≤ r := by
    apply (pi_norm_le_iff_of_nonneg r.coe_nonneg).mpr
    intro j
    by_cases hji : j = i
    · subst j; simpa using hs.le
    · simp [Pi.single_apply, hji]
  have hcoord := point_clamp_of_norm_le r hn
  have he : Darboux.axis r i (clamp r (Pi.single i s)) = clamp r (Pi.single i s) := by
    funext j
    apply Subtype.ext
    by_cases hji : j = i
    · subst j; exact axis_coordinate r i _
    · rw [axis_other r i j hji]
      have h := congrFun hcoord j
      simpa [point, Pi.single_apply, hji] using h.symm
  have ht := ha i (clamp r (Pi.single i s))
  rw [he] at ht
  change (w i).1 _ = φ i _ at ht
  change (w i).1 _ = φ i (point r (clamp r (Pi.single i s)) i) at ht
  simpa only [hcoord, Pi.single_eq_same, valuesOfJets, ContinuousMap.coe_mk] using ht

/-- An ordinary-function interface for coefficients smooth only near the initial
cube. The smaller radius is uniform in all smooth axis data. -/
theorem local_smooth_solution_on_open (R : ℝ≥0) (hR : 0 < R)
    {V : Set (ι → ℝ)} (hV : IsOpen V) (hbox : ∀ x : Cube ι R, point R x ∈ V)
    (γ : ι → ι → (ι → ℝ) → ℝ) (hγ : ∀ i j, ContDiffOn ℝ ∞ (γ i j) V)
    (hc : ∀ x ∈ V, ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      fderiv ℝ (γ i j) x (Pi.single k 1) =
        γ i j x * γ j k x + γ i k x * γ k j x - γ i j x * γ i k x) :
    ∃ r : ℝ≥0, 0 < r ∧ r ≤ R ∧
      ∀ (φ : ι → C(ℝ, ℝ)), (∀ i, ContDiff ℝ ∞ (φ i)) →
        ∃ f : (ι → ℝ) → (ι → ℝ),
          ContDiffOn ℝ ∞ f (Metric.ball 0 (r : ℝ)) ∧
          (∀ x ∈ Metric.ball 0 (r : ℝ), ∀ i j, i ≠ j →
            fderiv ℝ (fun y => f y i) x (Pi.single j 1) = γ i j x * (f x j - f x i)) ∧
          ∀ i (s : ℝ), |s| < r → f (Pi.single i s) i = φ i s := by
  obtain ⟨r, hr, hrpos, hsol⟩ := local_existsUnique_smooth_darboux hR
    (localCoefficientJets R hV hbox γ hγ)
    (localCoefficientJets_isCubeJet R hV hbox γ hγ hR)
    (localCoefficientJets_compatible R hV hbox γ hγ hR hc)
    (localCoefficientJets_contDiff R hV hbox γ hγ)
  refine ⟨r, hrpos, hr, fun φ hφ => ?_⟩
  obtain ⟨u, hu, _⟩ := hsol φ hφ
  refine ⟨fun x => u (clamp r x), hu.2, ?_, hu.axis⟩
  intro x hx i j hij
  have hp := hu.pde hx i j hij
  have hn : ‖x‖ ≤ r := (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
  change _ = γ i j (point r (clamp r x)) * _ at hp
  simpa only [point_clamp_of_norm_le r hn] using hp

end SemiHamiltonian.Darboux
