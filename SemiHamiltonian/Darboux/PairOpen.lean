module

public import SemiHamiltonian.Darboux.PairLocal
public import SemiHamiltonian.Darboux.LocalSmoothData

/-! Actual smooth coefficient functions for the general Darboux theorem. -/

@[expose] public section

open scoped NNReal Topology ContDiff
open Filter Set

namespace SemiHamiltonian.Darboux.Pair

variable {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)
  {V : Set (ι → ℝ)} (hV : IsOpen V) (hbox : ∀ x : Cube ι r, point r x ∈ V)
  (γ δ : ι → ι → (ι → ℝ) → ℝ)
  (hγ : ∀ i j, ContDiffOn ℝ ∞ (γ i j) V) (hδ : ∀ i j, ContDiffOn ℝ ∞ (δ i j) V)

noncomputable def localCoefficientJets : JetCoefficients (ι := ι) r :=
  (Darboux.localCoefficientJets r hV hbox γ hγ, Darboux.localCoefficientJets r hV hbox δ hδ)

theorem localCoefficientJets_isCubeJet (hr : 0 < r) (i j : ι) :
    IsCubeJet r ((localCoefficientJets r hV hbox γ δ hγ hδ).1 i j) ∧
      IsCubeJet r ((localCoefficientJets r hV hbox γ δ hγ hδ).2 i j) :=
  ⟨Darboux.localCoefficientJets_isCubeJet r hV hbox γ hγ hr i j,
    Darboux.localCoefficientJets_isCubeJet r hV hbox δ hδ hr i j⟩

theorem localCoefficientJets_contDiff :
    SmoothCoefficients r (coefficientValues r (localCoefficientJets r hV hbox γ δ hγ hδ)) :=
  ⟨Darboux.localCoefficientJets_contDiff r hV hbox γ hγ,
    Darboux.localCoefficientJets_contDiff r hV hbox δ hδ⟩

def CompatibleFunctions (γ δ : ι → ι → (ι → ℝ) → ℝ) (V : Set (ι → ℝ)) : Prop :=
  ∀ x ∈ V, ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
    fderiv ℝ (γ i j) x (Pi.single k 1) = fderiv ℝ (γ i k) x (Pi.single j 1) ∧
    fderiv ℝ (δ i j) x (Pi.single k 1) =
      γ i k x * δ i j x + δ i k x * δ k j x - δ i j x * γ j k x

theorem localCoefficientJets_compatible (hr : 0 < r) (hc : CompatibleFunctions γ δ V) :
    IsDarbouxCompatible r (localCoefficientJets r hV hbox γ δ hγ hδ) := by
  intro x i j k hij hik hjk
  have hscale (a : ℝ) : (r : ℝ)⁻¹ * ((r : ℝ) * a) = a := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (show (0 : ℝ) < r from hr)), one_mul]
  constructor
  · change (r : ℝ)⁻¹ * ((r : ℝ) * fderiv ℝ (γ i j) (point r x) (Pi.single k 1)) =
      (r : ℝ)⁻¹ * ((r : ℝ) * fderiv ℝ (γ i k) (point r x) (Pi.single j 1))
    rw [hscale, hscale]
    exact (hc (point r x) (hbox x) i j k hij hik hjk).1
  · change (r : ℝ)⁻¹ * ((r : ℝ) * fderiv ℝ (δ i j) (point r x) (Pi.single k 1)) = _
    rw [hscale]
    exact (hc (point r x) (hbox x) i j k hij hik hjk).2

variable {r}

theorem IsSmoothDarbouxSolution.pde {Γ : JetCoefficients (ι := ι) r}
    {φ : ι → C(ℝ, ℝ)} {u : Values (ι := ι) r} (hu : IsSmoothDarbouxSolution r Γ φ u)
    {x : ι → ℝ} (hx : x ∈ Metric.ball 0 (r : ℝ)) (i j : ι) (hij : i ≠ j) :
    fderiv ℝ (fun y => u (clamp r y) i) x (Pi.single j 1) =
      (Γ.1 i j).1 (clamp r x) * u (clamp r x) i + (Γ.2 i j).1 (clamp r x) * u (clamp r x) j := by
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
    (γ δ : ι → ι → (ι → ℝ) → ℝ)
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (γ i j) V) (hδ : ∀ i j, ContDiffOn ℝ ∞ (δ i j) V)
    (hc : CompatibleFunctions γ δ V) :
    ∃ r : ℝ≥0, 0 < r ∧ r ≤ R ∧
      ∀ (φ : ι → C(ℝ, ℝ)), (∀ i, ContDiff ℝ ∞ (φ i)) →
        ∃ f : (ι → ℝ) → (ι → ℝ),
          ContDiffOn ℝ ∞ f (Metric.ball 0 (r : ℝ)) ∧
          (∀ x ∈ Metric.ball 0 (r : ℝ), ∀ i j, i ≠ j →
            fderiv ℝ (fun y => f y i) x (Pi.single j 1) = γ i j x * f x i + δ i j x * f x j) ∧
          ∀ i (s : ℝ), |s| < r → f (Pi.single i s) i = φ i s := by
  obtain ⟨r, hr, hrpos, hsol⟩ := local_existsUnique_smooth_darboux hR
    (localCoefficientJets R hV hbox γ δ hγ hδ)
    (localCoefficientJets_isCubeJet R hV hbox γ δ hγ hδ hR)
    (localCoefficientJets_compatible R hV hbox γ δ hγ hδ hR hc)
    (localCoefficientJets_contDiff R hV hbox γ δ hγ hδ)
  refine ⟨r, hrpos, hr, fun φ hφ => ?_⟩
  obtain ⟨u, hu, _⟩ := hsol φ hφ
  refine ⟨fun x => u (clamp r x), hu.2, ?_, hu.axis⟩
  intro x hx i j hij
  have hp := hu.pde hx i j hij
  have hn : ‖x‖ ≤ r := (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
  change _ = γ i j (point r (clamp r x)) * _ + δ i j (point r (clamp r x)) * _ at hp
  simpa only [point_clamp_of_norm_le r hn] using hp

end SemiHamiltonian.Darboux.Pair
