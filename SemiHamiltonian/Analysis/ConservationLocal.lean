module

public import SemiHamiltonian.Analysis.SmoothSystem
public import SemiHamiltonian.Darboux.PairOpen
public import SemiHamiltonian.Conservation

/-! Arbitrary smooth axis data for conservation-density gradients. -/

@[expose] public section

open scoped NNReal Topology ContDiff Classical
open Filter Set

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)} (hU : IsOpen U)

/-- Arbitrary smooth single-variable data on all coordinate axes through each
base point extend to a genuine smooth density gradient. The radius is chosen
before the data. Balls use the sup norm, hence are coordinate cubes. -/
def LocallyDensityAxisSolvable (S : System hU) : Prop :=
  ∀ p : U, ∃ (r : ℝ≥0) (_ : 0 < r) (hsub : Metric.ball (p : ι → ℝ) r ⊆ U),
    ∀ (φ : ι → C(ℝ, ℝ)), (∀ i, ContDiff ℝ ∞ (φ i)) →
      ∃ w : ι → Functions (Metric.ball (p : ι → ℝ) r),
        (restrictSystem hU Metric.isOpen_ball hsub S).IsDensityGradient w ∧
        ∀ i (s : ℝ) (q : Metric.ball (p : ι → ℝ) r),
          (q : ι → ℝ) = p.val + Pi.single i s → w i q = φ i s

private theorem fderiv_comp_translate {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (p x : E) (hf : DifferentiableAt ℝ f (p + x)) :
    fderiv ℝ (fun y => f (p + y)) x = fderiv ℝ f (p + x) := by
  have h := hf.hasFDerivAt.comp x ((hasFDerivAt_id x).const_add p)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using h.fderiv

private theorem fderiv_comp_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (p x : E) (hf : DifferentiableAt ℝ f (x - p)) :
    fderiv ℝ (fun y => f (y - p)) x = fderiv ℝ f (x - p) := by
  have h := hf.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const p)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using h.fderiv

theorem locallyDensityAxisSolvable_of_semiHamiltonian (S : System hU) (hS : S.IsSemiHamiltonian) :
    LocallyDensityAxisSolvable hU S := by
  intro p
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU p p.property
  let R : ℝ≥0 := ⟨ε / 2, by positivity⟩
  have hR : 0 < R := by change 0 < ε / 2; positivity
  have hRε : (R : ℝ) < ε := by change ε / 2 < ε; linarith
  let V : Set (ι → ℝ) := {x | p.val + x ∈ U}
  have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
  have hbox : ∀ x : Darboux.Cube ι R, Darboux.point R x ∈ V := by
    intro x
    apply hεU
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using
      (Darboux.norm_point_le R x).trans_lt hRε
  let γ : ι → ι → (ι → ℝ) → ℝ := fun i j x => extend U (S.coeff i j) (p.val + x)
  have hγ : ∀ i j, ContDiffOn ℝ ∞ (γ i j) V := fun i j =>
    (smooth U (S.coeff i j)).comp (contDiffOn_const.add contDiffOn_id) (fun _ hx => hx)
  have hc : ∀ x ∈ V, ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      fderiv ℝ (γ i j) x (Pi.single k 1) =
        γ i j x * γ j k x + γ i k x * γ k j x - γ i j x * γ i k x := by
    intro x hx i j k hij hik hjk
    change p.val + x ∈ U at hx
    have hd := fderiv_comp_translate (p : ι → ℝ) x
      (hasFDerivAt_extend hU (S.coeff i j) ⟨p.val + x, hx⟩).differentiableAt
    have hz := congrArg (eval (⟨p.val + x, hx⟩ : U)) (S.darbouxResidual_eq_zero hS i j k hij hik hjk)
    simp only [DiagonalSystem.darbouxResidual, map_sub, map_add, map_mul, map_zero] at hz
    change fderiv ℝ (extend U (S.coeff i j)) (p.val + x) (Pi.single k 1) -
      S.coeff i j ⟨p.val + x, hx⟩ * S.coeff j k ⟨p.val + x, hx⟩ -
      S.coeff i k ⟨p.val + x, hx⟩ * S.coeff k j ⟨p.val + x, hx⟩ +
      S.coeff i j ⟨p.val + x, hx⟩ * S.coeff i k ⟨p.val + x, hx⟩ = 0 at hz
    dsimp only [γ]
    rw [hd]
    simp only [extend, hx, ↓reduceDIte]
    linear_combination hz
  have hcurl : ∀ x ∈ V, ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      fderiv ℝ (γ i j) x (Pi.single k 1) = fderiv ℝ (γ i k) x (Pi.single j 1) := by
    intro x hx i j k hij hik hjk
    have hd (a b : ι) := fderiv_comp_translate (p : ι → ℝ) x
      (hasFDerivAt_extend hU (S.coeff a b) ⟨p.val + x, hx⟩).differentiableAt
    dsimp only [γ]
    rw [hd, hd]
    exact congrArg (fun f : Functions U => f ⟨p.val + x, hx⟩) (hS i j k hij hik hjk)
  have hpair : Darboux.Pair.CompatibleFunctions γ (fun i j => γ j i) V := by
    intro x hx i j k hij hik hjk
    refine ⟨hcurl x hx i j k hij hik hjk, ?_⟩
    rw [hc x hx j i k hij.symm hjk hik]
    ring
  obtain ⟨r, hrpos, hrR, hsol⟩ := Darboux.Pair.local_smooth_solution_on_open R hR hV hbox
    γ (fun i j => γ j i) hγ (fun i j => hγ j i) hpair
  have hsub : Metric.ball (p : ι → ℝ) r ⊆ U :=
    (Metric.ball_subset_ball ((show (r : ℝ) ≤ R from hrR).trans hRε.le)).trans hεU
  refine ⟨r, hrpos, hsub, fun φ hφ => ?_⟩
  obtain ⟨f, hf, hpde, haxis⟩ := hsol φ hφ
  have htrans {q : ι → ℝ} (hq : q ∈ Metric.ball (p : ι → ℝ) r) :
      q - p ∈ Metric.ball 0 (r : ℝ) := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hq
  have hfi (i : ι) : ContDiffOn ℝ ∞ (fun x => f x i) (Metric.ball 0 (r : ℝ)) :=
    (contDiffOn_pi.mp hf) i
  have hwi (i : ι) : ContDiffOn ℝ ∞ (fun y => f (y - p) i) (Metric.ball (p : ι → ℝ) r) :=
    (hfi i).comp (contDiffOn_id.sub contDiffOn_const) (fun _ hx => htrans hx)
  let w : ι → Functions (Metric.ball (p : ι → ℝ) r) :=
    fun i => ofContDiffOn (fun y => f (y - p) i) (hwi i)
  refine ⟨w, ?_, ?_⟩
  · intro i j hij
    apply Subtype.ext
    funext q
    change directional Metric.isOpen_ball (Pi.single j 1) (w i) q =
      restrict hsub (S.coeff i j) q * w i q + restrict hsub (S.coeff j i) q * w j q
    rw [show w i = ofContDiffOn (fun y => f (y - p) i) (hwi i) from rfl,
      directional_ofContDiffOn, restrict_apply, restrict_apply]
    rw [fderiv_comp_sub (p : ι → ℝ) (q : ι → ℝ)
      (((hfi i).contDiffAt (Metric.isOpen_ball.mem_nhds (htrans q.property))).differentiableAt (by simp))]
    rw [hpde (q - p) (htrans q.property) i j hij]
    simp only [γ, add_sub_cancel, w, ofContDiffOn_apply]
    rw [extend_apply U (S.coeff i j) ⟨q.val, hsub q.property⟩,
      extend_apply U (S.coeff j i) ⟨q.val, hsub q.property⟩]
  · intro i s q hq
    change f ((q : ι → ℝ) - p) i = φ i s
    have hs : |s| < r := by
      have hnorm : ‖(q : ι → ℝ) - p‖ < r := by
        simpa only [Metric.mem_ball, dist_eq_norm] using q.property
      rw [hq, add_sub_cancel_left] at hnorm
      simpa only [Pi.norm_single, Real.norm_eq_abs] using hnorm
    rw [hq, add_sub_cancel_left]
    exact haxis i s hs

/-- Necessity already follows from realizing arbitrary gradient values locally. -/
theorem semiHamiltonian_of_locallyDensityAxisSolvable (S : System hU)
    (hS : LocallyDensityAxisSolvable hU S) : S.IsSemiHamiltonian := by
  intro i j k hij hik hjk
  apply Subtype.ext
  funext p
  obtain ⟨r, hr, hVU, hsol⟩ := hS p
  let V := Metric.ball (p : ι → ℝ) (r : ℝ)
  have hp : (p : ι → ℝ) ∈ V := Metric.mem_ball_self hr
  let SV := restrictSystem hU Metric.isOpen_ball hVU S
  let φ : ι → C(ℝ, ℝ) := fun a => ContinuousMap.const ℝ (if a = i then 1 else 0)
  obtain ⟨w, hw, haxis⟩ := hsol φ (fun _ => contDiff_const)
  have hv (a : ι) : w a ⟨p, hp⟩ = if a = i then 1 else 0 :=
    haxis a 0 ⟨p, hp⟩ (by simp)
  have hz := SV.densityObstruction_eq_zero_of_solution hw i j k hij hik hjk
  rw [SV.densityObstruction_eq] at hz
  have he := congrArg (eval (⟨p, hp⟩ : V)) hz
  simp only [map_sub, map_add, map_mul, map_zero] at he
  change _ = (0 : ℝ) at he
  have hv' (a : ι) : eval (⟨p, hp⟩ : V) (w a) = if a = i then 1 else 0 := hv a
  rw [hv' i, hv' j, hv' k] at he
  simp [hij.symm, hik.symm] at he
  have hd (a b c : ι) : eval (⟨p, hp⟩ : V) ((coordinateDerivations Metric.isOpen_ball).deriv c (SV.coeff a b)) =
      (coordinateDerivations hU).deriv c (S.coeff a b) p := by
    change derivation Metric.isOpen_ball (Pi.single c 1) (restrict hVU (S.coeff a b)) ⟨p, hp⟩ = _
    rw [← restrict_derivation hU Metric.isOpen_ball, restrict_apply]
    rfl
  rw [hd, hd] at he
  exact sub_eq_zero.mp he

theorem semiHamiltonian_iff_locallyDensityAxisSolvable (S : System hU) :
    S.IsSemiHamiltonian ↔ LocallyDensityAxisSolvable hU S :=
  ⟨locallyDensityAxisSolvable_of_semiHamiltonian hU S,
    semiHamiltonian_of_locallyDensityAxisSolvable hU S⟩

end SemiHamiltonian.Smooth
