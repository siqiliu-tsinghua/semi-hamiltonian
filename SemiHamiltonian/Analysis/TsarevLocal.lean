module

public import SemiHamiltonian.Analysis.SmoothSystem
public import SemiHamiltonian.Darboux.LocalSmoothData

/-! Tsarev's local smooth integrability theorem in actual Riemann coordinates. -/

@[expose] public section

open scoped NNReal Topology ContDiff Classical
open Filter Set

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)} (hU : IsOpen U)

/-- Arbitrary smooth single-variable data on all coordinate axes through each
base point extend to a genuine smooth commuting speed. The radius is chosen
before the data. Balls use the sup norm, hence are coordinate cubes. -/
def LocallyAxisSolvable (S : System hU) : Prop :=
  ∀ p : U, ∃ (r : ℝ≥0) (_ : 0 < r) (hsub : Metric.ball (p : ι → ℝ) r ⊆ U),
    ∀ (φ : ι → C(ℝ, ℝ)), (∀ i, ContDiff ℝ ∞ (φ i)) →
      ∃ w : ι → Functions (Metric.ball (p : ι → ℝ) r),
        (restrictSystem hU Metric.isOpen_ball hsub S).IsCommutingSpeed w ∧
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

theorem locallyAxisSolvable_of_semiHamiltonian (S : System hU) (hS : S.IsSemiHamiltonian) :
    LocallyAxisSolvable hU S := by
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
  obtain ⟨r, hrpos, hrR, hsol⟩ := Darboux.local_smooth_solution_on_open R hR hV hbox γ hγ hc
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
      restrict hsub (S.coeff i j) q * (w j q - w i q)
    rw [show w i = ofContDiffOn (fun y => f (y - p) i) (hwi i) from rfl,
      directional_ofContDiffOn, restrict_apply]
    rw [fderiv_comp_sub (p : ι → ℝ) (q : ι → ℝ)
      (((hfi i).contDiffAt (Metric.isOpen_ball.mem_nhds (htrans q.property))).differentiableAt (by simp))]
    rw [hpde (q - p) (htrans q.property) i j hij]
    simp only [γ, add_sub_cancel, w, ofContDiffOn_apply]
    rw [show extend U (S.coeff i j) q = S.coeff i j ⟨q, hsub q.property⟩ from
      extend_apply U (S.coeff i j) ⟨q.val, hsub q.property⟩]
  · intro i s q hq
    change f ((q : ι → ℝ) - p) i = φ i s
    have hs : |s| < r := by
      have hnorm : ‖(q : ι → ℝ) - p‖ < r := by
        simpa only [Metric.mem_ball, dist_eq_norm] using q.property
      rw [hq, add_sub_cancel_left] at hnorm
      simpa only [Pi.norm_single, Real.norm_eq_abs] using hnorm
    rw [hq, add_sub_cancel_left]
    exact haxis i s hs

theorem LocallyAxisSolvable.locallyRich {S : System hU} (hS : LocallyAxisSolvable hU S) :
    LocallyRich hU S := by
  intro p
  obtain ⟨r, hr, hsub, hsol⟩ := hS p
  have hp : (p : ι → ℝ) ∈ Metric.ball (p : ι → ℝ) r := Metric.mem_ball_self hr
  refine ⟨Metric.ball (p : ι → ℝ) r, Metric.isOpen_ball, hsub, hp, fun a => ?_⟩
  obtain ⟨w, hw, ha⟩ := hsol (fun i => ContinuousMap.const ℝ (a i)) (fun _ => contDiff_const)
  refine ⟨w, hw, fun i => ?_⟩
  exact ha i 0 ⟨p, hp⟩ (by simp)

/-- Tsarev sufficiency with the full freedom of n smooth functions of one variable. -/
theorem semiHamiltonian_iff_locallyAxisSolvable (S : System hU) :
    S.IsSemiHamiltonian ↔ LocallyAxisSolvable hU S :=
  ⟨locallyAxisSolvable_of_semiHamiltonian hU S,
    fun h => semiHamiltonian_of_locallyRich hU S (h.locallyRich hU)⟩

/-- Even the weaker pointwise richness of actual local smooth solutions is
equivalent to semi-Hamiltonianity. -/
theorem semiHamiltonian_iff_locallyRich (S : System hU) :
    S.IsSemiHamiltonian ↔ LocallyRich hU S :=
  ⟨fun h => (locallyAxisSolvable_of_semiHamiltonian hU S h).locallyRich hU,
    semiHamiltonian_of_locallyRich hU S⟩

/-- The usual derivative-ratio criterion for real, strictly hyperbolic smooth speeds. -/
theorem tsarev_iff_locallyAxisSolvable (v : ι → Functions U) (hv : StrictlyHyperbolic v) :
    (∀ (x : U) (i j k : ι), i ≠ j → i ≠ k → j ≠ k →
      fderiv ℝ (tsarevCoefficient v i j) x (Pi.single k 1) =
        fderiv ℝ (tsarevCoefficient v i k) x (Pi.single j 1)) ↔
    LocallyAxisSolvable hU (ofSpeeds hU v hv) :=
  (ofSpeeds_semiHamiltonian_iff hU v hv).symm.trans
    (semiHamiltonian_iff_locallyAxisSolvable hU _)

end SemiHamiltonian.Smooth
