module

public import SemiHamiltonian.Analysis.Hodograph
public import SemiHamiltonian.Analysis.TransportUniqueness

/-! Propagation of the hodograph equations along an actual hydrodynamic solution. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set Filter

set_option backward.isDefEq.respectTransparency.types false

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {U : Set (ι → ℝ)} (hU : IsOpen U) (S : System hU) (w : ι → Functions U)

noncomputable def graphResidual (u : (ℝ × ℝ) → (ι → ℝ)) (i : ι) (q : ℝ × ℝ) : ℝ :=
  extend U (w i) (u q) - (q.1 + q.2 * extend U (S.speed i) (u q))

theorem graphResidual_smooth {Ω : Set (ℝ × ℝ)} {u : (ℝ × ℝ) → (ι → ℝ)}
    (hu : ContDiffOn ℝ ∞ u Ω) (hm : MapsTo u Ω U) (i : ι) :
    ContDiffOn ℝ ∞ (graphResidual hU S w u i) Ω :=
  ((smooth U (w i)).comp hu hm).sub
    (contDiffOn_fst.add (contDiffOn_snd.mul ((smooth U (S.speed i)).comp hu hm)))

theorem graphResidual_transport (hw : S.IsCommutingSpeed w)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {u : (ℝ × ℝ) → (ι → ℝ)}
    (hu : ContDiffOn ℝ ∞ u Ω) (hm : MapsTo u Ω U)
    (hpde : ∀ q ∈ Ω, ∀ i, fderiv ℝ u q (0, 1) i =
      extend U (S.speed i) (u q) * fderiv ℝ u q (1, 0) i)
    (q : ℝ × ℝ) (hq : q ∈ Ω) (i : ι) :
    fderiv ℝ (graphResidual hU S w u i) q (extend U (S.speed i) (u q), -1) =
      -(∑ j, (extend U (S.coeff i j) (u q) *
        (extend U (S.speed j) (u q) - extend U (S.speed i) (u q)) *
        fderiv ℝ u q (1, 0) j) *
          (graphResidual hU S w u j q - graphResidual hU S w u i q)) := by
  let r : U := ⟨u q, hm hq⟩
  let v : ι → ℝ := fun k => S.speed k r
  let L := hodographRow hU S w q (u q) i
  have hdu := ((hu.contDiffAt (hΩ.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  have hdw := (hasFDerivAt_extend hU (w i) r).comp q hdu
  have hdv := (hasFDerivAt_extend hU (S.speed i) r).comp q hdu
  have hd := (hdw.sub ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).add
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := q)).mul hdv))).fderiv
  change fderiv ℝ (graphResidual hU S w u i) q = _ at hd
  have hdir : (v i, (-1 : ℝ)) = v i • (1, 0) - (0, 1) := by ext <;> simp
  have hrow (j : ι) (hij : i ≠ j) : L (Pi.single j 1) =
      S.coeff i j r * (graphResidual hU S w u j q - graphResidual hU S w u i q) := by
    have hwij := congrArg (fun f : Functions U => f r) (hw i j hij)
    have hvij := congrArg (fun f : Functions U => f r) (S.speed_deriv i j hij)
    change fderiv ℝ (extend U (w i)) (u q) (Pi.single j 1) =
      S.coeff i j r * (w j r - w i r) at hwij
    change fderiv ℝ (extend U (S.speed i)) (u q) (Pi.single j 1) =
      S.coeff i j r * (S.speed j r - S.speed i r) at hvij
    change fderiv ℝ (extend U (w i)) (u q) (Pi.single j 1) -
      q.2 * fderiv ℝ (extend U (S.speed i)) (u q) (Pi.single j 1) = _
    rw [hwij, hvij]
    simp only [graphResidual, show u q = (r : ι → ℝ) from rfl, extend_apply]
    ring
  have hvec : fderiv ℝ u q (v i, -1) =
      ∑ j, ((v i - v j) * fderiv ℝ u q (1, 0) j) • Pi.single j (1 : ℝ) := by
    rw [hdir, map_sub, map_smul]
    funext j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hpde q hq j]
    rw [show extend U (S.speed j) (u q) = v j from extend_apply U (S.speed j) r]
    simp [Finset.sum_apply, Pi.single_apply, sub_mul]
  have he : fderiv ℝ (graphResidual hU S w u i) q (v i, -1) =
      L (fderiv ℝ u q (v i, -1)) := by
    rw [hd]
    change fderiv ℝ (extend U (w i)) (u q) (fderiv ℝ u q (v i, -1)) -
      (v i + (q.2 * fderiv ℝ (extend U (S.speed i)) (u q) (fderiv ℝ u q (v i, -1)) +
        extend U (S.speed i) (u q) * (-1))) = _
    change _ = fderiv ℝ (extend U (w i)) (u q) (fderiv ℝ u q (v i, -1)) -
      q.2 * fderiv ℝ (extend U (S.speed i)) (u q) (fderiv ℝ u q (v i, -1))
    rw [show extend U (S.speed i) (u q) = v i from extend_apply U (S.speed i) r]
    ring
  rw [show extend U (S.speed i) (u q) = v i from extend_apply U (S.speed i) r, he, hvec, map_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp [v, r, graphResidual, sub_self]
  · rw [hrow j hij]
    simp only [show u q = (r : ι → ℝ) from rfl, extend_apply]
    dsimp only [v]
    ring

/-- Matching on a piece of the initial line forces the hodograph relation
on a genuine spacetime neighbourhood of the given solution. -/
theorem hodograph_relation_propagates (hw : S.IsCommutingSpeed w)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {q₀ : ℝ × ℝ} (h0 : q₀ ∈ Ω)
    {u : (ℝ × ℝ) → (ι → ℝ)} (hu : ContDiffOn ℝ ∞ u Ω) (hm : MapsTo u Ω U)
    (hpde : ∀ q ∈ Ω, ∀ i, fderiv ℝ u q (0, 1) i =
      extend U (S.speed i) (u q) * fderiv ℝ u q (1, 0) i)
    (hzero : ∀ q ∈ Ω, q.2 = q₀.2 → HodographRelation hU S w q (u q)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q, ‖q - q₀‖ < δ → HodographRelation hU S w q (u q) := by
  let v := fun q i => extend U (S.speed i) (u q)
  let c := fun q i j => extend U (S.coeff i j) (u q) * (v q j - v q i) *
    fderiv ℝ u q (1, 0) j
  have hv : ContinuousOn v Ω := continuousOn_pi.mpr (fun i => ((smooth U (S.speed i)).comp hu hm).continuousOn)
  have hc : ContinuousOn c Ω := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (((smooth U (S.coeff i j)).comp hu hm).continuousOn.mul
      ((continuousOn_pi.mp hv j).sub (continuousOn_pi.mp hv i))).mul
      (continuousOn_pi.mp ((hu.fderiv_of_isOpen hΩ (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn j)
  obtain ⟨δ, hδ, hh⟩ := Analysis.transport_difference_zero_near_point hΩ h0
    (graphResidual hU S w u) v c
    (fun i p hp => ((graphResidual_smooth hU S w hu hm i).contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp))
    hv hc (fun p hp ht i => sub_eq_zero.mpr (hzero p hp ht i))
    (graphResidual_transport hU S w hw hΩ hu hm hpde)
  exact ⟨δ, hδ, fun q hq i => sub_eq_zero.mp (hh q hq i)⟩

end SemiHamiltonian.Smooth
