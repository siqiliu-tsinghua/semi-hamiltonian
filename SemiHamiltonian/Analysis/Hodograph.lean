module

public import SemiHamiltonian.Analysis.TsarevLocal
public import SemiHamiltonian.Geometry.LocalInverse

/-! Actual smooth solutions supplied by the generalized hodograph formula.
The sign convention is u_t^i = v^i(u) u_x^i. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set Filter

set_option backward.isDefEq.respectTransparency.types false

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem linearForm_diagonal (L : (ι → ℝ) →L[ℝ] ℝ) (i : ι)
    (hL : ∀ j, j ≠ i → L (Pi.single j 1) = 0) (z : ι → ℝ) :
    L z = L (Pi.single i 1) * z i := by
  have hz : z = ∑ j, z j • Pi.single j (1 : ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hz, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hji; rw [hL j hji, mul_zero]
  · simp

variable {U : Set (ι → ℝ)} (hU : IsOpen U) (S : System hU) (w : ι → Functions U)

noncomputable def hodographRow (q : ℝ × ℝ) (r : ι → ℝ) (i : ι) : (ι → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (extend U (w i)) r - q.2 • fderiv ℝ (extend U (S.speed i)) r

def HodographRelation (q : ℝ × ℝ) (r : ι → ℝ) : Prop :=
  ∀ i, extend U (w i) r = q.1 + q.2 * extend U (S.speed i) r

theorem hodographRow_offDiagonal (hw : S.IsCommutingSpeed w) (q : ℝ × ℝ) (r : U)
    (he : HodographRelation hU S w q r) (i j : ι) (hij : i ≠ j) :
    hodographRow hU S w q r i (Pi.single j 1) = 0 := by
  have hwij := congrArg (fun f : Functions U => f r) (hw i j hij)
  have hvij := congrArg (fun f : Functions U => f r) (S.speed_deriv i j hij)
  change fderiv ℝ (extend U (w i)) r (Pi.single j 1) =
    S.coeff i j r * (w j r - w i r) at hwij
  change fderiv ℝ (extend U (S.speed i)) r (Pi.single j 1) =
    S.coeff i j r * (S.speed j r - S.speed i r) at hvij
  have he' (k : ι) : w k r = q.1 + q.2 * S.speed k r := by
    simpa only [extend_apply] using he k
  change fderiv ℝ (extend U (w i)) r (Pi.single j 1) -
    q.2 * fderiv ℝ (extend U (S.speed i)) r (Pi.single j 1) = 0
  rw [hwij, hvij, he' i, he' j]
  ring

theorem hodograph_derivative {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {u : (ℝ × ℝ) → (ι → ℝ)}
    (hu : ContDiffOn ℝ ∞ u Ω) (hmap : MapsTo u Ω U)
    (he : ∀ q ∈ Ω, HodographRelation hU S w q (u q))
    {q : ℝ × ℝ} (hq : q ∈ Ω) (i : ι) (d : ℝ × ℝ) :
    hodographRow hU S w q (u q) i (fderiv ℝ u q d) =
      d.1 + d.2 * extend U (S.speed i) (u q) := by
  have hdu := ((hu.contDiffAt (hΩ.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  have hdw := (hasFDerivAt_extend hU (w i) ⟨u q, hmap hq⟩).comp q hdu
  have hdv := (hasFDerivAt_extend hU (S.speed i) ⟨u q, hmap hq⟩).comp q hdu
  have hdr := (hasFDerivAt_fst (𝕜 := ℝ) (p := q)).add
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := q)).mul hdv)
  have heq : (fun z => extend U (w i) (u z)) =ᶠ[𝓝 q]
      (fun z : ℝ × ℝ => z.1 + z.2 * extend U (S.speed i) (u z)) := by
    filter_upwards [hΩ.mem_nhds hq] with z hz
    exact he z hz i
  have hh := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L d)
    (hdw.unique (hdr.congr_of_eventuallyEq heq))
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
    smul_eq_mul] at hh
  change fderiv ℝ (extend U (w i)) (u q) (fderiv ℝ u q d) = d.1 +
    (q.2 * fderiv ℝ (extend U (S.speed i)) (u q) (fderiv ℝ u q d) +
      extend U (S.speed i) (u q) * d.2) at hh
  change fderiv ℝ (extend U (w i)) (u q) (fderiv ℝ u q d) -
    q.2 * fderiv ℝ (extend U (S.speed i)) (u q) (fderiv ℝ u q d) = _
  linear_combination hh

/-- Every smooth graph satisfying the hodograph equations solves the original
hydrodynamic PDE. Its spatial derivatives are necessarily nonzero. -/
theorem hodograph_solves (hw : S.IsCommutingSpeed w)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {u : (ℝ × ℝ) → (ι → ℝ)}
    (hu : ContDiffOn ℝ ∞ u Ω) (hmap : MapsTo u Ω U)
    (he : ∀ q ∈ Ω, HodographRelation hU S w q (u q)) :
    ∀ q ∈ Ω, ∀ i,
      fderiv ℝ u q (0, 1) i = extend U (S.speed i) (u q) * fderiv ℝ u q (1, 0) i ∧
      fderiv ℝ u q (1, 0) i ≠ 0 := by
  intro q hq i
  let L := hodographRow hU S w q (u q) i
  have hL (z : ι → ℝ) : L z = L (Pi.single i 1) * z i :=
    linearForm_diagonal L i (fun j hji =>
      hodographRow_offDiagonal hU S w hw q ⟨u q, hmap hq⟩ (he q hq) i j hji.symm) z
  have hx := hodograph_derivative hU S w hΩ hu hmap he hq i (1, 0)
  have ht := hodograph_derivative hU S w hΩ hu hmap he hq i (0, 1)
  change L _ = _ at hx ht
  rw [hL] at hx ht
  simp only [zero_mul, one_mul, add_zero, zero_add] at hx ht
  have hn : L (Pi.single i 1) ≠ 0 := by intro hz; rw [hz, zero_mul] at hx; exact zero_ne_one hx
  refine ⟨?_, ?_⟩
  · apply mul_left_cancel₀ hn
    linear_combination ht - extend U (S.speed i) (u q) * hx
  · intro hz; rw [hz, mul_zero] at hx; exact zero_ne_one hx

noncomputable def hodographResidual (z : (ℝ × ℝ) × (ι → ℝ)) (i : ι) : ℝ :=
  extend U (w i) z.2 - (z.1.1 + z.1.2 * extend U (S.speed i) z.2)

theorem hodographResidual_smooth :
    ContDiffOn ℝ ∞ (hodographResidual hU S w) (univ ×ˢ U) := by
  apply contDiffOn_pi.mpr
  intro i
  exact ((smooth U (w i)).comp contDiffOn_snd (fun _ hx => hx.2)).sub
    (contDiffOn_fst.fst.add (contDiffOn_fst.snd.mul
      ((smooth U (S.speed i)).comp contDiffOn_snd (fun _ hx => hx.2))))

/-- Generalized hodograph local existence, with a genuine smooth implicit
solution and uniqueness in an open neighbourhood of the base point. -/
theorem generalized_hodograph (hw : S.IsCommutingSpeed w) (q₀ : ℝ × ℝ) (r₀ : U)
    (hzero : HodographRelation hU S w q₀ r₀)
    (hinv : ((fderiv ℝ (hodographResidual hU S w) (q₀, (r₀ : ι → ℝ))).comp
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ) (ι → ℝ))).IsInvertible) :
    ∃ (Ω : Set (ℝ × ℝ)) (B : Set ((ℝ × ℝ) × (ι → ℝ))) (u : (ℝ × ℝ) → (ι → ℝ)),
      IsOpen Ω ∧ q₀ ∈ Ω ∧ IsOpen B ∧ (q₀, (r₀ : ι → ℝ)) ∈ B ∧ B ⊆ univ ×ˢ U ∧
      u q₀ = r₀ ∧ ContDiffOn ℝ ∞ u Ω ∧
      (∀ q ∈ Ω, (q, u q) ∈ B ∧ HodographRelation hU S w q (u q)) ∧
      (∀ q ∈ Ω, ∀ i,
        fderiv ℝ u q (0, 1) i = extend U (S.speed i) (u q) * fderiv ℝ u q (1, 0) i ∧
        fderiv ℝ u q (1, 0) i ≠ 0) ∧
      ∀ q ∈ Ω, ∀ r, (q, r) ∈ B → HodographRelation hU S w q r → r = u q := by
  have hf0 : hodographResidual hU S w (q₀, (r₀ : ι → ℝ)) = 0 := by
    funext i
    exact sub_eq_zero.mpr (hzero i)
  obtain ⟨Ω, B, u, hΩ, hqΩ, hB, hpB, hBU, hu0, hu, hgraph, huniq⟩ :=
    Geometry.exists_smooth_implicit (isOpen_univ.prod hU) (hodographResidual_smooth hU S w)
      (show (q₀, (r₀ : ι → ℝ)) ∈ univ ×ˢ U from ⟨mem_univ _, r₀.property⟩) hinv
  have he : ∀ q ∈ Ω, HodographRelation hU S w q (u q) := by
    intro q hq i
    have hh := congrFun (hgraph q hq).2 i
    rw [hf0] at hh
    exact sub_eq_zero.mp hh
  have hm : MapsTo u Ω U := fun q hq => (hBU (hgraph q hq).1).2
  refine ⟨Ω, B, u, hΩ, hqΩ, hB, hpB, hBU, hu0, hu,
    fun q hq => ⟨(hgraph q hq).1, he q hq⟩, hodograph_solves hU S w hw hΩ hu hm he, ?_⟩
  intro q hq r hr her
  apply huniq q hq r hr
  rw [hf0]
  funext i
  exact sub_eq_zero.mpr (her i)

end SemiHamiltonian.Smooth
