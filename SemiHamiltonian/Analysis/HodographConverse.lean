module

public import SemiHamiltonian.Analysis.TsarevCurve
public import SemiHamiltonian.Analysis.HodographTransport

/-! The converse generalized hodograph theorem for actual C∞ PDE solutions. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set Filter

set_option backward.isDefEq.respectTransparency.types false

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {U : Set (ι → ℝ)} (hU : IsOpen U) (S : System hU)

/-- Every nondegenerate smooth hydrodynamic solution is locally represented
by an actual smooth commuting speed. Only spatial nondegeneracy at the base
point is assumed; neither a hodograph relation nor its propagation is assumed. -/
theorem generalized_hodograph_converse (hS : S.IsSemiHamiltonian)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {q₀ : ℝ × ℝ} (hq₀ : q₀ ∈ Ω)
    {u : (ℝ × ℝ) → (ι → ℝ)} (hu : ContDiffOn ℝ ∞ u Ω) (hm : MapsTo u Ω U)
    (hpde : ∀ q ∈ Ω, ∀ i, fderiv ℝ u q (0, 1) i =
      extend U (S.speed i) (u q) * fderiv ℝ u q (1, 0) i)
    (hreg : ∀ i, fderiv ℝ u q₀ (1, 0) i ≠ 0) :
    ∃ (V : Set (ι → ℝ)) (hV : IsOpen V) (hVU : V ⊆ U), u q₀ ∈ V ∧
      ∃ w : ι → Functions V, (restrictSystem hU hV hVU S).IsCommutingSpeed w ∧
        ∃ W : Set (ℝ × ℝ), IsOpen W ∧ q₀ ∈ W ∧ W ⊆ Ω ∧ MapsTo u W V ∧
          ∀ q ∈ W, HodographRelation hV (restrictSystem hU hV hVU S) w q (u q) := by
  let τ : ℝ → ℝ × ℝ := fun s => (q₀.1 + s, q₀.2)
  have hτ : ContDiff ℝ ∞ τ := (contDiff_const.add contDiff_id).prodMk contDiff_const
  have hτ0 : τ 0 = q₀ := by simp [τ]
  let I := τ ⁻¹' Ω
  have hI : IsOpen I := hΩ.preimage hτ.continuous
  have h0 : (0 : ℝ) ∈ I := by simpa [I, τ] using hq₀
  let κ := fun s => u (τ s)
  have hκ : ContDiffOn ℝ ∞ κ I := hu.comp hτ.contDiffOn (fun _ hs => hs)
  have hκ0 : κ 0 = u q₀ := by simp [κ, τ]
  have hκm : MapsTo κ I U := fun _ hs => hm hs
  have hκreg (i : ι) : deriv (fun s => κ s i) 0 ≠ 0 := by
    have hdt : HasDerivAt τ (1, 0) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_add q₀.1).prodMk (hasDerivAt_const (0 : ℝ) q₀.2)
    have hdu := ((contDiffOn_pi.mp hu i).contDiffAt (hΩ.mem_nhds hq₀)).differentiableAt (by simp)
    have hdu' : HasFDerivAt (fun y => u y i) (fderiv ℝ (fun y => u y i) q₀) (τ 0) :=
      hτ0.symm ▸ hdu.hasFDerivAt
    have hd := hdu'.comp_hasDerivAt (0 : ℝ) hdt
    have hdi := (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp q₀
      ((hu.contDiffAt (hΩ.mem_nhds hq₀)).differentiableAt (by simp)).hasFDerivAt
    have hh : deriv (fun s => κ s i) 0 = fderiv ℝ u q₀ (1, 0) i := by
      rw [show (fun s => κ s i) = (fun y => u y i) ∘ τ from rfl, hd.deriv]
      exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1, 0)) hdi.fderiv
    rw [hh]
    exact hreg i
  let φ := fun i s => q₀.1 + s + q₀.2 * extend U (S.speed i) (κ s)
  have hφ (i : ι) : ContDiffOn ℝ ∞ (φ i) I :=
    (contDiffOn_const.add contDiffOn_id).add
      (contDiffOn_const.mul ((smooth U (S.speed i)).comp hκ hκm))
  obtain ⟨V, hV, hVU, hpV, w, hw, ε, hε, htrace⟩ :=
    commutingSpeed_on_curve hU S hS hI h0 κ hκ (hκ0 ▸ hm hq₀) hκreg φ hφ
  let SV := restrictSystem hU hV hVU S
  have hv (r : ι → ℝ) (hr : r ∈ V) (i : ι) :
      extend V (SV.speed i) r = extend U (S.speed i) r := by
    rw [show extend V (SV.speed i) r = SV.speed i ⟨r, hr⟩ from extend_apply V (SV.speed i) ⟨r, hr⟩]
    change restrict hVU (S.speed i) ⟨r, hr⟩ = _
    rw [restrict_apply]
    exact (extend_apply U (S.speed i) ⟨r, hVU hr⟩).symm
  let Ω' := (Ω ∩ u ⁻¹' V) ∩ {q : ℝ × ℝ | |q.1 - q₀.1| < ε}
  have hΩ' : IsOpen Ω' := (hu.continuousOn.isOpen_inter_preimage hΩ hV).inter
    (isOpen_lt ((continuous_fst.sub continuous_const).abs) continuous_const)
  have hq' : q₀ ∈ Ω' := ⟨⟨hq₀, show u q₀ ∈ V from hκ0 ▸ hpV⟩, by simpa using hε⟩
  have hu' : ContDiffOn ℝ ∞ u Ω' := hu.mono (fun _ hq => hq.1.1)
  have hm' : MapsTo u Ω' V := fun _ hq => hq.1.2
  have hpde' : ∀ q ∈ Ω', ∀ i, fderiv ℝ u q (0, 1) i =
      extend V (SV.speed i) (u q) * fderiv ℝ u q (1, 0) i := by
    intro q hq i
    rw [hv _ hq.1.2]
    exact hpde q hq.1.1 i
  have hz : ∀ q ∈ Ω', q.2 = q₀.2 → HodographRelation hV SV w q (u q) := by
    intro q hq ht i
    obtain ⟨hsV, hs⟩ := htrace (q.1 - q₀.1) hq.2
    have heq : τ (q.1 - q₀.1) = q := by ext <;> simp [τ, ht]
    have heq' : κ (q.1 - q₀.1) = u q := congrArg u heq
    have hh : extend V (w i) (κ (q.1 - q₀.1)) = φ i (q.1 - q₀.1) :=
      (extend_apply V (w i) ⟨_, hsV⟩).trans (hs i)
    dsimp only [φ] at hh
    rw [heq'] at hh
    change extend V (w i) (u q) = q.1 + q.2 * extend V (SV.speed i) (u q)
    rw [hh, hv _ hq.1.2, ht]
    ring
  obtain ⟨δ, hδ, hh⟩ := hodograph_relation_propagates hV SV w hw hΩ' hq' hu' hm' hpde' hz
  refine ⟨V, hV, hVU, hκ0 ▸ hpV, w, hw, Ω' ∩ Metric.ball q₀ δ,
    hΩ'.inter Metric.isOpen_ball, ⟨hq', Metric.mem_ball_self hδ⟩,
    fun _ hq => hq.1.1.1, fun _ hq => hq.1.1.2, ?_⟩
  intro q hq
  exact hh q (by simpa only [Metric.mem_ball, dist_eq_norm] using hq.2)

/-- A smooth graph of commuting hodograph equations automatically has an
invertible state Jacobian. This connects the converse to the implicit theorem. -/
theorem hodograph_stateJacobian_invertible (w : ι → Functions U) (hw : S.IsCommutingSpeed w)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {u : (ℝ × ℝ) → (ι → ℝ)}
    (hu : ContDiffOn ℝ ∞ u Ω) (hm : MapsTo u Ω U)
    (he : ∀ q ∈ Ω, HodographRelation hU S w q (u q))
    (q : ℝ × ℝ) (hq : q ∈ Ω) :
    ((fderiv ℝ (hodographResidual hU S w) (q, u q)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ) (ι → ℝ))).IsInvertible := by
  let r : U := ⟨u q, hm hq⟩
  let L := hodographRow hU S w q (u q)
  have hdiag (i : ι) (z : ι → ℝ) : L i z = L i (Pi.single i 1) * z i := by
    have hz : z = ∑ j, z j • Pi.single j (1 : ℝ) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hz, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · ring
    · intro j _ hji
      rw [show L i (Pi.single j 1) = 0 from hodographRow_offDiagonal hU S w hw q r (he q hq) i j hji.symm, mul_zero]
    · simp
  have hn (i : ι) : L i (Pi.single i 1) ≠ 0 := by
    have hh := hodograph_derivative hU S w hΩ hu hm he hq i (1, 0)
    change L i _ = _ at hh
    rw [hdiag] at hh
    simp only [zero_mul, add_zero] at hh
    intro hz
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  have hdr (i : ι) : HasFDerivAt (fun y => hodographResidual hU S w (q, y) i) (L i) (u q) := by
    have hh := (hasFDerivAt_extend hU (w i) r).sub
      ((hasFDerivAt_const q.1 (u q)).add ((hasFDerivAt_extend hU (S.speed i) r).const_mul q.2))
    apply hh.congr_fderiv
    change _ - (0 + _) = _ - _
    rw [zero_add]
  have hd := hasFDerivAt_pi.mpr hdr
  have hF := ((hodographResidual_smooth hU S w).contDiffAt
    ((isOpen_univ.prod hU).mem_nhds (show (q, u q) ∈ univ ×ˢ U from ⟨mem_univ _, hm hq⟩))).differentiableAt (by simp)
  have hd' := hF.hasFDerivAt.comp (u q)
    ((hasFDerivAt_const q (u q)).prodMk (hasFDerivAt_id (u q)))
  have heq : (fderiv ℝ (hodographResidual hU S w) (q, u q)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ) (ι → ℝ)) = ContinuousLinearMap.pi L := hd'.unique hd
  rw [heq]
  apply Geometry.isInvertible_of_injective
  intro x y hxy
  funext i
  have hh : L i x = L i y := congrFun hxy i
  rw [hdiag i x, hdiag i y] at hh
  exact mul_left_cancel₀ (hn i) hh

end SemiHamiltonian.Smooth
