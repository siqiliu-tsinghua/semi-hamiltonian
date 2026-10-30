module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-! A local uniqueness argument for smooth diagonal transport systems.
The maximum principle uses backward characteristic directions on a compact
trapezoid; no existence or uniqueness theorem for PDEs is postulated. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Analysis

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem weighted_square_hasFDerivAt (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hf : DifferentiableAt ℝ f p) (c : ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => Real.exp (-c * q.2) * (f q) ^ 2)
      (Real.exp (-c * p.2) •
        ((2 * f p) • fderiv ℝ f p - (c * (f p) ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
  have hh := (((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).const_mul (-c)).exp).mul
    (hf.hasFDerivAt.mul hf.hasFDerivAt)
  simp only [pow_two]
  apply hh.congr_fderiv
  apply ContinuousLinearMap.ext
  intro z
  simp only [add_apply, sub_apply, smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

theorem transport_zero_of_compact
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (f : ι → ℝ × ℝ → ℝ) (v : (ℝ × ℝ) → ι → ℝ) (b : (ℝ × ℝ) → ι → ι → ℝ)
    (hf : ∀ i p, p ∈ K → DifferentiableAt ℝ (f i) p)
    (ht : ∀ p ∈ K, 0 ≤ p.2)
    (hzero : ∀ p ∈ K, p.2 = 0 → ∀ i, f i p = 0)
    (hpde : ∀ p ∈ K, ∀ i,
      fderiv ℝ (f i) p (v p i, -1) = -(∑ j, b p i j * f j p))
    (htangent : ∀ p ∈ K, 0 < p.2 → ∀ i, (v p i, -1) ∈ posTangentConeAt K p)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ p ∈ K, ∀ i j, |b p i j| ≤ B) :
    ∀ p ∈ K, ∀ i, f i p = 0 := by
  intro p hp i
  by_contra hne
  letI : TopologicalSpace ι := ⊥
  letI : DiscreteTopology ι := ⟨rfl⟩
  let c : ℝ := 2 * Fintype.card ι * B + 1
  let g : ι × (ℝ × ℝ) → ℝ := fun z => Real.exp (-c * z.2.2) * (f z.1 z.2) ^ 2
  have hg : ContinuousOn g (univ ×ˢ K) := by
    apply continuousOn_prod_of_discrete_left.mpr
    intro j
    have hh : ContinuousOn (f j) K := fun q hq => (hf j q hq).continuousAt.continuousWithinAt
    simp only [mem_prod, mem_univ, true_and]
    change ContinuousOn (fun q : ℝ × ℝ => Real.exp (-c * q.2) * (f j q) ^ 2) K
    exact (continuous_const.mul continuous_snd).rexp.continuousOn.mul (hh.pow 2)
  obtain ⟨⟨k, q⟩, hq, hmax⟩ := (isCompact_univ.prod hK).exists_isMaxOn ⟨(i, p), ⟨mem_univ _, hp⟩⟩ hg
  have hqp : q ∈ K := hq.2
  have hsource : 0 < g (i, p) := mul_pos (Real.exp_pos _) (sq_pos_of_ne_zero hne)
  have hpos : 0 < g (k, q) := hsource.trans_le
    (hmax (show (i, p) ∈ univ ×ˢ K from ⟨mem_univ _, hp⟩))
  have hqpos : 0 < q.2 := by
    have hh := ht q hqp
    by_contra hh'
    have he : q.2 = 0 := le_antisymm (not_lt.mp hh') hh
    have hz := hzero q hqp he k
    change 0 < Real.exp (-c * q.2) * (f k q) ^ 2 at hpos
    rw [hz] at hpos
    norm_num at hpos
  have hsq : 0 < (f k q) ^ 2 := (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hpos
  have hdom (j : ι) : (f j q) ^ 2 ≤ (f k q) ^ 2 := by
    have hh := hmax (show (j, q) ∈ univ ×ˢ K from ⟨mem_univ _, hqp⟩)
    change Real.exp (-c * q.2) * (f j q) ^ 2 ≤ Real.exp (-c * q.2) * (f k q) ^ 2 at hh
    nlinarith [Real.exp_pos (-c * q.2)]
  have hterm (j : ι) : 2 * f k q * (b q k j * f j q) ≤ 2 * B * (f k q) ^ 2 := by
    have hj : |f j q| ≤ |f k q| := (sq_le_sq).mp (hdom j)
    have hh : |f k q * f j q| ≤ (f k q) ^ 2 := by
      rw [abs_mul]
      calc
        _ ≤ |f k q| * |f k q| := mul_le_mul_of_nonneg_left hj (abs_nonneg _)
        _ = _ := by rw [← pow_two, sq_abs]
    have hh' := mul_le_mul (hb q hqp k j) hh (abs_nonneg _) hB
    calc
      _ ≤ 2 * |b q k j * (f k q * f j q)| := by
        have hle := le_abs_self (b q k j * (f k q * f j q))
        nlinarith
      _ ≤ 2 * (B * (f k q) ^ 2) := by rw [abs_mul]; linarith
      _ = _ := by ring
  have hsum : 2 * f k q * (∑ j, b q k j * f j q) ≤
      2 * Fintype.card ι * B * (f k q) ^ 2 := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _j : ι, 2 * B * (f k q) ^ 2 := Finset.sum_le_sum (fun j _ => hterm j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hm : IsMaxOn (fun z : ℝ × ℝ => Real.exp (-c * z.2) * (f k z) ^ 2) K q :=
    fun z hz => hmax (show (k, z) ∈ univ ×ˢ K from ⟨mem_univ _, hz⟩)
  have hd := weighted_square_hasFDerivAt (f k) q (hf k q hqp) c
  have hsign := hm.isLocalMaxOn.hasFDerivWithinAt_nonpos hd.hasFDerivWithinAt (htangent q hqp hqpos k)
  change Real.exp (-c * q.2) *
    (2 * f k q * fderiv ℝ (f k) q (v q k, -1) - c * (f k q) ^ 2 * (-1)) ≤ 0 at hsign
  rw [hpde q hqp k] at hsign
  have hh : 0 < 2 * f k q * (-(∑ j, b q k j * f j q)) - c * (f k q) ^ 2 * (-1) := by
    dsimp only [c]
    nlinarith
  exact (not_lt_of_ge hsign) (mul_pos (Real.exp_pos _) hh)

def transportTrapezoid (a T C : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ T ∧ p.1 + C * p.2 ≤ a ∧ -p.1 + C * p.2 ≤ a}

theorem transportTrapezoid_compact (a T C : ℝ) (hC : 0 ≤ C) :
    IsCompact (transportTrapezoid a T C) := by
  have hc : IsClosed (transportTrapezoid a T C) :=
    (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd continuous_const).inter
        ((isClosed_le (continuous_fst.add (continuous_const.mul continuous_snd)) continuous_const).inter
          (isClosed_le (continuous_fst.neg.add (continuous_const.mul continuous_snd)) continuous_const)))
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hc
  intro p hp
  change p ∈ Icc (-a) a ×ˢ Icc 0 T
  rcases hp with ⟨ht, hT, hx, hx'⟩
  exact ⟨⟨by nlinarith, by nlinarith⟩, ht, hT⟩

theorem transportTrapezoid_backward_tangent (a T C : ℝ) {p : ℝ × ℝ}
    (hp : p ∈ transportTrapezoid a T C) (ht : 0 < p.2) {v : ℝ} (hv : |v| ≤ C) :
    (v, -1) ∈ posTangentConeAt (transportTrapezoid a T C) p := by
  apply mem_posTangentConeAt_of_frequently_mem
  apply Filter.Eventually.frequently
  have he : ∀ᶠ s : ℝ in 𝓝[>] 0, s < p.2 :=
    (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, he] with s hs hst
  have hs' : 0 ≤ s := le_of_lt hs
  rcases abs_le.mp hv with ⟨hvn, hvp⟩
  rcases hp with ⟨hp0, hpT, hpL, hpR⟩
  change 0 ≤ p.2 + s * (-1) ∧ p.2 + s * (-1) ≤ T ∧
    (p.1 + s * v) + C * (p.2 + s * (-1)) ≤ a ∧
    -(p.1 + s * v) + C * (p.2 + s * (-1)) ≤ a
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> nlinarith

theorem transport_zero_near_initial_forward
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : ℝ × ℝ) ∈ Ω)
    (f : ι → ℝ × ℝ → ℝ) (v : (ℝ × ℝ) → ι → ℝ) (b : (ℝ × ℝ) → ι → ι → ℝ)
    (hf : ∀ i p, p ∈ Ω → DifferentiableAt ℝ (f i) p)
    (hv : ContinuousOn v Ω) (hb : ContinuousOn b Ω)
    (hzero : ∀ p ∈ Ω, p.2 = 0 → ∀ i, f i p = 0)
    (hpde : ∀ p ∈ Ω, ∀ i,
      fderiv ℝ (f i) p (v p i, -1) = -(∑ j, b p i j * f j p)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p, ‖p‖ < δ → 0 ≤ p.2 → ∀ i, f i p = 0 := by
  let C : ℝ := ‖v 0‖ + ‖b 0‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have he : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ), p ∈ Ω ∧ ‖v p‖ + ‖b p‖ < C := by
    have ht := ((hv.continuousAt (hΩ.mem_nhds h0)).norm.add
      (hb.continuousAt (hΩ.mem_nhds h0)).norm).tendsto
    have hh := ht.eventually (gt_mem_nhds (show ‖v 0‖ + ‖b 0‖ < C by dsimp [C]; linarith))
    filter_upwards [hΩ.mem_nhds h0, hh] with p hp hn
    exact ⟨hp, hn⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp he
  let a := ε / 2
  have ha : 0 < a := by dsimp [a]; positivity
  let K := transportTrapezoid a a C
  have hKball (p : ℝ × ℝ) (hp : p ∈ K) : p ∈ Metric.ball 0 ε := by
    rcases hp with ⟨ht, ht', hx, hx'⟩
    have hxn : |p.1| ≤ a := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    have htn : |p.2| ≤ a := by rw [abs_of_nonneg ht]; exact ht'
    have hn : ‖p‖ ≤ a := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le hxn htn
    have hlt : a < ε := by dsimp [a]; linarith
    simpa only [Metric.mem_ball, dist_zero_right] using hn.trans_lt hlt
  have hKU : K ⊆ Ω := fun p hp => (hball (hKball p hp)).1
  have hvB (p : ℝ × ℝ) (hp : p ∈ K) (i : ι) : |v p i| ≤ C := by
    have hh := (hball (hKball p hp)).2
    have hn := norm_le_pi_norm (v p) i
    change |v p i| ≤ ‖v p‖ at hn
    linarith [norm_nonneg (b p)]
  have hbB (p : ℝ × ℝ) (hp : p ∈ K) (i j : ι) : |b p i j| ≤ C := by
    have hh := (hball (hKball p hp)).2
    have hn := (norm_le_pi_norm (b p i) j).trans (norm_le_pi_norm (b p) i)
    change |b p i j| ≤ ‖b p‖ at hn
    linarith [norm_nonneg (v p)]
  have hz := transport_zero_of_compact (transportTrapezoid_compact a a C hC.le) f v b
    (fun i p hp => hf i p (hKU hp)) (fun _ hp => hp.1)
    (fun p hp => hzero p (hKU hp)) (fun p hp => hpde p (hKU hp))
    (fun p hp ht i => transportTrapezoid_backward_tangent a a C hp ht (hvB p hp i)) C hC.le hbB
  let δ := a / (2 * (C + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδa : δ < a := by
    dsimp [δ]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (C + 1))).mpr
    nlinarith
  have hδC : (C + 1) * δ < a := by
    have heq : (C + 1) * δ = a / 2 := by dsimp [δ]; field_simp
    rw [heq]; linarith
  refine ⟨δ, hδ, fun p hp ht i => hz p ?_ i⟩
  have hxp : |p.1| < δ := (norm_fst_le p).trans_lt hp
  have htp : |p.2| < δ := (norm_snd_le p).trans_lt hp
  have hxt := abs_lt.mp hxp
  have htt := abs_lt.mp htp
  change 0 ≤ p.2 ∧ p.2 ≤ a ∧ p.1 + C * p.2 ≤ a ∧ -p.1 + C * p.2 ≤ a
  exact ⟨ht, by linarith, by nlinarith, by nlinarith⟩

noncomputable def timeReflection : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-(ContinuousLinearMap.snd ℝ ℝ ℝ))

@[simp] theorem timeReflection_apply (p : ℝ × ℝ) : timeReflection p = (p.1, -p.2) := rfl

@[simp] theorem timeReflection_involutive (p : ℝ × ℝ) : timeReflection (timeReflection p) = p := by
  ext <;> simp

@[simp] theorem timeReflection_norm (p : ℝ × ℝ) : ‖timeReflection p‖ = ‖p‖ := by
  simp only [timeReflection_apply, Prod.norm_def, norm_neg]

/-- Zero initial values force a solution of a homogeneous linear diagonal
transport system to vanish on an actual two-sided neighbourhood. -/
theorem transport_zero_near_initial
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : ℝ × ℝ) ∈ Ω)
    (f : ι → ℝ × ℝ → ℝ) (v : (ℝ × ℝ) → ι → ℝ) (b : (ℝ × ℝ) → ι → ι → ℝ)
    (hf : ∀ i p, p ∈ Ω → DifferentiableAt ℝ (f i) p)
    (hv : ContinuousOn v Ω) (hb : ContinuousOn b Ω)
    (hzero : ∀ p ∈ Ω, p.2 = 0 → ∀ i, f i p = 0)
    (hpde : ∀ p ∈ Ω, ∀ i,
      fderiv ℝ (f i) p (v p i, -1) = -(∑ j, b p i j * f j p)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p, ‖p‖ < δ → ∀ i, f i p = 0 := by
  obtain ⟨δ₁, hδ₁, hforward⟩ := transport_zero_near_initial_forward hΩ h0 f v b hf hv hb hzero hpde
  let Ω' := timeReflection ⁻¹' Ω
  let f' := fun i p => f i (timeReflection p)
  let v' := fun p => -v (timeReflection p)
  let b' := fun p => -b (timeReflection p)
  have hΩ' : IsOpen Ω' := hΩ.preimage timeReflection.continuous
  have h0' : (0 : ℝ × ℝ) ∈ Ω' := by simpa only [Ω', mem_preimage, map_zero] using h0
  have hdf (i : ι) (p : ℝ × ℝ) (hp : p ∈ Ω') :
      HasFDerivAt (f' i) ((fderiv ℝ (f i) (timeReflection p)).comp timeReflection) p :=
    (hf i (timeReflection p) hp).hasFDerivAt.comp p timeReflection.hasFDerivAt
  have hpde' (p : ℝ × ℝ) (hp : p ∈ Ω') (i : ι) :
      fderiv ℝ (f' i) p (v' p i, -1) = -(∑ j, b' p i j * f' j p) := by
    rw [(hdf i p hp).fderiv]
    have he : timeReflection (v' p i, -1) = -(v (timeReflection p) i, -1) := by
      ext <;> simp [v']
    rw [ContinuousLinearMap.comp_apply, he, map_neg, hpde (timeReflection p) hp i]
    simp only [b', f', Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
  obtain ⟨δ₂, hδ₂, hbackward⟩ := transport_zero_near_initial_forward hΩ' h0' f' v' b'
    (fun i p hp => (hdf i p hp).differentiableAt)
    ((hv.comp timeReflection.continuous.continuousOn (fun _ hp => hp)).neg)
    ((hb.comp timeReflection.continuous.continuousOn (fun _ hp => hp)).neg)
    (fun p hp ht => hzero (timeReflection p) hp (by change -p.2 = 0; rw [ht, neg_zero])) hpde'
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro p hp i
  by_cases ht : 0 ≤ p.2
  · exact hforward p (hp.trans_le (min_le_left _ _)) ht i
  · have hh := hbackward (timeReflection p)
      (by rw [timeReflection_norm]; exact hp.trans_le (min_le_right _ _))
      (by change 0 ≤ -p.2; linarith) i
    simpa only [f', timeReflection_involutive] using hh

/-- The same uniqueness statement at an arbitrary point of the initial line. -/
theorem transport_zero_near_point
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {q₀ : ℝ × ℝ} (h0 : q₀ ∈ Ω)
    (f : ι → ℝ × ℝ → ℝ) (v : (ℝ × ℝ) → ι → ℝ) (b : (ℝ × ℝ) → ι → ι → ℝ)
    (hf : ∀ i p, p ∈ Ω → DifferentiableAt ℝ (f i) p)
    (hv : ContinuousOn v Ω) (hb : ContinuousOn b Ω)
    (hzero : ∀ p ∈ Ω, p.2 = q₀.2 → ∀ i, f i p = 0)
    (hpde : ∀ p ∈ Ω, ∀ i,
      fderiv ℝ (f i) p (v p i, -1) = -(∑ j, b p i j * f j p)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p, ‖p - q₀‖ < δ → ∀ i, f i p = 0 := by
  let τ : (ℝ × ℝ) → (ℝ × ℝ) := fun p => q₀ + p
  have hτ : ContDiff ℝ ∞ τ := contDiff_const.add contDiff_id
  have hΩ' : IsOpen (τ ⁻¹' Ω) := hΩ.preimage hτ.continuous
  have hd (i : ι) (p : ℝ × ℝ) (hp : τ p ∈ Ω) :
      fderiv ℝ (fun z => f i (τ z)) p = fderiv ℝ (f i) (τ p) := by
    exact ((hf i (τ p) hp).hasFDerivAt.comp p ((hasFDerivAt_id p).const_add q₀)).fderiv
  obtain ⟨δ, hδ, hh⟩ := transport_zero_near_initial hΩ' (by simpa [τ] using h0)
    (fun i p => f i (τ p)) (fun p => v (τ p)) (fun p => b (τ p))
    (fun i p hp => (hf i (τ p) hp).comp p (hτ.differentiable (by simp) p))
    (hv.comp hτ.continuous.continuousOn (fun _ hp => hp))
    (hb.comp hτ.continuous.continuousOn (fun _ hp => hp))
    (fun p hp ht => hzero (τ p) hp (by change q₀.2 + p.2 = q₀.2; rw [ht, add_zero]))
    (fun p hp i => by rw [hd i p hp]; exact hpde (τ p) hp i)
  refine ⟨δ, hδ, fun p hp i => ?_⟩
  simpa only [τ, add_sub_cancel] using hh (p - q₀) hp i

/-- A convenient form for systems written as sums of component differences. -/
theorem transport_difference_zero_near_point
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {q₀ : ℝ × ℝ} (h0 : q₀ ∈ Ω)
    (f : ι → ℝ × ℝ → ℝ) (v : (ℝ × ℝ) → ι → ℝ) (c : (ℝ × ℝ) → ι → ι → ℝ)
    (hf : ∀ i p, p ∈ Ω → DifferentiableAt ℝ (f i) p)
    (hv : ContinuousOn v Ω) (hc : ContinuousOn c Ω)
    (hzero : ∀ p ∈ Ω, p.2 = q₀.2 → ∀ i, f i p = 0)
    (hpde : ∀ p ∈ Ω, ∀ i,
      fderiv ℝ (f i) p (v p i, -1) = -(∑ j, c p i j * (f j p - f i p))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p, ‖p - q₀‖ < δ → ∀ i, f i p = 0 := by
  let b := fun p i j => c p i j - if j = i then ∑ k, c p i k else 0
  have hb : ContinuousOn b Ω := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    apply ((continuousOn_pi.mp (continuousOn_pi.mp hc i)) j).sub
    by_cases hji : j = i
    · simp only [hji, ↓reduceIte]
      exact continuousOn_finset_sum _ (fun k _ => continuousOn_pi.mp (continuousOn_pi.mp hc i) k)
    · simpa only [hji, ↓reduceIte] using (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ)) Ω)
  apply transport_zero_near_point hΩ h0 f v b hf hv hb hzero
  intro p hp i
  rw [hpde p hp i]
  congr 1
  simp [b, sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, ite_mul]

end SemiHamiltonian.Analysis
