module

public import SemiHamiltonian.Geometry.ConservationCriterion
public import SemiHamiltonian.Analysis.DensityClassification

/-! Realization of conservation-law first and second jets by actual Darboux
solutions. Finite families allow the neighbourhood to be fixed before the jets. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Smooth

open PSS.FrameData

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U V : Set (ι → ℝ)}

theorem linearForm_eq_of_single {L K : (ι → ℝ) →L[ℝ] ℝ}
    (h : ∀ i, L (Pi.single i 1) = K (Pi.single i 1)) : L = K := by
  apply ContinuousLinearMap.ext
  intro z
  have hz : z = ∑ i, z i • Pi.single i (1 : ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hz, map_sum, map_sum]
  simp only [map_smul, h]

theorem bilinearForm_eq_of_single {B C : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ}
    (h : ∀ i j, B (Pi.single i 1) (Pi.single j 1) = C (Pi.single i 1) (Pi.single j 1)) : B = C := by
  apply ContinuousLinearMap.ext
  intro z
  apply linearForm_eq_of_single
  intro j
  exact congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ => L z)
    (linearForm_eq_of_single (L := B.flip (Pi.single j 1)) (K := C.flip (Pi.single j 1))
      (fun i => h i j))

theorem coordinate_second (hU : IsOpen U) (h : Functions U) (p : U) (i j : ι) :
    (coordinateDerivations hU).deriv j ((coordinateDerivations hU).deriv i h) p =
      fderiv ℝ (fderiv ℝ (extend U h)) p (Pi.single j 1) (Pi.single i 1) := by
  change directional hU (Pi.single j 1) (directional hU (Pi.single i 1) h) p = _
  rw [show directional hU (Pi.single i 1) h = ofContDiffOn _ _ from rfl, directional_ofContDiffOn]
  have hd := ((smooth U h).contDiffAt (hU.mem_nhds p.property)).fderiv_right (m := ∞) (by simp)
  rw [fderiv_clm_apply (hd.differentiableAt (by simp)) (differentiableAt_const _)]
  simp

theorem diagonal_conservationLaw_iff (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (S : System hU) (h q : Functions V) :
    (restrictSystem hU hV hVU S).IsConservationLaw h q ↔
      IsMatrixConservationLaw (Endomorphism.matrix (diagonalMap S.speed)) h q := by
  constructor
  · intro hh p
    apply linearForm_eq_of_single
    intro i
    have he := congrArg (fun f : Functions V => f p) (hh i)
    change fderiv ℝ (extend V q) p (Pi.single i 1) =
      Smooth.restrict hVU (S.speed i) p * fderiv ℝ (extend V h) p (Pi.single i 1) at he
    rw [Smooth.restrict_apply] at he
    rw [ContinuousLinearMap.comp_apply]
    have hd : Endomorphism.matrix (diagonalMap S.speed) p (Pi.single i 1) =
        S.speed i ⟨p, hVU p.property⟩ • Pi.single i 1 := by
      ext j
      rw [diagonalMap_matrix_apply S.speed ⟨p, hVU p.property⟩]
      by_cases hij : i = j <;> simp [Pi.single_apply, hij, eq_comm]
    rw [hd, map_smul, smul_eq_mul]
    exact he
  · intro hh i
    apply Subtype.ext
    funext p
    have he := congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) (hh p)
    change fderiv ℝ (extend V q) p (Pi.single i 1) = _ at he
    have hd : Endomorphism.matrix (diagonalMap S.speed) p (Pi.single i 1) =
        S.speed i ⟨p, hVU p.property⟩ • Pi.single i 1 := by
      ext j
      rw [diagonalMap_matrix_apply S.speed ⟨p, hVU p.property⟩]
      by_cases hij : i = j <;> simp [Pi.single_apply, hij, eq_comm]
    rw [ContinuousLinearMap.comp_apply, hd, map_smul, smul_eq_mul] at he
    change fderiv ℝ (extend V q) p (Pi.single i 1) =
      Smooth.restrict hVU (S.speed i) p * fderiv ℝ (extend V h) p (Pi.single i 1)
    rw [Smooth.restrict_apply]
    exact he

/-- Arbitrary values and own-axis derivatives of the density gradient are
realized by a density with an actual flux on one open neighbourhood. -/
theorem exists_conservation_gradientJet (hU : IsOpen U) (S : System hU)
    (hS : S.IsSemiHamiltonian) (p : U) (a b : ι → ℝ) :
    ∃ V, ∃ hV : IsOpen V, ∃ hVU : V ⊆ U, ∃ hpV : (p : ι → ℝ) ∈ V,
      ∃ h q : Functions V,
        IsMatrixConservationLaw (Endomorphism.matrix (diagonalMap S.speed)) h q ∧
        (∀ i, (coordinateDerivations hV).deriv i h ⟨p, hpV⟩ = a i) ∧
        (∀ i, (coordinateDerivations hV).deriv i ((coordinateDerivations hV).deriv i h) ⟨p, hpV⟩ = b i) ∧
        (restrictSystem hU hV hVU S).IsDensity h := by
  obtain ⟨r, hr, hBU, hsol⟩ := locallyDensityAxisSolvable_of_semiHamiltonian hU S hS p
  let B := Metric.ball (p : ι → ℝ) (r : ℝ)
  have hpB : (p : ι → ℝ) ∈ B := Metric.mem_ball_self hr
  let φ : ι → C(ℝ, ℝ) := fun i => ⟨fun s => a i + b i * s, by fun_prop⟩
  obtain ⟨w, hw, haxis⟩ := hsol φ (fun i => show ContDiff ℝ ∞ (fun s => a i + b i * s) from by fun_prop)
  let SB := restrictSystem hU Metric.isOpen_ball hBU S
  obtain ⟨T, hT, hTB, hpT, f, _, hdf⟩ := exists_local_primitive Metric.isOpen_ball w
    (SB.densityGradient_closed hw) ⟨p, hpB⟩ 0
  have hfd : (restrictSystem hU hT (hTB.trans hBU) S).IsDensity f := by
    rw [← restrictSystem_trans hU Metric.isOpen_ball hT hBU hTB S]
    exact primitive_is_density Metric.isOpen_ball hT hTB SB hw hdf
  obtain ⟨V, hV, hVT, hpV, q, _, hq⟩ := exists_local_flux hT _ f hfd ⟨p, hpT⟩ 0
  let h := Smooth.restrict hVT f
  let hVU := hVT.trans (hTB.trans hBU)
  have hh : (restrictSystem hU hV hVU S).IsDensity h := by
    rw [← restrictSystem_trans hU hT hV (hTB.trans hBU) hVT S]
    exact density_restrict hT hV hVT _ hfd
  have hd (i : ι) : (coordinateDerivations hV).deriv i h = Smooth.restrict (hVT.trans hTB) (w i) := by
    change derivation hV (Pi.single i 1) (Smooth.restrict hVT f) = _
    rw [← restrict_derivation hT hV]
    change Smooth.restrict hVT ((coordinateDerivations hT).deriv i f) = _
    rw [hdf i, restrict_trans]
  have hw0 (i : ι) : w i ⟨p, hpB⟩ = a i := by
    have he := haxis i 0 ⟨p, hpB⟩ (by simp)
    simpa [φ] using he
  have hw1 (i : ι) : (coordinateDerivations Metric.isOpen_ball).deriv i (w i) ⟨p, hpB⟩ = b i := by
    let ℓ : ℝ → (ι → ℝ) := fun s => (p : ι → ℝ) + s • Pi.single i 1
    have hℓ : HasDerivAt ℓ (Pi.single i 1) 0 := by
      exact (((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ))).const_add (p : ι → ℝ)).congr_deriv (one_smul ℝ _)
    have hℓ0 : ℓ 0 = p := by simp [ℓ]
    have hw' : HasFDerivAt (extend B (w i)) (fderiv ℝ (extend B (w i)) p) (ℓ 0) := by
      rw [hℓ0]
      exact hasFDerivAt_extend Metric.isOpen_ball (w i) ⟨p, hpB⟩
    have hde : HasDerivAt (fun s => extend B (w i) (ℓ s))
        (fderiv ℝ (extend B (w i)) p (Pi.single i 1)) 0 :=
      hw'.comp_hasDerivAt 0 hℓ
    have he : (fun s => extend B (w i) (ℓ s)) =ᶠ[𝓝 0] (fun s => a i + b i * s) := by
      filter_upwards [hℓ.continuousAt.eventually (Metric.isOpen_ball.mem_nhds (hℓ0.symm ▸ hpB))] with s hs
      rw [extend_apply B (w i) ⟨ℓ s, hs⟩]
      apply haxis i s ⟨ℓ s, hs⟩
      dsimp only [ℓ]
      congr 1
      ext j
      by_cases hj : j = i <;> simp [Pi.single_apply, hj]
    have hb' : HasDerivAt (fun s => a i + b i * s) (b i) 0 :=
      (((hasDerivAt_id (0 : ℝ)).const_mul (b i)).const_add (a i)).congr_deriv (mul_one _)
    exact hde.unique (hb'.congr_of_eventuallyEq he)
  refine ⟨V, hV, hVU, hpV, h, q, ?_, ?_, ?_, hh⟩
  · apply (diagonal_conservationLaw_iff hU hV hVU S h q).mp
    rw [← restrictSystem_trans hU hT hV (hTB.trans hBU) hVT S]
    exact hq
  · intro i
    rw [hd i, Smooth.restrict_apply]
    exact hw0 i
  · intro i
    rw [hd i]
    change derivation hV (Pi.single i 1) (Smooth.restrict (hVT.trans hTB) (w i)) ⟨p, hpV⟩ = _
    rw [← restrict_derivation Metric.isOpen_ball hV, Smooth.restrict_apply]
    exact hw1 i

theorem section_sum_smul_apply {κ : Type} [Fintype κ]
    (a : κ → ℝ) (f : κ → Functions U) (p : U) :
    (∑ k, a k • f k : Functions U) p = ∑ k, a k * f k p := by
  exact map_sum (eval p) (fun k => a k • f k) Finset.univ

theorem conservationLaw_sum_smul (hU : IsOpen U) (S : System hU)
    {κ : Type} [Fintype κ] (a : κ → ℝ) (f q : κ → Functions U)
    (hf : ∀ k, S.IsConservationLaw (f k) (q k)) :
    S.IsConservationLaw (∑ k, a k • f k) (∑ k, a k • q k) := by
  intro i
  simp only [map_sum, Derivation.map_smul, Finset.mul_sum, mul_smul_comm]
  exact Finset.sum_congr rfl (fun k _ => congrArg (fun z => a k • z) (hf k i))

end SemiHamiltonian.Smooth

namespace SemiHamiltonian.Geometry

open Smooth PSS.FrameData

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}

/-- Sufficiency on one common neighbourhood: a finite family of linear and
quadratic initial data realizes every required first and second jet. -/
theorem locallyRichConservationLaws_of_semiHamiltonian (hU : IsOpen U) (S : System hU)
    (hS : S.IsSemiHamiltonian) :
    LocallyRichConservationLaws (Endomorphism.matrix (diagonalMap S.speed)) U := by
  intro p hp
  let pp : U := ⟨p, hp⟩
  let a : (Bool × ι) → ι → ℝ := fun k i => if k.1 then 0 else if i = k.2 then 1 else 0
  let b : (Bool × ι) → ι → ℝ := fun k i => if k.1 then (if i = k.2 then 1 else 0) else 0
  choose V hV hVU hpV f q hq ha hb hd using
    fun k : Bool × ι => exists_conservation_gradientJet hU S hS pp (a k) (b k)
  let T := U ∩ ⋂ k, V k
  have hT : IsOpen T := hU.inter (isOpen_iInter_of_finite hV)
  have hTU : T ⊆ U := inter_subset_left
  have hTV (k : Bool × ι) : T ⊆ V k := fun _ hx => mem_iInter.mp hx.2 k
  have hpT : p ∈ T := ⟨hp, mem_iInter.mpr hpV⟩
  let pt : T := ⟨p, hpT⟩
  let ST := restrictSystem hU hT hTU S
  let F := fun k => Smooth.restrict (hTV k) (f k)
  let Q := fun k => Smooth.restrict (hTV k) (q k)
  let D := (coordinateDerivations hT).deriv
  have hF (k : Bool × ι) : ST.IsConservationLaw (F k) (Q k) :=
    (diagonal_conservationLaw_iff hU hT hTU S _ _).mpr ((hq k).restrict hT (hTV k))
  have hF0 (k : Bool × ι) (i : ι) : D i (F k) pt = a k i := by
    change derivation hT (Pi.single i 1) (Smooth.restrict (hTV k) (f k)) pt = _
    rw [← restrict_derivation (hV k) hT, Smooth.restrict_apply]
    exact ha k i
  have hF1 (k : Bool × ι) (i : ι) : D i (D i (F k)) pt = b k i := by
    change derivation hT (Pi.single i 1) (derivation hT (Pi.single i 1)
      (Smooth.restrict (hTV k) (f k))) pt = _
    rw [← restrict_derivation (hV k) hT, ← restrict_derivation (hV k) hT, Smooth.restrict_apply]
    exact hb k i
  have hF2 (k i j : ι) : D j (D i (F (true, k))) pt = if i = k ∧ j = k then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      simpa only [b, Bool.true_eq, ↓reduceIte, and_self] using hF1 (true, k) i
    · have hh := congrArg (fun z : Functions T => z pt) (ST.conservationLaw_density (hF (true, k)) i j hij)
      change D j (D i (F (true, k))) pt =
        ST.coeff i j pt * D i (F (true, k)) pt + ST.coeff j i pt * D j (F (true, k)) pt at hh
      rw [hF0, hF0] at hh
      have hn : ¬ (i = k ∧ j = k) := fun h => hij (h.1.trans h.2.symm)
      simpa [a, hn] using hh
  refine ⟨T, hT, hTU, hpT, ?_, ?_⟩
  · intro L
    let c := fun k => L (Pi.single k 1)
    refine ⟨∑ k, c k • F (false, k), ∑ k, c k • Q (false, k),
      (diagonal_conservationLaw_iff hU hT hTU S _ _).mp
        (conservationLaw_sum_smul hT ST c _ _ (fun k => hF (false, k))), ?_⟩
    apply linearForm_eq_of_single
    intro i
    change D i (∑ k, c k • F (false, k)) pt = _
    rw [map_sum]
    simp only [Derivation.map_smul, section_sum_smul_apply, hF0, a, Bool.false_eq, ↓reduceIte]
    simp [c]
  · intro B hsym hcompat
    have hB (i j : ι) (hij : i ≠ j) : B (Pi.single i 1) (Pi.single j 1) = 0 := by
      have hh := hcompat (Pi.single i 1) (Pi.single j 1)
      have hm (k : ι) : Endomorphism.matrix (diagonalMap S.speed) p (Pi.single k 1) =
          S.speed k pp • Pi.single k 1 := by
        ext l
        rw [diagonalMap_matrix_apply S.speed pp]
        by_cases hkl : k = l <;> simp [Pi.single_apply, hkl, eq_comm]
      rw [hm i, hm j, map_smul, smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at hh
      have hgap : S.speed j pp - S.speed i pp ≠ 0 := (S.gap_unit i j hij).map (eval pp) |>.ne_zero
      apply (mul_eq_zero.mp (show (S.speed j pp - S.speed i pp) * B (Pi.single i 1) (Pi.single j 1) = 0 by
        linear_combination -hh)).resolve_left hgap
    let c := fun k => B (Pi.single k 1) (Pi.single k 1)
    let H : Functions T := ∑ k, c k • F (true, k)
    refine ⟨H, ∑ k, c k • Q (true, k),
      (diagonal_conservationLaw_iff hU hT hTU S _ _).mp
        (conservationLaw_sum_smul hT ST c _ _ (fun k => hF (true, k))), ?_, ?_⟩
    · apply linearForm_eq_of_single
      intro i
      change D i H pt = 0
      simp only [H, map_sum, Derivation.map_smul, section_sum_smul_apply, hF0, a, Bool.true_eq, ↓reduceIte, mul_zero, Finset.sum_const_zero]
    · apply bilinearForm_eq_of_single
      intro i j
      rw [← coordinate_second hT H pt j i]
      change D i (D j H) pt = _
      simp only [H, map_sum, Derivation.map_smul, section_sum_smul_apply, hF2]
      by_cases hij : i = j
      · subst j
        simp [c]
      · rw [hB i j hij]
        apply Finset.sum_eq_zero
        intro k _
        have hh : ¬ (j = k ∧ i = k) := fun h => hij (h.2.trans h.1.symm)
        simp [hh]

end SemiHamiltonian.Geometry
