module

public import SemiHamiltonian.Analysis.TsarevLocal
public import SemiHamiltonian.Analysis.LocalExtension
public import SemiHamiltonian.Darboux.CurveCoordinates

/-! Actual smooth commuting speeds with prescribed values on a curve whose
components all have nonzero derivative. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set Filter

set_option backward.isDefEq.respectTransparency.types false

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {U : Set (ι → ℝ)} (hU : IsOpen U) (S : System hU)

theorem coeff_compatible (hS : S.IsSemiHamiltonian) :
    ∀ x ∈ U, ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      fderiv ℝ (extend U (S.coeff i j)) x (Pi.single k 1) =
        extend U (S.coeff i j) x * extend U (S.coeff j k) x +
        extend U (S.coeff i k) x * extend U (S.coeff k j) x -
        extend U (S.coeff i j) x * extend U (S.coeff i k) x := by
  intro x hx i j k hij hik hjk
  have hz := congrArg (eval (⟨x, hx⟩ : U)) (S.darbouxResidual_eq_zero hS i j k hij hik hjk)
  simp only [DiagonalSystem.darbouxResidual, map_sub, map_add, map_mul, map_zero] at hz
  change fderiv ℝ (extend U (S.coeff i j)) x (Pi.single k 1) -
    S.coeff i j ⟨x, hx⟩ * S.coeff j k ⟨x, hx⟩ -
    S.coeff i k ⟨x, hx⟩ * S.coeff k j ⟨x, hx⟩ +
    S.coeff i j ⟨x, hx⟩ * S.coeff i k ⟨x, hx⟩ = 0 at hz
  simp only [extend, hx, ↓reduceDIte]
  linear_combination hz

theorem commutingSpeed_on_global_curve (hS : S.IsSemiHamiltonian)
    (κ : ι → ℝ → ℝ) (hκ : ∀ i, ContDiff ℝ ∞ (κ i))
    (hp : (fun i => κ i 0) ∈ U) (hreg : ∀ i, deriv (κ i) 0 ≠ 0)
    (φ : ι → C(ℝ, ℝ)) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    ∃ (V : Set (ι → ℝ)) (hV : IsOpen V) (hVU : V ⊆ U),
      (fun i => κ i 0) ∈ V ∧ ∃ w : ι → Functions V,
        (restrictSystem hU hV hVU S).IsCommutingSpeed w ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ s, |s| < ε →
          ∃ hs : (fun i => κ i s) ∈ V, ∀ i, w i ⟨_, hs⟩ = φ i s := by
  obtain ⟨V, hV, hVU, hpV, f, hf, hpde, ε, hε, htrace⟩ :=
    Darboux.local_smooth_solution_on_curve hU (fun i j => extend U (S.coeff i j))
      (fun i j => smooth U (S.coeff i j)) (coeff_compatible hU S hS) κ hκ hp hreg φ hφ
  let w : ι → Functions V := fun i => ofContDiffOn (fun x => f x i) (contDiffOn_pi.mp hf i)
  refine ⟨V, hV, hVU, hpV, w, ?_, ε, hε, ?_⟩
  · intro i j hij
    apply Subtype.ext
    funext x
    change directional hV (Pi.single j 1) (w i) x =
      restrict hVU (S.coeff i j) x * (w j x - w i x)
    rw [show w i = ofContDiffOn (fun x => f x i) (contDiffOn_pi.mp hf i) from rfl,
      directional_ofContDiffOn, restrict_apply, hpde x x.property i j hij]
    rw [show extend U (S.coeff i j) x = S.coeff i j ⟨x, hVU x.property⟩ from
      extend_apply U (S.coeff i j) ⟨x, hVU x.property⟩]
    rfl
  · intro s hs
    obtain ⟨hsV, hh⟩ := htrace s hs
    exact ⟨hsV, hh⟩

/-- Locally smooth data suffice; global extensions are used only as auxiliary
representatives of the same germs. -/
theorem commutingSpeed_on_curve (hS : S.IsSemiHamiltonian)
    {I : Set ℝ} (hI : IsOpen I) (h0 : (0 : ℝ) ∈ I)
    (κ : ℝ → (ι → ℝ)) (hκ : ContDiffOn ℝ ∞ κ I)
    (hp : κ 0 ∈ U) (hreg : ∀ i, deriv (fun s => κ s i) 0 ≠ 0)
    (φ : ι → ℝ → ℝ) (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) I) :
    ∃ (V : Set (ι → ℝ)) (hV : IsOpen V) (hVU : V ⊆ U),
      κ 0 ∈ V ∧ ∃ w : ι → Functions V,
        (restrictSystem hU hV hVU S).IsCommutingSpeed w ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ s, |s| < ε →
          ∃ hs : κ s ∈ V, ∀ i, w i ⟨κ s, hs⟩ = φ i s := by
  choose k hk hke using fun i => exists_global_smooth_germ hI h0 (contDiffOn_pi.mp hκ i)
  choose a ha hae using fun i => exists_global_smooth_germ hI h0 (hφ i)
  have hk0 : (fun i => k i 0) = κ 0 := funext (fun i => (hke i).eq_of_nhds)
  have hkreg (i : ι) : deriv (k i) 0 ≠ 0 := by rw [(hke i).deriv_eq]; exact hreg i
  obtain ⟨V, hV, hVU, hpV, w, hw, ε, hε, htrace⟩ :=
    commutingSpeed_on_global_curve hU S hS k hk (hk0 ▸ hp) hkreg
      (fun i => ⟨a i, (ha i).continuous⟩) ha
  have he : ∀ᶠ s in 𝓝 (0 : ℝ), (∀ i, k i s = κ s i) ∧ (∀ i, a i s = φ i s) :=
    (Filter.eventually_all.mpr hke).and (Filter.eventually_all.mpr hae)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨V, hV, hVU, hk0 ▸ hpV, w, hw, min ε δ, lt_min hε hδ, ?_⟩
  intro s hs
  have hh := hδsub (show s ∈ Metric.ball 0 δ by simpa [Real.dist_eq] using hs.trans_le (min_le_right ε δ))
  obtain ⟨hsV, hval⟩ := htrace s (hs.trans_le (min_le_left ε δ))
  have hks : (fun i => k i s) = κ s := funext hh.1
  refine ⟨hks ▸ hsV, ?_⟩
  intro i
  have hhval : w i ⟨_, hsV⟩ = a i s := hval i
  simpa only [hks, hh.2 i] using hhval

end SemiHamiltonian.Smooth
