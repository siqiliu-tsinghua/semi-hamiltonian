module

public import SemiHamiltonian.Analysis.TsarevLocal
public import SemiHamiltonian.Analysis.LocalExtension
public import SemiHamiltonian.Darboux.LocalUniqueness
public import SemiHamiltonian.Geometry.VectorFields

/-! A genuine classification of local smooth commuting speeds by their axis
germs. Equality of solution germs allows the neighbourhood to be shrunk. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}
  (hU : IsOpen U) (S : System hU) (p : U)

def IsLocalCommutingSpeed (W : (ι → ℝ) → (ι → ℝ)) : Prop :=
  ∃ V, IsOpen V ∧ V ⊆ U ∧ (p : ι → ℝ) ∈ V ∧ ContDiffOn ℝ ∞ W V ∧
    ∀ x ∈ V, ∀ i j, i ≠ j →
      fderiv ℝ (fun y => W y i) x (Pi.single j 1) =
        extend U (S.coeff i j) x * (W x j - W x i)

def CommutingSpeedGerm :=
  {g : Filter.Germ (𝓝 (p : ι → ℝ)) (ι → ℝ) //
    ∃ W : (ι → ℝ) → (ι → ℝ), IsLocalCommutingSpeed hU S p W ∧
      (W : Filter.Germ (𝓝 (p : ι → ℝ)) (ι → ℝ)) = g}

theorem localCommutingSpeed_of_section {V : Set (ι → ℝ)} (hV : IsOpen V) (hVU : V ⊆ U)
    (hpV : (p : ι → ℝ) ∈ V) (w : ι → Functions V)
    (hw : (restrictSystem hU hV hVU S).IsCommutingSpeed w) :
    IsLocalCommutingSpeed hU S p (field w) := by
  refine ⟨V, hV, hVU, hpV, field_smooth w, ?_⟩
  intro x hx i j hij
  have hh := congrArg (fun f : Functions V => f ⟨x, hx⟩) (hw i j hij)
  change fderiv ℝ (extend V (w i)) x (Pi.single j 1) =
    Smooth.restrict hVU (S.coeff i j) ⟨x, hx⟩ * (w j ⟨x, hx⟩ - w i ⟨x, hx⟩) at hh
  rw [Smooth.restrict_apply] at hh
  simpa only [field, extend_apply U (S.coeff i j) ⟨x, hVU hx⟩,
    extend_apply V (w j) ⟨x, hx⟩, extend_apply V (w i) ⟨x, hx⟩] using hh

theorem localCommutingSpeed_unique {W Z : (ι → ℝ) → (ι → ℝ)}
    (hW : IsLocalCommutingSpeed hU S p W) (hZ : IsLocalCommutingSpeed hU S p Z)
    (ha : ∀ i, (fun s => W ((p : ι → ℝ) + Pi.single i s) i) =ᶠ[𝓝 0]
      (fun s => Z ((p : ι → ℝ) + Pi.single i s) i)) : W =ᶠ[𝓝 (p : ι → ℝ)] Z := by
  obtain ⟨V, hV, hVU, hpV, hWV, hPW⟩ := hW
  obtain ⟨T, hT, hTU, hpT, hZT, hPZ⟩ := hZ
  exact Darboux.germ_unique (hV.inter hT) ⟨hpV, hpT⟩ (fun i j => extend U (S.coeff i j))
    (fun i j => (smooth U (S.coeff i j)).continuousOn.mono (inter_subset_left.trans hVU))
    W Z (hWV.mono inter_subset_left) (hZT.mono inter_subset_right)
    (fun x hx => hPW x hx.1) (fun x hx => hPZ x hx.2) ha

theorem localCommutingSpeed_section {W : (ι → ℝ) → (ι → ℝ)}
    (hW : IsLocalCommutingSpeed hU S p W) :
    ∃ V, ∃ hV : IsOpen V, ∃ hVU : V ⊆ U, (p : ι → ℝ) ∈ V ∧
      ∃ w : ι → Functions V, (restrictSystem hU hV hVU S).IsCommutingSpeed w ∧
        ∀ x ∈ V, field w x = W x := by
  obtain ⟨V, hV, hVU, hpV, hWV, hPW⟩ := hW
  let w : ι → Functions V := fun i => ofContDiffOn (fun x => W x i) (contDiffOn_pi.mp hWV i)
  refine ⟨V, hV, hVU, hpV, w, ?_, ?_⟩
  · intro i j hij
    apply Subtype.ext
    funext x
    change directional hV (Pi.single j 1) (w i) x = _
    rw [directional_ofContDiffOn]
    exact hPW x x.property i j hij
  · intro x hx
    funext i
    rw [field_apply w ⟨x, hx⟩]
    rfl

/-- Any two local symmetries commute, even if either has repeated eigenvalues. -/
theorem localCommutingSpeeds_pairwise {W Z : (ι → ℝ) → (ι → ℝ)}
    (hW : IsLocalCommutingSpeed hU S p W) (hZ : IsLocalCommutingSpeed hU S p Z) :
    ∀ᶠ x in 𝓝 (p : ι → ℝ), ∀ i j,
      fderiv ℝ (fun y => Z y i) x (Pi.single j 1) * (W x j - W x i) -
        fderiv ℝ (fun y => W y i) x (Pi.single j 1) * (Z x j - Z x i) = 0 := by
  obtain ⟨V, hV, _, hpV, _, hPW⟩ := hW
  obtain ⟨T, hT, _, hpT, _, hPZ⟩ := hZ
  filter_upwards [hV.mem_nhds hpV, hT.mem_nhds hpT] with x hxV hxT
  intro i j
  by_cases hij : i = j
  · subst j; simp
  · rw [hPW x hxV i j hij, hPZ x hxT i j hij]
    ring

omit hU S in
theorem axisLine_smooth (i : ι) : ContDiff ℝ ∞ (fun s : ℝ => (p : ι → ℝ) + Pi.single i s) :=
  contDiff_const.add ((ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i).contDiff)

omit hU S in
noncomputable def axisGerm (i : ι) (g : Filter.Germ (𝓝 (p : ι → ℝ)) (ι → ℝ)) :
    Filter.Germ (𝓝 (0 : ℝ)) ℝ :=
  (g.compTendsto (fun s => (p : ι → ℝ) + Pi.single i s)
    (by simpa using (axisLine_smooth p i).continuous.continuousAt.tendsto (x := (0 : ℝ)))).map
      (fun z => z i)

omit hU S in
theorem axisGerm_coe (i : ι) (W : (ι → ℝ) → (ι → ℝ)) :
    axisGerm p i (W : Filter.Germ (𝓝 (p : ι → ℝ)) (ι → ℝ)) =
      ((fun s => W ((p : ι → ℝ) + Pi.single i s) i) : Filter.Germ (𝓝 (0 : ℝ)) ℝ) := rfl

noncomputable def commutingSpeedAxisGerms (g : CommutingSpeedGerm hU S p) : ι → ScalarGerm 0 :=
  fun i => ⟨axisGerm p i g.val, by
    obtain ⟨W, ⟨V, hV, hVU, hpV, hW, hP⟩, hWg⟩ := g.property
    rw [← hWg, axisGerm_coe]
    let L := fun s : ℝ => (p : ι → ℝ) + Pi.single i s
    have hVL : IsOpen (L ⁻¹' V) := hV.preimage (axisLine_smooth p i).continuous
    have h0 : (0 : ℝ) ∈ L ⁻¹' V := by simpa [L] using hpV
    have hWi : ContDiffOn ℝ ∞ (fun s => W (L s) i) (L ⁻¹' V) :=
      (contDiffOn_pi.mp hW i).comp (axisLine_smooth p i).contDiffOn (fun _ hx => hx)
    obtain ⟨f, hf, heq⟩ := exists_global_smooth_germ hVL h0 hWi
    exact ⟨f, hf, heq.germ_eq⟩⟩

theorem commutingSpeedAxisGerms_injective : Function.Injective (commutingSpeedAxisGerms hU S p) := by
  intro g k heq
  apply Subtype.ext
  obtain ⟨W, hW, hWg⟩ := g.property
  obtain ⟨Z, hZ, hZk⟩ := k.property
  rw [← hWg, ← hZk]
  apply Filter.EventuallyEq.germ_eq
  apply localCommutingSpeed_unique hU S p hW hZ
  intro i
  have hh := congrArg (fun a : ι → ScalarGerm 0 => (a i).val) heq
  change axisGerm p i g.val = axisGerm p i k.val at hh
  rw [← hWg, ← hZk, axisGerm_coe, axisGerm_coe] at hh
  exact Filter.Germ.coe_eq.mp hh

theorem commutingSpeedAxisGerms_surjective (hS : S.IsSemiHamiltonian) :
    Function.Surjective (commutingSpeedAxisGerms hU S p) := by
  intro a
  choose f hf hfa using fun i => (a i).property
  let φ : ι → C(ℝ, ℝ) := fun i => ⟨f i, (hf i).continuous⟩
  obtain ⟨r, hr, hsub, hsol⟩ := (locallyAxisSolvable_of_semiHamiltonian hU S hS) p
  obtain ⟨w, hw, haxis⟩ := hsol φ hf
  have hp : (p : ι → ℝ) ∈ Metric.ball (p : ι → ℝ) r := Metric.mem_ball_self hr
  let g : CommutingSpeedGerm hU S p := ⟨(field w : Filter.Germ (𝓝 (p : ι → ℝ)) (ι → ℝ)),
    field w, localCommutingSpeed_of_section hU S p Metric.isOpen_ball hsub hp w hw, rfl⟩
  refine ⟨g, ?_⟩
  funext i
  apply Subtype.ext
  change axisGerm p i (field w : Filter.Germ (𝓝 (p : ι → ℝ)) (ι → ℝ)) = (a i).val
  rw [axisGerm_coe, ← hfa i]
  apply Filter.EventuallyEq.germ_eq
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < r from hr)] with s hs
  have hq : (p : ι → ℝ) + Pi.single i s ∈ Metric.ball (p : ι → ℝ) r := by
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Pi.norm_single,
      sub_zero] using hs
  rw [field_apply w ⟨_, hq⟩]
  exact haxis i s ⟨_, hq⟩ rfl

/-- All local smooth commuting speeds, with no repetitions, are parameterized
by n arbitrary smooth scalar germs. -/
noncomputable def commutingSpeedGermEquiv (hS : S.IsSemiHamiltonian) :
    CommutingSpeedGerm hU S p ≃ (ι → ScalarGerm 0) :=
  Equiv.ofBijective (commutingSpeedAxisGerms hU S p)
    ⟨commutingSpeedAxisGerms_injective hU S p, commutingSpeedAxisGerms_surjective hU S p hS⟩

end SemiHamiltonian.Smooth
