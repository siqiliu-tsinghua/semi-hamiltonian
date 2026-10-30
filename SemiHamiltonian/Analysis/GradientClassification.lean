module

public import SemiHamiltonian.Analysis.ConservationLocal
public import SemiHamiltonian.Analysis.SymmetryClassification
public import SemiHamiltonian.Darboux.PairUniqueness
public import SemiHamiltonian.Geometry.VectorFields

/-! A genuine classification of local smooth density gradients by their axis
germs. Equality of solution germs allows the neighbourhood to be shrunk. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}
  (hU : IsOpen U) (S : System hU) (p : U)

def IsLocalDensityGradient (W : (ι → ℝ) → (ι → ℝ)) : Prop :=
  ∃ V, IsOpen V ∧ V ⊆ U ∧ (p : ι → ℝ) ∈ V ∧ ContDiffOn ℝ ∞ W V ∧
    ∀ x ∈ V, ∀ i j, i ≠ j →
      fderiv ℝ (fun y => W y i) x (Pi.single j 1) =
        (extend U (S.coeff i j) x * W x i + extend U (S.coeff j i) x * W x j)

def DensityGradientGerm :=
  {g : Filter.Germ (𝓝 (p : ι → ℝ)) (ι → ℝ) //
    ∃ W : (ι → ℝ) → (ι → ℝ), IsLocalDensityGradient hU S p W ∧
      (W : Filter.Germ (𝓝 (p : ι → ℝ)) (ι → ℝ)) = g}

theorem localDensityGradient_of_section {V : Set (ι → ℝ)} (hV : IsOpen V) (hVU : V ⊆ U)
    (hpV : (p : ι → ℝ) ∈ V) (w : ι → Functions V)
    (hw : (restrictSystem hU hV hVU S).IsDensityGradient w) :
    IsLocalDensityGradient hU S p (field w) := by
  refine ⟨V, hV, hVU, hpV, field_smooth w, ?_⟩
  intro x hx i j hij
  have hh := congrArg (fun f : Functions V => f ⟨x, hx⟩) (hw i j hij)
  change fderiv ℝ (extend V (w i)) x (Pi.single j 1) =
    (Smooth.restrict hVU (S.coeff i j) ⟨x, hx⟩ * w i ⟨x, hx⟩ +
      Smooth.restrict hVU (S.coeff j i) ⟨x, hx⟩ * w j ⟨x, hx⟩) at hh
  rw [Smooth.restrict_apply, Smooth.restrict_apply] at hh
  simpa only [field, extend_apply U (S.coeff i j) ⟨x, hVU hx⟩, extend_apply U (S.coeff j i) ⟨x, hVU hx⟩,
    extend_apply V (w j) ⟨x, hx⟩, extend_apply V (w i) ⟨x, hx⟩] using hh

theorem localDensityGradient_unique {W Z : (ι → ℝ) → (ι → ℝ)}
    (hW : IsLocalDensityGradient hU S p W) (hZ : IsLocalDensityGradient hU S p Z)
    (ha : ∀ i, (fun s => W ((p : ι → ℝ) + Pi.single i s) i) =ᶠ[𝓝 0]
      (fun s => Z ((p : ι → ℝ) + Pi.single i s) i)) : W =ᶠ[𝓝 (p : ι → ℝ)] Z := by
  obtain ⟨V, hV, hVU, hpV, hWV, hPW⟩ := hW
  obtain ⟨T, hT, hTU, hpT, hZT, hPZ⟩ := hZ
  exact Darboux.Pair.germ_unique (hV.inter hT) ⟨hpV, hpT⟩ (fun i j => extend U (S.coeff i j))
    (fun i j => extend U (S.coeff j i))
    (fun i j => (smooth U (S.coeff i j)).continuousOn.mono (inter_subset_left.trans hVU))
    (fun i j => (smooth U (S.coeff j i)).continuousOn.mono (inter_subset_left.trans hVU))
    W Z (hWV.mono inter_subset_left) (hZT.mono inter_subset_right)
    (fun x hx => hPW x hx.1) (fun x hx => hPZ x hx.2) ha

theorem localDensityGradient_section {W : (ι → ℝ) → (ι → ℝ)}
    (hW : IsLocalDensityGradient hU S p W) :
    ∃ V, ∃ hV : IsOpen V, ∃ hVU : V ⊆ U, (p : ι → ℝ) ∈ V ∧
      ∃ w : ι → Functions V, (restrictSystem hU hV hVU S).IsDensityGradient w ∧
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

noncomputable def densityGradientAxisGerms (g : DensityGradientGerm hU S p) : ι → ScalarGerm 0 :=
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

theorem densityGradientAxisGerms_injective : Function.Injective (densityGradientAxisGerms hU S p) := by
  intro g k heq
  apply Subtype.ext
  obtain ⟨W, hW, hWg⟩ := g.property
  obtain ⟨Z, hZ, hZk⟩ := k.property
  rw [← hWg, ← hZk]
  apply Filter.EventuallyEq.germ_eq
  apply localDensityGradient_unique hU S p hW hZ
  intro i
  have hh := congrArg (fun a : ι → ScalarGerm 0 => (a i).val) heq
  change axisGerm p i g.val = axisGerm p i k.val at hh
  rw [← hWg, ← hZk, axisGerm_coe, axisGerm_coe] at hh
  exact Filter.Germ.coe_eq.mp hh

theorem densityGradientAxisGerms_surjective (hS : S.IsSemiHamiltonian) :
    Function.Surjective (densityGradientAxisGerms hU S p) := by
  intro a
  choose f hf hfa using fun i => (a i).property
  let φ : ι → C(ℝ, ℝ) := fun i => ⟨f i, (hf i).continuous⟩
  obtain ⟨r, hr, hsub, hsol⟩ := (locallyDensityAxisSolvable_of_semiHamiltonian hU S hS) p
  obtain ⟨w, hw, haxis⟩ := hsol φ hf
  have hp : (p : ι → ℝ) ∈ Metric.ball (p : ι → ℝ) r := Metric.mem_ball_self hr
  let g : DensityGradientGerm hU S p := ⟨(field w : Filter.Germ (𝓝 (p : ι → ℝ)) (ι → ℝ)),
    field w, localDensityGradient_of_section hU S p Metric.isOpen_ball hsub hp w hw, rfl⟩
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

/-- All local smooth density gradients, with no repetitions, are parameterized
by n arbitrary smooth scalar germs. -/
noncomputable def densityGradientGermEquiv (hS : S.IsSemiHamiltonian) :
    DensityGradientGerm hU S p ≃ (ι → ScalarGerm 0) :=
  Equiv.ofBijective (densityGradientAxisGerms hU S p)
    ⟨densityGradientAxisGerms_injective hU S p, densityGradientAxisGerms_surjective hU S p hS⟩

end SemiHamiltonian.Smooth
