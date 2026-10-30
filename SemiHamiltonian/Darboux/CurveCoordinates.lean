module

public import SemiHamiltonian.Darboux.CurveOpen
public import SemiHamiltonian.Geometry.CoordinateFrame

/-! Separate changes of Riemann coordinates straighten a noncharacteristic
initial curve. Compatibility is verified by the actual chain rule. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Darboux

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def coordinateProduct (κ : ι → ℝ → ℝ) (x : ι → ℝ) : ι → ℝ := fun i => κ i (x i)

theorem coordinateProduct_contDiff (κ : ι → ℝ → ℝ) (hκ : ∀ i, ContDiff ℝ ∞ (κ i)) :
    ContDiff ℝ ∞ (coordinateProduct κ) :=
  contDiff_pi.mpr (fun i => (hκ i).comp (contDiff_apply ℝ (fun _ : ι => ℝ) i))

theorem coordinateProduct_fderiv (κ : ι → ℝ → ℝ) (hκ : ∀ i, ContDiff ℝ ∞ (κ i))
    (x z : ι → ℝ) (i : ι) :
    fderiv ℝ (coordinateProduct κ) x z i = deriv (κ i) (x i) * z i := by
  have hd (j : ι) : HasFDerivAt (fun y : ι → ℝ => κ j (y j))
      (deriv (κ j) (x j) • ContinuousLinearMap.proj j) x :=
    ((hκ j).differentiable (by simp) (x j)).hasDerivAt.comp_hasFDerivAt x
      (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt
  unfold coordinateProduct
  rw [(hasFDerivAt_pi.mpr hd).fderiv]
  rfl

theorem coordinateProduct_fderiv_single (κ : ι → ℝ → ℝ) (hκ : ∀ i, ContDiff ℝ ∞ (κ i))
    (x : ι → ℝ) (j : ι) :
    fderiv ℝ (coordinateProduct κ) x (Pi.single j 1) = deriv (κ j) (x j) • Pi.single j 1 := by
  ext i
  rw [coordinateProduct_fderiv κ hκ]
  by_cases hij : i = j <;> simp [Pi.single_apply, hij]

noncomputable def curveCoefficients (κ : ι → ℝ → ℝ) (γ : ι → ι → (ι → ℝ) → ℝ)
    (i j : ι) (x : ι → ℝ) : ℝ := deriv (κ j) (x j) * γ i j (coordinateProduct κ x)

theorem curveCoefficients_contDiff (κ : ι → ℝ → ℝ) (hκ : ∀ i, ContDiff ℝ ∞ (κ i))
    {U : Set (ι → ℝ)} (γ : ι → ι → (ι → ℝ) → ℝ)
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (γ i j) U) (i j : ι) :
    ContDiffOn ℝ ∞ (curveCoefficients κ γ i j) (coordinateProduct κ ⁻¹' U) :=
  (((hκ j).deriv' (n := ∞)).comp (contDiff_apply ℝ (fun _ : ι => ℝ) j)).contDiffOn.mul
    ((hγ i j).comp (coordinateProduct_contDiff κ hκ).contDiffOn (fun _ hp => hp))

theorem curveCoefficients_compatible (κ : ι → ℝ → ℝ) (hκ : ∀ i, ContDiff ℝ ∞ (κ i))
    {U : Set (ι → ℝ)} (hU : IsOpen U) (γ : ι → ι → (ι → ℝ) → ℝ)
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (γ i j) U)
    (hc : ∀ x ∈ U, ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      fderiv ℝ (γ i j) x (Pi.single k 1) =
        γ i j x * γ j k x + γ i k x * γ k j x - γ i j x * γ i k x) :
    ∀ x ∈ coordinateProduct κ ⁻¹' U, ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      fderiv ℝ (curveCoefficients κ γ i j) x (Pi.single k 1) =
        curveCoefficients κ γ i j x * curveCoefficients κ γ j k x +
        curveCoefficients κ γ i k x * curveCoefficients κ γ k j x -
        curveCoefficients κ γ i j x * curveCoefficients κ γ i k x := by
  intro x hx i j k hij hik hjk
  have hβ := (((hκ j).deriv' (n := ∞)).differentiable (by simp) (x j)).hasDerivAt.comp_hasFDerivAt x
    (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt
  have hγ' := ((hγ i j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hcomp := hγ'.hasFDerivAt.comp x ((coordinateProduct_contDiff κ hκ).differentiable (by simp) x).hasFDerivAt
  have hd := (hβ.mul hcomp).fderiv
  change fderiv ℝ (fun y => deriv (κ j) (y j) * γ i j (coordinateProduct κ y)) x = _ at hd
  change fderiv ℝ (fun y => deriv (κ j) (y j) * γ i j (coordinateProduct κ y)) x _ = _
  rw [hd]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    coordinateProduct_fderiv_single κ hκ, map_smul, smul_eq_mul,
    ContinuousLinearMap.proj_apply, Pi.single_eq_of_ne hjk, mul_zero, add_zero]
  rw [hc (coordinateProduct κ x) hx i j k hij hik hjk]
  dsimp only [curveCoefficients, Function.comp_def, ContinuousLinearMap.proj_apply]
  ring

/-- Nonvanishing derivatives of the curve components are exactly what is
needed to straighten it by separate local changes of coordinates. -/
theorem exists_curve_chart (κ : ι → ℝ → ℝ) (hκ : ∀ i, ContDiff ℝ ∞ (κ i))
    {U : Set (ι → ℝ)} (hU : IsOpen U) (hp : coordinateProduct κ 0 ∈ U)
    (hreg : ∀ i, deriv (κ i) 0 ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ),
      (e : (ι → ℝ) → (ι → ℝ)) = coordinateProduct κ ∧ (0 : ι → ℝ) ∈ e.source ∧
      e.source ⊆ coordinateProduct κ ⁻¹' U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  apply Geometry.exists_smooth_local_inverse (hU.preimage (coordinateProduct_contDiff κ hκ).continuous)
    (coordinateProduct_contDiff κ hκ).contDiffOn hp
  apply Geometry.isInvertible_of_injective
  intro x y hxy
  funext i
  have hh := congrFun hxy i
  rw [coordinateProduct_fderiv κ hκ, coordinateProduct_fderiv κ hκ] at hh
  exact mul_left_cancel₀ (hreg i) hh

theorem local_smooth_solution_on_curve
    {U : Set (ι → ℝ)} (hU : IsOpen U)
    (γ : ι → ι → (ι → ℝ) → ℝ) (hγ : ∀ i j, ContDiffOn ℝ ∞ (γ i j) U)
    (hc : ∀ x ∈ U, ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      fderiv ℝ (γ i j) x (Pi.single k 1) =
        γ i j x * γ j k x + γ i k x * γ k j x - γ i j x * γ i k x)
    (κ : ι → ℝ → ℝ) (hκ : ∀ i, ContDiff ℝ ∞ (κ i))
    (hp : coordinateProduct κ 0 ∈ U) (hreg : ∀ i, deriv (κ i) 0 ≠ 0)
    (φ : ι → C(ℝ, ℝ)) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    ∃ V, IsOpen V ∧ V ⊆ U ∧ coordinateProduct κ 0 ∈ V ∧
      ∃ w : (ι → ℝ) → (ι → ℝ), ContDiffOn ℝ ∞ w V ∧
        (∀ x ∈ V, ∀ i j, i ≠ j →
          fderiv ℝ (fun y => w y i) x (Pi.single j 1) = γ i j x * (w x j - w x i)) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ s, |s| < ε →
          (fun i => κ i s) ∈ V ∧ ∀ i, w (fun i => κ i s) i = φ i s := by
  obtain ⟨e, heq, he0, heU, he, hi⟩ := exists_curve_chart κ hκ hU hp hreg
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp e.open_source 0 he0
  let R : ℝ≥0 := ⟨η / 2, by positivity⟩
  have hR : 0 < R := by change 0 < η / 2; positivity
  have hRη : (R : ℝ) < η := by change η / 2 < η; linarith
  have hbox : ∀ x : Cube ι R, point R x ∈ e.source := by
    intro x
    apply hball
    simpa only [Metric.mem_ball, dist_zero_right] using (norm_point_le R x).trans_lt hRη
  let δ := curveCoefficients κ γ
  obtain ⟨r, hr, hrR, hsol⟩ := local_smooth_solution_diagonalCurve R hR
    e.open_source hbox δ (fun i j => (curveCoefficients_contDiff κ hκ γ hγ i j).mono heU)
    (fun x hx => curveCoefficients_compatible κ hκ hU γ hγ hc x (heU hx))
  obtain ⟨f, hf, hpde, htrace⟩ := hsol φ hφ
  have hsub : Metric.ball (0 : ι → ℝ) (r : ℝ) ⊆ e.source :=
    (Metric.ball_subset_ball ((show (r : ℝ) ≤ R from hrR).trans hRη.le)).trans hball
  let V := e.target ∩ e.symm ⁻¹' Metric.ball (0 : ι → ℝ) (r : ℝ)
  have hV : IsOpen V := hi.continuousOn.isOpen_inter_preimage e.open_target Metric.isOpen_ball
  have hVU : V ⊆ U := by
    intro x hx
    have hh := heU (e.map_target hx.1)
    change coordinateProduct κ (e.symm x) ∈ U at hh
    rw [← heq, e.right_inv hx.1] at hh
    exact hh
  have hpV : coordinateProduct κ 0 ∈ V := by
    rw [← heq]
    exact ⟨e.map_source he0, by simp only [mem_preimage]; rw [e.left_inv he0]; exact Metric.mem_ball_self hr⟩
  let w := fun x => f (e.symm x)
  have hw : ContDiffOn ℝ ∞ w V := hf.comp (hi.mono inter_subset_left) (fun _ hx => hx.2)
  refine ⟨V, hV, hVU, hpV, w, hw, ?_, (r : ℝ), hr, ?_⟩
  · intro x hx i j hij
    let y := e.symm x
    have hy : y ∈ Metric.ball (0 : ι → ℝ) (r : ℝ) := hx.2
    have hye : y ∈ e.source := e.map_target hx.1
    have hxy : coordinateProduct κ y = x := by rw [← heq]; exact e.right_inv hx.1
    have hβ : deriv (κ j) (y j) ≠ 0 := by
      intro hz
      have hh : fderiv ℝ e y (Pi.single j 1) = 0 := by
        rw [heq, coordinateProduct_fderiv_single κ hκ, hz, zero_smul]
      have hh' := Geometry.chart_fderiv_injective e he hi hye (hh.trans (map_zero _).symm)
      have hh'' := congrFun hh' j
      simpa using hh''
    have hinv : fderiv ℝ e.symm x (deriv (κ j) (y j) • Pi.single j 1) = Pi.single j 1 := by
      have hh := congrArg (fun L : (ι → ℝ) →L[ℝ] (ι → ℝ) => L (Pi.single j 1))
        (Geometry.chart_fderiv_left_inverse e he hi hye)
      change fderiv ℝ e.symm (e y) (fderiv ℝ e y (Pi.single j 1)) = Pi.single j 1 at hh
      rw [heq, coordinateProduct_fderiv_single κ hκ, hxy] at hh
      exact hh
    have hd := (((contDiffOn_pi.mp hf) i).contDiffAt (Metric.isOpen_ball.mem_nhds hy)).differentiableAt (by simp)
    have hdi := (hi.contDiffAt (e.open_target.mem_nhds hx.1)).differentiableAt (by simp)
    have hchain := (hd.hasFDerivAt.comp x hdi.hasFDerivAt).fderiv
    have hh := congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ => L (deriv (κ j) (y j) • Pi.single j 1)) hchain
    change fderiv ℝ (fun x => w x i) x (deriv (κ j) (y j) • Pi.single j 1) =
      fderiv ℝ (fun z => f z i) y (fderiv ℝ e.symm x (deriv (κ j) (y j) • Pi.single j 1)) at hh
    rw [map_smul, smul_eq_mul, hinv, hpde y hy i j hij] at hh
    change deriv (κ j) (y j) * _ = deriv (κ j) (y j) * γ i j (coordinateProduct κ y) * _ at hh
    rw [hxy] at hh
    apply mul_left_cancel₀ hβ
    simpa only [mul_assoc] using hh
  · intro s hs
    have hy : (fun _ : ι => s) ∈ Metric.ball (0 : ι → ℝ) (r : ℝ) := by
      rw [Metric.mem_ball, dist_zero_right]
      exact (uniformScale_norm_le (ι := ι) s).trans_lt hs
    have hys := hsub hy
    have heys : e (fun _ => s) = fun i => κ i s := by rw [heq]; rfl
    have hval : e.symm (fun i => κ i s) = fun _ => s := by rw [← heys]; exact e.left_inv hys
    refine ⟨⟨by rw [← heys]; exact e.map_source hys, by simp only [mem_preimage]; rw [hval]; exact hy⟩, ?_⟩
    intro i
    change f (e.symm (fun i => κ i s)) i = _
    rw [hval]
    exact htrace i s hs

end SemiHamiltonian.Darboux
