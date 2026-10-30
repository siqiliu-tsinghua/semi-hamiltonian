module

public import SemiHamiltonian.Geometry.FrameEvaluation
public import SemiHamiltonian.Geometry.CoframeCoordinates

/-! Passage from involutivity of smooth sections to the differential Frobenius condition. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Filter Set

namespace SemiHamiltonian.Smooth.Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}

theorem dual_frobenius_of_involutive (hU : IsOpen U) (b : Frame U) (r : ι)
    (hc : b.Involutive hU {r}ᶜ) : Geometry.FrobeniusOneForm (b.dual r) U := by
  intro q hq v w hv hw
  let x : U := ⟨q, hq⟩
  have hsections (z : ι → ℝ) (hz : b.dual r q z = 0) :
      ∃ X : Fields U, field X q = z ∧ b.equivFun X r = 0 := by
    let Z : Fields U := fun k => algebraMap ℝ (Functions U) (z k)
    let X := Z - (b.equivFun Z r) • b r
    have hZ : field Z q = z := by
      ext k
      change field Z x k = z k
      simp [Z, field_apply, Algebra.algebraMap_eq_smul_one]
    have hzero : b.equivFun Z r x = 0 := by
      rw [← b.dual_field r Z x]
      exact hZ ▸ hz
    refine ⟨X, ?_, ?_⟩
    · ext k
      change field X x k = z k
      rw [field_apply]
      change (Z k - b.equivFun Z r * b r k) x = z k
      change Z k x - b.equivFun Z r x * b r k x = z k
      rw [hzero, zero_mul, sub_zero]
      simpa only [← field_apply Z x k] using congrFun hZ k
    · simp [X, b.equivFun_self]
  obtain ⟨X, hX, hXr⟩ := hsections v hv
  obtain ⟨Y, hY, hYr⟩ := hsections w hw
  have hmem (Z : Fields U) (hZ : b.equivFun Z r = 0) : b.InDistribution {r}ᶜ Z := by
    intro k hk
    have hkr : k = r := by simpa using hk
    simpa only [hkr] using hZ
  have hbr : b.equivFun (fieldBracket hU X Y) r = 0 :=
    hc X Y (hmem X hXr) (hmem Y hYr) r (by simp)
  have hbracket : b.dual r q (_root_.VectorField.lieBracket ℝ (field X) (field Y) q) = 0 := by
    change b.dual r x (_root_.VectorField.lieBracket ℝ (field X) (field Y) x) = 0
    rw [← fieldBracket_eval hU X Y x, b.dual_field, hbr]
    rfl
  have hz (Z : Fields U) (hZ : b.equivFun Z r = 0) (a : ι → ℝ) :
      fderiv ℝ (b.dual r) q a (field Z q) +
        b.dual r q (fderiv ℝ (field Z) q a) = 0 := by
    have hdα := (((b.dual_smooth r).contDiffAt (hU.mem_nhds hq)).differentiableAt
      (by simp)).hasFDerivAt
    have hdZ := (((field_smooth Z).contDiffAt (hU.mem_nhds hq)).differentiableAt
      (by simp)).hasFDerivAt
    have he : (fun y => b.dual r y (field Z y)) =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [hU.mem_nhds hq] with y hy
      rw [b.dual_field r Z ⟨y, hy⟩, hZ]
      rfl
    have hh := (hdα.clm_apply hdZ).unique
      ((hasFDerivAt_const (0 : ℝ) q).congr_of_eventuallyEq he)
    have hh' := congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ => L a) hh
    simpa [add_comm] using hh'
  have hxy := hz Y hYr v
  have hyx := hz X hXr w
  rw [hX] at hyx
  rw [hY] at hxy
  simp only [_root_.VectorField.lieBracket, map_sub, hX, hY] at hbracket
  linarith

theorem dual_invertible (b : Frame U) (x : U) :
    (ContinuousLinearMap.pi (fun i => b.dual i x)).IsInvertible := by
  apply Geometry.isInvertible_of_injective
  apply (ContinuousLinearMap.pi (fun i => b.dual i x)).ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  exact b.dual_separates x v (fun i => congrFun hv i)

end SemiHamiltonian.Smooth.Frame
