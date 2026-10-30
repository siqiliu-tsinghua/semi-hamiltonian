module

public import SemiHamiltonian.Geometry.LocalPotential
public import SemiHamiltonian.Analysis.SmoothSystem
public import SemiHamiltonian.Conservation

/-! Smooth coordinate one-forms and their actual local primitives. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set Filter

set_option backward.isDefEq.respectTransparency.types false

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}

noncomputable def oneForm (a : ι → Functions U) (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, extend U (a i) x • ContinuousLinearMap.proj i

theorem oneForm_single (a : ι → Functions U) (x : ι → ℝ) (i : ι) :
    oneForm a x (Pi.single i 1) = extend U (a i) x := by
  simp [oneForm, smul_apply, Pi.single_apply]

omit [DecidableEq ι] in
theorem oneForm_smooth (a : ι → Functions U) : ContDiffOn ℝ ∞ (oneForm a) U :=
  ContDiffOn.sum fun i _ => (smooth U (a i)).smul contDiffOn_const

theorem oneForm_fderiv_single (hU : IsOpen U) (a : ι → Functions U) (x : U) (v : ι → ℝ) (i : ι) :
    fderiv ℝ (oneForm a) x v (Pi.single i 1) = fderiv ℝ (extend U (a i)) x v := by
  have hd := (((oneForm_smooth a).contDiffAt (hU.mem_nhds x.property)).differentiableAt
    (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single i 1) (x : ι → ℝ))
  have he : (fun y => oneForm a y (Pi.single i 1)) = extend U (a i) := funext fun y => oneForm_single a y i
  rw [he] at hd
  have hh := congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ => L v) hd.fderiv
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, zero_add, add_zero,
    ContinuousLinearMap.flip_apply] using hh.symm

theorem oneForm_closed (hU : IsOpen U) (a : ι → Functions U)
    (ha : (coordinateDerivations hU).IsClosed a) (x : U) (v w : ι → ℝ) :
    fderiv ℝ (oneForm a) x v w = fderiv ℝ (oneForm a) x w v := by
  have hb (i j : ι) : fderiv ℝ (oneForm a) x (Pi.single j 1) (Pi.single i 1) =
      fderiv ℝ (oneForm a) x (Pi.single i 1) (Pi.single j 1) := by
    rw [oneForm_fderiv_single hU, oneForm_fderiv_single hU]
    exact congrArg (fun f : Functions U => f x) (ha i j)
  have hsum (z : ι → ℝ) : z = ∑ i, z i • Pi.single i (1 : ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hsum v, hsum w]
  simp only [map_sum, map_smul, sum_apply,
    smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hb]
  ring

theorem exists_local_primitive (hU : IsOpen U) (a : ι → Functions U)
    (ha : (coordinateDerivations hU).IsClosed a) (p : U) (c : ℝ) :
    ∃ V, ∃ hV : IsOpen V, ∃ hVU : V ⊆ U, ∃ hpV : (p : ι → ℝ) ∈ V,
      ∃ f : Functions V, f ⟨p, hpV⟩ = c ∧
        ∀ i, (coordinateDerivations hV).deriv i f = Smooth.restrict hVU (a i) := by
  obtain ⟨V, f, hV, hpV, hVU, hf, hfp, hd⟩ := Geometry.exists_local_potential hU
    (oneForm_smooth a) (fun x hx => oneForm_closed hU a ha ⟨x, hx⟩) p.property c
  refine ⟨V, hV, hVU, hpV, ofContDiffOn f hf, hfp, ?_⟩
  intro i
  apply Subtype.ext
  funext x
  change directional hV (Pi.single i 1) (ofContDiffOn f hf) x = _
  rw [directional_ofContDiffOn, hd x x.property, oneForm_single]
  rw [Smooth.restrict_apply]
  exact extend_apply U (a i) ⟨x, hVU x.property⟩

end SemiHamiltonian.Smooth
