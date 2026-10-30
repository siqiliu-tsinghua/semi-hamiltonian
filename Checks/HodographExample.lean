module

import SemiHamiltonian

/-! The scalar Burgers system u_t = u u_x, with w(u)=u and base point (0,0,0).
Its hodograph equation is u=x+t*u, whose regular branch is x/(1-t). -/

open scoped Topology ContDiff Classical
open Set SemiHamiltonian SemiHamiltonian.Smooth

namespace HodographCheck

abbrev E := Fin 1 → ℝ
abbrev U : Set E := univ

noncomputable def v (i : Fin 1) : Functions U :=
  ofContDiffOn (fun x => x i) (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) i).contDiffOn

theorem separated : StrictlyHyperbolic v := by
  intro x i j hij
  exact False.elim (hij (Subsingleton.elim i j))

noncomputable def S : System (ι := Fin 1) (U := U) isOpen_univ := ofSpeeds isOpen_univ v separated
def p : U := ⟨0, mem_univ _⟩

theorem value (i : Fin 1) (r : E) : extend U (S.speed i) r = r i := by
  simp [S, ofSpeeds, DiagonalSystem.ofSpeeds, v, ofContDiffOn, extend]

theorem relation : HodographRelation isOpen_univ S S.speed (0, 0) p := by
  intro i
  simp [value, p]

theorem nonsingular :
    ((fderiv ℝ (hodographResidual isOpen_univ S S.speed) ((0, 0), (0 : E))).comp
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ) E)).IsInvertible := by
  let F := hodographResidual isOpen_univ S S.speed
  have hF := (hodographResidual_smooth isOpen_univ S S.speed).contDiffAt
    ((isOpen_univ.prod isOpen_univ).mem_nhds (show ((0, 0), (0 : E)) ∈ univ ×ˢ U from ⟨mem_univ _, mem_univ _⟩))
  have hd : HasFDerivAt (fun r : E => F ((0, 0), r))
      ((fderiv ℝ F ((0, 0), (0 : E))).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) E)) 0 := by
    convert (hF.differentiableAt (by simp)).hasFDerivAt.comp (0 : E)
      ((hasFDerivAt_const ((0, 0) : ℝ × ℝ) (0 : E)).prodMk (hasFDerivAt_id (0 : E))) using 1 <;> rfl
  have he : (fun r : E => F ((0, 0), r)) = id := by
    funext r i
    simp [F, hodographResidual, value]
  rw [he] at hd
  rw [hd.unique (hasFDerivAt_id (0 : E))]
  exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩

example : ∃ (Ω : Set (ℝ × ℝ)) (u : (ℝ × ℝ) → E), IsOpen Ω ∧ (0, 0) ∈ Ω ∧
    u (0, 0) = 0 ∧ ContDiffOn ℝ ∞ u Ω ∧
    ∀ q ∈ Ω, ∀ i, fderiv ℝ u q (0, 1) i = u q i * fderiv ℝ u q (1, 0) i ∧
      fderiv ℝ u q (1, 0) i ≠ 0 := by
  obtain ⟨Ω, B, u, hΩ, h0, hB, hpB, hBU, hu0, hu, hgraph, hpde, huniq⟩ :=
    generalized_hodograph isOpen_univ S S.speed S.speed_isCommutingSpeed (0, 0) p relation nonsingular
  exact ⟨Ω, u, hΩ, h0, hu0, hu, by simpa only [value] using hpde⟩

end HodographCheck
