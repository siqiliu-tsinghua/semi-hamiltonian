module

import SemiHamiltonian

/-! A nonlinear, two-component actual PDE solution. Nondegeneracy is checked
only at the origin; the converse must produce the commuting speed itself. -/

open scoped Topology ContDiff Classical
open Set SemiHamiltonian SemiHamiltonian.Smooth

set_option backward.isDefEq.respectTransparency.types false

namespace HodographConverseCheck

abbrev E := Fin 2 → ℝ
abbrev U : Set E := univ

def c (i : Fin 2) : ℝ := i.val + 1

noncomputable def v (i : Fin 2) : Functions U := ofContDiffOn (fun _ => c i) contDiffOn_const

theorem separated : StrictlyHyperbolic v := by
  intro x i j hij he
  change (i.val : ℝ) + 1 = (j.val : ℝ) + 1 at he
  have hh : i.val = j.val := by exact_mod_cast (add_right_cancel he)
  exact hij (Fin.ext hh)

noncomputable def S : System (ι := Fin 2) (U := U) isOpen_univ := ofSpeeds isOpen_univ v separated

theorem semi : S.IsSemiHamiltonian := by
  intro i j k hij hik hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

def u (q : ℝ × ℝ) (i : Fin 2) : ℝ := (q.1 + c i * q.2) ^ 2 + (q.1 + c i * q.2)

theorem smooth : ContDiff ℝ ∞ u := by unfold u; fun_prop

theorem derivative (q d : ℝ × ℝ) (i : Fin 2) :
    fderiv ℝ u q d i = (2 * (q.1 + c i * q.2) + 1) * (d.1 + c i * d.2) := by
  let L (j : Fin 2) : (ℝ × ℝ) →L[ℝ] ℝ :=
    (2 * (q.1 + c j * q.2) + 1) •
      (ContinuousLinearMap.fst ℝ ℝ ℝ + c j • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hd (j : Fin 2) : HasFDerivAt (fun q => u q j) (L j) q := by
    have ha := (hasFDerivAt_fst (𝕜 := ℝ) (p := q)).add
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := q)).const_mul (c j))
    apply ((ha.pow 2).add ha).congr_fderiv
    apply ContinuousLinearMap.ext
    intro z
    simp only [L, add_apply, smul_apply, smul_eq_mul, nsmul_eq_mul]
    change (2 * (q.1 + c j * q.2) ^ (2 - 1)) * (z.1 + c j * z.2) +
      (z.1 + c j * z.2) = (2 * (q.1 + c j * q.2) + 1) * (z.1 + c j * z.2)
    norm_num
    ring
  have hh := (hasFDerivAt_pi.mpr hd).fderiv
  change fderiv ℝ u q = _ at hh
  rw [hh]
  rfl

theorem speed_value (x : E) (i : Fin 2) : extend U (S.speed i) x = c i := by
  exact extend_apply U (S.speed i) ⟨x, mem_univ _⟩

theorem pde (q : ℝ × ℝ) (i : Fin 2) :
    fderiv ℝ u q (0, 1) i = extend U (S.speed i) (u q) * fderiv ℝ u q (1, 0) i := by
  rw [derivative, derivative, speed_value]
  ring

theorem nondegenerate (i : Fin 2) : fderiv ℝ u 0 (1, 0) i ≠ 0 := by
  rw [derivative]
  norm_num

example : ∃ (V : Set E) (hV : IsOpen V) (hVU : V ⊆ U), u 0 ∈ V ∧
    ∃ w : Fin 2 → Functions V, (restrictSystem isOpen_univ hV hVU S).IsCommutingSpeed w ∧
      ∃ W : Set (ℝ × ℝ), IsOpen W ∧ (0 : ℝ × ℝ) ∈ W ∧ W ⊆ univ ∧ MapsTo u W V ∧
        ∀ q ∈ W, HodographRelation hV (restrictSystem isOpen_univ hV hVU S) w q (u q) :=
  generalized_hodograph_converse isOpen_univ S semi isOpen_univ (mem_univ 0)
    smooth.contDiffOn (fun _ _ => mem_univ _) (fun q _ => pde q) nondegenerate

end HodographConverseCheck
