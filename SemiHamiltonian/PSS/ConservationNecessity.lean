module

public import SemiHamiltonian.PSS.Eigenframe
public import Mathlib.Basic.Real.Basic

/-! The differentiated conservation-law obstruction in a noncoordinate
eigenframe. This is the pure second-jet specialization of PSS (2.21). -/

@[expose] public section

open scoped Classical

namespace SemiHamiltonian.PSS.FrameData

variable {𝕜 R ι : Type*} [CommRing 𝕜] [CommRing R] [Algebra 𝕜 R]
  [Fintype ι] [DecidableEq ι] (F : FrameData 𝕜 R ι)

/-- Unlike arbitrary frame-calculus data, actual vector fields satisfy this
identity on every scalar function. -/
def HasScalarCommutator : Prop :=
  ∀ i j f, F.deriv i (F.deriv j f) - F.deriv j (F.deriv i f) =
    ∑ a, F.structureCoeff a i j * F.deriv a f

/-- A conservation law with zero first jet and a single nonzero diagonal
second jet rules out the corresponding transverse bracket component. -/
theorem structureCoeff_eq_zero_of_conservation_jet
    (hc : F.HasScalarCommutator) (v : ι → R) (f q : R)
    (hq : ∀ a, F.deriv a q = v a * F.deriv a f)
    (ev : R →+* ℝ) (k : ι)
    (hzero : ∀ a, ev (F.deriv a f) = 0)
    (hjet : ∀ a b, ev (F.deriv a (F.deriv b f)) =
      if a = k ∧ b = k then 1 else 0)
    (i j : ι) (hik : i ≠ k) (hjk : j ≠ k)
    (hgap : ev (v k) ≠ ev (v j)) (hgap' : ev (v k) ≠ ev (v i)) :
    ev (F.structureCoeff k i j) = 0 := by
  have hthird (a b : ι) (hak : a ≠ k) (hbk : b ≠ k)
      (hvb : ev (v k) ≠ ev (v b)) :
      ev (F.deriv a (F.deriv b (F.deriv k f))) = 0 := by
    have hf := congrArg (fun z => ev (F.deriv a z)) (hc b k f)
    simp only [map_sub, map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
      hzero, hjet, hak, false_and, ite_false, mul_zero, zero_mul, zero_add,
      Finset.sum_const_zero] at hf
    have hg := hc b k q
    simp only [hq] at hg
    have hg' := congrArg (fun z => ev (F.deriv a z)) hg
    simp only [map_sub, map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
      hzero, hjet, hak, hbk, false_and, and_false, ite_false, mul_zero,
      zero_mul, add_zero, zero_add, Finset.sum_const_zero] at hg'
    have he : ev (F.deriv a (F.deriv b (F.deriv k f))) =
        ev (F.deriv a (F.deriv k (F.deriv b f))) := sub_eq_zero.mp hf
    rw [← he] at hg'
    exact (mul_eq_zero.mp (show (ev (v k) - ev (v b)) *
      ev (F.deriv a (F.deriv b (F.deriv k f))) = 0 by
        linear_combination hg')).resolve_left (sub_ne_zero.mpr hvb)
  have hh := congrArg ev (hc i j (F.deriv k f))
  simp only [map_sub, map_sum, map_mul, hjet, and_true] at hh
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at hh
  rw [hthird i j hik hjk hgap, hthird j i hjk hik hgap', sub_self] at hh
  exact hh.symm

end SemiHamiltonian.PSS.FrameData
