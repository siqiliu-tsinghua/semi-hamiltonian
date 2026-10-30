module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

/-! Compact coordinate cubes and the radial paths from their coordinate axes. -/

@[expose] public section

open scoped NNReal

namespace SemiHamiltonian.Darboux

abbrev Cube (ι : Type*) (r : ℝ≥0) := ι → Set.Icc (-(r : ℝ)) r

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

instance : Inhabited (Cube ι r) :=
  ⟨fun _ => ⟨0, neg_nonpos.mpr r.coe_nonneg, r.coe_nonneg⟩⟩

def point (x : Cube ι r) : ι → ℝ := fun i => x i

omit [Fintype ι] [DecidableEq ι] in
theorem abs_coordinate_le (x : Cube ι r) (i : ι) : |(x i : ℝ)| ≤ r :=
  abs_le.mpr (x i).property

noncomputable def radial (i : ι) (t : ℝ) (x : Cube ι r) : Cube ι r := fun j =>
  if j = i then x j else
    ⟨(Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) * x j, by
      have ht := (Set.projIcc (0 : ℝ) 1 zero_le_one t).property
      have hx := (x j).property
      apply abs_le.mp
      rw [abs_mul, abs_of_nonneg ht.1]
      calc
        _ ≤ 1 * (r : ℝ) := mul_le_mul ht.2 (abs_le.mpr hx) (abs_nonneg _) zero_le_one
        _ = _ := one_mul _⟩

omit [Fintype ι] in
theorem continuous_radial (i : ι) :
    Continuous (fun z : ℝ × Cube ι r => radial r i z.1 z.2) := by
  apply continuous_pi
  intro j
  by_cases h : j = i
  · simp only [radial, h, ite_true]
    fun_prop
  · simp only [radial, h, ite_false]
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp continuous_projIcc).comp continuous_fst).mul
      (continuous_subtype_val.comp ((continuous_apply j).comp continuous_snd))

omit [Fintype ι] in
theorem radial_apply_of_mem (i j : ι) (x : Cube ι r) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (radial r i t x j : ℝ) = if j = i then (x j : ℝ) else t * x j := by
  by_cases h : j = i <;> simp [radial, h, Set.projIcc_of_mem zero_le_one ht]

@[simp] theorem radial_one (i : ι) (x : Cube ι r) : radial r i 1 x = x := by
  funext j
  apply Subtype.ext
  rw [radial_apply_of_mem r i j x 1 (by constructor <;> norm_num)]
  split_ifs <;> simp

/-- The point on the i-th axis with the same i-th coordinate as x. -/
noncomputable def axis (i : ι) (x : Cube ι r) : Cube ι r := radial r i 0 x

omit [Fintype ι] in
@[simp] theorem axis_coordinate (i : ι) (x : Cube ι r) : (axis r i x i : ℝ) = x i := by
  simp [axis, radial]

theorem axis_other (i j : ι) (hji : j ≠ i) (x : Cube ι r) :
    (axis r i x j : ℝ) = 0 := by
  rw [axis, radial_apply_of_mem r i j x 0 (by constructor <;> norm_num)]
  simp [hji]

end SemiHamiltonian.Darboux
