module

public import SemiHamiltonian.Geometry.Superposition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.ProjIcc

/-! The bounded primitive operator on continuous paths over a fixed interval. -/

@[expose] public section

open scoped Topology ContDiff
open Filter Set MeasureTheory

namespace SemiHamiltonian.Geometry

abbrev Time := Icc (-2 : ℝ) 2

noncomputable def timeClamp : C(ℝ, Time) := ⟨projIcc (-2) 2 (by norm_num), continuous_projIcc⟩

def timeZero : Time := ⟨0, by norm_num⟩
def timeOne : Time := ⟨1, by norm_num⟩

@[simp] theorem timeClamp_zero : timeClamp 0 = timeZero := projIcc_of_mem (by norm_num) (by norm_num)
@[simp] theorem timeClamp_one : timeClamp 1 = timeOne := projIcc_of_mem (by norm_num) (by norm_num)

@[simp] theorem timeClamp_coe (s : Time) : timeClamp s = s := by
  exact projIcc_of_mem (by norm_num) s.property

@[simp] theorem timeClamp_val {s : ℝ} (hs : s ∈ Icc (-2 : ℝ) 2) : (timeClamp s : ℝ) = s := by
  exact congrArg Subtype.val (projIcc_of_mem (by norm_num) hs)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def primitive (z : C(Time, E)) : C(Time, E) :=
  ⟨fun s => ∫ t in (0 : ℝ)..(s : ℝ), z (timeClamp t),
    (intervalIntegral.continuous_primitive
      (fun a b => (z.continuous.comp timeClamp.continuous).intervalIntegrable a b) 0).comp
      continuous_subtype_val⟩

theorem primitive_norm_le (z : C(Time, E)) : ‖primitive z‖ ≤ 2 * ‖z‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro s
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := (s : ℝ)) (fun t _ => z.norm_coe_le_norm (timeClamp t))
  have hs : |(s : ℝ)| ≤ 2 := abs_le.mpr s.property
  change ‖∫ t in (0 : ℝ)..(s : ℝ), z (timeClamp t)‖ ≤ _
  calc
    _ ≤ ‖z‖ * |(s : ℝ)| := by simpa only [sub_zero] using h
    _ ≤ ‖z‖ * 2 := mul_le_mul_of_nonneg_left hs (norm_nonneg z)
    _ = _ := mul_comm _ _

noncomputable def primitiveCLM : C(Time, E) →L[ℝ] C(Time, E) :=
  LinearMap.mkContinuous (E := C(Time, E)) (F := C(Time, E))
    ({ toFun := primitive
       map_add' := by
         intro z w
         ext s
         exact intervalIntegral.integral_add
           ((z.continuous.comp timeClamp.continuous).intervalIntegrable _ _)
           ((w.continuous.comp timeClamp.continuous).intervalIntegrable _ _)
       map_smul' := by
         intro c z
         ext s
         exact intervalIntegral.integral_smul c _ } : C(Time, E) →ₗ[ℝ] C(Time, E))
    2 primitive_norm_le

@[simp] theorem primitiveCLM_apply (z : C(Time, E)) (s : Time) :
    primitiveCLM z s = ∫ t in (0 : ℝ)..(s : ℝ), z (timeClamp t) := rfl

@[simp] theorem primitiveCLM_zero (z : C(Time, E)) : primitiveCLM z ⟨0, by norm_num⟩ = 0 := by
  simp

theorem primitiveCLM_hasDerivAt (z : C(Time, E)) {s : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun t => primitiveCLM z (timeClamp t)) (z (timeClamp s)) s := by
  have hc := z.continuous.comp timeClamp.continuous
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    (hc.stronglyMeasurableAtFilter volume _) hc.continuousAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
  rw [primitiveCLM_apply, timeClamp_val (Ioo_subset_Icc_self ht)]
  rfl

end SemiHamiltonian.Geometry
