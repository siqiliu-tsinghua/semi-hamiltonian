module

public import SemiHamiltonian.Darboux.CubeGeometry

/-! Continuous identities on the interior extend to the compact cube. -/

@[expose] public section

open scoped NNReal Topology
open Filter

namespace SemiHamiltonian.Darboux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ≥0)

theorem continuousMap_eq_of_interior {F : Type*} [TopologicalSpace F] [T2Space F]
    (hr : 0 < r) (f g : C(Cube ι r, F))
    (hfg : ∀ x, point r x ∈ Metric.ball 0 (r : ℝ) → f x = g x) : f = g := by
  apply ContinuousMap.ext
  intro x
  have hl : NeBot (𝓝[Set.Ioo (0 : ℝ) 1] 1) := mem_closure_iff_nhdsWithin_neBot.mp (by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    simp)
  have hp : Continuous (fun t : ℝ => clamp r (t • point r x)) :=
    (clamp r).continuous.comp (continuous_id.smul continuous_const)
  have he : (fun t : ℝ => f (clamp r (t • point r x))) =ᶠ[𝓝[Set.Ioo (0 : ℝ) 1] 1]
      (fun t : ℝ => g (clamp r (t • point r x))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hn : ‖t • point r x‖ < r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      exact (mul_le_mul_of_nonneg_left (norm_point_le r x) ht.1.le).trans_lt
        (mul_lt_of_lt_one_left (show (0 : ℝ) < r from hr) ht.2)
    apply hfg
    rw [point_clamp_of_norm_le r hn.le, Metric.mem_ball, dist_zero_right]
    exact hn
  have hf := ((f.continuous.comp hp).tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioo (0 : ℝ) 1))
  have hg := ((g.continuous.comp hp).tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioo (0 : ℝ) 1))
  have h := tendsto_nhds_unique (hf.congr' he) hg
  simpa only [Function.comp_apply, one_smul, clamp_point] using h

end SemiHamiltonian.Darboux
