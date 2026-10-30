module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.Sequences

/-!
# Keeping a derivative while taking a Banach fixed point

The graph of differentiation is closed in the product of the uniform norms on
functions and derivatives. This lets us apply contraction to a function together
with a scaled derivative, without assuming that the limit is differentiable.
-/

@[expose] public section

open Filter
open scoped Topology NNReal

namespace SemiHamiltonian.Darboux

variable {K E F : Type*} [TopologicalSpace K] [hcompact : CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev FunctionJet (K E F : Type*) [TopologicalSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  C(K, F) × C(K, E →L[ℝ] F)

/-- `R` provides an ambient extension of functions on `K`; `a` allows us to use
a weighted norm for the derivative component. -/
def IsFunctionJet (R : E → K) (U : Set E) (a : ℝ) (z : FunctionJet K E F) : Prop :=
  ∀ x ∈ U, HasFDerivAt (fun y => z.1 (R y)) (a • z.2 (R x)) x

def functionJets (R : E → K) (U : Set E) (a : ℝ) :
    Submodule ℝ (FunctionJet K E F) where
  carrier := {z | IsFunctionJet R U a z}
  zero_mem' := by intro x _; simpa using (hasFDerivAt_const (0 : F) x)
  add_mem' := by
    intro f g hf hg x hx
    have hh := (hf x hx).add (hg x hx)
    change HasFDerivAt (fun y => f.1 (R y) + g.1 (R y))
      (a • f.2 (R x) + a • g.2 (R x)) x at hh
    simpa only [Prod.fst_add, Prod.snd_add, ContinuousMap.add_apply, smul_add] using hh
  smul_mem' := by
    intro c f hf x hx
    change HasFDerivAt (fun y => c • f.1 (R y)) (a • (c • f.2 (R x))) x
    have hh := (hf x hx).const_smul c
    change HasFDerivAt (fun y => c • f.1 (R y)) (c • (a • f.2 (R x))) x at hh
    simpa only [smul_comm a c] using hh

include hcompact in
theorem isClosed_isFunctionJet (R : E → K) {U : Set E} (hU : IsOpen U) (a : ℝ) :
    IsClosed {z : FunctionJet K E F | IsFunctionJet R U a z} := by
  let : FirstCountableTopology (FunctionJet K E F) :=
    UniformSpace.firstCountableTopology (FunctionJet K E F)
  apply IsSeqClosed.isClosed
  intro z q hz hq
  have hf := ContinuousMap.tendsto_iff_tendstoUniformly.mp
    (continuous_fst.tendsto q |>.comp hq)
  have hd := ContinuousMap.tendsto_iff_tendstoUniformly.mp
    (continuous_snd.tendsto q |>.comp hq)
  have hds : TendstoUniformly (fun n x => a • (z n).2 (R x))
      (fun x => a • q.2 (R x)) atTop :=
    ((ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] F)) a).uniformContinuous.comp_tendstoUniformly
      (hd.comp R)
  intro x hx
  exact hasFDerivAt_of_tendstoUniformlyOn hU hds.tendstoUniformlyOn
    (fun n y hy => hz n y hy) (fun y _ => (hf.comp R).tendsto_at y) hx

/-- A contraction preserving genuine derivative pairs has a genuine derivative
pair as its fixed point. The preservation and contraction estimates must still
be verified for the concrete integral operator. -/
theorem fixedPoint_isFunctionJet [CompleteSpace F]
    (R : E → K) {U : Set E} (hU : IsOpen U) (a : ℝ)
    (T : FunctionJet K E F → FunctionJet K E F) {q : ℝ≥0}
    (hT : ContractingWith q T)
    (hpres : ∀ z, IsFunctionJet R U a z → IsFunctionJet R U a (T z)) :
    IsFunctionJet R U a (hT.fixedPoint T) := by
  have hzero : IsFunctionJet R U a (0 : FunctionJet K E F) := by
    intro x _
    simpa using (hasFDerivAt_const (0 : F) x)
  have hit : ∀ n : ℕ, IsFunctionJet R U a (T^[n] 0) := by
    intro n
    induction n with
    | zero => exact hzero
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hpres _ ih
  exact (isClosed_isFunctionJet R hU a).mem_of_tendsto
    (hT.tendsto_iterate_fixedPoint 0) (Eventually.of_forall hit)

end SemiHamiltonian.Darboux
