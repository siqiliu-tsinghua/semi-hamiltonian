module

public import SemiHamiltonian.Geometry.Haantjes
public import SemiHamiltonian.Geometry.FrameEvaluation
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! Smooth matrix fields and endomorphisms of actual smooth sections. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)}

noncomputable def constantField (v : ι → ℝ) : Fields U :=
  fun k => algebraMap ℝ (Functions U) (v k)

@[simp] theorem field_constantField (v : ι → ℝ) (x : U) :
    field (constantField (U := U) v) x = v := by
  ext k
  simp [constantField, field_apply, Algebra.algebraMap_eq_smul_one]

namespace Endomorphism

noncomputable def matrix (A : Endomorphism U) (q : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun k => ∑ j,
    field (A (standardField j)) q k • ContinuousLinearMap.proj j)

theorem matrix_field (A : Endomorphism U) (X : Fields U) (x : U) :
    A.matrix x (field X x) = field (A X) x := by
  conv_rhs => rw [← sum_standardField X, map_sum]
  ext k
  simp only [matrix, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, field_apply, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ j, A (standardField j) k x * X j x) =
    eval x (∑ j, X j * A (standardField j) k)
  rw [map_sum]
  simp only [map_mul]
  change (∑ j, A (standardField j) k x * X j x) = ∑ j, X j x * A (standardField j) k x
  simp only [mul_comm]

theorem matrix_smooth (A : Endomorphism U) : ContDiffOn ℝ ∞ A.matrix U := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_pi.mpr
  intro k
  simpa only [matrix, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul] using
    (ContDiffOn.sum (s := Finset.univ) (fun j _ =>
      (contDiffOn_pi.mp (field_smooth (A (standardField j))) k).mul
        (contDiffOn_const (c := v j))))

/-- Every smooth matrix field acts on the module of smooth vector fields. -/
noncomputable def ofField (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hM : ContDiffOn ℝ ∞ M U) : Endomorphism U where
  toFun X k := ofContDiffOn (fun q => M q (field X q) k)
    (contDiffOn_pi.mp (hM.clm_apply (field_smooth X)) k)
  map_add' X Y := by
    funext k
    apply Subtype.ext
    funext x
    have he : field (X + Y) x = field X x + field Y x := by ext j; simp [field_apply]
    change M x (field (X + Y) x) k = (M x (field X x) + M x (field Y x)) k
    rw [he, map_add]
  map_smul' f X := by
    funext k
    apply Subtype.ext
    funext x
    have he : field (f • X) x = f x • field X x := by ext j; simp [field_apply]
    change M x (field (f • X) x) k = (f x • M x (field X x)) k
    rw [he, map_smul]

theorem field_ofField (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hM : ContDiffOn ℝ ∞ M U) (X : Fields U) (x : U) :
    field (ofField M hM X) x = M x (field X x) := by
  ext k
  rw [field_apply]
  rfl

theorem matrix_ofField (M : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hM : ContDiffOn ℝ ∞ M U) (x : U) : (ofField M hM).matrix x = M x := by
  ext v k
  have hh := (ofField M hM).matrix_field (constantField v) x
  rw [field_constantField, field_ofField, field_constantField] at hh
  exact congrFun hh k

end Endomorphism
end SemiHamiltonian.Smooth
