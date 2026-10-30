module

public import SemiHamiltonian.PSS.Tensoriality
public import SemiHamiltonian.PSS.Eigenframe

@[expose] public section

open scoped Classical

namespace SemiHamiltonian.PSS.FrameData

variable {𝕜 R ι : Type*} [CommRing 𝕜] [CommRing R] [Algebra 𝕜 R]
  [Fintype ι] [DecidableEq ι] (F : FrameData 𝕜 R ι)

def calculus : BracketCalculus R (ι → R) where
  bracket := F.bracket
  anchor X f := ∑ p, X p * F.deriv p f
  add_left X Y Z := by
    funext r
    simp only [bracket, Pi.add_apply, map_add, mul_add, add_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  add_right X Y Z := by
    funext r
    simp only [bracket, Pi.add_apply, map_add, mul_add, add_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  skew X Y := by
    funext r
    simp only [bracket, Pi.neg_apply]
    have hs : (∑ p, ∑ q, X p * Y q * F.structureCoeff r p q) =
        -(∑ p, ∑ q, Y p * X q * F.structureCoeff r p q) := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro q _
      rw [F.skew r q p]
      ring
    rw [hs]
    simp only [Finset.sum_sub_distrib]
    ring
  smul_left f X Y := by
    funext r
    simp only [bracket, Pi.smul_apply, smul_eq_mul, Derivation.leibniz,
      Pi.sub_apply, mul_sub, mul_add, mul_assoc, ← Finset.mul_sum,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp_rw [mul_left_comm (Y _) f, mul_comm (X r), ← mul_assoc]
    simp only [← Finset.sum_mul]
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  smul_right f X Y := by
    funext r
    simp only [bracket, Pi.smul_apply, smul_eq_mul, Derivation.leibniz,
      Pi.add_apply, mul_sub, mul_add, mul_assoc, ← Finset.mul_sum,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp_rw [mul_left_comm (X _) f, mul_comm (Y r), ← mul_assoc]
    simp only [← Finset.sum_mul]
    simp only [mul_assoc, ← Finset.mul_sum]
    ring

def diagonalMap (v : ι → R) : (ι → R) →ₗ[R] (ι → R) where
  toFun := applyDiagonal v
  map_add' X Y := by funext r; simp [applyDiagonal, mul_add]
  map_smul' f X := by funext r; simp [applyDiagonal, mul_left_comm]

omit [DecidableEq ι] in
theorem recipe_N_eq (v X Y : ι → R) :
    TensorRecipe.N F.bracket (diagonalMap v) X Y = F.nijenhuis v X Y := by
  funext r
  simp only [TensorRecipe.N, diagonalMap, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.add_apply, Pi.sub_apply, applyDiagonal, nijenhuis]
  ring

theorem sum_scaledBasis (X : ι → R) : ∑ p, X p • scaledBasis p 1 = X := by
  funext r
  simp [scaledBasis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end SemiHamiltonian.PSS.FrameData
