module

public import SemiHamiltonian.PSS.FrameCalculus

@[expose] public section

namespace SemiHamiltonian.PSS.FrameData

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Over a ring with invertible eigenvalue gaps, the centralizer consists of diagonal maps. -/
theorem diagonalMap_eq_of_commute (v : ι → R)
    (hgap : ∀ i j, i ≠ j → IsUnit (v i - v j))
    (B : (ι → R) →ₗ[R] (ι → R)) (hc : Function.Commute (diagonalMap v) B) :
    B = diagonalMap (fun i => B (scaledBasis i 1) i) := by
  let w := fun i => B (scaledBasis i 1) i
  have hb (i : ι) : B (scaledBasis i 1) = scaledBasis i (w i) := by
    funext r
    by_cases hri : r = i
    · subst r; simp [w, scaledBasis]
    have hh := congrFun (hc (scaledBasis i 1)) r
    change v r * B (scaledBasis i 1) r = B (applyDiagonal v (scaledBasis i 1)) r at hh
    rw [applyDiagonal_scaledBasis, mul_one] at hh
    have he : scaledBasis i (v i) = v i • scaledBasis i 1 := by
      funext k; simp [scaledBasis, mul_ite]
    rw [he, map_smul] at hh
    change v r * B (scaledBasis i 1) r = v i * B (scaledBasis i 1) r at hh
    have hz : (v r - v i) * B (scaledBasis i 1) r = 0 := by rw [sub_mul, hh, sub_self]
    have hz' : B (scaledBasis i 1) r = 0 :=
      (hgap r i hri).mul_left_cancel (by simpa only [mul_zero] using hz)
    simp [scaledBasis, hri, hz']
  apply LinearMap.ext
  intro X
  rw [← sum_scaledBasis X, map_sum]
  simp only [map_smul, hb]
  funext r
  simp [diagonalMap, applyDiagonal, scaledBasis, Finset.sum_apply, mul_comm]

end SemiHamiltonian.PSS.FrameData
