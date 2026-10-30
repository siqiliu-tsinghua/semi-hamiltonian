module

public import SemiHamiltonian.PSS.Polynomial
public import SemiHamiltonian.PSS.Eigenframe

/-!
# The PSS tensor in diagonal coordinates

These are the component recipes for N, K = 3{N,A²}, M, Q and P, specialized to a
diagonal operator in a coordinate frame. In particular P is built from N and its
derivatives, not defined to be a multiple of the semi-Hamiltonian obstruction.
The intrinsic construction and its covariance are proved in `Tensoriality` and
`Geometry/ChartTransport`; `DiagonalRecipe` proves agreement with this file.
-/

@[expose] public section

namespace SemiHamiltonian.PSS

variable {𝕜 R ι : Type*} [CommRing 𝕜] [CommRing R] [Algebra 𝕜 R]
variable [Fintype ι] [DecidableEq ι]

namespace CoordinateDerivations

/-- A coordinate frame has zero structure coefficients. -/
def frame (D : SemiHamiltonian.CoordinateDerivations 𝕜 R ι) : FrameData 𝕜 R ι where
  deriv := D.deriv
  structureCoeff := fun _ _ _ => 0
  self := by intros; rfl
  skew := by intros; simp

end CoordinateDerivations

namespace DiagonalTensor

variable (D : SemiHamiltonian.CoordinateDerivations 𝕜 R ι) (v : ι → R)

/-- Nijenhuis components in diagonal coordinates. -/
def N (r i j : ι) : R :=
  (if r = j then (v i - v j) * D.deriv i (v j) else 0) +
    (if r = i then (v i - v j) * D.deriv j (v i) else 0)

theorem N_eq_nijenhuis (r i j : ι) :
    N D v r i j = (CoordinateDerivations.frame D).nijenhuis v
      (FrameData.scaledBasis i 1) (FrameData.scaledBasis j 1) r := by
  rw [FrameData.nijenhuis_scaledBasis]
  simp [N, CoordinateDerivations.frame]

def contractN (f : ι → R) (i j : ι) : R := ∑ p, f p * N D v p i j

theorem contractN_eq (f : ι → R) (i j : ι) :
    contractN D v f i j = f j * ((v i - v j) * D.deriv i (v j)) +
      f i * ((v i - v j) * D.deriv j (v i)) := by
  simp [contractN, N, mul_add, mul_ite, Finset.sum_add_distrib]

/-- One cyclic summand in PSS (4.21), with B = A². -/
def Kcycle (r a b c : ι) : R :=
  (v r ^ 2 - v a ^ 2) * D.deriv a (N D v r b c) +
    (if r = a then contractN D v (fun p => D.deriv p (v a ^ 2)) b c else 0) -
    N D v r a c * D.deriv b (v c ^ 2) + N D v r a b * D.deriv c (v b ^ 2)

/-- K = 3{N,A²}, including all three cyclic summands. -/
def K (r a b c : ι) : R :=
  Kcycle D v r a b c + Kcycle D v r b c a + Kcycle D v r c a b

/-- PSS (4.12), expressed as contractions of N. -/
def M (r a b c : ι) : R :=
  contractN D v (fun p => (v p + v a - v b - v c) * N D v r a p) b c -
    v b * contractN D v (fun p => N D v r p b) a c +
    v c * contractN D v (fun p => N D v r p c) a b

/-- PSS (4.15). -/
def Q (r a b c : ι) : R :=
  (v a * v b - v a ^ 2 - v b * v c + v a * v c) * K D v r a b c +
    (4 * v a - 2 * v b - 2 * v c) * M D v r a b c

/-- PSS (4.18). -/
def P (r a b c : ι) : R :=
  (v r * v b + v r * v c - v r ^ 2 - v b * v c) * Q D v r a b c

/-- The component of K used in PSS (4.11). -/
theorem K_target (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) :
    K D v a a b c = alpha D v a b c +
      2 * (v b - v c) * ((v b - v a) + (v c - v a)) *
        (D.deriv b (v a) * D.deriv c (v a) -
          D.deriv b (v c) * D.deriv c (v a) - D.deriv c (v b) * D.deriv b (v a)) := by
  simp [K, Kcycle, contractN_eq, N, hab, hac,
    Derivation.leibniz, smul_eq_mul, map_sub, alpha]
  rw [D.commute c b]
  ring

/-- The component of M used in PSS (4.14). -/
theorem M_target (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) :
    M D v a a b c = -(v b - v c) * (v b - v a) * (v c - v a) *
      (D.deriv b (v a) * D.deriv c (v a) -
        D.deriv b (v c) * D.deriv c (v a) - D.deriv c (v b) * D.deriv b (v a)) := by
  simp [M, contractN_eq, N, hab, hac]
  ring

/-- PSS (4.19), for its possibly nonzero component. -/
theorem P_target (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) :
    P D v a a b c = (v b - v a) ^ 2 * (v c - v a) ^ 2 * alpha D v a b c := by
  rw [P, Q, K_target D v a b c hab hac, M_target D v a b c hab hac]
  ring

theorem P_at_second (a b c : ι) : P D v b a b c = 0 := by
  unfold P
  have h : v b * v b + v b * v c - v b ^ 2 - v b * v c = 0 := by ring
  rw [h, zero_mul]

theorem P_at_third (a b c : ι) : P D v c a b c = 0 := by
  unfold P
  have h : v c * v b + v c * v c - v c ^ 2 - v b * v c = 0 := by ring
  rw [h, zero_mul]

/-- All components of P, including repeated input indices. -/
theorem P_eq (r a b c : ι) :
    P D v r a b c =
      if r = a then (v b - v a) ^ 2 * (v c - v a) ^ 2 * alpha D v a b c else 0 := by
  by_cases hrb : r = b
  · subst r
    rw [P_at_second]
    by_cases hba : b = a <;> simp [hba]
  by_cases hrc : r = c
  · subst r
    rw [P_at_third]
    by_cases hca : c = a <;> simp [hca]
  by_cases hra : r = a
  · subst r
    rw [P_target D v a b c hrb hrc]
    simp
  · simp [P, Q, K, Kcycle, M, contractN_eq, N, hra, hrb, hrc]

/-- PSS's tensor criterion in diagonal coordinates, for the tensor assembled
from its N, K, M, Q recipes above. -/
theorem semiHamiltonian_iff_P_zero (S : DiagonalSystem D) :
    S.IsSemiHamiltonian ↔ ∀ r a b c, P D S.speed r a b c = 0 := by
  rw [semiHamiltonian_iff_alpha_zero D S]
  constructor
  · intro h r a b c
    rw [P_eq]
    split_ifs with hra
    · by_cases hab : a = b
      · subst b; simp
      by_cases hac : a = c
      · subst c; simp
      by_cases hbc : b = c
      · subst c
        have hz : alpha D S.speed a b b = 0 := by simp [alpha]
        rw [hz, mul_zero]
      · rw [h a b c hab hac hbc, mul_zero]
    · rfl
  · intro h a b c hab hac _
    have hz := h a a b c
    rw [P_target D S.speed a b c hab hac] at hz
    apply ((S.gap_unit a b hab).pow 2 |>.mul ((S.gap_unit a c hac).pow 2)).mul_left_cancel
    simpa only [mul_zero] using hz

end DiagonalTensor
end SemiHamiltonian.PSS
