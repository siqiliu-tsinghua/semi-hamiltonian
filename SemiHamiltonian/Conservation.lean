module

public import SemiHamiltonian.Tsarev

/-! Conservation densities and their gradient Darboux system.
All statements here are algebraic; existence of a potential or a flux is a
separate local analytic assertion. -/

@[expose] public section

namespace SemiHamiltonian

variable {𝕜 R ι : Type*} [CommRing 𝕜] [CommRing R] [Algebra 𝕜 R]

namespace CoordinateDerivations

def IsClosed (D : CoordinateDerivations 𝕜 R ι) (a : ι → R) : Prop :=
  ∀ i j, D.deriv j (a i) = D.deriv i (a j)

theorem gradient_closed (D : CoordinateDerivations 𝕜 R ι) (h : R) :
    D.IsClosed (fun i => D.deriv i h) := fun i j => D.commute j i h

end CoordinateDerivations

namespace DiagonalSystem

variable {D : CoordinateDerivations 𝕜 R ι} (S : DiagonalSystem D)

def IsConservationLaw (h q : R) : Prop := ∀ i, D.deriv i q = S.speed i * D.deriv i h

def IsDensityGradient (a : ι → R) : Prop :=
  ∀ i j, i ≠ j → D.deriv j (a i) = S.coeff i j * a i + S.coeff j i * a j

def IsDensity (h : R) : Prop := S.IsDensityGradient (fun i => D.deriv i h)

theorem densityGradient_closed {a : ι → R} (ha : S.IsDensityGradient a) : D.IsClosed a := by
  intro i j
  by_cases hij : i = j
  · subst j; rfl
  · rw [ha i j hij, ha j i (Ne.symm hij), add_comm]

theorem densityGradient_common_closed {a w : ι → R} (ha : S.IsDensityGradient a)
    (hw : S.IsCommutingSpeed w) : D.IsClosed (fun i => w i * a i) := by
  intro i j
  by_cases hij : i = j
  · subst j; rfl
  · simp only [Derivation.leibniz, smul_eq_mul]
    rw [ha i j hij, ha j i (Ne.symm hij), hw i j hij, hw j i (Ne.symm hij)]
    ring

theorem densityGradient_iff_closed (a : ι → R) :
    S.IsDensityGradient a ↔ D.IsClosed a ∧ D.IsClosed (fun i => S.speed i * a i) := by
  constructor
  · intro ha
    exact ⟨S.densityGradient_closed ha, S.densityGradient_common_closed ha S.speed_isCommutingSpeed⟩
  · rintro ⟨ha, hv⟩ i j hij
    have hh := hv i j
    simp only [Derivation.leibniz, smul_eq_mul] at hh
    rw [S.speed_deriv i j hij, S.speed_deriv j i hij.symm, ← ha i j] at hh
    apply (S.gap_unit i j hij).mul_right_cancel
    linear_combination -hh

theorem density_iff_closed (h : R) :
    S.IsDensity h ↔ D.IsClosed (fun i => S.speed i * D.deriv i h) := by
  exact (S.densityGradient_iff_closed _).trans (and_iff_right (D.gradient_closed h))

theorem conservationLaw_density {h q : R} (hq : S.IsConservationLaw h q) : S.IsDensity h := by
  apply (S.density_iff_closed h).mpr
  intro i j
  have hh := D.commute j i q
  rw [hq i, hq j] at hh
  exact hh

/-- The mixed derivative obstruction for the gradient system, evaluated on
arbitrary values, not on a putative solution. -/
def densityObstruction (i j k : ι) (a : ι → R) : R :=
  D.deriv k (S.coeff i j) * a i +
    S.coeff i j * (S.coeff i k * a i + S.coeff k i * a k) +
    D.deriv k (S.coeff j i) * a j +
    S.coeff j i * (S.coeff j k * a j + S.coeff k j * a k) -
  (D.deriv j (S.coeff i k) * a i +
    S.coeff i k * (S.coeff i j * a i + S.coeff j i * a j) +
    D.deriv j (S.coeff k i) * a k +
    S.coeff k i * (S.coeff k j * a k + S.coeff j k * a j))

def DensityCompatible : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ a, S.densityObstruction i j k a = 0

theorem densityObstruction_eq (i j k : ι) (a : ι → R) :
    S.densityObstruction i j k a =
      (D.deriv k (S.coeff i j) - D.deriv j (S.coeff i k)) * a i +
      S.darbouxResidual j i k * a j - S.darbouxResidual k i j * a k := by
  unfold densityObstruction darbouxResidual
  ring

theorem densityObstruction_eq_zero_of_solution {a : ι → R} (ha : S.IsDensityGradient a)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    S.densityObstruction i j k a = 0 := by
  have hh := D.commute k j (a i)
  rw [ha i j hij, ha i k hik] at hh
  simp only [map_add, Derivation.leibniz, smul_eq_mul] at hh
  rw [ha i k hik, ha j k hjk, ha i j hij, ha k j hjk.symm] at hh
  unfold densityObstruction
  linear_combination hh

theorem semiHamiltonian_iff_densityCompatible : S.IsSemiHamiltonian ↔ S.DensityCompatible := by
  constructor
  · intro hs i j k hij hik hjk a
    rw [S.densityObstruction_eq, hs i j k hij hik hjk,
      S.darbouxResidual_eq_zero hs j i k hij.symm hjk hik,
      S.darbouxResidual_eq_zero hs k i j hik.symm hjk.symm hij]
    ring
  · intro hc i j k hij hik hjk
    classical
    have hh := hc i j k hij hik hjk (fun l => if l = i then 1 else 0)
    rw [S.densityObstruction_eq] at hh
    simpa [hij.symm, hik.symm, sub_eq_zero] using hh

end DiagonalSystem
end SemiHamiltonian
