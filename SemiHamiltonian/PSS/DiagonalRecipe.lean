module

public import SemiHamiltonian.PSS.FrameCalculus
public import SemiHamiltonian.PSS.DiagonalTensor

/-! The invariant PSS tensor specializes to the diagonal component formula.
All components, including repeated indices, are covered. -/

@[expose] public section

open scoped Classical

namespace SemiHamiltonian.PSS.DiagonalRecipe

variable {𝕜 R ι : Type*} [CommRing 𝕜] [CommRing R] [Algebra 𝕜 R]
  [Fintype ι] [DecidableEq ι]
  (D : SemiHamiltonian.CoordinateDerivations 𝕜 R ι) (v : ι → R)

local notation "F" => CoordinateDerivations.frame D
local notation "C" => FrameData.calculus (CoordinateDerivations.frame D)
local notation "A" => FrameData.diagonalMap v
local notation "e" => fun i => FrameData.scaledBasis i (1 : R)

theorem N_basis (r i j : ι) :
    (C).nijenhuis A (e i) (e j) r = DiagonalTensor.N D v r i j := by
  change TensorRecipe.N (F).bracket A (e i) (e j) r = _
  rw [FrameData.recipe_N_eq (F) v]
  exact (DiagonalTensor.N_eq_nijenhuis D v r i j).symm

theorem N_left (X : ι → R) (r j : ι) :
    (C).nijenhuis A X (e j) r = ∑ p, X p * DiagonalTensor.N D v r p j := by
  nth_rw 1 [← FrameData.sum_scaledBasis X]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, N_basis]

theorem N_right (Y : ι → R) (r i : ι) :
    (C).nijenhuis A (e i) Y r = ∑ p, Y p * DiagonalTensor.N D v r i p := by
  nth_rw 1 [← FrameData.sum_scaledBasis Y]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, N_basis]

theorem bracket_basis (i j : ι) : (F).bracket (e i) (e j) = 0 := by
  funext r
  simp [FrameData.bracket_scaledBasis, CoordinateDerivations.frame]

theorem bracket_basis_left (i : ι) (Y : ι → R) :
    (F).bracket (e i) Y = fun r => D.deriv i (Y r) := by
  funext r
  by_cases h : r = i <;>
    simp [FrameData.bracket, FrameData.scaledBasis, CoordinateDerivations.frame, h]

theorem bracket_scaled_left (i j : ι) (a : R) :
    (F).bracket (a • e i) (e j) = -(D.deriv j a) • e i := by
  change (C).bracket (a • e i) (e j) = _
  rw [(C).smul_left]
  change a • (F).bracket (e i) (e j) - (∑ p, e j p * D.deriv p a) • e i = _
  simp [bracket_basis, FrameData.scaledBasis]

theorem bracket_scaled_right (i j : ι) (a : R) :
    (F).bracket (e i) (a • e j) = (D.deriv i a) • e j := by
  change (C).bracket (e i) (a • e j) = _
  rw [(C).smul_right]
  change (∑ p, e i p * D.deriv p a) • e j + a • (F).bracket (e i) (e j) = _
  simp [bracket_basis, FrameData.scaledBasis]

omit [Fintype ι] in
theorem A_basis (i : ι) : A (e i) = v i • e i := by
  funext r
  by_cases h : r = i <;> simp [FrameData.diagonalMap, FrameData.applyDiagonal,
    FrameData.scaledBasis, h]

omit [Fintype ι] [DecidableEq ι] in
theorem A_apply (X : ι → R) (r : ι) : A X r = v r * X r := rfl

theorem Kcycle_basis (r a b c : ι) :
    TensorRecipe.FNcycle (F).bracket (fun X => A (A X))
      (fun X Y => (C).nijenhuis A X Y) (e a) (e b) (e c) r =
      DiagonalTensor.Kcycle D v r a b c := by
  have hA (i : ι) : A (A (e i)) = (v i ^ 2) • e i := by
    rw [A_basis, map_smul, A_basis, smul_smul, ← pow_two]
  simp only [TensorRecipe.FNcycle, hA, bracket_basis, map_zero,
    bracket_scaled_left, bracket_scaled_right, map_smul,
    add_zero, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hs (f : R) (X Y : ι → R) : (F).bracket (f • X) Y =
      f • (F).bracket X Y - (∑ p, Y p * D.deriv p f) • X := (C).smul_left f X Y
  rw [hs]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [A_apply, bracket_basis_left, N_basis D v,
    FrameData.scaledBasis, DiagonalTensor.Kcycle, DiagonalTensor.contractN]
  by_cases h : r = a <;> simp [h, mul_comm, mul_left_comm] <;> ring

theorem K_basis (r a b c : ι) :
    (C).kTensor A (e a) (e b) (e c) r = DiagonalTensor.K D v r a b c := by
  change TensorRecipe.FNcycle (F).bracket (fun X => A (A X))
      (fun X Y => (C).nijenhuis A X Y) (e a) (e b) (e c) r +
    TensorRecipe.FNcycle (F).bracket (fun X => A (A X))
      (fun X Y => (C).nijenhuis A X Y) (e b) (e c) (e a) r +
    TensorRecipe.FNcycle (F).bracket (fun X => A (A X))
      (fun X Y => (C).nijenhuis A X Y) (e c) (e a) (e b) r = _
  simp only [Kcycle_basis, DiagonalTensor.K]

theorem M_basis (r a b c : ι) :
    (C).mTensor A (e a) (e b) (e c) r = DiagonalTensor.M D v r a b c := by
  simp only [BracketCalculus.mTensor_apply, TensorRecipe.M, ← BracketCalculus.nijenhuis_apply,
    A_basis, map_smul, LinearMap.smul_apply, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, N_basis D v, N_left D v, N_right D v]
  simp only [A_apply, N_basis D v, DiagonalTensor.M, DiagonalTensor.contractN]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem Q_basis (r a b c : ι) :
    (C).qTensor A (e a) (e b) (e c) r = DiagonalTensor.Q D v r a b c := by
  simp only [BracketCalculus.qTensor_apply, TensorRecipe.Q,
    ← BracketCalculus.kTensor_apply, ← BracketCalculus.mTensor_apply,
    A_basis, map_smul, LinearMap.smul_apply, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, K_basis, M_basis, DiagonalTensor.Q]
  simp only [nsmul_eq_mul]
  ring

/-- Equality with the component recipe used in the already proved diagonal criterion. -/
theorem P_basis (r a b c : ι) :
    (C).pTensor A (e a) (e b) (e c) r = DiagonalTensor.P D v r a b c := by
  simp only [BracketCalculus.pTensor_apply, TensorRecipe.P,
    ← BracketCalculus.qTensor_apply, A_basis, map_smul, LinearMap.smul_apply,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [A_apply, Q_basis D v, DiagonalTensor.P]
  ring

/-- The intrinsic tensor criterion, with arbitrary vector inputs. -/
theorem semiHamiltonian_iff_tensor_zero (S : DiagonalSystem D) :
    S.IsSemiHamiltonian ↔ ∀ X Y Z,
      (C).pTensor (FrameData.diagonalMap S.speed) X Y Z = 0 := by
  rw [DiagonalTensor.semiHamiltonian_iff_P_zero]
  constructor
  · intro h X Y Z
    have hb (a b c : ι) :
        (C).pTensor (FrameData.diagonalMap S.speed) (e a) (e b) (e c) = 0 := by
      funext r
      exact (P_basis D S.speed r a b c).trans (h r a b c)
    rw [← FrameData.sum_scaledBasis X, ← FrameData.sum_scaledBasis Y,
      ← FrameData.sum_scaledBasis Z]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      hb, smul_zero, Finset.sum_const_zero]
  · intro h r a b c
    rw [← P_basis D S.speed r a b c, h]
    rfl

end SemiHamiltonian.PSS.DiagonalRecipe
