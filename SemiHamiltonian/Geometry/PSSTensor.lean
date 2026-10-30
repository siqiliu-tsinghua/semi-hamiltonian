module

public import SemiHamiltonian.Geometry.Haantjes
public import SemiHamiltonian.PSS.FrameCalculus

/-! PSS tensors of actual smooth endomorphisms and their arbitrary-frame formula. -/

@[expose] public section

open scoped Classical
open Set

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)} (hU : IsOpen U)

noncomputable def bracketCalculus : PSS.BracketCalculus (Functions U) (Fields U) where
  bracket := fieldBracket hU
  anchor X f := fieldDerivation hU X f
  add_left X Y Z := by
    funext i
    simp only [fieldBracket, fieldDerivation_apply, Pi.add_apply, map_add,
      add_mul, Finset.sum_add_distrib]
    ring
  add_right X Y Z := by
    funext i
    simp only [fieldBracket, fieldDerivation_apply, Pi.add_apply, map_add,
      add_mul, Finset.sum_add_distrib]
    ring
  skew := fieldBracket_swap hU
  smul_left := fun f X Y => fieldBracket_smul_left hU X Y f
  smul_right := fun f X Y => fieldBracket_smul_right hU X Y f

/-- The PSS tensor is linear over C∞ functions in all three inputs. -/
noncomputable def pssTensor (A : Endomorphism U) :
    Fields U →ₗ[Functions U] Fields U →ₗ[Functions U] Fields U →ₗ[Functions U] Fields U :=
  (bracketCalculus hU).pTensor A

@[simp] theorem pssTensor_apply (A : Endomorphism U) (X Y Z : Fields U) :
    pssTensor hU A X Y Z = PSS.TensorRecipe.P (fieldBracket hU) A X Y Z := rfl

def PSSVanish (A : Endomorphism U) : Prop := ∀ X Y Z, pssTensor hU A X Y Z = 0

namespace Frame

variable (b : Frame U) (A : Endomorphism U) (v : ι → Functions U)
  (heigen : ∀ i, A (b i) = v i • b i)

include heigen

/-- The invariant construction agrees with the recipe in any smooth eigenframe,
including nonzero structure coefficients. -/
theorem pss_coordinates (X Y Z : Fields U) :
    b.equivFun (pssTensor hU A X Y Z) =
      PSS.TensorRecipe.P (b.data hU).bracket (PSS.FrameData.applyDiagonal v)
        (b.equivFun X) (b.equivFun Y) (b.equivFun Z) :=
  PSS.TensorRecipe.map_P b.equivFun.toAddMonoidHom
    (fun X Y => b.bracket_coordinates hU X Y)
    (b.endomorphism_coordinates A v heigen) X Y Z

end Frame
end SemiHamiltonian.Smooth
