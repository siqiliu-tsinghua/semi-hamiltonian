module

public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

namespace SemiHamiltonian.Geometry

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A fixed linear splitting along a normalized transverse vector. -/
noncomputable def hyperplaneSplit (ℓ : E →L[ℝ] ℝ) (t : E) (ht : ℓ t = 1) :
    E ≃L[ℝ] (ℓ.ker × ℝ) :=
  ({ toFun := fun v => (⟨v - ℓ v • t, by simp [ht]⟩, ℓ v)
     invFun := fun q => (q.1 : E) + q.2 • t
     left_inv := by intro v; simp
     right_inv := by
       intro ⟨v, s⟩
       have hv : ℓ v = 0 := v.property
       ext <;> simp [ht, hv]
     map_add' := by
       intro v w
       ext <;> simp [add_smul] <;> module
     map_smul' := by
       intro s v
       ext <;> simp [smul_sub, smul_smul, mul_comm] } : E ≃ₗ[ℝ] (ℓ.ker × ℝ)).toContinuousLinearEquiv

@[simp] theorem hyperplaneSplit_symm_apply (ℓ : E →L[ℝ] ℝ) (t : E) (ht : ℓ t = 1)
    (q : ℓ.ker × ℝ) : (hyperplaneSplit ℓ t ht).symm q = (q.1 : E) + q.2 • t := rfl

@[simp] theorem hyperplaneSplit_snd (ℓ : E →L[ℝ] ℝ) (t : E) (ht : ℓ t = 1)
    (v : E) : (hyperplaneSplit ℓ t ht v).2 = ℓ v := rfl

end SemiHamiltonian.Geometry
