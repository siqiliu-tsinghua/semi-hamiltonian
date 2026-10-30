module

public import SemiHamiltonian.Tsarev
public import SemiHamiltonian.PSS.Eigenframe

/-!
# Necessary conditions from actual families of symmetries

Pointwise richness is weaker than freedom of n one-variable functions, but is
enough for the necessity arguments below. It refers to actual solutions, and is
not defined by formal compatibility. Separating evaluations abstract evaluation
of smooth functions at points of their domain.
-/

@[expose] public section

namespace SemiHamiltonian

variable (R K Point : Type*) [CommRing R] [CommRing K]

structure SeparatingEvaluations where
  eval : Point → R →+* K
  separates : ∀ f g, (∀ p, eval p f = eval p g) → f = g

variable {R K Point} {ι : Type*}

/-- Every value vector at every point is realized by an actual solution. -/
def SeparatingEvaluations.PointwiseRich (E : SeparatingEvaluations R K Point)
    (solution : (ι → R) → Prop) : Prop :=
  ∀ p (a : ι → K), ∃ w, solution w ∧ ∀ i, E.eval p (w i) = a i

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra 𝕜 R]

/-- The necessity half of Tsarev's criterion for pointwise-rich actual symmetries. -/
theorem DiagonalSystem.semiHamiltonian_of_pointwiseRich
    {D : CoordinateDerivations 𝕜 R ι} (S : DiagonalSystem D)
    (E : SeparatingEvaluations R K Point) (h : E.PointwiseRich S.IsCommutingSpeed) :
    S.IsSemiHamiltonian := by
  classical
  intro i j k hij hik hjk
  apply E.separates
  intro p
  obtain ⟨w, hw, hv⟩ := h p (fun a => if a = i then 1 else 0)
  have hz := congrArg (E.eval p)
    (S.mixedObstruction_eq_zero_of_solution w hw i j k hij hik hjk)
  simp only [DiagonalSystem.mixedObstruction, map_sub, map_add, map_mul, map_zero] at hz
  rw [hv i, hv j, hv k] at hz
  simp [hij.symm, hik.symm] at hz
  linear_combination -hz

namespace PSS.FrameData

variable [Fintype ι] [DecidableEq ι] (F : PSS.FrameData 𝕜 R ι)

/-- PSS's algebraic necessity argument applied to a family of actual solutions. -/
theorem noTripleStructure_of_pointwiseRich (v : ι → R)
    (hgap : ∀ i j, i ≠ j → IsUnit (v i - v j))
    (E : SeparatingEvaluations R K Point)
    (h : E.PointwiseRich (F.IsHydrodynamicSymmetry v)) : F.NoTripleStructure := by
  intro r i j hri hrj hij
  apply E.separates
  intro p
  obtain ⟨w, hw, hv⟩ := h p (fun a => if a = r then 1 else 0)
  have hz := congrArg (E.eval p)
    (F.symmetryValuesAdmissible_of_symmetry v w hw r i j hri hrj hij)
  simp only [map_mul, map_add, map_sub, map_zero] at hz
  rw [hv r, hv i, hv j] at hz
  simp [hri.symm, hrj.symm] at hz
  have hu : IsUnit (E.eval p (v i) - E.eval p (v j)) := by
    simpa using (hgap i j hij).map (E.eval p)
  apply hu.mul_right_cancel
  simpa using hz

theorem haantjes_vanish_of_pointwiseRich (v : ι → R)
    (hgap : ∀ i j, i ≠ j → IsUnit (v i - v j))
    (E : SeparatingEvaluations R K Point)
    (h : E.PointwiseRich (F.IsHydrodynamicSymmetry v)) : F.HaantjesComponentsVanish v :=
  (F.haantjes_vanish_iff v hgap).mpr (F.noTripleStructure_of_pointwiseRich v hgap E h)

end PSS.FrameData
end SemiHamiltonian
