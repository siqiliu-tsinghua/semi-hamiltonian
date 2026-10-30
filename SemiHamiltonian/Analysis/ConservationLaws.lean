module

public import SemiHamiltonian.Analysis.Potential
public import SemiHamiltonian.Analysis.GradientClassification

/-! Actual smooth densities and fluxes, including common densities for all
commuting hydrodynamic flows. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Set Filter

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U V T : Set (ι → ℝ)}

theorem restrict_trans (hVU : V ⊆ U) (hTV : T ⊆ V) (f : Functions U) :
    Smooth.restrict hTV (Smooth.restrict hVU f) = Smooth.restrict (hTV.trans hVU) f := by
  apply Subtype.ext
  funext x
  simp only [Smooth.restrict_apply]

theorem restrictSystem_trans (hU : IsOpen U) (hV : IsOpen V) (hT : IsOpen T)
    (hVU : V ⊆ U) (hTV : T ⊆ V) (S : System hU) :
    restrictSystem hV hT hTV (restrictSystem hU hV hVU S) =
      restrictSystem hU hT (hTV.trans hVU) S := by
  have hs : (fun i => Smooth.restrict hTV (Smooth.restrict hVU (S.speed i))) =
      (fun i => Smooth.restrict (hTV.trans hVU) (S.speed i)) := funext fun i => restrict_trans hVU hTV _
  have hc : (fun i j => Smooth.restrict hTV (Smooth.restrict hVU (S.coeff i j))) =
      (fun i j => Smooth.restrict (hTV.trans hVU) (S.coeff i j)) :=
    funext fun i => funext fun j => restrict_trans hVU hTV _
  unfold restrictSystem
  congr

theorem densityGradient_restrict (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (S : System hU) {a : ι → Functions U} (ha : S.IsDensityGradient a) :
    (restrictSystem hU hV hVU S).IsDensityGradient (fun i => Smooth.restrict hVU (a i)) := by
  intro i j hij
  change derivation hV (Pi.single j 1) (Smooth.restrict hVU (a i)) = _
  have hh := ha i j hij
  change derivation hU (Pi.single j 1) (a i) = _ at hh
  rw [← restrict_derivation hU hV, hh, map_add, map_mul, map_mul]
  rfl

theorem density_restrict (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (S : System hU) {h : Functions U} (hh : S.IsDensity h) :
    (restrictSystem hU hV hVU S).IsDensity (Smooth.restrict hVU h) := by
  have hd := densityGradient_restrict hU hV hVU S hh
  have he (i : ι) : (coordinateDerivations hV).deriv i (Smooth.restrict hVU h) =
      Smooth.restrict hVU ((coordinateDerivations hU).deriv i h) :=
    (restrict_derivation hU hV hVU (Pi.single i 1) h).symm
  intro i j hij
  dsimp only
  simp only [he]
  exact hd i j hij

theorem primitive_is_density (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (S : System hU) {a : ι → Functions U} (ha : S.IsDensityGradient a)
    {h : Functions V} (hh : ∀ i, (coordinateDerivations hV).deriv i h = Smooth.restrict hVU (a i)) :
    (restrictSystem hU hV hVU S).IsDensity h := by
  intro i j hij
  dsimp only
  rw [hh i, hh j]
  exact densityGradient_restrict hU hV hVU S ha i j hij

/-- Every density has an actual local flux for every commuting speed. Neither
the density nor the auxiliary commuting speed needs nondegenerate derivatives. -/
theorem exists_local_common_flux (hU : IsOpen U) (S : System hU)
    (h : Functions U) (hh : S.IsDensity h) (w : ι → Functions U) (hw : S.IsCommutingSpeed w)
    (p : U) (c : ℝ) :
    ∃ V, ∃ hV : IsOpen V, ∃ hVU : V ⊆ U, ∃ hpV : (p : ι → ℝ) ∈ V,
      ∃ q : Functions V, q ⟨p, hpV⟩ = c ∧
        ∀ i, (coordinateDerivations hV).deriv i q =
          Smooth.restrict hVU (w i) * (coordinateDerivations hV).deriv i (Smooth.restrict hVU h) := by
  obtain ⟨V, hV, hVU, hpV, q, hqp, hqd⟩ := exists_local_primitive hU
    (fun i => w i * (coordinateDerivations hU).deriv i h)
    (S.densityGradient_common_closed hh hw) p c
  refine ⟨V, hV, hVU, hpV, q, hqp, ?_⟩
  intro i
  rw [hqd i, map_mul]
  exact congrArg (fun z => Smooth.restrict hVU (w i) * z)
    (restrict_derivation hU hV hVU (Pi.single i 1) h)

theorem exists_local_flux (hU : IsOpen U) (S : System hU)
    (h : Functions U) (hh : S.IsDensity h) (p : U) (c : ℝ) :
    ∃ V, ∃ hV : IsOpen V, ∃ hVU : V ⊆ U, ∃ hpV : (p : ι → ℝ) ∈ V,
      ∃ q : Functions V, q ⟨p, hpV⟩ = c ∧
        (restrictSystem hU hV hVU S).IsConservationLaw (Smooth.restrict hVU h) q :=
  exists_local_common_flux hU S h hh S.speed S.speed_isCommutingSpeed p c

end SemiHamiltonian.Smooth
