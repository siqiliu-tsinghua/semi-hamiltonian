module

public import SemiHamiltonian.Analysis.SmoothFunctions
public import SemiHamiltonian.Symmetry

/-! Strictly hyperbolic smooth diagonal systems and local families of actual symmetries. -/

@[expose] public section

open scoped Topology ContDiff Classical
open Filter Set

namespace SemiHamiltonian.Smooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℝ)} (hU : IsOpen U)

abbrev System := DiagonalSystem (coordinateDerivations hU)

/-- The real diagonal eigenvalues are pairwise distinct at every point. -/
def StrictlyHyperbolic (v : ι → Functions U) : Prop :=
  ∀ (x : U) (i j : ι), i ≠ j → v i x ≠ v j x

noncomputable def ofSpeeds (v : ι → Functions U) (hv : StrictlyHyperbolic v) : System hU :=
  DiagonalSystem.ofSpeeds (coordinateDerivations hU) v
    (fun i j hij => isUnit_of_ne_zero (v j - v i) (fun x => sub_ne_zero.mpr (hv x j i hij.symm)))

noncomputable def tsarevCoefficient (v : ι → Functions U) (i j : ι) (x : ι → ℝ) : ℝ :=
  fderiv ℝ (extend U (v i)) x (Pi.single j 1) / (extend U (v j) x - extend U (v i) x)

theorem ofSpeeds_coeff_apply (v : ι → Functions U) (hv : StrictlyHyperbolic v)
    (i j : ι) (hij : i ≠ j) (x : U) :
    (ofSpeeds hU v hv).coeff i j x = tsarevCoefficient v i j x := by
  have h := congrArg (fun f : Functions U => f x) ((ofSpeeds hU v hv).speed_deriv i j hij)
  change fderiv ℝ (extend U (v i)) x (Pi.single j 1) =
    (ofSpeeds hU v hv).coeff i j x * (v j x - v i x) at h
  simp only [tsarevCoefficient, extend_apply]
  exact (eq_div_iff (sub_ne_zero.mpr (hv x j i hij.symm))).mpr h.symm

theorem ofSpeeds_semiHamiltonian_iff (v : ι → Functions U) (hv : StrictlyHyperbolic v) :
    (ofSpeeds hU v hv).IsSemiHamiltonian ↔
      ∀ (x : U) (i j k : ι), i ≠ j → i ≠ k → j ≠ k →
        fderiv ℝ (tsarevCoefficient v i j) x (Pi.single k 1) =
          fderiv ℝ (tsarevCoefficient v i k) x (Pi.single j 1) := by
  have hd (i j k : ι) (hij : i ≠ j) (x : U) :
      (coordinateDerivations hU).deriv k ((ofSpeeds hU v hv).coeff i j) x =
        fderiv ℝ (tsarevCoefficient v i j) x (Pi.single k 1) := by
    have he : extend U ((ofSpeeds hU v hv).coeff i j) =ᶠ[𝓝 (x : ι → ℝ)] tsarevCoefficient v i j := by
      filter_upwards [hU.mem_nhds x.property] with y hy
      rw [show extend U ((ofSpeeds hU v hv).coeff i j) y =
        (ofSpeeds hU v hv).coeff i j ⟨y, hy⟩ from extend_apply _ _ ⟨y, hy⟩]
      exact ofSpeeds_coeff_apply hU v hv i j hij ⟨y, hy⟩
    change fderiv ℝ _ (x : ι → ℝ) _ = _
    rw [he.fderiv_eq]
  constructor
  · intro h x i j k hij hik hjk
    have he := congrArg (fun f : Functions U => f x) (h i j k hij hik hjk)
    simpa only [hd i j k hij x, hd i k j hik x] using he
  · intro h i j k hij hik hjk
    apply Subtype.ext
    funext x
    simpa only [hd i j k hij x, hd i k j hik x] using h x i j k hij hik hjk

noncomputable def restrictSystem {V : Set (ι → ℝ)} (hV : IsOpen V) (hVU : V ⊆ U)
    (S : System hU) : System hV where
  speed i := restrict hVU (S.speed i)
  coeff i j := restrict hVU (S.coeff i j)
  speed_deriv i j hij := by
    rw [show (coordinateDerivations hV).deriv j (restrict hVU (S.speed i)) =
      restrict hVU ((coordinateDerivations hU).deriv j (S.speed i)) from
        (restrict_derivation hU hV hVU (Pi.single j 1) (S.speed i)).symm]
    rw [S.speed_deriv i j hij, map_mul, map_sub]
  gap_unit i j hij := by
    simpa only [map_sub] using (S.gap_unit i j hij).map (restrict hVU)

theorem restrictSystem_semiHamiltonian {V : Set (ι → ℝ)} (hV : IsOpen V) (hVU : V ⊆ U)
    (S : System hU) (hS : S.IsSemiHamiltonian) : (restrictSystem hU hV hVU S).IsSemiHamiltonian := by
  intro i j k hij hik hjk
  change derivation hV (Pi.single k 1) (restrict hVU (S.coeff i j)) =
    derivation hV (Pi.single j 1) (restrict hVU (S.coeff i k))
  rw [← restrict_derivation hU hV, ← restrict_derivation hU hV]
  exact congrArg (restrict hVU) (hS i j k hij hik hjk)

/-- A local symmetry is an actual smooth solution on a neighbourhood. The
neighbourhood can depend on the base point, but is uniform in all prescribed values. -/
def LocallyRich (S : System hU) : Prop :=
  ∀ p : U, ∃ (V : Set (ι → ℝ)) (hV : IsOpen V) (hVU : V ⊆ U) (hp : (p : ι → ℝ) ∈ V),
    ∀ a : ι → ℝ, ∃ w : ι → Functions V,
      (restrictSystem hU hV hVU S).IsCommutingSpeed w ∧ ∀ i, w i ⟨p, hp⟩ = a i

theorem semiHamiltonian_of_locallyRich (S : System hU) (hS : LocallyRich hU S) :
    S.IsSemiHamiltonian := by
  intro i j k hij hik hjk
  apply Subtype.ext
  funext p
  obtain ⟨V, hV, hVU, hp, hsol⟩ := hS p
  let SV := restrictSystem hU hV hVU S
  obtain ⟨w, hw, hval⟩ := hsol (fun a => if a = i then 1 else 0)
  have hz := congrArg (eval (⟨p, hp⟩ : V))
    (SV.mixedObstruction_eq_zero_of_solution w hw i j k hij hik hjk)
  simp only [DiagonalSystem.mixedObstruction, map_sub, map_add, map_mul, map_zero] at hz
  change _ = (0 : ℝ) at hz
  have hv (a : ι) : eval (⟨p, hp⟩ : V) (w a) = if a = i then 1 else 0 := hval a
  rw [hv i, hv j, hv k] at hz
  simp [hij.symm, hik.symm] at hz
  have hd (a b c : ι) : eval (⟨p, hp⟩ : V) ((coordinateDerivations hV).deriv c (SV.coeff a b)) =
      (coordinateDerivations hU).deriv c (S.coeff a b) p := by
    change derivation hV (Pi.single c 1) (restrict hVU (S.coeff a b)) ⟨p, hp⟩ = _
    rw [← restrict_derivation hU hV, restrict_apply]
    rfl
  rw [hd, hd] at hz
  linear_combination -hz

/-- The abstract flow bracket is exactly the usual pointwise differential expression. -/
theorem flowBracketCoeff_apply (S : System hU) (w : ι → Functions U) (x : U) (i j : ι) :
    S.flowBracketCoeff w i j x =
      fderiv ℝ (extend U (w i)) x (Pi.single j 1) * (S.speed j x - S.speed i x) -
      fderiv ℝ (extend U (S.speed i)) x (Pi.single j 1) * (w j x - w i x) := rfl

theorem isCommutingSpeed_iff_pointwiseBracket (S : System hU) (w : ι → Functions U) :
    S.IsCommutingSpeed w ↔ ∀ (x : U) (i j : ι),
      fderiv ℝ (extend U (w i)) x (Pi.single j 1) * (S.speed j x - S.speed i x) -
      fderiv ℝ (extend U (S.speed i)) x (Pi.single j 1) * (w j x - w i x) = 0 := by
  rw [S.isCommutingSpeed_iff_flowBracketCoeff]
  constructor
  · intro h x i j
    exact congrArg (fun f : Functions U => f x) (h i j)
  · intro h i j
    apply Subtype.ext
    funext x
    exact h x i j

/-- All of the actual smooth commuting speeds constructed for one system also
commute with each other. -/
theorem commuting_speeds_pairwise_pointwise (S : System hU) (w z : ι → Functions U)
    (hw : S.IsCommutingSpeed w) (hz : S.IsCommutingSpeed z) (x : U) (i j : ι) :
    fderiv ℝ (extend U (z i)) x (Pi.single j 1) * (w j x - w i x) -
      fderiv ℝ (extend U (w i)) x (Pi.single j 1) * (z j x - z i x) = 0 :=
  congrArg (fun f : Functions U => f x) (S.commuting_speeds_pairwise w z hw hz i j)

end SemiHamiltonian.Smooth
