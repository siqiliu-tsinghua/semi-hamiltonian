# Formalization review

English | [中文](REVIEW.zh-CN.md)

- **Reviewed**: commit `b0e140b` (Lean `v4.35.0`, mathlib `v4.35.0`)
- **Date**: 2026-10-30
- **Reviewer**: Claude Code (`claude-opus-5-5`)
- **Scope**:
  1. axiom dependencies;
  2. whether the Lean definitions agree with the papers;
  3. whether the Lean statements of the main theorems agree with the papers.
- **References compared**:
  - The TeX source of the Pavlov–Sharipov–Svinolupov paper (PSS below, [arXiv:solv-int/9407003](https://arxiv.org/abs/solv-int/9407003)), formula by formula.
  - Tsarev's 1990 paper was not available. The Tsarev part was compared with (1.4) as quoted by PSS and with the standard statements of these results.

## Summary

- No mathematical errors were found, and no definition disagrees with the papers.
- Every declaration depends only on Lean's three standard axioms.
- PSS Theorems 2 and 4 are not formalized; Lean uses their conclusions as definitions. Both are standard material.
- A few points narrow the scope; see Section 4.

## 1. Axiom dependencies

**Only Lean's three standard axioms are used: `propext`, `Classical.choice`, `Quot.sound`.**

- **Full scan.** The script in the appendix goes through all 1888 declarations of the project (1511 theorems, 359 definitions) and collects the axioms each one depends on.
  - No declaration depends on any axiom outside these three.
  - The project contains no `axiom`, `opaque` or `unsafe` declarations.
- **`Checks/Axioms.lean`.** The 120 main theorems listed there all depend only on these three axioms, as the README states.
- **Reliability of the check under the module system.** The project uses Lean's module system, in which an importing module by default sees only the public interface of the modules it imports.
  - Lean 4.35's `Lean/Util/CollectAxioms.lean` shows that when a module's `.olean` is written, the axiom dependencies of every declaration are precomputed in an environment that contains all proof bodies, and exported with the module.
  - So `#print axioms` across module boundaries does see inside proofs, and a `sorry` inside a proof cannot be missed.
- **Source scan.** None of the following occur:
  - `sorry`, `admit`
  - `native_decide`, `implemented_by`, `@[extern]`
  - `debug.skipKernelTC`
  - custom macros or notation
- **Build and checks.**
  - `lake build` succeeds: 2996 jobs, 0 errors.
  - All 9 files in `Checks/` pass, with linter messages only.

## 2. Definitions

| PSS / Tsarev | Lean | Verdict |
|---|---|---|
| (1.4) semi-Hamiltonian condition | [`IsSemiHamiltonian`](SemiHamiltonian/Basic.lean), `Smooth.tsarevCoefficient`, `ofSpeeds_semiHamiltonian_iff` | Agrees; indices renamed only |
| (2.8) frame bracket and structure coefficients | [`FrameData.bracket`](SemiHamiltonian/PSS/Eigenframe.lean); `structureCoeff r i j` is `c^r_{ij}` | Agrees |
| (4.1) Nijenhuis tensor, (4.2) Haantjes tensor | `FrameData.nijenhuis`, `FrameData.haantjes`, `TensorRecipe.N` | Agrees |
| (4.4) components of the Nijenhuis tensor | [`matrixNijenhuis`](SemiHamiltonian/Geometry/MatrixTorsion.lean) | Agrees term by term |
| (4.3) eigenframe decomposition of the Haantjes tensor | `FrameData.haantjes_basis` | Agrees |
| (2.5) polarized, (2.9) | `polarizedSymmetry`, `PSS.polarized`, `SymmetryValuesAdmissible` | Agrees, including signs |
| (4.6), (4.9), (4.12), (4.15), (4.18) | [`TensorRecipe.FN / K / M / Q / P`](SemiHamiltonian/PSS/TensorRecipe.lean) | Agrees term by term, including the coefficients 4, −2, −2 |
| (4.7) α | [`PSS.alpha`](SemiHamiltonian/PSS/Polynomial.lean) | Agrees |
| (2.17) a conservation law has a flux | [`IsMatrixConservationLaw`](SemiHamiltonian/Geometry/ConservationJets.lean#L23): dq = dh∘M | Agrees |
| Tsarev's commuting-flow equation ∂ⱼwⁱ = Γᵢⱼ(wʲ−wⁱ) | `DiagonalSystem.IsCommutingSpeed` | Agrees |
| Tsarev's conservation-density equation ∂ⱼ∂ᵢh = Γᵢⱼ∂ᵢh + Γⱼᵢ∂ⱼh | `IsDensityGradient`, `IsDensity` | Agrees |
| Tsarev's hodograph formula wⁱ(u) = x + t·vⁱ(u) | `HodographRelation` | Agrees; same sign as the paper's uₜ = A·uₓ |

Further checks:

- **Smoothness.** The `∞` in `ContDiffOn ℝ ∞` is the coerced `(⊤ : ℕ∞)`, i.e. C∞. The project never uses `⊤` or `ω`, which would mean analyticity.
- **Derivatives and brackets.**
  - All derivatives are actual Fréchet derivatives.
  - `fieldBracket` is proved equal to mathlib's `VectorField.lieBracket`.
  - `Smooth.Functions U` is the algebra of actual C∞ functions on the open set U.
- **The diagonal formulas are checked.** The hand-derived formulas in diagonal coordinates in `DiagonalTensor` (for example `Kcycle`) are proved by [`DiagonalRecipe.P_basis`](SemiHamiltonian/PSS/DiagonalRecipe.lean#L122) to equal the values on the coordinate basis of the intrinsic tensor P, built literally from the paper's formulas.

## 3. Theorem statements

| PSS / Tsarev | Lean main theorem |
|---|---|
| Theorems 1, 3: rich symmetries ⇔ diagonalizable and semi-Hamiltonian | `Geometry.locallyRichMatrix_iff_locallySemiHamiltonian` |
| Theorem 5: rich conservation laws ⇔ diagonalizable and semi-Hamiltonian | `Geometry.locallyRichConservationLaws_iff_locallySemiHamiltonian` |
| Theorem 8: H = 0 ⇔ diagonalizable by a point transformation | `Geometry.haantjes_iff_locally_diagonalizable` |
| Theorem 9: P = 0 ⇔ semi-Hamiltonian | `Geometry.pss_iff_locallyAxisIntegrable`, `Geometry.locallyRichMatrix_iff_tensors`; in diagonal coordinates `DiagonalTensor.semiHamiltonian_iff_P_zero` |
| (4.8): α = 0 ⇔ semi-Hamiltonian | `PSS.semiHamiltonian_iff_alpha_zero` (proved through `alpha_eq`, not assumed) |
| (4.19), including repeated indices | [`DiagonalTensor.P_eq`](SemiHamiltonian/PSS/DiagonalTensor.lean#L117) |
| Tsarev: semi-Hamiltonian ⇔ commuting flows depend on n arbitrary functions of one variable | `Smooth.semiHamiltonian_iff_locallyAxisSolvable`, `Smooth.tsarev_iff_locallyAxisSolvable` |
| Tsarev's generalized hodograph method | `Smooth.generalized_hodograph`; the converse (completeness) `Smooth.generalized_hodograph_converse` goes beyond the papers |

Further checks:

- **No hidden extra hypotheses.**
  - The full kernel signatures of the theorems above were printed. The main theorems of the geometric layer have exactly three hypotheses: U is open, M is C∞ on U, and M is strictly hyperbolic at every point of U.
  - The 16 `include` commands in the sources add no hypotheses to the main theorems.
- **The theorems are not vacuous.** The check files give positive and negative instances of every key predicate:
  - In `Checks/PSSExample.lean`, a system with H = 0 but P ≠ 0 is proved neither rich nor integrable.
  - In `Checks/HaantjesExample.lean`, a system with H ≠ 0 is likewise proved neither rich nor integrable.
  - Both files also contain positive instances, including after a nonlinear change of coordinates.
- **The germ classifications have content.** `commutingSpeedGermEquiv`, `densityGermEquiv` and `originalConservationGermEquiv` are all obtained by applying `Equiv.ofBijective` to the natural map that takes germs along the coordinate axes. They are not vacuous statements of the form "equal cardinality gives some bijection".
- **Necessity does not presuppose coordinates.** The definitions of `LocallyRichMatrix` and `LocallyRichConservationLaws` mention no eigenframe and no Riemann coordinates. The coordinates are derived from the Haantjes condition.

## 4. Differences and caveats

In order of importance.

1. **PSS Theorem 2 is not proved; its conclusion is used as a definition.**
   - PSS Definition 1 calls a system a "hydrodynamic symmetry" when the two PDE flows are compatible. (2.4)+(2.5) is the equivalent characterization given by Theorem 2.
   - Lean defines [`Smooth.IsHydrodynamicSymmetry`](SemiHamiltonian/Geometry/SymmetryTransport.lean#L16) directly by (2.4)+(2.5).
   - Two docstrings state facts that are not proved:
     - [InvariantSymmetry.lean:11](SemiHamiltonian/PSS/InvariantSymmetry.lean#L11) says this is the condition that the two flows commute.
     - [Basic.lean:72](SemiHamiltonian/Basic.lean#L72) says `flowBracketCoeff` is the coefficient of uₓⁱuₓʲ in the commutator of the flows.
   - In the diagonal case this definition is equivalent to Tsarev's standard commutation condition.
   - This is standard material; it has been decided not to formalize it.
2. **PSS Theorem 4 is not formalized.**
   - Conservation laws are defined directly as "a flux dq = dh∘M exists".
   - Neither the paper's (2.14)–(2.16) (a conserved functional ⇔ a flux exists) nor the invariant form (2.18) appears in the code.
   - This is standard material; it has been decided not to formalize it.
3. **Only real eigenvalues are covered.** [`StrictHyperbolicAt`](SemiHamiltonian/Geometry/SmoothEigenframe.lean#L36) requires real, pairwise distinct eigenvalues. The paper's "general position" only requires distinct eigenvalues, so the case of complex eigenvalues is outside the Lean results.
4. **"Depends on n arbitrary functions of one variable" is formalized by choice.** The paper's phrase is informal. Lean gives four versions:
   - arbitrary values at the base point: `LocallyRichMatrix`
   - arbitrary first- and second-order jets: `LocallyRichConservationLaws`
   - arbitrary data on the axes of Riemann coordinates: `LocallyAxisSolvable`
   - bijections of function germs

   The necessity direction uses the weakest version, so its conclusion is stronger than the paper's statement.

   Note that the definition of [`LocallyOriginalConservationParametrized`](SemiHamiltonian/Geometry/ConservationClassification.lean#L206) itself requires Riemann coordinates to exist. Necessity for conservation laws without presupposing coordinates is given by the jet version.
5. **The general theory of the Frölicher–Nijenhuis bracket is not formalized** (Section 3 and Theorems 6, 7 of the paper).
   - K is defined directly by the expanded formula (4.6).
   - Lean proves that K, M, Q, P defined this way are C∞-linear tensors (`PSS/Tensoriality.lean`) and covariant under C∞ changes of coordinates (`Geometry/ChartTransport.lean`).
   - This is independent evidence that (4.6) contains no typo.
6. **Out of scope:**
   - the Hamiltonian-structure part of Tsarev's paper, that is, Dubrovin–Novikov brackets and flat metrics;
   - the items listed in the README section "Out of scope for now": infinite jet algebras, higher-order vanishing and uniqueness, quasi-triviality.
7. **Two typos in the paper itself; the formalization is not affected.**
   - In (2.16), ∂ⱼ(∂ₖAᵏᵢ) is missing f; it should be ∂ⱼ(∂ₖf·Aᵏᵢ).
   - In the sentence before (2.23), "(2.12) should be trivial" should refer to (2.21).
8. **Maintenance.**
   - The build reports 7 uses of deprecated names, for example `continuousOn_finset_sum`. These will become errors when mathlib is upgraded.
   - There are about 100 further linter messages, mostly unused section variables and unused simp arguments.

## 5. Method and limitations

- **The proofs were not read line by line.** The Lean kernel guarantees the correctness of the 15,000 lines of proofs. The review concentrated on what the kernel cannot guarantee: whether the definitions are faithful to the papers, the statements and hypotheses of the main theorems, and whether the theorems are vacuous.
- **Intermediate lemmas were not compared one by one.** The statements of intermediate lemmas, for example in the Darboux modules, were not each compared with the papers, since they only serve the proofs of the final theorems. One check was made: the compatibility condition ∂ₖΓᵢⱼ = ΓᵢⱼΓⱼₖ + ΓᵢₖΓₖⱼ − ΓᵢⱼΓᵢₖ in `local_existsUnique_smooth_darboux_of_functions` agrees with a direct computation of mixed-partial compatibility for the commuting-flow equations.
- **The Tsarev comparison is limited.** Tsarev's original paper was not available, so this part was compared only with PSS's citations and the standard statements.

## Appendix: full axiom scan script

Save the following as a `.lean` file anywhere outside the project directory, and run `lake env lean <path>` from the project root (after `lake build`).

```lean
import SemiHamiltonian

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut total : Nat := 0
  let mut byAx : Std.HashMap Name Nat := {}
  let mut offenders : Array (Name × Array Name) := #[]
  let mut unsafeDecls : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    unless (`SemiHamiltonian).isPrefixOf mods[idx.toNat]! do continue
    total := total + 1
    if ci.isUnsafe then unsafeDecls := unsafeDecls.push n
    let axs ← collectAxioms n
    for a in axs do byAx := byAx.insert a (byAx.getD a 0 + 1)
    if axs.any (fun a => !std.contains a) then offenders := offenders.push (n, axs)
  logInfo m!"declarations scanned: {total}"
  logInfo m!"unsafe declarations: {unsafeDecls}"
  logInfo m!"axiom usage: {byAx.toList}"
  logInfo m!"non-standard axioms: {offenders.size} {offenders.toList.take 20}"
```

Output on `b0e140b`:

```text
declarations scanned: 1888
unsafe declarations: []
axiom usage: [(Quot.sound, 1750), (Classical.choice, 1622), (propext, 1819)]
non-standard axioms: 0 []
```
