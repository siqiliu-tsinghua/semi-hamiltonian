# Semi-Hamiltonian systems in Lean

English | [中文](README.zh-CN.md)

The goal is to formalize, under strict hyperbolicity, the results of Tsarev and of Pavlov–Sharipov–Svinolupov (PSS): a system of hydrodynamic type is integrable if and only if it locally admits Riemann coordinates and is semi-Hamiltonian.

**Current status: the local integrability equivalence is proved for general C∞ matrix fields with pairwise distinct real eigenvalues. Actual commuting flows in the original variables can realize every centralizer value at the base point if and only if Riemann coordinates exist locally and the system is semi-Hamiltonian.** Both conditions are also equivalent to `H=0 ∧ P=0`, and to solvability for arbitrary smooth one-variable data on n axes. Necessity starts from actual commuting operators, derives the vanishing of the Haantjes tensor, and constructs the coordinates. Sufficiency uses the C∞ Darboux existence theorem proved in this project. Neighbourhoods are chosen before any prescribed values or initial data. Solvability is never replaced by formal compatibility, and there is no `sorry` and no new axiom.

Building on this, the project classifies the germs of commuting flows and of conservation densities, and proves local existence of a common flux. For the generalized hodograph method, it proves both the forward construction of local solutions and the converse (completeness). For general matrix fields, it shows that first- and second-order jet richness of conservation laws is equivalent to a parametrization of all actual conservation-density germs in the original variables by n arbitrary one-variable function germs. The parameter map and the additive constant of the density are given explicitly.

## Building

Lean and mathlib are both pinned to `v4.35.0`; the dependency commits are recorded in `lake-manifest.json`.

```powershell
lake build
lake env lean Checks/Axioms.lean
lake env lean Checks/DarbouxExample.lean
lake env lean Checks/SmoothDarbouxExample.lean
lake env lean Checks/LocalIntegrabilityExample.lean
lake env lean Checks/HaantjesExample.lean
lake env lean Checks/PSSExample.lean
lake env lean Checks/ClassificationExample.lean
lake env lean Checks/HodographExample.lean
lake env lean Checks/HodographConverseExample.lean
```

To download the Mathlib cache again:

```powershell
lake exe cache get Mathlib.RingTheory.Derivation.Basic Mathlib.Algebra.MvPolynomial.PDeriv Mathlib.Tactic.Ring Mathlib.Tactic.LinearCombination Mathlib.Tactic.FinCases Mathlib.Data.Matrix.Mul
lake exe cache get Mathlib.Analysis.Calculus.UniformLimitsDeriv Mathlib.Analysis.Calculus.Deriv.Comp Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus Mathlib.MeasureTheory.Integral.DominatedConvergence Mathlib.Analysis.Normed.Operator.Prod Mathlib.Topology.MetricSpace.Contracting
lake exe cache get Mathlib.Analysis.Calculus.ContDiff.Operations Mathlib.Analysis.Calculus.ContDiff.Deriv Mathlib.Analysis.Calculus.MeanValue
lake exe cache get Mathlib.Analysis.Calculus.FDeriv.Symmetric
lake exe cache get Mathlib.Analysis.Calculus.BumpFunction.InnerProduct Mathlib.Order.Filter.Germ.Basic
```

## What is proved

The equations are written `uₜⁱ = vⁱ(u) uₓⁱ`, with coefficients `Γᵢⱼ = ∂ⱼvⁱ / (vʲ − vⁱ)`, used only for distinct indices.

| File | Result proved |
| --- | --- |
| [Basic.lean](SemiHamiltonian/Basic.lean) | Commuting coordinate derivations; diagonal systems whose speed differences are invertible; construction and uniqueness of Tsarev's coefficients; equivalence of the symmetry equation with the commutator coefficients. |
| [Tsarev.lean](SemiHamiltonian/Tsarev.lean) | `semiHamiltonian_iff_formallyCompatible`: the semi-Hamiltonian condition is equivalent to the vanishing of every three-index mixed-derivative obstruction of the symmetry equations. |
| [Symmetry.lean](SemiHamiltonian/Symmetry.lean) | Tsarev's linear equations are equivalent to the PSS polarized commutation condition in a coordinate frame; these symmetries of one system commute with each other. |
| [Richness.lean](SemiHamiltonian/Richness.lean) | For a family of actual symmetries that realizes arbitrary values pointwise: Tsarev's necessity of the semi-Hamiltonian condition, and the vanishing of the PSS three-index structure coefficients and of the Haantjes components. |
| [PSS/Centralizer.lean](SemiHamiltonian/PSS/Centralizer.lean) | A matrix that commutes with a diagonal matrix whose speed differences are invertible is itself diagonal. |
| [PSS/Eigenframe.lean](SemiHamiltonian/PSS/Eigenframe.lean) | Nijenhuis and Haantjes tensors computed from the definition of the frame bracket; the PSS decomposition (4.3) and its equivalence with the vanishing of the three-index structure coefficients; (2.9) derived from the polarized commutation equation. |
| [PSS/Polynomial.lean](SemiHamiltonian/PSS/Polynomial.lean) | The polynomial obstruction `alpha` of PSS (4.7) is equivalent to the semi-Hamiltonian condition. |
| [PSS/DiagonalTensor.lean](SemiHamiltonian/PSS/DiagonalTensor.lean) | Builds P from the component formulas `N → K,M → Q → P` in diagonal coordinates; proves (4.11), (4.14), (4.19) and `semiHamiltonian_iff_P_zero`, including every case with repeated indices. |
| [PSS/TensorRecipe.lean](SemiHamiltonian/PSS/TensorRecipe.lean), [Tensoriality.lean](SemiHamiltonian/PSS/Tensoriality.lean) | The intrinsic constructions (4.6), (4.9), (4.12), (4.15), (4.18) of the paper; `K,M,Q,P` are proved to be trilinear tensors from the Leibniz rule for the Lie bracket, and to be natural. |
| [PSS/DiagonalRecipe.lean](SemiHamiltonian/PSS/DiagonalRecipe.lean) | The values of the intrinsic `P` on the standard basis equal the diagonal components above, including repeated indices, so it inherits the semi-Hamiltonian criterion. |
| [Examples.lean](SemiHamiltonian/Examples.lean) | Constant-coefficient systems, and the family of actual symmetries given by three arbitrary one-variable polynomials; a non-semi-Hamiltonian counterexample with speeds `(f,f+1,f+2)`, `f=X₁X₂`. Lean uses the indices `0,1,2`. |
| [Darboux/LocalC1.lean](SemiHamiltonian/Darboux/LocalC1.lean) | `local_existsUnique_C1_darboux`: for compatible C¹ coefficients there is a cube of positive radius on which, for arbitrary one-variable C¹ data on each axis, an actual C¹ solution exists and is unique; the radius depends only on the coefficients. |
| [Darboux/SmoothExistence.lean](SemiHamiltonian/Darboux/SmoothExistence.lean) | `local_existsUnique_smooth_darboux`: smooth coefficients and arbitrary smooth axis data give a unique C∞ solution; derivatives of all orders use the same neighbourhood of positive radius. Also a regularity theorem that upgrades existing C¹ solutions. |
| [Darboux/SmoothData.lean](SemiHamiltonian/Darboux/SmoothData.lean) | `local_existsUnique_smooth_darboux_of_functions`: accepts ordinary smooth coefficient functions directly and builds their actual first-derivative data automatically. |
| [Darboux/LocalSmoothData.lean](SemiHamiltonian/Darboux/LocalSmoothData.lean) | The coefficients need only be smooth on an open neighbourhood of the closed cube; interfaces for local solutions in terms of the actual PDE, axis data and ordinary functions. |
| [Analysis/SmoothFunctions.lean](SemiHamiltonian/Analysis/SmoothFunctions.lean) | The algebra of actual C∞ functions on an open set; coordinate derivations and their commutation; restriction to open subsets; pointwise evaluation; smooth inverses of nowhere-vanishing functions. |
| [Analysis/SmoothSystem.lean](SemiHamiltonian/Analysis/SmoothSystem.lean) | Systems built from pointwise strictly hyperbolic smooth speeds; links to the usual derivative-ratio condition, to actual commuting flows, and to necessity from sufficient local freedom. |
| [Analysis/TsarevLocal.lean](SemiHamiltonian/Analysis/TsarevLocal.lean) | Semi-Hamiltonicity is equivalent to solvability for arbitrary smooth data on n axes, and also to actual local smooth commuting flows taking arbitrary values at the base point. |
| [Analysis/PSSLocal.lean](SemiHamiltonian/Analysis/PSSLocal.lean) | For actual smooth diagonal systems, both local integrability conditions above are equivalent to the vanishing of the PSS diagonal components, `P=0`. |
| [Geometry/HaantjesLocal.lean](SemiHamiltonian/Geometry/HaantjesLocal.lean) | A general C∞ matrix field with distinct real eigenvalues at the base point and vanishing Haantjes tensor on a neighbourhood has genuine C∞ local diagonalizing coordinates. |
| [Geometry/HaantjesConverse.lean](SemiHamiltonian/Geometry/HaantjesConverse.lean) | Local smooth diagonalizability forces the Haantjes tensor to vanish; under strict hyperbolicity this gives an equivalence. |
| [Geometry/PSSTensor.lean](SemiHamiltonian/Geometry/PSSTensor.lean), [ChartTransport.lean](SemiHamiltonian/Geometry/ChartTransport.lean) | The PSS tensor on actual smooth vector fields; pushforward by the actual Jacobian preserves the Lie bracket, and the tensor is covariant under C∞ changes of coordinates. |
| [Geometry/PSSRestriction.lean](SemiHamiltonian/Geometry/PSSRestriction.lean) | Restriction of the PSS tensor to open subsets, and global vanishing from local vanishing, without assuming that local sections extend globally. |
| [Geometry/PSSLocal.lean](SemiHamiltonian/Geometry/PSSLocal.lean) | `pss_iff_locallyAxisIntegrable`: for a general strictly hyperbolic C∞ matrix field, `H=0 ∧ P=0` is equivalent to local solvability for arbitrary smooth axis data in Riemann coordinates. |
| [Geometry/SymmetryTransport.lean](SemiHamiltonian/Geometry/SymmetryTransport.lean), [PSSExistence.lean](SemiHamiltonian/Geometry/PSSExistence.lean) | Actual commuting operators in the sense of PSS (2.4), (2.5) are transported under changes of coordinates; a common coordinate neighbourhood is chosen before the data, and smooth commuting operators are then built in the original variables. |
| [PSS/SymmetryCalculus.lean](SemiHamiltonian/PSS/SymmetryCalculus.lean), [Geometry/SymmetryRestriction.lean](SemiHamiltonian/Geometry/SymmetryRestriction.lean) | When the operators commute algebraically, the polarized commutation equation is tensorial; actual commuting operators restrict to any open subset. |
| [PSS/DiagonalCentralizer.lean](SemiHamiltonian/PSS/DiagonalCentralizer.lean), [Geometry/SymmetryFrame.lean](SemiHamiltonian/Geometry/SymmetryFrame.lean) | An operator commuting with one of simple spectrum is diagonal in its eigenframe; the actual commutation equations are transported to frame components. |
| [Geometry/MatrixRichness.lean](SemiHamiltonian/Geometry/MatrixRichness.lean) | Defines `LocallyRichMatrix` without presupposing coordinates; realizability of arbitrary centralizer values forces the three-index structure coefficients to vanish at the base point, hence `H=0`. |
| [Geometry/RichnessTransport.lean](SemiHamiltonian/Geometry/RichnessTransport.lean), [DiagonalRichness.lean](SemiHamiltonian/Geometry/DiagonalRichness.lean) | Actual Jacobian changes of variables preserve local richness and its quantifier order; in the diagonal case it is equivalent to the existing `Smooth.LocallyRich`. |
| [Geometry/Integrability.lean](SemiHamiltonian/Geometry/Integrability.lean) | `locallyRichMatrix_iff_locallySemiHamiltonian`, `locallyRichMatrix_iff_locallyAxisIntegrable`, `locallyRichMatrix_iff_tensors`: the full local equivalence theorems for general matrix fields. |
| [Geometry/SmoothEigenframe.lean](SemiHamiltonian/Geometry/SmoothEigenframe.lean) | From a simple real spectrum at the base point, the implicit function theorem applied to a normalized eigen-equation gives a local C∞ eigenframe and nowhere-vanishing spectral gaps. |
| [Geometry/MatrixTorsion.lean](SemiHamiltonian/Geometry/MatrixTorsion.lean) | For general matrix fields, the pointwise Nijenhuis and Haantjes tensors agree with their definitions through brackets of actual smooth vector fields. |
| [Geometry/FrobeniusGraph.lean](SemiHamiltonian/Geometry/FrobeniusGraph.lean) | The C∞ Frobenius local-coordinate theorem for flat graph distributions, including a smooth inverse on the same fixed neighbourhood. |
| [Geometry/FirstIntegral.lean](SemiHamiltonian/Geometry/FirstIntegral.lean) | Every regular codimension-one Frobenius distribution has a local smooth first integral whose differential has kernel exactly the distribution. |
| [Geometry/CoframeCoordinates.lean](SemiHamiltonian/Geometry/CoframeCoordinates.lean) | The first integrals of an independent integrable coframe together form smooth coordinates; left eigenforms give an actual diagonalization of the matrix. |
| [Geometry/ConservationCriterion.lean](SemiHamiltonian/Geometry/ConservationCriterion.lean) | For general matrix fields, jet richness of actual conservation laws implies `H=0`, local semi-Hamiltonicity and `P=0`. |
| [Geometry/ConservationJetSufficiency.lean](SemiHamiltonian/Geometry/ConservationJetSufficiency.lean), [ConservationJetTransport.lean](SemiHamiltonian/Geometry/ConservationJetTransport.lean) | From Darboux data, builds arbitrary density gradients, critical Hessians and actual fluxes on a common neighbourhood; proves that Hessian richness is coordinate invariant, completing the two-sided criterion. |
| [Geometry/ConservationGerms.lean](SemiHamiltonian/Geometry/ConservationGerms.lean), [ConservationClassification.lean](SemiHamiltonian/Geometry/ConservationClassification.lean) | Bijections, under restriction and under changes of coordinates, of all density germs in the original variables that have an actual local flux; the natural axis-trace parametrization is equivalent to finite jet richness. |
| [Darboux/CurveCoordinates.lean](SemiHamiltonian/Darboux/CurveCoordinates.lean), [Analysis/TsarevCurve.lean](SemiHamiltonian/Analysis/TsarevCurve.lean) | Arbitrary local smooth data along a non-degenerate curve extend to actual smooth Darboux solutions and commuting speeds. |
| [Analysis/TransportUniqueness.lean](SemiHamiltonian/Analysis/TransportUniqueness.lean), [HodographTransport.lean](SemiHamiltonian/Analysis/HodographTransport.lean) | Local uniqueness of zero data for homogeneous linear transport systems, and the actual propagation equation of the hodograph residual. |
| [Analysis/HodographConverse.lean](SemiHamiltonian/Analysis/HodographConverse.lean) | Every actual C∞ solution of the PDE that is non-degenerate at the base point has a local hodograph representation, and its state Jacobian is invertible. |

The two two-sided criteria of the algebraic part are:

```lean
S.IsSemiHamiltonian ↔ S.FormallyCompatible
S.IsSemiHamiltonian ↔ ∀ r a b c, PSS.DiagonalTensor.P D S.speed r a b c = 0
```

They do not assert that every compatible differential algebra contains enough solutions; an arbitrary differential algebra has no such local existence property.

## Local integrability of actual smooth systems

Let `U ⊆ (ι → ℝ)` be open, `ι` finite, and `v : ι → Smooth.Functions U` actual C∞ functions. `Smooth.StrictlyHyperbolic v` requires the real characteristic speeds to be pairwise distinct at every point. `Smooth.ofSpeeds hU v hv` builds Tsarev's coefficients automatically. Equality of functions means pointwise equality on `U`. Ordinary functions enter this algebra through `Smooth.ofContDiffOn`.

The main results, in the namespace `SemiHamiltonian.Smooth`, are:

```lean
semiHamiltonian_iff_locallyAxisSolvable hU S :
  S.IsSemiHamiltonian ↔ LocallyAxisSolvable hU S

semiHamiltonian_iff_locallyRich hU S :
  S.IsSemiHamiltonian ↔ LocallyRich hU S

locallyAxisSolvable_iff_P_zero hU S :
  LocallyAxisSolvable hU S ↔
    ∀ r a b c, PSS.DiagonalTensor.P (coordinateDerivations hU) S.speed r a b c = 0
```

The quantifier order in `LocallyAxisSolvable` is as follows. For every base point `p ∈ U` there is a positive radius `r` with `B(p,r) ⊆ U` such that, for arbitrary smooth data `φᵢ : ℝ → ℝ`, there are actual smooth functions `wᵢ` with

```math
\partial_j w^i=\Gamma_{ij}(w^j-w^i),\qquad i\ne j,
\qquad w^i(p+s e_i)=\varphi_i(s).
```

The radius is chosen before the data and serves all orders of differentiation. The sup norm is used, so balls are open coordinate cubes. This predicate requires existence only; the Darboux modules separately prove existence and uniqueness for solutions with a C¹ extension to the closed cube.

`LocallyRich` only asks that commuting flows on one local neighbourhood take arbitrary prescribed values at the base point. The theorems show that this already implies semi-Hamiltonicity, and hence the stronger solvability for arbitrary axis data. Necessity uses the commutation of actual mixed partial derivatives; sufficiency uses the C∞ Darboux existence theorem proved here. `tsarev_iff_locallyAxisSolvable` states semi-Hamiltonicity in the usual form
`∂ₖ(∂ⱼvⁱ/(vʲ−vⁱ)) = ∂ⱼ(∂ₖvⁱ/(vᵏ−vⁱ))`.

`isCommutingSpeed_iff_pointwiseBracket` relates these solutions to the flow-commutation condition written with actual derivatives, and `commuting_speeds_pairwise_pointwise` proves that they commute with each other.

`Checks/LocalIntegrabilityExample.lean` starts from the actual speeds `vⁱ(x)=x⁰+x¹+x²+i`. On an arbitrary open set it checks strict hyperbolicity, nonzero Tsarev coupling coefficients, the three-index semi-Hamiltonian condition, solvability for arbitrary smooth axis data, and the PSS criterion.

## Local existence and uniqueness for the Darboux system

The Darboux modules treat the system on a finite-dimensional real space

```math
\partial_j w^i=\Gamma_{ij}(w^j-w^i),\qquad i\ne j,
\qquad w^i(s e_i)=\varphi_i(s).
```

The compatibility condition `IsDarbouxCompatible` is, for distinct indices,

```math
\partial_k\Gamma_{ij}
=\Gamma_{ij}\Gamma_{jk}+\Gamma_{ik}\Gamma_{kj}-\Gamma_{ij}\Gamma_{ik}.
```

The derivatives here are mathlib's actual Fréchet derivatives. `ScalarJet` records only a continuous function and its scaled continuous first derivative, and `IsCubeJet` asserts their relation with `HasFDerivAt`. This is not an infinite jet space, and "solvable" is not built into the definition of compatibility.

Main entry points:

- `existsUnique_C1_darboux_axisData`: on a small cube satisfying the contraction estimate, takes `φ ψ : ι → C(ℝ, ℝ)` directly, where `ψᵢ` is the derivative of `φᵢ` on the relevant interval. The conclusion is `∃! u : Values r, IsC1DarbouxSolution r Γ ... u`; uniqueness is for actual function values.
- `local_existsUnique_C1_darboux`: starting from compatible coefficients on a cube of any positive radius, constructs a smaller **positive radius** that works uniformly for all such data.
- `local_existsUnique_smooth_darboux`: when the coefficients are C∞ in the interior of the original cube, gives for arbitrary `φ : ι → C(ℝ, ℝ)` with `∀ i, ContDiff ℝ ∞ (φ i)` a unique `IsSmoothDarbouxSolution`. The radius is independent of both the data and the order of differentiation.
- `local_existsUnique_smooth_darboux_of_functions`: a convenience interface that takes ordinary smooth functions `γ i j` on the whole space; compatibility is required only on the given closed cube. It builds `smoothCoefficientJets` automatically, so no derivatives have to be supplied by hand. Coefficients that are only locally smooth can use the previous interface.
- `classicalSolution_unique`: any two classical solutions of the original PDE with the same axis data agree on a sufficiently small cube. Uniqueness itself needs no compatibility condition.

The proof first constructs a fixed point of a radial integral operator, iterating the function and its derivatives together and proving differentiability with the theorem on differentiating uniform limits. The chain rule, the fundamental theorem of calculus and the compatibility condition then show that the differential residual satisfies a homogeneous integral equation, and the contraction estimate forces the residual to vanish. The existence proved is therefore genuinely **existence for the PDE**, not merely a continuous solution of the integral equation.

C∞ regularity uses a parameter method. On the fixed unit cube set `zₓ(y) = w(x₁y₁,…,xₙyₙ)`; it satisfies `zₓ = Aₓ + Tₓ zₓ`. The scaled coefficients are `xⱼ Γᵢⱼ(xy)` and the data are `φᵢ(xᵢyᵢ)`. `CompactSmooth` proves that these are smooth maps into spaces of continuous functions, and `SmoothLinear` uses `‖Tₓ‖ < 1` and smoothness of operator inversion to prove that `(1 − Tₓ)⁻¹ Aₓ` is smooth. Evaluating at `y=(1,…,1)` gives C∞ regularity of the original solution. Only the contraction estimate for the zeroth-order operator is used, so the radius does not have to shrink order by order. The regularity conclusion of `integralFixedPoint_contDiff` does not itself need compatibility; compatibility is used in the earlier step that identifies the integral-equation solution as a solution of the PDE.

| Modules | Role |
| --- | --- |
| `IntegralEquation`, `Uniqueness`, `Local` | The continuous integral equation, uniqueness of classical solutions, choice of a positive radius. |
| `C1FixedPoint`, `JetAlgebra`, `C1Operator` | Closedness of the derivative graph; preservation of derivatives under multiplication, composition and integration; construction of the C¹ fixed point. |
| `JetCalculus`, `Homotopy`, `Residual`, `Interior` | The radial fundamental theorem of calculus, the identity for the differential residual, norm estimates for the residual, continuous extension. |
| `Existence`, `ValueUniqueness`, `AxisData`, `LocalC1` | Solutions of the original PDE, uniqueness of actual solutions, arbitrary one-variable data, the local theorem. |
| `CompactSmooth`, `SmoothLinear`, `Scaling` | Higher derivatives of compactly parametrized families of functions, smooth parameter dependence of linear fixed points, coordinate-scaling identities. |
| `SmoothExistence`, `SmoothData` | The C∞ regularity upgrade, smooth local existence and uniqueness, the interface for ordinary coefficient functions. |

The smooth Darboux version asserts `ContDiffOn ℝ ∞` in the interior of the coordinate cube, with the function and its first derivatives extending continuously to the closed cube. It does not additionally claim that all higher derivatives extend continuously to the boundary. Uniqueness is for actual function values. `Analysis/TsarevLocal.lean` connects this, by translation and restriction to open sets, to Tsarev systems near an arbitrary base point. `Checks/DarbouxExample.lean` exercises the C¹ data interface. `Checks/SmoothDarbouxExample.lean` exercises a two-dimensional system with non-constant, two-way coupling coefficients, and a three-dimensional system whose three-index compatibility is verified explicitly. The axiom dependencies of the main theorems are included in `Checks/Axioms.lean`.

## Haantjes local coordinates for general matrix fields

Let `U ⊆ (ι → ℝ)` be open, `ι` an arbitrary finite index set, and `A` an actual C∞ matrix field. `Geometry.StrictHyperbolicAt A p` only requires a real eigenbasis with distinct real eigenvalues at the point `p`. It contains no assumption that a smooth eigenframe, first integrals or coordinates exist.

From `p ∈ U`, `StrictHyperbolicAt A p` and `Smooth.MatrixHaantjesVanish A U`, `Geometry.haantjes_local_diagonalization` constructs coordinates `e` of type `OpenPartialHomeomorph`, whose source contains `p` and is contained in `U`, such that:

```text
e and e.symm are C∞ on their respective fixed open domains;
speed i is C∞ on e.source, and the speeds are pointwise distinct;
D e(q) (A(q) z) i = speed i(q) * D e(q) z i.
```

So in the new coordinates `r=e(q)` the matrix is diagonal with entries `speed i(e.symm r)`. The converse theorem `matrixHaantjesVanish_of_diagonalization` does not need distinct eigenvalues. If the field is strictly hyperbolic at every point of `U`, `haantjes_iff_locally_diagonalizable` gives:

```lean
Smooth.MatrixHaantjesVanish A U ↔ Geometry.LocallyDiagonalizable A U
```

The chain of proof is as follows. The implicit function theorem first selects simple eigenpairs, keeping the frame invertible and the spectral gaps nonzero on a common neighbourhood. The eigenframe decomposition of the actual Haantjes tensor is then linked to the involutivity of the complementary eigendistributions. For each codimension-one distribution, a transversal direction is chosen, the distribution is brought to flat graph form, and a first integral is constructed. Finally, the inverse function theorem assembles the independent first integrals into coordinates.

The Frobenius existence theorem used here is also proved. The smooth implicit function theorem on a Banach space of continuous paths solves a radial integral equation; after taking variations in the parameter, the transversal PDE residual satisfies a homogeneous linear ODE and vanishes by uniqueness. All orders share the same open neighbourhood; `ContDiffAt ℝ ∞` is never mistaken for C∞ on a fixed neighbourhood. The converse builds a commuting frame from the inverse of the coordinate Jacobian and uses the symmetry of second derivatives to show that its brackets vanish.

`Checks/HaantjesExample.lean` uses the non-constant, non-diagonal three-dimensional matrix `[[1,0,0],[x₀,2,0],[0,0,3]]` to exercise the pointwise tensor formulas, the strictly hyperbolic spectrum and the full local-coordinate interface. It also uses `[[1,0,0],[0,2,0],[0,-x₀,3]]` to verify a nonzero Haantjes obstruction: at the origin the third component of `H(e₀,e₁)` is `4`, so this field cannot be smoothly diagonalized locally.

## The PSS criterion in general coordinates

`Smooth.pssTensor hU A` is a threefold iterated `Functions U`-linear map acting on actual smooth vector fields. Its definition uses the actual Lie bracket and forms, in turn, `N`, `K=3{N,A²}`, `M`, `Q`, `P`. The proof that `K` is tensorial explicitly cancels every term that differentiates the input functions; tensoriality is not taken as an assumption.

In the `Geometry` namespace, `pss_iff_locallyAxisIntegrable hU hM hs` states:

```lean
(Smooth.MatrixHaantjesVanish M U ∧
  Smooth.PSSVanish hU (Smooth.Endomorphism.ofField M hM)) ↔
  LocallyAxisIntegrable M U
```

Here `hs` requires strict hyperbolicity at every point of `U`, and `hM` requires C∞. For every base point, `LocallyAxisIntegrable` requires genuine C∞ local coordinates with a smooth inverse and a diagonal system `S` on the target, such that the Jacobian actually transforms `M` into `S.speed` and `S` satisfies the `LocallyAxisSolvable` above. The coordinates are constructed in the conclusion, and "solvable for arbitrary data" still refers to actual smooth solutions of the PDE.

`LocallyAxisIntegrable.exists_symmetries` further restricts the coordinates to a chosen target cube and constructs smooth operators `B` in the original variables, proving that together with `M` they satisfy the PSS algebraic commutation and polarized bracket equations. The coordinates, the cube and the neighbourhood in the original variables are all chosen before any data. `hydrodynamicSymmetry_conjugate_iff` also transports general commuting operators in both directions.

`Checks/PSSExample.lean` uses actual C∞ coefficients to check `(f,f+1,f+2)`. For `f=x₀+x₁+x₂`, `P=0`; for `f=x₁x₂`, `P⁰₀₁₂=8` at the origin, so strict hyperbolicity alone is not enough. Both systems are also conjugated by the nonlinear shear `r₁=x₁+x₀²`, checking the zero/nonzero criterion and the transport of commuting operators.

## Integrability in the original variables is equivalent to semi-Hamiltonicity

`Geometry.LocallyRichMatrix hM` makes no mention of eigenframes or Riemann coordinates. It requires that for every `p ∈ U` there is a common open neighbourhood `V ⊆ U` such that every real linear operator `T` with `M(p) T = T M(p)` is realized by an actual smooth commuting operator `B` on `V`, that is, `B(p)=T`. Commuting here means `Smooth.IsHydrodynamicSymmetry`: the operators commute algebraically, and the PSS polarized equation built from actual Lie brackets vanishes identically. `V` is chosen before `T`.

`Geometry.LocallySemiHamiltonian M U` requires genuine smooth local Riemann coordinates with a smooth inverse, whose Jacobian transforms `M` into a diagonal system `S` with `S.IsSemiHamiltonian`. For a C∞ matrix field with simple real spectrum at every point of `U`, the main theorems are:

```lean
locallyRichMatrix_iff_locallySemiHamiltonian hU hM hs :
  LocallyRichMatrix hM ↔ LocallySemiHamiltonian M U

locallyRichMatrix_iff_locallyAxisIntegrable hU hM hs :
  LocallyRichMatrix hM ↔ LocallyAxisIntegrable M U

locallyRichMatrix_iff_tensors hU hM hs :
  LocallyRichMatrix hM ↔
    Smooth.MatrixHaantjesVanish M U ∧
      Smooth.PSSVanish hU (Smooth.Endomorphism.ofField M hM)
```

For necessity, the simple real spectrum first yields a local smooth eigenframe. Every actual commuting operator is diagonal in this frame, and arbitrary diagonal values can be prescribed through centralizer values at the base point. Substituting them into PSS (2.9) shows that the structure coefficients with three distinct indices vanish at that point, so `H=0`. The Haantjes local coordinates proved above then give Riemann coordinates. Local richness is preserved under actual changes of coordinates, and the compatibility of actual mixed partial derivatives gives the semi-Hamiltonian condition. Sufficiency goes the other way: smooth Darboux solutions realize arbitrary diagonal values, which are then transported back to the original variables.

`Checks/PSSExample.lean` verifies a positive example of the full theorem, the obstruction that `P≠0` poses to richness in the original variables, and that rich commuting flows persist after a nonlinear change of coordinates. `Checks/HaantjesExample.lean` also proves that the twisted matrix above has distinct real eigenvalues everywhere but `H≠0`, so it cannot have this richness. This also exercises the step of the necessity proof that must not presuppose Riemann coordinates.

## Germ classification of commuting flows

`Analysis/SymmetryClassification.lean` uses `Filter.Germ (𝓝 p)` for actual function germs, so neighbourhoods may shrink. A representative of `CommutingSpeedGerm hU S p` must be C∞ on some open neighbourhood of the base point and satisfy the actual Tsarev PDE. `ScalarGerm 0` denotes smooth one-variable germs. Its definition uses globally smooth representatives, but `exists_global_smooth_germ` proves with a smooth cutoff that every locally smooth germ has such a representative, so the data are not restricted.

For a semi-Hamiltonian system, `commutingSpeedGermEquiv` gives a genuine bijection:

```text
commuting-speed germs ≃ (ι → ScalarGerm 0)
w ↦ the germs of (s ↦ wⁱ(p + s eᵢ)).
```

Surjectivity comes from C∞ Darboux existence. Injectivity comes from `Darboux.germ_unique`, proved for this purpose, which applies to arbitrary solutions on different neighbourhoods and does not require them to share a boundary extension. `localCommutingSpeeds_pairwise` proves that any two such local flows commute.

`Geometry/SymmetryClassification.lean` further defines `HydrodynamicSymmetryGerm` for actual smooth operators. `symmetry_eq_diagonal` uses the distinct eigenvalues of the system to show that every commuting operator is diagonal, so `hydrodynamicSymmetryGermEquiv` puts **all** hydrodynamic commuting-operator germs in bijection with the n function germs above. The commuting operators themselves may have repeated eigenvalues. This classification is stated in chosen Riemann coordinates; the existing `hydrodynamicSymmetry_conjugate_iff` handles conjugation by actual coordinate changes.

## Conservation densities and common fluxes

Conservation laws are written `∂ₜ h(u) = ∂ₓ q(u)`. The corresponding equations are:

```text
∂ᵢq = vⁱ ∂ᵢh,
∂ⱼaᵢ = Γᵢⱼ aᵢ + Γⱼᵢ aⱼ,  aᵢ = ∂ᵢh,  i ≠ j.
```

`Conservation.lean` proves that formal compatibility of the gradient system is equivalent to semi-Hamiltonicity, and that for a gradient solution `a` both `a` and `v*a` are closed one-forms. For any commuting speed `w`, `w*a` is closed as well.

The analytic proof uses the extended Darboux equation `∂ⱼaᵢ = Aᵢⱼ aᵢ + Bᵢⱼ aⱼ`, with two independent coefficients. `Darboux/PairIntegral`, `PairC1`, `PairResidual`, `PairExistence`, `PairValueUniqueness`, `PairSmooth`, `PairLocal` and `PairOpen` prove, in turn, the integral equation, actual C¹ derivatives, vanishing of the differential residual, uniqueness, and C∞ regularity on the same neighbourhood. The positive radius in `Pair.local_existsUnique_smooth_darboux` is chosen before all axis data. `PairUniqueness` also gives germ uniqueness for arbitrary local solutions.

`Analysis/ConservationLocal.lean` connects this to actual semi-Hamiltonian systems, proving:

```lean
semiHamiltonian_iff_locallyDensityAxisSolvable hU S :
  S.IsSemiHamiltonian ↔ LocallyDensityAxisSolvable hU S
```

`Geometry.exists_local_potential` constructs actual smooth potentials from the radial Frobenius theorem proved above, and `Analysis/Potential.lean` connects it to coordinate one-forms. `exists_local_common_flux` therefore constructs an actual local flux for each commuting flow, rather than only proving that the flux equations are formally closed.

The main interface of `Analysis/DensityClassification.lean` is:

```lean
densityGermEquiv hU S p hS :
  DensityGerm hU S p ≃ (ℝ × (ι → ScalarGerm 0))
```

The real factor is the independent value `h(p)`; the remaining data are the germs of each `∂ᵢh` on the corresponding coordinate axis. So this classifies actual densities, not only their gradients. The flux has another independent additive constant, and `flux_germ_unique` proves that the flux germ is unique once this constant is fixed. The gradient existence theorem gives a common radius independent of the data; the potential and flux interfaces currently allow the neighbourhood to shrink further, and the classification is stated at the level of germs.

`Geometry/ConservationCriterion.lean` supplies the independent necessity part of PSS Theorem 5. For an actual C∞ matrix field with simple real spectrum, rich conservation laws imply that the Haantjes tensor vanishes; Riemann coordinates are then constructed and semi-Hamiltonicity follows. The main interfaces are `LocallyRichConservationLaws.haantjesVanish`, `.locallySemiHamiltonian` and `.tensors_vanish`; the last gives both `H=0` and `P=0`. The proof neither presupposes local diagonalizability nor borrows richness of commuting flows as a hypothesis.

"Rich" is made precise by `Geometry.LocallyRichConservationLaws`. Every point has a common open neighbourhood on which actual C∞ densities and fluxes satisfying `dq = dh ∘ M` realize every density gradient and, at zero gradient, every symmetric Hessian satisfying `B(Mx,y)=B(x,My)`. The neighbourhood is chosen before these first- and second-order data. At zero gradient the Hessian is an intrinsic bilinear tensor. `PSS/ConservationNecessity.lean` eliminates the structure coefficients with three distinct indices using a commutator identity for actual frame derivations and third derivatives; `Geometry/ScalarCommutator.lean` and `ConservationJets.lean` connect the computation to actual derivatives and conservation laws.

`Geometry/ConservationJetSufficiency.lean` proves the converse. In Riemann coordinates, constant and linear axis data give a finite family of actual densities and fluxes; the finite intersection of their neighbourhoods is taken, and linear combinations realize any required derivatives. This preserves the quantifier order "common neighbourhood before arbitrary jet data". `ConservationJetTransport.lean` proves the change-of-coordinates formula for critical Hessians with the actual second-order chain rule, which yields the two-sided theorem in general coordinates.

`Smooth.MatrixDensityGerm M U p` consists of actual C∞ density germs in the original coordinates; each has a representative with an actual C∞ flux satisfying `dq = dh ∘ M` on some open neighbourhood. `Geometry/ConservationGerms.lean` proves genuine bijections under restriction to open sets, under smooth changes of coordinates, and with the existing diagonal definition of densities.

The main results of `Geometry/ConservationClassification.lean` are:

```lean
locallyRichConservationLaws_iff_originalParametrized hU hM hs :
  LocallyRichConservationLaws M U ↔ LocallyOriginalConservationParametrized M U

locallyRichConservationLaws_iff_locallySemiHamiltonian hU hM hs :
  LocallyRichConservationLaws M U ↔ LocallySemiHamiltonian M U

locallyRichConservationLaws_iff_tensors hU hM hs :
  LocallyRichConservationLaws M U ↔
    MatrixHaantjesVanish M U ∧ PSSVanish hU (Endomorphism.ofField M hM)
```

`LocallyOriginalConservationParametrized` requires an actual local Riemann chart such that, at every point of the chart, the specified map `originalConservationData` is a bijection. This map takes `h(p)` and the germs of the `∂ᵢ` components of `h ∘ e⁻¹` on the i-th coordinate axis; the definition does not include the semi-Hamiltonian condition. `originalConservationGermEquiv` puts all density germs in the original variables in bijection with `ℝ × (ι → ScalarGerm 0)`, and `originalConservationData_value` and `originalConservationData_axes` verify explicitly what the parameters mean. Modulo the additive constant of the density, exactly n arbitrary smooth one-variable germs remain. The classification holds for germs, so representatives may shrink their neighbourhoods; finite jet richness on a common neighbourhood is ensured separately by the finite-family construction above.

## Actual local solutions by the generalized hodograph method

`Analysis/Hodograph.lean` uses the plus sign that matches the PDE of this project:

```text
wⁱ(u) = x + t vⁱ(u).
```

`generalized_hodograph` takes an actual commuting speed `w`, a base point `(x₀,t₀,u₀)` satisfying this equation, and the invertibility of the Jacobian with respect to the state variables `u`. It constructs a C∞ function `u(x,t)` on an open neighbourhood and proves the hodograph relation, the original PDE `uₜⁱ=vⁱ(u)uₓⁱ` and `uₓⁱ≠0`, together with uniqueness for the implicit equation in a specified open neighbourhood.

The core lemma `hodograph_solves` differentiates actual functions directly. Tsarev's equations make every off-diagonal entry of the hodograph Jacobian vanish on the solution, and differentiating in `x` and `t` then gives the original PDE. The semi-Hamiltonian condition is used earlier, to produce commuting speeds with arbitrary germs; once a commuting speed is given, this step uses only its PDE.

`generalized_hodograph_converse` in `Analysis/HodographConverse.lean` proves the converse (completeness). For any given C∞ solution `u(x,t)` whose components `uₓⁱ` are all nonzero at the base point, it constructs an actual C∞ commuting speed `w` on a neighbourhood in state space such that the same given solution satisfies `wⁱ(u)=x+t vⁱ(u)` on a space-time neighbourhood. The base point `(x₀,t₀)` is arbitrary, and the conclusion records the state neighbourhood, the space-time neighbourhood and the inclusions between them. `hodograph_stateJacobian_invertible` further proves from this relation that the state Jacobian is invertible, so the result connects directly to the implicit-function interface above.

The converse relies on a Darboux theorem for curves, which allows arbitrary local C∞ data on a curve whose component derivatives are all nonzero. `Darboux/CurveProjection` through `CurveSmooth` modify the integral operator by a projection onto the diagonal trace and prove actual C¹ solutions and C∞ regularity on the same neighbourhood. `CurveOpen` proves the corresponding uniqueness. `CurveCoordinates` handles general curves by componentwise local changes of coordinates and verifies that the transformed coefficients are actually compatible. `Analysis/TsarevCurve.lean` connects this to commuting speeds and handles data that are only locally smooth with a smooth cutoff.

Once `w` has been constructed along the initial line, `Analysis/HodographTransport.lean` proves that the residual `Fᵢ=wⁱ(u)-x-tvⁱ(u)` satisfies a homogeneous linear transport system. `Analysis/TransportUniqueness.lean` applies a maximum argument to a weighted square on shrinking trapezoids and proves that zero initial data force the residual to vanish on a time neighbourhood in both directions. The converse therefore rests on uniqueness of propagation for actual PDE solutions, not on uniqueness for the implicit equation.

`Checks/ClassificationExample.lean` checks a two-dimensional coupled system, arbitrary sine and exponential axis germs, the density constant `7`, and data representatives that are smooth only near the base point. `Checks/PSSExample.lean` also checks the density classification for a three-dimensional system with non-constant coupling, where the three-index compatibility condition is non-vacuous. After a nonlinear shear it checks richness of conservation laws in the original variables, and the unique original-variable density germ with constant `7` and prescribed sine and exponential data. The PSS and Haantjes counterexamples each rule out rich conservation laws, exercising the two independent obstructions `P≠0` and `H≠0`, and `P≠0` is also checked to rule out the full parametrization. `Checks/HodographExample.lean` exercises the forward construction of local solutions on the Burgers equation `uₜ=u uₓ`. `Checks/HodographConverseExample.lean` checks the converse representation on a nonlinear explicit two-component solution with distinct constant speeds, verifying its PDE and its non-degeneracy at the base point directly. `Checks/Axioms.lean` currently checks 120 main results, all of which depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Mathematical model and scope

The foundation is a family of commuting derivations `D.deriv i` on a commutative algebra `R`. `Analysis/SmoothFunctions.lean` realizes it as actual smooth functions on an open set with coordinate partial derivatives, and proves from the symmetry of second Fréchet derivatives that the derivations commute. A nowhere-vanishing speed difference has a smooth reciprocal, so pointwise strict hyperbolicity gives the `IsUnit (vʲ − vⁱ)` needed in the algebraic part. This condition cannot be replaced by the two functions merely being unequal as ring elements.

In the abstract algebra, `PointwiseRich` means that every vector of values at every point is attained by some actual solution; it is used in the necessity proofs. The smooth local theorems use `LocallyRich`, which lets the neighbourhood depend on the base point, and prove it equivalent to the stronger `LocallyAxisSolvable`. `SeparatingEvaluations` abstracts pointwise evaluation of functions, so that equality at every point implies equality of functions.

`FrameData` provides frame derivations and antisymmetric structure coefficients for calculations. `Geometry/VectorFields` and `SmoothFrame` realize it as actual smooth local frames and Lie brackets on Euclidean open sets, and `HaantjesLocal` constructs coordinates from the tensor condition. The geometric interface currently targets open subsets of finite-dimensional Euclidean space; it is not yet packaged as an interface for abstract smooth manifolds. `DiagonalTensor.P` is the component construction, and `Smooth.pssTensor` is the intrinsic tensor in general coordinates, proved to agree with it.

## Out of scope for now

Infinite jet algebras, the higher-order vanishing and uniqueness results in the appendices of the literature, and the quasi-triviality question after adjoining `(u^{i,1})⁻¹` are not covered at this stage.

## References

- S. P. Tsarev, *The geometry of Hamiltonian systems of hydrodynamic type. The generalized hodograph method*, Math. USSR-Izv. 37 (1991), 397–419; Russian original 1990: [record](https://www.mathnet.ru/php/archive.phtml?jrnid=im&option_lang=rus&paperid=1062&wshow=paper).
- M. V. Pavlov, R. A. Sharipov, S. I. Svinolupov, *Invariant Integrability Criterion for the Equations of Hydrodynamical Type*: [arXiv:solv-int/9407003](https://arxiv.org/abs/solv-int/9407003). Formula numbers follow this paper.

## License

Released under the MIT License; see [LICENSE](LICENSE).
