# Semi-Hamiltonian systems in Lean

[English](README.md) | 中文

目标是在严格双曲条件下形式化 Tsarev 与 Pavlov–Sharipov–Svinolupov（PSS）的结论：流体型可积，当且仅当局部存在 Riemann 坐标且系统半哈密顿。

**当前状态：已证明一般 C∞ 矩阵场在实特征值两两互异条件下的局部可积性等价定理：原变量中的实际交换流能在基点实现任意中心化子值，当且仅当局部存在 Riemann 坐标且系统半哈密顿。** 两者也等价于 `H=0 ∧ P=0`，以及任意 n 个光滑单变量轴上初值可解。必要性从实际交换算子出发推导 Haantjes 消失并构造坐标；充分性使用已经证明的 C∞ Darboux 存在定理。邻域在任意取值或初值之前选定。没有把可解性替换为形式相容，也没有 `sorry` 或新增公理。

在此基础上，已加入完整交换流函数芽分类、守恒密度函数芽分类及公共通量的局部存在性。广义 hodograph 方法的正向局部解构造与反向完备性均已证明。一般矩阵场的守恒律一阶、二阶 jet 丰富性，现已与原变量中全部实际守恒密度芽的任意 n 个单变量函数芽参数化建立双向等价；参数映射和密度加法常数均明确给出。

## 构建

Lean 与 mathlib 均固定为 `v4.35.0`，依赖提交记录在 `lake-manifest.json`。

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

需要重新下载缓存时：

```powershell
lake exe cache get Mathlib.RingTheory.Derivation.Basic Mathlib.Algebra.MvPolynomial.PDeriv Mathlib.Tactic.Ring Mathlib.Tactic.LinearCombination Mathlib.Tactic.FinCases Mathlib.Data.Matrix.Mul
lake exe cache get Mathlib.Analysis.Calculus.UniformLimitsDeriv Mathlib.Analysis.Calculus.Deriv.Comp Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus Mathlib.MeasureTheory.Integral.DominatedConvergence Mathlib.Analysis.Normed.Operator.Prod Mathlib.Topology.MetricSpace.Contracting
lake exe cache get Mathlib.Analysis.Calculus.ContDiff.Operations Mathlib.Analysis.Calculus.ContDiff.Deriv Mathlib.Analysis.Calculus.MeanValue
lake exe cache get Mathlib.Analysis.Calculus.FDeriv.Symmetric
lake exe cache get Mathlib.Analysis.Calculus.BumpFunction.InnerProduct Mathlib.Order.Filter.Germ.Basic
```

## 已证明的内容

约定方程为 `uₜⁱ = vⁱ(u) uₓⁱ`，系数为 `Γᵢⱼ = ∂ⱼvⁱ / (vʲ − vⁱ)`，只在互异指标上使用。

| 文件 | 已证明的结论 |
| --- | --- |
| [Basic.lean](SemiHamiltonian/Basic.lean) | 交换坐标导数、速度差可逆的对角系统、Tsarev 系数的构造与唯一性、对称方程与交换子系数的等价性。 |
| [Tsarev.lean](SemiHamiltonian/Tsarev.lean) | `semiHamiltonian_iff_formallyCompatible`：半哈密顿条件等价于对称方程全部三指标混合导数障碍消失。 |
| [Symmetry.lean](SemiHamiltonian/Symmetry.lean) | Tsarev 线性方程等价于坐标标架中的 PSS 极化交换条件；同一系统的这些对称彼此交换。 |
| [Richness.lean](SemiHamiltonian/Richness.lean) | 对逐点可实现任意值的实际对称族，证明 Tsarev 的半哈密顿必要性，以及 PSS 的三指标结构系数消失、Haantjes 分量消失。 |
| [PSS/Centralizer.lean](SemiHamiltonian/PSS/Centralizer.lean) | 与速度差可逆的对角矩阵交换的矩阵必为对角矩阵。 |
| [PSS/Eigenframe.lean](SemiHamiltonian/PSS/Eigenframe.lean) | 从标架括号定义计算 Nijenhuis 与 Haantjes 张量；证明 PSS (4.3) 的分解及其与三指标结构系数消失的等价性，并从极化交换式推出 (2.9)。 |
| [PSS/Polynomial.lean](SemiHamiltonian/PSS/Polynomial.lean) | PSS (4.7) 的多项式障碍 `alpha` 与半哈密顿条件等价。 |
| [PSS/DiagonalTensor.lean](SemiHamiltonian/PSS/DiagonalTensor.lean) | 按对角坐标下的 `N → K,M → Q → P` 分量公式构造 P，证明 (4.11)、(4.14)、(4.19)，以及 `semiHamiltonian_iff_P_zero`。包含所有重复指标的情形。 |
| [PSS/TensorRecipe.lean](SemiHamiltonian/PSS/TensorRecipe.lean)、[Tensoriality.lean](SemiHamiltonian/PSS/Tensoriality.lean) | 原文 (4.6)、(4.9)、(4.12)、(4.15)、(4.18) 的内在构造；从 Lie 括号 Leibniz 规则证明 `K,M,Q,P` 为三线性张量，并证明自然性。 |
| [PSS/DiagonalRecipe.lean](SemiHamiltonian/PSS/DiagonalRecipe.lean) | 内在 `P` 在标准基上的取值等于已有对角分量；包括重复指标，故继承半哈密顿判据。 |
| [Examples.lean](SemiHamiltonian/Examples.lean) | 常系数系统及三个任意单变量多项式给出的实际对称族；速度为 `(f,f+1,f+2)`、`f=X₁X₂` 的非半哈密顿反例。Lean 使用指标 `0,1,2`。 |
| [Darboux/LocalC1.lean](SemiHamiltonian/Darboux/LocalC1.lean) | `local_existsUnique_C1_darboux`：相容 C¹ 系数在某个正半径立方体上，对任意各轴单变量 C¹ 初值存在唯一实际 C¹ 解；半径只依赖系数。 |
| [Darboux/SmoothExistence.lean](SemiHamiltonian/Darboux/SmoothExistence.lean) | `local_existsUnique_smooth_darboux`：光滑系数、任意光滑轴上初值产生唯一 C∞ 解；所有阶导数使用同一个正半径邻域。另有既存 C¹ 解的正则性提升定理。 |
| [Darboux/SmoothData.lean](SemiHamiltonian/Darboux/SmoothData.lean) | `local_existsUnique_smooth_darboux_of_functions`：直接接受普通光滑系数函数，自动构造其真实一阶导数数据。 |
| [Darboux/LocalSmoothData.lean](SemiHamiltonian/Darboux/LocalSmoothData.lean) | 系数只需在闭立方体的开邻域中光滑；提供实际 PDE、轴上初值及普通函数形式的局部解接口。 |
| [Analysis/SmoothFunctions.lean](SemiHamiltonian/Analysis/SmoothFunctions.lean) | 开集上的实际 C∞ 函数代数、坐标导子及其交换性、开集限制、逐点取值、处处非零函数的光滑逆。 |
| [Analysis/SmoothSystem.lean](SemiHamiltonian/Analysis/SmoothSystem.lean) | 从逐点严格双曲的光滑速度构造系统；连接通常的导数比条件、实际交换流及局部充分自由度的必要性。 |
| [Analysis/TsarevLocal.lean](SemiHamiltonian/Analysis/TsarevLocal.lean) | 半哈密顿性等价于任意 n 个光滑轴上初值可解，也等价于实际局部光滑交换流在基点可取得任意值。 |
| [Analysis/PSSLocal.lean](SemiHamiltonian/Analysis/PSSLocal.lean) | 实际光滑对角系统的上述两种局部可积性条件均等价于 PSS 对角分量 `P=0`。 |
| [Geometry/HaantjesLocal.lean](SemiHamiltonian/Geometry/HaantjesLocal.lean) | 一般 C∞ 矩阵场在基点有互异实特征值、邻域内 Haantjes 张量为零时，存在真正的 C∞ 局部对角化坐标。 |
| [Geometry/HaantjesConverse.lean](SemiHamiltonian/Geometry/HaantjesConverse.lean) | 局部光滑对角化必有 Haantjes 张量为零；在严格双曲条件下得到双向等价。 |
| [Geometry/PSSTensor.lean](SemiHamiltonian/Geometry/PSSTensor.lean)、[ChartTransport.lean](SemiHamiltonian/Geometry/ChartTransport.lean) | 实际光滑向量场上的 PSS 张量；实际雅可比推送保持 Lie 括号，张量在 C∞ 坐标变化下协变。 |
| [Geometry/PSSRestriction.lean](SemiHamiltonian/Geometry/PSSRestriction.lean) | PSS 张量限制到开子集以及由局部消失推出全域消失，不假设局部截面可全局延拓。 |
| [Geometry/PSSLocal.lean](SemiHamiltonian/Geometry/PSSLocal.lean) | `pss_iff_locallyAxisIntegrable`：一般严格双曲 C∞ 矩阵场的 `H=0 ∧ P=0` 等价于 Riemann 坐标中的任意光滑轴上初值局部可解。 |
| [Geometry/SymmetryTransport.lean](SemiHamiltonian/Geometry/SymmetryTransport.lean)、[PSSExistence.lean](SemiHamiltonian/Geometry/PSSExistence.lean) | PSS (2.4)、(2.5) 的实际交换算子在坐标变化下搬运；在初值之前选定共同坐标邻域，再构造原变量中的光滑交换算子。 |
| [PSS/SymmetryCalculus.lean](SemiHamiltonian/PSS/SymmetryCalculus.lean)、[Geometry/SymmetryRestriction.lean](SemiHamiltonian/Geometry/SymmetryRestriction.lean) | 在算子代数交换条件下，极化交换方程具有张量性；实际交换算子可限制到任意开子集。 |
| [PSS/DiagonalCentralizer.lean](SemiHamiltonian/PSS/DiagonalCentralizer.lean)、[Geometry/SymmetryFrame.lean](SemiHamiltonian/Geometry/SymmetryFrame.lean) | 简单谱的交换算子在特征标架中必为对角算子；把实际交换方程搬到标架分量。 |
| [Geometry/MatrixRichness.lean](SemiHamiltonian/Geometry/MatrixRichness.lean) | 定义不预设坐标的 `LocallyRichMatrix`；由任意中心化子值的可实现性推出三指标结构系数在基点消失，继而推出 `H=0`。 |
| [Geometry/RichnessTransport.lean](SemiHamiltonian/Geometry/RichnessTransport.lean)、[DiagonalRichness.lean](SemiHamiltonian/Geometry/DiagonalRichness.lean) | 实际雅可比变换保持局部丰富性及其量词顺序；对角情形与已有 `Smooth.LocallyRich` 等价。 |
| [Geometry/Integrability.lean](SemiHamiltonian/Geometry/Integrability.lean) | `locallyRichMatrix_iff_locallySemiHamiltonian`、`locallyRichMatrix_iff_locallyAxisIntegrable`、`locallyRichMatrix_iff_tensors`：一般矩阵场的完整局部等价定理。 |
| [Geometry/SmoothEigenframe.lean](SemiHamiltonian/Geometry/SmoothEigenframe.lean) | 由基点处简单实谱，通过规范化特征方程的隐函数定理构造局部 C∞ 特征标架及处处非零的谱隙。 |
| [Geometry/MatrixTorsion.lean](SemiHamiltonian/Geometry/MatrixTorsion.lean) | 一般矩阵场的逐点 Nijenhuis、Haantjes 张量与实际光滑向量场括号定义一致。 |
| [Geometry/FrobeniusGraph.lean](SemiHamiltonian/Geometry/FrobeniusGraph.lean) | 平坦图分布的 C∞ Frobenius 局部坐标定理，包含同一固定邻域上的光滑逆。 |
| [Geometry/FirstIntegral.lean](SemiHamiltonian/Geometry/FirstIntegral.lean) | 任意正则余维一 Frobenius 分布存在局部光滑第一积分，其微分的核恰好等于该分布。 |
| [Geometry/CoframeCoordinates.lean](SemiHamiltonian/Geometry/CoframeCoordinates.lean) | 独立可积余标架的第一积分可同时组成光滑坐标；左特征形式给出实际矩阵对角化。 |
| [Geometry/ConservationCriterion.lean](SemiHamiltonian/Geometry/ConservationCriterion.lean) | 一般矩阵场的实际守恒律 jet 丰富性推出 `H=0`、局部半哈密顿性及 `P=0`。 |
| [Geometry/ConservationJetSufficiency.lean](SemiHamiltonian/Geometry/ConservationJetSufficiency.lean)、[ConservationJetTransport.lean](SemiHamiltonian/Geometry/ConservationJetTransport.lean) | 从 Darboux 初值构造共同邻域上的任意密度梯度、临界 Hessian 与实际通量；证明 Hessian 丰富性的坐标不变性，补成完整双向判据。 |
| [Geometry/ConservationGerms.lean](SemiHamiltonian/Geometry/ConservationGerms.lean)、[ConservationClassification.lean](SemiHamiltonian/Geometry/ConservationClassification.lean) | 原变量中具有实际局部通量的全部密度芽，在限制及坐标变换下的双射；自然轴迹参数化与有限 jet 丰富性等价。 |
| [Darboux/CurveCoordinates.lean](SemiHamiltonian/Darboux/CurveCoordinates.lean)、[Analysis/TsarevCurve.lean](SemiHamiltonian/Analysis/TsarevCurve.lean) | 任意局部光滑数据沿非退化曲线延拓为实际光滑 Darboux 解与交换速度。 |
| [Analysis/TransportUniqueness.lean](SemiHamiltonian/Analysis/TransportUniqueness.lean)、[HodographTransport.lean](SemiHamiltonian/Analysis/HodographTransport.lean) | 齐次线性输运系统的局部零初值唯一性，以及 hodograph 残差的实际传播方程。 |
| [Analysis/HodographConverse.lean](SemiHamiltonian/Analysis/HodographConverse.lean) | 任意基点非退化的实际 C∞ PDE 解局部具有 hodograph 表示，并且状态 Jacobian 可逆。 |

代数部分的两个双向判据是：

```lean
S.IsSemiHamiltonian ↔ S.FormallyCompatible
S.IsSemiHamiltonian ↔ ∀ r a b c, PSS.DiagonalTensor.P D S.speed r a b c = 0
```

它们没有断言任意相容微分代数内都存在足够多的解。任意微分代数并不具备相应的局部存在性质。

## 实际光滑系统的局部可积性

设 `U ⊆ (ι → ℝ)` 是开集，`ι` 有限，`v : ι → Smooth.Functions U` 是实际 C∞ 函数。`Smooth.StrictlyHyperbolic v` 要求每一点的实特征速度两两不同。`Smooth.ofSpeeds hU v hv` 自动构造 Tsarev 系数，函数相等表示在 `U` 上逐点相等。普通函数可通过 `Smooth.ofContDiffOn` 转入该代数。

在 `SemiHamiltonian.Smooth` 命名空间中，主要结论为：

```lean
semiHamiltonian_iff_locallyAxisSolvable hU S :
  S.IsSemiHamiltonian ↔ LocallyAxisSolvable hU S

semiHamiltonian_iff_locallyRich hU S :
  S.IsSemiHamiltonian ↔ LocallyRich hU S

locallyAxisSolvable_iff_P_zero hU S :
  LocallyAxisSolvable hU S ↔
    ∀ r a b c, PSS.DiagonalTensor.P (coordinateDerivations hU) S.speed r a b c = 0
```

`LocallyAxisSolvable` 的量词顺序是：对每个基点 `p ∈ U`，存在正半径 `r`，使 `B(p,r) ⊆ U`，对任意 `φᵢ : ℝ → ℝ` 光滑初值，都有实际光滑函数 `wᵢ` 满足

```math
\partial_j w^i=\Gamma_{ij}(w^j-w^i),\qquad i\ne j,
\qquad w^i(p+s e_i)=\varphi_i(s).
```

半径在初值之前选定，且适用于全部微分阶数。这里使用上确界范数，因此球就是开坐标立方体。此谓词要求存在性；Darboux 模块中带闭立方体 C¹ 延拓的解另有存在唯一性定理。

`LocallyRich` 只要求同一局部邻域内的交换流能在基点取得任意指定值；定理证明这已足以推出半哈密顿性，继而推出更强的任意轴上初值可解。必要性使用真实混合偏导的交换，充分性使用已经证明的 C∞ Darboux 存在定理。`tsarev_iff_locallyAxisSolvable` 将半哈密顿性写成通常的
`∂ₖ(∂ⱼvⁱ/(vʲ−vⁱ)) = ∂ⱼ(∂ₖvⁱ/(vᵏ−vⁱ))` 条件。

`isCommutingSpeed_iff_pointwiseBracket` 将这些解与实际导数写出的流交换条件联系起来，`commuting_speeds_pairwise_pointwise` 证明它们彼此交换。

`Checks/LocalIntegrabilityExample.lean` 从实际速度 `vⁱ(x)=x⁰+x¹+x²+i` 出发，在任意开集上检查严格双曲性、非零 Tsarev 耦合系数、三指标半哈密顿条件、任意光滑轴上初值可解和 PSS 判据。

## Darboux 局部存在唯一性

新模块处理实有限维空间中的系统

```math
\partial_j w^i=\Gamma_{ij}(w^j-w^i),\qquad i\ne j,
\qquad w^i(s e_i)=\varphi_i(s).
```

相容条件 `IsDarbouxCompatible` 是对互异指标成立的

```math
\partial_k\Gamma_{ij}
=\Gamma_{ij}\Gamma_{jk}+\Gamma_{ik}\Gamma_{kj}-\Gamma_{ij}\Gamma_{ik}.
```

这里的导数是 mathlib 的实际 Fréchet 导数。`ScalarJet` 仅记录连续函数和缩放后的一阶连续导数；`IsCubeJet` 用 `HasFDerivAt` 断言二者的关系。这不是无穷 jet 空间，也没有将“可解”放入相容性定义。

主要入口：

- `existsUnique_C1_darboux_axisData`：在满足压缩估计的小立方体上，直接接受 `φ ψ : ι → C(ℝ, ℝ)`，其中 `ψᵢ` 是 `φᵢ` 在相关区间的导数。结论是 `∃! u : Values r, IsC1DarbouxSolution r Γ ... u`，唯一性针对实际函数值。
- `local_existsUnique_C1_darboux`：从任意正半径立方体上的相容系数出发，构造更小的**正半径**，统一适用于所有上述初值。
- `local_existsUnique_smooth_darboux`：系数在原立方体内部 C∞ 时，对任意 `φ : ι → C(ℝ, ℝ)` 及 `∀ i, ContDiff ℝ ∞ (φ i)`，得到唯一的 `IsSmoothDarbouxSolution`；半径同时独立于初值和微分阶数。
- `local_existsUnique_smooth_darboux_of_functions`：便利接口，接受全空间上的普通光滑函数 `γ i j`，相容性只要求在给定闭立方体上成立。自动构造 `smoothCoefficientJets`，无须手填导数。仅局部光滑的系数可使用前一接口。
- `classicalSolution_unique`：任意满足原 PDE 的经典解，只要有相同轴上初值，就在足够小的立方体上相同；唯一性本身不需要相容条件。

证明先用径向积分算子构造不动点。同时迭代函数及导数，并由一致极限求导定理证明可微性。随后通过链式法则、微积分基本定理及相容条件，证明微分余项满足齐次积分方程，最后用压缩估计推出余项为零。因此已证明的存在性确实是 **PDE 的存在性**，并非仅有连续积分方程解。

C∞ 正则性采用参数法。在固定单位立方体上令 `zₓ(y) = w(x₁y₁,…,xₙyₙ)`，则它满足 `zₓ = Aₓ + Tₓ zₓ`。缩放后的系数是 `xⱼ Γᵢⱼ(xy)`，初值是 `φᵢ(xᵢyᵢ)`。`CompactSmooth` 证明这些是连续函数空间中的光滑映射；`SmoothLinear` 用 `‖Tₓ‖ < 1` 和算子求逆的光滑性证明 `(1 − Tₓ)⁻¹ Aₓ` 光滑。最后在 `y=(1,…,1)` 取值得到原解的 C∞ 正则性。整个过程只使用零阶算子的压缩估计，无须逐阶缩小半径。`integralFixedPoint_contDiff` 的正则性结论本身不要求相容性；相容性用于之前将积分方程解确认为 PDE 解的步骤。

| 模块 | 作用 |
| --- | --- |
| `IntegralEquation`、`Uniqueness`、`Local` | 连续积分方程、经典解唯一性、正半径选择。 |
| `C1FixedPoint`、`JetAlgebra`、`C1Operator` | 导数图的闭性、乘法/复合/积分保持导数、C¹ 不动点构造。 |
| `JetCalculus`、`Homotopy`、`Residual`、`Interior` | 径向 FTC、微分余项恒等式、余项范数估计、连续延拓。 |
| `Existence`、`ValueUniqueness`、`AxisData`、`LocalC1` | 原 PDE 解、实际解的唯一性、任意单变量初值、局部定理。 |
| `CompactSmooth`、`SmoothLinear`、`Scaling` | 紧参数函数族的高阶微分、线性不动点的光滑参数依赖、坐标缩放恒等式。 |
| `SmoothExistence`、`SmoothData` | C∞ 正则性提升、光滑局部存在唯一性、普通系数函数接口。 |

光滑 Darboux 版本在坐标立方体内部断言 `ContDiffOn ℝ ∞`，函数及一阶导数连续延伸到闭立方体；没有额外断言所有高阶导数都连续延伸到边界。唯一性针对实际函数值。`Analysis/TsarevLocal.lean` 已通过平移和开集限制将它连接到任意基点附近的 Tsarev 系统。`Checks/DarbouxExample.lean` 检验 C¹ 初值接口；`Checks/SmoothDarbouxExample.lean` 检验非恒定系数的二维双向耦合系统，以及显式验证三指标相容性的三维系统。主定理的公理依赖纳入 `Checks/Axioms.lean`。

## 一般矩阵场的 Haantjes 局部坐标化

设 `U ⊆ (ι → ℝ)` 为开集，`ι` 为任意有限指标集，`A` 为实际 C∞ 矩阵场。`Geometry.StrictHyperbolicAt A p` 只要求在点 `p` 有一组实特征基与互异实特征值，不包含光滑特征标架、第一积分或坐标存在性假设。

`Geometry.haantjes_local_diagonalization` 从 `p ∈ U`、`StrictHyperbolicAt A p` 和 `Smooth.MatrixHaantjesVanish A U` 构造 `OpenPartialHomeomorph` 型的坐标 `e`，其源集包含 `p` 且包含于 `U`，满足：

```text
e 和 e.symm 在各自的固定开定义域上 C∞；
speed i 在 e.source 上 C∞，各速度逐点互异；
D e(q) (A(q) z) i = speed i(q) * D e(q) z i。
```

因此在新坐标 `r=e(q)` 中，矩阵对角元为 `speed i(e.symm r)`。反向定理 `matrixHaantjesVanish_of_diagonalization` 不需要互异特征值。若 `U` 上逐点严格双曲，`haantjes_iff_locally_diagonalizable` 给出：

```lean
Smooth.MatrixHaantjesVanish A U ↔ Geometry.LocallyDiagonalizable A U
```

证明链如下：先用隐函数定理选择简单特征对，并在共同邻域保持标架可逆与谱隙非零；然后将实际 Haantjes 张量的特征标架分解连接到补特征分布的对合性。对每个余维一分布，选定横向方向、化为平坦图分布，构造第一积分，最后用逆函数定理把独立第一积分拼成坐标。

这里的 Frobenius 存在性也已证明：在连续路径的 Banach 空间中用光滑隐函数定理解径向积分方程；求参数变分后，横向 PDE 余项满足齐次线性 ODE，由唯一性得余项为零。所有阶数共用同一开邻域，没有把 `ContDiffAt ℝ ∞` 误当作固定邻域上的 C∞。反向通过坐标雅可比的逆构造交换标架，并利用二阶导数对称性证明其括号为零。

`Checks/HaantjesExample.lean` 用非恒定、非对角的三维矩阵 `[[1,0,0],[x₀,2,0],[0,0,3]]` 检验逐点张量公式、严格双曲谱及完整局部坐标接口；另以 `[[1,0,0],[0,2,0],[0,-x₀,3]]` 验证非零 Haantjes 障碍：原点处 `H(e₀,e₁)` 的第三分量为 `4`，因而不能局部光滑对角化。

## 一般坐标下的 PSS 判据

`Smooth.pssTensor hU A` 的类型是三个逐次的 `Functions U` 线性映射，作用在实际光滑向量场上。定义使用真实 Lie 括号，依次形成 `N`、`K=3{N,A²}`、`M`、`Q`、`P`。`K` 的张量性证明明确消去了所有对输入函数求导的项，而不是把张量性列作假设。

在 `Geometry` 命名空间中，`pss_iff_locallyAxisIntegrable hU hM hs` 的结论为：

```lean
(Smooth.MatrixHaantjesVanish M U ∧
  Smooth.PSSVanish hU (Smooth.Endomorphism.ofField M hM)) ↔
  LocallyAxisIntegrable M U
```

这里 `hs` 要求 `U` 上逐点严格双曲，`hM` 要求 C∞。`LocallyAxisIntegrable` 对每个基点要求存在真正的 C∞ 局部坐标及光滑逆、目标域上的对角系统 `S`，并要求雅可比实际将 `M` 化为 `S.speed`，且 `S` 满足前述 `LocallyAxisSolvable`。坐标在结论中构造；“任意初值可解”仍指实际光滑 PDE 解。

`LocallyAxisIntegrable.exists_symmetries` 进一步将坐标限制到所选目标立方体，构造原变量中的光滑算子 `B`，证明其与 `M` 满足 PSS 的代数交换与极化括号方程。坐标、立方体和原变量中的邻域都在任意初值之前选定。`hydrodynamicSymmetry_conjugate_iff` 也提供一般交换算子的双向搬运。

`Checks/PSSExample.lean` 使用实际 C∞ 系数检验 `(f,f+1,f+2)`：`f=x₀+x₁+x₂` 时 `P=0`；`f=x₁x₂` 时原点的 `P⁰₀₁₂=8`，因此严格双曲性不够。两个系统同时经非线性剪切 `r₁=x₁+x₀²` 共轭，验证零/非零判据及交换算子搬运。

## 原变量中的可积性与半哈密顿性的等价

`Geometry.LocallyRichMatrix hM` 完全不提特征标架或 Riemann 坐标。它要求对每个 `p ∈ U`，存在共同开邻域 `V ⊆ U`，使每个满足 `M(p) T = T M(p)` 的实线性算子 `T`，都可由 `V` 上的实际光滑交换算子 `B` 实现，即 `B(p)=T`。这里的交换指 `Smooth.IsHydrodynamicSymmetry`：算子代数交换，且实际 Lie 括号构成的 PSS 极化方程恒为零。`V` 在 `T` 之前选定。

`Geometry.LocallySemiHamiltonian M U` 则要求局部存在真正的光滑 Riemann 坐标与光滑逆，坐标雅可比将 `M` 化为对角系统 `S`，且 `S.IsSemiHamiltonian`。对于 `U` 上逐点简单实谱的 C∞ 矩阵场，主定理为：

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

必要性先由简单实谱选取局部光滑特征标架。任意实际交换算子在该标架中必定对角；任意对角值可由基点中心化子值指定。将它们代入 PSS (2.9) 得到三重不同指标的结构系数在该点为零，故 `H=0`。已证明的 Haantjes 局部坐标化给出 Riemann 坐标。局部丰富性在实际坐标变化下保持，随后由真实混合偏导相容性推出半哈密顿条件。充分性沿相反方向，用光滑 Darboux 解实现任意对角值，再搬回原变量。

`Checks/PSSExample.lean` 验证完整定理的正例、`P≠0` 对原变量丰富性的阻碍，以及非线性坐标变换后仍有丰富交换流。`Checks/HaantjesExample.lean` 另证明上述扭转矩阵处处具有互异实特征值，但 `H≠0`，因而不可能具有该丰富性。这同时检验了必要性中不能预设 Riemann 坐标的步骤。

## 交换流的函数芽分类

`Analysis/SymmetryClassification.lean` 使用 `Filter.Germ (𝓝 p)` 表示允许缩小邻域的实际函数芽。`CommutingSpeedGerm hU S p` 的代表必须在基点的某个开邻域上 C∞，并满足实际 Tsarev PDE。`ScalarGerm 0` 表示光滑单变量函数芽；虽然其定义选用全局光滑代表，`exists_global_smooth_germ` 已用光滑截断证明任意局部光滑函数芽都有这样的代表，因而不限制初值。

对于半哈密顿系统，`commutingSpeedGermEquiv` 给出真正的双射：

```text
交换速度函数芽 ≃ (ι → ScalarGerm 0)
w ↦ (s ↦ wⁱ(p + s eᵢ)) 的函数芽。
```

满射性来自 C∞ Darboux 存在性；单射性来自新证明的 `Darboux.germ_unique`，适用于不同邻域上的任意解，不要求它们使用同一边界延拓。`localCommutingSpeeds_pairwise` 证明任意两个这样的局部流彼此交换。

`Geometry/SymmetryClassification.lean` 进一步定义实际光滑算子的 `HydrodynamicSymmetryGerm`。`symmetry_eq_diagonal` 由原系统的互异特征值推出每个交换算子必定对角，`hydrodynamicSymmetryGermEquiv` 因而将**所有**水动力型交换算子芽与上述 n 个函数芽建立双射。交换算子本身可以有重复特征值。此分类接口在选定的 Riemann 坐标中表述；已有的 `hydrodynamicSymmetry_conjugate_iff` 负责实际坐标共轭。

## 守恒密度与公共通量

约定守恒律为 `∂ₜ h(u) = ∂ₓ q(u)`，相应方程是：

```text
∂ᵢq = vⁱ ∂ᵢh，
∂ⱼaᵢ = Γᵢⱼ aᵢ + Γⱼᵢ aⱼ，aᵢ = ∂ᵢh，i ≠ j。
```

`Conservation.lean` 证明梯度系统的形式相容性与半哈密顿性等价，并证明梯度解 `a` 与 `v*a` 都是闭一形式。对于任意交换速度 `w`，`w*a` 也闭合。

这里的解析证明使用扩展后的 Darboux 方程 `∂ⱼaᵢ = Aᵢⱼ aᵢ + Bᵢⱼ aⱼ`，两个系数独立。`Darboux/PairIntegral`、`PairC1`、`PairResidual`、`PairExistence`、`PairValueUniqueness`、`PairSmooth`、`PairLocal`、`PairOpen` 依次证明积分方程、真实 C¹ 导数、微分余项消失、唯一性及同一邻域上的 C∞ 正则性。`Pair.local_existsUnique_smooth_darboux` 的正半径在所有轴初值之前选定。`PairUniqueness` 另给出任意局部解的函数芽唯一性。

`Analysis/ConservationLocal.lean` 将其连接到实际半哈密顿系统，证明：

```lean
semiHamiltonian_iff_locallyDensityAxisSolvable hU S :
  S.IsSemiHamiltonian ↔ LocallyDensityAxisSolvable hU S
```

`Geometry.exists_local_potential` 从已经证明的径向 Frobenius 定理构造真实光滑势函数；`Analysis/Potential.lean` 将它连接到坐标一形式。`exists_local_common_flux` 因而构造每个交换流的实际局部通量，不只是证明通量方程形式闭合。

`Analysis/DensityClassification.lean` 的主接口为：

```lean
densityGermEquiv hU S p hS :
  DensityGerm hU S p ≃ (ℝ × (ι → ScalarGerm 0))
```

实数因子是独立的 `h(p)`，其余数据是各 `∂ᵢh` 在对应坐标轴上的函数芽。因此这分类的是实际密度，并非只有梯度。通量有另一个独立的加法常数；`flux_germ_unique` 证明固定该常数后通量芽唯一。梯度存在定理给出初值无关的共同半径；势函数与通量接口目前允许进一步缩小邻域，分类结论在函数芽层面表述。

`Geometry/ConservationCriterion.lean` 已补齐 PSS 定理 5 的独立必要性：对于简单实谱的实际 C∞ 矩阵场，丰富守恒律推出 Haantjes 消失，再构造 Riemann 坐标并推出半哈密顿性。主接口为 `LocallyRichConservationLaws.haantjesVanish`、`.locallySemiHamiltonian` 和 `.tensors_vanish`；最后一个同时给出 `H=0` 与 `P=0`。证明没有预设局部可对角化，也没有借用交换流丰富性作为假设。

这里“丰富”的精确定义是 `Geometry.LocallyRichConservationLaws`：每个点有一个共同开邻域，在其中实际 C∞ 密度和通量满足 `dq = dh ∘ M`，并能实现任意密度梯度，以及零梯度处任意对称、满足 `B(Mx,y)=B(x,My)` 的 Hessian。邻域在这些一阶、二阶数据之前选定。零梯度处 Hessian 是内在双线性张量。`PSS/ConservationNecessity.lean` 通过实际标架导子的交换子恒等式和三阶导数，消去三重不同指标的结构系数；`Geometry/ScalarCommutator.lean` 与 `ConservationJets.lean` 将计算连接到真实导数与守恒律。

`Geometry/ConservationJetSufficiency.lean` 已证明相反方向：在 Riemann 坐标中，以常数和一次轴初值构造有限组实际密度、通量，取它们邻域的有限交，再通过线性组合实现任意所需导数。这样保持了“共同邻域先于任意 jet 数据”的量词顺序。`ConservationJetTransport.lean` 用真实二阶链式法则证明临界 Hessian 的坐标变换公式，继而得到一般坐标下的双向定理。

`Smooth.MatrixDensityGerm M U p` 由原坐标中的实际 C∞ 密度芽组成，每个代表在某个开邻域上具有满足 `dq = dh ∘ M` 的实际 C∞ 通量。`Geometry/ConservationGerms.lean` 证明限制开集、光滑坐标变换以及与已有对角密度定义之间的真正双射。

`Geometry/ConservationClassification.lean` 的主结论是：

```lean
locallyRichConservationLaws_iff_originalParametrized hU hM hs :
  LocallyRichConservationLaws M U ↔ LocallyOriginalConservationParametrized M U

locallyRichConservationLaws_iff_locallySemiHamiltonian hU hM hs :
  LocallyRichConservationLaws M U ↔ LocallySemiHamiltonian M U

locallyRichConservationLaws_iff_tensors hU hM hs :
  LocallyRichConservationLaws M U ↔
    MatrixHaantjesVanish M U ∧ PSSVanish hU (Endomorphism.ofField M hM)
```

`LocallyOriginalConservationParametrized` 要求局部存在实际 Riemann 图，并且图内每个点处，指定的 `originalConservationData` 映射都是双射。该映射取 `h(p)`，以及 `h ∘ e⁻¹` 的各 `∂ᵢ` 分量在第 i 条坐标轴上的函数芽；定义不包含半哈密顿条件。`originalConservationGermEquiv` 将所有原变量密度芽与 `ℝ × (ι → ScalarGerm 0)` 建立等价，`originalConservationData_value`、`originalConservationData_axes` 明确核验其参数含义。模掉密度加法常数后，恰好剩下 n 个任意单变量光滑函数芽。分类在函数芽意义下成立，代表允许缩小邻域；共同邻域的有限 jet 丰富性则由上述有限组构造另行保证。

## 广义 hodograph 的实际局部解

`Analysis/Hodograph.lean` 使用与项目 PDE 一致的正号：

```text
wⁱ(u) = x + t vⁱ(u)。
```

`generalized_hodograph` 接受一个实际交换速度 `w`、满足该方程的基点 `(x₀,t₀,u₀)`，以及对状态变量 `u` 的 Jacobian 可逆条件。结论构造同一开邻域上的 C∞ 函数 `u(x,t)`，证明 hodograph 关系、原 PDE `uₜⁱ=vⁱ(u)uₓⁱ`、`uₓⁱ≠0`，并给出隐式方程在指定开邻域内的唯一性。

核心 `hodograph_solves` 直接微分实际函数。Tsarev 方程使 hodograph Jacobian 在解上所有非对角元为零；对 `x,t` 分别求导后得到原 PDE。半哈密顿条件用于之前产生任意函数芽的交换速度；给定交换速度之后，这一步直接使用其 PDE。

`Analysis/HodographConverse.lean` 的 `generalized_hodograph_converse` 已证明反向完备性：任意给定的 C∞ 解 `u(x,t)`，只要基点处每个 `uₓⁱ` 都非零，就能构造状态空间邻域上的实际 C∞ 交换速度 `w`，使同一个给定解在时空邻域内满足 `wⁱ(u)=x+t vⁱ(u)`。基点 `(x₀,t₀)` 任意；结论同时记录状态邻域、时空邻域及包含关系。`hodograph_stateJacobian_invertible` 进一步从该关系证明状态 Jacobian 可逆，因而能直接连接前述隐函数定理接口。

这一步新增的曲线 Darboux 定理允许在每个分量导数非零的曲线上指定任意局部 C∞ 数据。`Darboux/CurveProjection` 至 `CurveSmooth` 以对角线迹投影修改积分算子，证明真实 C¹ 解及同一邻域上的 C∞ 正则性；`CurveOpen` 证明相应唯一性；`CurveCoordinates` 用逐分量局部坐标变换处理一般曲线，并实际核验变换后系数的相容性。`Analysis/TsarevCurve.lean` 将它连接到交换速度，并通过光滑截断处理仅局部光滑的初始数据。

沿初始线构造 `w` 后，`Analysis/HodographTransport.lean` 证明残差 `Fᵢ=wⁱ(u)-x-tvⁱ(u)` 满足齐次线性输运系统。`Analysis/TransportUniqueness.lean` 在收缩梯形上对加权平方使用最大值论证，证明零初值迫使残差在双向时间邻域内为零。因此反向结论使用的是实际 PDE 解的传播唯一性，而非隐式方程的唯一性。

`Checks/ClassificationExample.lean` 检验二维耦合系统、任意正弦/指数轴函数芽、密度常数 `7`，以及只在基点附近光滑的初值代表。`Checks/PSSExample.lean` 还在三维非恒定耦合系统中检验密度分类，此时三指标相容条件非空；经非线性剪切变换后，检验原变量守恒律丰富性，以及具有常数 `7` 和指定正弦、指数数据的唯一原变量密度芽。PSS 与 Haantjes 的两个反例分别排除丰富守恒律，检验 `P≠0` 与 `H≠0` 两种独立障碍，并检查 `P≠0` 排除完整参数化。`Checks/HodographExample.lean` 以 Burgers 方程 `uₜ=u uₓ` 检验正向局部解构造；`Checks/HodographConverseExample.lean` 用两分量、互异常速度的非线性显式解检验反向表示，直接验证其 PDE 和基点非退化性。当前 `Checks/Axioms.lean` 包含 120 项主结论检查，依赖均仅为 `propext`、`Classical.choice`、`Quot.sound`。

## 数学模型与适用范围

底层是交换代数 `R` 上的交换导子 `D.deriv i`。`Analysis/SmoothFunctions.lean` 已将其实现为开集上的实际光滑函数及坐标偏导，并从二阶 Fréchet 导数的对称性证明导子交换。处处非零的速度差具有光滑倒数，因此逐点严格双曲性推出代数部分需要的 `IsUnit (vʲ − vⁱ)`。不能仅用两个函数作为环元素“不相等”来代替这一条件。

抽象代数中的 `PointwiseRich` 指每个点的任意值向量都能由某个实际解取得，用于必要性证明。光滑局部定理使用 `LocallyRich`，允许邻域随基点改变，并证明它与更强的 `LocallyAxisSolvable` 等价。`SeparatingEvaluations` 抽象了函数的逐点取值，允许由所有点上的等式推出函数等式。

`FrameData` 提供标架导子和反对称结构系数，用于计算。`Geometry/VectorFields`、`SmoothFrame` 已将其实现为欧氏开集上的实际光滑局部标架与 Lie 括号，`HaantjesLocal` 已由张量条件构造坐标。当前几何接口针对有限维欧氏开集，尚未封装为抽象光滑流形接口。`DiagonalTensor.P` 是分量构造，`Smooth.pssTensor` 是已证明与它一致的一般坐标内在张量。

## 本阶段以外的内容

无限 jet 代数、文献附录中的高阶消失/唯一性，以及添加 `(u^{i,1})⁻¹` 后的拟平凡性问题，暂未纳入本阶段。

## 文献

- S. P. Tsarev, *The geometry of Hamiltonian systems of hydrodynamic type. The generalized hodograph method*, Math. USSR-Izv. 37 (1991), 397–419；俄文原版 1990：[原文记录](https://www.mathnet.ru/php/archive.phtml?jrnid=im&option_lang=rus&paperid=1062&wshow=paper)。
- M. V. Pavlov, R. A. Sharipov, S. I. Svinolupov, *Invariant Integrability Criterion for the Equations of Hydrodynamical Type*：[arXiv:solv-int/9407003](https://arxiv.org/abs/solv-int/9407003)。公式编号按该文。

## 许可证

本项目以 MIT 许可证发布，见 [LICENSE](LICENSE)。
