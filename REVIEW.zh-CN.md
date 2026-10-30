# 形式化审查报告

[English](REVIEW.md) | 中文

- **审查对象**：提交 `b0e140b`（Lean `v4.35.0`，mathlib `v4.35.0`）
- **审查日期**：2026-10-30
- **审查者**：Claude Code（`claude-opus-5-5`）
- **审查内容**：
  1. 公理依赖；
  2. Lean 定义是否与论文一致；
  3. 主要定理的 Lean 表述是否与论文一致。
- **对照文献**：
  - Pavlov–Sharipov–Svinolupov 论文（以下简称 PSS，[arXiv:solv-int/9407003](https://arxiv.org/abs/solv-int/9407003)）的 TeX 源文件，逐个公式对照。
  - Tsarev 1990 年的原文未能获得。Tsarev 部分对照的是 PSS 引用的 (1.4)，以及这些结果的标准表述。

## 结论

- 未发现数学错误，也未发现与论文不一致的定义。
- 所有声明都只依赖 Lean 的三个标准公理。
- PSS 的定理 2 和定理 4 没有形式化，Lean 直接用它们的结论作为定义。这两条属于标准内容。
- 另有几处范围上的收窄，见第 4 节。

## 1. 公理依赖

**只用了 Lean 的三个标准公理：`propext`、`Classical.choice`、`Quot.sound`。**

- **全量扫描。** 用附录中的脚本遍历了项目的全部 1888 个声明，其中定理 1511 个、定义 359 个，逐个收集公理依赖。
  - 没有一个声明依赖上述三条以外的公理。
  - 项目中没有 `axiom`、`opaque` 或 `unsafe` 声明。
- **`Checks/Axioms.lean`。** 这里列出的 120 个主要定理都只依赖上述三条，与 README 的说法一致。
- **模块系统下检查是否可靠。** 项目使用 Lean 的模块系统。导入方默认只看到被导入模块的公开接口。
  - 查阅 Lean 4.35 的 `Lean/Util/CollectAxioms.lean` 后确认：每个模块写出 `.olean` 时，会用包含全部证明体的环境，预先计算每个声明的公理依赖，并随模块导出。
  - 因此跨模块的 `#print axioms` 能看到证明内部，证明里的 `sorry` 不会被漏掉。
- **源码扫描。** 没有发现以下写法：
  - `sorry`、`admit`
  - `native_decide`、`implemented_by`、`@[extern]`
  - `debug.skipKernelTC`
  - 自定义的宏或记号
- **构建与检查。**
  - `lake build` 成功，共 2996 个任务，0 个错误。
  - `Checks/` 下的 9 个文件全部通过，只有 linter 提示。

## 2. 定义对照

| PSS / Tsarev | Lean | 结论 |
|---|---|---|
| (1.4) 半哈密顿条件 | [`IsSemiHamiltonian`](SemiHamiltonian/Basic.lean)、`Smooth.tsarevCoefficient`、`ofSpeeds_semiHamiltonian_iff` | 一致，只有指标改名 |
| (2.8) 标架括号与结构系数 | [`FrameData.bracket`](SemiHamiltonian/PSS/Eigenframe.lean)，`structureCoeff r i j` 对应 `c^r_{ij}` | 一致 |
| (4.1) Nijenhuis 张量、(4.2) Haantjes 张量 | `FrameData.nijenhuis`、`FrameData.haantjes`、`TensorRecipe.N` | 一致 |
| (4.4) Nijenhuis 张量的分量公式 | [`matrixNijenhuis`](SemiHamiltonian/Geometry/MatrixTorsion.lean) | 逐项一致 |
| (4.3) Haantjes 张量的特征标架分解 | `FrameData.haantjes_basis` | 一致 |
| (2.5) 极化形式、(2.9) | `polarizedSymmetry`、`PSS.polarized`、`SymmetryValuesAdmissible` | 一致，符号也一致 |
| (4.6)、(4.9)、(4.12)、(4.15)、(4.18) | [`TensorRecipe.FN / K / M / Q / P`](SemiHamiltonian/PSS/TensorRecipe.lean) | 逐项一致，系数 4、−2、−2 也一致 |
| (4.7) α | [`PSS.alpha`](SemiHamiltonian/PSS/Polynomial.lean) | 一致 |
| (2.17) 守恒律存在通量 | [`IsMatrixConservationLaw`](SemiHamiltonian/Geometry/ConservationJets.lean#L23)：dq = dh∘M | 一致 |
| Tsarev 交换流方程 ∂ⱼwⁱ = Γᵢⱼ(wʲ−wⁱ) | `DiagonalSystem.IsCommutingSpeed` | 一致 |
| Tsarev 守恒密度方程 ∂ⱼ∂ᵢh = Γᵢⱼ∂ᵢh + Γⱼᵢ∂ⱼh | `IsDensityGradient`、`IsDensity` | 一致 |
| Tsarev hodograph 公式 wⁱ(u) = x + t·vⁱ(u) | `HodographRelation` | 一致，符号与论文的 uₜ = A·uₓ 相同 |

补充核实：

- **光滑性。** `ContDiffOn ℝ ∞` 中的 `∞` 是经强制转换的 `(⊤ : ℕ∞)`，即 C∞。全项目没有用 `⊤` 或 `ω` 表示的解析条件。
- **导数和括号。**
  - 导数都是真实的 Fréchet 导数。
  - `fieldBracket` 已证明等于 Mathlib 的 `VectorField.lieBracket`。
  - `Smooth.Functions U` 是开集 U 上真正的 C∞ 函数构成的代数。
- **对角公式经过核对。** `DiagonalTensor` 中手工推导的对角坐标公式（如 `Kcycle`），已由 [`DiagonalRecipe.P_basis`](SemiHamiltonian/PSS/DiagonalRecipe.lean#L122) 证明等于按论文字面构造的内在张量 P 在坐标基上的取值。

## 3. 定理表述对照

| PSS / Tsarev | Lean 主定理 |
|---|---|
| 定理 1、3：对称丰富 ⇔ 可对角化且半哈密顿 | `Geometry.locallyRichMatrix_iff_locallySemiHamiltonian` |
| 定理 5：守恒律丰富 ⇔ 可对角化且半哈密顿 | `Geometry.locallyRichConservationLaws_iff_locallySemiHamiltonian` |
| 定理 8：H = 0 ⇔ 可用点变换对角化 | `Geometry.haantjes_iff_locally_diagonalizable` |
| 定理 9：P = 0 ⇔ 半哈密顿 | `Geometry.pss_iff_locallyAxisIntegrable`、`Geometry.locallyRichMatrix_iff_tensors`；对角坐标下为 `DiagonalTensor.semiHamiltonian_iff_P_zero` |
| (4.8)：α = 0 ⇔ 半哈密顿 | `PSS.semiHamiltonian_iff_alpha_zero`（由 `alpha_eq` 证明，不是假设） |
| (4.19)，包括重复指标 | [`DiagonalTensor.P_eq`](SemiHamiltonian/PSS/DiagonalTensor.lean#L117) |
| Tsarev：半哈密顿 ⇔ 交换流依赖 n 个单变量任意函数 | `Smooth.semiHamiltonian_iff_locallyAxisSolvable`、`Smooth.tsarev_iff_locallyAxisSolvable` |
| Tsarev 的 hodograph 方法 | `Smooth.generalized_hodograph`；反向完备性 `Smooth.generalized_hodograph_converse` 是论文以外的补充 |

补充核实：

- **没有隐藏的额外假设。**
  - 打印了上述定理在内核中的完整签名。几何层主定理的假设只有三条：U 是开集、M 在 U 上 C∞、M 在 U 上逐点严格双曲。
  - 源码中有 16 处 `include`，都没有给主定理增加额外假设。
- **定理不是空洞的。** 检查文件对每个关键谓词都给出了正例和反例：
  - `Checks/PSSExample.lean` 中，H = 0 但 P ≠ 0 的系统被证明不丰富、不可积。
  - `Checks/HaantjesExample.lean` 中，H ≠ 0 的系统同样被证明不丰富、不可积。
  - 两个文件里还有正例，以及经过非线性坐标变换后的正例。
- **函数芽分类有实际内容。** `commutingSpeedGermEquiv`、`densityGermEquiv`、`originalConservationGermEquiv` 都是对自然映射（取各坐标轴上的函数芽）应用 `Equiv.ofBijective` 得到的。它们不是"基数相等就存在双射"那种空洞结论。
- **必要性没有预设坐标。** `LocallyRichMatrix` 与 `LocallyRichConservationLaws` 的定义中不含特征标架或 Riemann 坐标。坐标是由 Haantjes 条件推出来的。

## 4. 差异与注意事项

按重要性排序。

1. **PSS 定理 2 没有被证明，它的结论被直接当作定义。**
   - PSS 定义 1 说"水动力对称"是两个 PDE 流相容。(2.4)+(2.5) 是定理 2 推出的等价刻画。
   - Lean 直接用 (2.4)+(2.5) 定义 [`Smooth.IsHydrodynamicSymmetry`](SemiHamiltonian/Geometry/SymmetryTransport.lean#L16)。
   - 有两处注释陈述了没有证明的事实：
     - [InvariantSymmetry.lean:11](SemiHamiltonian/PSS/InvariantSymmetry.lean#L11) 说"这就是两个流交换的条件"。
     - [Basic.lean:72](SemiHamiltonian/Basic.lean#L72) 说 `flowBracketCoeff` 是流交换子中 uₓⁱuₓʲ 的系数。
   - 对角情形下，这个定义等价于 Tsarev 的标准交换条件。
   - 这属于标准内容，经确认不计划形式化。
2. **PSS 定理 4 没有被形式化。**
   - 守恒律直接用"存在通量 dq = dh∘M"来定义。
   - 论文的 (2.14)–(2.16)（泛函守恒 ⇔ 存在通量）和不变形式 (2.18) 都没有出现在代码中。
   - 这属于标准内容，经确认不计划形式化。
3. **只覆盖实特征值。** [`StrictHyperbolicAt`](SemiHamiltonian/Geometry/SmoothEigenframe.lean#L36) 要求特征值是实的且两两不同。论文的"一般位置"只要求互异，所以复特征值的情形不在 Lean 结论的范围内。
4. **"依赖 n 个单变量任意函数"的形式化方式是自选的。** 论文中这一说法是非形式的。Lean 给出了四种版本：
   - 基点值任意可取：`LocallyRichMatrix`
   - 一、二阶 jet 任意可取：`LocallyRichConservationLaws`
   - Riemann 坐标轴上任意给定初值：`LocallyAxisSolvable`
   - 函数芽双射

   必要性方向使用最弱的版本，所以结论比论文的陈述更强。

   需要注意，[`LocallyOriginalConservationParametrized`](SemiHamiltonian/Geometry/ConservationClassification.lean#L206) 的定义本身就要求存在 Riemann 坐标。真正不预设坐标的守恒律必要性，由 jet 版本给出。
5. **没有形式化 Frölicher–Nijenhuis 括号的一般理论**，即论文第 3 节和定理 6、7。
   - K 是直接按 (4.6) 的展开式定义的。
   - Lean 证明了按此定义的 K、M、Q、P 都是 C∞-线性的张量（`PSS/Tensoriality.lean`），并且在 C∞ 坐标变换下协变（`Geometry/ChartTransport.lean`）。
   - 这为 (4.6) 没有笔误提供了独立旁证。
6. **以下内容不在范围内：**
   - Tsarev 论文中关于哈密顿结构的部分，即 Dubrovin–Novikov 括号与平坦度量；
   - README"本阶段以外的内容"一节列出的无限 jet 代数、高阶消失与唯一性、拟平凡性。
7. **论文自身有两处笔误，形式化没有受影响。**
   - (2.16) 中的 ∂ⱼ(∂ₖAᵏᵢ) 漏了 f，应为 ∂ⱼ(∂ₖf·Aᵏᵢ)。
   - (2.23) 前一句的 "(2.12) should be trivial" 应为 (2.21)。
8. **维护方面。**
   - 构建时有 7 处使用已弃用名字的警告，例如 `continuousOn_finset_sum`。升级 mathlib 时这些地方会报错。
   - 另有约 100 条 linter 提示，主要是未使用的 section 变量和 simp 参数。

## 5. 审查方法与局限

- **未逐行阅读证明。** 1.5 万行证明的正确性由 Lean 内核保证。审查集中在内核无法保证的部分：定义是否忠实于论文、主定理的表述与假设、定理是否空洞。
- **中间引理未逐一核对。** Darboux 模块等中间引理的表述没有逐一对照论文，因为它们只服务于最终定理的证明。不过已核对：`local_existsUnique_smooth_darboux_of_functions` 中的相容条件 ∂ₖΓᵢⱼ = ΓᵢⱼΓⱼₖ + ΓᵢₖΓₖⱼ − ΓᵢⱼΓᵢₖ，与交换流方程混合偏导相容的直接计算一致。
- **Tsarev 部分的对照有局限。** 未能获得 Tsarev 原文，这部分只对照了 PSS 的引用和标准表述。

## 附录：全量公理扫描脚本

把下面的内容存为项目目录以外的任意 `.lean` 文件，在项目根目录下运行 `lake env lean <文件路径>`（需要先执行 `lake build`）。

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

在 `b0e140b` 上的输出：

```text
declarations scanned: 1888
unsafe declarations: []
axiom usage: [(Quot.sound, 1750), (Classical.choice, 1622), (propext, 1819)]
non-standard axioms: 0 []
```
