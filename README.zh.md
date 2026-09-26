# Some Bounds Related to the 2-adic Littlewood Conjecture — 开放问题

本项目旨在完整回答 Dinis Vitorino、Ingrid Vukusic 的论文 [*Some Bounds Related to the 2-adic Littlewood Conjecture* 第 8 节](https://arxiv.org/html/2506.04110v2#S8)提出的全部开放问题，并用 Lean 形式化。**当前研究快照尚未达到这一目标。** 已有工作涉及 Problems 3、4、5、7，使用实际实数连分数及尾等价类。

**Problems 1、2、6 未解决；Problem 4 仍是部分回答。Problem 5 的界 11 和 Problem 7 的维数零结论仍分别依赖一个明确保留项。** 新增的 Problem 5 小规模证书已经内核验证，但没有完成界 11 所需的大计算。

| 问题 | 本版本的具体结论 | 状态 |
|---|---|---|
| 1、2、6 | 本次快照未提供解答。 | 后续工作。 |
| 3 | 成功尾类的本原二次判别式满足奇整数方程 `t² − Dv² = ±8`；二次性和 Serret 定理均在工程内证明。 | `VV.problem3_classification`，无保留。固定代表另需首项系数为奇数。 |
| 4 | 最小最终周期为 `ℓ` 的成功尾类有限，类数 ≤ `3 * ℓ * 4^ℓ`；周期 0、1、2 为空；周期 3、4 各恰有一个类，分别满足 `B=3`、`B=5`。每个周期都有共同的有限最终数字集。 | 上述结果无保留。一般精确类数和显式数值数字界尚未证明。 |
| 5，小实例 | 任意实无理数 `x` 的 `x,2x,4x` 中至少一个，部分商 ≥3 无穷多次。 | `VV.P5SmallCertificate.frequently_three_within_two`，无保留。这是证书方法验证，未改善论文的界 5。 |
| 5，较强条件结论 | 每个实无理数 `x` 有固定 `k≥0`，使 `2^k x` 的部分商 ≥11 无穷多次。 | `VV.P5FiniteCheck.problem5_bound_eleven`，仍依赖大规模有限检查。 |
| 7 | `VV.BExceptional` 的 Hausdorff 维数为零。 | `VV.problem7` 签名无外部参数，但依赖 EL 核心。 |

Problem 4 的共同最终数字集大小至多 `3 * ℓ² * 4^ℓ`；其最大值给出非计算的统一数字界，并非已求出的显式公式。周期 3 的完整分类见 `VV/P4PeriodThree.lean`。

周期 3 的唯一类由 `(3+√17)/2`、周期词 `[3,1,1]` 代表；周期 4 的唯一类由 `(5+√33)/2`、周期词 `[5,2,1,2]` 代表。共同最终数字集分别恰为 `{1,3}`、`{1,2,5}`。`VV/P4PeriodFourClassification.lean` 通过覆盖无界整数数字的 48 个符号分支证明周期 4 唯一性，不是枚举到某个数字截断值。

Problem 5 的小规模反向测试也已完成：8 条真实转移给出原始 `windowGraph 3 0` 的秩检查为假的内核证明；这不涉及 `C=10,r=14`。新增 `P5PrunedCertificate.lean` 将带下降证书的瞬态剪枝接回原始布尔义务，仍需提供实际的大证书数据。

仅保留两个 `sorry` 声明：

1. `VV.P5FiniteCheck.rank_check_10_14`：断言 `(VV.P5Window.windowGraph 10 14).checkEventuallyDeterministic = true`。尚未执行，也未独立确认其为真。原始图大小为 `10 * 2400 ^ 4782969`，这里只进行符号证明，没有展开大整数。其顶点编号使用非计算有限等价，原检查定义搜索整个秩函数，不能把“有限”当作“可以高效直接运行”。新增稀疏证书、压缩和剪枝接口证明了与原始图的联系，但尚无完成大检查的具体证书。
2. `VV.BBEKLowEntropyCore.rootAlternative_of_positive_entropy`：具有正熵、全分裂对角不变且遍历并满足约化闭轨道排除条件的概率测度，被某个非零实或二进根元素保持。缺口是叶条件熵、低熵剪切及异常分支排除。

本次还补了四种实际根叶族的原子／Dirac 二分、射影与精确平移稳定子相等，以及图域交叠处的局部条件测度不变性。`BBEKOneRootSupport.lean` 从实际条件核解积分出发，证明 ambient 测度满质量集合的支撑转移到四种根叶族。这些辅助结果尚未消除 EL 核心；局部叶不变性不能直接当成全局 ambient 测度不变性。

`BBEKOneRootSupportEscape.lean` 进一步补完四分支的条件矛盾：若 canonical 根叶族的平移稳定子几乎处处为整个根群，则与全对角不变、支撑在正 Mahler 紧集中的概率测度矛盾。此路线不要求先重构 ambient 根不变性；但从正熵条件获得所需叶对称性仍未完成。

根群生成、四分支 Mahler 逃逸、熵与盒维数转换及最终组装都在 EL 保留之外。`VV/BBEKFinal.lean` 内部构造 `VV.bbekTheorem42` 与 `VV.problem7`。最终 Problem 7 的原始公理输出为：

```text
[propext, sorryAx, Classical.choice, Quot.sound]
```

`VV/Audit.lean` 核对两项保留的准确类型，仅抽象证明体，再递归审计其余工程声明。允许的标准公理只有 `propext`、`Classical.choice`、`Quot.sound`。审计通过不表示两项保留已经证明。

## 复现与验证

工具链固定为 `leanprover/lean4:v4.20.1`，其[官方发行版](https://github.com/leanprover/lean4/releases/tag/v4.20.1)对应 commit `b02228b03f655c0cd051d82280ad5758359ec8ba`。官方文件名为 `lean-4.20.0-*`，编译器也显示 **Lean 4.20.0**；这是官方标签与版本显示的差异。Mathlib 固定在 `5c0c94b3f563ed756b48b9439788c53b0d56a897`。

```sh
lake build
lake env lean VV/Audit.lean
```

Windows PowerShell 7 可运行 `./Check-VV.ps1`，生成审计与源码哈希报告，并检查全部工程 Lean 源码进入导入闭包。普通构建不会执行庞大的 Problem 5 检查；小证书通过普通 `decide` 内核验证，没有使用 `native_decide`。

本次快照包含新的本地工程构建与递归审计，复用了版本及完整性经过核验的依赖缓存。数量、时间、源码哈希见 [verification/report.json](verification/report.json)，公理输出见 [verification/final-axioms.txt](verification/final-axioms.txt)。这不等于空缓存干净克隆、跨平台验证或独立数学审稿。

详细边界见 [PROOF_STATUS.md](PROOF_STATUS.md)，AI 辅助开发说明见 [AI_DISCLOSURE.md](AI_DISCLOSURE.md)。第三方源码保留 Apache-2.0 与作者署名；**原创贡献尚未指定项目级许可证**，见 [THIRD_PARTY.md](THIRD_PARTY.md)。仓库不包含私人聊天或工作档案。


## 2026-09-27：EL 形式化增量

本次补齐了实际叶稳定子的开集命中可测性、保留原半径的收缩复归二分、
几乎处处根逃逸，以及 Mahler 紧支撑下四种实际 canonical 根族的精确／
射影稳定子平凡性；另证明横截面条件熵与字面图册条件核的对应公式。
详见 [进展与剩余缺口](verification/EL-progress-20260927.md)。

**EL 核心仍未完成，两个指定的 sorry 均保留。** 正 KS 熵到根熵贡献的连接、
低熵联合返回和异常轨道分支仍缺证明。按“先完成 EL，再限时尝试有限计算”
的顺序，本次没有启动有限计算尝试，也没有执行庞大枚举。
