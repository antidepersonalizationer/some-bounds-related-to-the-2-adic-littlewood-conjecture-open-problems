# Some Bounds Related to the 2-adic Littlewood Conjecture — 开放问题

本项目旨在完整回答 Dinis Vitorino、Ingrid Vukusic 的论文 [*Some Bounds Related to the 2-adic Littlewood Conjecture* 第 8 节](https://arxiv.org/html/2506.04110v2#S8)提出的全部开放问题，并用 Lean 形式化。**当前初始快照尚未达到这一目标。** 已有工作涉及 Problems 3、4、5、7，对象使用实际实数连分数及尾等价类。

**本次发布未解决 Problems 1、2、6；Problem 4 仅完成下述有限性与上界，不能称为完整回答。工程另保留两个 `sorry`：Problem 5 的有限检查尚未执行或独立核验，Problem 7 依赖一个 EL 低熵理论核心。**

| 问题 | 本版本的具体结论 | 状态 |
|---|---|---|
| 1、2、6 | 本次快照未提供解答。 | 项目后续工作。 |
| 3 | 成功尾类的本原二次判别式满足奇整数方程 `t² − Dv² = ±8`；二次性和 Serret 定理均在工程内证明。 | `VV.problem3_classification`，无保留。固定代表另需二次方程首项系数为奇数。 |
| 4 | 部分回答：最小最终周期为 `ℓ` 的成功尾类有限，类数 ≤ `3 * ℓ * 4^ℓ`；周期 0、1、2 时为空。 | `VV.Problem4.problem4_all_periods` 的此项结论无保留。一般精确类数和候选最大部分商公式尚未证明。 |
| 5 | 每个实无理数 `x` 均有某个固定 `k ≥ 0`，使 `2^k x` 的部分商 ≥ 11 无穷多次。 | `VV.P5FiniteCheck.problem5_bound_eleven`，依赖下述有限检查。 |
| 7 | `VV.BExceptional` 的 Hausdorff 维数为零。 | `VV.problem7` 签名无外部参数，但证明依赖下述 EL 核心。 |

仅保留的两个声明是：

1. `VV.P5FiniteCheck.rank_check_10_14`：断言 `(VV.P5Window.windowGraph 10 14).checkEventuallyDeterministic = true`。该明确有限图检查尚未执行，也未独立确认其为真；没有附带原计算证书，未核验与此前描述的剪枝／合并实现等价。
2. `VV.BBEKLowEntropyCore.rootAlternative_of_positive_entropy`：全分裂对角不变且遍历、具有正熵并满足约化闭轨道排除条件的概率测度，受到某个非零实或二进根元素保持。保留部分是叶条件测度熵、低熵剪切及异常分支排除，属于理论缺口。

根群生成、四分支 Mahler 逃逸、熵与盒维数转换及最终组装都在第二项之外。`VV/BBEKFinal.lean` 内部构造 `VV.bbekTheorem42`，再给出最终 `VV.problem7`。

最终 Problem 7 的既有原始公理输出是：

```text
[propext, sorryAx, Classical.choice, Quot.sound]
```

`VV/Audit.lean` 核对两项保留的准确类型，仅抽象其证明体，再对其余工程声明进行递归审计；允许的标准公理只有 `propext`、`Classical.choice`、`Quot.sound`。审计通过不表示这两项保留已经证明。

## 复现

固定工具链是 `leanprover/lean4:v4.20.1`，其[官方发行版](https://github.com/leanprover/lean4/releases/tag/v4.20.1)对应 commit `b02228b03f655c0cd051d82280ad5758359ec8ba`。官方发行文件名称为 `lean-4.20.0-*`，既有验证使用的编译器也显示 **Lean 4.20.0**；这是官方发行标签和版本显示的差异，并非本机自造别名。Mathlib 固定在 `5c0c94b3f563ed756b48b9439788c53b0d56a897`。

在匹配编译器与锁定依赖可用时，从仓库根目录运行：

```sh
lake build
lake env lean VV/Audit.lean
```

Windows PowerShell 7 可运行 `./Check-VV.ps1`，额外生成公理审计和源码哈希报告。普通构建不会运行 Problem 5 的庞大有限检查。本次整理发布文档没有进行新的干净克隆或跨平台构建，既有验证记录应按其原始范围理解。

详细边界见 [PROOF_STATUS.md](PROOF_STATUS.md)，AI 辅助开发说明见 [AI_DISCLOSURE.md](AI_DISCLOSURE.md)。第三方源码保留 Apache-2.0 与原作者署名；**原创贡献尚未指定项目级许可证**，详见 [THIRD_PARTY.md](THIRD_PARTY.md)。仓库不包含私人聊天记录或链接。
