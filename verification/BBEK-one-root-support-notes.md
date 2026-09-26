> 后续进展（18:53 UTC）：本文最后一节的 hit 可测性缺口已在三个新模块中严格证明，任意半径的实/2-adic 指定收缩时间 bot/top 接口也已编译。详见 [可测性与递归二分说明](BBEK-leaf-stabilizer-measurable-notes.md)。本文保留先前阶段记录；熵识别和低熵 shearing 仍未完成。

# 实际 canonical 根叶的支撑转移与紧支撑逃逸

2026-09-26 本轮有界增量；不更改现有 EL 核心和 P5 有限计算保留项。

## 新增已编译模块

- `VV/BBEKOneRootSupport.lean`：实际 canonical 条件叶族的支撑转移。
- `VV/BBEKOneRootSupportEscape.lean`：全平移稳定子与 Mahler 紧支撑不相容。

两个模块均零 sorry、零新增公理。传递公理审计分别保存在同目录 `BBEKOneRootSupportAxioms.log`、`BBEKOneRootSupportEscapeAxioms.log`，只含 `propext`、`Classical.choice`、`Quot.sound`。

## 支撑转移的准确范围

`canonical_real_lower_supported` 的输入为概率 μ、可测 K、μ(K)=1、r>0，以及实际 `IsConstructedRootFamily realSplit μ t r η`。结论为

```lean
∀ᵐ q ∂μ, ∀ᵐ u ∂η q, x u 0 • q ∈ K
```

`canonical_padic_lower_supported` 对应 `padicSplit` 与 `x 0 u`。两个 upper 端点使用实际 `IsConstructedUpperRootFamily`，对应 `upperPoint u 0` 和 `upperPoint 0 u`。支撑转移本身不需要 K 紧或闭，也不需要 μ 的对角不变性、叶稳定子条件、熵条件。

证明明确经过以下已定义对象，而非抽象未证明兼容参数：

1. `coordinateMeasureOf μ c` 经 `quotientCoordinates` 推回后恰为 `μ.restrict c.image`。
2. 将 `Measure.disintegrate` 和 `ae_compProd_iff` 应用于字面的条件核。
3. 用 `realMatrix_leaf_add` / `padicMatrix_leaf_add` 将 centeredKernel 的坐标差变成真实 quotient 根群作用。
4. 对可数张 expanded/selected charts 同时取 conull 集，再利用 canonical 每个 growingBall 的限制等式与球的穷尽性。
5. 上根用实际 W 反射；保留根参数负号，不增设条件核假设。

## 无需 ambient 重构的紧支撑矛盾

`closed_conull_eq_univ` 证明：η 的每个中心球都有正质量，且 `translationStabilizer η = ⊤`，则任何 η-conull 的闭集都是整个根参数空间。理由是平移对称将中心球正质量传到任意中心，闭集补集的开球不能有零质量。

`orbit_subset_of_supported` 因而把 AE 叶支撑升级为整根轨道包含在闭 K 中。

四个最终端点位于 `VV.BBEKOneRootSupportEscape`：

```text
no_real_lower_top
no_padic_lower_top
no_real_upper_top
no_padic_upper_top
```

每个端点的输入只有：

- μ 是实际 quotient X 的概率、对完整分裂对角群 A 不变；
- δ>0 且 μ(K δ)=1；
- 对应实际 canonical family η（r>0）；
- μ-AE q，η_q 的每个中心球有正质量；
- μ-AE q，真正的 translationStabilizer(η_q)=⊤。

结论为 False。没有 ambient 根群不变性输入，也没有遍历性或正熵输入。

关键步骤是在对角 d 的 K 原像上再次使用同一 canonical 族的支撑转移。该原像闭、且由 A 不变性有质量 1，于是几乎处处每条根轨道经 d 后仍在 K。已证的显式 root/diagonal escape 为 K 中每个点提供一个开逃逸邻域；紧性选出有限多个这样的邻域。每个邻域为 μ-null，有限并却覆盖满质量 K，矛盾。这避免了不合法地将无限全叶测度的平移稳定性直接套到有限图册条件概率。

## 仍未完成的主理论

本增量没有从正 KS 熵推出非平凡或全根叶稳定子，也没有完成条件熵到 canonical 叶族的识别或低熵 shearing。`BBEKLowEntropyCore.rootAlternative_of_positive_entropy` 仍是项目保留的理论 sorry；原子二分不等于非平凡稳定子，非原子也不直接蕴含平移不变性。

新端点减少了该专门紧支撑应用所需的后续测度重构：一旦真实 canonical 任一根族的稳定子为 top 几乎处处，即可直接推出矛盾，无需再证明整个 ambient μ 的根群不变性。既有 projective=exact 的 Poincare 结果也可先将 projective top 转成 exact top。该缺口缩小不应被描述为 EL 核心已经消除。

### 非零叶稳定子到 top：已经证明的接口与尚需实例化的条件

这一步不能仅用“基点随对角作用时稳定子协变”冒充“同一基点稳定子在所有缩放下固定”。项目有更准确的递归/遍历接口：

- `VV/BBEKRealStabilizerField.lean` 的 `ae_real_subgroup_bot_or_top`：有限不变测度、闭加法子群场、开集 hit 事件可测，以及一个真正收缩的对角映射下的 AE 协变，推出 AE 为 bot 或 top。
- `VV/BBEKPadicStabilizerField.lean` 的 `ae_padic_subgroup_bot_or_top`：对应 Q₂ 闭子群场的真实收缩递归结论。两个文件的 `ae_*_translationStabilizer_bot_or_top` 是叶测度版本，但既有包装采用单位球归一化；实际 canonical 族的归一化半径是 r，应用时必须显式处理该差别或调用一般子群场版本。
- `VV/BBEKStabilizerErgodic.lean` 的 `ae_eq_top_of_ergodic_of_pos`：可测非平凡事件、对完整 A 的 AE 子群协变、A 遍历性、上述 bot/top 二分，以及非平凡事件有正测度，推出 AE top。它是已经证明的通用接口；本轮没有将全部条件进一步实例化到 canonical 四根族。
- `VV/BBEKOneRootRecurrence.lean` 的四个 `exists_*_exact_stabilizer_data` 已在实际 canonical 四根族上证明 projective stabilizer = exact translation stabilizer，保留同一实际图册构造。它不证明非平凡事件正测度。

`VV/BBEKRootSubgroups.lean` 的 `additive_eq_top_of_square_stable` 也确已证明，但它要求同一个子群在所有非零平方缩放下稳定。不能仅凭随基点变化的协变直接套用。

因此主剩余工作准确分为：正 KS 熵与正确 canonical 一维根叶的非原子性/正贡献识别；低熵 shearing 产生正测度非零 projective 稳定子；将实际 canonical 场的 hit 事件、完整 A 协变与递归二分连接到上述遍历接口。上述三段完成后，本轮四个 `no_*_top` 已足够在紧支撑应用中结束矛盾，通用 ambient 根群不变性的局部到全局拼接不再是该专门路线所必需。

### 最后一次有界接口核查（17:46 UTC）

继续核对后确认，当前不能直接把指定时间下的递归二分实例化到实际 η，缺少的是开集 hit 可测性，并非半径 r 或收缩常数。整个 VV 源码中，`BBEKCompactZeroHit.measurableSet_exists_zero_on_open` 只有声明，还没有实际叶平移稳定子的调用实例。

需要的最小辅助定理可表述为：对 U=ℝ 或 Q₂、可测族 θ:Z→Measure U，若每个 θ_z 都局部有限且 Radon，则

```lean
∀ O : Set U, IsOpen O →
  MeasurableSet {z | ∃ u ∈ translationStabilizer (θ z), u ∈ O}
```

这里应先用已有 `BBEKRadonModification.exists_everywhere_good_ae_eq` 在一个可测零集上将实际族修改为 everywhere Radon 的 θ，最终将 AE 二分转回字面 canonical η；不能忽略原族仅 AE 满足 Radon 条件的区别。上述最小辅助定理仍需构造决定局部有限 Radon 测度的可数紧支撑连续积分测试，证明测试关于 z 可测、关于平移 u 连续，再应用已证 CompactZeroHit。当前尚无此完整测试桥，把 `Measurable η` 直接当成 hit 可测性会漏证明。

根据本轮“不新建 Fell 可测性框架”的有界要求，本次只核实并记录该缺口，未新加声明、假设或草稿。已冻结的五个模块及其成功编译结果不变。

