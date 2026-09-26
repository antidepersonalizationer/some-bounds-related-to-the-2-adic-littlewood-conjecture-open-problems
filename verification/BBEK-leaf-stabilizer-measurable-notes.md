# 实际叶稳定子 hit 可测性与单一收缩时间下的二分

2026-09-26 新增三模块，均已逐文件通过 Lean 编译，无新增 sorry 或 axiom：

- `VV/BBEKLeafMeasureTests.lean`
- `VV/BBEKLeafStabilizerMeasurable.lean`
- `VV/BBEKLeafStabilizerDichotomy.lean`

这三个模块完成了先前支撑说明中明确列出的 hit 可测性缺口。它们没有证明正熵产生非零稳定子，没有修改 `BBEKLowEntropyCore.rootAlternative_of_positive_entropy`。

## 可数真实积分测试

`SupportedTest n` 是紧开拓扑中支撑包含于 `closedBall 0 n` 的连续实值函数子空间。由第二可数局部紧域上的连续函数空间第二可数性，该子空间存在可数稠密序列。将 n 与序列索引配对得到字面 `testFunction : ℕ → C(U,ℝ)`。

`ext_of_test_integrals` 证明此族决定任意局部有限 Radon 测度，包括总质量无限的测度。证明分两层：共同紧支撑使积分在函数的紧开拓扑下连续，因此可数稠密测试推广到所有紧支撑连续测试；Urysohn 函数、紧集内正则性与开集外正则性再推出测度相等。没有把“决定测试族”当成外部假设。

`continuous_integral_translate` 证明紧支撑测试平移后的积分关于根参数连续：在任一点的紧邻域上，所有平移测试共同支撑于两个紧集的差集，套已有连续参数积分定理。`measurable_integral_family` 则从测度族本身可测得到每个固定测试的积分可测，不要求总质量有限。

## 实际稳定子事件可测

`mem_stabilizer_iff_tests` 将

```lean
u ∈ translationStabilizer (η z)
```

严格等价于所有 `testDifference η j z u = 0`。这里差值为平移测试积分与原测试积分之差。

`measurableSet_stabilizer_hit` 因而实际实例化已有 `BBEKCompactZeroHit.measurableSet_exists_zero_on_open`，输出

```lean
∀ O : Set U, IsOpen O →
  MeasurableSet {z | ∃ u ∈ translationStabilizer (η z), u ∈ O}
```

输入只有可测族 η、每点 η_z 是 Radon 测度，以及 U 的 proper normed additive group 与第二可数 Borel 结构。没有假设 Fell 可测性、稳定子 hit 可测性或目标等价式。

## 保留原族与原半径的收缩二分

最终端点位于 `VV.BBEKLeafStabilizerDichotomy`：

```lean
ae_real_stabilizer_bot_or_top
ae_padic_stabilizer_bot_or_top
```

实根输入是有限测度 μ、保测 T、可测 η:Z→Measure ℝ、AE η_z.Regular、AE η_z(ball 0 r)=1、0<a<1，以及

```lean
∀ᵐ q ∂μ, ∃ d : ℝ≥0,
  η (T q) = d • (η q).map (a * ·)
```

结论为原族的精确稳定子几乎处处是 bot 或 top。Q_p 版本将实收缩条件改为 a≠0 与 ‖a‖<1。输入不再含任何 hit 可测性参数；r 是实际族的任意归一化半径，不要求 r=1。归一化只用于推出协变倍数 d≠0。

原族仅 AE Radon，因此证明内使用已有零集可测包络构造 θ，使 θ 处处 Radon 且 θ=η AE。实际 hit 定理用于 θ，原归一化与保测性确保稳定子协变传到 θ，已有实/2-adic 收缩子群递归给出二分，最后通过 θ=η AE 将结论传回字面的原 η。结论没有替换为一个失去 canonical 关联的任意族。

## 审计与界限

`verification/BBEKLeafStabilizerMeasurableAxioms.lean` 对14个关键端点逐一打印传递公理；日志为同名 `.log`。新增源码仍保留 Lean 的少量 unused-section-variable 提示；无编译错误，提示不影响声明或审计。

与已证的 actual canonical 支撑转移、root/diagonal 逃逸结合，单一时间的收缩二分即可排除 top 并得到 AE bot，无需全 A 的叶族协变或遍历提升。这不消除剩余 EL 核心：从正 KS 熵识别正确 canonical 根叶的非原子性/正贡献，以及低熵 shearing 产生非零 projective translation stabilizer，仍需独立证明。
