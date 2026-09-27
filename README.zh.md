# Vitorino–Vukusic：2-adic Littlewood 猜想论文开放问题

研究对象是 Vitorino–Vukusic 的 [*Some Bounds Related to the 2-adic Littlewood Conjecture* 第 8 节](https://arxiv.org/html/2506.04110v2#S8)。目标是完整回答全部开放问题，**目前尚未完成**。

- Problem 3：已形式化尾等价类的二次方程判据，无未证输入。
- Problem 4：已证明各周期下有限性、统一计数上界和有限的最终数字集；周期 3、4 各恰有一类。一般精确计数和显式数值数字界尚未完成。
- Problem 5：小证书已核验；界 11 的理论归约保留，但指定的大规模有限检查尚未核验。
- Problem 7：内部构造无外部参数的 `VV.bbekTheorem42` 和 `VV.problem7`，仍依赖下述未证理论输入。
- Problem 1、2、6：本工程尚未解决。

## 本次缩短路线

主工程只保留现有问题成果及缩短后的证明路线。对 Problem 7，已证明的归约从“受困参数集不是零上盒维”产生一个全对角不变、遍历、正熵且在 `K δ` 上质量为 1 的概率测度。剩余输入正是“任意 `δ > 0` 下不存在这样的测度”。排除它之后，零上盒维、BBEK Theorem 4.2 和最终 Problem 7 的归约全部已写出。

**这次是调整未证输入的边界，不是消掉 EL，也不是获得无 `sorryAx` 的 Problem 7。** 主工程恰有两个未证证明体：

1. `VV.P5FiniteCheck.rank_check_10_14`：指定的有限计算。
2. `VV.BBEKCompactEntropyCore.no_positive_entropy_supported_K`：紧支撑正熵测度不存在命题。

原先不再被主工程导入的 180 个模块，已独立整理到 [S-arithmetic dynamics 理论基础库](https://github.com/antidepersonalizationer/s-arithmetic-dynamics-lean)。该库的已证基础入口不导入任何未证声明；可选研究入口保留原先更一般的 EL 根不变性目标。共享依赖作有来源记录的快照，两库分别构建。

“主工程不导入”不等于“未来补 EL 时用不到”。叶测度和回返工具仍可能用于补齐当前缺口。没有删除旧成果，也不声称已经形式化完整的 EL、Ratner–Tomanov 或某本教材。

详见 [证明状态](PROOF_STATUS.md)、[分库说明](docs/SPLIT.md)、[模块清单](docs/MODULES.md)、[构建说明](BUILD.md) 和 [实际验证报告](verification/report.json)。原有第三方归属和许可证保留；原创建设尚未指定统一的项目许可证。
