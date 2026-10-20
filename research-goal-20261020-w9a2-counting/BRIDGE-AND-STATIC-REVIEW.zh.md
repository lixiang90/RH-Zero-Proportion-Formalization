# W9A2 有限势求和至实际零点计数：源码准备与静审

本包只完成源码准备和静态核对，未运行 Lean、Comparator、export 或 nanoda。
`Counting.lean` 与 `Final.lean` 同时逐字镜像到
`StructuralW9A220261020/`；`static-check.json` 记录字节与 SHA。
不能据此宣称新的无条件比例已经验证。原宏观007与主代理的轮次计数保持不动。

## 精确单位与候选

固定 `SA=10^20`，原 W9A2 实际全域基线为
`c0=893029029923108825/SA`。冻结图的顶点成本 `cost(v)` 是原整数
checker 的 cN 单位，不是物理能量。整数潜势 `p(v)` 的共同分母为5，
逐边证书方向必须是

```
622387738726 + p(v) - p(u) <= 5*cost(u).
```

因此物理增量是 `increment=622387738726/(5*SA)`，物理势是
`P(v)=p(v)/(5*SA)`。最大 p 是 `2504722000690`，最小是0，故只需边界
`C=2504722000690/(5*SA)`。这不是重复把 potential 分母5付款，也不是
把 good threshold `10^12` 误当成平均增量。

得到 `c=c0+increment=4465145772003282851/500000000000000000000`。
本源 H 与 B 逐字取自官方 W9A2：H 的分子为
`6721237468782417141365717707344332375586`、分母为 `10^40`，
`B=454741897490/10^14`。实际计数输出候选为

```
(H-B)/(1-c) =
3337881639516708570682858853672166187793 /
4955348542279967171490000000000000000000.
```

`static_check.py` 只用 Python 标准库 Fraction 核对此恒等式、严格超过冻结
2026-10-19 W9A2 纪录、`0<=C<=c<=1/64`。它没有重新求图最优解、核函数、
LP 或几何；不能替代实际定位或 Lean 检查。届时网站若再更新，最终 strict
improvement 必须对新鲜可信 spec 重核，不能只引用本地冻结 baseline。

## 实际定位是必需依赖

`Counting.summed_of_state` 的全部数学前提显式列出，最终
`Final.actual_summed` 必须由以下两项实际定理消除它们：

1. `Localization.located_state` 对任意真实 `g : Fin 8 -> R`，只要求
   每个 gap 至少 `17/20`，给一个 `v : Fin 49`，同时证明
   `Graph.StateAt g v` 与 `c0+cost(v)/SA <= Fw RiemannFail.W9 g`。
   必须包含原 walk 的全部分支、全部根、根外、反射及闭边界；它不能只是
   `StateAt -> floor`，更不能只列原数值叶。这部分由 localization 代理负责。
2. `Graph.edge_from_locations` 对真实十点的两个共享八-gap窗口证明
   `StateAt left u -> StateAt right v -> Edge u v`，由全部排除对的共享
   span 严格矛盾给出，不能从“图列过这些边”推出实际转移。这部分由图代理负责。

`Final.lean` 直接引用上述两项，没有把它们加到最终零点比例定理的参数中。
源码结构消除了抽象前提不等于它们已经经核验证：二者仍待本次冻结编译关。

## 有限求和与端点

对任意 m 个排序、两两分离点，真实九点窗口数为 `N=m-8`。证明先从
两两分离与严格排序取得所有合法 gap 的 `>=17/20`，再对每个 `i<N`
用 `located_state` 的存在证明选择 `s_i`。范围外统一置 good 状态 G。

每个内部相邻对通过真实十点窗口转移取得图边；最后一个窗口通过
`all_to_good` 接 G。它只使用最后窗口的源成本，不假设存在第 N 个真实窗口，
也不丢掉最后一个成本。零长度的通用求和引理单独由空和化简成立。

于是每个有效 i 有

```
Fw_i >= c0 + cost(s_i)/SA
     >= c0 + increment + P(s_(i+1)) - P(s_i).
```

有限和精确 telescoping 后为 `sum Fw_i >= N*c+P(s_N)-P(s_0)`；
由 `P(s_N)>=0` 与 `P(s_0)<=C` 得 `sum Fw_i >= N*c-C`。
代码中的一般势引理不依赖图是无环，也不需要实际无限序列、周期点、
任何概率分布或极小值存在。

## 与实际 ζ 桥的接口

`section Payment` 至 `actual_defect_estimate_effective` 全段与已接受 v3
开发中的 `StructuralS1RTiny20261018/Production/Counting.lean` 逐字相同，
静审段 SHA 为
`421c93f7c9c2fc679547017a1a19043855725efa026722fe073aada433af83e0`。
它导入本次 W9A2 Core，因此其中 `wfun/kfun/Fw`、实际 AM 零点配置、
同算子 retained Gram、pressure 与分离谱均属于当前核。没有导入旧 s1R Core、
其导数表、数值叶或旧 H。

这条一般桥先把全窗和转为 band+pressure 下界；最大匹配中的 close pairs
仍支付当前源码证明的 `1/64`，只有唯一分离 remainder 支付一次 C。
`C<=c` 允许把 harmless defect index 从9增加至10，吸收有限边界；
误差项也相应从8邻域保守增为9邻域，不能声称仍使用原 n=9 的误差式。

`Counting.actual_dyadic_of_summed` 用 W9A2 的 H 与同一实际
`OpethN.Counting.defect_to_dyadic` 接 `Zeta23.Ncount/N0star`；
cumulative 通过原实际 `cumulative_of_dyadic`。最终两个结论都只有
epsilon/T0/T 与实际根计数函数，不留下 RH、局部 floor、图模型或矩阵假设。

## 尚未通过的验收

本包 `compiler_runs=0`，静审只检查算术、文本来源和证明路线。
全部新源码的语法/elaboration、各最终根的传递公理只标准三项
`propext/Quot.sound/Classical.choice`、完整导出、Comparator 与独立 nanoda、
最终单文件字节及生产总时限仍须通过根代理的后续冻结关。
最终源码还须与 GitHub 和可提交材料逐字同步。旧已接受源及其收据不覆盖
本次新增图、定位、求和或最终候选。
