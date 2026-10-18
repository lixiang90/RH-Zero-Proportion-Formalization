# 窗口势函数的独立静态审查与现有计数接口

本审查只读源码、合同和已冻结证据说明，作符号推导；没有构图、遍历 H/B、运行 DFS/SCC、提取 FS、计算点/矩阵/核、搜索 q、优化或运行 Lean。结论为固定模型的充分条件和下一必要关逻辑，不声称该模型可行。

绑定：

- 固定 s1R 原源 `research-goal-20261018-record-source-audit/snapshot/Solution.lean`，1,818,411 B，SHA256 `f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf`；下列源码行号均指此文件。
- 宏观004 `research-goal-20261016/macro-reviews/004-20261018.zh.md`，审查时 SHA256 `b36cf3d32cae2a232dea169f7c90af5948d93f38040b4c3577bcc5793e848fea`。I Phase1 先行；本审查没有改主线或治理。
- 审查时 `CONTRACT.zh.md` SHA256 `93acb123fe2de132024d2a764e1a612f3dc60f63a5e7373c5014cf471ff4adbb`。此哈希仅识别所读版本；root 可另加接口，本文件与独立小清单只冻结本审查。

## 1. 固定量、实际标签与方向

写 `K=kappa*SA>0`，`eta=c-c9=tau-c=d/K`，`d=kappa*(Nc-N9)`。必要前提明确是 `0<=c9<=c`，故 `0<=eta<=c`；所有核接近误差 `delta>=0`。

原每个闭例外 cell 的真实单窗结论是 `F9>=c9+Mi/K`，用原精确 Mi，不能替换为 Nat floor 或仅状态示意。每个 cell 设 id/rev 两标签并共用 Mi。对真实按物理从左到右滑动的窗口序列，若 `F9>=tau` 选 star，否则用 B 的完整 sublevel 覆盖及原 Ordered/反射选择 cell 标签；边界可选任一有效标签。有限经典选择足够，不需可计算地评价真实 F9。

对原 index `q=((i*1187+j)*4+chart)`，chart 固定为 `[id/id,id/rev,rev/id,rev/rev]`，边方向应为

```
source = 2*i + chart//2,
target = 2*j + chart%2.
```

第一位是前窗的局部反射，第二位是后窗的局部反射。局部 rev 改变 cell/Ordered 的坐标映射，不会反转物理向右的窗口转移。不能把某个 rev chart 的边反向，不能把标签图无向化，也不能把 id/rev 预合并。

真实低能转移不可能落入 G/H 的严格 Empty 证书范围；其余允许边必须包含所有 paid 对及所有 star 转移。保守未解边不宣称几何非空。相邻边各自可行也不保证三窗以上同时可实现；这不影响下面模型的充分性，但限制模型失败的含义。

## 2. (P) 与 Phi：符号、star 及相消

要求每条允许有向边 `a->b` 满足

```
q_b-q_a <= M_a+M_b-2d.                 (P)
Phi(a)=(q_a-M_a+2d)/(2K).
```

则

```
Phi(b)-Phi(a)
 = (q_b-q_a-M_b+M_a)/(2K)
 <= (M_a-d)/K
 = c9+M_a/K-c
 <= F9(window_a)-c.
```

最后一步是对边起点窗口收费，不能误写为后窗能量。沿真实向右窗口序列相加，内部 Phi 相消，符号一致。

取 `M_star=2d,q_star=0`，则 `Phi(star)=0`，形式下界为 `c9+2d/K=tau`。双向 star 边分别给 `q_a<=M_a`、`-q_a<=M_a`，即 `|q_a|<=M_a`。把 star 放到长度 L 的真实窗口序列两端，沿 `star,a0,...,a(L-1),star` 的 L+1 条代数边求和：

```
0 <= (tau-c)+sum_r(F9(window_r)-c),
sum_r F9(window_r) >= L*c-eta.
```

虚拟 star 只用于受约束整数的代数闭链，并不声称它可几何实现或是一额外实际窗口。完整模型强加了全部 star 边，因而此闭合合法；若将来删任何 star 边，就不能直接沿用这个端点损失结论。

固定模型若成功，亏损能量可在长序列摊销，不要求每对窗口平均都达到 c。因此一个实际两窗的 affine 低点不自动否定它。

## 3. 15378 条全负边的必要停止门

这里只静态核查逻辑，不运行图。H 残余来自 G underpaid 分支，其固定边权为 `w_ab=Mi+Mj-2d<0`。若有有向环，逐边 (P) 相加得到

```
0 = sum_cycle(q_b-q_a) <= sum_cycle w_ab < 0,
```

直接否定这个固定 scalar graph-potential 模型。一个环的独审只需逐边核原 H membership、原 index/chart 对应顶点、原 B 精确 Mi 及严格负总和；不需 FS、真实核、q 或 LP。环不必是真实多窗同时可实现，故它不会否定真实累计能量、细化状态或非线性余项路线。

对这些全负边，完整 canonical DFS 给 DAG 只通过必要关；所有 paid 边与 star 边仍可能形成负的混合环或其他不相容约束。不能据 DAG 宣称完整图无负环或存在 q。最终成功仍须给具体整数 q 及所有允许边的完整 (P) 核验。

## 4. 真正需要修改的源码求和处

原 `block_energy_band` 在 5316--5357。其 5330--5345 通过逐窗 `hCert` 得到 `(m-8)c<=sum_windows F9`；这是新累计假设应替换的准确位置。5338--5345 的逐项求和不能直接引用原接口来证明累计下界。

对于 17/20 分离的 m 个排序点，若 m>=9，新标签链给

```
(m-8)c-eta <= sum_{i=0}^{m-9} F9(window_i).
```

实际 band 容量、pair 总和及 pressure 身份在 5346--5357，可保持同一个 W9。`window_pairs_le_band`、`W9.Adm` 和 `pressure_le_n`（16542--16565）无需增加压力预算。分离只用于选择标签和累计能量，不改变容量。

随后 `band_close_n`（16465 起）用 n=9 的邻域宽度 8，误差是 `32*delta*m`；`remainder_bound_n` 在 16586--16592 合并 band、pressure、offdiag/defect。新的分离版 remainder 可得到

```
(c-32*delta)*m - W9.B*R - 8*c - eta <= defect.
```

m<9 时用 `defect>=0`、`m<=8`、`c>=0`、`eta>=0`、`W9.B*R>=0`、`delta>=0` 单独处理，不可套不存在的窗口。

原 16569/16604 的 `hCert` 是所有非负 gap 的 pointwise floor，势函数合同只给分离累计结论，故不能直接填这些参数。应另做分离累计版 band/remainder/submatrix 桥，并把 matching 中已有的 hsep 传进去。

## 5. matching 的唯一 None 余项块

原 matching 在 16644--16662 构造最大近对匹配；`S none` 是唯一可能含任意多点的余项块，16657--16660 已给其 17/20 分离，所以可用新累计版 remainder。`some pair` 块仍用 16682--16690 的 close-pair bound，须保留原 `0<=c`、`c<=1/64` 和 `delta>=0`，它们不使用新窗口势函数。

额外 `eta` 只能向这个唯一 None 块收费。16701--16711 的 `hcharge` 本来就把常数边界向 None 收费一次；不是每个匹配 pair 都支付 eta。空 None 仍由非负 defect 处理即可。这里没有新空间分块的数量假设；若未来改变分块方式，需重新核总边界费。

## 6. n=10 仅作现有 ActualDefectEstimate 的误差/端点接口

在 `0<=c9<=c` 下，`0<=eta=c-c9<=c`。因此对 `m>=0,delta>=0` 有

```
(c-36*delta)*m-W9.B*R-9*c
 <= (c-32*delta)*m-W9.B*R-8*c-eta.
```

这允许保守放宽匹配后的实际估计为

```
(c-36*delta)*m-B*R-9*c <= Dcirc.
```

它恰好符合源 16720--16724 的 `ActualDefectEstimate Z 10 c B`。该类型的 n 只决定误差系数 `4*(n-1)` 及有限端点损失 `(n-1)c`，不含 WCert，也不要求 W10。真实 band、权重、容量和 pressure 始终是 W9；不能把此接口技巧说成构造了 W10。

可于是复用 `defect_to_dyadic`（16725--16804），取其误差/端点参数 n=10。其 16755 与 16780--16782 用 `N(T,2T)->infinity` 吸收一次性的 `9c`。无需把 eta 偷塞进原 n=9 的更强 `ActualDefectEstimate`。

源 16813--16860 的 `actual_defect_estimate/actual_dyadic/actual_cumulative` 外层又要求同 n 的 pointwise WCert，不能不改参数就调用；应由新实际估计直接接 `defect_to_dyadic`，再接 16859--16860 的 `Zeta23.cumulative_of_dyadic`。这是保留既有极限证明的短接口路径，尚未 Lean 实现或测时。

## 7. 交付范围

这条静态桥只说明如果完整整数 (P) 证书存在，计数接口有可复用路径；未证明任何新累计 floor 或零点比例。2375 个 q、大整数解码、全部允许边检查、原状态选择/反射覆盖、累计 band/matching 桥及最终两个陈述，均须计入原 181,589 B 余量与总运行预算。完整源、规定公理、Comparator/Lean/nanoda、GitHub 与提交材料义务均未完成。当前仍只准备必要图门，I Phase1 及其独审先行，未有本审查方图执行。

## 8. 准备中的 canonical DFS 源码只读审查

审查版本 `research-goal-20261018-window-potential-cycle/cycle_once.py` SHA256 `4184a9dca7db7b1a40226e3287258c02100c26e53f69b6d436e24e5eaf67cfd9`；只读，未 AST、导入、启动或构图。若准备源码之后改变，此版本审查不能自动覆盖变化。

- 输入先绑定 B/H 生产与独立清单，读取全部 1187 精确原 margin 和全部 15378 H indices。长度、唯一性、升序、全 index 范围、所有 margin 区间及每边严格负权均显式检查后才进入 DFS。index→四 chart 及上述源/目标映射一致。
- root 顶点 0..2373 升序，adjacency 按完整升序 index 输入，迭代 DFS 依次推进 offset，故首个 gray backedge 的含义固定。gray target 是当前 stack 祖先；沿 parent 向祖先收集、reverse 后追加 backedge，方向正确。自环时 parent 路径为空也成立。结果另核 cycle 首尾、每源顶点唯一、长度至多 2374 和严格负总和。
- 无 backedge 时输出完整 2374 顶点拓扑序，另核每条已加载边的严格拓扑 rank。其解释保留“只是 underpaid 子图必要门”，不宣称完整模型可行或存在 q。
- gate 要求 I 独审 receipt `passed=true` 及固定 manifest/input hashes。launcher 与 child 都使用 exclusive 输出，记录一次 child，父进程执行 60 秒/8 MB 限制、超限终止，不含自动重试/新 family。失败不会产生数学成功结果。实际执行后仍须独立核 terminal 的真实 exit、elapsed、最终 closed output bytes 及 pins；单个 `result.passed` 不替代资源与完整性审查。

在此所读版本未见 vertex 方向或 DFS 环重建错误。当前没有执行授权；此静态审查不等于结果验证。
