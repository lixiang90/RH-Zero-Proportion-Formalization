# prefix/suffix 两窗口例外不相容：独立静态充分性审查

2026-10-17。此项只读旧 Core 与已有静态审查，不解码或检查任何
叶，不评价核，不枚举例外 cell 对，不运行求解器、Lean 或覆盖搜索。
不改旧证书、已有包或主轮计数。admissibility、score 与完整源码
预算由另一个审查负责；本文只核数学例外分类和其完整性接口。

## 精确的充分命题

令 F9 为旧核、旧 W9 ledger 的实际八 gap 能量。Core:13250–13256
的 cert_AM 给出所有非负八 gap 的

`F9(h)>=c9=859538525913875481/10^20`。

令 s=123/128，D=[s,infinity)^8，R(h)_r=h_(7-r)。对九 gap g 定义
L(g)=(g0,...,g7)、T(g)=(g1,...,g8)。固定组合的实际能量是

`A(g)=(F9(L(g))+F9(T(g)))/2`。

固定 c=8611/1000000，并令

`tau=2c-c9=862661474086124519/10^20`。

若 A(g)<c，因 L(g)、T(g) 都在 D，已有 floor 分别强迫
`F9(L(g))<tau` 和 `F9(T(g))<tau`。这是严格不等式；不需要
g、L(g) 或 T(g) 是任何目标函数的极小点，也不需要 KKT。

因此以下两个前提足以证明所有 g>=s 都有 A(g)>=c：

1. **完整 sublevel 外包**：给一个有限有理集合 E，使所有 h∈D
   且 F9(h)<tau 的点都属于 E。E 可以包括大量实际能量较高的点，
   但不能漏掉任意真实 sublevel 点。
2. **完整相邻不相容**：不存在 g>=s 同时满足 L(g)∈E、T(g)∈E。

推理是普通反证法，不涉及“两个窗口的极小值必须同时达到”的
未证断言。这里没有证明这两个前提成立。

## 从旧完整树提取 E 所需的覆盖性质

旧 PCell.Pg（Core:9281）是
`cN<=Fg OR h7<h0`；不是无条件的能量 floor。专用 Covered 和
mcheckP、mleafP、walk 绑定原 cN（10555、10572、10906–11038）。
低层 mcheckGX 的 threshold 参数可以复用，但高层不能只替换常数
就当作已经得到新分类定理。

可先在有序半域 O={h∈D:h0<=h7} 分类。对每个原 numerical leaf，
用其原见证和**原实际 cell**检查是否足以证明 F9>=tau。已证成功
的整个 cell 可删除；其余 numerical leaf 的 cell 必须全部留在
例外并集 E0 中，或者用包含它们的可证明外包替代。检查失败只
表示这条见证不够，不能反过来声称该 cell 的 F9<tau。若某叶的
scalar guards、见证解码或数值检查有问题，保守做法也是留下它，
而不是删除它。

纯空域 Farkas leaf 的结论与 threshold 无关，可在复核原几何
证书后删除。reflection leaf 也不是能量付款：Core:10995、
11010–11015 只从 u7<l0 推出 h7<h0，故在 O 中不可能。这些叶
不能在全域直接按“已证 F9>=tau”删除。

最后取 `E=E0 union R(E0)`。旧实际反射恒等式见
Core:12959–12960；每个 h∈D 可独立选择 id 或 R 使其落入 O。
h0=h7 时选择 id 即可；用闭半域两侧都保留也只增加重复，不漏点。
允许忽略 orientation guard 来增大例外 cell，但不允许无证明地
收紧它。这里的分类必须针对任意 sublevel 点，不能用新24核或
其他 minimizer-only Newton/KKT 残余来代替。

## 两窗口反射必须独立

L(g) 和 T(g) 的 orientation 分别取决于 g0 对 g7、g1 对 g8，
没有一般理由相同。例如 g=(1,2,1,1,1,1,1,2,1) 全部满足 g>=s，
prefix 已有序，而 suffix 需要反射；这个例子只说明朝向独立，
没有评价它的能量。

因此对于每一对 C,D∈E0，原则上要检查四个组合
`(C,D),(C,RD),(RC,D),(RC,RD)`。若利用整个十点反射减少重复，
也须先证明索引和组合的对称对应，不能直接省去混合朝向。

最稳的接口在同一组十点位置 p0,...,p9 上放入约束。原局部
cell 的一个跨度约束记作 ell<=p_j-p_i<=u（局部0<=i<j<=8）。
四个嵌入为：

| 窗口/朝向 | 同一全局位置系统的跨度 |
| --- | --- |
| prefix / id | p_j-p_i |
| prefix / R | p_(8-i)-p_(8-j) |
| suffix / id | p_(j+1)-p_(i+1) |
| suffix / R | p_(9-i)-p_(9-j) |

这些映射保留共享七 gap 的全部相关性。不能给两个窗口各自
独立的共享 gap 变量，再拿彼此无关的解声称联合可行或不相容。
所有全局 gap 均另加 g_r=p_(r+1)-p_r>=s。

等价充分检验是
`projection_tail7(C') intersect projection_head7(D') = empty`，
其中 C',D' 已在物理朝向。投影可以使用可证明的外包，单坐标
区间也可以，但外包必须包含所有真实投影。丢弃额外约束只扩大
可行域，因而若扩大后的系统仍不可行，则结论安全；若扩大后
可行，只表示该充分判据未通过。

## 原根外区域不能遗漏

Core:9398–9460 的 root_cover 会在原 c9 floor 已足够时提前
返回，不是“所有 F9<tau 都落入原 RC 森林”的现成证明。tau>c9，
必须新写并证明相应的 root_locate_below_tau 接口。

可复用的静态证明路线是：

- 旧 COV=true unary 段已有 a_adj*w>=c9；在 D 上再加整个
  pressure>=s*B9，所以 F9>=c9+s*B9。不能丢掉这笔 pressure
  就直接把旧 c9 unary 结论升级到 tau。
- 某 gap>=SMAX_r/SC 的尾部给
  F9>=b_r*SMAX_r/SC+s*(B9-b_r)。必须逐个 r 核对新阈值。
- 原小 gap<=1/2 分支与 g>=s>1/2 不相容。
- 剩余点才由 COV 的 bad intervals、原 RC、全部原分支和几何
  规范化导向叶；不得仅挑已导出的某部分 roots 或数据块。

joint_gluing_review 的固定静态包给出前两项分别约
.012801293384 和最小 .0122311934375，均高于 tau。本审查核对
上述付款的数学方向及 Core 规则，不重新执行这八行算术或叶检查。
这些数不能替代新参数分类器的完整覆盖定理。

## 必须提供的完整 replay / formal 接口

下一阶段若另获授权，至少需要以下可复核输出；本轮没有实现或运行：

1. 固定 Core hash、c/tau/SA/SC、COV/SMAX、所有 RC 和 WL/WD
   数据块的身份；完整原树 token 消耗、fuel、分支及最终端点。
   新阈值检查失败后也必须正确跳过原见证位数，不能令原 mleafP
   返回0后失去 stream 对齐。
2. 每个 leaf 的类型、原 cell、其派生依据、原 witness offset、
   原 scalar guards 和显式 threshold 结果。所有叶必须归入
   proved-above-tau、empty、ordered-impossible 或 retained-exception。
   任何 unresolved 都保守留在例外；分类计数须覆盖整份森林。
3. `h∈D & h0<=h7 & F9(h)<tau -> exists C∈E0, h∈C`，含根外
   支付和 cell 边界；然后给反射闭合的全域覆盖。
4. 全部反射组合的物理嵌入和 pair-list 完整性。每个不可行结论
   给 exact rational difference-constraint negative-cycle 或等价
   非负 Farkas 付款；不能信任浮点 infeasible 标签。
5. 由这些前提接出实际 A(g)>=c 的顶层 theorem，再由其他代理
   审查其 ledger admissibility、实际核身份、计数桥、源码和内核
   预算。数值 topology replay 不能作为新的 Lean 前提。

## 边界、并集保守性及明确停止线

原 cell 和投影宜保留闭边界；严格 sublevel 使任何已证 F9>=tau
的边界点都可安全排除，但要由能量结论排除。reflection 的
u7<l0 是严格符号；端点相等不够。difference constraints 的零
权环也不证明空集，负环才够；若采用严格约束，须另外保存严格
标签及其证明，不能用 eps 或数值容差隐式收紧。

失败集合可以有重叠，也可以把整棵失败子树向祖先外包。如此会
增大 E、增加兼容 pair，却不会使充分性失真。反过来，只保留
leftmost representative、样本、极小点或挑选最方便的不相容叶
不能覆盖 arbitrary F9<tau。

任一 source/decoder/coverage guard 未闭合，就停在分类未证；
任一例外 pair 仍几何可行，就停在本纯几何充分判据未过。兼容
cell 对不是实际低能反例，也不授权自动细分、改 c/tau、换见证、
新优化或新核值。若几何全部通过，仍必须另过完整形式化、单文件
和网站复核预算；本文没有替这些关卡背书。

结论：逻辑链在上述完整前提下成立，未发现额外隐藏的极小性要求。
当前未证明例外规模、例外对不相容或所需 floor，也没有运行
相关检查。它仅是一项可进一步授权的静态充分性规格。
