# W9A2 实际转移、有限势与零点计数独立静审

结论：本次独立静审没有发现确定的数学缺口或可从源码确定的 elaboration 错误。
原始 24 个 state 的全部 73 字段及 margin 成本、48 朝向之间 2267 个已选严格冲突、
49 状态 134 条边的势不等式、H/B/κ 算术与 root 计数接口均通过独立标准库核对。
这不是普通 Lean 或任何内核的通过收据；全部新 theorem 仍需实际编译。

本代理只读审查 `StructuralW9A220261020/` 五源及其冻结输入；唯一写入本目录。
未运行 compiler、LP、Karp、新几何搜索、核函数求值、覆盖批次或任何旧 producer。
主轮计数读取为 macro007 后的 1，没有修改。

## 证据的精确范围

`audit.json` 固定所有输入的 bytes/SHA，执行前后逐字节散列相同。
本次运行 `python research-goal-20261020-w9a2-independent-static/audit.py` 实际 exit0。
脚本只调用 Python 标准库，直接解析本次 Lean 的 literal，不 import 原准备或静审程序。
它只代入每一对原已选的 span，不寻找新的冲突，也不重新计算图最优值。

| 项目 | 本次核对 |
| --- | --- |
| qState | 24×73 字段逐项等于原 first24；M 全部为0 |
| qCost | 原 margin 整除 335544320000000000，49 成本与图一致 |
| span 反射 | 全36种 `[i,j]` 的符号 gap 系数与 `[8-j,8-i]` 一致 |
| 共享 span | 全28种左 `[i,j]` 与右 `[i-1,j-1]` 对应同物理 gap |
| 闭边界排除 | 2267 已选严格不等式；最小整数差1，SC=32768 |
| 图 | 37 bad→bad 边及所有 incident-G 边，合计134 |
| 势 | 134条 `622387738726+p(v)-p(u)≤5 cost(u)`；最小余量0 |
| 势振幅 | p(G)=min p=0，max p=2504722000690 |
| κ | `(H-B)/(1-c)` 精确等于本次 candidate，严格大于冻结 baseline |

## 实际 span/reflection 与全域输入

`Graph.cell_span_bounds` 使用原 InCell 的闭 lower/upper；PR 的算术索引另与完整
pair 列表核对。`Graph.located_span` 对 odd 状态把区间两端映射为 `[8-j,8-i]`，
随后双反射恢复原 g 的 span，未把整个 reversed cell 当成另一个独立物理窗口。
`Graph.shared_span` 对应同一个九 gap 路径的两个八 gap 窗口，恰共享七 gap。

`Graph.edge_from_locations` 逐方向用同一共享 span、SC 正性及严格端点冲突反证。
G 没有几何限制；所有 incident-G 边都保留。因此这个 theorem 不需要额外的 sep
或 ordered 前提，任意真实两个 location 均可使用。端点相等或区间接触没有被排除。

Final 的实际 location 来自 `Localization.located_state`，不是抽象 At 参数：它对
每个 gap≥17/20 的任意实际 g，给 StateAt 与同窗实际 Fw 的定量下界。
其下游依赖原全部48根的定量 walk；root 外 tails/true-WZ 通过附加 sep 压力支付 G，
小 gap 分支与 sep 冲突，原 Pg 的反向分支由实际 ordering 排除。
reverse 使用当前新核的 `PC9QB6M_G_rev` 和 `Fg_G`。未把原 cN 的 cover guard
静默升级为新阈值；原 guarded 部分与额外压力分别支付。
该全域证明体的上述逻辑经静读无缺口；尚无本次编译收据证明 tactics 与48根有限检查完成。

## 势求和、末窗与一次 C 付款

`Counting.summed_of_state` 对 m≥9 个实际有序分离点取 N=m−8 个真实九点窗口。
内部 `i+1<N` 分支构造真实十点窗口后应用实际转移；其余最后一窗只取
`Edge(S i,G)`，从源成本支付本窗。它不假设存在第 N 个真实窗口，没有丢弃最后窗。
`S N=G` 的势在整个构造中良定义。通用空和情况单独由原归纳基础处理。

逐窗使用物理势 `p/(5·10^20)` 与增量 `622387738726/(5·10^20)`，故和式为
`N·c+P(N)−P(0)`，由非负终势和初势≤C 得 `N·c−C`。
没有把整数µ、分母5或 G 成本10^12误作物理平均能量。

Payment 至 actual_defect_estimate_effective 整段与旧已接受开发中的通用桥逐字相同，
归一化文本 SHA 为 `421c93f7c9c2fc679547017a1a19043855725efa026722fe073aada433af83e0`。
它 import 当前 W9A2 Core，因此所有实际 wfun/kfun/Fw、retained Gram、谱及压力均
绑定本次新核。没有 import 旧 s1R Core 或移植旧数值表。

匹配分区只在 `z=none` 的唯一 separated remainder 中出现 C。所有 close pair
仍用当前核的1/64付款，不各自再扣 C。`C≤c` 后把 harmless boundary 参数从9
升至10，同时把 δ 邻域系数从8升至9，误差方向保守；最终 n=10 的实际计数接口
与本次 Core 的 ActualDefectEstimate 定义吻合。

## H/B、κ 与 root 计数接口

H 分子 `6721237468782417141365717707344332375586`、分母10^40；
B=`454741897490/10^14`；c=`4465145772003282851/(5·10^20)`。
C=`2504722000690/(5·10^20)` 满足 `0≤C≤c≤1/64`。
所得候选精确为

```
3337881639516708570682858853672166187793 /
4955348542279967171490000000000000000000
```

Final 的 `_root_.Ncount/N0star` 与 Counting 的 `Zeta23.Ncount/N0star` 不是一对
abbrev。trusted ChallengeDeps 与实际 package Statement 的 IsNontrivialZero、
zeroMult、zerosIn、Ncount、N0star 五个 def 声明均逐字符相同；递归展开后
definitionally equal。因此 Final 的 `exact h` 接口有源码依据，且旧已接受 Final
使用相同形式。它没有用错误的乘数、distinct denominator 或条件零点计数替代。

## 编译与交付边界

本次没有发现需要预先改写源码的确定问题；没有为了静审而改任何 proof。
不能由静审推断 `decide`/`interval_cases`/cast normalization/`linarith` 等 tactics
已实际成功。冻结 ordinary gate 必须包含 Core、Graph、Localization、Counting、
Final，先证实际 located_state、actual transition 与 finite checks，再核最终根。

五个实际 Lean 文件 raw 合计1,827,766字节；这不是已生成的单文件。
flatten、可信新鲜 CandidateSpec、公理传递审计、Comparator、Lean/nanoda、生产总时限、
届时最新网站纪录、GitHub逐字同步与提交材料均仍未在本包验证。
原已接受结果、现数值重放或这份静审不覆盖上述最终验收。
