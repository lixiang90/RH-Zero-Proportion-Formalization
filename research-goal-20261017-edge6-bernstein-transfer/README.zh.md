# 固定逐边六阶 Bernstein 转移：未通过

本包执行根部明确授权的一份固定结构性准备及一次固定数学候选的总
付款判定。目标仍为 c=11/1250，原单元、DBM whole spans、旧/新多项式、
lambda、保留 Gram 因子、正 divisor 与真实 margin 均保持固定。没有
求解器、特征分解、实际 oracle、新点、参数/界扫描、区间细分、升阶
或 Lean 编译。

数学准备结果：41 条边各使用单一 degree6 Bernstein，不先将负的
edge upper 截成零；正权与 incident 求和后才取 epsilon>=0。每条边
的旧 U3/A4、新 U5/E6/L6、Dplus/Dminus、18 个坐标差及 q0=L2−L6
均核对回同一 5005 单项式系数。123 次 Bernstein 正逆变换全部相等。
准备用时 5.913 秒，报告峰值 working set 187,703,296 B；packet raw
1,027,219 B，gzip 339,808 B，均低于40MiB/1.5GiB guard。

固定 q0 拆分使用

`Cbar=old_F_lower−old_uniform_payment−b dot old_anchor`，

九个线性差通过正相邻边的
`tau_adj=(old_gradient_midpoint−b)/a_adj`
吸收，其余 tau=0。各边二次项保留原 whole-span second lower，
最后 aggregate 只除以 c 一次。没有重新采样旧 oracle 或将旧数值
区间冒充已证实际 Lean 区间。

独立 epsilon 重放已经通过；其记录位于
`research-goal-20261017-edge6-transfer-audit/independent-replay.json`。
总 K 的独立复算由该审阅者另行封存，不导入本 producer。

## 总 K 的固定判定

使用保留后的实际 lambda/L/div：

- retained-ray SHA
  `b51724e37d219705828d08a5af8db3d1588563d22908fe75b9dc29261e944d21`；
- retained exact certificate SHA
  `7c8d083cec89942c19642a8206156a2f77879e3c1278d21c56bf3f2da2233332`；
- 真实 margin =
  `190972275995535925423158387453/200000000000000000000000000000`
  （约0.9548613799776796）。

所有 180 个旧 KKT 标量都按 lambda/(10^12*row.scale) 付款；18 个
KKT Gram 及 q0 块均使用实际保留列的
`B=sum_col(sum_basis(abs(integerFactor)))^2/(10^24*blockDivisor)`。
本包没有为了改善结果更换这个固定上界。

| 部分 | 有理结果的浮点显示，仅供阅读 |
|---|---:|
| 180 个旧 KKT scalar | 0.1755160257655382 |
| 18 个旧 KKT Gram | 30.270897734292884 |
| q0 Gram | 29.052806606644072 |
| 总 K | **59.499220366702495** |
| retained margin | **0.9548613799776796** |

`budget.json` 用精确 Fraction 比较，结果为 FAIL。没有消除任何旧
F0/L2/P3/E4 的实际解析义务；8 个交换的 actual 包络义务也保持。
先前约1970.66的预算用了另一组 Gram/上界，不能把两次数字的差
单独归因于 Bernstein。当前未通过也不否定旧实际区间真命题。

## 序列化恢复记录

第一次 K 算术执行到达总和与精确判据后，在 `str(scalar_total)`
生成 JSON 时超过 Python 默认 4300 位整数显示限制，退出且没有
输出 budget.json。它不是数学判据失败或数据不一致。

经根部明确许可，保留原脚本
`evaluate_initial_serialization_failure.py`，在同一固定输入上仅以
`sys.set_int_max_str_digits(0)` 解除序列化限制并补记 provenance，
随后重建上述结果。诚实计数为 **2 次算术执行、1 个数学候选**。
epsilon 包没有重生或变化。恢复执行用时483ms、峰值156,180,480 B。

默认不要重跑 producer。全部输出为不可覆写的固定记录；独立审阅
脚本负责复核，不能借重跑选择另一个 bound、Gram 或 margin。

## 对全域与源码目标的含义

根部覆盖审计已确认此 fixed cell 是历史 baseline 中的已闭合子树：
4 branches、5 accepted leaves，不属于当前17个 frontier，也无
prefix 关系。其原5个 leaf payload 约6021 B。因此本包只评估一个
actualization 方法，不计为新增 frontier 闭合、ancestor 覆盖或有益
源码压缩。保留 Gram 的数据源码本身仍有2,394,367 B，网站单文件
及完整全域证明均未满足。

本固定任务到此停止，没有新 Lean、进一步付款试验或 κ 主张。
