# 固定精确射线的实际 Lean 连接与源码计划

本报告只读审阅一份固定证书，不运行 Lean、求解器、特征分解、实际
函数采样或参数搜索，不改变宏观回顾计数。具体证书的独立精确算术
重放由另一审阅者完成；这里不重复其 2,548,856 项组合。

绑定的量化包 SHA 为
`4862b3437fbc68766e1870afdabda9ea466b18750e2715cbe953e0b8cd363805`，
DS30 包络证书 SHA 为
`7935f4945013c087357141c6f4406ef1b83c03fd9c8cfef61a7cd397f21e57a0`。
标量权与 Gram 因子分母都为 10^12。仅第 5793、5794 行权重为零；
14,562 个标量权均正，73 个 Gram 块全部非零，3010 个因子列均保留。
新 181 行全部活动。因此以下依赖不是按浮点阈值猜测的“可能依赖”。

## 1. 真正活动的实际义务

以下编号为固定模型的零基编号。

| 活动部分 | 数量/编号 | 实际意义及现状 |
|---|---|---|
| DBM 标量与两两松弛乘积 | 90 + 4095 | 由实际 `Contains cell g` 给出各跨度区间，再乘非负实数；已有实际几何 API，可作有限代数实例。 |
| 旧自由 KKT 标量 | 180，4185..4364 | 是 `E4_r ± test*P3_r >= 0`，test 为 1 或单个 y；需要旧导数包的实际身份，除非采用第 4 节的已付款转移。 |
| 旧与新增矩箱 | 1428 + 8580 | 对真实 y 的单项式成立；由每个 `|y_r|<=1` 推出，不需要抽象伪矩存在假设。偶次各坐标指数的单项式另有下界 0。 |
| 旧软 L4 能量及松弛 | 5793、5794，权为 0 | 两行可精确省略。不由此省略其他活动块的旧 F0/L2/P3/E4 义务。 |
| 交换标量 | 8，5795..5802 | 每个 D4 必须是实际交换能量差的上界，才能由全局极小性得到 D4>=0。 |
| 新绝对 L6 能量 | 1，14383 | 需实际逐边绝对下包络 L6<=Fw24，再用 Fw24<c；不需要旧 F0。 |
| 新自由 KKT | 180，14384..14563 | 需实际 `|gradient_r-P5_r|<=E6_r` 和自由坐标 gradient=0；仅 P5 乘 test，E6 不乘。 |
| Gram 块 0 | M3，220×220 | 乘子为 1；对实际单项式向量，任意给定有理因子直接给平方和非负。 |
| Gram 块 1 | 55×55 | 乘子 `(c-L2)/c`，仍依赖实际旧二次下界，除非有已付款转移。 |
| Gram 块 2..46 | 45 个 55×55 | 乘子为各跨度上下松弛的非负乘积，实际 DBM 足够。 |
| Gram 块 47..54 | 8 个 10×10 | 乘子为交换 D4，仍需上述实际全局竞争点与包络桥。 |
| Gram 块 55..72 | 18 个 10×10 | 乘子为旧 E4±P3，而不是 P3−E4。仍需旧输入或已付款转移。 |

最终实际命题应是
`RelevantBelow (123/128) (11/1250) g ∧ Contains C g → False`。
这里的 `Relevant` 包含整个分离正交域中的全局极小性。当前 C 是经
极小点条件收缩的单元，不能将本命题改写为任意低能窗口分类或平均
坏集频率。本单元排除也没有补齐祖先到完整 root 的全部覆盖证明。

## 2. 可以直接使用的实际定理，与不能直接复用的具体数据

已有实际基础可复用：

- `WindowGramExpansion.actual_energy_expansion`：实际 Fw24 等于压力与
  41 个正权实际 w 值之和。
- `WindowKKTInstance.of_relevantBelow`、`WindowGapEnergy` 的实际梯度
  和 `WindowDirectionalAffine` 的 41 项导数展开：本 C 的九个相邻
  下界均严格大于 sep，故九坐标确实自由，梯度为零。
- `WindowMomentLayout.normalized_bounds`：给真实
  `y_r=(g_r-center_r)/radius_r` 的 [-1,1] 界。它不是已证的通用
  5004 高矩布局；仍需有限单项式求值与乘法映射的声音性桥。
- `WindowRawCoefficients.sound` 和 `WindowDerivativeTableArithmetic`
  的移位系数/全局 24 阶余项：实际 normalized-W 表已经有来源证明。
  `WindowFixedDerivative.interval` 与 `WindowCellDerivative.interval`
  可在其对应布尔检查真正通过后给实际点/整区间导数界。
- `WindowGlobalCompetitor`：实际 gap 交换保持正交域可行，真正全局
  极小点满足 `Fw24 g <= Fw24(swap g)`。交换像不需要留在 C 内。
- `WindowBoundedMomentFarkas.exclude`：可复用精确整数聚合与箱支持
  函数付款。Gram 项可以先转成相同方向的线性 Row 不等式。

但以下具体实例尚不存在，不能用“已有通用模块”替代：

1. **当前 C 不是已证 friendly 两叶。** 已证 82 个粗 point packets
   的路径是另外两个单元。当前 C 为
   `r001000001000100110011001`。旧 P3 的 41 个 anchor 仅有 2 个位置
   与该 82 点集重合；新 41 点仅 1 个位置重合。位置重合本身还不
   证明目标的旧精确端点比已证粗端点宽。

2. **新绝对 L6 不是共同向量 anchor 的能量包。** 新 41 个逐边
   whole-span midpoint 中，25 个不等于同一 layout center 的跨度。
   例如边 (0,5) 的 anchor 是 87081/16384，而 layout center 五项之和
   是 351369/65536。现 `WindowMomentEnergyCertificate.checkGeometry`
   要求共同 center、`point<82` 并查询固定 734 行 q2 表；不能直接
   实例化新 L6。正确路线是对 41 条边各自建立绝对 scalar 下包络，
   然后调用 `actual_energy_expansion`。不应增加假的 anchor 可积性假设。

3. **精确 QI 与 FI 检查不是字面相同。** 新包用未逐步舍入的有理
   interval Horner，给出精确分数端点；现 FI checker 会作固定格
   外舍入。不能未经有限比较就将其 bool check 当作已经通过。
   最直接的精确桥是用已有 `WindowRationalInterval.add_sound`、
   `mul_sound` 和已证移位系数建立同一未舍入 Horner 的声音性；这
   是缺少的小算术接口，不是新的数学假设。

4. **局部 Taylor 的实际解析定理仍缺。** 新 L6 与 U5/E6 需要整段
   M7：先由 p,x 都在同一 whole-span Icc 推出 uIcc(p,x) 也在其中，
   再用实际 w 的 Lagrange 余项。现 `taylor_remainder` 使用全域导数
   界，不能直接喂一个仅在局部成立的 M7。实际光滑性和 Mathlib
   Lagrange API 已有；需要把该局部性及奇次误差转偶次付款写成证明。

5. **旧 provider 不能自动继承。** 旧 P3/E4 来自 `cover_newjet.json`
   的 w-prime 系数、41 个旧共同 anchor 上的 w1..w4 区间和 658 个
   旧 q5 网格界。此前系数包含性检查已经表明，它们与已证
   normalized-W 推导区间不是全表相同/单向包含。旧 L2 又使用旧
   F0、梯度区间及 whole-span q2 lower。通用
   `WindowMomentEnergy.lower` 给出了适当的数学模式，但硬绑定的
   friendly 数据消费者不能直接证明这一旧 L2 多项式。

6. **交换 D4 仍需实际 scalar 上下包络。** 固定 normalized 交换
   包有 87 个逐边包、orders0..4 及 622 个 q5 网格界。应证明
   `actual_delta <= D4`，再接实际 `actual_delta>=0`；不能把 D4 的
   符号直接当作 actual 全局极小性。新 41 点的 orders0..4 中有 40
   份与这 87 份精确字面相同，唯一未出现于交换库的是总跨度边
   (0,9)，anchor=793251/65536。此处可以共享数据与一个声音性桥，
   但当前共享的只是固定数据身份，并非新增 Lean 实例。

无旧输入转移时，实际网格需求分别是旧 q5 658、normalized 交换 q5
622、新 q7 658；旧 q5 与交换 q5 的 cell index 并集为 679。不同
阶数和 provider 的同一 cell index 不能仅按下标合并为同一证明。

## 3. 固定证书的最小实际连接次序

当前不启动任何编译。下一次执行须由精确证书与旧输入转移预算的
结果决定。

1. **先定实际 scalar 前提集合。** 若第 4 节的固定转移预算通过，
   优先删掉旧 F0/L2/P3/E4 provider，保留新绝对六阶与交换 normalized
   provider；若未通过，则不能声称这些旧输入已消除。
2. **先做一个真正的实际有限实例。** 选择已固定的新 edge0：
   p=73739/65536、n=1 的 orders0..6，以及其第一个 whole q7 cell62，
   即 [31/32,63/64]。证明实际 exact-QI enclosure，不生成整批静态
   模块。这一小关直接检验目前最具体的端点/余项接口缺口。
3. **局部 scalar 包络。** 接局部 Lagrange 余项、point 的 mu/eps、
   |d|<=R，得到实际 T6±A6 和 U5±E6；随后用同样的局部形式覆盖
   交换 quartic 的 T4±A4。没有新极值/全局最小存在性的假设。
4. **逐边实际能量、自由 KKT、交换。** 41 边绝对下界给 L6<=Fw24；
   九坐标导数展开给 |P5-gradient|<=E6；已有实际全局竞争点给 D4>=0。
   将这几项接成 active scalar 与 localizer 的实际非负性。
5. **真实高矩与 Gram。** 定义固定 5005 个单项式为真实 y 的乘积，
   用有限乘法目标映射声音性连接因子多项式；每个 Gram 项直接是
   `q_b(y) * sum_col(linear_combination)^2 / divisor_b`。整数因子已经
   是 PSD 证据，无需 Lean 重做 eigh 或验证任意浮点 PSD 矩阵。
6. **最后才接 DS30 有限算术与单元排除。** 按单项式或小组核验
   2,548,856 个有理 atom 的 floor/ceil 聚合及所有实际矩箱。它是
   包络付款，不是声称残差精确为零。避免一个巨大的 `ring` 或
   `decide` 同时展开所有 Gram 与 181 行；用独立 aux 和已证明的
   sum/product 声音性组合。具体小块尺寸须以后实测，当前不排批次。

第 2 步是明确的下一证明任务，而非单独添加一个带所有目标前提的
通用条件定理。完整单元排除之前仍需真正核验所有被它调用的具体
点/网格义务；完成后还只得到这个 contracted cell 的排除。

## 4. 旧输入的已付款转移：公式正确，预算仍待另一任务计算

令真正自由极小点上已证 `|P5_r|<=E6_r`，且 |test|<=1。记
Delta=P3_r−P5_r。若

`eps_r=max(0,boxUpper(E6_r−E4_r+Delta),boxUpper(E6_r−E4_r−Delta))`，

则 `E4_r ± test*P3_r >= -eps_r`。证明只用三角不等式；无需旧 E4
实际非负、旧导数区间身份或旧 P3 真的逼近梯度。

同理，由实际 L6<=Fw24<c 及 c>0，

`(c−L2)/c >= -eps0`，其中
`eps0=max(0,boxUpper((L2−L6)/c))`。

固定 Gram 因子分母为 D_L，实际基函数绝对值均<=1，因此每块的
非负平方和 S_b 有明确上界

`B_b = sum_col(sum_basis |integerFactor|)^2 / (D_L^2 * blockDivisor_b)`。

实际总组合 H 因而不再假设 H>=0，而可得 H>=-K。必须包含：

- block1 的 `eps0*B_1`；q0 已经含 1/c，不能漏缩放；
- 18 个旧 KKT Gram 的 `eps_r*B_b`；
- **全部 180 个旧 KKT 标量**的
  `lambdaNumerator*eps_r/(D_lambda*row.scale)`。

最后一项不能只因考虑 Gram 就省略。若精确证明 K 小于现有正 margin，
可与同一固定多项式的 `H<=-margin` 矛盾，删掉上述旧 analytic 输入。
原证书不改，须另存转移预算及其独立重放。8 个交换块/标量的实际
包络义务不会由这两条转移公式自动消失。

该转移若通过，会将主要 provider 收敛到同一已证 normalized-W
来源：new41 与 swap87 可共享 40 份 orders0..4，最多 88 个 anchor，
522 个所需 point derivative intervals；再分别核 new q7 与 swap q5。
本报告没有计算 K、没有选择新的精度、秩、参数或求解器。

## 5. 单 cell 源码体积：当前字面值方案明确不合规

以下是固定数据的逐字节静态计数，不是 gzip artifact 与 Lean 文件
之间的类比：

| 项目 | 固定计数/UTF-8 字节 |
|---|---:|
| scalar 权整数 | 14,564 个，flat decimal array 138,875 B |
| Gram 因子整数 | 190,150 个，flat decimal arrays 2,131,443 B |
| 权重与因子合计 | **2,270,318 B** |
| 5005 个系数区间的两端点 array | 194,558 B |
| 三类 literal 合计 | **2,464,876 B**，尚无任何证明或 decoder |
| 原量化 JSON 解压 | 2,295,719 B |
| 原量化 gzip | 1,106,957 B，只是外部数据格式 |
| 原完整 metadata certificate | 758,192 B，多数 box/支付字段可由定义重算 |

因此直接写十进制 λ/L 字面值已经超过网站 2,000,000 B，连系数区间
和实际函数证明都还没加。即使不存两端点、在 Lean 中重算它们，也
没有消除此字面值障碍。量化 gzip 加 certificate 小于约1.9MB并不
代表它们能作为网站的单个 Lean 源码使用。

为识别复用瓶颈，另只读统计了所选现有实际 API 与 counting 根的
仓库 import closure：132 个文件，未裁剪源码共 3,087,115 B。这里
含 `GramDefect20261015/Core.lean` 1,912,350 B、JetTableData 322,302 B
和 GridCertificateData 207,485 B；存在许多未使用声明，这不是
最小 bundle 的下界，也没有包含未来新增的六阶/SOS 源码。但如果
照搬当前 closure 加十进制证书和端点，已达 5,551,991 B。

可复用方向仅限可证明的结构，不是当前合规承诺：

- normalized-W 的 33×24 来源表与 actual kernel/计数证明只保留一份；
  不能为了消除旧 provider 再复制整套表。
- 41 个逐边 affine span 的幂、单项式乘法目标、Gram block offsets、
  moment boxes 和最后支付由通用定义重算，不复制数百万 atoms。
- 旧 L2/P3/E4 若经预算转移可由定义参与纯有理代数，无需保存并
  形式化旧 w-prime 解析 provider；仍需证明转移付款本身。
- 固定 λ/L 需要无损整数编码或可证明的公共结构；当前并未实现或
  编译任何此类 decoder。保留全部当前秩和精度，不在这里做压缩/
  截秩/参数试验。最终 source 还必须包含 decoder 和 actual soundness。
- 源码裁剪须按真正 theorem 依赖进行，并重新核验最终单文件。
  源 import closure 和已有 gzip bytes 都不能充当这项验证。

单 cell 的 λ/L 也不能默认为全树各 cell 共用。未来完整覆盖需要
证书复用、区域统一性或另一个可验证的全域压缩机制；当前只确定了
一个固定单元的外模型严格矛盾。全域 floor、最终无条件 κ、最终
独立内核及网站提交材料的完成标志均保持 false。
