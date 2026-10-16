# 继续消除全域缺口与改变数学结构

本轮仍未证明新的无条件零点比例，所有新候选均不可提交网站。
`proof-status.json` 列出当前源码与普通 Lean 内核检查的逐项绑定。
浮点局部极小值是全局下确界的上界，不能用作全域下界。

本轮 **14 个当前源码模块**已通过固定版本的普通 Lean 内核检查；打印的公理仅含 `propext`、`Classical.choice`、`Quot.sound`。这包括最弱窄室的实际能量定理、新窗正性与 majorant、新权重容量和可变 matching 计数。没有对新结果运行 nanoda，也没有证明全域 floor。

## 当前缺口的推进

`StructuralW10Followup20261016/scalar_Checker.lean` 把冻结的 PT 数据、连续有理分片和二次多项式端点检查连到实际 `AMW.Cert.wfun`。`scalar_Basin7.lean` 给出最弱窄室的 39 个具体标量下界；`scalar_FwBasin7.lean` 合成该室内的实际十点能量下界。是否通过当前源码检查，以 `proof-status.json` 为准。这些定理只有明确的实数区间条件，不能替代全域覆盖。

重新生成该组源码后，运行 `python -B -X utf8 research-20261016-followup/scalar_canonicalize.py`，将二次恒等式的九项和改写为显式项；`--check` 只检查当前形式。该步骤保留所有系数和区间条件，避免有限向量查值影响 `ring` 的原子识别。内核回执绑定最终规范化后的源码。

扩大 maximal matching 阈值的通用计数推导见 `MatchingThreshold.lean`。`KernelPair123128.lean` 使用旧短对定理与冻结金字塔，证明旧核在整个 `|t|≤123/128` 上支付 `433/50000`。严格整数几何实验 `matching_domain_probe.json` 显示：缩域套用旧树只减少 29 个分支，仍需 95,750 个分区叶，不能解决提交尺寸。

## 改变窗函数与权重

新窗取

\[
v_d(t)=\cos(\sqrt2t)+\sum_{j=1}^{m}d_j\cos(2\pi jt),\quad m=12,24.
\]

它改变实际 Fourier 核，而非细化旧 Taylor 常数。优化同时支付窗能量的正二次代价。所有整数余弦项零均值，所以归一化保持一致。通用正性与同一 majorant 的支配见 `WindowProfileGeneral.lean`、`WindowMajorantGeneral.lean`；冻结具体窗见 `NewWindows.lean`。`NewLedger.lean` 只证明新权重的容量、压力和对称性。新窗的有限高度算子与实际零点计数桥仍须重建。

| 配置 | 未证明的全域 floor 目标 | 若全部解析及覆盖前提完成后的比例 |
|---|---:|---:|
| 原固定 W10 | 0.00866 | 67.3601930886% |
| 24 模新窗，原权重 | 0.0088 | 67.3624361793% |
| 24 模新窗，新权重 | 0.00884 | 67.3628951339% |

最后一行的精确候选为

\[
\kappa=\frac{1669185178522559118481248059191797347567}
{2477900000000000000000000000000000000000}.
\]

有理权重见 `window_reweight_rational.json`。全体 19,683 个三元起点加 1,200 个随机起点的局部优化，没有找到低于 0.00884 的反例；这不是全域证明。窗能量与短对端点分别由两种有理区间实现核对：`window_exact_parameters.json` 和 `window_independent_audit.json`。完整推导、混窗的受限负结果及缺失的解析桥，见 [改窗研究记录](window_research_note.md)。

## 为什么还要引入长距离结构

`global_periodic_upper_bound.py` 用有理区间证明：旧核、旧各 rank 总量与旧压力在一个明确周期二配置上的平均能量小于 0.008674。因此仅添加有界 telescoping potential 的方法，在这些固定参数下有严格的能量上限。它不是新的零点比例下界，也没有排除改窗、改权重或增加 rank 的方法。

`global_tail_probe.json` 和 `global_tail_local_probe.json` 给出增加 rank 10 至 32 的容量合法构造与数值尺度；其中所有极小值仍为上界。Fourier minorant 路线把全链问题转为寻找一维函数：若偶函数 `h≤w`、Fourier 变换非负、在距离 `T` 后非正，则周期化可导出有限 band 的能量下界；相应代数转移形式化在 `FourierMinorantTransfer.lean`。目前测试的 Gaussian–Hermite 子族不足以超过旧 floor，尚无可用的具体一维证书。详见本目录 `global_*` 研究记录。

## 提交状态

没有生成声称无条件新纪录的 `Solution.lean`，没有向网站提交。原候选仍需完整有限覆盖的内核证明、尺寸合规的单文件、严格的声明比较与双内核重放；新窗候选还需完整的新算子和解析计数连接。`submission-research-note.txt` 是带这些限制的材料草稿，不能当作完成证明上传。
