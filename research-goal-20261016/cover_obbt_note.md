# 子水平集、驻点与完整 epigraph 的联合覆盖

本文件记录结构方法及其严格有限证据，不宣称已经得到新的无条件零点比例。
所有实际解析桥和全域覆盖的完成状态，必须分别核对普通 Lean 内核收据和全域 frontier。

## 收缩对象与数学逻辑

固定新的 24 模核和权重。正 pressure 保证能取到原正交象限上的全局极小点，
这一存在性由 `CoverCoerciveKKT.exists_global_min` 真正证明，没有额外假设。
要反证 floor `F≥c`，只需覆盖满足 `F<c` 的原全局极小点。
它们在严格内部坐标满足梯度为零，在原 sep 边界满足梯度非负。
cell 自己的边界不构成新的优化约束。

普通 value checker 只在某个仿射 minorant `A(q)=C+a·q` 的整个 cell 下界已经达到 c 时闭合。
更强的方法利用全部子水平信息：`A(q)≤F(q)<c`。
若整数 flow 证明

`m ≤ s K DEN z(q) + p SC A(q)`，其中 `p≥0`、`s=±1`，

则 `s=1` 给出 `z(q)≥(m-p SC TARGET)/(K DEN)`；
`s=-1` 给出 `z(q)≤(p SC TARGET-m)/(K DEN)`。
这里 q 是以 SC=32768 缩放的真实 gap，不能当作整数；因此下界保守取 floor，上界取 ceil。
最终差分约束闭包也必须重建。

`CoverSublevelContraction.lean` 的四个薄引理已经普通内核核验。
它们只保留 `F<c` 的点，不能套用旧的 pointwise `PCell.walk_sound`。
Newton 另有 `CoverKKTContraction.lean`，只保留原 KKT 点。
新 runner 用分离的映射固定按 OBBT 后 Newton 的顺序解释这些操作。

## 为什么完整 epigraph 有实质收益

只复用一次 energy-minimization 得到的 A，不一定适合给每个 span 的上下界。
完整 epigraph 保留每个标量的全部有效切线和零下界，并加入 `F_relax≤c`。
针对每个 span 和符号分别求 LP，dual 只用于选择：

- 一个非负 Lagrange multiplier；
- 一组总质量不超过对应核权重的非负标量支持混合；
- 一个 exact flow 支持。

浮点 LP 的目标值和 infeasibility 都不作为接受依据。
所有容量、整数仿射系数、flow balance/cost 和最终 outward bound 重新严格检查。
`cover_sublevel_obbt_api.make_engine(w)` 给 high/low 窗口建立私有实例，
`contract(state,target,axes,engine)` 显式接收目标整数，避免修改另一个模块的 TARGET 或活跃进程。

同一组 1000 个均匀旧父 cell，先前一阶方向能排除 191 个：

| 方法 | 另外收缩 | 另外闭合父 cell |
| --- | ---: | ---: |
| 旧 Newton，4 轮 | 111 | 17 |
| 同一 energy minorant 的子水平收缩，2 轮 | 237 | 91 |
| 完整 epigraph，逐 span 单独选择 minorant，1 轮 | 806 | 506 |

最后一行有 12180 个有效 bound，472 个新方向闭合、34 个新 value 闭合。
这些是原来需要 split 的父 cell；506 个 topmost 闭合覆盖原树 1442 个父分支。
收缩后 gap 盒体积比的中位数约 0.00354025，658 个 cell 小于原体积的十分之一。

`cover-sublevel-obbt-replay.json` 已完整通过 806 个 cell、12180 个 bound 和506 个闭合的独立有限算术重放。
它复算固定 Fraction 标量 oracle，没有调用 LP 或 min-cost-flow 优化器。
实际核的 Lean 解析联系仍须单独完成。

## 可重放归档与证书负担

`cover-obbt-archive/manifest.json` 固定 24 个源码/输入依赖、原目标、原收据及 SHA256。
七个有效 gzip witness 分片加一个祖先 projection 总计 8631889 字节，最大 witness 分片 1496351 字节。
独立 archive replayer 从 root 重建 4459 个必要祖先分支和全部 806 个 cell，
逐项重放12180个 bound，并逐字节重建原 44720364 字节的 witness JSON。
它不需要原完整 41k-node snapshot。归档明确标记全域未完成。

在另一个独立后处理实验中，逐一删除方向闭合叶不需要的 OBBT bound，
只在更宽 cell 上重新得到严格方向/flow 证书时接受删除。
472 个方向闭合的 bound 从7903降至2258，其中81个仅需一个bound，141个不超过两个。
这不能直接删掉仍有后继子树的收缩约束；扩大 branch cell 之后必须重新覆盖其全部保留区域。
`cover-obbt-pruned-replay.json` 是该后处理的独立核验收据。
Root 的 forest flow basis 再独立去掉可由 divergence 唯一重建的巨大 flow amount。
两者解决不同的证书负担，不能把文件压缩结果当作 Lean 全域证明。

## Gram 盆域与补充负结果

69 个 Gram 锚全部在各自所有41个正权 span 的整数中心±.21内，
最大偏移仅11690437/100000000。
更强的精确检查表明：69 个锚周围的整个每gap±1/100盒（交原 sep 象限）均被 registry 接受。
因此盆域非空且有正体积。登记的整数gap总和在12..14；
当前 DFS 先经过总和较小的区域，因此早期0个Gram叶并不意味着盆域不包含这些极小点。

OBBT 后300个残余cell没有得到统一负曲率排除；再作8轮Newton，
119个收缩、58个一阶排除，仍没有新的负曲率证书。
原cell上直接将 energy epigraph 与 affine-gradient KKT 同时放入一个LP，
用一个整数flow证明 `D_dF+lam(c-A)<0`，在1000父cell新增52个闭合，均独立重放通过。
这比先OBBT收缩再重做导数 Taylor 余量的506个闭合弱，暂未加到主 runner。

完整新搜索由 `window_obbt_newton_cover.py` 从 root 运行。
500节点 pilot 已独立重放全部5652个OBBT bound和795步Newton，仍有11个frontier。
主搜索是否完成必须读取它自己最新 checkpoint；任何 partial checkpoint 都不是无条件新纪录。
