# 固定 O 的两条实际解析桥：待编译源码

本包只准备两个新模块。旧 CurrentPrefix、QuantizedComponent、Sparse78、B2 与所有旧收据均不修改。尚未编译，也未生成固定 1322606 的有限数据或证明其实际 pair floor。O 数字结果是固定 pair 的条件性结果，独立数字审查仍由另一 owner 处理。

## 现有源码与新定理的精确差别

`StructuralS1RO20261018/CellAQuantitative.lean` 只导入已普通编译通过的当前 s1R CurrentPrefix。

原 source 7578–7602 的 `AMW.G.CellA.w2_nonneg` 先证明

`W2L.v ≤ (k1AM(x)^2 + kfunAM(x)*k2AM(x))*DZ^2`

再丢弃数值大小，仅输出 `0≤w2AM(x)`。新 `lower_le_w2` 保留相同 K1 平方和 K0*K2 下包络，输出

`2*W2L.v/DZ^2 ≤ w2AM(x)`。

guards 仍是原 `CellA.ok=true`、`0<E2L`、`0<E3L` 与原闭区间 membership。该不等式本身允许 W2L 有符号；`lower_nonneg` 单独从原 W2L.nonneg 得非负。`cellN_lower` 接受原 `CellN.convOk=true`，给出非负性和实际 `Cert.w2` 的定量下界。当前实际 DZ 为 source 的 `10^15`，不替换为其他 profile 的尺度。

`StructuralS1RO20261018/StrongQuantized.lean` 只导入本桥、已通过的 PhaseA1 QuantizedComponent 和当前 Mathlib 凸性 API，不导入旧 24-mode 核。

* `ell_le_true_tangent` 保留原 L0 和原导数量化，证明原 ell 不超过实际点切线。
* `strong_tangent` 用当前全局 HasDerivAt(wfun,w1) 与 HasDerivAt(w1,w2)，仅在显式 `uIcc q s` 上证明 `w(t)-m(t-q)^2/2` 凸，从而得实际强切线。不假设任何未证全局凸性。
* `ell_strong_hull` 的数值输入必须覆盖 `Icc(min q a,max q b)`，q=p/SC；同时保留原 TVal、L0≤L、s∈[L/SC,U/SC]、m≥0 与 s∈[a,b]。
* `scaled_strong_hull` 返回实际 raw row 可用的 κm/2 平方余项。物理跨度 s 不换成整数 X；若另改用 X=20Qp，平方系数必须相应除 `(20Q)^2`。

两份新文件的完整内容即本次精确源码差异；没有原文件的原位补丁。定理和 tactic 仍待普通 Lean 验证，尤其新的 ConvexOn API 实例化尚未实测。

## 固定有限消费者的最短后续接口（本次不生成）

1. **23 个原 ccell**：每个仅存原整数 L/U 与一个有理 m。由原 source 的 `ccell L U` 计算/证明 convOk；再以纯整数比较证明 `m*DZ^2≤2*W2L.v`。不必复制 FA/K0/K1/K2 中间记录。可从原 hR 的 conjunction 提取既有 convOk，或对这 23 条独立作有限 bool 核验；实现和耗时尚未知。
2. **49 条原正 μ anchor**：保存原 rowID/term/anchor、L0/L/U、物理 span、μ 和对 23 cells 的覆盖索引。由原 PT 全局 ptS 和原 ivIn guard 得 TVal；覆盖证明必须覆盖 hull(q,I)。每条通过 `scaled_strong_hull` 得 raw row 的额外 `κm(s-q)^2/2`。不得再乘旧 FS mass 或 external a。
3. **原 full52 raw dual**：仍须证明所有活动 geometry/constant/anchor rows 的实际有效性，以及完整 52 坐标 balance、μ 非负和原 cost。不能仅相信 packet 的 cost。旧 Sparse78 当前失败，不算已有这一消费者；本次不修它，也不把其改成新的 52 模块。
4. **网络付款**：只存固定 p* 的 10 个有理坐标（逐分量 gauge 的零坐标可省），与每 anchor 的 c=μκm/2。十条有限有理 stationarity equality 加 c≥0，足以证明

   `Σc(span(P)-q)^2 = Q(p*) + Σc(span(P-p*))^2 ≥ Q(p*)`。

   不需要在 Lean 证明求逆/高斯消元算法正确，也不需要 p* 满足原几何域。最后用已核原 dual cost 与 `cost+Q(p*)≥target` 的有限比较付款。
5. **最终局部结论**：仍限原 cells278/665、rev/id、真实双 Ordered 和 sep 的固定 pair。全 product cover、所有 residual pair、全局计数与网站新比例均未由此得到。

## 源码和运行预算

Root 的另项只读库存报固定数据约 15,950B（原 305 μ、23 m、49 映射、9 p*），只是数据字面量，不是 actual checker。此处直接读取既有 packet 的字符串长度仅为 source-layout 参考：p* 字符串共 7,603B，49 μ 字符串共 1,155B；没有重新算付款或方程。

两条解析桥的新 source 体积由 prepared manifest 精确列出；后续小的有限消费者可以共享本桥和当前 source 的全部 PT/REG。无需复用 M 的 173KB 逐行展开版本。完整 fixed-case checker 的证明体/实际 kernel 展开代价仍未知，更不能从这些局部数字推出 2MB 全域交付合规。

未来编译只运行两个新模块，复用 prefix.olean 与 QuantizedComponent.olean，不重编前缀。新 isolated lib 中按原模块路径复制两份已 PASS olean 并双端校验，规避已实测的 namespace-root fallback 问题。j1/M13500/stack256MiB/relaxedAutoImplicit=false/Elab.async=false；先失败即停，不自动修复或运行有限数据。必须由 root 再提供 immutable gate。
