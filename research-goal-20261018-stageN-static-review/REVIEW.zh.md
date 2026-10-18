# N 全剩余 pooled-component 准备稿：独立静态审查

固定 prepared manifest `ce7fdca4ebbce2e82fb915c1f1a3892dec362bff5e4ff8e74ef73de8aa854bd7`。本审查只读六份 Python source、SPEC 和 gate template，记录文件字节/哈希；没有 import/调用 producer、FS、点值、矩阵、秩、solver、核或 Lean，没有独立执行其 AST/preparation，也没有重放 282 项依赖。没有修改 N 或任何冻结包/root 状态。

**结论：在下述固定 scope 内未发现数学符号或闭合范围错误。N 尚未执行，资源 gate、实际结果、完整独立重放与 Lean/source/runtime 交付均未通过。**

## 审过的关键链

- `component_model.py` 保留两 cell 的 144 span 行、9 sep 与2 Ordered；id/rev 只重映射本地 span/gap。原 68 term 来源与 mixture identity 检查先保留，再按物理 span 汇为动态组。组件行来源不丢失，group objective=2Σa。准备时不计算 42/51/full52；运行时从固定 source 重建后断言。
- native p=X/(20Q)、U=T/κ 的目标/行闭式符合原 raw 模型。相同 S 只在 native 约束中保留最大 E，相等取最小原 rowID；同一组 slope normal 相同，所以该支配预处理不改 max。原 raw 行全部保留，marginals 用显式 rowID 扩回零。
- `reconstruct_support.py` 只用 native 正 support；base 按固定最大正 hint 选择。非零 ΔS 除 |ΔS| 得 signed incidence；只解一次 normalized 位置 RREF，再恢复 μ=γ/|ΔS| 与 group base mass。>9 未知、负 hint、缺 group 正质量、同 slope 异截距或不一致都保守处理，不切换支持或精度。相同 slope/intercept 行的质量移回 base 不改余额或成本。
- exact base 质量为零时，正 extra 不推出 tie。代码明确把 native face 等式仅当候选生成；free 位置取原 binary64 的 exact dyadic，T 取全部原组件 max，逐原始 row 检查后才可称 primal 有效。每个合法 primal 还核原单窗 `2κc9N+2Mi` 强 floor；这已经由原 cell 行与 mixture/flow 蕴含，失败应判接线 bug。
- `check_raw_certificate.py` 不调用 RREF/native：重新核每个 raw μ 非负、全部10位置+42T余额与 −Σμrhs；primal 重核全部原 rows/objective。Lower 只需有效 dual 成本≥target，不需 primal 或最优性。Below 需有效 raw primal 且 objective<target，只排除固定 pooled 组件模型；它不是 actual F 反例。invalid/不足支付/仅 native status 归 unresolved，不能宣称非空或家族不可能。

## 完整域、调用与持久化

`discover_complete.py` 固定读取 H 升序 15378 个 original Gindex，不重排阈值/方向。J deduction 由 JLB2 tag、H/J remaining 差及 J 独审绑定；M deduction 明确核独审 `valid_local_Lower`、原 M cells0/604、id/rev 与 index2417/target。M separate Lower 蕴含 pooled Lower。只有 index2417 与5331088复用，其他最多15376次固定 HiGHS 调用，每 case 一次，零 auxiliary/retry。本版 reflection reuse=False，未暗中减少域。

call intent 在真实 LP 前 fsync；native 全记录在 exact 重建前 fsync。每个完整 record 的 gzip member durable 后，才 atomic 发布包含 stream bytes/hash/record counts 与 original index prefix hash 的 prefix。若 hard kill 或失败产生尾数据，只能审已发布字节前缀，不能把尚未 commit 的 native/原组件尾部当 complete case。完整运行须核全 original index 次序、全部 gzip members/EOF、counts/deductions 与输入哈希；这些实际审计本轮没有执行。

首个 exact Below 保存后停止，属于合法部分 scope。完整遍历有 unresolved 仍非完整 floor；`all_range_Lower_candidate` 必须原域全长且 Below/unresolved 为零，并明确 independent replay pending。soft WorkLimit 只报已发布前缀；launcher 一个 child、总 hard time/output 限制、无自动重启，terminal 确认后再处理。输入及外部 runtime 有 start/end pin；不把 SciPy 成功状态作为证明。

## 仍待的关口

当前 template 的总资源限额故意未选定，必须 root 另 gate；每条无损 native、完整 rational μ、原组件 cache 的实际压缩输出和总耗时未知，不能把 M 一次墙钟时间简单外推。source ≤2m、网站总验证≤3200s、全 product cover 与实际计数仍未知。此 code review 不是执行授权、全域有限验证或 Lean pass。

若本 pooled 模型出现 exact Below，下一结构候选是既存 source `w2_nonneg` 证明内的量化 w2 下界，在有效 anchor↔span hull guard 上恢复 tangent 的 μ/2(s−q)²，再将同物理 span 多个 anchor 的平方和写成正平方加 weighted variance 常量。原 FS 强 cell floor 与该余项可合用，无需新 anchor；未具备 hull/curvature guard 的项只能用 μ=0。TVal 的 outside 导数链不自动给二阶界。另一个只用 TVal 的候选是保留同一实际导数 interval 的两线 min/其原区间 chord，而不是独立丢掉端点相关性。两者均尚无数值/全域/预算证据，不在本 N 执行范围；若另开，须单独固定模型和一次必要关，不能以本次 inconclusive 为借口任意换 dual 重试。
