# 最终结果：官网已验证并收录

本次无条件渐近比例下界为 **67.3587173312944342020759392480%**，已成为官网公开纪录，作者 **Li Xiang / lixiang90**。相对提交前纪录严格提高，精确分数与增益见 [strict-improvement.json](strict-improvement.json)。

[完整单文件证明](proof/Solution.lean)为官网接受的原 v3：**1,979,280 字节**，SHA256 `024902a7ef01ccba2a6c71e54682a31712417e5d3c0b4ead5f6f80ad25fd1a81`。它与官网公布源码、用户原上传文件逐字节相同。公开 manifest 和源码重算的任务 digest 为 `23e3dd765aa27de76938e056f13d3e0f08d849d0e7c39c6f78c62e7640c0a10f`，与用户任务完全匹配。

新增数学结构是相邻九点/八 gap 窗口的唯一例外不能同时发生：共享 gap 在四种反射朝向下均被迫落入不相交区间。由此加强相邻窗口能量和，再以固定边界亏损转移到实际零点计数，得到无 Riemann 假设或额外局部 floor 前提的 dyadic 与 cumulative 结论。[数学说明](MATHEMATICS.zh.md)保留完整论证与精确常数。

[官方验收记录](official/attestation.json)的 verifiedAt 为 `2026-10-18T17:50:12.033Z`，状态为 `kernel-verified`，核为 Lean、nanoda；[官方日志](official/verifier.log)明确记录两核接受及三个公开定理只使用允许的标准公理。固定官方策略为 Comparator 3200 秒、外层任务 3240 秒；公开资料未给出精确总耗时，单独的编译耗时不能视为总耗时。

[官方公开源码](https://github.com/josusanmartin/riemann/blob/6bc7f07fb939e066ac2923493d9a01cca553fe87/submissions/lixiang90-single-exception-overlap-20261018/proof/Solution.lean)与[官方验收记录](https://github.com/josusanmartin/riemann/blob/6bc7f07fb939e066ac2923493d9a01cca553fe87/submissions/lixiang90-single-exception-overlap-20261018/verification/attestation.json)均位于同一不可变接受提交。

历史记录保持原样：本地 v0 的 3200 秒超时没有改为 PASS；备用 native-v4 已在官网接受原 v3 后由 root 取消，非数学反例、非整轮 PASS。早期 README 中“运行中的 native-v4”一语由本最终状态更正。最终交付使用本目录原 v3，原 pending 材料与冻结清单不覆写。新增官方日志及本说明由 verification-addendum-files.json 绑定；工程仓库最终全树同步回执另保存。
