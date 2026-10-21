# v16 官网验收补记（2026-10-21）

官网于 2026-10-21T12:02:11.696Z 接受 Li Xiang / @lixiang90 的 `lixiang90-w9a2-point-center-v16-20261021`，Lean 默认内核和独立 nanoda 均通过。三项公开定理仅依赖 `propext`、`Classical.choice`、`Quot.sound`，给出实际零点计数的无条件 dyadic 和 cumulative 比例结论。

精确比例为 5468785278184175322207229683562307584 / 8118842181460468609667905735697265625，约 **67.35917703477782944%**。较此前 H33 纪录增加约 **1.020399621 × 10⁻⁸ 个百分点**，这是极小的严格提高。

[源码与原始提交包](../w9a2-point-center-v16-20261021/README.zh.md)保留生成时状态；其中 `submitted/official_acceptance` 等 false、unknown、null 是提交前快照。此补记单独记录之后发生的真实验收，不改写旧快照。

本目录的 [attestation.json](attestation.json) 和 [verifier.log](verifier.log) 是[官网不可变证据](https://github.com/josusanmartin/riemann/tree/aaff49408a7fd7561e5023f9c908604b5fda5b06/submissions/lixiang90-w9a2-point-center-v16-20261021)的原始公开字节；[record.json](record.json) 与 [previous-record.json](previous-record.json)取自[官方提升提交的账本](https://github.com/josusanmartin/riemann/blob/0423147a64f4b14cdf895c4d0574a0af60bfcc01/data/records.json)。P 的唯一父提交为 E。完整摘要、上下文摘要、精确比较范围见 [official-public-receipt.json](official-public-receipt.json)。该账本的 39 个合格精确分数中本次为唯一最大值；一个历史条目缺精确分数，其公开小数低于 H33。

源码 1,833,816 字节，SHA256 `cc480ccf11ee3416410abc3d2af19afbeb76d49d00c636257bae88d02e4a72e6`，与官网原始源码逐字节相同，低于 2,000,000 字节限制。官网公开 manifest 与源码重算 wire 为 `0cef2c7a041cc705246184c904c0c5c53ca2286bfbd8d540ec957a65f82974a0`。attestation 不含 proofDigest 字段，重算值单独标注。

整源内存异常经过定位及资源合同审查后，本地内部限制由 -M6500 明确修订为有限 -M7168（+668 MiB），观察峰值拒绝阈值仍为 7 GiB；本地单次整源通过，峰值约 6.92 GiB。官网双核通过由上述公开证据证明。日志中的 976 秒只是 Solution 构建阶段；官网总流水线时间与峰值内存未公开。旧失败、旧资源合同及旧材料不改记成功。

署名、继承归属及 Apache-2.0 许可见原提交包；本目录仅包含已公开的官方证据与说明。
