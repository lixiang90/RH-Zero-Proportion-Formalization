# H33 零点比例新纪录：正式接受材料

本次以 **Li Xiang / @lixiang90** 提交，官网已于 **2026-10-21T02:52:42.396Z** 完成验证并正式发布。模型字段为 null，harness 为 Codex，源码采用 Apache-2.0。

精确新比例为 `10937570556368350644414459367124615168/16237684365380724838807895177884765625`，显示百分比为 `67.3591770245738332299780842385%`。相对提交前的 `attempt-030`，精确增益为 `114688/16237684365380724838807895177884765625`（比例约增加 7.06×10^-33）。显示的有限小数可相同，纪录按精确有理数排序。

这次保留 Samuel Lavery 的 attempt-030 九点窗口、权重、完整证书、c/B 及三角有理界，只将终端 H_W 下界从 `67212374687824171413662471723172/10^32` 精化至 `672123746878241714136624717231727/10^33`，并传播到原有实际 dyadic 与 cumulative 零点计数证明。全部原有归属与许可声明保留，新增 Li Xiang 变更说明。

正式验收覆盖 `candidate_strict_improvement`、`candidate_critical_line_bound`、`candidate_critical_line_bound_cumulative`，不是数值或局部模型替代。公开 attestation 为 `kernel-verified`、kernels `[lean,nanoda]`，允许公理仅为 `propext/Quot.sound/Classical.choice`；公开 verifier.log 末尾实际记录 Nanoda 接受、Lean default kernel 接受和 `Your solution is okay!`。日志中的 `Solution.Candidate (1090s)` 是构建阶段耗时；没有单独公开整轮同钟耗时或峰值 RSS，不能把 1090 秒说成整个流水线。官网成功结果对应原 3200 秒验收策略，本地没有再重跑旧证明或内核。

公开证明逐字等于已准备和事先同步的 1,799,144B 源码，SHA256 `a3b0ee880a647539e4bdb65a31e693de5b8e2e5ad085ec46ebbd031319a848cb`，低于 2,000,000B。实际公开 manifest+source 组合摘要为 `c0c3df2ca61fc0a55fb6a66d5ce865e803b8d9d67a0f2d22655f13b5a08ca1db`，与上传准备值一致。

不可变证明提交 E：[`9ab832ca`](https://github.com/josusanmartin/riemann/tree/9ab832ca9c2414b086c39dd9e5a4e4ee45bd5f61/submissions/lixiang90-w9a2-hw-rounding-v12-20261021)。实际发布账本提交 P：[`78d0557b`](https://github.com/josusanmartin/riemann/commit/78d0557b1b83136a5cc8b4e2af8d84bce29b5dc1)，其 parent 正是 E，变更的 records blob 为 `18e993ebcab4979f44e7e389383fcfad064ea3c2`。账本条目唯一，作者、精确分数、正式状态与 E 下的 manifest/proof URL 一致；其分数是当次公开账本中全部可做精确比较的合格 critical-line 记录的最高值。缺失精确分数的历史项保留未知范围。

本目录只收录官网已经公开的四文件、公开账本选取条目、归属/许可与本说明。独立源码上游的项目检查点为 `0430f759a1e634bf38d3ae0da16ddd237f0c4c36`，源码本身未因验收而改写。历史 DRAFT、失败/中断回执均保持原字节。官方 attestation 中的上下文摘要予以保留，不冒充另一次独立重算当前部署上下文的结果。
