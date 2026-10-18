# 单例外相邻窗口法：提交材料草稿

本目录供用户 review 和填写网站字段。它不执行上传、不更换正在网站运行的版本，也不
宣称网站已接受新纪录。后续网站状态另存新 receipt，保留本目录冻结时的状态。

候选精确比例：

```
3337839448633819172184136761695440236797
------------------------------------------------
4955319193827760237900000000000000000000
```

约 **67.35871733129443%**。相对本次绑定的网站基准，分子相同、分母较小，因此是严格
有理改进；实际比例增量约 0.000000000002647，即约 0.0000000002647 个百分点。
提交前后仍以网站的最新可信纪录和最终 verifier 结果为准。

可用的主证明源是用户已上传的不可变 **v3**，不是新去重版，也不是本目录的复制件：

[打开原 Solution.lean](../../research-goal-20261018-tiny-flatten-preparation-v3/draft/Solution.lean)

仓库相对路径为
`research-goal-20261018-tiny-flatten-preparation-v3/draft/Solution.lean`，
**1,979,280 UTF-8 bytes**，SHA256
`024902a7ef01ccba2a6c71e54682a31712417e5d3c0b4ead5f6f80ad25fd1a81`。
本目录没有另存这份约2MB源码。所有继承版权、归属和许可均在该源中保留；材料不改变
原贡献者或已绑定的证明源。

字段建议见 [website-fields.draft.json](website-fields.draft.json)，数学说明见
[MATHEMATICS.zh.md](MATHEMATICS.zh.md)，逐项验证边界见
[verification-status.json](verification-status.json)。姓名、方法和摘要是供 review 的
字段草稿；GitHub认证身份由网站决定，本目录不声称或覆盖登录账户。

当前已保存证据支持：完整单文件普通 Lean、Comparator 的精确 statement/依赖/
primitive 比较、传递公理与 Lean default kernel 均 PASS；同一 solution export
另行完成独立 nanoda 重放，**75,371 declarations、427.389541876秒**，仅三个标准
公理 `propext`、`Quot.sound`、`Classical.choice`。

这些通过不能合并成一次3200秒冷流程通过。原统一 cold-v0 在 nanoda 阶段只剩
352.0973792110003秒，随后总计时3200.015159496秒超时，整体 **FAIL**；后来的 nanoda
PASS 是单独诊断，未改变这次失败。新去重源的静态审查也不替代该v3的生产时间要求。

网站状态仅采用用户已报告的 **running**，digest
`23e3dd765aa27de76938e056f13d3e0f08d849d0e7c39c6f78c62e7640c0a10f`。
它不是源码SHA，不表示最终接受；本次材料整理没有查询网站或运行 collector。

网站操作说明：已有这份源的 running job 时，等待并保存该 job 的最终结果，不因本
草稿自动再次提交。若用户另行决定提交，文件选择上述原v3路径，精确 numerator/
denominator 从字段草稿复制，不填写小数分数；先确认网站最新纪录仍低于候选。不要把
材料目录、JSON、模块集或尚未完成验证的替代源当作该已绑定 Solution 上传。

`files.json` 只锁本目录稳定文件。外部证据的路径和哈希在 evidence-references.json
内作为引用保存；将来的最终网站状态另建带时间、job/digest和原始响应的新receipt，
不覆盖本目录中当前的 pending 状态。
