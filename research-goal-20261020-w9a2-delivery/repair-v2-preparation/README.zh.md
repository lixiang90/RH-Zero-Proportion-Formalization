本包仅独立逐字审查 Graph proof 修复，并从 frozen draft-v1 生成 NEW draft-v2。没有运行 compiler、exporter、kernel、solver、下载或安装，未改旧 canonical、draft-v0、draft-v1 或其 manifest。

Graph 修复包 `research-goal-20261020-w9a2-graph-repair-v1/files.json` SHA `a7a9b9090f51919d3f07276a758e333fed135f98a7b854dbe84f755bc4f0de19` 的18项 bytes/SHA均独立核同。新Graph为17,366B，SHA `9877394187460ee686e31561fe8f1ccb5015eb29fa2b7f5c2565071351add00c`。唯一区别是 `reverse_span` 第151行在原 norm_num 与 ring 之间加 `<;> simp only [Fin.reduceFinMk]`，增加32字节，保留原CRLF。实际SDK固定源码确认这是 builtin Fin simp reduction；此处不推断新源必然编译通过。

新源与旧源通过唯一 proof 行双向逐字回投，定理statement及其余全部字节相同。因此所有定义、literal、134 edges、2267 exclusions、StateAt、cost和threshold不变。Core使用已冻结v1的完整Bool修复源；Localization/Counting/Final及整个wrapper、trusted模板、CandidateSpec与ChallengeDeps均逐字从frozen v1读入。三个public types与原wrapper完全相同，去除空白后仍等captured official types。

`../draft-v2/Solution.lean` 为1,829,987B，SHA `43cfdfddf4282e29c5f7f251ce6b33462964919173104efe0533438097c5107b`，源码余量170,013B。`../draft-v2/files.json` SHA `4bdee1454b87659360f845d9e62c6d842002a10edfa359d24c28f80a714f5f20`，含18项。v1flat→v2flat也恰是同一Graph proof行+32B；逆投影逐字等v1flat。详细证据为draft-v2的source-review.json、source-origins.json、Solution-v1-to-v2.diff。

`generate_draft_v2.py --freeze-once`仅执行过一次文本生成，目录已存在时拒绝再运行或覆盖。官网提交材料作者按用户最新明确授权填写Li Xiang；实际官网操作及身份核实由root在完整验证后执行。本包不声称ordinary Graph、完整单文件、Comparator、双内核、3200秒、官网接受或原目标已完成。
