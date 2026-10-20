# Replay-only v1 独立静审

结论为 **PASS_STATIC**：对冻结的 `run_replay.py` f9048bc8…、禁用 gate 0837b097…、准备清单 d5552f25…没有发现当前确定的执行阻断或数学检查削弱。这不是重放执行通过；本代理没有执行 runner、SDK API、Lean、exporter 或 Nano，没有触碰主轮计数或任何冻结文件。

原实际失败范围已独立核对：macro008 的 SHA 为 ce010248…；`fullchain-v2-terminal/files.json` ae3eb7e1…下 41 个小归档文件的字节数和 SHA 全部一致。原 session68962/PID49320 的真实父句柄 exit1，TimeoutExpired 总耗时 3200.578 秒。普通单文件及两个导出完成，15 个打印根只使用三个标准公理；CoreAudit 未完成、Nano 未开始。保留的 1 GB 导出对象不是此次小归档的副本，本独审没有重新读取这些大对象。

新 controller 要求新的明确 gate，且只允许从禁用提案改变两个授权布尔值。新工作目录必须不存在。它绑定旧 gate、失败归档及原 outer exit1，检查原四次普通编译、15 个根、两个导出实际 exit0 的完整收据和 SHA/大小/输出路径/三公开目标。既有源码与冻结提交源码的实际 SHA 均由本独审重新算得 a517df6…，大小 1,830,052 字节；新 runner 开始和结束还会实际散列这些源码与两份导出。候选 `.olean` 不进入新的导入路径。

运行库选择已用独立标准库 metadata/AST 计算复核：14,194 个原 closure 成员，声明总量 2,473,438,841 字节。其中保守保留完整官方 SDK 的 13,951 文件、2,404,331,570 字节，另有五个工具 `.olean`、可信工具源码、Python/PE/ELF 和 Nano 来源，包含原 17 个 UNC 文件。未选 Mathlib、Zeta、package overlay 或 Candidate 数据。新 gate 的 runtime 字段逐项等于原已审 gate；完整 source-cache/SDK 来源链复用旧 closure，当前选中数据则由新 runner 前后实际核 SHA。本独审没有替 runner 读取这 2.47 GB 数据，也没有声称当前重新核完原 17 万数学包文件或具有官网运行时等价性。

CoreAudit 的原 7e88e84d…源保持不变，实际计划调用一次可信 `lean --run`，单列计数。其环境只有固定 SDK 与五工具 overlay；默认内核重放、statement/dependency/primitive 比较和传递公理检查均保持。只有实际 exit0 且原三条完成消息全出现，才启动 Nano。Nano 配置通过独立 AST 字面计算与原 92cc runner 逐项相等：num_threads=0、三允许公理、未知公理硬错、unsafe=false、原扩展和完整成功打印。Nano 仍经 `setsid --wait`、完整 solution export stdin，要求实际 exit0、正声明计数和标准公理集合。

新 3200 秒从 `main` 开头覆盖门控、输入/运行库核对、两重放、后验 SHA 和三份 fsync 收据；原进程/deadline/cleanup 方法来自精确 92cc Python 源，非 main 导入，不调用原 ordinary/export/execute/finish。新收据明确候选编译次数0、exporter次数0，而可信 CoreAudit Lean 调用计划1。新任务失败后停，不修补或重试。完成仍须 Root 观察新原父句柄实际 exit0、复核 terminal SHA 并确认没有 failure；源码中的将来 exit0 提示不是外层实际观察。

两项非阻断范围澄清：README“只读取旧 closure 一次”应理解为 JSON 解析一次；实际仍有前验 SHA、解析读取和后验 SHA，全部在新预算内。新 work path 使用 lexical absolute 校验；本独审实际复核其现存父目录 canonical 为本项目 `tmp/w9a2-20261020`，且目标叶目录不存在。

所有新收据的 `cold_full_3200s_passed`、`official_website_acceptance` 和 `submitted` 均保持 false。即使数学重放实际通过，也不会把原 cold3200 失败升级；最终仍须同一 a517 源获得官网固定流程实际接受。旧 collector 不适用于本重放。

具体静态检查数据见 `review.json`，本次实际小文件 pins 见 `files.json`。`baseline-evidence.json` 保留此前原失败范围核对，不修改。
