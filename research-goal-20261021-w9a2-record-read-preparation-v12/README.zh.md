# K33/v12 未来公开 records 只读 reader；未执行

本包从原 v1 reader 精确派生，仅四个原始 byte spans：版本说明、独立输出前缀、固定 K33 与 not-before 常量、main 中 GET/输出目录创建前的本地时钟门。逆投影精确回到原 SHA ab7d72c479f481b08adcf7885fbcc252bd9fe551c5a34742459c7bbc080c82fd；其余网络/解析/比较/保存/退出代码全字节不变。旧 reader 的 K 已落后，不得用于 v12 鲜核。

固定 K33=10937570556368350644414459367124615168/16237684365380724838807895177884765625。此 reader 不包含任何 Lean 证明或资源 PASS 声明。新 H 算术实际通过由 root 独立保存，不是本 helper 的网络执行证据。

未来 root 明确授权后 CLI：`python -B research-goal-20261021-w9a2-record-read-preparation-v12/read_public_records.py --output NEW_LEAF`。这只是说明，本次没有运行此命令或 --help。输出固定在 `research-goal-20261021-w9a2-record-read-v12-output/NEW_LEAF`；要求简单、全新 leaf，拒绝已有目录/符号链接，绝不删改/覆盖旧输出。脚本从自身新 sibling 目录的 HERE 加载本包 pre-execution-files.json，仍只校验同名 reader/README 两个 allowlist 成员、preexec 本身和原两份 captured rule/schema pins；无需编辑冻结清单才能获得 root 日后的单次授权。

not-before 固定 2026-10-21T00:00:00Z（epoch ns1792540800000000000）。在 main 的首次 time.time_ns() 后、解析 CLI/读取 pins/建立输出目录/建立连接之前检查；早于该本地时钟边界则 preflight 非0、无 GET、无新输出。它不读取官网，不证明额度已重置，不替代 root 的 fresh 认证/额度/无活任务检查，也不安排自动唤醒或执行。没有 root 单独授权，即使时间已过仍不得运行。

网络策略保持原样：唯一 GET 到公开 GitHub contents API 的 main records.json，加 nonce/no-cache；不发 auth、不 redirect、不 retry；HTTP raw body上限2,000,000B并先保存/fsync，再解析 JSON，Date只作 plain string。验证 canonical base64、size 和 Git blob SHA1 后保存 decoded records。总采纳预算30s，analysis上限256KB。DNS/fsync/print不是硬实时；root必须观察真实 outer0且整次 elapsed≤30s，落盘正收据不能代替真实退出。

当前记录规则仍绑定 captured records.ts（1135c038）：critical-line 原数组最后 kernel-verified，否则最后 published；不按日期或小数排序。K33 必须严格超过当前 exact 与所有已知 critical-line/kernel-verified exact 才通过限定门。缺失 exact 完整列出为 unknown，不由 decimal/expression 补分数；不宣称已比较未知项或已完成全目标。此次准备不读取当前网络 ledger，旧 41/38/37 仅历史，未硬编码。

本次只做新 reader 文本生成、raw 正反投影和 ast.parse 语法检查。没有 import/执行 helper module body、main、网络、process查询、UI、Lean/compiler/kernel/export、Git/state修改或大 runtime 树读取。将来任何 HTTP/schema/hash/比较失败仍保存其真实已有 raw/small receipt 并停止，不自动改 K、重试或换读取路径。
