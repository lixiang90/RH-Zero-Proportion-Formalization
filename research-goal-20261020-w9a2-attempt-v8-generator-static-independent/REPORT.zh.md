# attempt-v8 生成器独立静审

结论：在下述有限范围内 PASS_STATIC，未发现确定阻断。这是生成诚实的官网尝试材料的静态审查，不是 v8 编译、数学、资源、双内核或官网通过。

已逐行阅读 `prepare_attempt_v8.py` 全文（0011c4732accb90350cbbd18e0e296a85e045cc07c71de5153dfeb8b608b8b4e），核对禁用模板与 README。准备清单 1f608acb37baa3a5d03c01c1d504e19a4eb172877f850b63120fa8d283f8de21 的三个成员当前 size/SHA 全相符。只用 PowerShell 读文件、解析冻结 JSON 数据、计算直接文件哈希，并写本独审包；未执行 Python、AST、生成器、Lean、exporter、kernel、solver、API、进程查询、网络或 UI，未创建 attempt 包，未修改旧源、材料、脚本、失败归档、root 状态或轮数。

## 路线和实际失败

宏观012当前字节 SHA fb7516e57e8fe56802d16b088178c29215d10161a10060a1e007e2b7a9274347 与生成器常量及模板一致。它明确按人类已有直接尝试授权替代旧的本地 resource PASS 前提，保留失败并让官网原8GB/3200秒完整验证作实际裁决；不授权本地重跑、提高 -M6500、修改 InfoTree、调用旧 ready 生成器或削弱官网验证。

生成器要求 NEW root gate 的 allow=true、proposal_only=false、sole_owner=/root、精确 basis 和自身源码 SHA。当前模板仍为 allow=false/proposal_only=true/generator_sha256=null，不能直接执行。两份失败清单固定为8317a845…与31913ded…，并在实际运行时逐成员校验；静审读取其冻结 outer、terminal 和第二次 stderr，字段与 guards 一致：

- v1 原72573，parent54132/child12924，实际 outer1/child1；旧 commit 线由 ownrunner 主动停止，resource_limit=true、budget_expired=false、resource_PASS=false。
- v2 原93095，parent35104/child5564，原 tool4bb34b 实际 outer1，child3221226505；stderr196B包含 `lean::memory_exception: excessive memory consumption detected at 'interpreter'`。resource_limit=false、budget_expired=false、C生成和resource_PASS均false。

这些失败在新 basis、状态、说明和引用中明确保留；没有改称 OS OOM、数学拒绝或成功。旧 pending 和 PID 误标仅作为历史保留，不再描述为当前活进程。静审不重新判断内存归因或数学内容。

## 原始材料和输出范围

源码固定1829382B/SHA5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b，且与旧prepared-v8 proof直接比较；服务器JSON固定1343B/SHAd88b70050b2a1e1a69d2e1044bcc6a3d1a75c56ab8342f8559f77fe9b270362a，并与旧submission.draft.json比较。完整JSON固定哈希约束原p/q、三个公开根、ID、method、605字符summary、Li Xiang/lixiang90、model=null、harness=Codex及Apache-2.0；另有author/model/harness/summary显式guard。

bundle计算保持 SHA256(`submission.json` + NUL + exact server JSON + `proof/Solution.lean` + NUL + exact raw source)，须等于fb457eecc550ce09bee528294dfff90137631c08e95fa26ffba1e99ec4e11bd4。该值始终标为预期值，不冒称观察到的官方proofDigest。

新目录固定为 `submission/w9a2-weighted-potential-20261020-attempt-v8`，必须事先不存在；文件用xb排他创建。不存在对旧目录的写入路径。LICENSE及源码notices按原字节保留。ATTRIBUTION只在新包纠正首句为真实draft-v8并说明v5→v6→v7→v8继承关系。MATHEMATICS保留历史数学描述，但替换旧pending尾段，明确v8未通过、两个实际失败和官网未上传。继承的mathematical-source-check明确只是历史说明，v8数学验证字段false；source-wire-policy仍明确expected digest不是observed digest。

新状态的普通Lean、C生成资源、Comparator、默认内核、Nano、双内核、单轮3200、官方结果/接受、submitted、upload_ready均false或null。生成器末尾再次核输入不变和输出source/server精确字节，再写新manifest。它只import标准库，不执行旧ready脚本、外部程序、网络或浏览器；metadata生成成功不能推出任何这些验证通过。

## 未覆盖与停止条件

本独审没有执行生成器，不能声称其运行成功、实际输出已存在或输出清单已核；没有再次逐成员复核两个完整失败包或历史19项DRAFT材料，相关原独审36338e03…按既有范围引用。未来实际准备仍须执行其完整输入pins和前后不变检查，并保全真实外层终态。当前官网登录、配额、活任务、最新纪录、实际上传字节、官方digest、job、双内核attestation、promotion和ledger均未在本审查中观察。它们仍由root按宏观012的独立实际交付关处理；材料生成不等于准许盲目重复Submit。

本报告封存后停止，不提出新源码、资源门、hook、编译或优化家族。
