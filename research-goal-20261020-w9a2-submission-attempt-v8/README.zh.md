本目录只准备新的attempt-v8 metadata生成器与禁用模板，尚未执行Python、AST、生成器、Lean、API、网络、UI、Git或任何新验证，也未生成attempt包。旧ready-v8生成器永不调用；其真实PASS条件已经失败，不能用本流程伪装满足。所有旧源、脚本、失败、DRAFT/pending快照、root state/counter均不改。

新路线的依据是固定宏观012（fb7516e57e8fe56802d16b088178c29215d10161a10060a1e007e2b7a9274347）协调用户已有“不再重复核查、直接提交尝试”的明确授权，带已知local soft6500失败选择官网原8GB/3200完整验收。它替代旧本地PASS前提，不改失败flags，不本地重跑或提高-M6500，不用会panic的裸InfoTree关闭，不改fixed证明源。这是授权尝试的依据，绝不是local PASS或官网接受。

gate-template仍allow_attempt_material_generation=false、proposal_only=true、generator_sha256=null。未来root必须先审/冻NEW enabled gate，精确绑定生成器、macro012、DRAFT独审36338e03…和两个实际失败清单8317a845…/31913ded…。缺任一pin、原失败事实不符或目标已存在均拒绝；此模板不授权执行。生成器不import/exec旧ready脚本，不调用编译或内核，不查询进程/当前网站。

实际失败会在新attempt材料明确保留：v1原72573，parent54132/child12924，outer1/child1，旧peak-commit线由ownrunner停止，非确认OS OOM或数学拒绝；RSS-only v2原93095，parent35104/child5564，原tool4bb34b outer1、child3221226505，stderr196B为lean::memory_exception at interpreter，非runner阈值/timeout，C生成未完成。只读取已冻归档，不读取活输出或重放检查。

新输出目录固定submission/w9a2-weighted-potential-20261020-attempt-v8，raw proof5424212b…/1829382B、serverJSON d88b7005…/1343B、expectedwire fb457eec…完全不变；author Li Xiang/lixiang90、605字符summary、原method/pq、model=null、harness Codex与许可保留。ATTRIBUTION仅在新包首句纠正为实际draft-v8及v5→v6→v7→v8继承关系，嵌入源码notices与LICENSE原字节保留。

新verification-status全部资源/PASS/普通Lean/完整3200/独立双核/官网/上传ready标志仍false或unknown；新当前状态为“两次本地资源尝试实际失败”，不将旧pending继续当active。MATHEMATICS仅为固定源码所声称的数学内容及历史说明，不当作新本地通过。新包尚未上传/未接受/双核未完；官方完整验收未来actual结果另立addendum，不改源。

prepare_attempt_v8.py只在未来NEW gate授权后进行纯文件复制、直接hash、元数据写入。它将输出official-attempt-basis.json、明确失败的状态及expected-wire.json；不会把任何原false验证flag翻true。此时只封准备清单并交独立静审，等待root正式门。
