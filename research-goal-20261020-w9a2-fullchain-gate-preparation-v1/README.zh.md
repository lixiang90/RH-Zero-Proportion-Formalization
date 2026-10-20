本包只准备 disabled fullchain gate 组装器，不改已封的 `verification-preparation-v1/run_verification.py`，也不运行任何 compiler、exporter、kernel、下载或 source generator。它不能写授权 gate；所有前置证据真实完成且核同后，仅输出 `allow_verification_execution=false` proposal。原始无条件比例、新纪录、完整单文件、双内核、3200 秒和官网接受目标全部保留。

最终输入由 root 的新 request 绑定 delivery 目录下最终已封 draft 的 manifest、完整 Solution bytes/SHA。request 模板故意不预填尚未完成的 draft；生成器必须拒绝未封、不匹配或超过2,000,000B的源。最终各模块的预检 source SHA 直接匹配该 draft；完整Core仍限定已独审 c2af…，对应开发split26e2…和原Prefix bfd7…。本包仅读取 manifest、参数及文件 hashes，不生成、切割或复制 proof source body。实际 fresh source、trusted CandidateSpec/Challenge 与 fresh lib 全部留给冻结 runner 在同一3200秒deadline内完成。

普通预检采用request的显式阶段链，不要求所有模块来自单一批次。既有实际证据为v0/session68239/parent39800/gate3960…整批exit1但Prefix PASS；v1/session93720/parent40416/gate92de…整批exit1但修复后Core PASS；v2/session42867/parent24036/gate5906…整批exit1且Graph失败；v3/session46495/parent40528/gate8c89…整批exit1但Graph PASS、Loc失败。后续同数学显式proof修复阶段必须有新的root授权gate、实际internal terminal与对应外层真实父handle退出。失败批次按实际exit1保留，不升级整批PASS；仅其失败前的具体PASS模块可贡献开发证据。每份开发reused olean必须逐一映射此前真实PASS产物的相同path/module_path/SHA。

组装器独立核所有已完成target的source/olean/log/command/child/receipt，按request选择恰好Prefix/Core/Graph/Localization/Counting/Final六个真实PASS来源；选中source必须与最终draft一致。Counting五根与Final七根共十二根直接重新解析真实日志，严格匹配标准公理集合。最后一个显式阶段还须真实整批PASS/actual parent exit0。支持原普通runner09b7…与仅修正同SDK进程查询范围的scoped runner6330…，不接受任意新执行器。旧trusted ChallengeDeps同样仅为开发预检。生产LEAN_PATH不包含这些开发lib，没有olean复制或复用。

runtime接口已与runtime-closure-v1负责人协调：closure.json保持冻结runner的w9a2-trusted-runtime-closure-v1，额外含package_root和完整runtime_gate_fragment。固定九个candidate package lib必须位于统一clean package-overlay，允许额外同固定commit的Cli目录（当前assembler按source字典创建，未import时为空）；顺序去除Cli后须等原九个。Zeta lib只保留Zeta23/，旧root ChallengeDeps不得进入。单个interpreted tool-overlay恰有Comparator、Axioms、Compare、Util、Export/Parse五个olean，包含nested原来源的Parse。每个overlay数据文件必须在closure.files绑定；拒绝native/cache注入与用户olean污染。完整source/SDK/cache/PE/实际Python pyd/WSL loader来源由runtime assembler及root实际审核负责；本包不会把incomplete改成complete。

runtime的trusted_setup_receipt还须含实际assembler_pid、assembler_sha256、proof_runs=0、user_proofs_compiled_or_reused_in_setup=false。root必须保存该次assembler实际外层terminal exit0，而非只接受receipt自称未来会exit0。本包observation模板接受root保存的原始exec_command/write_stdin返回对象，须含真实exit_code与output，并与原session/parent/runner/completion pin对应。ordinary还接受root已封存的原handle退出attestation：archive_manifest、archived_job_directory、root_attestation三字段，先核整份archive manifest，再比较started/terminal副本与真实job完全一致，核root记录的原session和actual exit。v0/v1的原记录就在archive files.json，v2在graph-repair-v2/repair.json，v3及以后可用root的record_ordinary_stage.py产生的root-parent-exit-attestation.json。不会只靠内部terminal、失踪PID或未来退出声明推断成功。失败批严格要求实际1，成功批和setup严格要求实际0。root对原始外层handle观察的保存是明确的信任边界，JSON本身不能证明自己来自工具。

freshRecord接受root新取的HTTP原文与receipt，不联网。它核对HTTPS官网/api/leaderboard、status200、bytes/SHA、带时区取回时间、最多900秒龄、critical-line kernel-verified exact rational最大值，要求仍为固定基准且candidate严格更大。全部input hash审核后再次检查年龄；过期、竞品纪录变化、没有覆盖全部模块的actual PASS链、缺失真实父退出或runtime不完整均拒绝输出。root可复用现有runtime/fresh_record_v1.py进行一次明确的新读取；此处没有运行。

root在所有前置进程结束并审好runtime后，填NEW request、各阶段和setup observations，保存raw工具结果并计算各SHA，再调用：

```powershell
C:\Python312\python.exe -B -X utf8 research-goal-20261020-w9a2-fullchain-gate-preparation/assemble_gate.py --request ROOT_NEW_REQUEST.json --request-sha256 ROOT_EXACT_REQUEST_SHA --preparation-manifest-sha256 ROOT_EXACT_THIS_PACKAGE_MANIFEST_SHA
```

成功时 exclusive 新建 request 指定的 proposal 目录，fsync 三个 JSON：`bound-inputs-manifest.json`、`gate-proposal.json`、`assembly-receipt.json`。该 manifest 将原冻结 runner 七项、本包、draft、ordinary 真实日志/receipt、外层 handle evidence、freshRecord 与 closure 来源等绑定进未改 runner 已有的 `bind`/`immutable()`；closure.files 已由原 `setup_runtime()` 全量绑定，不在初始 manifest 再重复整套 SDK/cache walk。完整3200秒合同、源码重生成、4个普通编译、2个native export、锁定CoreAudit的statement/dependency/primitive/axiom/defaultLean检查、serialNano及三份真实fsync收据均不变。

root 审查具体 proposal、证据、当前唯一进程所有权与 OS trust boundary 后，另写 NEW gate，只将 `allow_verification_execution` 改 true、`proposal_only` 改 false、`runtime.root_reviewed_complete_runtime_closure` 改 true；计算新 gate SHA，再明确启动原冻结 runner。组装器不会进行这些授权或启动动作。最后还必须由 root 实际外层 handle 观察完整 production exit0，并保存 terminal hash；内部三份收据不替代该观察。组装器本身也不声称自己的未来退出。

准备阶段仅做AST/JSON/固定pins静审；真实ordinary覆盖与runtime setup尚未满足时，没有输出任何可执行或已通过gate。主研究轮计数不变。官网作者按用户明确授权固定Li Xiang；完成全链验证后的实际提交由root执行，此处无提交或接受声明。


本v1仅修复原cd24…封包的历史失败日志解析阻断：printed_axioms只parse，允许失败receipt诊断中的sorryAx占位被保留为rejected；只在真实PASS分支严格要求axioms为ALLOWED子集。failed仍须该阶段最后一项、whole-stage实际exit1、observed字典等失败receipt，选中模块仍必须真实PASS且source精确等最终draft。派生gate额外列rejected_failed_module_diagnostics，accepted_as_proof固定false。不会接受旧Final的sorryAx，也不改变完整production gate/runner/内核合同。原包逐项核不变；本v1没有运行assembler或proof。
