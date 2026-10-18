# 成功冷验证后的材料收集准备

本目录只准备脚本，不执行材料收集，不读取尚未结束的任务为成功，不改任何已绑定输入。生产 session 86707 的状态由根作为唯一 owner 确认。若它失败或超时，不能执行本收集器，也不能使用中间 verification.json 包装成成功材料。

根须先保存真实 terminal tool result 的 exit_code=0 及最终 stdout JSON，并填写一份新的 root confirmation 到 `research-goal-20261016/gates/`。其中 `confirmed_by=/root`、session=86707、退出码0、真实终端输出以及 reviewed collector prepared SHA 必须绑定。不能把 template 本身当成功确认。

`collect_once.py` 只运行在 Linux/WSL。首先验证自身 prepared 和冻结依赖，要求目标 `submission/single-exception-overlap-20261018` 不存在。随后要求：

1. 根确认 actual terminal exit0，stdout 的总耗时为正且≤3200秒；
2. Linux verification、deadline receipt、仓库 mirror terminal 三者相互 SHA 一致，预算和成功字段全真，无任何 failure.json；
3. 四个冷用户/可信规格模块、九个可信工具模块、十九个顺序阶段全部真实 exit0；日志 SHA 和资源 RSS 与 receipt 一致；
4. Comparator statement/dependency/primitive、公理闭包、默认 kernel 的三个成功行都存在，nanoda 声明确实检查完毕，公理集合只含标准三项；
5. nanoda 的硬错误设置没有放开允许公理；两个 NDJSON 原地核大小及 SHA；
6. flatten 上传源、cold Solution.Candidate 源、generation 和 verification 的 SHA/字节大小完全一致，源≤2,000,000 UTF-8 bytes；
7. 候选和比较基准是冻结的精确有理数，且候选严格更大。

全部门通过后，才独占创建新提交目录。以二进制逐字节复制上传源至 `proof/Solution.lean`，复制小型日志/资源/receipts 和本地 trusted overlay 的三个小源作审阅证据。每个证据文件≤20MB，整个复制清单≤64MB；NDJSON、olean、ilean、归档及 cache 不会进入材料。原 NDJSON 的原地复核属于验证完成后的打包核对，不冒称包括在生产3200秒内。

新输出包括 submission-fields.json、README.zh.md、MATHEMATICAL-NOTE.zh.md、verification-status.json 和逐文件 SHA/大小 manifest。所有提交/官方接受字段恒 false；“ready_for_manual_website_submission”只表示材料已完成本地冷验证，网站仍须按最新合同实际验收。所有源版权和许可按原字节保留。旧 `submission/tiny-overlap-20261018` 草案的两份冻结文件在前后均复核 SHA；本脚本不写旧目录或任何原输入。生成中途失败会留下 COLLECTION-FAILED.json，绝不覆盖、自动修复或重试。

未来根执行命令形状（本准备未执行）：

```
wsl --distribution Ubuntu --exec /usr/bin/python3 /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/research-goal-20261019-tiny-materials-preparation/collect_once.py --prepared-sha256 REVIEWED_COLLECTOR_PREPARED_SHA --root-confirmation /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/research-goal-20261016/gates/ROOT_CONFIRMATION.json --root-confirmation-sha256 ROOT_CONFIRMATION_SHA
```

本脚本不运行 Lean/export/求解器/网络/Git，不提交网站，也不把本地 PASS 说成官网纪录。GitHub 同步与最新网站纪录复查由根另外完成。
