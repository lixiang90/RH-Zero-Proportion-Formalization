# 原生冷验证通过后的材料收集准备

这里只准备脚本，没有执行 collector，也没有观察活动生产目录为完成状态。唯一编译和运行持有人仍为 root。旧绑定失败 session 86707 的 collector 不使用。

新版固定 session **84529**、job `/var/tmp/rh-zero-20261015/tiny-production-v2`、生产 gate SHA `3cd2bc378f815b53d5c31233d89662c090b04bcdabc489c115f3a4d66924631a`、生产 prepared SHA `f2ab9d281bf39769da08280f40d9369e9b9ffc2f51c57acccbb116999daa9d74`、flatten-v4 prepared SHA `2b77159157e500b0177c3c2294860830a495248ce3e3b216a813524032509d72`。完整实际源 SHA 只能从真实生成的 metadata 读取，不预填成功。

先由 root 持有的真实工具句柄取得 terminal exit0，并核对 Linux `verification.json`、`deadline-receipt.json` 和 mirror `terminal.json` 均完整、receipt SHA 互相关联、真实最终 stdout 的统一总时间 ≤3200 秒、所有 failure 文件缺席、所有 bound 输入与 runtime symlink 未变。root 在 `research-goal-20261016/gates/` 新建确认文件，按模板保存真实原始终结 stdout 和实际收据 SHA；不能修改模板冒充终结记录。三个确认布尔值必须由 root 在实际审完后置 true。仅凭日志出现 PASS 或活动源已经生成，无法使用 collector。

collector 再独立核对10个阶段的实际顺序、退出码、日志哈希、resources、started/terminal 记录，以及四个冷编译源与 olean SHA。per-stage terminal 在原 runner 中写于扩展 log/output hashes 之前，因此核对共有字段，不要求它和最终 stage 字典完全同形。两个大 export 在原处重算 SHA；Comparator 必须以原生 coreaudit 检查3个公开根，并具有 statement/dependency/primitive、transitive axiom 和 default kernel 成功文本。Nano 必须使用完整 solution export、精确0线程配置、标准3公理白名单与 hard error、完整 Checked 行。允许公理范围和检查范围没有减少。

原生安装路径和 SHA 由已锁 gate 指定；当前安装是 native-tools-v2，SHA `2b636d4a943acfdd44bc14225c3128992c2df634320a6623f735b362e220e797`。collector 检查原始 installation、source provenance、native binaries/runtime closure 与 production receipt 一致，且所有源码/运行闭包和 symlink 绑定仍相同。只生成有明确原始完整收据 SHA 的摘要，不把 ELF、共享库或完整SDK复制进材料。可信工具安装发生在 proof 计时之前；材料明确区分该安装和已经包含全部 proof pins、生成、冷编译、export、双 kernel、最终哈希与 fsynced receipts 的3200秒证明计时。

新材料独占目标为 `submission/single-exception-overlap-native-v4-20261019`。任何已存在目标导致停止；创建后失败写 `COLLECTION-FAILED.json` 并保留现场，0自动重试/覆盖/修复。上传源按字节复制真实 v4 `Solution.lean`；两个 actual generation metadata 原样归档。白名单只复制小日志、resources、JSON收据、3个小规格源码与完整上传源；单文件≤2MB，复制总量≤16MB。NDJSON、olean、ilean、ELF、cache 和 archive 均不进入提交目录或Git。所有 frozen 输入、旧材料与全部 production bound 文件在收集前后再次核 SHA。

数学正文直接沿用 `submission/single-exception-overlap-20261019/MATHEMATICS.zh.md` 的数学部分，κ仍为相同 p/q，仅替换历史运行状态段并保存原说明 SHA；不把原 v0 失败或 v3 单独诊断重新分类。新字段仍只是供用户审核和手动填写的建议，显示名称保留审核标志。新材料中的 `submitted` 和 `official_website_acceptance` 一律 false，网站 pending 单独成文件；不把用户独立上传的旧 v3 网站运行等同本地 v4 的结果。

仅在上述 root 确认之后，可由 root 在 WSL 使用下列形式运行一次；这段命令是待执行说明，本准备不运行它：

```text
/usr/bin/python3 -B research-goal-20261019-native-materials-preparation/collect_once.py --prepared-sha256 <本准备manifest实际SHA> --root-confirmation <root新建终结确认文件绝对路径> --root-confirmation-sha256 <确认文件实际SHA>
```

收集材料在证明完成后进行，其耗时不并入、不缩短、不更写原3200秒收据。collector 不做编译、生成、export、求解、内核、网络、Git操作或官网提交。
