# v7 官网资源与执行路径独立静审

结论：本次已证实的失败是 `Solution.Candidate` 的 Lake 构建步骤在日志标示 1014 秒后报告 Lean 退出码 137，随后 build failed、Comparator 子进程 1、外层 bash 1。它不是已知的 3200 秒 timeout，也没有证明是数学 type error。`2057:30` 是七个 `push_neg` 弃用 warning 的第一处；不能把 UI 的这个位置当作致命证明错误位置。当前日志没有 RSS、cgroup `memory.events`、内核 OOM 记录或发出 kill 的主体。137 与被 SIGKILL 终止相容，但单凭它不能确诊 OOM，不能排除其他 kill 原因，也不能断言发生在 elaboration 或 C emission 的哪一段。

本审查只读现存源、收据和小型 GitHub primary 文件。没有运行 Lean、compiler、exporter、kernel、solver 或数值扫描，没有改候选源、冻结旧包或 round counter。

## 官方仓库配置与实际实例的边界

通过 GitHub 连接器只读取得当前仓库 HEAD `1135c0386310a0a038004d3b0fe64d0237e47dce`，所有后续文件固定此 ref。十二个捕获文件均按 Git blob SHA1 实际核对；来源及准确网址列于 `official-current/fetch-provenance.json`。这证明当前仓库的配置内容，不是本次部署 build ID、环境变量或实际 sandbox cgroup 的证明。

- `e2b/build-template.ts:14–15` 请求 `cpuCount: 4`、`memoryMB: 8_192`。`src/lib/e2b-config.ts:9` 允许 `E2B_TEMPLATE_ID` 覆盖默认名称，当前资料没有实际 template/build ID 及资源读数。
- `src/lib/e2b-verifier.ts:15` 的 sandbox lifetime 是 3600 秒。创建及连接均设置此 lifetime，不能把它等同于证明预算。
- `e2b/run-verification-job.sh:32` 外层为 3240 秒，TERM 后 15 秒可强杀；`scripts/run-comparator-e2b.sh:96` 内层比较器为 3200 秒，同样 TERM 后 15 秒。现行固定数学验证预算仍是 3200 秒。
- 比较器 shell 设置 `ulimit -f 8388608` 与 `ulimit -u 512`，没有设置 `ulimit -v` 或 `-m`。这不表示 sandbox 没有内存限制；template 资源层与 Lean 自己的内存上限是不同控制。
- 官方 shell 使用干净环境与固定 runtime；Lake wrapper 只转发命令并清除已完成模块的 setup 文件，没有注入 `-j1` 或 `-M13500`。准备器只追加 `[[lean_lib]] name = "Candidate"`。`e2b-verifier.ts` 的 progress schema 记录进程数和日志等字段，没有 peak RSS 或 OOM-event 字段。

## 本地成功收据不能作为官网同资源基准

`tmp/w9a2-20261020/fullchain-v2/generation.json` 及 ordinary terminal 绑定旧 v6 源 `a517df6a…`；实际 Windows ordinary 退出 0、耗时 `1150.3280000000013` 秒。其参数为 `-j1 -M13500 --tstack=262144 -DrelaxedAutoImplicit=false -DElab.async=false -R … -o … source`。这既不是 v7 的 `dae01f…`，也不是 Linux/Lake 的相同运行路径。

v7 官网实际 trace 明确请求 `source -o Candidate.olean -i Candidate.ilean -c Candidate.c --setup Candidate.setup.json --json`，没有显示显式 `-j`、`-M` 或 thread-stack 参数。`--setup` 从 JSON 载入模块身份、imports、options 等配置，不应略去为无意义装饰。

同版 SDK `Lean/Shell.lean:552–568` 先调用 frontend，随后仅在 `-c` 被请求时执行 `LCNF.emitC`，得到完整 C 文本再转换 UTF8 写盘。因此官网具有本地 `-o` 命令没有请求的 C emission 分支。两条命令仍可能在 frontend 中生成可执行 IR，不能反过来声称本地完全没有 codegen。日志不足以判断本次 kill 是否已经进入 C emission，也没有该分支的独立耗时或内存读数。`--json` 是消息格式参数，`-i` 请求附加元数据输出；没有证据把七条短 warning 或 JSON 格式归因为 GB 级内存原因。

SDK `Lean/Shell.lean:219–223,237,300–307` 显示未给 `-j` 时，线程数来自 multithread build 下的 hardware concurrency；本次实例的实际返回值没有记录，不能直接把 template 的 4 CPU 等同于四个同时执行的大证明。`-M13500` 设置 Lean 的 `max_memory`，Shell 在 476–478 按 `1024*1024` 换算；它是允许的上限，不是已使用或峰值的证明。官网命令无此显式值，其编译时默认值也不能从本次日志确定。

对现有 `research-goal-20261020-*` 的 JSON/MD/log 及 `tmp/w9a2-20261020` 同类文件作有限关键词检索，没有找到 W9A2 ordinary 的 peak RSS/working-set 数值收据；仅发现 Linux 准备合同描述未来 RSS 观察。这个结论限于上述检索范围，不是声称全仓库、历史压缩包或根代理对话中从来没有内存观察。

已有历史资源收据仍可准确引用，但都不能作为 v7 内存下界：

| 现有收据 | 实测值 | 适用范围 |
| --- | --- | --- |
| `verification/whole-optimized-sync-resources.json` | sampled tree RSS 8,372,035,584 B；Lean working set 8,343,334,912 B；3200.5 秒停止 | 旧 Windows 源 `583c5bec…`，退出 15、编译实验 cutoff，不是 v6/v7 |
| `verification/gram-defect-20261015/lean/resource-manifest.json` 及原 time-v 文本 | Nano modular/single 最大 RSS 分别 7,200,616 / 7,180,896 kB；188.16 / 195.83 秒；均 exit 0 | 2026-10-15 旧导出与 Nano 四线程阶段，不是本次 Lean 构建，也不是 v7 官网资源验收 |

这些历史值说明库和验证阶段可能有显著资源开销；它们不能证明新源需要某个确切 RAM 数值、137 的根因、额外 codegen 的秒数，或增加资源即可在固定时限通过。

## 并发及最小资源改动评议

此处与 formal_owner 分工：本报告固定官方 runtime 与收据边界；其本轮 SDK 静审负责 v7 全源 async 与大定义 codegen，不在这里重复 profiling。其已报告 v7 全局及局部 `Elab.async` 均为 false，SDK proof 路径同步且 LCNF 有 compilation non-parallel 的明确分支。因此不能用“默认线程池更大”推导多个大证明或 codegen 同时运行，也不能把再次设置 `Elab.async false` 当作新修复。`-j1` 仅是运行池的可审单变量差异，当前资料不支持承诺它会修复 137。

当前最小候选资源方向是 root 已选择、由 formal_owner 单独审查的十个 proof-only 数据声明 `PTT_0` 至 `PTT_7`、`PTT`、`PT` 添加显式 `noncomputable`，保持数值、类型与 kernel 可归约定义体不变，仅减少无实际 runtime consumer 的 native codegen。这里记录为待冻结、待实际验证的资源候选，不把建议当作已编译成功、峰值改善或正式接受。其消费者闭包与宏运行边界以 formal_owner 的专门静审为准；本报告不重新扩大扫描。

不建议据目前证据修改固定 3200 秒、削弱两 kernel/公理检查，或把本地 `-M13500` 机械移到 8192 MB template。若维护者另审 runtime 的 `-j1`，必须明确这会改变 trusted runtime 配置，且保留原预算及所有验证；这不是当前候选上传所能自行设置的选项，也不是本次 137 已找到的确定修复。资源候选后续是否执行和提交由 root 的新 gate 决定，本审查没有发起任何批次。
