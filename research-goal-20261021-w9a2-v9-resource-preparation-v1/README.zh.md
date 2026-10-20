# 固定 v9 的未启用资源测量准备

本包从冻结 v8 resource-preparation-v3 的 runner 复制，仅适配新 v9 身份、协议名和首次独占目录。原 runner SHA256 为 `d47d98607df23d7711176116ce62fa13d85925f5c634af1175cc74ef7b3ad880`。9 个精确文本替换、offset 与正反投影见 `exact-runner-diff.json`；小 patch 另列实际变更行。没有运行 Python、import、AST、--help、runner、Lean、compiler、native API、版本探测、export、kernel、网络、UI 或 Git。

固定源由 root 指定为 `research-goal-20261021-w9a2-delivery/draft-v9/Solution.lean`，1861120 字节，SHA256 `7552bbb829b86986798b58cf40caf998ea8c51ab19201998b533dae4b9518c99`。模板绑定已存在的源清单（SHA256 `d5cb77b9915dc7437a66a5739acd57093f0ed6acc6f0643e995f415169f2a454`）；本准备只比对清单里的源 bytes/hash 与 root 指定值，没有读取或修改大源 body / projection。Root 后续报告两份 projection 已 PASS_STATIC（正式审前缀 a8decada、数学审前缀 1d947e89）；这不是启动许可，模板仍留 `independent_static_source_review` 的 path/hash 为 null，待 root 在 NEW gate 绑定完整清单路径和完整 SHA。

新 schema 为 `w9a2-v9-resource-gate-v1`，terminal schema 为 `w9a2-v9-compiler-resource-terminal-v1`。新 work 固定 `tmp/w9a2-20261021/v9-resource-v1`；不使用任何旧 session、parent/child PID、已失败工作目录或 Candidate 输出。outer observation 模板 role 为 `v9-resource-v1`，所有实际结果与终端 hash 仍为空。

资源门保持：单个 own-child Lean、`-j1 -M6500 --tstack=262144 -DrelaxedAutoImplicit=false -DElab.async=false`、fresh `-o/-i/-c --json`，统一 3200 秒；7*1024^3 字节停止条件只看 own-child PeakWorkingSetSize。PeakPagefileUsage / PagefileUsage / PrivateUsage 继续采样但仅作诊断。30 秒采样、retained Popen handle 的实际 wait/exit、只停止自己 child、最终 peak、三个非空 fresh 输出、runner 自身及直接 pins 前后复核、fsync/terminal SHA 逻辑均保持。无 cap 增加、自动 retry、repair 或 source discovery。

可信复用边界保持原 v3：固定 Lean/Python 和历史 fullchain-v2 gate，两份可信 ChallengeDeps / CandidateSpec 的 source、actual ordinary exit0 及 olean pins，以及既有 clean package-overlay 路径。旧 fullchain lib 不加入 LEAN_PATH，只把两份可信 olean 复制到 fresh trusted-lib；不复用旧 Solution.Candidate 或 Challenge.Candidate。不重核整个 SDK/runtime/DLL/package 大树，历史 closure 仅作来源引用，不能称新的 fresh closure audit。旧宏观 011 与 import-memory 独审 pins 仅保留为 RSS-only 计量的历史依据，不构成本次 v9 执行授权。

`historical-evidence-pins.json` 另绑定 v8 两次本地资源失败及官网失败的已有清单：首个本地 run 因 own peak-commit 阈值停止；第二个本地 run 为 interpreter memory_exception / outer1；官网 v8 为 Solution 939s / Lean137 / bash1，未完成 Solution export 或双核，未确诊 OOM。它们保持失败，不翻 PASS，也不能据此预判新源成功或失败。v9 是新源资源测量预备，不是旧源重验或数学重放。

模板默认 `allow_compiler_execution=false`、`proposal_only=true`，runner_sha256=null，ownership 未填，窄缓存复用授权 false，源独审 pin 未填。Root 必须完整绑定已完成的独审证据，另行审阅并冻结 NEW enabled gate、精确 runner/source/review pins 及新的 W9A2 ownership 后，才可单次启动。本准备者不启动批次，不生成 ready/上传材料，不改 proof、状态、计数或旧包。原 parent 真正退出须由 root 的新原工具句柄独立记录，内部 code-to-return 不充当 actual outer0。

这里继承的“no kernel/replay”范围只指不额外调用独立 kernel replay 工具，不是关闭 Lean 编译时正常的 kernel typechecking。若 root 以后授权运行，新资源编译自身仍须正常检查全部 proof，不用旧 ordinary PASS 或旧 exports 替代。

Windows 资源测量依然没有官方 `--setup`，不等价 Linux 8GB cgroup，也不代表 fullchain、Comparator、Nano、官方 3200 秒验收、接受或公开推广。此包没有任何新编译、资源 PASS 或证明完成声明。
