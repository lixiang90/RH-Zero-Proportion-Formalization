# v8 Windows 导入内存静审

结论：需要更正诊断门的指标解释。现有证据支持“runner 自己的 Windows peak-process-commit 阈值触发并中止”；不支持“Lean 已实际占用 7 GiB resident RAM”“触犯官网 Linux 8 GB 内存门”或“OS OOM”。同 pin Lean 的 `.olean` COW 映射确实能够在导入阶段产生大 commit、低 working set。它是此次曲线的有源码依据的解释，仍不是已测出的实际映射归因或阶段定位。原始失败不升级为 PASS。

## 实际收据

原始 root observation 固定 session 72573、parent PID 54132、child PID 12924、原 outer exit 1。runner 在约 663.234 秒因预声明的 7 GiB peak RSS 或 peak commit 门主动停止自己持有的 child；不是本审查启动、杀掉或重试的过程。

现存 `memory.jsonl` 的 24 个样本包括 23 个存活期间样本和 1 个 wait 后样本。最大 working set 为 375,066,624 B（357.69140625 MiB）；peak commit 为 7,728,263,168 B（7370.24609375 MiB）。存活样本中 commit 持续上升，最后一个为 7,728,250,880 B，而 working set 为 375,062,528 B。wait 后 current commit 回落至 8,409,088 B，但 peak 字段保留历史最大值。两个输出日志均为 0 B，三个目标输出没有成功收据。没有命令级进度或实际 mapped-region 清单，故不能从零 stdout 确证“始终只在 import”，也不能确证已进入新证明或 C emission。

## 从 Lean import 到 Windows COW 的准确源码链

本机同版 `Lean/Environment.lean:1782–1789` 的 `readModuleDataParts` 逐个调用 `CompactedRegion.read`；`Lean/CompactedRegion.lean` 将后者绑定到 `lean_compacted_region_read`。按此实际 extern 名称，再从 exact-ref Git tree 定位 C++，没有运行 DLL 或 executable。

以下文件均固定 [Lean commit d8b18978322de05a8f3dba51ef03cf5461676c17](https://github.com/leanprover/lean4/tree/d8b18978322de05a8f3dba51ef03cf5461676c17)，捕获的完整小文件按 Git blob SHA1 实际核对：

- [`src/library/module.cpp:454–616`](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/library/module.cpp#L454) 的 reader 获取文件大小，Windows 映射用 `CreateFileMapping(..., PAGE_WRITECOPY, ...)`（511）与 `MapViewOfFileEx(..., FILE_MAP_COPY, ..., 0, base_addr)`（516）。0 长度请求整个文件；成功落在保存的 base address 才保留映射。映射不可用则退回 `malloc(size)` 加完整读取（559–565）。源码说明 COW 写权限用于必要的指针 fixup，未写页可以保持文件缓存共享；本审查没有测量当前实际走了哪条分支或哪些页被修正。
- [`src/CMakeLists.txt:106,155–156`](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/CMakeLists.txt#L106) 默认 `MMAP` 为 ON，并在开启时定义 `LEAN_MMAP`。这是同 pin 源码默认配置；本审查没有执行二进制 feature probe，也没有把默认配置当作实际 mapped-region 收据。
- Microsoft 明确规定 `FILE_MAP_COPY` 会对整个 view 收取系统及进程 commit，因为每页都可能日后变为私有副本；这不要求整份文件已经进入物理内存。[MapViewOfFile](https://learn.microsoft.com/en-us/windows/win32/api/memoryapi/nf-memoryapi-mapviewoffile)

因此导入大量 `.olean`/parts 时，即便只触及少量头部和对象页，也存在 commit 远大于 working set 的合法实现路径。源码中的 Linux 分支使用 `MAP_PRIVATE`；不能把 Windows 的 COW 承诺额度直接等同于 Linux 实际 resident/cgroup 用量。

## `-M6500` 与额外门是两个不同指标

同 pin [`src/runtime/memory.cpp:42–59`](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/runtime/memory.cpp#L42) 的 Windows RSS 分支从 `GetProcessMemoryInfo` 读取 `PeakWorkingSetSize` 与 `WorkingSetSize`。`check_memory:145–156` 间歇检查 `g_max_memory` 时先看 peak RSS，必要时再看 current RSS；没有在这里使用 `PagefileUsage`。这与本次 runner 额外的 `PeakPagefileUsage >= 7 GiB` 判据不同，不能把本次主动停止描述为 `-M6500` 被 Lean 检出超限。源码另有 HAS_JEMALLOC 条件分支；本审查陈述的是 Windows 分支，没有新运行或修改 allocator 配置。

Microsoft 将 `WorkingSetSize` 定义为当前 working set，`PeakPagefileUsage` 定义为进程历史 peak commit；`PrivateUsage` 与 current commit 对应。commit 不是已经写入磁盘 pagefile 的字节数，也不是当前 resident RAM。[PROCESS_MEMORY_COUNTERS_EX](https://learn.microsoft.com/en-us/windows/win32/api/psapi/ns-psapi-process_memory_counters_ex)，[Working Set](https://learn.microsoft.com/en-us/windows/win32/memory/working-set)

一般的 `VirtualAlloc(MEM_COMMIT)` 也能先计 backing commitment、后按触页分配物理页；单独 `MEM_RESERVE` 则只保留地址空间。故低 working set 本身也不能排除其他已 commit 但未触及的分配。这里不把全部差额武断归给 COW，也不与 formal_owner 的独立 thread-stack 审查争抢归因。[VirtualAlloc](https://learn.microsoft.com/en-us/windows/win32/api/memoryapi/nf-memoryapi-virtualalloc)

## 只读库清单的范围

只读取并 hash 了一次既有 89 MB closure JSON（SHA `4d295c059a87faad191c34d1c221bbb744f04f98e226c4a5d0d08f3c01c2d67a`）；没有 stat 或重新 hash 它指向的 17 GB 树。该清单有 171,231 行，同时包含原包路径与 overlay 副本，不能直接相加为进程实际 imports。

仅把清单的 SDK 路径与 package-overlay 路径中的 `.olean`、`.olean.server`、`.olean.private` 可用文件相加，得到 7,460,811,000 B；重复原包和 tool-overlay 不计入此小计。这只是“可用 artifact inventory”，不是本次实际导入或映射数量、实际 commit 的来源分解、内存下界或容量需求。具体分类保存在 `closure-metadata-stats.json`，实际观察与推断分列于 `memory-observation-summary.json`。

## 可支持的下一门建议

应先书面改清测量合同，再由 root 决定新的独占 gate；本报告不准备或执行下门。若目标是 Windows resident-resource 诊断，应以 working-set 指标表述相应阈值，保留 commit 为独立的 Windows host-safety 指标，并准确说明触发哪一个。若仍用 7 GiB commit 主动停止，就应继续称“保守的 host commit 中止”，不能称官网 8 GB 内存失败。

仅把阈值换成 RSS 也不能建立 Linux cgroup 等价：两种系统、缓存与多进程归账并不相同。不能从本静审自动推出应取消、提高 commit 保护，不能保证余下编译会通过、会在 3200 秒完成或能通过官网。原终态仍为主动中止、未完成三个输出；保留原源、日志、失败收据和 counter。本审查至此停止，零 Lean/compiler/export/kernel/solver、零探针、零新进程查询、零候选修改。
