# W9A2 单文件与双核交付配方（仅静态准备）

本目录没有执行 Lean、导出、Comparator、nanoda、安装、优化或网络写入。
`draft-v0` 是当时五模块的字节快照，不是通过证明。原模块与旧 accepted v3
均未修改。`freeze_text.py` 只读源码、模板及已归档的 leaderboard，纯文本生成。
若普通编译需要修源，使用新 `draft-vN` 独占快照，旧版本保留。

## 精确交付合同

候选 κ 为
`3337881639516708570682858853672166187793/4955348542279967171490000000000000000000`。
当前比较纪录为同分子除以
`4955348548503844558750000000000000000000`，来自 2026-10-20T05:09:17Z
归档的 fresh leaderboard。后续生产运行必须另取新鲜纪录；纪录变化即停止，不能
把此处 trusted spec 自动改成其他值，也不能把 preview 里已检查过的大小替代实际源。

`Solution.lean` 保留 Core、Graph、Localization、Counting、Final 的所有非 import
字节、全部数值、宏、notice 和 license；只把外部 import 移到首部，删除已经内联的
四个模块 import，补 `import ChallengeDeps.CandidateSpec` 与三个 wrapper。
源码不定义 `candidateKappa` 或 `currentRecordKappa`。这两个定义仅由捕获的官方
`CandidateSpec.lean.tmpl` 及确切两个有理数生成到独立 `trusted` 目录。
`Challenge/Candidate.lean` 是原官方模板，包括作为 statement holes 的三个 `sorry`；
这些 holes 不允许出现在 Solution 的证明依赖闭包中。Comparator 必须分别读取
challenge 与 solution 两份导出，不能拿 solution 与自己比较。

公开 roots 固定为：

1. `candidate_strict_improvement`
2. `candidate_critical_line_bound`
3. `candidate_critical_line_bound_cumulative`

它们分别从实际 Final.strict_improvement、actual_dyadic、actual_cumulative 得到，
不接受图最优、数值模型、条件定理或部分叶证明充当最终结论。

## 可移植的当前可用路径

旧 WSL `/var/tmp/rh-zero-20261015` runtime 已丢失；旧回执中的路径不可当现存安装。
Windows Lean v4.33.0-rc2 / commit d8b18978322de05a8f3dba51ef03cf5461676c17、
Windows 原生 lean4export 和仓库内 WSL nanoda ELF 均在当前磁盘，具体 SHA 见
`runtime-inventory.json`。inventory 只证明文件存在及字节身份，不证明可运行或
版本兼容。不得以旧 linux 运行时间或旧 ELF SHA 替代这些新平台文件的实际核验。

所有 `<...>` 是根代理在新冻结 gate 中填写的参数，不能原样执行。路径用 Python
`Path` 和参数数组传递，Windows 库路径用 `os.pathsep` 分隔；WSL 只接收通过
`wslpath`/已验证盘符映射得到的 Linux 路径。不要把旧 D 盘路径硬编码到 E 盘工作区。

1. 单独准备可信工具，只构建锁定 Comparator / Export / CoreAudit 源，绝不编
   Solution、候选 module 或证书。现存 exporter 可复用，前后 hash 及 DLL 闭包仍须
   核验。CoreAudit 可采用同版 Windows `lean --run tools/ComparatorCoreAudit.lean`
   的解释执行；它在生产预算内编译可信 driver。更快的 native CoreAudit 则须先有
   独立可信安装回执，绑定同一源与库闭包；本目录没有做这项安装。
2. 为候选建立新的空 `source` 和 `lib`，`LEAN_PATH` 只包含这个新 lib 和当前
   source-bound `.lake/packages/*/.lake/build/lib/lean`。不加入仓库主 lib、旧 proof
   jobs、拆分 W9A2 oleans、旧 accepted v3 oleans，或可信工具安装工程的用户缓存。
3. 同一个 monotonic t0 必须位于所有候选 pins 核验、source flatten 与 trusted
   spec 生成之前，deadline=t0+3200s。source 生成、fresh ordinary、两份 export、
   Comparator/默认 Lean kernel、nanoda 及最终 SHA/fsync/terminal receipt 全在此
   deadline 内。每个子进程只得到当前剩余秒数；超时杀本次完整进程树，0自动重试、
   0自动修源、0恢复。预览 `draft-v0` 不构成这种统一计时。
4. 在 t0 之后，用纯文本生成器重建确切已冻结源；重新核输出 SHA 与完整字节数
   `<= 2_000_000`。再复制可信 ChallengeDeps、重建 CandidateSpec、复制官方
   Challenge.Candidate，形成四个源 module：ChallengeDeps、
   ChallengeDeps.CandidateSpec、Challenge.Candidate、Solution.Candidate。
   源 root 设置为新 `source`，按这四个 module 的顺序全新编译：

   `lean.exe -j1 -M13500 --tstack=262144 -DrelaxedAutoImplicit=false -DElab.async=false -R <fresh-source> -o <fresh-lib/module.olean> <fresh-source/module.lean>`

   `#print axioms` 的三 roots 输出必须齐全，全部只允许 propext、Quot.sound、
   Classical.choice。Lean exit0、输出存在、输入首尾 SHA 不变仍只是普通 Lean 子关。
5. 固定 `LEAN_SYSROOT` 到同版 Windows SDK；两次运行同一 exporter，stdout 以
   二进制流写入不同文件，避免 shell 的 UTF-16/redirection 改写。参数精确为：

   `lean4export.exe Challenge.Candidate -- <三公开roots> <所有primitive名字>`

   `lean4export.exe Solution.Candidate -- <三公开roots> <所有primitive名字>`

   完整 primitive 名单和命令字段见 `verification-contract.json`。导出必须保留三
   roots 的全部传递依赖及 primitives；禁止 `--export-unsafe`、选择更少 roots、
   仅检查新增 wrapper 或过滤已有证明。
6. 使用锁定 `tools/ComparatorCoreAudit.lean` 及锁定原 Comparator modules，分别
   输入 `challenge.ndjson`、`solution.ndjson`、三 roots。若解释执行，工具导入路径
   额外包含 `tmp/Comparator/.lake/build/lib/lean` 与
   `tmp/lean4export/.lake/build/lib/lean`，不得把这些路径用于候选编译或 exporter。
   原 driver 必须打印全部三行：

   - `Pinned Comparator statement, dependency and primitive comparison passed`
   - `Pinned Comparator transitive axiom check passed`
   - `Lean default kernel replay passed`

   此 driver 调用原 compareAt/checkAxioms/env.replay；它不运行 landrun，也不代替
   网站隔离政策。未实际执行不能声称 Comparator 或默认 Lean 内核通过。
7. 启动 WSL nanoda：`wsl.exe --distribution Ubuntu --exec <mapped-nanoda-bin> <mapped-config>`，
   stdin 直接传 `solution.ndjson` 的二进制文件流，stdout/stderr 留日志。配置见
   `nanoda-config.json`，显式 num_threads=0，匹配锁定官方默认串行模式；不因本地
   4线程诊断较快而替代生产配置。必须 exit0 且有
   `Checked N declarations with no errors`，所有打印 axiom 仅允许标准三项。
8. 复核所有 bound 输入/源码/导出/工具/动态库和 symlink 身份，记录实际 source
   SHA、两份 export SHA、全部命令、三个内核子关、声明数、资源、总 elapsed。
   root 另核进程真实 terminal exit0；统一3200秒内写完 verification、deadline、
   terminal 三回执且无 failure 才能宣告本地全链成功。分阶段成功或单独 nanoda
   成功不证明统一时间合规，更不等于官网接受。

## 最后交付仍缺的证据

完整普通 Lean 与三 roots 公理检查、statement/dependency/primitive Comparator、
默认 Lean replay、nanoda、实际统一3200s、随后 fresh record 严格比较、官网
attestation、GitHub一致的最终源码与提交材料，均须由根代理以实际收据验证。
本配方没有把这些 gates 降格为文本准备或模型证书。
