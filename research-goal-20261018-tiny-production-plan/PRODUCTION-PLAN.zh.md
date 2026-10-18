# Tiny 单源生产验证：静态执行计划

本包只检索既有成功配方、冻结来源和待执行命令；没有生成 tiny 单源，没有运行 Lean、export、Comparator、nanoda、网络或数学重放。必须等当前 Dev 编译进程全部 terminal，并由 root 指定 sole owner 和新 gate 后执行。macro006/旧审计和任何编译输入均不改。

## 可复用的成功配方

`verification/gram-defect-20261015/lean/single/verification.json` 是旧候选的完整本地单源成功证据：ordinary、三官方 statement 比较、transitive axiom、Lean default-kernel replay、nanoda 全部通过，nanoda 检查 74,925 declarations；official acceptance=false。实际原生入口是 `scripts/verify_record_20261015.py`，它用 SHA 绑定的源码归档适配 `scripts/verify_single_solution.py`，而不是假称这些归档为 Git checkout。`tools/ComparatorCoreAudit.lean` 保留原 Comparator 的 statement/primitive 比较、公理闭包及默认内核重放。

不能直接运行两个旧 CLI：旧 p/q、ledger/目录和模块名单被硬钉；单进程 `--timeout` 也不是总预算。只复用其 proven steps、归档提取、工具源码和日志形状，另准备最小 tiny 参数适配和全程 deadline，不能用旧 `--resume` / `--reuse-compiled` 或成功 receipt 跳过新用户源编译。

固定 Linux Lean 4.33.0-rc2，commit d8b18978322de05a8f3dba51ef03cf5461676c17，编译器 SHA `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`。nanoda 原生 SHA `0c8332aae13164943ebfed4f8f4ed969494d8e85edff9d774a70fd92ea9318c2`，由 commit 418320295890faed83a96fd97907b12a3b6728c2 的 locked release build 产生。工具版本/归档/原证明 receipt 的精确来源见 tool-provenance.json；执行前还须重核实际二进制和固定 package cache 字节。

## 新可信规格和冷检目录

建议独占新 Linux 目录 `/var/tmp/rh-zero-20261015/tiny-production-v0`；不得覆盖已有目录。root 最终确定路径后必须记入新 prepared。结构为 `source/{ChallengeDeps.lean,ChallengeDeps/CandidateSpec.lean,Challenge/Candidate.lean,Solution/Candidate.lean}`、空 `lib/`、`tools/`、`logs/`。

1. 在统一 monotonic t0 后执行冻结 flatten generator（命令见 COMMANDS.txt）；实际验证输出 bytes≤2,000,000、输入/输出 SHA 与许可证保留。prepared 918b377…只预测 1,978,954B，不代替实际输出或单源编译。
2. 可信 `ChallengeDeps.lean` 只取固定 Zeta23 3635e748…归档的 `comparator/ChallengeDeps.lean`。它从 Mathlib 独立定义 root namespace 的 Ncount/N0star；不能拿 Zeta23 命名空间别名或 Dev olean 替代。
3. **新** CandidateSpec 只写 fresh/source/ChallengeDeps/CandidateSpec.lean：使用捕获官方模板，把当前可信 ledger 的 exactExpression 和表单候选 p/q 代入。预期当前 R 与 tiny p/q 见 flatten 的 candidate-parameters.json；CURRENT_EXPRESSION 不能由 candidate 源自定义。不得修改任何本机旧 CandidateSpec。本地精确模板重建是 local trusted overlay；只有服务器的官方 prepare 和 attestation 才能证明官方生成/接受。
4. Challenge/Candidate.lean 原字节取官方模板；Solution/Candidate.lean 原字节取生成的完整上传单源。不得通过 import StructuralS1R*, Mprefix、Dev 或项目根来读取用户 olean。
5. ordinary 的第一 LEAN_PATH 必须是 fresh/lib，后面仅 runtime.json 列出的固定 `/.lake/packages/*/.lake/build/lib/lean`。必须先冷编译 root `ChallengeDeps` 到 **lib/ChallengeDeps.olean**，再编译 CandidateSpec、Challenge.Candidate、Solution.Candidate。禁止把 Shape/namespace 不同的旧 ChallengeDeps.olean 放到该位置；读取错误模块可在类型相似时误导接口检查。
6. 工具目录仅包含固定 Export/Comparator/驱动；白名单不能包含 ChallengeDeps、Solution 或任一用户模块。export/Comparator 时 tools/lib 可置于 fresh/lib 之前，但它不得遮蔽这些名字。工具自身可重新普通编译并计时；若复用预编译可信工具，必须核其 source/olean/compiler 闭包，不能扩展为复用用户缓存。

## 顺序、成功判据和资源

COMMANDS.txt 是从旧成功日志逐式提取的未来命令形状，不是已准备/授权 runner。精确新 overlay/spec/路径、模板/ledger 身份、二进制/cache pins 和全程 deadline 仍须在执行 gate 前具化。一次顺序：generation → trusted overlay → ordinary 四模块 → trusted tool modules → challenge/solution export → Comparator+default kernel → nanoda →前后 hashes/资源/receipt。各阶段失败即保留历史并停，不自动修源或重试。

export 必须包含三官方 roots 和旧成功配方的完整 primitive/allowed 列表。Comparator 日志须同时确认 statement+dependency+primitive comparison、transitive axiom check、Lean default kernel replay。nanoda 仅允许 propext、Quot.sound、Classical.choice，unsafe_permit_all_axioms=false、unpermitted_axiom_hard_error=true，必须真的读完同 SHA solution export 并报告 Checked … declarations with no errors。定理名称完整列于 COMMANDS.txt。`#print axioms`、普通 elaboration、Comparator、nanoda 任一项均不能代替其余项。

本地严格计时从 generation 前 t0 至最后 replay/hash/receipt 完成，所有普通编译、导出、检查和工具准备计入；每步只得到剩余 deadline，**总 elapsed≤3200s** 才满足本路线交付要求。未来应由一个 Linux/WSL-aware sole-owner launcher 管全进程树，TERM 后15s清理是宽限而非证明预算。仅在各子进程传 `timeout=3200`、相加旧 receipt 的部分时间、在 Dev 缓存外重复小 wrapper，均不证明此门。

捕获官网 cb97717d3ea82c45f19f2ce04c410440b6492aa6 的 `run-comparator-e2b.sh` 实际 inner timeout 为3200s、单文件上限由 prepare-candidate.ts:64 明确为2,000,000 bytes；`run-verification-job.sh` 的3240s是外层 job allowance，不是更大的证明预算。官网内层覆盖范围与上述更严格本地 generation-through-replay 计时分别记录，不能混写。8GiB 是文件大小限制（ulimit -f，block单位须按运行 shell记录），不是该片段给出的内存上限；本地须记录每阶段/总峰值RSS、磁盘和出口文件。旧成功 export 为数百MB，不能按2MB源大小估计磁盘/RAM。

本地 CoreAudit 不执行 landrun/无网络隔离策略，故完整 local PASS 仍不能称 official acceptance；官网 full verifier 的受限环境/最新协议及最终 attestation 必须另过。此包无网络更新，只绑定现有捕获合同；root 15:00:44Z fresh记录另有证据，不在本包重复请求。

## 本包交付边界

静态来源/命令计划已具化；四 Dev 模块是否成功、最终 flatten 身份/大小、fresh numeric spec 生产、tiny 冷单源普通内核、全部 replay、公理、3200s资源和官方接受均仍待实际结果。源码预算只剩约21KB的静态预测，不以压缩包/olean小替代UTF-8原源限制。
