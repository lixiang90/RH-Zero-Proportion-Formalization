# 实际完整验收入口，尚未执行

`run_verification.py` 是可执行实现的静态准备。本目录没有运行该入口，也没有运行
Lean、exporter、Comparator、kernel、nanoda 或安装。模板的授权开关为 false。
旧 accepted v3、原五模块、已冻结 draft-v0 和锁定 CoreAudit 均保持原字节。

该入口以 `scripts/verify_single_solution.py` 的公开 roots、primitive 清单和原
CoreAudit 为合同，并保留完整原任务：实际 ζ 无条件 dyadic/cumulative 比例、
严格超过新鲜纪录、完整源码及允许公理、双核、统一3200秒、官网接受、GitHub一致
与提交材料。此入口成功只证明规定范围的本地全链，官网与GitHub/材料仍须另验。

## 根代理使用顺序

1. 先对实际当前 runtime 做独立 setup/身份审核，提供新的 closure manifest。
   `runtime-closure-template.json` 给出必要字段与范围；Windows 当前 native
   exporter/DLL/解释执行模块闭包尚未复核，所以不能把模板 false 改成 true 就当
   完成。manifest 需要 compiler、Python控制器及DLL、PE/ELF动态闭包、source-bound
   trusted package cache、固定 Comparator/Export 源/构建来源。若选 native
   CoreAudit，还需实际独立安装成功收据；解释执行不需要另安装 CoreAudit native。
   setup 不得编译本候选或复用用户 oleans，root 必须观察 setup handle 真 exit0。
2. 若普通 Lean 修过源，先生成并审查新的 `draft-vN`，不覆盖旧 draft-v0。
   修改根 gate 的 frozen_draft 目录、manifest SHA、完整源码 SHA/bytes 和可信模板
   路径。重建格式与现有 freeze_text.py 完全相同；任何不同都会在 ordinary 前硬停。
3. 取新鲜 leaderboard raw+receipt，root gate 绑定两者 SHA。运行开始时 receipt
   必须 HTTP200、raw SHA相同、age在0–900秒，当前最大 kernel-verified exactRational
   必须与 gate 一致，候选以整数分数严格比较；纪录变化停止，不自动换 score。
4. 将 `gate-template.json` 复制到新 gate 路径，填写所有 ROOT_MUST 字段及当前
   runtime绝对路径。不要修改本准备包或旧收据。gate 的 prepared manifest SHA 和
   runner SHA 由冻结后的实际文件获得。审核完成才把 allow_verification_execution、
   root_reviewed_complete_runtime_closure 和 root_confirmed_setup_terminal_exit_code
   设置成实际证据对应的值。
5. 待此前 compiler 真 terminal 后，root 作为唯一 owner 运行下列参数数组形状：

   `python -B -X utf8 run_verification.py --gate <new-gate.json> --gate-sha256 <exact-SHA>`

   这是命令形状，本准备没有执行。原文件路径应使用完整路径；工具不经 shell 拼接。
   Windows gate 采用 Windows Lean/native exporter + WSL串行nanoda；Linux运行时把
   platform改为 linux-native，并填Linux Python/Lean/tool/cache绝对路径和closure。
   Linux所有子进程使用独立session，Windows所有子进程使用独立process group。
6. root 必须保留执行工具的真实 handle，观察其 terminal exit0，并核控制台返回的
   terminal_sha256 等于磁盘 `terminal.json`。三份成功 receipt 都存在且SHA链相同、
   `failure.json`不存在，才能接受完整本地成功。receipt 声称 completion_return_code=0
   不能替代工具真实观察到exit0；任何一个缺失或相矛盾都视为未通过。

## 入口实际执行的范围

单一 monotonic t0 在 gate/pins 核验之前，deadline=t0+3200。它先核完整runtime
闭包、实际compiler版本和新鲜纪录，再在预算内从五份冻结模块去除内部import、
保留全部非import字节与wrapper重新构造完整上传源；校验预期SHA、bytes及2MB上限。
trusted CandidateSpec 从审核过的官方模板和精确数字重新生成，record表达式由
整数构造，不执行leaderboard中的任意字符串。Challenge模板保持官方源，Solution
不定义candidateKappa/currentRecordKappa。

四个module在新空lib内全新ordinary编译，候选LEAN_PATH只含该lib和审查过的可信
package libs。不会复用拆分W9A2或旧候选olean。全部生成的olean/server/private/IR
等实际文件都绑定SHA，三public roots必须出现在#print axioms输出中，所有打印的
公理都必须属于标准三项。

随后同一native exporter分别导出Challenge.Candidate与Solution.Candidate，三个
roots和完整primitive列表都传入；所有导出stdout以二进制文件流保存。原样固定
`tools/ComparatorCoreAudit.lean` SHA
`7e88e84d1d35d5f3115c97a574cc64dd089ef713ef6f9bccb2303fbd41e07ff2`
执行statement/dependency/primitive比较、公理闭包与默认Lean replay。全部三条
明确成功消息必须实际出现。解释执行的tool libs只在此阶段加入，不污染候选编译
和export。native模式则运行独立审核过的同源binary。

nanoda直接消费同一solution.ndjson二进制stdin，配置显式num_threads=0，原允许
公理与hard_error=true，必须exit0并显示完整Checked N declarations with no errors。
Windows通过WSL setsid固定参数shell启动，保存本次新进程组PID；超时只对自己的
Windows进程树和经/proc/exe重新核对的本次nanoda组清理。无重试、恢复、修源或
独立内核分支裁剪。清理可在失败后运行，但不把清理时间包装成3200秒成功。

结束前再次核所有bound输入、源码、运行库、编译产物、日志和两份export。完整
verification.json、deadline-receipt.json、terminal.json以排他创建+flush+fsync保存，
后两份逐级引用前文件SHA，最终控制台给terminal SHA。整个生成到最后SHA/fsync
均在统一deadline内，且程序随即返回0；root另验真实exit。所有success文件仍明确
official_website_acceptance=false，不能替代网站attestation。

## v1 唯一执行修复

Windows nanoda 的固定启动参数增加 `setsid --wait`。util-linux setsid 在自身是
process-group leader 时会 fork；缺少 --wait 时父进程可能先返回0，不能代表真正
nanoda 的退出状态。--wait 等待实际 child 并传回其状态，保留本次独立session及
PID/pgid清理。其余deadline、源码、export、CoreAudit、serial配置和receipt合同
不变。v0 包保持原字节；本版本仍未运行任何proof工具。
