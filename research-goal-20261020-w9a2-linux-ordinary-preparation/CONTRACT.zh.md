# Linux ordinary / trusted-import 执行准备

本包只准备源码、gate模板与静态核对；没有执行任何compiler、import、optimizer或kernel。
当前Windows候选仍活着时不得运行本runner。所有模板authorized=false，不能作为执行许可。
主轮counter不改；canonical数学proof也不改。

## 两个必须分开的门

第一门为trusted：先编译现有 `TrustedImport.lean`，导入当前Core全部22个非
ChallengeDeps进口并检查实际Zeta23计数定义；只有它实际exit0、输出存在且输入未变，
才编译可信定义层ChallengeDeps。第二份源码的原定义前缀与已固定f05666d0…源逐字相同，
仅追加 `#print axioms Ncount/N0star/cMT` 三项诊断，无新数学声明。
字节关系见trusted-audit-generation.json。

任何import/ABI/IR/part/extern错误都会立即停止这一门，保全日志和真实Popen句柄；
没有自动重编142个依赖、cache get、改源或重新运行机制。
trusted通过只说明这些现有library data可被当前官方Linux工具链实际加载，并且
这次可信定义层普通编译通过三公理审计，不能升级为新候选验证。

第二门为candidate：根代理必须另核第一门terminal/probe/ChallengeDeps收据，另写新gate。
固定按现有开发切分顺序编译 Prefix、Core、Graph、Localization、Counting、Final。
只复用第一门Linux实际生成且收据绑定的ChallengeDeps.olean；任何candidate olean都不复用。
Counting五个、Final七个现有transitive roots的#print axioms列表，已与实际source逐项核对。
这些根必须完整出现，任何漏根、意外根或标准三公理以外的名字都令该target失败。
空列表仅用于没有print命令的模块，并没有跳过最终传递公理检查。

## Source/data pin与ext4路径

runner读取固定 `/var/tmp/rh-zero-w9a2-20261020/runtime-v0/runtime.json`，
要求其仍是已记录的setup-only receipt；核manifest SHA、官方Linux archive SHA、
Linuxbin SHA、十包commit映射。随后把mirror-files.jsonl的每一份destination源码与
library data按bytes/SHA前后完整重核。未以package commit名称代替data散列。
不运行Lake，也不从Windows加载DLL或native插件。

证明输入原件来自 `/mnt/e/codex-build/RH-Zero-Proportion-Formalization`，均按gate的
source_files核SHA；每个实际target先逐字节快照到ext4的sources，再从该快照编译。
完整batch之后再核原件、快照与所有runtime mirror pins。Gatehelper保留原Windows
ordinary proposal的全部来源pins及目标顺序，不改其数学源。

两个新工作根固定为：

```
/var/tmp/rh-zero-w9a2-20261020/dev/trusted-v0
/var/tmp/rh-zero-w9a2-20261020/dev/ordinary-v0
```

lib、源快照、完整日志与proof输出都在ext4。gate、command、started、child、逐20秒
observation、模块收据和terminal/failure不可变写入，并把metadata/log镜像到项目
`tmp/w9a2-20261020/linux-trusted-v0` 或 `linux-ordinary-v0`。
镜像metadata不复制olean；每份收据给ext4olean绝对路径和SHA。
所有目录都必须新建，已存在就失败，不覆盖旧历史。

## 独占与实际句柄

执行门必须固定根代理产生的Windows原句柄terminal证据。make_gate.py要求该证据含
原exec session、parent/Lean PID、鲜核时间以及observed_windows_lean_processes=[]。
证据文件本身进入source pins。这不替代运行时检测：runner会用pgrep -a -x lean核
Linux，用WSL互通的Windows PowerShell Get-Process lean核Windows，任一活着即拒绝。

取得跨两个stage共享的普通编译owner锁后，再鲜核一次；每个compiler启动前也重复。
旧锁不会被自动清除；旧锁本身从来不被当作“仍活”或“已经停止”的证明。
runner在启动每个实际compiler时记录Popen.pid和/proc的start_ticks、cmdline、ppid，
之后持续poll同一Popen并写CPU ticks/RSS/log bytes。单次/proc观察race不会触发重启。
只有实际wait得到exit code才产生模块终端收据。

正常失败、超时或收到停止信号时，runner只停止自己仍持有且start_ticks相同的子进程；
保全PID/命令/日志，绝不查找并终止其他Lean。旧句柄需根代理明确判断，不能靠慢或
没有日志就重开。模板hard上限为每target7200秒、batch28800秒，可由根在执行门中
明确审定；这是开发资源上限，与网站统一3200秒验收没有对应保证。

## 准备gate与未来命令

当runtime实际恢复完成、Windows原句柄真实终止后，根代理可只运行无compiler的helper：

```
wsl.exe -d Ubuntu -- python3 /mnt/e/codex-build/RH-Zero-Proportion-Formalization/research-goal-20261020-w9a2-linux-ordinary-preparation/make_gate.py trusted --windows-terminal-evidence <repo-relative-evidence.json> --output <new-repo-relative-trusted-proposal.json>
```

helper读实际runtime与镜像清单散列，生成仍authorized=false的完整proposal。
根审查后另写新authorized=true/proposal_only=false gate，并计算其实际SHA；执行命令为：

```
wsl.exe -d Ubuntu -- python3 /mnt/e/codex-build/RH-Zero-Proportion-Formalization/research-goal-20261020-w9a2-linux-ordinary-preparation/run.py --gate <new-repo-relative-gate.json> --gate-sha256 <actual-sha256>
```

trusted实际terminal PASS后，再用make_gate.py candidate准备另一个proposal；它会拒绝
失败/缺失的probe或可信定义收据，并绑定实际LinuxChallengeDeps.olean字节。
runner仍重新核这条PASS链和artifact散列，不能仅凭helper先前通过就绕开检查。
当前两份template中的runtime与terminal散列均为null；当前不能授权或执行。

## 本次静态验证与剩余验收

Python AST解析通过，实际六模块与12个公理root列表核同；可信源原始前缀字节同。
没有运行runner/make_gate，没有现Linuximport成功率或时间收据。
runtime恢复、普通模块编译、三公理audit、单源flatten、精确Comparator/primitive/依赖、
Lean/nanoda、统一3200秒、届时最新纪录、GitHub与提交材料仍分别需要真实证据。
本包不宣称当前新无条件比例已验证。
