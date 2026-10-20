# ordinary runner 与 candidate gate 提案静审

本审查不执行 compiler。当前 `compile_frozen.py` SHA256 为
`09b7478efdc8ed380df82b7e04329cd783e347230b46ff283014e20a36822c62`。
`candidate-ordinary-gate-proposal.json` 明确 `authorized=false`，可信依赖的
olean hash 为待填值；它不是执行许可。主代理确定实际 Windows/Linux 环境后，
须另建完整冻结 gate 并传达准确 hash。

现 runner 支持本次开发路径。它以每个 target 的 source_root 作为 Lean `-R`，
以 target.module 在新 job/lib 中生成同名 olean。Prefix/Core 的 source_root
为 `development-split`，二者在该 root 下的路径分别精确等于
StructuralW9A220261020/Prefix.lean 与 Core.lean；其余4模块的 source_root
为项目根。每个 source 的相对路径推导出相同 module 名，且全都列入 source pins。

LEAN_PATH 将该单一 job/lib 放在最前，后面仅列固定 package_libs，没有放入
旧的项目级 `.lake/build/lib/lean`。导入 Prefix/Core/Graph 等会读取本次 job
先前输出；不复用旧候选 olean。单独建立的可信 ChallengeDeps.olean 拟复制到
新 job/lib/ChallengeDeps.olean，并在复制前后核对准确 hash。所有6个 target
按 Prefix、Core、Graph、Localization、Counting、Final 排序，新增项目内部
import 都只指向排在前面的模块。

提案的14项 source pins 包含6份实际开发输入、完整 canonical Core、官方原源、
geometry与sorted metadata、可信ChallengeDeps源、runner及两个独立审查清单。
另有唯一待冻结的 trusted olean pin，以及10个 package 的源码commit pin。
Counting 的5个与 Final 的7个 `#print axioms` 根名从当前源码精确提取；runner
要求打印集合完全相同，且每根的传递公理都属于三项标准允许公理。Prefix/Core/
Graph/Localization 本身没有 print 命令；其实际关键根由 Final 一并审计。

runner 逐模块保存原源快照、命令/LEAN_PATH、child PID、日志、exit code、
olean与source hash及公理表。首个不通过的模块会停止整个批次，无自动修复、
重试或后续模块编译。它不跑 solver、Lake build、export、Comparator 或 nanoda。
执行所有模块前后再次检查 source pins；它并未赋予本次开发批次最终网站验收的
身份，也没有3200秒生产时限的PASS含义。

明确边界如下：package只冻结源码commit，未逐文件哈希全部预编译依赖；编译
从原路径读源，必须维持不并发修改源的约定；preflight失败尚未建job时需保留
调用方console；现 runner 直接调用 powershell.exe 并冻结Windows Lean路径，
不能原样当作Linux runner执行。这些边界均写入提案。若选择Linux，应另准备
对应runner、工具链、依赖安装/版本与新gate，不改名套用Windows gate。

当前 candidate compiler_runs 仍为0。收到主代理完整冻结gate之后，唯一candidate
compiler owner 才可启动一次批次；任何报错须保全该版本源码日志并交回精确
proof-only修复建议，未经新gate不得自动重跑。
