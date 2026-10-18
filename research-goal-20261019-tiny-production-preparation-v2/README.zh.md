# Native + 串行 Nano：完整冷验证 v2 静态准备

本包没有执行 generator、Lean、native tool、export、kernel、nanoda 或网络；只版本化并冻结入口。旧v1、canonical/Production源、flatten-v4及用户上传中的v3源均不修改。原old-v0超时证据保留，不把诊断或部分通过当完整成功。

新独占Linux目录 `/var/tmp/rh-zero-20261015/tiny-production-v2`，镜像 `tmp/current-s1r-tiny-20261018/production-v2`。flatten-v4/draft仍必须不存在，由主进程在单一monotonic t0之后独占创建完整上传源；从未编译的四个Production模块重新生成，预测1,856,430 UTF-8 bytes。随后在全新空lib中冷编译ChallengeDeps、新可信CandidateSpec、官方Challenge.Candidate和整个Solution.Candidate。旧用户olean和任何拆分证书缓存均不用。

## 原生工具安装门

可信工具先独立安装是与官方template预装相同性质的setup，不能在setup中编用户证明。本proof不重编可信工具。成功安装回执路径、SHA、对应setup prepared路径/SHA以及root确认该安装主进程真实exit0，全部由新的不可变gate提供，不硬编码某个失败的native-tools版本。

只接受固定runtime下 `tiny-native-tools-vN/installation.json`。进入proof t0之后核：安装passed、无failure、mirror回执同SHA、proof_runs=0、源和SDK/C闭包在setup前后未变、没有外部Lake包或用户olean；核九个源的SHA确为锁定Export/Comparator归档和原CoreAudit，核原lakefile及toolchain；核两个ELF及完整必要.so/loader闭包，包含symlink解析路径。只有安装生成的source/ELF/运行时文件被绑定，不把它的trusted oleans放入proof LEAN_PATH。

安装时SDK/C编译输入及全部生成物的完整来源保存在安装receipt，receipt自身在本proof内hash并绑定。proof内重新核其实际运行闭包、工具原源及二进制；不重新调用C compiler，不重编工具。之后所有bound输入和artifact在export前、独立内核后重复hash并检查native路径解析未变。安装回执给出的“成功”不能代替本候选任何proof阶段。

## 完整范围及计时

单一t0在本包pins、动态安装receipt/source/binary/.so pins、最新精确纪录gate及最终源生成之前；deadline=t0+3200秒。每个子进程仅得到剩余deadline，失败立即停止，0自动修源/重试。源码生成、所有fresh spec/user ordinary、native challenge/solution exports、native CoreAudit的精确statement/dependency/primitive比较、标准三公理闭包、默认Lean kernel replay、独立nanoda和最终hash/fsync三份receipt全在统一计时内。

两次export直接执行已绑定的原生lean4export，传入与旧配方相同三个公开roots及所有primitives；CoreAudit直接执行原生ELF，源码SHA和全部检查不改。LEAN_SYSROOT固定同SDK，LEAN_PATH只为fresh lib和runtime固定可信packages，不额外导入安装工程的oleans。原生CLI不会接收lean --run的-j/--tstack开关；其main栈仍由相同RLIMIT_STACK=256MiB约束，内置运行时行为与相应native程序相同，不通过改变检查范围取得速度。

nanoda显式num_threads=0，走锁定官方缺省相同的串行分支。允许公理仅propext、Quot.sound、Classical.choice；unsafe_permit_all_axioms=false，unpermitted_axiom_hard_error=true，必须完整Checked declarations with no errors。保留print_success_message/axioms用于本地证据，不减少声明检查。此处不再用4或更多worker改善本地计时。

资源继续逐阶段time-v记录。8GiB仅RLIMIT_FSIZE单文件限制，不声称RAM限制。完整PASS要求真实主进程exit0、verification/deadline/mirror terminal全部相互一致且无failure，完整总elapsed≤3200。根须另查真实handle完成；中间verification单独存在仍不够。

官网隔离、CPU/平台配置和官方attestation不在本入口内，submitted/official_website_acceptance恒false；native+serial实现方式接近官方也不自动构成官网接受。最新记录由gate的新鲜receipt精确核，变化则硬停，不静默修改当前候选或trusted spec。

## 待根执行命令形状（本准备未运行）

```
wsl --distribution Ubuntu --exec /usr/bin/python3 /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/research-goal-20261019-tiny-production-preparation-v2/run_production.py --gate /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/research-goal-20261016/gates/ROOT_NEW_NATIVE_FULLCOLD_GATE.json --gate-sha256 ROOT_NEW_GATE_SHA
```

该入口不做单独benchmark；下一有意义的运行是由根选择的完整fresh冷验证。所有旧输入保持原字节，本准备不授权执行。
