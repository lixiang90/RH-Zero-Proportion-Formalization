# Tiny 冷生产验证准备

本目录是可审查脚本和固定输入的静态准备；没有执行 generator、Lean、export、Comparator、nanoda 或网络。必须由根审查 prepared SHA，并另写不可变 gate 后，由根指定的唯一 compiler owner 执行一次。Phase4.Final 已通过的模块检查只是输入依据，最终验证完全不读取其用户 olean。

`run_production.py` 必须运行在 Linux/WSL。一个主进程的 monotonic t0 在输入检查及文本生成前开始，唯一 deadline 为 t0+3200 秒。每个子进程只得到当前剩余秒数；哈希、文本生成、fresh spec、四个普通模块、可信工具编译、两个 export、Comparator/default kernel、nanoda、最终哈希和 fsync receipt 全部计时。不支持 resume、重试、自动修源或复用用户 olean。失败立即停止，保留本次输出；进程树清理最多15秒另记，不能算作证明时间。

Windows 原生 Python 是 flatten prepared 已绑定的解释器。Linux 主进程在计时内通过 WSL interop 执行 `windows_generate.py`，该 helper 先独占写其 Windows PID，再在同一 Windows 进程用 runpy 执行绑定的 generator。这样不更换 Python 身份，也不在生产计时外先生成。若 generation 超时，owner 对该 PID 执行精确 taskkill /T，并终止其 Linux 进程组。其他 Linux 子进程均是独立进程组，超时先 TERM，宽限后 KILL。此实现是静态审查结果，尚未声称已验证 WSL interop 启动。

独占冷目录固定为 `/var/tmp/rh-zero-20261015/tiny-production-v0`；镜像状态目录固定为仓库 `tmp/current-s1r-tiny-20261018/production-v0`。任一存在则拒绝执行。先新建空 lib，再从固定 Zeta23 归档取得 root `ChallengeDeps.lean`，从捕获的官方模板、可信记录 ledger 的 exactExpression 和候选 p/q 生成新的 CandidateSpec。旧 installed CandidateSpec 完全不改。四个本地源及新 lib 外，LEAN_PATH 只用 runtime manifest 的固定 package paths；任何 cache 提供 root ChallengeDeps/Spec/Challenge/Solution 都会拒绝。所有用户模块拼成一个上传源，不能 import Dev/prefix olean。

可信 Export/Comparator 源从 SHA-bound 归档逐文件读取；tool source allowlist 精确九个模块，全部重新编译并计时。export 包括三个公开 theorem roots 和旧成功配方的完整 primitives。Comparator 日志必须同时出现 statement/dependency/primitive、传递公理和默认 Lean kernel 三项通过；nanoda 允许且只允许 propext、Quot.sound、Classical.choice，并必须报告完整 Checked declarations with no errors。前后绑定 source、tool、output、export、解释器与二进制；Zeta23 cache source/olean 校验来自固定依赖 build receipt。Mathlib 的 cache 来源是 runtime 命名的既有缓存，全部导出的证明仍须经过默认 kernel 和 nanoda，不把 cache 命名本身当数学证明。

每子进程用 `/usr/bin/time -v` 记录 RSS。RLIMIT_FSIZE 明确为 8 GiB **单文件大小限制**，没有设置或声称 8 GiB RAM 限制；栈设256MiB，Lean 参数复用旧已通过配方 `-j1 --tstack=32768 -DrelaxedAutoImplicit=false`。不启用 landrun，也不声称网络隔离或官网接受。最终 local PASS 需要该次主进程真实 exit0、verification/deadline/mirror terminal 三份 receipt、没有 failure.json、总 elapsed≤3200，且所有 proof gates 为真。中途写出的 verification.json 单独存在不构成完整 PASS。

执行命令形状（本准备没有运行）：

```
wsl --distribution Ubuntu --exec /usr/bin/python3 /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/research-goal-20261018-tiny-production-preparation/run_production.py --gate /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/research-goal-20261016/gates/ROOT_CHOSEN.json --gate-sha256 ROOT_GATE_SHA
```

旧候选的各子进程耗时合计1924.904秒（普通853.542、工具7.911、export153.630、Comparator713.949、nanoda195.872）；这既不是该次统一全流程计时，也不推断本候选会在预算内完成。完整网站提交仍需官方最新协议和实际受限 verifier/attestation。
